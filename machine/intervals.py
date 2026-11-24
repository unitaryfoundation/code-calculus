"""Extracted module from machine/priced_calculus.py."""

import copy
import re
import itertools
import json
import math
from collections import deque
from dataclasses import dataclass
from decimal import Decimal
from fractions import Fraction
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

from machine.gf2 import *
from machine.state import *
from machine.connectivity import *
from machine.layout import *
from machine.tower_prices import *

@dataclass(frozen=True)
class Interval:
    """Closed integer interval; None denotes +infinity at either endpoint."""

    lower: Optional[int]
    upper: Optional[int]

    def __post_init__(self):
        for endpoint in (self.lower, self.upper):
            if endpoint is not None and (isinstance(endpoint, bool)
                                        or not isinstance(endpoint, int)):
                raise ValueError("distance endpoints must be integers")
        if self.lower is not None and self.lower < 0:
            raise ValueError("distance lower bounds are nonnegative")
        if self.upper is not None and self.upper < 0:
            raise ValueError("distance upper bounds are nonnegative")
        if self.lower is None and self.upper is not None:
            raise ValueError("an infinite lower endpoint requires an infinite upper endpoint")
        if self.lower is not None and self.upper is not None and self.lower > self.upper:
            raise ValueError("empty interval")

    def staged_distance_check(self, state, *args, **kwargs):
        from machine import planner as _planner
        return _planner.staged_distance_check(state, *args, **kwargs)

    def staged_check(self, state, *args, **kwargs):
        return self.staged_distance_check(state, *args, **kwargs)

    def as_json(self):
        return {
            "lower": "inf" if self.lower is None else self.lower,
            "upper": "inf" if self.upper is None else self.upper,
        }

def _min_upper(left, right):
    if left is None:
        return right
    if right is None:
        return left
    return min(left, right)

def _transport_interval(lower, upper):
    """Build a transported interval, refusing a contradictory one.

    A carried endpoint contradicted by a witness or a price is a failed
    premise of the transport rule, not a crash and not a widened interval:
    it is `no_derivation`, one of the three outcomes of
    `spec/TERM_LANGUAGE.md` 5.
    """
    try:
        return Interval(lower, upper)
    except ValueError as exc:
        raise NoDerivation("interval transport is inconsistent: %s" % exc)

def _copy_small_mapping(entry):
    """Shallow copy of a small mapping, with explicit copies of any nested
    lists/dicts. Used for witness and condition entries so that mutation of a
    copied ledger cannot leak back into the original."""
    if not isinstance(entry, dict):
        return entry
    copied = dict(entry)
    for key, value in list(copied.items()):
        if isinstance(value, list):
            copied[key] = list(value)
        elif isinstance(value, dict):
            copied[key] = dict(value)
    return copied

def _copy_witnesses(witnesses):
    if isinstance(witnesses, dict):
        return {side: [_copy_small_mapping(w) for w in entries]
                for side, entries in witnesses.items()}
    return witnesses

def _copy_conditions(conditions):
    if isinstance(conditions, list):
        return [_copy_small_mapping(c) for c in conditions]
    return conditions

# Labels a witness may carry for the depth of the search that found it
# (`witness_confidence` in machine/entrypoints.py maps a trial count to one).
WITNESS_CONFIDENCE_LABELS = ("deep", "screened")


class DistanceLedger:
    """Consumer-side distance intervals, separate from CodeState."""

    def __init__(self, full, sector, witnesses=None, conditions=None):
        self.full = full
        self.sector = dict(sector)
        # Copy the caller's witness and condition entries, so that the ledger
        # never aliases data owned by the caller.  A witness keeps the
        # confidence label it was given and gets none otherwise: the label
        # describes how deep the search that found the witness went, and the
        # ledger has no basis for inventing one (issue #632).
        self.witnesses = _copy_witnesses({
            "X": (witnesses or {}).get("X", []),
            "Z": (witnesses or {}).get("Z", []),
        })
        self.conditions = _copy_conditions(conditions or [])

    @classmethod
    def for_constructed(cls, state, lower_bounds=None, witnesses=None, constructor_cell=None, intervals=None):
        """The ledger of a freshly constructed state (spec/JUDGMENT_LAYER.md
        sections 2g and 2g.1, spec/OPERATIONAL_SEMANTICS.md section 4.45):
        every interval starts at [0, +inf); a sector or full lower endpoint is
        raised only by a supplied bound with a source or an admitted
        conditional constructor cell, and upper endpoints come only from
        witnesses validated in the constructed state.
        """
        if not isinstance(state, CodeState):
            raise Malformed("for_constructed takes a CodeState")
        lower_bounds = lower_bounds or {}
        if not isinstance(lower_bounds, dict):
            raise Malformed("supplied lower bounds must be an object")
        conditions = []
        values = {}
        for key in ("X", "Z", "d"):
            raw = lower_bounds.get(key, 0)
            if isinstance(raw, dict):
                if not isinstance(raw.get("source"), str) or not raw["source"].strip():
                    raise Malformed("a supplied lower bound needs a source")
                conditions.append({"cell": "input lower bound", "property": key,
                                   "source": raw["source"]})
                raw = raw.get("value", 0)
            elif raw != 0 or not isinstance(raw, int) or isinstance(raw, bool):
                # An unsourced bare number would raise the endpoint without an
                # `input lower bound` condition, making it indistinguishable
                # from a proved bound (JUDGMENT_LAYER.md §2c). Zero is the
                # default and needs no record.
                raise Malformed(
                    "a supplied lower bound needs a source: use "
                    "{'value': n, 'source': '...'}"
                )
            if not isinstance(raw, int) or isinstance(raw, bool) or raw < 0:
                raise Malformed("supplied lower bounds must be nonnegative integers")
            values[key] = raw

        if constructor_cell is not None:
            if not isinstance(constructor_cell, dict):
                raise Malformed("constructor_cell must be an object")
            c_name = constructor_cell.get("constructor")
            source = constructor_cell.get("source")
            if not isinstance(source, str) or not source.strip():
                raise Malformed("a conditional constructor cell needs a non-empty source")

            def _pos_int(val, label):
                if not isinstance(val, int) or isinstance(val, bool) or val < 1:
                    raise Malformed("%s must be a positive integer" % label)
                return val

            def _pos_or_inf(val, label):
                if val is None or val == "inf":
                    return None
                return _pos_int(val, label)

            if c_name == "L-HGP":
                d1 = _pos_or_inf(constructor_cell.get("d1"), "L-HGP d1")
                d2 = _pos_or_inf(constructor_cell.get("d2"), "L-HGP d2")
                d1_t = _pos_or_inf(constructor_cell.get("d1_T"), "L-HGP d1_T")
                d2_t = _pos_or_inf(constructor_cell.get("d2_T"), "L-HGP d2_T")
                cell_x = _min_upper(d2, d1_t)
                cell_z = _min_upper(d1, d2_t)
                if cell_x is None or cell_z is None:
                    raise Malformed("L-HGP conditional cell requires at least one finite bound per sector")
                cell_d = min(cell_x, cell_z)
            elif c_name == "L-NESTED-CSS":
                raw_x = constructor_cell.get("d_ker_HZ", constructor_cell.get("d_X"))
                raw_z = constructor_cell.get("d_ker_HX", constructor_cell.get("d_Z"))
                cell_x = _pos_int(raw_x, "L-NESTED-CSS d_ker_HZ")
                cell_z = _pos_int(raw_z, "L-NESTED-CSS d_ker_HX")
                cell_d = min(cell_x, cell_z)
            elif c_name == "A-CONCAT":
                outer_b = constructor_cell.get("outer") or {}
                inner_b = constructor_cell.get("inner") or {}
                block_b = constructor_cell.get("outer_block") or {}
                k_in = _pos_int(constructor_cell.get("k_in", 1), "A-CONCAT k_in")
                d_ox = _pos_int(constructor_cell.get("d_out_X", outer_b.get("X")), "A-CONCAT d_out_X")
                d_oz = _pos_int(constructor_cell.get("d_out_Z", outer_b.get("Z")), "A-CONCAT d_out_Z")
                d_ix = _pos_int(constructor_cell.get("d_in_X", inner_b.get("X")), "A-CONCAT d_in_X")
                d_iz = _pos_int(constructor_cell.get("d_in_Z", inner_b.get("Z")), "A-CONCAT d_in_Z")
                raw_bx = constructor_cell.get("d_block_X", block_b.get("X"))
                raw_bz = constructor_cell.get("d_block_Z", block_b.get("Z"))
                d_bx = _pos_int(raw_bx, "A-CONCAT d_block_X") if raw_bx is not None else 0
                d_bz = _pos_int(raw_bz, "A-CONCAT d_block_Z") if raw_bz is not None else 0
                eff_ox = max((d_ox + k_in - 1) // k_in, d_bx)
                eff_oz = max((d_oz + k_in - 1) // k_in, d_bz)
                cell_x = eff_ox * d_ix
                cell_z = eff_oz * d_iz
                cell_d = min(cell_x, cell_z)
            elif c_name == "A-PRODUCT":
                cert = constructor_cell.get("display_certificate")
                if not cert or (isinstance(cert, str) and not cert.strip()):
                    raise NoDerivation(
                        "A-PRODUCT conditional distance cell requires an explicit display_certificate")
                if "d_X" in constructor_cell or "d_Z" in constructor_cell:
                    cell_x = _pos_int(constructor_cell.get("d_X"), "A-PRODUCT d_X")
                    cell_z = _pos_int(constructor_cell.get("d_Z"), "A-PRODUCT d_Z")
                    cell_d = min(cell_x, cell_z)
                else:
                    left_b = constructor_cell.get("left") or {}
                    right_b = constructor_cell.get("right") or {}
                    d_ax = _pos_int(constructor_cell.get("d_A_X", left_b.get("X")), "A-PRODUCT d_A_X")
                    d_az = _pos_int(constructor_cell.get("d_A_Z", left_b.get("Z")), "A-PRODUCT d_A_Z")
                    d_bx = _pos_int(constructor_cell.get("d_B_X", right_b.get("X")), "A-PRODUCT d_B_X")
                    d_bz = _pos_int(constructor_cell.get("d_B_Z", right_b.get("Z")), "A-PRODUCT d_B_Z")
                    cell_x = d_ax * d_bx
                    cell_z = d_az * d_bz
                    cell_d = min(cell_x, cell_z)
            elif c_name == "A-DOUBLE":
                wiring = constructor_cell.get("wiring")
                wiring_empty = constructor_cell.get("wiring_empty", not bool(wiring))
                if not wiring_empty:
                    if not constructor_cell.get("twisted_certificate"):
                        raise NoDerivation(
                            "A-DOUBLE conditional distance cell with non-empty wiring requires an explicit twisted_certificate")
                    cell_x = _pos_int(constructor_cell.get("d_X"), "A-DOUBLE twisted d_X")
                    cell_z = _pos_int(constructor_cell.get("d_Z"), "A-DOUBLE twisted d_Z")
                    cell_d = min(cell_x, cell_z)
                else:
                    parent_b = constructor_cell.get("parent") or {}
                    d_cx = _pos_int(constructor_cell.get("d_C_X", parent_b.get("X")), "A-DOUBLE d_C_X")
                    d_cz = _pos_int(constructor_cell.get("d_C_Z", parent_b.get("Z")), "A-DOUBLE d_C_Z")
                    conj = constructor_cell.get("conjugate", False)
                    if not isinstance(conj, bool):
                        raise Malformed("A-DOUBLE conjugate must be a boolean")
                    if conj:
                        cell_x = min(d_cx, d_cz)
                        cell_z = min(d_cx, d_cz)
                    else:
                        cell_x = d_cx
                        cell_z = d_cz
                    cell_d = min(cell_x, cell_z)
            else:
                raise Malformed("unsupported conditional constructor cell %r" % (c_name,))

            values["X"] = max(values["X"], cell_x)
            values["Z"] = max(values["Z"], cell_z)
            values["d"] = max(values["d"], cell_d)
            conditions.append({
                "cell": "%s conditional distance cell" % c_name,
                "status": "conditional",
                "source": source,
                "bounds": {"X": cell_x, "Z": cell_z, "d": cell_d},
            })

        validated_witnesses = {"X": [], "Z": []}
        uppers = {"X": None, "Z": None, "d": None}
        intervals = intervals or {}
        if not isinstance(intervals, dict):
            raise Malformed("supplied intervals must be an object")
        for key in ("X", "Z", "d"):
            if key not in intervals:
                continue
            spec = intervals[key]
            if not isinstance(spec, dict):
                raise Malformed("a supplied interval must be an object with lower, upper, source")
            if not isinstance(spec.get("source"), str) or not spec["source"].strip():
                raise Malformed("a supplied interval needs a source")
            lo = spec.get("lower", spec.get("value", 0))
            up = spec.get("upper")
            if not isinstance(lo, int) or isinstance(lo, bool) or lo < 0:
                raise Malformed("supplied lower bounds must be nonnegative integers")
            if up is not None and (not isinstance(up, int) or isinstance(up, bool) or up < 0):
                raise Malformed("supplied upper bounds must be nonnegative integers")
            values[key] = max(values.get(key, 0), lo)
            uppers[key] = _min_upper(uppers.get(key), up)
            conditions.append({"cell": "supplied distance interval", "property": key,
                               "status": "conditional", "source": spec["source"]})
        if witnesses is not None:
            if not isinstance(witnesses, dict) or not set(witnesses).issubset({"X", "Z"}):
                raise Malformed("constructed witnesses must be a dict keyed by 'X' and/or 'Z'")
            for side in ("X", "Z"):
                seen = set()
                for entry in witnesses.get(side, ()):
                    if isinstance(entry, dict):
                        raw_sup = entry.get("support")
                        w_source = entry.get("source", "constructed witness")
                        conf = entry.get("confidence")
                        if conf is not None and conf not in WITNESS_CONFIDENCE_LABELS:
                            raise Malformed("witness confidence must be one of %s"
                                            % ", ".join(WITNESS_CONFIDENCE_LABELS))
                    else:
                        raw_sup = entry
                        w_source = "constructed witness"
                        conf = None
                    if not isinstance(raw_sup, (list, tuple, set, frozenset)):
                        raise Malformed("witness support must be a list of qubit labels")
                    labels = []
                    for q in raw_sup:
                        if isinstance(q, bool) or not isinstance(q, int) or q < 0:
                            raise Malformed("witness qubit labels must be nonnegative integers")
                        labels.append(q)
                    support = tuple(sorted(labels))
                    weight = len(support)
                    validate_witness(state, side, support, weight)
                    if support not in seen:
                        record = {
                            "support": list(support),
                            "value": weight,
                            "source": w_source,
                        }
                        if conf is not None:
                            record["confidence"] = conf
                        validated_witnesses[side].append(record)
                        seen.add(support)
                    uppers[side] = _min_upper(uppers[side], weight)

        full_upper = _min_upper(_min_upper(uppers["X"], uppers["Z"]), uppers["d"])
        sec_x = _transport_interval(values["X"], uppers["X"])
        sec_z = _transport_interval(values["Z"], uppers["Z"])
        full_iv = _transport_interval(values["d"], full_upper)
        return cls(full_iv, {"X": sec_x, "Z": sec_z},
                   witnesses=validated_witnesses, conditions=conditions)

    @classmethod
    def from_challenge(cls, state, document, lower_bounds=None):
        lower_bounds = lower_bounds or {}
        if not isinstance(lower_bounds, dict):
            raise Malformed("supplied lower bounds must be an object")
        witnesses = {"X": [], "Z": []}
        conditions = []
        uppers = {"X": None, "Z": None}
        try:
            for side in ("X", "Z"):
                item = document["distance"][side]
                support = tuple(sorted(item["witness"]))
                weight = item["value"]
                validate_witness(state, side, support, weight)
                witnesses[side].append({"support": list(support), "value": weight,
                                        "source": "qldpc-challenge witness"})
                uppers[side] = weight
        except (KeyError, TypeError) as exc:
            raise Malformed("challenge distance witness is incomplete: %s" % exc)
        side_bounds = {}
        for side in ("X", "Z"):
            raw = lower_bounds.get(side, 0)
            if isinstance(raw, dict):
                if not isinstance(raw.get("source"), str) or not raw["source"].strip():
                    raise Malformed("a supplied lower bound needs a source")
                conditions.append({"cell": "input lower bound", "property": side,
                                   "source": raw["source"]})
                raw = raw.get("value", 0)
            elif raw != 0 or not isinstance(raw, int) or isinstance(raw, bool):
                raise Malformed(
                    "a supplied lower bound needs a source: use "
                    "{'value': n, 'source': '...'}"
                )
            if not isinstance(raw, int) or isinstance(raw, bool) or raw < 0:
                raise Malformed("supplied lower bounds must be nonnegative integers")
            try:
                side_bounds[side] = Interval(raw, uppers[side])
            except ValueError as exc:
                raise Malformed("supplied lower bound contradicts the witness: %s" % exc)
        d_lower = lower_bounds.get("d", 0)
        if isinstance(d_lower, dict):
            if not isinstance(d_lower.get("source"), str) or not d_lower["source"].strip():
                raise Malformed("a supplied lower bound needs a source")
            conditions.append({"cell": "input lower bound", "property": "d",
                               "source": d_lower["source"]})
            d_lower = d_lower.get("value", 0)
        elif d_lower != 0 or not isinstance(d_lower, int) or isinstance(d_lower, bool):
            raise Malformed(
                "a supplied lower bound needs a source: use "
                "{'value': n, 'source': '...'}"
            )
        if not isinstance(d_lower, int) or isinstance(d_lower, bool) or d_lower < 0:
            raise Malformed("supplied lower bounds must be nonnegative integers")
        side_min_lower = min(
            (bound.lower for bound in side_bounds.values() if bound.lower is not None),
            default=None,
        )
        if d_lower:
            try:
                side_bounds = {
                    side: Interval(max(bound.lower if bound.lower is not None else 0, d_lower),
                                   bound.upper)
                    for side, bound in side_bounds.items()
                }
            except ValueError as exc:
                raise Malformed("supplied lower bound contradicts the witness: %s" % exc)
        full_lower = max(d_lower, side_min_lower or 0)
        full_upper = _min_upper(uppers["X"], uppers["Z"])
        if full_upper is not None and full_lower > full_upper:
            raise Malformed("supplied lower bound contradicts the witness")
        return cls(Interval(full_lower, full_upper), side_bounds, witnesses, conditions)

    def copy(self):
        return DistanceLedger(
            self.full,
            self.sector,
            _copy_witnesses(self.witnesses),
            _copy_conditions(self.conditions),
        )

    def record_witness(self, state, side, support, source="consumer witness",
                       confidence=None, trials=None, depth=None):
        if confidence is not None and confidence not in WITNESS_CONFIDENCE_LABELS:
            raise Malformed("witness confidence must be one of %s"
                            % ", ".join(WITNESS_CONFIDENCE_LABELS))
        support = tuple(sorted(support))
        weight = len(support)
        validate_witness(state, side, support, weight)
        entry = {"support": list(support), "value": weight, "source": source}
        if confidence is not None:
            entry["confidence"] = confidence
        if trials is not None:
            entry["trials"] = trials
        if depth is not None:
            entry["depth"] = depth
        self.witnesses[side].append(entry)

    def _valid_witnesses(self, state, side):
        valid = []
        seen = set()
        for witness in self.witnesses[side]:
            support = tuple(sorted(witness["support"]))
            try:
                validate_witness(state, side, support, witness["value"])
            except NoDerivation:
                continue
            if support not in seen:
                kept = {"support": list(support), "value": witness["value"],
                        "source": witness.get("source", "consumer witness")}
                if witness.get("confidence") is not None:
                    kept["confidence"] = witness["confidence"]
                valid.append(kept)
                seen.add(support)
        return valid

    def propagate(self, operation, new_state, hypothesis=None, observations=None,
                  parent_state=None, lower_bound_mode="direction2"):
        """Apply the licensed interval rule; hypotheses are never inferred.

        `parent_state` carries the state before the step, for hypothesis
        cells whose cheap structural side is computed rather than trusted
        (direct-sum extinction, and, since the sector split, the deleted sector of a
        priced `C-DELETE-CHECK`). A priced deletion without `parent_state`
        has no derivation.
        """
        hypothesis = hypothesis or {}
        observations = observations or {}
        extinction_applied = False
        extinction_factor = None
        if not isinstance(hypothesis, dict) or not isinstance(observations, dict):
            raise Malformed("hypotheses and observations must be objects")
        if not isinstance(operation, dict) or not isinstance(operation.get("op"), str):
            raise Malformed("operation must be an object with a string 'op'")
        out = self.copy()
        op = operation["op"]
        if op == "C-SKIP":
            pass
        elif op == "C-ADD-CHECK":
            # Every licensed addition rule only raises lower endpoints
            # (distance cannot decrease under an added check). Hypotheses on
            # one step compose by max of lower endpoints: each block reads
            # the running `out`, not the parent ledger, so a sector-aware
            # price and a rank-completion cell on the same step tighten
            # instead of overwriting.
            strict = hypothesis.get("strict_improvement")
            if strict is not None:
                if not isinstance(strict, dict):
                    raise NoDerivation("strict-improvement hypothesis must be an object")
                old = self.full
                base = strict.get("base_distance")
                if (old.lower is None or old.upper is None or old.lower != old.upper
                        or not isinstance(base, int) or isinstance(base, bool)
                        or base != old.lower
                        or strict.get("all_minimum_classes_killed") is not True
                        or not isinstance(strict.get("enumeration_id"), str)
                        or not strict.get("enumeration_id").strip()):
                    raise NoDerivation("strict-improvement hypothesis is incomplete or mismatched")
                improved = base + 1
                out.full = Interval(max(out.full.lower, improved), None)
                # Raise lower endpoints, never lower them: a sector can
                # coherently carry a lower bound above base+1, because
                # d = min(d_X, d_Z) constrains the sectors only through their
                # minimum.
                for side in ("X", "Z"):
                    carried = out.sector[side].lower
                    out.sector[side] = (
                        Interval(None, None) if carried is None
                        else Interval(max(carried, improved), None)
                    )
                out.conditions.append({"cell": "C-ADD-CHECK strict improvement",
                                       "status": "conditional",
                                       "enumeration_id": strict["enumeration_id"]})
            sector_gauging = hypothesis.get("sector_gauging")
            if sector_gauging is not None:
                if not isinstance(sector_gauging, dict):
                    raise NoDerivation("sector-gauging hypothesis must be an object")
                evidence = sector_gauging.get("evidence")
                if not isinstance(evidence, str) or not evidence.strip():
                    raise NoDerivation("sector-gauging requires an evidence reference")
                prices = {}
                for side, field in (("X", "w_X"), ("Z", "w_Z")):
                    value = sector_gauging.get(field)
                    if value is None:
                        continue
                    if (not isinstance(value, int) or isinstance(value, bool) or value < 0):
                        raise NoDerivation("sector-gauging prices must be nonnegative integers")
                    prices[side] = value
                if not prices:
                    raise NoDerivation("sector-gauging requires at least one sector price")
                for side in ("X", "Z"):
                    if side in prices:
                        carried = out.sector[side].lower
                        out.sector[side] = (
                            Interval(prices[side], None)
                            if carried is None
                            else Interval(max(carried, prices[side]), None)
                        )
                out.conditions.append({"cell": "C-ADD-CHECK sector-aware gauging",
                                       "status": "conditional",
                                       "prices": prices,
                                       "evidence": evidence})
            extinction = hypothesis.get("direct_sum_extinction")
            if extinction is not None:
                if not isinstance(extinction, dict):
                    raise NoDerivation("direct-sum extinction hypothesis must be an object")
                old = self.full
                base = extinction.get("base_distance")
                factor = extinction.get("factor_distance")
                evidence = extinction.get("evidence")
                if (old.lower is None or old.upper is None or old.lower != old.upper
                        or base != old.lower
                        or not isinstance(factor, int) or isinstance(factor, bool)
                        or factor <= base
                        or parent_state is None):
                    raise NoDerivation("direct-sum extinction hypothesis is incomplete or mismatched")
                # The cheap parts of the hypothesis are computed, not trusted
                # disjoint union, the added check must lie inside one block,
                # and gauging must extinguish that block's last logical
                # (k drops by exactly one). Only the surviving block's
                # distance d_B stays an external judgment input, covered by
                # the required evidence reference.
                if not isinstance(evidence, str) or not evidence.strip():
                    raise NoDerivation("direct-sum extinction requires an evidence reference")
                if tanner_components(parent_state) != 2 or tanner_components(new_state) != 2:
                    raise NoDerivation(
                        "direct-sum extinction: the parent is not a two-block disjoint union "
                        "or the added check merges the blocks (rank_check %r)"
                        % extinction.get("rank_check"))
                added_support = [q for q in operation.get("support", [])]
                if not added_support:
                    raise NoDerivation("direct-sum extinction: missing added-check support")
                parent_components = _tanner_component_of(parent_state)
                if any(q not in parent_components for q in added_support):
                    raise NoDerivation("direct-sum extinction: added check outside Q")
                block_root = parent_components[added_support[0]]
                if any(parent_components[q] != block_root for q in added_support):
                    raise NoDerivation("direct-sum extinction: added check spans two blocks")
                block_qs = [q for q in parent_state.Q
                            if parent_components[q] == block_root]
                other_qs = [q for q in parent_state.Q
                            if parent_components[q] != block_root]
                if _restricted_k(new_state, block_qs) != 0:
                    raise NoDerivation(
                        "direct-sum extinction: the gauged block still has logicals "
                        "(k_A' != 0)")
                if not other_qs or _restricted_k(parent_state, other_qs) < 1:
                    raise NoDerivation(
                        "direct-sum extinction: the surviving block has no logical "
                        "(d_B meaningless)")
                # A carried sector lower bound may exceed d_B = min(d_X,B, d_Z,B)
                # (issue: direct-sum extinction monotonicity): tightening a
                # coarse parent ledger to the exact truth must not break a
                # valid derivation. Only the full-distance lower endpoint,
                # which is <= d_B by construction, is checked.
                if out.full.lower is not None and out.full.lower > factor:
                    raise NoDerivation(
                        "direct-sum extinction: full lower bound exceeds d_B")
                extinction_applied = True
                extinction_factor = factor
                out.full = Interval(factor, factor)
                for side in ("X", "Z"):
                    carried = out.sector[side].lower
                    out.sector[side] = (
                        Interval(None, None) if carried is None
                        else Interval(max(carried, factor), None)
                    )
                out.conditions.append({"cell": "C-ADD-CHECK direct-sum extinction",
                                       "status": "conditional",
                                       "rank_check": "computed (tanner components + k drop)",
                                       "evidence": evidence})
            # Given both sector lower endpoints, the full-distance lower
            # endpoint may be raised to their minimum: d = min(d_X, d_Z) is
            endpoint_X = out.sector["X"].lower
            endpoint_Z = out.sector["Z"].lower
            if endpoint_X is not None and endpoint_Z is not None:
                current_lower = 0 if out.full.lower is None else out.full.lower
                new_lower = max(current_lower, min(endpoint_X, endpoint_Z))
                # A stale parent upper endpoint must not make a true
                if out.full.upper is not None and new_lower > out.full.upper:
                    out.full = Interval(new_lower, None)
                else:
                    out.full = Interval(new_lower, out.full.upper)
        elif op == "C-DELETE-CHECK":
            out.full = Interval(0, self.full.upper)
            out.sector = {side: Interval(0, self.sector[side].upper)
                          for side in ("X", "Z")}
            price = hypothesis.get("deletion_price")
            if price is not None:
                if not isinstance(price, dict):
                    raise NoDerivation("priced deletion hypothesis must be an object")
                if not isinstance(price.get("evidence"), str) or not price["evidence"].strip():
                    raise NoDerivation("priced deletion requires an evidence reference")
                values = (price.get("w_del"), price.get("w_exp"))
                if any(not isinstance(value, int) or isinstance(value, bool) or value <= 0
                       for value in values):
                    raise NoDerivation("priced deletion requires positive integer minima")
                w_del, w_exp = values
                if parent_state is None:
                    raise NoDerivation(
                        "priced deletion requires parent_state to identify the "
                        "deleted row's sector")
                row_id = operation.get("row_id")
                if row_id is None:
                    row_id = operation.get("id")
                row = None
                for candidate in getattr(parent_state, "rows", ()):
                    if getattr(candidate, "id", None) == row_id:
                        row = candidate
                        break
                if row is None:
                    raise NoDerivation(
                        "priced deletion: deleted row %r not found in "
                        "parent_state" % row_id)
                tau = getattr(row, "sector", None)
                if tau not in ("X", "Z"):
                    raise NoDerivation(
                        "priced deletion: deleted row has no X/Z sector")
                for key in ("sector", "deleted_sector"):
                    supplied = operation.get(key)
                    if (isinstance(supplied, str) and supplied in ("X", "Z")
                            and supplied != tau):
                        raise NoDerivation(
                            "priced deletion: operation %r sector %r disagrees "
                            "with the deleted row's sector %r"
                            % (key, supplied, tau))
                other = "Z" if tau == "X" else "X"
                for side, pval in ((tau, w_del), (other, w_exp)):
                    low = _min_upper(self.sector[side].lower, pval)
                    high = _min_upper(self.sector[side].upper, pval)
                    out.sector[side] = Interval(low, high)
                low = _min_upper(self.full.lower, min(values))
                high = _min_upper(self.full.upper, min(values))
                out.full = Interval(low, high)
                out.conditions.append({"cell": "C-DELETE-CHECK priced",
                                       "status": "conditional",
                                       "evidence": price["evidence"],
                                       "deleted_sector": tau,
                                       "exposure_sector": other})
        elif op == "E-GRAFT":
            # Sector-wise graft price (code-deformation row 28.2 under the
            # corrected rules of OPERATIONAL_SEMANTICS.md §4.13):
            #   d'_sigma = min(d_sigma, w_expose,sigma) for the non-spliced
            #   sector; the spliced sector carries its lower endpoint only and
            #   drops its upper endpoint to +inf unless a child-valid witness
            #   supplies one. The scalar form d' = min(d, w_expose,tau_bar)
            #   (d' <= d) is refuted for this transition; see §4.13.
            # The non-spliced sector is where exposure happens: its lower
            # endpoint resets to zero and its upper endpoint carries, since
            # d'_sigma <= d_sigma for that sector.
            out.full = Interval(0, None)
            tau = operation["sector"]
            other = "Z" if tau == "X" else "X"
            out.sector[tau] = Interval(self.sector[tau].lower, None)
            out.sector[other] = Interval(0, self.sector[other].upper)
            price = hypothesis.get("graft_price")
            if price is not None:
                if not isinstance(price, dict):
                    raise NoDerivation("graft price hypothesis must be an object")
                value = price.get("w_expose")
                if (not isinstance(value, int) or isinstance(value, bool) or value < 0
                        or not isinstance(price.get("evidence"), str)
                        or not price["evidence"].strip()):
                    raise NoDerivation("graft price needs a nonnegative exposure minimum and evidence")
                # The exposure price is indexed to the **non-spliced**
                # sector, so it licenses that sector's exact interval as
                # well as the full distance. The spliced sector needs no
                # price and gets none.
                out.full = Interval(
                    _min_upper(self.full.lower, value),
                    value,
                )
                out.sector[other] = Interval(
                    _min_upper(self.sector[other].lower, value),
                    _min_upper(self.sector[other].upper, value),
                )
                out.conditions.append({"cell": "E-GRAFT price",
                                       "status": "conditional",
                                       "evidence": price["evidence"],
                                       "exposure_sector": other})
        elif op == "P-REBASE":
            # The row spaces are unchanged in both sectors (§4.26), so every
            # span-expressible endpoint and every witness stays valid; the
            # display-relative properties are recomputed elsewhere and need
            # no ledger action.
            out.conditions.append({"cell": "P-REBASE", "status": "structural",
                                   "sector": operation.get("sector")})
        elif op == "E-LOCAL-HADAMARD":
            if parent_state is None:
                raise NoDerivation("E-LOCAL-HADAMARD transport needs the parent state")
            qubits = sorted(operation.get("qubits", []))
            if len(set(qubits)) != len(qubits):
                raise Malformed(
                    "E-LOCAL-HADAMARD lists a qubit label twice; a list with "
                    "repeats does not name a subset")
            if set(qubits) != set() and set(qubits) != set(parent_state.Q):
                # The transport is only licensed where the state transition is
                # derivable (spec/TERM_LANGUAGE.md §2): T = Q or T = ∅, and
                # inapplicable otherwise. Swapping the sector intervals of a
                # proper subset T ⊊ Q would carry a judgment the transition
                raise NoDerivation(
                    "E-LOCAL-HADAMARD transport is admitted only for the T=Q "
                    "sector exchange and the T=∅ identity "
                    "(spec/OPERATIONAL_SEMANTICS.md §2, §4.27)")
            if qubits:
                # §4.27: the full distance carries exactly (d' = d,
                # weight-preserving conjugation), and the sector distances
                # exchange exactly (d'_X = d_Z, d'_Z = d_X). Witnesses swap
                # sides and are then revalidated against the child by the
                # shared tail below.
                out.full = self.full
                out.sector = {"X": self.sector["Z"], "Z": self.sector["X"]}
                out.witnesses = {
                    "X": [_copy_small_mapping(w) for w in self.witnesses["Z"]],
                    "Z": [_copy_small_mapping(w) for w in self.witnesses["X"]],
                }
            # T = ∅ is the identity on the state (card); the ledger carries
            # unchanged.
            out.conditions.append({"cell": "E-LOCAL-HADAMARD sector swap",
                                   "status": "structural",
                                   "qubits": qubits})
        elif op == "E-PEEL":
            selected = operation.get("sector")
            other = ("Z" if selected == "X" else "X") if selected in ("X", "Z") else None
            if lower_bound_mode not in ("reset", "direction2"):
                raise Malformed("unknown lower_bound_mode %r; expected "
                                "'reset' or 'direction2'" % lower_bound_mode)
            if lower_bound_mode == "reset":
                # Opt-out: the pre-admission refusal (everything resets).
                out.full = Interval(0, None)
                out.sector = {side: Interval(0, None) for side in ("X", "Z")}
                out.conditions.append({"cell": "E-PEEL", "status": "structural",
                                       "selected_sector": operation.get("sector")})
            else:
                # Admitted ( ratified 2026-11-06; sharpened
                # 2026-11-10): §4.28 derives, for the selected
                # sector tau, d_tau' = w_avoid,tau(q) >= d_tau (the lightest
                # parent tau logical avoiding q), and for the opposite sector
                # sigma, d_sigma' = min(d_sigma, w_expose,sigma(q)), the
                # graft's exposure relation at m = 1, so that
                # d_sigma - 1 <= d_sigma' <= d_sigma. Unpriced: the selected
                # lower endpoint carries, the opposite lower endpoint carries
                # less one, the opposite upper endpoint carries, and the full
                # distance takes the minimum of the two sector endpoints
                # (d' = min(d_tau', d_sigma') >= min(d_tau, d_sigma - 1)).
                # Priced (`peel_price`): `w_expose` moves the opposite
                # sector's endpoints as the graft price does, and `w_avoid`
                # pins the selected sector exactly. Recorded as a structural
                # cell, plus a conditional cell when a price is supplied.
                if selected in ("X", "Z"):
                    sel_lower = self.sector[selected].lower
                    opp_lower = self.sector[other].lower
                    opp_lower_less_one = (None if opp_lower is None
                                          else max(opp_lower - 1, 0))
                    opp_upper = self.sector[other].upper
                    sel = Interval(sel_lower, None)
                    opp = _transport_interval(opp_lower_less_one, opp_upper)
                    price = hypothesis.get("peel_price")
                    if price is not None:
                        if not isinstance(price, dict):
                            raise NoDerivation("peel price hypothesis must be an object")
                        evidence = price.get("evidence")
                        if not isinstance(evidence, str) or not evidence.strip():
                            raise NoDerivation("peel price requires an evidence reference")
                        w_expose = price.get("w_expose")
                        w_avoid = price.get("w_avoid")
                        if w_expose is None and w_avoid is None:
                            raise NoDerivation("peel price needs w_expose, w_avoid, or both")
                        if w_expose is not None and (not isinstance(w_expose, int)
                                                     or isinstance(w_expose, bool)
                                                     or w_expose < 0):
                            raise NoDerivation("peel price w_expose must be a nonnegative integer")
                        if w_avoid is not None and (not isinstance(w_avoid, int)
                                                    or isinstance(w_avoid, bool)
                                                    or w_avoid <= 0):
                            raise NoDerivation("peel price w_avoid must be a positive integer")
                        if w_expose is not None:
                            # d_sigma' = min(d_sigma, w_expose): the price is
                            # indexed to the opposite sector, as the graft's.
                            opp = _transport_interval(
                                _min_upper(opp_lower, w_expose),
                                _min_upper(opp_upper, w_expose))
                        if w_avoid is not None:
                            # d_tau' = w_avoid exactly; a value below the
                            # carried selected lower bound contradicts §4.28
                            # and is refused, not widened.
                            if sel_lower is not None and w_avoid < sel_lower:
                                raise NoDerivation(
                                    "peel price w_avoid %d is below the carried "
                                    "selected-sector lower bound %d" % (w_avoid, sel_lower))
                            sel = Interval(w_avoid, w_avoid)
                        out.conditions.append({
                            "cell": "E-PEEL price", "status": "conditional",
                            "evidence": evidence, "selected_sector": selected,
                            "exposure_sector": other,
                            "w_expose": w_expose, "w_avoid": w_avoid})
                    out.sector = {selected: sel, other: opp}
                    # d' = min(d_tau', d_sigma'): both endpoints are minima of
                    # the sector endpoints (`_min_upper` reads None as +inf,
                    # which is the k = 0 reading of a missing lower bound).
                    out.full = _transport_interval(
                        _min_upper(sel.lower, opp.lower),
                        _min_upper(sel.upper, opp.upper))
                else:
                    out.full = Interval(0, None)
                    out.sector = {side: Interval(0, None) for side in ("X", "Z")}
                out.conditions.append({"cell": "E-PEEL", "status": "structural",
                                       "carried": "selected-lower,opposite-lower-less-one,"
                                                  "opposite-upper,full-min",
                                       "selected_sector": selected})
        elif op == "E-PUNCTURE":
            # §4.29: same disposition as the peel -- no distance rule
            # carries; in particular even the qubit-named-by-no-row instance
            # can raise the minimum (the deleted qubit's own free logical
            # can be the parent's lightest). Reset + child-witness uppers.
            out.full = Interval(0, None)
            out.sector = {side: Interval(0, None) for side in ("X", "Z")}
            out.conditions.append({"cell": "E-PUNCTURE", "status": "structural"})
        elif op == "E-EXTEND":
            if parent_state is None:
                raise NoDerivation("E-EXTEND transport needs the parent state")
            new_qubits = tuple(operation.get("new_qubits", ()))
            additions = list(operation.get("additions", ()))
            added_sectors = {record[0] for record in additions if record}
            if new_qubits:
                # §4.30: with a namespace change no distance rule is derivable;
                # every interval resets its lower endpoint and only
                # child-valid witnesses supply upper endpoints.
                out.full = Interval(0, None)
                out.sector = {side: Interval(0, None) for side in ("X", "Z")}
            else:
                # Δ = ∅: treated exactly as a C-ADD-CHECK sequence (§4.30):
                # carry the lower endpoints and rebuild every upper endpoint
                # from child-valid witnesses. Adding a check can only raise a
                # distance, and the carried (pre-change) upper endpoint is not
                # a sound bound for the child.
                out.full = Interval(self.full.lower, None)
                out.sector = {side: Interval(self.sector[side].lower, None)
                              for side in ("X", "Z")}
            out.conditions.append({"cell": "E-EXTEND", "status": "structural",
                                   "new_qubits": list(new_qubits),
                                   "additions": len(additions)})
        elif op == "E-GLUE":
            right_ledger = (operation.get("right_ledger")
                            or operation.get("right")
                            or operation.get("other_ledger"))
            if right_ledger is None and isinstance(hypothesis, dict):
                right_ledger = (hypothesis.get("right_ledger")
                                or hypothesis.get("right")
                                or hypothesis.get("other_ledger"))
            if not isinstance(right_ledger, DistanceLedger):
                raise Malformed("E-GLUE propagate requires a right_ledger DistanceLedger")
            seam_certificate = (operation.get("seam_certificate")
                                or operation.get("certificate")
                                or operation.get("seam"))
            if seam_certificate is None and isinstance(hypothesis, dict):
                seam_certificate = (hypothesis.get("seam_certificate")
                                    or hypothesis.get("certificate")
                                    or hypothesis.get("seam"))
            out = self.glue(right_ledger, hypothesis=hypothesis,
                            seam_certificate=seam_certificate,
                            child_state=new_state)
            out.conditions = list(out.conditions)
        else:
            raise Malformed("unknown operation %s" % op)

        for side in ("X", "Z"):
            out.witnesses[side] = out._valid_witnesses(new_state, side)
            observed = observations.get(side)
            if observed:
                out.record_witness(new_state, side, observed,
                                   source="supplied post-step logical witness")
                out.witnesses[side] = out._valid_witnesses(new_state, side)
            upper = min((w["value"] for w in out.witnesses[side]), default=None)
            current = out.sector[side]
            delta_empty_extend = (op == "E-EXTEND"
                                     and not tuple(operation.get("new_qubits", ())))
            if op == "C-ADD-CHECK" or delta_empty_extend:
                # Old upper endpoints are stale; rebuild from witnesses only.
                out.sector[side] = _transport_interval(current.lower, upper)
            else:
                # Carry the licensed upper endpoint and tighten with
                # witnesses. A witness is only ever an upper bound: it may
                # tighten what the transition rule proved, and never widen or
                # discard it -- not even when the caller supplies it as an
                # observation.
                out.sector[side] = _transport_interval(
                    current.lower, _min_upper(current.upper, upper)
                )

        if new_state.k() == 0:
            out.full = Interval(None, None)
            out.sector = {side: Interval(None, None) for side in ("X", "Z")}
        else:
            sector_upper = _min_upper(out.sector["X"].upper, out.sector["Z"].upper)
            if op == "C-ADD-CHECK":
                out.full = _transport_interval(out.full.lower, sector_upper)
            else:
                out.full = _transport_interval(
                    out.full.lower, _min_upper(out.full.upper, sector_upper)
                )
        if extinction_applied and new_state.k() != 0:
            out.full = Interval(out.full.lower, extinction_factor)
        return out

    def decide(self, target):
        if (not isinstance(target, int) or isinstance(target, bool)
                or target < 1):
            raise Malformed("target must be a positive integer")
        if self.full.lower is None or self.full.lower >= target:
            return "certify"
        # spec/JUDGMENT_LAYER.md section 2b: `prune` when the upper endpoint
        # is finite and below the target, and nothing else.  The verdict reads
        # the interval only.  A witness confidence label is a record of search
        # depth and does not gate it (issue #632): every upper endpoint in a
        # ledger already comes from a validated witness or a licensed rule.
        if self.full.upper is not None and self.full.upper < target:
            return "prune"
        return "re-measure"

    def has_deep_witness(self):
        """Whether some carried witness is labeled ``deep``.  Descriptive:
        no verdict reads it."""
        return self._has_deep_witness()

    def _has_deep_witness(self):
        for side in ("X", "Z"):
            for witness in self.witnesses.get(side, []):
                if isinstance(witness, dict) and witness.get("confidence") == "deep":
                    return True
        return False

    def as_json(self):
        return {
            "d": self.full.as_json(),
            "d_X": self.sector["X"].as_json(),
            "d_Z": self.sector["Z"].as_json(),
            "conditional_inputs": list(self.conditions),
            "witnesses": _copy_witnesses(self.witnesses),
        }

    @staticmethod
    def direct_sum(left, right):
        def min_intervals(a, b):
            lower = _min_upper(a.lower, b.lower)
            upper = _min_upper(a.upper, b.upper)
            return Interval(lower, upper)

        return DistanceLedger(
            min_intervals(left.full, right.full),
            {side: min_intervals(left.sector[side], right.sector[side])
             for side in ("X", "Z")},
            {"X": [], "Z": []},
            left.conditions + right.conditions,
        )

    def glue(self, other, hypothesis=None, seam_certificate=None, child_state=None,
             **kwargs):
        """E-GLUE ledger transport: min of the two factor intervals, conditional
        on an admissible seam certificate (JUDGMENT_LAYER.md section 2e).

        ``child_state`` is the glued state. When it is supplied, both factors'
        witnesses are carried into the child and kept only where they are
        still logical there (section 2c: a witness certifies an upper bound in
        the state it is validated in), so the X and full upper endpoints, which
        the seam certificate never licenses, come from surviving factor
        witnesses, and a surviving minimum-weight Z witness closes the Z
        interval without the certificate's claim (OPERATIONAL_SEMANTICS.md
        section 4.31, instance-wise equality, 2026-11-10). Without a child
        state no witness is carried: a factor witness may fail to commute with
        a seam check or be absorbed into the glued span, and an unrevalidated
        witness must not be presented as current.
        """
        left = self
        right = other
        if not isinstance(left, DistanceLedger) or not isinstance(right, DistanceLedger):
            raise Malformed("E-GLUE requires two DistanceLedger inputs")
        if child_state is not None and not isinstance(child_state, CodeState):
            raise Malformed("E-GLUE child_state must be a CodeState")
        hypothesis = hypothesis or kwargs.get("hypothesis") or {}
        if not isinstance(hypothesis, dict):
            raise Malformed("E-GLUE hypothesis must be an object")
        if seam_certificate is None:
            seam_certificate = (hypothesis.get("seam_certificate")
                                or hypothesis.get("seam")
                                or hypothesis.get("certificate")
                                or kwargs.get("seam_certificate")
                                or kwargs.get("certificate"))
        # Allow the certificate to be carried directly in the hypothesis.
        if seam_certificate is None and any(k in hypothesis for k in
                ("move_word_A", "move_word_B", "move_words", "word_A", "word_B",
                 "c_A", "c_B")):
            seam_certificate = hypothesis
        has_certificate = isinstance(seam_certificate, dict)
        if seam_certificate is not None and not has_certificate:
            raise Malformed("E-GLUE seam certificate must be an object")

        # E-GLUE is refused without an admissible seam certificate, even
        # though its lower endpoints are sound without one.
        if not has_certificate:
            raise NoDerivation("E-GLUE requires an admissible seam certificate")

        word_a = None
        word_b = None
        evidence = None
        if has_certificate:
            words = seam_certificate.get("move_words", seam_certificate.get("words"))
            word_a = seam_certificate.get("move_word_A")
            if word_a is None:
                word_a = seam_certificate.get("word_A", seam_certificate.get("word_a",
                          seam_certificate.get("c_A", seam_certificate.get("move_word_a"))))
            word_b = seam_certificate.get("move_word_B")
            if word_b is None:
                word_b = seam_certificate.get("word_B", seam_certificate.get("word_b",
                          seam_certificate.get("c_B", seam_certificate.get("move_word_b"))))
            if words is not None and (word_a is None or word_b is None):
                if isinstance(words, (list, tuple)) and len(words) == 2:
                    word_a, word_b = words
            if not (isinstance(word_a, str) and isinstance(word_b, str)):
                raise Malformed("E-GLUE seam certificate move words must be strings")
            if not (all(ch in "UDLR" for ch in word_a)
                    and all(ch in "UDLR" for ch in word_b)):
                raise Malformed("E-GLUE seam certificate move words must be "
                                "strings over {U,D,L,R}^*")
            if word_a != word_b:
                raise NoDerivation("E-GLUE seam certificate is inadmissible: move words differ")
            evidence = seam_certificate.get("evidence", seam_certificate.get("source"))
            if not (isinstance(evidence, str) and evidence.strip()):
                raise NoDerivation("E-GLUE seam certificate requires an evidence reference")

        # Lower endpoints are sound without any certificate (adding seam
        # checks never lowers a distance); the seam certificate of §2e
        # licenses only the Z sector's upper endpoint, d_Z(Q) =
        # min(d_A, d_B). The X and full upper endpoints are not licensed
        # and are left to child-valid witnesses.
        merged_full_lower = _min_upper(left.full.lower, right.full.lower)
        # The factors' witnesses, revalidated in the glued child. A witness
        # of a factor is a candidate only: an X seam check can anticommute
        # with a factor's Z witness, and a seam row can pull a factor witness
        # into the glued span, so each is checked in the child before it is
        # kept (section 4.31, instance-wise equality).
        carried = {"X": [], "Z": []}
        if child_state is not None:
            for side in ("X", "Z"):
                seen = set()
                for witness in left.witnesses[side] + right.witnesses[side]:
                    support = tuple(sorted(witness["support"]))
                    try:
                        validate_witness(child_state, side, support, witness["value"])
                    except NoDerivation:
                        continue
                    if support in seen:
                        continue
                    seen.add(support)
                    carried[side].append({
                        "support": list(support), "value": witness["value"],
                        "source": "factor witness revalidated in the glued child"})
        sectors = {"X": Interval(_min_upper(left.sector["X"].lower,
                                            right.sector["X"].lower), None),
                   "Z": Interval(_min_upper(left.sector["Z"].lower,
                                            right.sector["Z"].lower),
                                 _min_upper(left.sector["Z"].upper,
                                            right.sector["Z"].upper))}
        for side in ("X", "Z"):
            witness_upper = min((w["value"] for w in carried[side]), default=None)
            sectors[side] = _transport_interval(
                sectors[side].lower, _min_upper(sectors[side].upper, witness_upper))
        merged = DistanceLedger(
            _transport_interval(merged_full_lower,
                                _min_upper(sectors["X"].upper, sectors["Z"].upper)),
            sectors,
            carried,
            left.conditions + right.conditions,
        )
        if has_certificate:
            merged.conditions.append({
                "cell": "E-GLUE seam certificate",
                "status": "conditional",
                "move_word": word_a,
                "evidence": evidence,
            })
        try:
            from machine import entrypoints as _ep
        except Exception:
            try:
                import entrypoints as _ep
            except Exception:
                _ep = None
        if _ep is not None:
            hyp = hypothesis if isinstance(hypothesis, dict) else {}
            combined = {}
            if isinstance(seam_certificate, dict):
                combined.update(seam_certificate)
            combined.update(hyp)
            criteria_keys = ("odd_cycle", "has_odd_cycle", "bipartite",
                             "is_bipartite", "union_layout", "union_layout_bipartite",
                             "seam_graph", "signatures_agree", "signature_agree",
                             "boundary_signatures", "boundary_signatures_agree",
                             "signature_A", "signature_a", "signature_B",
                             "signature_b", "monotone", "monotone_top_to_bottom",
                             "top_to_bottom", "move_word_A", "move_word_B",
                             "move_word_a", "move_word_b", "word_A", "word_B",
                             "words", "move_words", "evidence", "source")
            supplied = any(k in combined for k in criteria_keys)
            if supplied:
                records, overall = _ep.positive_composition_criteria(
                    seam_certificate=combined)
                for rec in (records or []):
                    merged.conditions.append({
                        "cell": "E-GLUE %s" % rec.get("criterion", "positive composition"),
                        "status": "conditional",
                        "criterion": rec.get("criterion"),
                        "verdict": rec.get("verdict"),
                        "hypothesis": rec.get("hypothesis"),
                        "admissible": rec.get("admissible", False),
                        "inconclusive": rec.get("inconclusive", False),
                        "bound": rec.get("bound"),
                        "odd_cycle_table_omitted": True,
                        "certificate_producer_incomplete": True,
                        "circuit_preservation": "empirical",
                    })
                if overall:
                    merged.conditions.append({
                        "cell": "E-GLUE positive composition criteria",
                        "status": "conditional",
                        "verdicts": overall.get("verdicts"),
                        "all_admissible": overall.get("all_admissible", False),
                        "any_inconclusive": overall.get("any_inconclusive", False),
                        "odd_cycle_table_omitted": True,
                        "certificate_producer_incomplete": True,
                        "circuit_preservation": "empirical",
                    })
        return merged

    e_glue = glue

    def equal_syndrome_weight_floor(self) -> Optional[int]:
        """Lower bound ceil(L_d / 2) on the equal-syndrome generator weight
        omega(C), transported by weakening (spec/JUDGMENT_LAYER.md §2h).

        Returns None (+infinity) when the full-distance lower endpoint is None
        (k = 0), and (L_d + 1) // 2 otherwise. Re-read at each state from the
        current full-distance lower endpoint, never substituted from a parent.
        """
        if self.full.lower is None:
            return None
        return (self.full.lower + 1) // 2

def validate_witness(state, side, support, claimed_weight):
    if side not in ("X", "Z"):
        raise Malformed("witness side must be X or Z")
    if len(set(support)) != len(support) or not set(support) <= set(state.Q):
        raise NoDerivation("witness support is not a subset of Q")
    if len(support) != claimed_weight or not support:
        raise NoDerivation("witness weight does not match its support")
    vector = support_mask(support)
    same = "X" if side == "X" else "Z"
    opposite = "Z" if side == "X" else "X"
    if not commutes(vector, [row.mask for row in state.sector_rows(opposite)]):
        raise NoDerivation("witness does not commute with opposite-sector checks")
    if in_span(vector, [row.mask for row in state.sector_rows(same)]):
        raise NoDerivation("witness lies in the same-sector stabilizer span")
    return True

def _sector_interval_key(interval):
    """Order carried sector intervals for a consumer that wants the sector's
    distance large: by lower endpoint, then by upper endpoint, ``None``
    reading as +inf at either end (the vacuous k = 0 interval is the
    strongest lower endpoint; an unbounded upper endpoint is the loosest)."""
    lower = float("inf") if interval.lower is None else interval.lower
    upper = float("inf") if interval.upper is None else interval.upper
    return (lower, upper)


__all__ = [
    'Interval',
    '_min_upper',
    '_transport_interval',
    '_copy_small_mapping',
    '_copy_witnesses',
    '_copy_conditions',
    'DistanceLedger',
    'validate_witness',
    '_sector_interval_key',
]
