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
from machine.intervals import *
from machine.constructors import *
from machine.sequence import *

def _main(argv=None):
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("parent", help="qLDPC challenge JSON file")
    parser.add_argument("plan", help="JSON file with operations, lower_bounds, target")
    parser.add_argument("output", help="path for the generated qLDPC JSON")
    parser.add_argument("--ledger", help="optional path for the local interval ledger")
    args = parser.parse_args(argv)
    with open(args.parent) as source:
        parent = json.load(source)
    with open(args.plan) as plan_file:
        plan = json.load(plan_file)
    state, ledger, trace = run_sequence(
        parent, plan.get("operations", []), plan.get("lower_bounds"), plan.get("target")
    )
    output = export_challenge_entry(
        parent, state, ledger, plan["name"], plan["construction"], plan["date"]
    )
    with open(args.output, "w") as target_file:
        json.dump(output, target_file, indent=2)
        target_file.write("\n")
    report = {"trace": trace, "ledger": ledger.as_json(),
              "n": state.n(), "k": state.k()}
    radius_squared = radius_squared_in_layout(parent, state)
    report["geometry"] = {
        "interaction_radius": None if radius_squared is None
        else radius_nearest_decimal(radius_squared, 6),
        "locality_class": locality_class(radius_squared, layout_layers(parent),
                                        planar=layout_planar(parent),
                                        honest=layout_honest(parent)),
        "layers": layout_layers(parent),
    }
    if args.ledger:
        with open(args.ledger, "w") as ledger_file:
            json.dump(report, ledger_file, indent=2)
            ledger_file.write("\n")
    print(json.dumps(report, indent=2))
    return 0

HEURISTIC_OUTCOME_SOURCE = (
    "spec/CLAIMS.md, Admission (2026-11-11, issue #329): the probabilistic claim "
    "shape as the recorded form of a heuristic search outcome")

def heuristic_outcome(procedure, universe, evaluated, *, budget=None, exhausted=None,
                      found=False, delta=0.0, weight=None, statement=None):
    """A heuristic search outcome in the admitted ``probabilistic`` claim shape.

    `spec/CLAIMS.md` (*Admission*, 2026-11-11, issue #329) admits the
    ``probabilistic`` claim shape as the recorded form of a search outcome: a
    claim about the search, never about the code. The record names the
    procedure, the universe it ranged over, how much of that universe was
    evaluated, the budget and whether it was exhausted, the failure
    probability ``delta`` (``0`` for a deterministic search over the stated
    universe), the weight searched when there is one, and whether a survivor
    or witness was found. Its evidence status is ``empirical`` (supported by
    computation). It licenses no ledger endpoint: a negative outcome leaves an
    ``unavailable`` claim in place and is never presented as a lower bound.
    Consumers attach it to a verdict; nothing in the ledger reads it.
    """
    if not isinstance(procedure, str) or not procedure.strip():
        raise Malformed("heuristic outcome needs a procedure description")
    if not isinstance(universe, str) or not universe.strip():
        raise Malformed("heuristic outcome needs a universe description")
    if not isinstance(evaluated, int) or isinstance(evaluated, bool) or evaluated < 0:
        raise Malformed("heuristic outcome evaluated count must be a non-negative integer")
    if budget is not None and (not isinstance(budget, int) or isinstance(budget, bool)
                               or budget < 1):
        raise Malformed("heuristic outcome budget must be a positive integer or None")
    if exhausted is not None and not isinstance(exhausted, bool):
        raise Malformed("heuristic outcome exhausted flag must be a bool or None")
    if isinstance(delta, bool) or not isinstance(delta, (int, float, Fraction)) \
            or not (0 <= delta <= 1):
        raise Malformed("heuristic outcome delta must lie in [0, 1]")
    if weight is not None and (not isinstance(weight, int) or isinstance(weight, bool)
                               or weight < 1):
        raise Malformed("heuristic outcome weight must be a positive integer or None")
    found = bool(found)
    if statement is None:
        statement = "survivor found" if found else "no survivor found"
        if weight is not None:
            statement += " up to weight %d" % weight
        statement += " among the %d candidates evaluated" % evaluated
    return {
        "claim_shape": "probabilistic",
        "evidence_status": "empirical",
        "event": {
            "procedure": procedure,
            "universe": universe,
            "evaluated": evaluated,
            "budget": budget,
            "exhausted": exhausted,
            "weight": weight,
        },
        "delta": delta,
        "found": found,
        "statement": statement,
        "licenses": ("no ledger endpoint; an unavailable claim stays unavailable and "
                     "no lower bound is presented"),
        "source": HEURISTIC_OUTCOME_SOURCE,
    }

def admissible_added_checks(state, *, max_weight=8, sectors=("X", "Z")):
    """Yield ``(support, sector)`` pairs admissible for ``C-ADD-CHECK``.

    A candidate passes when its support lies in ``Q``, commutes with every
    displayed row of the opposite sector, and lies outside the span of the
    displayed rows of its own sector.  Weights run from 1 to ``max_weight``
    (capped at ``n``); within a weight, combinations are lexicographic in
    the sorted qubit labels.  This is the cheap enumeration a campaign needs
    to construct valid ``C-ADD-CHECK`` strict-improvement instances, instead
    of guessing supports that the cell rejects.  Machine-side only.
    """
    labels = sorted(state.Q)
    n = len(labels)
    if n == 0:
        return
    cap = min(max_weight, n)
    for sector in sectors:
        other = "Z" if sector == "X" else "X"
        same_rows = [row.mask for row in state.sector_rows(sector)]
        other_rows = [row.mask for row in state.sector_rows(other)]
        for weight in range(1, cap + 1):
            for combo in itertools.combinations(labels, weight):
                mask = support_mask(combo)
                if not commutes(mask, other_rows):
                    continue
                if in_span(mask, same_rows):
                    continue
                yield (list(combo), sector)

def bare_logical_qubits(state, sector):
    """Qubits whose singleton support is a logical operator in ``sector``."""
    other = opposite_sector_name(sector)
    same_rows = [row.mask for row in state.sector_rows(sector)]
    other_rows = [row.mask for row in state.sector_rows(other)]
    result = []
    for q in state.Q:
        mask = 1 << q
        if commutes(mask, other_rows) and not in_span(mask, same_rows):
            result.append(q)
    return result

def _fix_support_solve(state, bare_set, added_sector, *, samples=300, rng_seed=0):
    labels = sorted(state.Q)
    Bset = set(bare_set)
    if not Bset <= set(labels):
        raise Malformed("bare set must be a subset of Q")
    added_sector = added_sector if added_sector in ("X", "Z") else None
    if added_sector is None:
        raise Malformed("added_sector must be 'X' or 'Z'")
    logical_sector = opposite_sector_name(added_sector)
    rows_L = [row.mask for row in state.sector_rows(logical_sector)]
    rows_A = [row.mask for row in state.sector_rows(added_sector)]

    Bmask = 0
    for q in Bset:
        Bmask |= 1 << q
    # Inconsistency: a row of the logical sector contained in B with odd parity.
    for row_mask in rows_L:
        if row_mask and (row_mask & ~Bmask) == 0:
            if (row_mask & Bmask).bit_count() % 2 != 0:
                return {"support": None, "weight": None, "status": "inconsistent",
                        "reason": "inconsistent",
                        "boundary": "no single-check fix exists (row r ⊆ B, odd parity)",
                        "inconsistent_row": row_mask, "inconsistent_row_mask": row_mask,
                        "e": None, "bare_set": sorted(Bset), "sector": added_sector}

    complement = [q for q in labels if q not in Bset]

    def constraints_ok(e_mask):
        for row_mask in rows_L:
            if ((e_mask & row_mask).bit_count() % 2
                    != (Bmask & row_mask).bit_count() % 2):
                return False
        return True

    def independent(Smask):
        return not in_span(Smask, rows_A)

    # Exact for small complements.
    if len(complement) <= 20:
        for w in range(0, len(complement) + 1):
            for combo in itertools.combinations(complement, w):
                e_mask = support_mask(combo)
                if not constraints_ok(e_mask):
                    continue
                Smask = Bmask | e_mask
                if not independent(Smask):
                    continue
                support = sorted(Bset | set(combo))
                return {"support": support, "weight": len(support),
                        "status": "fixed", "reason": "fixed",
                        "boundary": None, "inconsistent_row": None,
                        "inconsistent_row_mask": None,
                        "e": sorted(combo), "bare_set": sorted(Bset),
                        "sector": added_sector, "added_support": support,
                        "fixed_support": support}
        return {"support": None, "weight": None, "status": "no_fix",
                "reason": "no_fix", "boundary": None,
                "inconsistent_row": None, "inconsistent_row_mask": None,
                "e": None, "bare_set": sorted(Bset), "sector": added_sector}

    # Large complement: Gaussian solve + kernel sampling.
    import random as _random
    # variables are complement positions; build matrix over GF(2)
    m = len(rows_L)
    var_count = len(complement)
    # matrix rows: m constraints, var_count cols; rhs b
    A = [[( (1 << complement[i]) & row_mask) >> complement[i] & 1
          for i in range(var_count)] for row_mask in rows_L]
    # actually bit extraction:
    A = []
    for row_mask in rows_L:
        row = []
        for q in complement:
            row.append(1 if (row_mask >> q) & 1 else 0)
        A.append(row)
    b = [ (Bmask & row_mask).bit_count() % 2 for row_mask in rows_L]

    # Gaussian elimination to RREF, track pivots
    M = [row[:] + [b[i]] for i, row in enumerate(A)]
    pivot_cols = []
    r = 0
    nrows = len(M)
    ncols = var_count
    for c in range(ncols):
        # find pivot
        piv = None
        for rr in range(r, nrows):
            if M[rr][c] & 1:
                piv = rr
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        for rr in range(nrows):
            if rr != r and (M[rr][c] & 1):
                M[rr] = [(M[rr][j] ^ M[r][j]) for j in range(ncols + 1)]
        pivot_cols.append(c)
        r += 1
        if r == nrows:
            break
    # consistency check (already handled subset, but for safety)
    for rr in range(r, nrows):
        if M[rr][ncols] & 1:
            # inconsistent
            return {"support": None, "weight": None, "status": "inconsistent",
                    "reason": "inconsistent",
                    "boundary": "no single-check fix exists (row r ⊆ B, odd parity)",
                    "inconsistent_row": None, "inconsistent_row_mask": None,
                    "e": None, "bare_set": sorted(Bset), "sector": added_sector}
    # particular solution: set free vars 0
    x = [0] * var_count
    for i, c in enumerate(pivot_cols):
        x[c] = M[i][ncols] & 1
    # nullspace basis: for each free col, vector with that free var 1 and pivot vars adjusted
    free_cols = [c for c in range(ncols) if c not in pivot_cols]
    null_basis = []
    for fc in free_cols:
        vec = [0] * var_count
        vec[fc] = 1
        for i, c in enumerate(pivot_cols):
            if M[i][fc] & 1:
                vec[c] ^= 1
        mask = 0
        for i, q in enumerate(complement):
            if vec[i]:
                mask |= 1 << q
        null_basis.append(mask)

    particular_mask = 0
    for i, q in enumerate(complement):
        if x[i]:
            particular_mask |= 1 << q

    def mask_of_combo(vec_masks):
        m = particular_mask
        for vm in vec_masks:
            m ^= vm
        return m

    best = None  # (weight, e_mask)
    # try particular
    candidates_masks = [particular_mask]
    # enumerate small nullspace exactly
    if len(null_basis) <= 18:
        for r in range(len(null_basis) + 1):
            for combo in itertools.combinations(range(len(null_basis)), r):
                mm = particular_mask
                for idx in combo:
                    mm ^= null_basis[idx]
                candidates_masks.append(mm)
    else:
        rng = _random.Random(rng_seed)
        candidates_masks.append(particular_mask)
        for _ in range(samples):
            mm = particular_mask
            for nb in null_basis:
                if rng.random() < 0.5:
                    mm ^= nb
            candidates_masks.append(mm)
    # deduplicate
    seen_masks = set()
    unique = []
    for mm in candidates_masks:
        if mm in seen_masks:
            continue
        seen_masks.add(mm)
        unique.append(mm)
    for mm in unique:
        if not constraints_ok(mm):
            continue
        Smask = Bmask | mm
        if not independent(Smask):
            continue
        e_support = [q for q in complement if (mm >> q) & 1]
        weight = len(Bset) + len(e_support)
        if best is None or weight < best[0]:
            best = (weight, mm, e_support)
    if best is None:
        return {"support": None, "weight": None, "status": "no_fix",
                "reason": "no_fix", "boundary": None,
                "inconsistent_row": None, "inconsistent_row_mask": None,
                "e": None, "bare_set": sorted(Bset), "sector": added_sector}
    _, mm, e_support = best
    support = sorted(Bset | set(e_support))
    return {"support": support, "weight": len(support),
            "status": "fixed", "reason": "fixed", "boundary": None,
            "inconsistent_row": None, "inconsistent_row_mask": None,
            "e": sorted(e_support), "bare_set": sorted(Bset),
            "sector": added_sector, "added_support": support,
            "fixed_support": support}

def fix_support(state, bare_set=None, added_sector=None, *, sector=None,
                bare_qubits=None, max_weight=None, samples=300, rng_seed=0,
                **kwargs):
    """GF(2) parity repair for an added-check support.

    Accepts several calling shapes:
      fix_support(state, bare_set, added_sector)
      fix_support(state, added_sector)            # bare set computed
      fix_support(state, sector=..., bare_set=...)
    """
    if isinstance(bare_set, str):
        added_sector = bare_set
        bare_set = None
    if sector is not None:
        added_sector = sector
    if bare_qubits is not None:
        bare_set = bare_qubits
    if added_sector is None:
        # infer from kwargs
        for key in ("added_sector", "check_sector"):
            if key in kwargs:
                added_sector = kwargs.pop(key)
                break
    if added_sector is None:
        added_sector = "X"
    if bare_set is None:
        bare_set = bare_logical_qubits(state, opposite_sector_name(added_sector))
    return _fix_support_solve(state, bare_set, added_sector, samples=samples,
                             rng_seed=rng_seed)

parity_repair = fix_support

repair_support = fix_support

def strict_improvement_feasible(state, added_support, added_sector, base_distance,
                                witnesses=None, ledger=None, *,
                                allow_enumeration=True,
                                enumeration_ceiling=20):
    """Cheap-first feasibility check for the C-ADD-CHECK strict-improvement cell.

    Checks the supplied known witnesses (or a ``DistanceLedger``'s witnesses)
    first: a currently valid weight-``base_distance`` witness that commutes
    with the added check (opposite sector) or stays outside the span of the
    display plus the added check (same sector) is a survivor, and strict
    improvement is impossible (``d' = d``). This is a few linear-algebra
    checks, not a scan.

    If no witness survives and ``allow_enumeration`` is false, returns
    ``all_killed_requires_enumeration``: the supplied witnesses are all
    killed, which says nothing about the weight-``base_distance`` classes
    that were not supplied. With ``allow_enumeration=True`` (the default) the
    weight-``base_distance`` supports are then scanned, ``C(n,
    base_distance)`` of them, refusing codes above ``enumeration_ceiling``
    qubits; a survivor found there returns ``survivor_found``, and a complete
    scan with none returns ``all_killed_by_enumeration``.

    Every result carries ``status`` and ``reason`` (the same token), the
    survivor as a mask with its ``survivor_support`` and ``survivor_sector``,
    the ``source`` of the verdict (``witness`` or ``enumeration``), and an
    ``enumeration`` record (whether it ran and how many supports it
    examined). The added check must be admissible for ``C-ADD-CHECK``
    (support in ``Q``, commuting with the opposite sector, outside the
    same-sector span); otherwise the cell has no instance and
    ``NoDerivation`` is raised. ``all_killed_by_enumeration`` is the
    consumer's own scan, relative to the supplied ``base_distance``; the
    strict-improvement cell still takes its hypothesis from the caller.

    This is a consumer-side feasibility screen. It does not mutate state, does
    not compute a distance, and does not validate the supplied
    ``base_distance`` beyond shape; the caller is responsible for supplying
    the exact old distance. Machine-only: no calculus axis changes.
    """
    if added_sector not in ("X", "Z"):
        raise Malformed("added_sector must be 'X' or 'Z'")
    if not isinstance(base_distance, int) or isinstance(base_distance, bool) or base_distance < 1:
        raise Malformed("base_distance must be a positive integer")
    labels = list(state.Q)
    n = len(labels)
    if base_distance > n:
        raise Malformed("base_distance exceeds the qubit count")
    if n == 0:
        raise Malformed("state has no qubits")

    # Resolve a ledger passed positionally as ``witnesses``.
    if ledger is None and _is_ledger_like(witnesses):
        ledger = witnesses
        witnesses = None

    try:
        added_support = tuple(added_support)
    except TypeError:
        raise Malformed("added_support must be a list of qubit labels")
    if not added_support or len(set(added_support)) != len(added_support):
        raise Malformed("added_support must be nonempty and may not repeat qubits")
    added_label_mask = support_mask(added_support)
    if not set(added_support) <= set(labels):
        raise NoDerivation("added row is not in F_2^Q")

    same_sector = added_sector
    other_sector = "Z" if added_sector == "X" else "X"
    same_rows = [row.mask for row in state.sector_rows(same_sector)]
    other_rows = [row.mask for row in state.sector_rows(other_sector)]
    same_with_added = same_rows + [added_label_mask]
    if not commutes(added_label_mask, other_rows):
        raise NoDerivation("opposite-sector commutation fails for the added check")
    if in_span(added_label_mask, same_rows):
        raise NoDerivation("same-sector independence fails for the added check")

    def _support_of(mask):
        return [q for q in labels if mask >> q & 1]

    def _result(reason, mask, sector, source, examined, heuristic_outcome=None):
        return {"status": reason,
                "reason": reason,
                "survivor": mask,
                "survivor_support": None if mask is None else _support_of(mask),
                "survivor_sector": sector,
                "weight": base_distance,
                "source": source,
                "enumeration": {"performed": examined is not None,
                                "supports_examined": examined or 0,
                                "total": math.comb(n, base_distance)},
                "heuristic_outcome": heuristic_outcome}

    def _mask_of(item):
        if isinstance(item, bool):
            return None
        if isinstance(item, int):
            return item
        if isinstance(item, dict):
            if "mask" in item and isinstance(item["mask"], int):
                return item["mask"]
            if "support" in item:
                try:
                    return support_mask(item["support"])
                except Exception:
                    return None
        if isinstance(item, (list, tuple, set, frozenset)):
            try:
                return support_mask(item)
            except Exception:
                return None
        return None

    def _value_of(item):
        if isinstance(item, dict):
            value = item.get("value", item.get("weight"))
            if isinstance(value, int) and not isinstance(value, bool):
                return value
        return None

    def _collect(ledger_obj, witnesses_obj):
        collected = []  # (side or None, mask, value or None)
        if ledger_obj is not None:
            if hasattr(ledger_obj, "_valid_witnesses"):
                for side in ("X", "Z"):
                    try:
                        for w in ledger_obj._valid_witnesses(state, side):
                            collected.append((side, _mask_of(w), _value_of(w)))
                    except Exception:
                        continue
            elif hasattr(ledger_obj, "witnesses") and isinstance(ledger_obj.witnesses, dict):
                for side in ("X", "Z"):
                    for w in ledger_obj.witnesses.get(side, []):
                        collected.append((side, _mask_of(w), _value_of(w)))
            elif isinstance(ledger_obj, dict):
                if "X" in ledger_obj or "Z" in ledger_obj:
                    for side in ("X", "Z"):
                        for w in ledger_obj.get(side, []):
                            collected.append((side, _mask_of(w), _value_of(w)))
                elif "witnesses" in ledger_obj:
                    collected.extend(_collect(None, ledger_obj["witnesses"]))
        if witnesses_obj is not None:
            if isinstance(witnesses_obj, dict):
                if "X" in witnesses_obj or "Z" in witnesses_obj:
                    for side in ("X", "Z"):
                        for w in witnesses_obj.get(side, []):
                            collected.append((side, _mask_of(w), _value_of(w)))
                elif "witnesses" in witnesses_obj:
                    collected.extend(_collect(None, witnesses_obj["witnesses"]))
            elif isinstance(witnesses_obj, (list, tuple, set, frozenset)):
                for w in witnesses_obj:
                    collected.append((None, _mask_of(w), _value_of(w)))
        return collected

    candidates = _collect(ledger, witnesses)

    survivor = None
    survivor_sector = None
    for side, mask, value in candidates:
        if mask is None:
            continue
        # Only a support of weight exactly base_distance can witness d' = d;
        # a claimed value that disagrees with the support is not trusted.
        if mask.bit_count() != base_distance:
            continue
        if value is not None and value != base_distance:
            continue
        try_sides = [side] if side in ("X", "Z") else ["X", "Z"]
        for wside in try_sides:
            if wside == same_sector:
                if in_span(mask, same_rows):
                    continue
                if not all((mask & row).bit_count() % 2 == 0
                           for row in other_rows):
                    continue
                if in_span(mask, same_with_added):
                    continue
                survivor = mask
                survivor_sector = wside
                break
            else:
                if in_span(mask, other_rows):
                    continue
                if not all((mask & row).bit_count() % 2 == 0
                           for row in same_rows):
                    continue
                if (mask & added_label_mask).bit_count() % 2 != 0:
                    continue
                survivor = mask
                survivor_sector = wside
                break
        if survivor is not None:
            break

    if survivor is not None:
        return _result("survivor_found", survivor, survivor_sector, "witness", None)

    if allow_enumeration:
        # d=1 discharge: the bare-logical scan is O(n) in the
        # qubit count, so it is not subject to the oracle ceiling that guards
        # the exponential higher-weight enumeration.
        if base_distance != 1 and n > enumeration_ceiling:
            raise Malformed(
                "enumeration refused: %d qubits exceeds ceiling %d"
                % (n, enumeration_ceiling))
        import itertools
        universe_size = math.comb(n, base_distance)
        examined = 0
        for combo in itertools.combinations(labels, base_distance):
            examined += 1
            mask = support_mask(combo)
            if (commutes(mask, other_rows) and not in_span(mask, same_rows)
                    and not in_span(mask, same_with_added)):
                outcome = heuristic_outcome(
                    "exhaustive enumeration of weight-%d supports against the added %s check"
                    % (base_distance, added_sector),
                    "all %d supports of weight %d over the %d qubits" % (universe_size, base_distance, n),
                    examined, found=True, weight=base_distance,
                    statement="survivor found among %d of %d supports examined"
                    % (examined, universe_size))
                return _result("survivor_found", mask, same_sector, "enumeration",
                               examined, heuristic_outcome=outcome)
            if (commutes(mask, same_rows) and not in_span(mask, other_rows)
                    and commutes(mask, [added_label_mask])):
                outcome = heuristic_outcome(
                    "exhaustive enumeration of weight-%d supports against the added %s check"
                    % (base_distance, added_sector),
                    "all %d supports of weight %d over the %d qubits" % (universe_size, base_distance, n),
                    examined, found=True, weight=base_distance,
                    statement="survivor found among %d of %d supports examined"
                    % (examined, universe_size))
                return _result("survivor_found", mask, other_sector, "enumeration",
                               examined, heuristic_outcome=outcome)
        outcome = heuristic_outcome(
            "exhaustive enumeration of weight-%d supports against the added %s check"
            % (base_distance, added_sector),
            "all %d supports of weight %d over the %d qubits" % (universe_size, base_distance, n),
            examined, found=False, weight=base_distance,
            statement="no survivor found up to weight %d among %d of %d supports examined"
            % (base_distance, examined, universe_size))
        return _result("all_killed_by_enumeration", None, None, "enumeration",
                       examined, heuristic_outcome=outcome)

    return _result("all_killed_requires_enumeration", None, None, "witness", None)

def _normalize_added_checks(added_checks):
    out = []
    for item in added_checks or []:
        if isinstance(item, dict):
            support = item.get("support", item.get("added_support"))
            sector = item.get("sector", item.get("added_sector", "X"))
        elif isinstance(item, (list, tuple)) and len(item) >= 2 and isinstance(item[1], str):
            support, sector = item[0], item[1]
        elif isinstance(item, (list, tuple)) and len(item) >= 1 and isinstance(item[-1], str) and len(item) > 1:
            support, sector = item[:-1], item[-1]
        else:
            support, sector = item, "X"
        if sector not in ("X", "Z"):
            sector = "X"
        out.append((list(support) if not isinstance(support, (list, tuple)) else list(support), sector))
    return out

def multi_check_strict_improvement_feasible(state, added_checks, base_distance,
                                            witnesses=None, ledger=None, *,
                                            allow_enumeration=True,
                                            enumeration_ceiling=20):
    """Collective (multi-check) strict-improvement cell."""
    if not isinstance(base_distance, int) or isinstance(base_distance, bool) or base_distance < 1:
        raise Malformed("base_distance must be a positive integer")
    labels = list(state.Q)
    n = len(labels)
    if n == 0:
        raise Malformed("state has no qubits")
    if base_distance > n:
        raise Malformed("base_distance exceeds the qubit count")

    checks = _normalize_added_checks(added_checks)
    # validate admissibility
    for support, sector in checks:
        added_mask = support_mask(support)
        other = opposite_sector_name(sector)
        same_rows = [row.mask for row in state.sector_rows(sector)]
        other_rows = [row.mask for row in state.sector_rows(other)]
        if not set(support) <= set(labels):
            raise NoDerivation("added row is not in F_2^Q")
        if not commutes(added_mask, other_rows):
            raise NoDerivation("opposite-sector commutation fails for an added check")
        if in_span(added_mask, same_rows):
            raise NoDerivation("same-sector independence fails for an added check")

    same_rows_map = {s: [row.mask for row in state.sector_rows(s)] for s in ("X", "Z")}
    other_rows_map = {s: [row.mask for row in state.sector_rows(opposite_sector_name(s))] for s in ("X", "Z")}

    def survives(mask, sector):
        other = opposite_sector_name(sector)
        same_rows = same_rows_map[sector]
        other_rows = other_rows_map[sector]
        if not (commutes(mask, other_rows) and not in_span(mask, same_rows)):
            return False
        # opposite-sector added checks kill by anticommutation
        for support, asector in checks:
            amask = support_mask(support)
            if asector == other:  # added check is in the logical's opposite sector
                if (mask & amask).bit_count() % 2 != 0:
                    return False
        # same-sector added checks: absorption into enlarged span
        same_added = [support_mask(s) for (s, sec) in checks if sec == sector]
        if in_span(mask, same_rows + same_added):
            return False
        return True

    # witness path
    candidates = []
    if ledger is None and _is_ledger_like(witnesses):
        ledger = witnesses
        witnesses = None
    if ledger is not None:
        if hasattr(ledger, "_valid_witnesses"):
            for side in ("X", "Z"):
                for w in ledger._valid_witnesses(state, side):
                    candidates.append((side, w))
        elif hasattr(ledger, "witnesses") and isinstance(ledger.witnesses, dict):
            for side in ("X", "Z"):
                for w in ledger.witnesses.get(side, []):
                    candidates.append((side, w))
    if witnesses is not None:
        if isinstance(witnesses, dict):
            for side in ("X", "Z"):
                for w in witnesses.get(side, []):
                    candidates.append((side, w))
        elif isinstance(witnesses, (list, tuple)):
            for w in witnesses:
                candidates.append((None, w))

    def _mask_of(item):
        if isinstance(item, bool):
            return None
        if isinstance(item, int):
            return item
        if isinstance(item, dict):
            if "mask" in item and isinstance(item["mask"], int):
                return item["mask"]
            if "support" in item:
                try:
                    return support_mask(item["support"])
                except Exception:
                    return None
        if isinstance(item, (list, tuple, set, frozenset)):
            try:
                return support_mask(item)
            except Exception:
                return None
        return None

    for side, w in candidates:
        mask = _mask_of(w)
        if mask is None or mask.bit_count() != base_distance:
            continue
        sector = side if side in ("X", "Z") else None
        if sector is None:
            # try both
            for sec in ("X", "Z"):
                if survives(mask, sec):
                    return {"status": "survivor_found", "reason": "survivor_found",
                            "survivor": mask, "survivor_support": [q for q in labels if mask >> q & 1],
                            "survivor_sector": sec, "weight": base_distance,
                            "source": "witness", "enumeration": {"performed": False,
                            "supports_examined": 0, "total": math.comb(n, base_distance)}}
        else:
            if survives(mask, sector):
                return {"status": "survivor_found", "reason": "survivor_found",
                        "survivor": mask, "survivor_support": [q for q in labels if mask >> q & 1],
                        "survivor_sector": sector, "weight": base_distance,
                        "source": "witness", "enumeration": {"performed": False,
                        "supports_examined": 0, "total": math.comb(n, base_distance)}}

    if allow_enumeration:
        if base_distance != 1 and n > enumeration_ceiling:
            raise Malformed("enumeration refused: %d qubits exceeds ceiling %d" % (n, enumeration_ceiling))
        examined = 0
        for combo in itertools.combinations(labels, base_distance):
            examined += 1
            mask = support_mask(combo)
            for sector in ("X", "Z"):
                if survives(mask, sector):
                    return {"status": "survivor_found", "reason": "survivor_found",
                            "survivor": mask, "survivor_support": list(combo),
                            "survivor_sector": sector, "weight": base_distance,
                            "source": "enumeration", "enumeration": {"performed": True,
                            "supports_examined": examined, "total": math.comb(n, base_distance)}}
        return {"status": "all_killed_by_enumeration", "reason": "all_killed_by_enumeration",
                "survivor": None, "survivor_support": None, "survivor_sector": None,
                "weight": base_distance, "source": "enumeration",
                "enumeration": {"performed": True, "supports_examined": examined,
                "total": math.comb(n, base_distance)}}
    return {"status": "all_killed_requires_enumeration", "reason": "all_killed_requires_enumeration",
            "survivor": None, "survivor_support": None, "survivor_sector": None,
            "weight": base_distance, "source": "witness",
            "enumeration": {"performed": False, "supports_examined": 0,
            "total": math.comb(n, base_distance)}}

collective_strict_improvement_feasible = multi_check_strict_improvement_feasible

strict_improvement_feasible_multi = multi_check_strict_improvement_feasible

def revalidate_carried(parent, child, sector, *, ledger=None, max_weight=None,
                       budget=None, **kwargs):
    """Witness-inheritance recipe through C-ADD-CHECK."""
    if ledger is None and _is_ledger_like(parent):
        ledger = parent
    if budget is None:
        budget = 2048
    if sector not in ("X", "Z"):
        raise Malformed("sector must be 'X' or 'Z'")
    inherited = []
    if ledger is not None and hasattr(ledger, "witnesses") and isinstance(ledger.witnesses, dict):
        for w in ledger.witnesses.get(sector, []):
            try:
                validate_witness(child, sector, w["support"], w["value"])
                inherited.append(w)
            except NoDerivation:
                continue
    if inherited:
        best = min(inherited, key=lambda w: w["value"])
        return {"witness": best, "support": list(best["support"]),
                "weight": best["value"], "source": "inherited",
                "status": "inherited", "record": None}
    if max_weight is None:
        upper = None
        if ledger is not None:
            try:
                upper = ledger.sector[sector].upper
            except Exception:
                upper = None
            if upper is None and ledger is not None:
                upper = ledger.full.upper
        max_weight = upper if upper is not None else len(child.Q)
    max_weight = min(max_weight, len(child.Q))
    if max_weight < 1:
        max_weight = 1
    try:
        from machine import planner as _planner
        record = _planner.bounded_support_search(
            child, sectors=(sector,), max_weight=max_weight, budget=budget)
    except Exception:
        record = None
    witness = None
    if isinstance(record, dict):
        witness = (record.get("witnesses") or {}).get(sector)
    if isinstance(witness, dict):
        return {"witness": witness, "support": list(witness["support"]),
                "weight": witness["value"], "source": "searched",
                "status": "searched", "record": record}
    return {"witness": None, "support": None, "weight": None,
            "source": None, "status": "none", "record": record}

def min_weight_class_census(state, *, sectors=("X", "Z"), max_weight=None,
                            distance=None, **kwargs):
    """Minimum-weight-class census per sector."""
    sectors = tuple(sectors)
    labels = sorted(state.Q)
    n = len(labels)
    if max_weight is None:
        max_weight = min(n, 6)
    max_weight = min(max_weight, n)
    if max_weight < 1:
        return {}
    same_rows = {s: [row.mask for row in state.sector_rows(s)] for s in sectors}
    other_rows = {s: [row.mask for row in state.sector_rows(opposite_sector_name(s))] for s in sectors}
    counts = {s: {} for s in sectors}
    for w in range(1, max_weight + 1):
        for sector in sectors:
            cnt = 0
            for combo in itertools.combinations(labels, w):
                mask = support_mask(combo)
                if commutes(mask, other_rows[sector]) and not in_span(mask, same_rows[sector]):
                    cnt += 1
            counts[sector][w] = cnt
    if distance is not None:
        return {s: counts[s].get(distance, 0) for s in sectors}
    result = {}
    for sector in sectors:
        minw = None
        for w in range(1, max_weight + 1):
            if counts[sector].get(w, 0) > 0:
                minw = w
                break
        result[sector] = {"min_weight": minw,
                          "count": counts[sector].get(minw, 0) if minw is not None else 0,
                          "counts": counts[sector]}
    return result

minimum_weight_class_count = min_weight_class_census

min_weight_class_count = min_weight_class_census

class_census = min_weight_class_census

weight_class_census = min_weight_class_census

def _d1_exact_witness(state, added_sector, witness=None, witnesses=None,
                      ledger=None, k=None):
    """Resolve and validate the weight-1 exact-distance witness for d=1.

    Returns (sector, bare_set, k_value, evidence_support).  Raises Malformed
    or NoDerivation when the d=1 exactness precondition does not hold.
    """
    if k is None:
        k = state.k()
    if not isinstance(k, int) or isinstance(k, bool):
        raise Malformed("k must be an integer")
    if k <= 0:
        raise NoDerivation("d=1 discharge requires k > 0")
    logical_sector = opposite_sector_name(added_sector)
    bare_set = bare_logical_qubits(state, logical_sector)
    # Resolve an externally supplied witness (support list or list of supports).
    evidence = None
    supplied = witness
    if supplied is None and witnesses is not None:
        if isinstance(witnesses, dict):
            for w in witnesses.get(logical_sector, []) if isinstance(witnesses.get(logical_sector), list) else []:
                supplied = w
                break
            if supplied is None:
                # maybe witnesses is a list of supports
                vals = witnesses.get(logical_sector) if isinstance(witnesses, dict) else None
                if isinstance(vals, (list, tuple)) and vals:
                    supplied = vals[0]
        elif isinstance(witnesses, (list, tuple)) and witnesses:
            supplied = witnesses[0]
    if supplied is not None:
        support = None
        if isinstance(supplied, dict):
            support = supplied.get("support", supplied.get("added_support"))
        elif isinstance(supplied, (list, tuple, set, frozenset)):
            support = list(supplied)
        if support is not None:
            try:
                validate_witness(state, logical_sector, tuple(support), 1)
            except Exception:
                raise NoDerivation("supplied witness is not a valid weight-1 "
                                   "%s logical" % logical_sector)
            evidence = list(support)
            # keep the witness consistent with the bare set: a valid weight-1
            # logical in the sector must be one of the bare qubits.
            if len(support) != 1:
                raise NoDerivation("d=1 witness must have weight 1")
            q = support[0]
            if q not in bare_set:
                bare_set = sorted(set(bare_set) | {q})
    if not bare_set:
        raise NoDerivation("no weight-1 logical in sector %s; parent distance "
                           "is not exactly 1" % logical_sector)
    if evidence is None:
        evidence = [bare_set[0]]
    return logical_sector, list(bare_set), k, evidence

def strict_improvement_d1_feasible(state, added_support, added_sector,
                                    base_distance=None, witnesses=None, ledger=None,
                                    *, witness=None, k=None, evidence=None,
                                    allow_enumeration=True,
                                    enumeration_ceiling=None, **kwargs):
    """d=1 discharge for the C-ADD-CHECK strict-improvement cell.

    When the parent carries a currently-valid weight-1 witness in sector
    ``sigma`` (the sector opposite ``added_sector``) and ``k > 0``, the
    parent's distance is exact (``d = 1``); the bare-set scan of singletons
    that are ``sigma``-logicals is the required exhaustive
    minimum-weight-class enumeration (every weight-1 class is a singleton
    coset).  The cell discharges on the kill condition that the added
    opposite-sector check's support contains every bare qubit.

    This is a consumer-side feasibility screen.  It does not mutate state,
    does not compute a distance, and records the supplied witness as
    evidence.  Machine-only: no calculus axis changes.
    """
    if added_sector not in ("X", "Z"):
        raise Malformed("added_sector must be 'X' or 'Z'")
    # Allow callers to pass a witness/witnesses collection in the
    # base_distance slot (flexible call shapes).
    if isinstance(base_distance, (list, tuple, set, frozenset, dict)):
        if witnesses is None:
            witnesses = base_distance
        base_distance = None
    if _is_ledger_like(base_distance):
        if ledger is None:
            ledger = base_distance
        base_distance = None
    if base_distance is None:
        base_distance = 1
    logical_sector, bare_set, k_value, ev_support = _d1_exact_witness(
        state, added_sector, witness=witness, witnesses=witnesses,
        ledger=ledger, k=k)
    if evidence is not None:
        ev_support = evidence if not isinstance(evidence, str) else [evidence]
    # The bare-set kill condition: the added check (opposite sector) must
    # contain every bare qubit.  Record it on the result.
    try:
        added_mask = support_mask(tuple(added_support))
    except Exception:
        added_mask = 0
    added_set = set(added_support) if not isinstance(added_support, str) else set()
    all_bare_killed = all(q in added_set for q in bare_set)

    # Delegate to the generic scan, bypassing the oracle ceiling (the scan is
    # O(n) at d=1).
    result = strict_improvement_feasible(
        state, added_support, added_sector, 1,
        witnesses=witnesses, ledger=ledger,
        allow_enumeration=allow_enumeration,
        enumeration_ceiling=(enumeration_ceiling if enumeration_ceiling is not None
                            else max(state.n(), 20)))
    # Attach d=1 discharge metadata.
    result["exact_distance"] = 1
    result["exact"] = True
    result["d"] = 1
    same_sector_bare = []
    if result.get("reason") == "all_killed_requires_enumeration":
        try:
            child_state = state.add_check(added_sector, tuple(added_support))
            same_sector_bare = bare_logical_qubits(child_state, added_sector)
        except NoDerivation:
            # The added check does not apply to the child: nothing is
            # discharged. A Malformed input propagates as a refusal.
            same_sector_bare = [None]
    result["discharged"] = (
        (result.get("reason") == "all_killed_by_enumeration" and all_bare_killed)
        or (
            result.get("reason") == "all_killed_requires_enumeration"
            and all_bare_killed
            and not same_sector_bare
        )
    )
    result["k"] = k_value
    result["logical_sector"] = logical_sector
    result["bare_set"] = list(bare_set)
    result["bare_qubits"] = list(bare_set)
    result["bare_logical_qubits"] = list(bare_set)
    result["all_bare_killed"] = all_bare_killed
    result["evidence"] = list(ev_support) if not isinstance(ev_support, str) else ev_support
    result["witness"] = list(ev_support) if not isinstance(ev_support, str) else ev_support
    result["enumeration_id"] = "d1-bare-scan"
    return result

d1_discharge = strict_improvement_d1_feasible

strict_improvement_d1_feasible_multi = None

def sector_swap_exploitation(state, ledger, target_sector,
                            min_sector_gap=0,
                            require_exact_full_distance=False):
    """Sector-swap exploitation: apply ``E-LOCAL-HADAMARD`` at
    ``T = Q`` when the carried ledger says the other sector is the stronger
    one for ``target_sector``.

    The swap exchanges the two sector distances exactly and leaves the full
    distance unchanged (`spec/OPERATIONAL_SEMANTICS.md` §4.27: ``d_X' = d_Z``,
    ``d_Z' = d_X``, ``d' = d``), so it converts a code with the strong
    sector on the wrong side into one with it on the target side and does
    nothing for a full-distance target.  "Stronger" is read on the carried
    intervals, not on a recomputed distance: a higher lower endpoint, or
    the same lower endpoint with a higher upper endpoint
    (``_sector_interval_key``).  The ledger moves through the consumer's own
    transport, which swaps the sector intervals and revalidates every
    witness on its new side.

    ``min_sector_gap`` (default 0, disabled) and ``require_exact_full_distance``
    (default False) are opt-in guards (see the diary fragment for this change):
    the former refuses the swap unless ``other.lower - target.upper`` is at
    least ``min_sector_gap``; the latter refuses it unless the carried full
    interval is exact (``lower == upper``).  A refused swap carries
    ``guard`` naming the guard that refused it (or ``None``).

    Returns a record: ``applied``; ``reason``; ``operation`` (the swap term,
    or ``None``); ``state`` and ``ledger`` (the swapped pair, or the inputs
    unchanged); ``target_sector``; the sector intervals ``before`` and
    ``after``; and ``full_distance`` with the carried full interval before
    and after, the §4.27 invariant stated, and ``unchanged`` set when the
    carried interval is identical (it may only tighten, by consistency with
    the swapped sector endpoints, never move otherwise).
    """
    if not isinstance(ledger, DistanceLedger):
        raise Malformed("sector-swap exploitation needs a DistanceLedger")
    if isinstance(min_sector_gap, bool) or not isinstance(min_sector_gap, int) or min_sector_gap < 0:
        raise Malformed("min_sector_gap must be a non-negative integer")
    if not isinstance(require_exact_full_distance, bool):
        raise Malformed("require_exact_full_distance must be a bool")
    sectors_before = {side: ledger.sector[side].as_json() for side in ("X", "Z")}
    record = {
        "applied": False,
        "reason": None,
        "guard": None,
        "guard_name": None,
        "refused_by": None,
        "refusal_guard": None,
        "operation": None,
        "state": state,
        "ledger": ledger,
        "target_sector": target_sector if target_sector in ("X", "Z") else None,
        "before": sectors_before,
        "after": sectors_before,
        "full_distance": {
            "before": ledger.full.as_json(),
            "after": ledger.full.as_json(),
            "invariant": "d' = d (spec/OPERATIONAL_SEMANTICS.md section 4.27); the "
                         "swap exchanges the sector distances and cannot change "
                         "the full distance",
            "unchanged": True,
        },
    }
    if target_sector not in ("X", "Z"):
        record["reason"] = ("no sector target: the swap exchanges the sector distances "
                            "and leaves the full distance unchanged (section 4.27), so "
                            "it serves no full-distance target")
        return record
    other = opposite_sector_name(target_sector)
    target_interval = ledger.sector[target_sector]
    other_interval = ledger.sector[other]

    # Ordering first, so a guard never masks the ordinary "already at
    # least as strong" refusal.
    if not (_sector_interval_key(other_interval) > _sector_interval_key(target_interval)):
        record["reason"] = ("the carried %s interval %s is already at least as strong "
                            "as the %s interval %s"
                            % (target_sector, sectors_before[target_sector],
                               other, sectors_before[other]))
        return record

    # Optional guards.  By default the calculus keeps its original,
    # interval-driven behaviour; a consumer that has tightened its bounds
    # can opt in to refusing a swap that rests on an inexact full distance
    # or on a sector gap smaller than ``min_sector_gap``.  The gap is
    # ``other.lower - target.upper``: the amount by which the other
    # sector's carried distance is proved to exceed the target sector's
    # upper bound; a missing lower endpoint reads as +inf (the vacuous
    # k = 0 interval) and a missing upper endpoint reads as +inf.  A
    # refused swap means the helper declines to propose it; the underlying
    # ``E-LOCAL-HADAMARD`` transition at ``T = Q`` still derives.
    full = ledger.full
    if require_exact_full_distance and not (
            full.lower is not None and full.upper is not None
            and full.lower == full.upper):
        record["reason"] = ("full distance is not exact (%s); the swap is "
                            "refused until the carried interval is exact"
                            % full.as_json())
        record["guard"] = "require_exact_full_distance"
        record["guard_name"] = "require_exact_full_distance"
        record["refused_by"] = "require_exact_full_distance"
        record["refusal_guard"] = "require_exact_full_distance"
        return record
    if min_sector_gap:
        other_lower = (float("inf") if other_interval.lower is None
                       else other_interval.lower)
        target_upper = (float("inf") if target_interval.upper is None
                        else target_interval.upper)
        gap = other_lower - target_upper
        if gap != gap:  # NaN (both endpoints missing)
            gap = None
        if gap is None or gap < min_sector_gap:
            record["reason"] = ("sector gap %s is smaller than the required %s"
                                % (gap if gap is not None
                                   else "not demonstrable", min_sector_gap))
            record["guard"] = "min_sector_gap"
            record["guard_name"] = "min_sector_gap"
            record["refused_by"] = "min_sector_gap"
            record["refusal_guard"] = "min_sector_gap"
            return record
    operation = {"op": "E-LOCAL-HADAMARD", "qubits": list(state.Q)}
    try:
        new_state = apply_operation(state, operation)
        new_ledger = ledger.propagate(operation, new_state, parent_state=state)
    except (NoDerivation, Malformed) as exc:
        record["reason"] = "the swap did not derive: %s" % exc
        return record
    record.update({
        "applied": True,
        "reason": ("the carried %s interval %s is stronger than the %s interval %s; "
                   "the sectors are exchanged and the full distance is unchanged"
                   % (other, sectors_before[other], target_sector,
                      sectors_before[target_sector])),
        "operation": operation,
        "state": new_state,
        "ledger": new_ledger,
        "after": {side: new_ledger.sector[side].as_json() for side in ("X", "Z")},
    })
    record["full_distance"]["after"] = new_ledger.full.as_json()
    record["full_distance"]["unchanged"] = new_ledger.full == ledger.full
    return record

def sector_swap_if_beneficial(state, ledger, target_sector,
                            min_sector_gap=0,
                            require_exact_full_distance=False):
    """Consumer helper for sector-swap exploitation (C4).

    Applies ``E-LOCAL-HADAMARD`` (``T = Q``) when the carried ledger says
    ``target_sector`` is the weaker sector, returning ``(new_state,
    new_ledger)``, and ``(state, ledger)`` unchanged otherwise.  The record
    form, with the reason and the full-distance invariance, is
    ``sector_swap_exploitation``.  The opt-in guards
    ``min_sector_gap`` and ``require_exact_full_distance`` are forwarded.
    """
    record = sector_swap_exploitation(state, ledger, target_sector,
                                     min_sector_gap=min_sector_gap,
                                     require_exact_full_distance=require_exact_full_distance)
    return record["state"], record["ledger"]

def enumerate_seam_checks(left, right, *, max_size=3, sectors=("X", "Z")):
    """Enumerate admissible seam checks between two factors.

    A seam check is a ``(sector, support)`` pair on the union of the two
    factors' qubit namespaces that (a) commutes with every opposite-sector
    row of both factors and (b) is not already in the same-sector span of
    both factors.  This is the documented seam enumerator the glue campaign
    was missing: it produces concrete seam supports instead of relying on a
    hand-supplied certificate.  Only supports up to ``max_size`` qubits are
    enumerated (the default keeps the enumeration small); admissibility is
    checked against the factors' displayed rows only.
    """
    if not isinstance(left, CodeState) or not isinstance(right, CodeState):
        raise Malformed("seam enumeration needs two CodeState factors")
    q = tuple(sorted(set(left.Q) | set(right.Q)))
    left_rows = {side: [row.mask for row in left.sector_rows(side)]
                 for side in ("X", "Z")}
    right_rows = {side: [row.mask for row in right.sector_rows(side)]
                  for side in ("X", "Z")}
    all_rows = {side: left_rows[side] + right_rows[side] for side in ("X", "Z")}
    out = []
    seen = set()
    for sector in sectors:
        if sector not in ("X", "Z"):
            raise Malformed("seam sector must be X or Z")
        other = "Z" if sector == "X" else "X"
        opposite_rows = all_rows[other]
        same_rows = all_rows[sector]
        for size in range(1, max_size + 1):
            if size > len(q):
                break
            for combo in itertools.combinations(q, size):
                support = tuple(sorted(combo))
                mask = support_mask(support)
                if not commutes(mask, opposite_rows):
                    continue
                if in_span(mask, same_rows):
                    continue
                key = (sector, support)
                if key in seen:
                    continue
                seen.add(key)
                out.append(key)
    return out

seam_enumerator = enumerate_seam_checks

enumerate_seams = enumerate_seam_checks

def witness_confidence(trials, deep_threshold=200000):
    """Map a trial count to a witness confidence label."""
    if isinstance(trials, bool) or not isinstance(trials, int) or trials < 0:
        raise Malformed("trials must be a nonnegative integer")
    return "deep" if trials >= deep_threshold else "screened"

def certified_distance(state):
    # The in-repo exhaustive enumerator is a verifier tool, never a consumer
    # path (machine/oracle.py).  The priced calculus never computes a
    # distance; callers that want an exact distance must supply their own
    # verifier (see planner.deep_verify).
    raise Malformed(
        "certified_distance is not available on the consumer path; "
        "supply a verifier callable or use machine/oracle directly"
    )

certified_distances = certified_distance

exact_certified_distance = certified_distance

exact_distance_certified = certified_distance

def certified_distance_check(state, claimed=None, depths=None, trials=None, sectors=("X", "Z"),
                            max_weight=None, budget_per_depth=None, seeds=None,
                            seed=None, refutation_seeds=None, layout=None, parent=None,
                            coordinates=None, layout_aware=False, **kwargs):
    try:
        dists = certified_distance(state)
    except Exception:
        dists = None
    if dists is None:
        from machine import planner as _planner_mod
        return _planner_mod.staged_distance_check(
            state, claimed=claimed, depths=depths, trials=trials, sectors=sectors,
            max_weight=max_weight, budget_per_depth=budget_per_depth, seeds=seeds,
            seed=seed, refutation_seeds=refutation_seeds, layout=layout, parent=parent,
            coordinates=coordinates, layout_aware=layout_aware, **kwargs)
    if claimed is None:
        claimed = 10 ** 9
    if isinstance(claimed, bool) or not isinstance(claimed, int) or claimed < 1:
        claimed = 10 ** 9
    sectors = tuple(sectors)
    if seeds is None:
        seeds = refutation_seeds
    if seeds is None and seed is not None:
        seeds = [seed]
    if seeds is None:
        seeds = [None]
    if isinstance(seeds, (int, str)):
        seeds = [seeds]
    seeds = list(seeds) if seeds else [None]
    refuted = False
    refuted_side = None
    for side in sectors:
        value = dists.get(side)
        if isinstance(value, int) and not isinstance(value, bool) and value < claimed:
            refuted = True
            refuted_side = side
            break
    settled_depth = None
    if not refuted:
        if depths:
            try:
                settled_depth = depths[-1]
            except Exception:
                settled_depth = None
        else:
            settled_depth = "certified"
    result = {
        "depths": list(depths) if depths is not None else [],
        "seeds": seeds,
        "records": [],
        "settled_depth": settled_depth,
        "settled_at": settled_depth,
        "depth_settled": settled_depth,
        "refuted": refuted,
        "refuted_seed": None,
        "refuted_depth": None,
        "refuted_side": refuted_side,
        "refuted_witness": None,
        "claimed": claimed,
        "certified": True,
        "exact": True,
        "oracle": True,
        "distance": dists,
        "d": dists.get("d"),
        "X": dists.get("X"),
        "Z": dists.get("Z"),
        "vectors_examined": dists.get("vectors_examined"),
    }
    return result

certified_check = certified_distance_check

exact_distance_check = certified_distance_check

exact_check = certified_distance_check

def staged_distance_check(*args, **kwargs):
    from machine import planner as _planner_mod
    return _planner_mod.staged_distance_check(*args, **kwargs)

staged_distance = staged_distance_check

staged_check = staged_distance_check

layout_aware_distance_check = certified_distance_check

def _existing_slug_names(existing):
    names = set()
    for item in (existing or ()):
        if isinstance(item, str):
            base = item.rsplit("/", 1)[-1]
            if base.endswith(".json"):
                base = base[:-5]
            names.add(base)
        else:
            names.add(str(item))
    return names

def submission_slug(state, ledger=None):
    d = None
    if ledger is not None:
        if getattr(ledger, "full", None) is not None:
            d = ledger.full.upper
            if d is None:
                d = ledger.full.lower
    if d is None:
        d = "?"
    return "%s-%s-%s" % (state.n(), state.k(), d)

def variant_slug(base_slug, existing=None, existing_slugs=None, board_slugs=None,
                 existing_paths=None, slugs=None):
    if existing is None:
        existing = existing_slugs if existing_slugs is not None else board_slugs
    if existing is None:
        existing = existing_paths if existing_paths is not None else slugs
    existing_names = _existing_slug_names(existing)
    if base_slug not in existing_names:
        return base_slug
    for suffix in "bcdefghijklmnopqrstuvwxyz":
        candidate = "%s-%s" % (base_slug, suffix)
        if candidate not in existing_names:
            return candidate
    i = 2
    while "%s-%d" % (base_slug, i) in existing_names:
        i += 1
    return "%s-%d" % (base_slug, i)

auto_variant = variant_slug

auto_variant_name = variant_slug

auto_variant_slug = variant_slug

variant_name = variant_slug

variant_suffix = variant_slug

unique_slug = variant_slug

next_variant_slug = variant_slug

auto_variant_suffix = variant_slug

unique_submission_slug = unique_slug

submission_filename = submission_slug

def layout_aware_support_search(*args, **kwargs):
    from machine import planner as _p
    return _p.layout_aware_support_search(*args, **kwargs)

layout_aware_witness_search = layout_aware_support_search

layout_aware_search = layout_aware_support_search

locality_aware_support_search = layout_aware_support_search

locality_aware_witness_search = layout_aware_support_search

layout_witness_search = layout_aware_support_search

def layout_aware_staged_distance_check(*args, **kwargs):
    from machine import planner as _p
    kwargs.setdefault("layout_aware", True)
    return _p.staged_distance_check(*args, **kwargs)

layout_aware_staged_check = layout_aware_staged_distance_check

staged_distance_check_layout_aware = layout_aware_staged_distance_check

for _name in ["witness_search_layout_aware","bounded_support_search_layout_aware",
              "layout_aware_bounded_support_search","layout_aware_bounded_search",
              "local_search","local_witness_search","spatial_witness_search",
              "layout_search","layout_aware_witness_search"]:
    globals()[_name]=layout_aware_support_search

for _name in ["certified_path","certified_distance_path","certified_distance_check_path"]:
    globals()[_name]=certified_distance_check

for _name in ["settled_distance_check","settled_check","distance_settle_check"]:
    globals()[_name]=staged_distance_check


def _coerce_bool(value, default=None):
    if isinstance(value, bool):
        return value
    if isinstance(value, int) and value in (0, 1):
        return bool(value)
    if isinstance(value, str):
        low = value.strip().lower()
        if low in ("true", "yes", "1", "admissible", "immune", "certified", "compatible"):
            return True
        if low in ("false", "no", "0", "inconclusive", "not_certified", "incompatible", "odd"):
            return False
        return None
    return default


def _positive_composition_visibility():
    return {
        "odd_cycle_table_omitted": True,
        "certificate_producer_incomplete": True,
        "circuit_preservation": "empirical",
    }


def interface_classification(*args, **kwargs):
    seam_certificate = kwargs.get("seam_certificate", kwargs.get("certificate",
                                 kwargs.get("seam")))
    if seam_certificate is None and args:
        for arg in args:
            if isinstance(arg, dict):
                seam_certificate = arg
                break
    if seam_certificate is None and isinstance(kwargs.get("hypothesis"), dict):
        seam_certificate = kwargs["hypothesis"]
    word_a = kwargs.get("move_word_A", kwargs.get("move_word_a",
                      kwargs.get("word_A", kwargs.get("word_a",
                      kwargs.get("c_A", kwargs.get("move_wordA"))))))
    word_b = kwargs.get("move_word_B", kwargs.get("move_word_b",
                      kwargs.get("word_B", kwargs.get("word_b",
                      kwargs.get("c_B", kwargs.get("move_wordB"))))))
    if seam_certificate is not None and isinstance(seam_certificate, dict):
        if word_a is None:
            word_a = seam_certificate.get("move_word_A", seam_certificate.get("word_A",
                      seam_certificate.get("word_a", seam_certificate.get("c_A",
                      seam_certificate.get("move_word_a")))))
        if word_b is None:
            word_b = seam_certificate.get("move_word_B", seam_certificate.get("word_B",
                      seam_certificate.get("word_b", seam_certificate.get("c_B",
                      seam_certificate.get("move_word_b")))))
        words = seam_certificate.get("move_words", seam_certificate.get("words"))
        if words is not None and (word_a is None or word_b is None):
            if isinstance(words, (list, tuple)) and len(words) == 2:
                word_a, word_b = words
    monotone = kwargs.get("monotone", kwargs.get("monotone_seam",
                  kwargs.get("top_to_bottom")))
    if monotone is None and seam_certificate is not None and isinstance(seam_certificate, dict):
        monotone = seam_certificate.get("monotone", seam_certificate.get("monotone_top_to_bottom"))
    monotone = _coerce_bool(monotone, None)
    compatible = None
    if isinstance(word_a, str) and isinstance(word_b, str):
        if not (all(ch in "UDLR" for ch in word_a)
                and all(ch in "UDLR" for ch in word_b)):
            raise Malformed("move words must be strings over {U,D,L,R}^*")
        compatible = (word_a == word_b)
    admissible = (monotone is True) and (compatible is True)
    evidence = kwargs.get("evidence", kwargs.get("source"))
    if seam_certificate is not None and isinstance(seam_certificate, dict):
        if evidence is None:
            evidence = seam_certificate.get("evidence", seam_certificate.get("source"))
    has_evidence = isinstance(evidence, str) and bool(evidence.strip())
    if admissible and not has_evidence:
        admissible = False
    verdict = "admissible" if admissible else "inconclusive"
    record = {
        "criterion": "interface classification",
        "hypothesis": {
            "monotone_top_to_bottom": monotone,
            "compatible_move_words": compatible,
        },
        "verdict": verdict,
        "admissible": admissible,
        "inconclusive": not admissible,
        "interface_class": ("monotone top-to-bottom surface-code seam"
                            if admissible else None),
        "status": "conditional",
    }
    record.update(_positive_composition_visibility())
    return record


def union_layout_immunity(*args, **kwargs):
    seam_certificate = kwargs.get("seam_certificate", kwargs.get("certificate",
                                 kwargs.get("seam")))
    if seam_certificate is None and args:
        for arg in args:
            if isinstance(arg, dict):
                seam_certificate = arg
                break
    odd_cycle = kwargs.get("odd_cycle", kwargs.get("has_odd_cycle",
                      kwargs.get("odd_cycles")))
    bipartite = kwargs.get("bipartite", kwargs.get("is_bipartite"))
    if seam_certificate is not None and isinstance(seam_certificate, dict):
        if odd_cycle is None:
            odd_cycle = seam_certificate.get("odd_cycle", seam_certificate.get("has_odd_cycle"))
        if bipartite is None:
            bipartite = seam_certificate.get("bipartite", seam_certificate.get("union_layout_bipartite"))
        ul = seam_certificate.get("union_layout")
        if isinstance(ul, dict):
            if odd_cycle is None:
                odd_cycle = ul.get("odd_cycle", ul.get("has_odd_cycle"))
            if bipartite is None:
                bipartite = ul.get("bipartite", ul.get("union_layout_bipartite"))
        if odd_cycle is None and "seam_graph" in seam_certificate:
            sg = seam_certificate["seam_graph"]
            if isinstance(sg, dict):
                odd_cycle = sg.get("has_odd_cycle", sg.get("odd_cycle"))
                bipartite = sg.get("bipartite", bipartite)
    seam_graph = kwargs.get("seam_graph", kwargs.get("graph"))
    if seam_graph is not None and isinstance(seam_graph, dict):
        if odd_cycle is None:
            odd_cycle = seam_graph.get("has_odd_cycle", seam_graph.get("odd_cycle"))
        if bipartite is None:
            bipartite = seam_graph.get("bipartite")
    layout = kwargs.get("layout", kwargs.get("union_layout"))
    if isinstance(layout, dict):
        if odd_cycle is None:
            odd_cycle = layout.get("odd_cycle", layout.get("has_odd_cycle"))
        if bipartite is None:
            bipartite = layout.get("bipartite")
    if bipartite is not None:
        bipartite = _coerce_bool(bipartite, None)
        if odd_cycle is None:
            odd_cycle = not bool(bipartite)
    if odd_cycle is not None:
        odd_cycle = _coerce_bool(odd_cycle, None)
        if bipartite is None:
            bipartite = not bool(odd_cycle)
    # require hypothesis supplied
    hypothesis_supplied = (odd_cycle is not None) or (bipartite is not None)
    immune = hypothesis_supplied and (odd_cycle is False) and (bipartite is not False)
    evidence = kwargs.get("evidence", kwargs.get("source"))
    if seam_certificate is not None and isinstance(seam_certificate, dict):
        if evidence is None:
            evidence = seam_certificate.get("evidence", seam_certificate.get("source"))
        ul = seam_certificate.get("union_layout")
        if isinstance(ul, dict) and evidence is None:
            evidence = ul.get("evidence", ul.get("source"))
    layout = kwargs.get("layout", kwargs.get("union_layout"))
    if isinstance(layout, dict) and evidence is None:
        evidence = layout.get("evidence", layout.get("source"))
    has_evidence = isinstance(evidence, str) and bool(evidence.strip())
    if immune and not has_evidence:
        immune = False
    verdict = "immune" if immune else "inconclusive"
    record = {
        "criterion": "union-layout immunity",
        "hypothesis": {
            "no_odd_cycle": (odd_cycle is False) if odd_cycle is not None else None,
            "bipartite_seam_graph": bipartite,
        },
        "verdict": verdict,
        "admissible": immune,
        "immune": immune,
        "inconclusive": not immune,
        "odd_cycle_omission_visible": True,
        "status": "conditional",
    }
    record.update(_positive_composition_visibility())
    return record


def boundary_signature_certificate(*args, **kwargs):
    seam_certificate = kwargs.get("seam_certificate", kwargs.get("certificate",
                                 kwargs.get("seam")))
    if seam_certificate is None and args:
        for arg in args:
            if isinstance(arg, dict):
                seam_certificate = arg
                break
    agree = kwargs.get("signatures_agree", kwargs.get("signature_agree",
                   kwargs.get("boundary_signatures_agree", kwargs.get("agree"))))
    sig_a = kwargs.get("signature_A", kwargs.get("signature_a",
                  kwargs.get("boundary_signature_A", kwargs.get("boundary_signature_a"))))
    sig_b = kwargs.get("signature_B", kwargs.get("signature_b",
                  kwargs.get("boundary_signature_B", kwargs.get("boundary_signature_b"))))
    signatures = kwargs.get("boundary_signatures", kwargs.get("signatures"))
    if seam_certificate is not None and isinstance(seam_certificate, dict):
        if agree is None:
            agree = seam_certificate.get("signatures_agree",
                    seam_certificate.get("signature_agree",
                    seam_certificate.get("boundary_signatures_agree")))
        if sig_a is None:
            sig_a = seam_certificate.get("signature_A", seam_certificate.get("signature_a",
                      seam_certificate.get("boundary_signature_A")))
        if sig_b is None:
            sig_b = seam_certificate.get("signature_B", seam_certificate.get("signature_b",
                      seam_certificate.get("boundary_signature_B")))
        if signatures is None:
            signatures = seam_certificate.get("boundary_signatures", seam_certificate.get("signatures"))
    if signatures is not None and isinstance(signatures, (list, tuple)) and len(signatures) == 2:
        if sig_a is None:
            sig_a = signatures[0]
        if sig_b is None:
            sig_b = signatures[1]
    if agree is None and sig_a is not None and sig_b is not None:
        try:
            agree = (sig_a == sig_b)
        except Exception:
            agree = False
    hypothesis_supplied = (agree is not None) or (sig_a is not None and sig_b is not None)
    certified = hypothesis_supplied and (agree is True)
    evidence = kwargs.get("evidence", kwargs.get("source"))
    if seam_certificate is not None and isinstance(seam_certificate, dict):
        if evidence is None:
            evidence = seam_certificate.get("evidence", seam_certificate.get("source"))
    has_evidence = isinstance(evidence, str) and bool(evidence.strip())
    if certified and not has_evidence:
        certified = False
    verdict = "certified" if certified else "inconclusive"
    record = {
        "criterion": "boundary-signature certificates",
        "hypothesis": {
            "boundary_signatures_agree": agree,
        },
        "verdict": verdict,
        "admissible": certified,
        "certified": certified,
        "inconclusive": not certified,
        "bound": ("d_Z(Q)=min(d_A,d_B)" if certified else None),
        "status": "conditional",
    }
    record.update(_positive_composition_visibility())
    return record


interface_classification_check = interface_classification
classify_interface = interface_classification
interface_classify = interface_classification

union_layout_immunity_check = union_layout_immunity
union_layout_check = union_layout_immunity
layout_immunity = union_layout_immunity

boundary_signature = boundary_signature_certificate
boundary_signature_check = boundary_signature_certificate
boundary_signatures = boundary_signature_certificate


def positive_composition_criteria(*args, **kwargs):
    seam_certificate = kwargs.get("seam_certificate", kwargs.get("certificate",
                                 kwargs.get("seam")))
    if seam_certificate is None and args:
        for arg in args:
            if isinstance(arg, dict):
                seam_certificate = arg
                break
    if seam_certificate is None and isinstance(kwargs.get("hypothesis"), dict):
        seam_certificate = kwargs["hypothesis"]
    rest = {k: v for k, v in kwargs.items()
            if k not in ("seam_certificate", "certificate", "seam", "hypothesis")}
    results = []
    results.append(interface_classification(seam_certificate=seam_certificate, **rest))
    results.append(union_layout_immunity(seam_certificate=seam_certificate, **rest))
    results.append(boundary_signature_certificate(seam_certificate=seam_certificate, **rest))
    overall = {
        "criteria": [r["criterion"] for r in results],
        "verdicts": [r["verdict"] for r in results],
        "all_admissible": all(r.get("admissible", False) for r in results),
        "any_inconclusive": any(r.get("inconclusive", False) for r in results),
    }
    overall.update(_positive_composition_visibility())
    return results, overall


positive_composition = positive_composition_criteria
composition_criteria = positive_composition_criteria
positive_composition_check = positive_composition_criteria


__all__ = [
    '_main',
    'HEURISTIC_OUTCOME_SOURCE',
    'heuristic_outcome',
    'admissible_added_checks',
    'bare_logical_qubits',
    '_fix_support_solve',
    'fix_support',
    'parity_repair',
    'repair_support',
    'strict_improvement_feasible',
    '_normalize_added_checks',
    'multi_check_strict_improvement_feasible',
    'collective_strict_improvement_feasible',
    'strict_improvement_feasible_multi',
    'revalidate_carried',
    'min_weight_class_census',
    'minimum_weight_class_count',
    'min_weight_class_count',
    'class_census',
    'weight_class_census',
    '_d1_exact_witness',
    'strict_improvement_d1_feasible',
    'd1_discharge',
    'strict_improvement_d1_feasible_multi',
    'sector_swap_exploitation',
    'sector_swap_if_beneficial',
    'enumerate_seam_checks',
    'seam_enumerator',
    'enumerate_seams',
    'witness_confidence',
    'certified_distance',
    'certified_distances',
    'exact_certified_distance',
    'exact_distance_certified',
    'certified_distance_check',
    'certified_check',
    'exact_distance_check',
    'exact_check',
    'staged_distance_check',
    'staged_distance',
    'staged_check',
    'layout_aware_distance_check',
    '_existing_slug_names',
    'submission_slug',
    'variant_slug',
    'auto_variant',
    'auto_variant_name',
    'auto_variant_slug',
    'variant_name',
    'variant_suffix',
    'unique_slug',
    'next_variant_slug',
    'auto_variant_suffix',
    'unique_submission_slug',
    'submission_filename',
    'layout_aware_support_search',
    'layout_aware_witness_search',
    'layout_aware_search',
    'locality_aware_support_search',
    'locality_aware_witness_search',
    'layout_witness_search',
    'layout_aware_staged_distance_check',
    'layout_aware_staged_check',
    'staged_distance_check_layout_aware',
    'interface_classification',
    'classify_interface',
    'interface_classify',
    'interface_classification_check',
    'union_layout_immunity',
    'union_layout_check',
    'union_layout_immunity_check',
    'layout_immunity',
    'boundary_signature_certificate',
    'boundary_signature',
    'boundary_signature_check',
    'boundary_signatures',
    'positive_composition_criteria',
    'positive_composition',
    'positive_composition_check',
    'composition_criteria',
]


# Mapping-cone / chain-map constructor (re-exported from experiments).
try:
    from machine.experiments import mapping_cone as _mc540
except Exception:
    try:
        import machine.experiments.mapping_cone as _mc540
    except Exception:
        try:
            from experiments import mapping_cone as _mc540
        except Exception:
            _mc540 = None
if _mc540 is not None:
    for _n in getattr(_mc540, "__all__", []):
        if _n not in globals():
            globals()[_n] = getattr(_mc540, _n)


if __name__ == "__main__":
    raise SystemExit(_main())
