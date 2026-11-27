"""Judgment-level conformance harness for the priced consumer.

This harness is the instrument. It generates small random
CSS states, applies every admitted transition, measures the exact per-sector
distances with the external oracle in ``issue21_challenge_replay.py``, and
asserts that every interval emitted by ``machine.priced_calculus`` contains
the corresponding exact distance.

It is evidence about the transport rules, never a proof and never a discharge
of ``OBL-PRICED-INTERVAL-SOUNDNESS``.  A price hypothesis is trusted by
construction; the harness checks that the *transport rules* are sound given
the hypothesis, not that the hypothesis is true.  A run that reports 0
violations is a run that failed to falsify, nothing more.

Issue #235: the suite randomizes *nonzero* lower endpoints (and a little
upper-endpoint slack, i.e. interval width) across the small states, and
records per-operation coverage so that every admitted operation this harness
transits is checked under at least one nonzero lower endpoint -- the
lower-endpoint transport rules ``OBL-PRICED-INTERVAL-SOUNDNESS`` depends on
are the ones a zero-seeded suite can never exercise.

Report path (issue #235 / TODO item 12): the run must not dirty a tracked
file, so the JSON report goes to ``priced_conformance_report.json`` in the system temporary directory (see ``DEFAULT_REPORT_PATH``)
by default; set ``PRICED_CONFORMANCE_REPORT`` to another path to override it,
or to ``-`` to skip writing a report entirely.  The case count defaults to
``DEFAULT_CASES`` and may be overridden with ``PRICED_CONFORMANCE_CASES``.
"""

from __future__ import print_function

import copy
import itertools
import json
import os
import tempfile
import random
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
MACHINE = os.path.dirname(HERE)
ROOT = os.path.dirname(MACHINE)
for path in (MACHINE, ROOT, HERE):
    if path not in sys.path:
        sys.path.insert(0, path)

from machine import priced_calculus as pc
from issue21_challenge_replay import exact_distances

SECTORS = ("X", "Z")

# The operations this harness transits (issue #235).  Each one must see at
# least one case whose *input* ledger carries a nonzero lower endpoint,
# otherwise the run did not exercise the lower-endpoint transport rules for
# that operation.  The suite fails if an admitted operation is never
# transited or never transited with a nonzero lower endpoint.
ADMITTED_OPERATIONS = ("C-ADD-CHECK", "C-DELETE-CHECK", "C-DIRECT-SUM",
                       "C-SKIP", "E-GRAFT", "E-PEEL", "E-SPLIT")

DEFAULT_CASES = 200
DEFAULT_SEED = 20261021
DEFAULT_REPORT_PATH = os.path.join(tempfile.gettempdir(),
                                   "priced_conformance_report.json")


def _popcount(value):
    return bin(value).count("1")


def _all_vectors(n_labels):
    # enumerate subsets over the state's own qubit labels
    result = [(0, 0)]
    for label in n_labels:
        bit = 1 << label
        result = result + [(mask | bit, weight + 1) for mask, weight in result]
    return result


def random_state(rng, q_labels, id_prefixes=("a", "b")):
    """Generate one well-formed random CSS state over the given qubit labels.

    Rows are independent within each sector and the sectors are orthogonal.
    Qubit labels may be arbitrary nonnegative integers.
    """
    qset = set(q_labels)
    q_sorted = sorted(q_labels)
    n = len(q_sorted)
    # index labels -> bit positions for vector arithmetic is by label, not
    # position; masks use 1 << label directly.
    for _attempt in range(10000):
        # pick a random subset of X rows (independent) and Z rows in X_perp
        # (independent).
        x_masks = []
        # random number of X rows
        target_x = rng.randrange(0, min(n, 4) + 1)
        attempts = 0
        while len(x_masks) < target_x and attempts < 1000:
            attempts += 1
            mask = 0
            for label in q_sorted:
                if rng.random() < 0.35:
                    mask |= 1 << label
            if mask == 0:
                continue
            # independence: not in span of existing x_masks
            if pc.in_span(mask, x_masks):
                continue
            x_masks.append(mask)
        # Z rows must be orthogonal to every X row and independent.
        z_masks = []
        x_perp = [m for m in range(1 << max(q_sorted + [0]) + 1) if all(
            _popcount(m & xm) % 2 == 0 for xm in x_masks
        ) and m != 0] if q_sorted else []
        # restrict to labels subset
        x_perp = [m for m in x_perp if (m & ~sum(1 << q for q in q_sorted)) == 0]
        target_z = rng.randrange(0, min(n, 4) + 1)
        attempts = 0
        pool = list(x_perp)
        rng.shuffle(pool)
        for mask in pool:
            if len(z_masks) >= target_z:
                break
            if mask == 0:
                continue
            if pc.in_span(mask, z_masks):
                continue
            z_masks.append(mask)
        # build rows
        x_prefix, z_prefix = id_prefixes
        rows = []
        used = set()
        for i, mask in enumerate(x_masks, start=1):
            rid = "%s%d" % (x_prefix, i)
            support = tuple(sorted(q for q in q_sorted if (mask >> q) & 1))
            rows.append(pc.Row(rid, "X", support))
            used.add(rid)
        for i, mask in enumerate(z_masks, start=1):
            rid = "%s%d" % (z_prefix, i)
            support = tuple(sorted(q for q in q_sorted if (mask >> q) & 1))
            rows.append(pc.Row(rid, "Z", support))
            used.add(rid)
        try:
            state = pc.CodeState(tuple(q_sorted), tuple(rows), frozenset(used))
            state.validate()
        except (pc.Malformed, pc.NoDerivation, ValueError):
            continue
        return state
    raise RuntimeError("failed to generate a valid CSS state")


def _seed_lower(exact, lower_seed):
    """Derive a safe (<= exact) lower bound from ``lower_seed``."""
    if isinstance(lower_seed, bool):
        lower_seed = int(lower_seed)
    if isinstance(lower_seed, str):
        mode = lower_seed.strip().lower()
        if mode in ("exact",):
            if exact is None:
                return 0
            return exact
        if mode in ("exact-1", "exact_minus_1"):
            if exact is None:
                return 0
            return max(0, exact - 1)
        if mode in ("zero", "0"):
            return 0
        try:
            lower_seed = int(mode)
        except ValueError:
            return 0
    if lower_seed is None:
        lower_seed = 0
    try:
        lower_seed = int(lower_seed)
    except (TypeError, ValueError):
        return 0
    if lower_seed < 0:
        lower_seed = 0
    if exact is None:
        return lower_seed
    if lower_seed > exact:
        return exact
    return lower_seed


def _init_ledger(state, lower=0, lower_seed=None, upper_slack=0):
    """Seed the ledger from the oracle at ``lower_seed`` (<= exact per cell).

    ``upper_slack`` widens every finite upper endpoint by that many units, so
    the suite also exercises intervals whose width is not pinned to the exact
    distance (issue #235).  The oracle still contains the seeded interval,
    because slack only ever *raises* an upper endpoint.
    """
    if lower_seed is None:
        lower_seed = lower
    ex = exact_distances(state)
    sector_lowers = {}
    for side in SECTORS:
        sector_lowers[side] = _seed_lower(ex[side], lower_seed)
    full_candidate = _seed_lower(ex["d"], lower_seed)
    finite_sector = [v for v in sector_lowers.values() if v is not None]
    if finite_sector:
        sector_min = min(finite_sector)
        if full_candidate is None:
            full_lower = sector_min
        else:
            full_lower = min(full_candidate, sector_min)
    else:
        full_lower = 0 if full_candidate is None else full_candidate
    if full_lower is None:
        full_lower = 0
    if ex["d"] is None:
        full = pc.Interval(full_lower, None)
    else:
        full = pc.Interval(
            max(full_lower, 0),
            ex["d"] + upper_slack,
        )
    sector = {}
    for side in SECTORS:
        if ex[side] is None:
            sector[side] = pc.Interval(sector_lowers[side], None)
        else:
            sector[side] = pc.Interval(
                max(sector_lowers[side], 0), ex[side] + upper_slack)
    ledger = pc.DistanceLedger(full, sector, witnesses=None, conditions=[])
    # carry challenge-style witnesses if present
    for side in SECTORS:
        if ex[side] is not None:
            support = None
            # find a minimum-weight witness by brute force
            # (reuse exact_distances logic: enumerate subsets)
            pass
    return ledger, ex


def _has_nonzero_lower(ledger):
    """Whether any endpoint of ``ledger``'s lower side is strictly positive."""
    endpoints = [ledger.full.lower]
    endpoints.extend(ledger.sector[side].lower for side in SECTORS)
    return any(endpoint is not None and endpoint > 0 for endpoint in endpoints)


def _note_input(coverage, op_name, ledger):
    """Record one transport of ``op_name`` against its *input* ledger.

    ``coverage`` maps an operation name to transport and nonzero-lower-input
    counts (issue #235): the suite fails unless every admitted operation has
    at least one transport whose input ledger carried a nonzero lower
    endpoint.
    """
    if coverage is None:
        return
    entry = coverage.setdefault(op_name,
                                {"transports": 0, "nonzero_lower_inputs": 0})
    entry["transports"] += 1
    if _has_nonzero_lower(ledger):
        entry["nonzero_lower_inputs"] += 1


def _contains(interval, exact):
    if exact is None:
        # infinite distance: interval must have no finite upper bound
        return interval.upper is None
    # A missing lower endpoint is read as positive infinity, so an interval
    # with no lower bound cannot contain any finite exact distance.
    lower = interval.lower if interval.lower is not None else float("inf")
    if exact < lower:
        return False
    if interval.upper is not None and exact > interval.upper:
        return False
    return True


def _check_ledger(ledger, exact):
    ok = True
    reasons = []
    if not _contains(ledger.full, exact["d"]):
        ok = False
        reasons.append("full interval %s does not contain %s" % (ledger.full.as_json(), exact["d"]))
    for side in SECTORS:
        if not _contains(ledger.sector[side], exact[side]):
            ok = False
            reasons.append("%s interval %s does not contain %s" % (side, ledger.sector[side].as_json(), exact[side]))
    return ok, reasons


def _check_decide(ledger, target):
    '''Verdicts must be justified by the endpoint that justifies them.'''
    if target is None:
        return True, []
    reasons = []
    verdict = ledger.decide(target)
    if verdict == "certify":
        if not (ledger.full.lower is not None and ledger.full.lower >= target):
            reasons.append("certify at target %s but lower endpoint %s" % (target, ledger.full.lower))
    elif verdict == "prune":
        if not (ledger.full.upper is not None and ledger.full.upper < target):
            reasons.append("prune at target %s but upper endpoint %s" % (target, ledger.full.upper))
    # re-measure carries no claim
    return (len(reasons) == 0), reasons



def _check_state_invariants(parent_state, child_state, op_desc):
    """Post-operation state invariants (deliverable 2)."""
    reasons = []
    try:
        child_state.validate()
    except (pc.Malformed, ValueError, TypeError) as e:
        reasons.append("validate() failed: %s" % e)
    # used must not shrink (canonical mint / used = live U retired).
    if not set(parent_state.used).issubset(set(child_state.used)):
        reasons.append("used shrank: parent=%s child=%s" % (sorted(parent_state.used), sorted(child_state.used)))
    # live row identifiers pairwise unique (also in validate, stated here).
    live_ids = [row.id for row in child_state.rows]
    if len(live_ids) != len(set(live_ids)):
        reasons.append("duplicate live row identifiers")
    # live row identifiers subset of used (also in validate).
    if not set(live_ids).issubset(set(child_state.used)):
        reasons.append("live row identifier not in used")
    return (len(reasons) == 0), reasons


def _logical_weights(state, side):
    """Every ``side`` logical of a small state as (support, weight).

    Exhaustive, so it is an oracle-side aid for building the peel prices a
    consumer would supply; the consumer never computes these.
    """
    opposite = "Z" if side == "X" else "X"
    same = [row.mask for row in state.sector_rows(side)]
    other = [row.mask for row in state.sector_rows(opposite)]
    found = []
    labels = list(state.Q)
    for weight in range(1, len(labels) + 1):
        for support in itertools.combinations(labels, weight):
            mask = pc.support_mask(support)
            if pc.commutes(mask, other) and not pc.in_span(mask, same):
                found.append((support, weight))
    return found


def _peel_prices(state, qubit, sector):
    """The two true peel prices of section 4.28 from the oracle: w_expose for
    the opposite sector (one less than the lightest logical through q, or
    None) and w_avoid for the selected sector (the lightest logical avoiding
    q, or None)."""
    opposite = "Z" if sector == "X" else "X"
    expose = [w - 1 for support, w in _logical_weights(state, opposite) if qubit in support]
    avoid = [w for support, w in _logical_weights(state, sector) if qubit not in support]
    return (min(expose) if expose else None), (min(avoid) if avoid else None)


def _all_minimum_classes_killed(state, added_mask, side, base_distance):
    """Whether every weight-base_distance logical (as vectors) is killed."""
    if base_distance is None:
        return False
    same = [row.mask for row in state.sector_rows(side)]
    opposite = [row.mask for row in state.sector_rows("Z" if side == "X" else "X")]
    # enumerate all vectors of exact weight base_distance
    q_labels = list(state.Q)
    for combo in itertools.combinations(q_labels, base_distance):
        mask = 0
        for q in combo:
            mask |= 1 << q
        # logical: commutes with opposite, not in same span
        if not all(_popcount(mask & row) % 2 == 0 for row in opposite):
            continue
        if pc.in_span(mask, same):
            continue
        # killed if odd intersection with added_mask OR in killed span
        if _popcount(mask & added_mask) % 2 == 0:
            # not killed by anticommutation; check killed span not implemented
            # conservatively: not killed
            return False
    return True


def _all_minimum_classes_absorbed(state, added_mask, side, base_distance):
    """Whether every weight-base_distance logical in ``side`` is absorbed."""
    if base_distance is None:
        return False
    same = [row.mask for row in state.sector_rows(side)]
    opposite = [row.mask for row in state.sector_rows("Z" if side == "X" else "X")]
    q_labels = list(state.Q)
    for combo in itertools.combinations(q_labels, base_distance):
        mask = 0
        for q in combo:
            mask |= 1 << q
        if not all(_popcount(mask & row) % 2 == 0 for row in opposite):
            continue
        if pc.in_span(mask, same):
            continue
        if not pc.in_span(mask ^ added_mask, same):
            return False
    return True


def run_case(rng, state, operations_log, hyp_counts=None, lower_seed=0,
             lower=None, hypothesis=None, coverage=None, upper_slack=0):
    """Run one random state through a set of operations; return violations.

    When ``hyp_counts`` is provided it is mutated in place with per-hypothesis
    application counts; when ``coverage`` is provided it is mutated in place
    with per-operation transport and nonzero-lower-input counts (issue #235).
    The return value is the violation list only, so callers that predate the
    counting (including the unit test) keep working.
    """
    if hyp_counts is None:
        hyp_counts = {}
    if lower is not None:
        lower_seed = lower
    violations = []

    def _merge_hyp(hyp):
        if not hypothesis:
            return hyp if hyp is not None else {}
        merged = dict(hypothesis)
        if hyp:
            merged.update(hyp)
        return merged
    # initial ledger
    ledger, ex0 = _init_ledger(state, lower_seed=lower_seed,
                               upper_slack=upper_slack)
    ok, reasons = _check_ledger(ledger, ex0)
    _dok, _dre = _check_decide(ledger, ex0["d"])
    if not _dok:
        ok = False
        reasons = reasons + _dre
    if not ok:
        violations.append({"where": "initial", "reasons": reasons})
    current_state = state
    current_ledger = ledger
    current_exact = ex0

    def record_violation(op_desc, new_state, new_ledger, new_exact, reasons):
        violations.append({
            "operation": op_desc,
            "state_n": len(new_state.Q) if new_state is not None else None,
            "reasons": reasons,
        })

    # 1. C-ADD-CHECK: try a few random supports per sector
    for sector in SECTORS:
        for _ in range(3):
            support = tuple(sorted(rng.sample(list(current_state.Q), rng.randint(1, len(current_state.Q)))))
            # ensure valid added check by attempting
            try:
                new_state = current_state.add_check(sector, support)
            except (pc.NoDerivation, pc.Malformed, ValueError):
                continue
            _inv_ok, _inv_reasons = _check_state_invariants(
                current_state, new_state, "C-ADD-CHECK sector=%s" % sector)
            if not _inv_ok:
                record_violation("C-ADD-CHECK sector=%s" % sector, new_state, None, None, _inv_reasons)
                continue
            new_exact = exact_distances(new_state)
            # ledger transport (unpriced)
            hyp = {}
            # try strict improvement if applicable
            added_mask = 0
            for q in support:
                added_mask |= 1 << q
            base = current_exact["d"]
            if base is not None and current_ledger.full.lower == current_ledger.full.upper == base:
                tau = sector
                sigma = "Z" if sector == "X" else "X"
                improve = True
                if current_exact.get(sigma) == base:
                    if not _all_minimum_classes_killed(current_state, added_mask, sigma, base):
                        improve = False
                if current_exact.get(tau) == base:
                    if not _all_minimum_classes_absorbed(current_state, added_mask, tau, base):
                        improve = False
                if improve:
                    hyp = {"strict_improvement": {
                        "base_distance": base,
                        "all_minimum_classes_killed": True,
                        "enumeration_id": "harness-enumeration",
                    }}
                    hyp_counts["strict_improvement"] = hyp_counts.get("strict_improvement", 0) + 1
            # sector-aware gauging: trust the child sector distance as w_sigma
            if not hyp and new_exact[sector] is not None:
                hyp = {"sector_gauging": {
                    "w_%s" % sector: new_exact[sector],
                    "evidence": "harness",
                }}
                hyp_counts["sector_gauging"] = hyp_counts.get("sector_gauging", 0) + 1
            # direct-sum extinction: only when structural side computes
            if not hyp:
                try:
                    if (pc.tanner_components(current_state) == 2
                            and pc.tanner_components(new_state) == 2):
                        parent_components = pc._tanner_component_of(current_state)
                        added = [q for q in support]
                        if added and all(q in parent_components for q in added):
                            root = parent_components[added[0]]
                            if all(parent_components[q] == root for q in added):
                                block_qs = [q for q in current_state.Q
                                            if parent_components[q] == root]
                                other_qs = [q for q in current_state.Q
                                            if parent_components[q] != root]
                                if (pc._restricted_k(new_state, block_qs) == 0
                                        and other_qs
                                        and pc._restricted_k(current_state, other_qs) >= 1
                                        and base is not None
                                        and new_exact["d"] is not None
                                        and new_exact["d"] > base
                                        and current_ledger.full.lower == current_ledger.full.upper == base):
                                    hyp = {"direct_sum_extinction": {
                                        "base_distance": base,
                                        "factor_distance": new_exact["d"],
                                        "evidence": "harness",
                                    }}
                                    hyp_counts["direct_sum_extinction"] = hyp_counts.get("direct_sum_extinction", 0) + 1
                except (KeyError, TypeError, ValueError, AttributeError, IndexError):
                    hyp = hyp or {}
            op = {"op": "C-ADD-CHECK"}
            _note_input(coverage, "C-ADD-CHECK", current_ledger)
            new_ledger = current_ledger.propagate(op, new_state, hypothesis=_merge_hyp(hyp), observations={})
            ok, reasons = _check_ledger(new_ledger, new_exact)
            _dok, _dre = _check_decide(new_ledger, new_exact["d"])
            if not _dok:
                ok = False
                reasons = reasons + _dre
            if not ok:
                record_violation("C-ADD-CHECK sector=%s" % sector, new_state, new_ledger, new_exact, reasons)

    # 2. C-DELETE-CHECK: try deleting a random row
    if current_state.rows:
        row = rng.choice(current_state.rows)
        try:
            new_state = current_state.delete_check(row.id)
        except (pc.NoDerivation, pc.Malformed, ValueError):
            new_state = None
        if new_state is not None:
            _inv_ok, _inv_reasons = _check_state_invariants(
                current_state, new_state, "C-DELETE-CHECK id=%s" % row.id)
            if not _inv_ok:
                record_violation("C-DELETE-CHECK id=%s" % row.id, new_state, None, None, _inv_reasons)
            else:
                op = {"op": "C-DELETE-CHECK", "row_id": row.id}
                # unpriced
                _note_input(coverage, "C-DELETE-CHECK", current_ledger)
                new_ledger = current_ledger.propagate(op, new_state, hypothesis=_merge_hyp({}), observations={}, parent_state=current_state)
                new_exact = exact_distances(new_state)
                ok, reasons = _check_ledger(new_ledger, new_exact)
                _dok, _dre = _check_decide(new_ledger, new_exact["d"])
                if not _dok:
                    ok = False
                    reasons = reasons + _dre
                if not ok:
                    record_violation("C-DELETE-CHECK id=%s (unpriced)" % row.id, new_state, new_ledger, new_exact, reasons)
                # priced with true-ish sector prices: w_del for the deleted
                # sector, w_exp for the opposite sector.
                _deleted_sector = row.sector
                _other_sector = "Z" if _deleted_sector == "X" else "X"
                _w_del = new_exact[_deleted_sector]
                if _w_del is None:
                    _w_del = 10
                _w_exp = new_exact[_other_sector]
                if _w_exp is None:
                    _w_exp = 10
                hyp = {"deletion_price": {"w_del": _w_del, "w_exp": _w_exp, "evidence": "harness"}}
                hyp_counts["deletion_price"] = hyp_counts.get("deletion_price", 0) + 1
                try:
                    _note_input(coverage, "C-DELETE-CHECK", current_ledger)
                    new_ledger2 = current_ledger.propagate(op, new_state, hypothesis=_merge_hyp(hyp), observations={}, parent_state=current_state)
                    ok2, reasons2 = _check_ledger(new_ledger2, new_exact)
                    _dok2, _dre2 = _check_decide(new_ledger2, new_exact["d"])
                    if not _dok2:
                        ok2 = False
                        reasons2 = reasons2 + _dre2
                    if not ok2:
                        record_violation("C-DELETE-CHECK id=%s (priced)" % row.id, new_state, new_ledger2, new_exact, reasons2)
                except (pc.NoDerivation, pc.Malformed, ValueError):
                    pass

    # 3. E-GRAFT: try each qubit/sector with a random ordering
    for qubit in list(current_state.Q):
        for sector in SECTORS:
            touching = [r for r in current_state.sector_rows(sector) if qubit in r.support]
            if not touching:
                continue
            opposite = "Z" if sector == "X" else "X"
            # The source's spliced-sector-unchanged relation assumes the
            # grafted qubit is present in the opposite sector; otherwise the
            # selected sector can lose a logical supported on q. Such grafts
            # are outside the relation's domain (see the guard proposed in
            # the companion E-GRAFT applicability PR).
            if not any(qubit in r.support for r in current_state.sector_rows(opposite)):
                continue
            ordered = [r.id for r in touching]
            rng.shuffle(ordered)
            try:
                new_state = current_state.graft(qubit, sector, ordered)
            except (pc.NoDerivation, pc.Malformed, ValueError):
                continue
            _inv_ok, _inv_reasons = _check_state_invariants(
                current_state, new_state, "E-GRAFT q=%s sector=%s" % (qubit, sector))
            if not _inv_ok:
                record_violation("E-GRAFT q=%s sector=%s" % (qubit, sector), new_state, None, None, _inv_reasons)
                continue
            op = {"op": "E-GRAFT", "sector": sector, "qubit": qubit}
            _note_input(coverage, "E-GRAFT", current_ledger)
            new_ledger = current_ledger.propagate(op, new_state, hypothesis=_merge_hyp({}), observations={}, parent_state=current_state)
            new_exact = exact_distances(new_state)
            ok, reasons = _check_ledger(new_ledger, new_exact)
            _dok, _dre = _check_decide(new_ledger, new_exact["d"])
            if not _dok:
                ok = False
                reasons = reasons + _dre
            if not ok:
                record_violation("E-GRAFT q=%s sector=%s" % (qubit, sector), new_state, new_ledger, new_exact, reasons)
            # with graft price
            price = new_exact["X" if sector == "Z" else "Z"]
            if price is None:
                price = 10
            hyp = {"graft_price": {"w_expose": price, "evidence": "harness"}}
            hyp_counts["graft_price"] = hyp_counts.get("graft_price", 0) + 1
            try:
                _note_input(coverage, "E-GRAFT", current_ledger)
                new_ledger2 = current_ledger.propagate(op, new_state, hypothesis=_merge_hyp(hyp), observations={}, parent_state=current_state)
                ok2, reasons2 = _check_ledger(new_ledger2, new_exact)
                _dok2, _dre2 = _check_decide(new_ledger2, new_exact["d"])
                if not _dok2:
                    ok2 = False
                    reasons2 = reasons2 + _dre2
                if not ok2:
                    record_violation("E-GRAFT q=%s sector=%s (priced)" % (qubit, sector), new_state, new_ledger2, new_exact, reasons2)
            except (pc.NoDerivation, pc.Malformed, ValueError):
                pass

    # 3b. E-PEEL: every unique-touch peel, unpriced and priced.
    # Section 4.28: d_tau' = w_avoid,tau(q) for the selected sector and
    # d_sigma' = min(d_sigma, w_expose,sigma(q)) for the opposite sector,
    # so the unpriced ledger carries the selected lower, the opposite lower
    # less one, the opposite upper, and the minimum for the full distance;
    # the priced ledger pins the sectors. The prices come from the oracle
    # here, as a consumer's would come from its own enumeration.
    for qubit in list(current_state.Q):
        for sector in SECTORS:
            touching = [r for r in current_state.sector_rows(sector) if qubit in r.support]
            if len(touching) != 1:
                continue
            try:
                new_state = current_state.peel(qubit, sector, touching[0].id)
            except (pc.NoDerivation, pc.Malformed, ValueError):
                continue
            desc = "E-PEEL q=%s sector=%s" % (qubit, sector)
            _inv_ok, _inv_reasons = _check_state_invariants(current_state, new_state, desc)
            if not _inv_ok:
                record_violation(desc, new_state, None, None, _inv_reasons)
                continue
            op = {"op": "E-PEEL", "qubit": qubit, "sector": sector,
                  "row_id": touching[0].id}
            new_exact = exact_distances(new_state)
            _note_input(coverage, "E-PEEL", current_ledger)
            new_ledger = current_ledger.propagate(op, new_state, hypothesis=_merge_hyp({}),
                                                  observations={})
            ok, reasons = _check_ledger(new_ledger, new_exact)
            _dok, _dre = _check_decide(new_ledger, new_exact["d"])
            if not _dok:
                ok = False
                reasons = reasons + _dre
            if not ok:
                record_violation(desc + " (unpriced)", new_state, new_ledger, new_exact, reasons)
            w_expose, w_avoid = _peel_prices(current_state, qubit, sector)
            price = {"evidence": "harness oracle"}
            if w_expose is not None:
                price["w_expose"] = w_expose
            if w_avoid is not None:
                price["w_avoid"] = w_avoid
            if len(price) == 1:
                continue
            hyp_counts["peel_price"] = hyp_counts.get("peel_price", 0) + 1
            try:
                _note_input(coverage, "E-PEEL", current_ledger)
                new_ledger2 = current_ledger.propagate(op, new_state,
                                                       hypothesis=_merge_hyp({"peel_price": price}),
                                                       observations={})
            except (pc.NoDerivation, pc.Malformed, ValueError) as exc:
                record_violation(desc + " (priced)", new_state, None, new_exact,
                                 ["true prices refused: %s" % exc])
                continue
            ok2, reasons2 = _check_ledger(new_ledger2, new_exact)
            _dok2, _dre2 = _check_decide(new_ledger2, new_exact["d"])
            if not _dok2:
                ok2 = False
                reasons2 = reasons2 + _dre2
            # The two cells are exact: with both prices supplied the sector
            # intervals must pin the oracle's values, not merely contain them.
            opposite = "Z" if sector == "X" else "X"
            if w_avoid is not None and new_exact[sector] is not None and \
                    new_ledger2.sector[sector] != pc.Interval(new_exact[sector], new_exact[sector]):
                ok2 = False
                reasons2.append("selected sector %s not pinned by w_avoid=%s: %s vs exact %s"
                                % (sector, w_avoid, new_ledger2.sector[sector].as_json(),
                                   new_exact[sector]))
            if (w_expose is not None and new_exact[opposite] is not None
                    and current_ledger.sector[opposite].lower == current_ledger.sector[opposite].upper
                    and new_ledger2.sector[opposite] != pc.Interval(new_exact[opposite],
                                                                    new_exact[opposite])):
                ok2 = False
                reasons2.append("opposite sector %s not pinned by w_expose=%s from an exact "
                                "parent interval: %s vs exact %s"
                                % (opposite, w_expose, new_ledger2.sector[opposite].as_json(),
                                   new_exact[opposite]))
            if not ok2:
                record_violation(desc + " (priced)", new_state, new_ledger2, new_exact, reasons2)

    # 3c. E-SPLIT: separating deletion over a random block cut, unpriced and priced.
    if len(current_state.Q) >= 2:
        size = rng.randint(1, len(current_state.Q) - 1)
        block = sorted(rng.sample(list(current_state.Q), size))
        crossing_ids = [row.id for row in current_state.crossing_rows(block)]
        others = [row.id for row in current_state.rows if row.id not in crossing_ids]
        extra = rng.sample(others, rng.randint(0, min(1, len(others)))) if others else []
        cut_ids = crossing_ids + extra
        try:
            new_state = current_state.split(block, cut_ids)
        except (pc.NoDerivation, pc.Malformed, ValueError):
            new_state = None
        if new_state is not None:
            desc = "E-SPLIT block=%s cut=%s" % (block, cut_ids)
            _inv_ok, _inv_reasons = _check_state_invariants(current_state, new_state, desc)
            if not _inv_ok:
                record_violation(desc, new_state, None, None, _inv_reasons)
            else:
                op = {"op": "E-SPLIT", "block": block, "cut_ids": cut_ids}
                new_exact = exact_distances(new_state)
                _note_input(coverage, "E-SPLIT", current_ledger)
                new_ledger = current_ledger.propagate(
                    op, new_state, hypothesis=_merge_hyp({}),
                    observations={}, parent_state=current_state,
                )
                ok, reasons = _check_ledger(new_ledger, new_exact)
                _dok, _dre = _check_decide(new_ledger, new_exact["d"])
                if not _dok:
                    ok = False
                    reasons = reasons + _dre
                if not ok:
                    record_violation(desc + " (unpriced)", new_state, new_ledger, new_exact, reasons)
                # Priced cell: oracle block intervals for restriction displays A and B.
                bset = set(block)
                comp = tuple(q for q in new_state.Q if q not in bset)
                rows_a = tuple(row for row in new_state.rows if set(row.support) <= bset)
                rows_b = tuple(row for row in new_state.rows if set(row.support) <= set(comp))
                part_a = pc.CodeState(tuple(block), rows_a, frozenset(row.id for row in rows_a))
                part_b = pc.CodeState(comp, rows_b, frozenset(row.id for row in rows_b))
                part_a.validate()
                part_b.validate()
                ex_a = exact_distances(part_a)
                ex_b = exact_distances(part_b)
                split_hyp = {"evidence": "harness oracle"}
                for side in SECTORS:
                    da, db = ex_a[side], ex_b[side]
                    la = None if da is None else _seed_lower(da, lower_seed)
                    lb = None if db is None else _seed_lower(db, lower_seed)
                    ua = None if da is None else da + upper_slack
                    ub = None if db is None else db + upper_slack
                    split_hyp[side] = {"A": [la, ua], "B": [lb, ub]}
                hyp_counts["split_block_intervals"] = hyp_counts.get("split_block_intervals", 0) + 1
                try:
                    _note_input(coverage, "E-SPLIT", current_ledger)
                    new_ledger2 = current_ledger.propagate(
                        op, new_state,
                        hypothesis=_merge_hyp({"split_block_intervals": split_hyp}),
                        observations={}, parent_state=current_state,
                    )
                    ok2, reasons2 = _check_ledger(new_ledger2, new_exact)
                    _dok2, _dre2 = _check_decide(new_ledger2, new_exact["d"])
                    if not _dok2:
                        ok2 = False
                        reasons2 = reasons2 + _dre2
                    if not ok2:
                        record_violation(desc + " (priced)", new_state, new_ledger2, new_exact, reasons2)
                except (pc.NoDerivation, pc.Malformed, ValueError) as exc:
                    record_violation(desc + " (priced)", new_state, None, new_exact,
                                     ["true block intervals refused: %s" % exc])

    # 4. C-DIRECT-SUM: combine with a second disjoint state
    try:
        small_other = random_state(rng, list(range(rng.randint(2, 5))), id_prefixes=("c", "d"))
        offset = (max(current_state.Q) if current_state.Q else 0) + 1
        other_q = tuple(q + offset for q in small_other.Q)
        other_rows = tuple(
            pc.Row(row.id, row.sector, tuple(q + offset for q in row.support))
            for row in small_other.rows
        )
        other = pc.CodeState(other_q, other_rows, small_other.used)
        other.validate()
        new_state = pc.CodeState.direct_sum(current_state, other)
        _inv_ok, _inv_reasons = _check_state_invariants(
            current_state, new_state, "C-DIRECT-SUM")
        if not _inv_ok:
            record_violation("C-DIRECT-SUM", new_state, None, None, _inv_reasons)
            raise RuntimeError("invariants")
        # ledger direct sum: need a second ledger for other
        other_ledger, other_exact = _init_ledger(
            other, lower_seed=lower_seed, upper_slack=upper_slack)
        # combine ledgers via DistanceLedger.direct_sum
        _note_input(coverage, "C-DIRECT-SUM", current_ledger)
        combined_ledger = pc.DistanceLedger.direct_sum(current_ledger, other_ledger)
        new_exact = exact_distances(new_state)
        ok, reasons = _check_ledger(combined_ledger, new_exact)
        _dok, _dre = _check_decide(combined_ledger, new_exact["d"])
        if not _dok:
            ok = False
            reasons = reasons + _dre
        if not ok:
            record_violation("C-DIRECT-SUM", new_state, combined_ledger, new_exact, reasons)
    except (pc.NoDerivation, pc.Malformed, ValueError, RuntimeError):
        pass

    # 5. C-SEQUENCE: apply two operations in sequence (skip then add) - already covered by sequential
    # (no separate rule beyond composition; skip identity)
    try:
        new_state = current_state.skip()
        _inv_ok, _inv_reasons = _check_state_invariants(current_state, new_state, "C-SKIP")
        if not _inv_ok:
            record_violation("C-SKIP", new_state, None, None, _inv_reasons)
            raise RuntimeError("invariants")
        _note_input(coverage, "C-SKIP", current_ledger)
        new_ledger = current_ledger.propagate({"op": "C-SKIP"}, new_state, hypothesis=_merge_hyp({}), observations={})
        new_exact = exact_distances(new_state)
        ok, reasons = _check_ledger(new_ledger, new_exact)
        if not ok:
            record_violation("C-SKIP", new_state, new_ledger, new_exact, reasons)
    except (pc.NoDerivation, pc.Malformed, ValueError, RuntimeError):
        pass

    return violations


def seeded_stack_extinction_case(rng, hyp_counts, coverage=None):
    """A seeded stack-parent family so direct-sum extinction actually fires."""
    violations = []
    state = pc.CodeState(
        (0, 1, 2, 3, 4, 5),
        (pc.Row("a9001", "X", (0, 1)),
         pc.Row("a9002", "X", (2, 3, 4, 5)),
         pc.Row("b9001", "Z", (2, 3, 4, 5))),
        frozenset(("a9001", "a9002", "b9001")),
    )
    child = state.add_check("Z", (0, 1))
    operation = {"op": "C-ADD-CHECK", "sector": "Z", "support": [0, 1]}
    _inv_ok, _inv_reasons = _check_state_invariants(state, child, "C-ADD-CHECK (seeded stack extinction)")
    if not _inv_ok:
        return [{"operation": "C-ADD-CHECK (seeded stack extinction)", "state_n": len(child.Q), "reasons": _inv_reasons}]
    ex0 = exact_distances(state)
    ledger = pc.DistanceLedger(
        pc.Interval(ex0["d"], ex0["d"]),
        {side: pc.Interval(0, ex0[side]) for side in SECTORS},
    )
    hyp = {"direct_sum_extinction": {
        "base_distance": ex0["d"],
        "factor_distance": exact_distances(child)["d"],
        "evidence": "harness-seeded",
    }}
    hyp_counts["direct_sum_extinction"] = hyp_counts.get("direct_sum_extinction", 0) + 1
    _note_input(coverage, "C-ADD-CHECK", ledger)
    try:
        new_ledger = ledger.propagate(operation, child, hypothesis=hyp, parent_state=state)
        new_exact = exact_distances(child)
        ok, reasons = _check_ledger(new_ledger, new_exact)
        _dok, _dre = _check_decide(new_ledger, new_exact["d"])
        if not _dok:
            ok = False
            reasons = reasons + _dre
        if not ok:
            violations.append({"operation": "C-ADD-CHECK (seeded stack extinction)",
                               "state_n": len(child.Q), "reasons": reasons})
    except (pc.NoDerivation, pc.Malformed, ValueError, TypeError, KeyError) as e:
        violations.append({"operation": "C-ADD-CHECK (seeded stack extinction)",
                           "state_n": len(child.Q), "reasons": [str(e)]})
    return violations


def run_suite(cases=DEFAULT_CASES, seed=DEFAULT_SEED):
    """Run the suite and return its report dict (violations and coverage).

    Exposed separately from ``main`` so tests can assert the per-operation
    nonzero-lower coverage (issue #235) without writing a report file.
    """
    rng = random.Random(seed)
    total_violations = 0
    violation_shapes = []
    per_op_counts = {}
    hyp_counts = {}
    coverage = {}
    lower_seed_counts = {}
    cases_attempted = 0
    for case_index in range(cases):
        # Issue #235: seed nonzero lower endpoints, not 0 everywhere.  The
        # first sixteen cases are forced nonzero so every fast operation sees
        # one even in a short run; the rest randomize L (and a little
        # upper-endpoint slack, i.e. interval width) across the small states.
        if case_index < 16:
            lower_seed = 1 + (case_index % 3)
            upper_slack = case_index % 2
        else:
            lower_seed = rng.choice((0, 1, 1, 2, 3))
            upper_slack = rng.choice((0, 0, 1))
        lower_seed_counts[str(lower_seed)] = lower_seed_counts.get(str(lower_seed), 0) + 1
        n = rng.randint(3, 7)
        q_labels = list(range(n))
        try:
            state = random_state(rng, q_labels)
        except RuntimeError:
            continue
        cases_attempted += 1
        vs = run_case(rng, state, [], hyp_counts, lower_seed=lower_seed,
                      coverage=coverage, upper_slack=upper_slack)
        total_violations += len(vs)
        for v in vs:
            op = v["operation"].split()[0]
            per_op_counts[op] = per_op_counts.get(op, 0) + 1
            if len(violation_shapes) < 20:
                violation_shapes.append(v)
    # Seeded stack-parent family so the direct-sum-extinction cell fires.
    vs = seeded_stack_extinction_case(rng, hyp_counts, coverage)
    total_violations += len(vs)
    for v in vs:
        op = v["operation"].split()[0]
        per_op_counts[op] = per_op_counts.get(op, 0) + 1
        if len(violation_shapes) < 20:
            violation_shapes.append(v)

    # Issue #235 acceptance: every admitted operation must be transited at
    # least once with a nonzero lower endpoint on its input ledger.
    unexercised = [op for op in ADMITTED_OPERATIONS
                   if coverage.get(op, {}).get("transports", 0) == 0]
    without_nonzero_lower = [op for op in ADMITTED_OPERATIONS
                             if coverage.get(op, {}).get("nonzero_lower_inputs", 0) == 0]

    report = {
        "harness": "priced_conformance_harness",
        "git_commit": _git_commit(),
        "cases_attempted": cases_attempted,
        "total_violations": total_violations,
        "per_operation_violation_counts": per_op_counts,
        "hypothesis_application_counts": hyp_counts,
        "lower_seed_counts": lower_seed_counts,
        "coverage_by_operation": coverage,
        "admitted_operations": list(ADMITTED_OPERATIONS),
        "admitted_operations_never_transited": unexercised,
        "admitted_operations_without_nonzero_lower_case": without_nonzero_lower,
        "violation_shapes": violation_shapes,
        "note": "Evidence only. Does not discharge OBL-PRICED-INTERVAL-SOUNDNESS.",
    }
    return report


def _git_commit():
    try:
        commit = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, stderr=subprocess.DEVNULL
        ).decode().strip()
    except (OSError, subprocess.SubprocessError):
        commit = "unknown"
    return commit


def _report_path():
    """Where the JSON report goes; never a tracked repository path."""
    override = os.environ.get("PRICED_CONFORMANCE_REPORT")
    if override == "-":
        return None
    if override:
        return override
    return DEFAULT_REPORT_PATH


def main():
    cases = DEFAULT_CASES
    raw_cases = os.environ.get("PRICED_CONFORMANCE_CASES")
    if raw_cases:
        try:
            cases = max(1, int(raw_cases))
        except ValueError:
            print("ignoring non-integer PRICED_CONFORMANCE_CASES=%r" % raw_cases)
    report = run_suite(cases=cases)
    print(json.dumps({k: report[k] for k in (
        "cases_attempted", "total_violations",
        "per_operation_violation_counts", "lower_seed_counts",
        "coverage_by_operation",
        "admitted_operations_never_transited",
        "admitted_operations_without_nonzero_lower_case")}, indent=2))

    # Write the report to an untracked path only: a run must never dirty a
    # tracked file (issue #235, TODO item 12).
    out_path = _report_path()
    if out_path:
        try:
            parent = os.path.dirname(os.path.abspath(out_path))
            if parent:
                os.makedirs(parent, exist_ok=True)
            with open(out_path, "w") as f:
                json.dump(report, f, indent=2)
            print("report written to %s" % out_path)
        except OSError as exc:
            print("report not written (%s)" % exc)

    failures = []
    if report["total_violations"]:
        failures.append("%d interval violations" % report["total_violations"])
    if report["admitted_operations_never_transited"]:
        failures.append("admitted operations never transited: %s"
                        % ", ".join(report["admitted_operations_never_transited"]))
    if report["admitted_operations_without_nonzero_lower_case"]:
        failures.append(
            "admitted operations without a nonzero-lower-endpoint case: %s"
            % ", ".join(report["admitted_operations_without_nonzero_lower_case"]))
    # fail build on any violation or coverage gap
    if failures:
        raise SystemExit("; ".join(failures))


if __name__ == "__main__":
    main()
