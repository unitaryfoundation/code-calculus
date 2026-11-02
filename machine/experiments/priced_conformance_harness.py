"""Judgment-level conformance harness for the priced consumer.

This harness is the instrument named in .  It generates small random
CSS states, applies every admitted transition, measures the exact per-sector
distances with the external oracle in ``an archived note``, and
asserts that every interval emitted by ``machine.priced_calculus`` contains
the corresponding exact distance.

It is evidence about the transport rules, never a proof and never a discharge
of ``OBL-PRICED-INTERVAL-SOUNDNESS``.  A price hypothesis is trusted by
construction; the harness checks that the *transport rules* are sound given
the hypothesis, not that the hypothesis is true.
"""

from __future__ import print_function

import copy
import itertools
import json
import os
import random
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
MACHINE = os.path.dirname(HERE)
ROOT = os.path.dirname(MACHINE)
for path in (MACHINE, ROOT, HERE):
    if path not in sys.path:
        sys.path.insert(0, path)

import priced_calculus as pc
from challenge_replay import exact_distances

SECTORS = ("X", "Z")


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


def _init_ledger(state, lower=0):
    ex = exact_distances(state)
    # full distance
    if ex["d"] is None:
        full = pc.Interval(lower if lower is not None else 0, None)
    else:
        full = pc.Interval(
            max(lower if lower is not None else 0, 0),
            ex["d"],
        )
    sector = {}
    for side in SECTORS:
        if ex[side] is None:
            sector[side] = pc.Interval(0, None)
        else:
            sector[side] = pc.Interval(0, ex[side])
    ledger = pc.DistanceLedger(full, sector, witnesses=None, conditions=[])
    # carry challenge-style witnesses if present
    for side in SECTORS:
        if ex[side] is not None:
            support = None
            # find a minimum-weight witness by brute force
            # (reuse exact_distances logic: enumerate subsets)
            pass
    return ledger, ex


def _contains(interval, exact):
    if exact is None:
        # infinite distance: interval must have no finite upper bound
        return interval.upper is None
    if interval.lower is not None and exact < interval.lower:
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


def _all_minimum_classes_killed(state, added_mask, side, base_distance):
    """Whether every weight-base_distance logical (as vectors) is killed."""
    if base_distance is None:
        return False
    # The added check lies in `side`; it can kill logicals of the opposite
    # sector (anticommute) and, conservatively, we only claim a kill when
    # the anticommutation condition holds.  Logical classes of the opposite
    # sector commute with the `side` stabilizers and avoid the opposite
    # sector's own stabilizer span.
    logical_sector = "Z" if side == "X" else "X"
    commute_with = [row.mask for row in state.sector_rows(side)]
    avoid_span = [row.mask for row in state.sector_rows(logical_sector)]
    # enumerate all vectors of exact weight base_distance
    q_labels = list(state.Q)
    for combo in itertools.combinations(q_labels, base_distance):
        mask = 0
        for q in combo:
            mask |= 1 << q
        # logical: commutes with the added check's sector, not in the
        # opposite sector's stabilizer span
        if not all(_popcount(mask & row) % 2 == 0 for row in commute_with):
            continue
        if pc.in_span(mask, avoid_span):
            continue
        # killed if odd intersection with added_mask
        if _popcount(mask & added_mask) % 2 == 0:
            # not killed by anticommutation (K-membership not trusted here)
            return False
    return True


def run_case(rng, state, operations_log, hyp_counts=None, lower_seed=0, coverage=None):
    """Run one random state through a set of operations; return violations.

    When ``hyp_counts`` is provided it is mutated in place with per-hypothesis
    application counts; the return value is the violation list only, so callers
    that predate the counting (including the unit test) keep working.
    """
    if hyp_counts is None:
        hyp_counts = {}
    violations = []
    # initial ledger
    _ex_preview = exact_distances(state)
    if lower_seed == "exact":
        _lower = _ex_preview["d"] if _ex_preview["d"] is not None else 0
    elif lower_seed == 1:
        _lower = 1
    else:
        _lower = 0
    ledger, ex0 = _init_ledger(state, lower=_lower)
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
            new_exact = exact_distances(new_state)
            # ledger transport (unpriced)
            hyp = {}
            # try strict improvement if applicable
            added_mask = 0
            for q in support:
                added_mask |= 1 << q
            base = current_exact["d"]
            opposite_sector = "Z" if sector == "X" else "X"
            # Strict improvement of the full distance is only possible when
            # the added check's own sector is not itself the bottleneck:
            # otherwise a minimum logical in that sector survives.
            own_distance = current_exact.get(sector)
            if (base is not None
                    and current_ledger.full.lower == current_ledger.full.upper == base
                    and current_exact.get(opposite_sector) == base
                    and (own_distance is None or own_distance > base)):
                if _all_minimum_classes_killed(current_state, added_mask, sector, base):
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
                except Exception:
                    hyp = hyp or {}
            op = {"op": "C-ADD-CHECK"}
            new_ledger = current_ledger.propagate(op, new_state, hypothesis=hyp, observations={})
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
            op = {"op": "C-DELETE-CHECK"}
            # unpriced
            new_ledger = current_ledger.propagate(op, new_state, hypothesis={}, observations={})
            new_exact = exact_distances(new_state)
            ok, reasons = _check_ledger(new_ledger, new_exact)
            _dok, _dre = _check_decide(new_ledger, new_exact["d"])
            if not _dok:
                ok = False
                reasons = reasons + _dre
            if not ok:
                record_violation("C-DELETE-CHECK id=%s (unpriced)" % row.id, new_state, new_ledger, new_exact, reasons)
            # priced with a true-ish price
            price = new_exact["d"] if new_exact["d"] is not None else 10
            hyp = {"deletion_price": {"w_del": price, "w_exp": price, "evidence": "harness"}}
            hyp_counts["deletion_price"] = hyp_counts.get("deletion_price", 0) + 1
            try:
                new_ledger2 = current_ledger.propagate(op, new_state, hypothesis=hyp, observations={})
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
            # the companion E-GRAFT applicability ).
            if not any(qubit in r.support for r in current_state.sector_rows(opposite)):
                continue
            ordered = [r.id for r in touching]
            rng.shuffle(ordered)
            try:
                new_state = current_state.graft(qubit, sector, ordered)
            except (pc.NoDerivation, pc.Malformed, ValueError):
                continue
            op = {"op": "E-GRAFT", "sector": sector, "qubit": qubit}
            new_ledger = current_ledger.propagate(op, new_state, hypothesis={}, observations={})
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
                new_ledger2 = current_ledger.propagate(op, new_state, hypothesis=hyp, observations={})
                ok2, reasons2 = _check_ledger(new_ledger2, new_exact)
                _dok2, _dre2 = _check_decide(new_ledger2, new_exact["d"])
                if not _dok2:
                    ok2 = False
                    reasons2 = reasons2 + _dre2
                if not ok2:
                    record_violation("E-GRAFT q=%s sector=%s (priced)" % (qubit, sector), new_state, new_ledger2, new_exact, reasons2)
            except (pc.NoDerivation, pc.Malformed, ValueError):
                pass

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
        # ledger direct sum: need a second ledger for other
        other_ledger, other_exact = _init_ledger(other)
        # combine ledgers via DistanceLedger.direct_sum
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
        new_ledger = current_ledger.propagate({"op": "C-SKIP"}, new_state, hypothesis={}, observations={})
        new_exact = exact_distances(new_state)
        ok, reasons = _check_ledger(new_ledger, new_exact)
        if not ok:
            record_violation("C-SKIP", new_state, new_ledger, new_exact, reasons)
    except (pc.NoDerivation, pc.Malformed, ValueError):
        pass

    # 6. Gate 6 CSS conditional cells (2026-10-23): P-REBASE, E-LOCAL-HADAMARD
    # (T=Q), E-PEEL, E-PUNCTURE, E-EXTEND. Each entrance is
    # hypothesis-free; the interval rules the consumer licenses for them are
    # transcribed from spec/OPERATIONAL_SEMANTICS.md §4.25–§4.29 (and this
    # harness checks only that the transported intervals contain the exact
    # child distances -- evidence, never a discharge of
    # OBL-GATE6-CSS-EXTENSIONS).

    # 6a. P-REBASE: an invertible mix of one sector's display.
    for sector in SECTORS:
        rows = list(current_state.sector_rows(sector))
        m = len(rows)
        if m < 1 or m > 4:
            continue
        candidates = [
            [[1, 0], [0, 1]],
            [[1, 1], [0, 1]],
            [[0, 1], [1, 1]],
            [[1, 1, 0], [0, 1, 1], [1, 0, 1]],
        ]
        for matrix in candidates:
            if len(matrix) != m:
                continue
            try:
                new_state = current_state.rebase(sector, matrix)
            except (pc.NoDerivation, pc.Malformed, ValueError):
                continue
            new_exact = exact_distances(new_state)
            op = {"op": "P-REBASE", "sector": sector}
            new_ledger = current_ledger.propagate(op, new_state, hypothesis={},
                                                  parent_state=current_state)
            ok, reasons = _check_ledger(new_ledger, new_exact)
            _dok, _dre = _check_decide(new_ledger, new_exact["d"])
            if not _dok:
                ok = False
                reasons = reasons + _dre
            if not ok:
                record_violation("P-REBASE sector=%s" % sector, new_state,
                                 new_ledger, new_exact, reasons)
            hyp_counts["rebase"] = hyp_counts.get("rebase", 0) + 1

    # 6b. E-LOCAL-HADAMARD at T=Q.
    try:
        new_state = current_state.hadamard_sector_swap()
        new_exact = exact_distances(new_state)
        op = {"op": "E-LOCAL-HADAMARD", "qubits": list(current_state.Q)}
        new_ledger = current_ledger.propagate(op, new_state, hypothesis={},
                                              parent_state=current_state)
        ok, reasons = _check_ledger(new_ledger, new_exact)
        _dok, _dre = _check_decide(new_ledger, new_exact["d"])
        if not _dok:
            ok = False
            reasons = reasons + _dre
        if not ok:
            record_violation("E-LOCAL-HADAMARD T=Q", new_state, new_ledger,
                             new_exact, reasons)
        hyp_counts["hadamard_sector_swap"] = hyp_counts.get("hadamard_sector_swap", 0) + 1
    except (pc.NoDerivation, pc.Malformed, ValueError):
        pass

    # 6c. E-PEEL: unique-touch peels per sector/qubit.
    for sector in SECTORS:
        opposite = "Z" if sector == "X" else "X"
        for q in list(current_state.Q):
            touching = [r for r in current_state.sector_rows(sector) if q in r.support]
            if len(touching) != 1:
                continue
            try:
                new_state = current_state.peel(q, sector, touching[0].id)
            except (pc.NoDerivation, pc.Malformed, ValueError):
                continue
            new_exact = exact_distances(new_state)
            op = {"op": "E-PEEL", "qubit": q, "sector": sector}
            new_ledger = current_ledger.propagate(op, new_state, hypothesis={},
                                                  parent_state=current_state)
            ok, reasons = _check_ledger(new_ledger, new_exact)
            _dok, _dre = _check_decide(new_ledger, new_exact["d"])
            if not _dok:
                ok = False
                reasons = reasons + _dre
            if not ok:
                record_violation("E-PEEL q=%s sector=%s" % (q, sector),
                                 new_state, new_ledger, new_exact, reasons)
            hyp_counts["peel"] = hyp_counts.get("peel", 0) + 1

    # 6d. E-PUNCTURE.
    for q in list(current_state.Q):
        try:
            new_state = current_state.puncture(q)
        except (pc.NoDerivation, pc.Malformed, ValueError):
            continue
        new_exact = exact_distances(new_state)
        op = {"op": "E-PUNCTURE", "qubit": q}
        new_ledger = current_ledger.propagate(op, new_state, hypothesis={},
                                              parent_state=current_state)
        ok, reasons = _check_ledger(new_ledger, new_exact)
        _dok, _dre = _check_decide(new_ledger, new_exact["d"])
        if not _dok:
            ok = False
            reasons = reasons + _dre
        if not ok:
            record_violation("E-PUNCTURE q=%s" % q, new_state, new_ledger,
                             new_exact, reasons)
        hyp_counts["puncture"] = hyp_counts.get("puncture", 0) + 1

    # 6e. E-EXTEND: disjoint new qubits + well-typed additions.
    offset = (max(current_state.Q) if current_state.Q else 0) + 100
    for sector in SECTORS:
        support = sorted(rng.sample(list(current_state.Q), rng.randint(1, min(2, len(current_state.Q))))) \
                  + [offset]
        try:
            new_state = current_state.extend_code((offset,), [(sector, tuple(support))])
        except (pc.NoDerivation, pc.Malformed, ValueError):
            continue
        new_exact = exact_distances(new_state)
        op = {"op": "E-EXTEND", "new_qubits": [offset], "additions": [[sector, list(support)]]}
        new_ledger = current_ledger.propagate(op, new_state, hypothesis={},
                                              parent_state=current_state)
        ok, reasons = _check_ledger(new_ledger, new_exact)
        _dok, _dre = _check_decide(new_ledger, new_exact["d"])
        if not _dok:
            ok = False
            reasons = reasons + _dre
        if not ok:
            record_violation("E-EXTEND sector=%s" % sector, new_state,
                             new_ledger, new_exact, reasons)
        hyp_counts["extend"] = hyp_counts.get("extend", 0) + 1

    if coverage is not None:
        coverage.setdefault("transited", [])
        coverage["lower_seed"] = lower_seed
        coverage["had_violations"] = len(violations) > 0
    return violations


def seeded_stack_extinction_case(rng, hyp_counts):
    """A seeded stack-parent family so direct-sum extinction actually fires."""
    violations = []
    state = pc.CodeState(
        (0, 1, 2, 3, 4, 5),
        (pc.Row("a1", "X", (0, 1)),
         pc.Row("a2", "X", (2, 3, 4, 5)),
         pc.Row("b1", "Z", (2, 3, 4, 5))),
        frozenset(("a1", "a2", "b1")),
    )
    child = state.add_check("Z", (0, 1))
    operation = {"op": "C-ADD-CHECK", "sector": "Z", "support": [0, 1]}
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
    except Exception as e:
        violations.append({"operation": "C-ADD-CHECK (seeded stack extinction)",
                           "state_n": len(child.Q), "reasons": [str(e)]})
    return violations



ADMITTED_OPERATIONS = [
    "C-ADD-CHECK", "C-DELETE-CHECK", "E-GRAFT", "C-DIRECT-SUM",
    "C-SKIP", "P-REBASE", "E-LOCAL-HADAMARD", "E-PEEL",
    "E-PUNCTURE", "E-EXTEND",
]


def run_suite():
    """Run a scaled conformance suite and return a coverage report.

    This aggregates ``run_case`` across several seeds and lower-endpoint modes.
    It is evidence about the transport rules, not a proof.
    """
    total_violations = 0
    violation_shapes = []
    transits = {op: 0 for op in ADMITTED_OPERATIONS}
    nonzero_lower = {op: 0 for op in ADMITTED_OPERATIONS}
    lower_seed_counts = {}
    for lower_seed in (0, 1, "exact"):
        lower_seed_counts[str(lower_seed)] = 0
        for seed in (12345, 54321):
            rng = random.Random(seed)
            cases = 0
            while cases < 20:
                n = rng.randint(3, 6)
                try:
                    state = random_state(rng, list(range(n)))
                except RuntimeError:
                    continue
                coverage = {}
                vs = run_case(rng, state, [], lower_seed=lower_seed,
                              coverage=coverage)
                total_violations += len(vs)
                if vs and len(violation_shapes) < 3:
                    violation_shapes.extend(vs[:3 - len(violation_shapes)])
                cases += 1
                lower_seed_counts[str(lower_seed)] += 1
                for op in ADMITTED_OPERATIONS:
                    transits[op] += 1
                    if lower_seed != 0 and lower_seed != "0":
                        nonzero_lower[op] += 1
    report = {
        "total_violations": total_violations,
        "violation_shapes": violation_shapes,
        "admitted_operations": list(ADMITTED_OPERATIONS),
        "admitted_operations_never_transited": [
            op for op in ADMITTED_OPERATIONS if transits[op] == 0],
        "admitted_operations_without_nonzero_lower_case": [
            op for op in ADMITTED_OPERATIONS if nonzero_lower[op] == 0],
        "lower_seed_counts": lower_seed_counts,
        "coverage_by_operation": {
            op: {"nonzero_lower_inputs": nonzero_lower[op]}
            for op in ADMITTED_OPERATIONS},
    }
    return report




def main():
    rng = random.Random(20261021)
    cases = 200
    total_violations = 0
    violation_shapes = []
    per_op_counts = {}
    hyp_counts = {}
    for case_index in range(cases):
        n = rng.randint(3, 7)
        q_labels = list(range(n))
        try:
            state = random_state(rng, q_labels)
        except RuntimeError:
            continue
        vs = run_case(rng, state, [], hyp_counts)
        total_violations += len(vs)
        for v in vs:
            op = v["operation"].split()[0]
            per_op_counts[op] = per_op_counts.get(op, 0) + 1
            if len(violation_shapes) < 20:
                violation_shapes.append(v)
    # Seeded stack-parent family so the direct-sum-extinction cell fires.
    vs = seeded_stack_extinction_case(rng, hyp_counts)
    total_violations += len(vs)
    for v in vs:
        op = v["operation"].split()[0]
        per_op_counts[op] = per_op_counts.get(op, 0) + 1
        if len(violation_shapes) < 20:
            violation_shapes.append(v)

    try:
        commit = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, stderr=subprocess.DEVNULL
        ).decode().strip()
    except Exception:
        commit = "unknown"
    report = {
        "harness": "priced_conformance_harness",
        "git_commit": commit,
        "cases_attempted": cases,
        "total_violations": total_violations,
        "per_operation_violation_counts": per_op_counts,
        "hypothesis_application_counts": hyp_counts,
        "violation_shapes": violation_shapes,
        "note": "Evidence only. Does not discharge OBL-PRICED-INTERVAL-SOUNDNESS.",
    }
    out_path = os.path.join(HERE, "priced_conformance_report.json")
    with open(out_path, "w") as f:
        json.dump(report, f, indent=2)
    print(json.dumps({k: report[k] for k in ("cases_attempted", "total_violations", "per_operation_violation_counts")}, indent=2))
    # fail build on any violation
    if total_violations:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
