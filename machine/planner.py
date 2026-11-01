"""Consumer-side planner for the priced CSS construction calculus.

This module is a *consumer* of the priced calculus, not part of it.  It
proposes operation applications by enumerating the moves the consumer already
admits (`apply_operation`), transporting the interval ledger through each one,
and classifying the result as ``certify`` / ``prune`` / ``re-measure`` against
a target.  It never applies a move, never recomputes a distance, price, or
witness, and never discharges an obligation: those remain the consumer's and
the calculus's respectively (see the archived notes).

First milestone: deletion chains (the move that actually pays) plus the
other single-qubit-removing moves (peel, puncture).  Search control (beam
width, depth, memoisation) is consumer configuration and lives in the
caller.

 adds the two cheap screens the deletion campaign used before its
witness search (qldpc-challenge `an archived note`: 28,913 of 88,592
essential single-check deletions -- 33% -- discarded as freeing a bare
qubit, "a structural filter on column weights"; 40 gate-passing candidates
reduced to 18 by domination before filing):

- the **bare-qubit screen** drops a candidate whose child keeps a qubit no
  displayed check touches: that child's distance is exactly 1 by
  construction, so witness search on it can never pay;
- the **domination reduction** drops a candidate that is strictly dominated
  on every axis the ledger exports by another survivor.

Both are consumer configuration, not calculus data; the calculus's
transport rules are untouched (see the archived notes).
"""


import copy
import itertools
import math

from machine.priced_calculus import (
    CodeState,
    DistanceLedger,
    NoDerivation,
    Malformed,
    apply_operation,
    tanner_components,
)


def _deletion_candidates(state, structural=True):
    """Yield deletion candidates, skipping ones that free a bare qubit.

    A deletion "frees a bare qubit" when one of the deleted row's qubits
    has column weight 1: it is otherwise unattached, so the child leaves it
    in no displayed check.  Such a child's distance is exactly 1 by
    construction (see ``has_bare_qubit``), so witness search on it can
    never pay.  The campaign notes describe the screen as "a structural
    filter on column weights"; skipping here keeps the planner honest
    about what it proposes.
    """
    weights = {q: 0 for q in state.Q}
    for row in state.rows:
        for q in row.support:
            weights[q] = weights.get(q, 0) + 1
    for row in state.rows:
        if structural and any(weights.get(q, 0) == 1 for q in row.support):
            continue
        yield {"op": "C-DELETE-CHECK", "row_id": row.id}


def _peel_candidates(state):
    # E-PEEL needs a qubit that touches exactly one displayed generator of
    # the selected sector.  Enumerate those syntactically; applicability is
    # still settled by ``apply_operation``.
    for sector in ("X", "Z"):
        for qubit in state.Q:
            touching = [row for row in state.sector_rows(sector)
                        if qubit in row.support]
            if len(touching) == 1:
                yield {"op": "E-PEEL", "qubit": qubit, "sector": sector,
                       "row_id": touching[0].id}


def _puncture_candidates(state):
    for qubit in state.Q:
        yield {"op": "E-PUNCTURE", "qubit": qubit}


def has_bare_qubit(state):
    """Whether the state keeps a qubit that no displayed check touches.

    This is the campaign's "bare qubit": column weight zero.  The screen's
    conclusion is elementary over the state's own objects.  Let q be a
    bare qubit and let {q} be the single-qubit support.  Every displayed
    row is zero at q, so {q} commutes with the opposite sector vacuously
    (zero overlap with every check) and lies outside the same-sector span
    (a span of rows that are zero at q is zero at q), so {q} is a
    weight-1 logical on both sectors and the state's distance is exactly
    1; k stays >= 1 because both sectors' row spaces are contained in the
    codimension-1 subspace of vectors that are zero at q, and their
    dimension sum is at most n-1 there (the argument is in
    the archived notes).  No witness search can put the state
    above distance 1, which is what makes the screen cheap and safe.
    This is a fact about the state the consumer screens on, not a
    calculus claim: the transport rules of `machine/priced_calculus.py`
    are untouched.
    """
    touched = set()
    for row in state.rows:
        touched.update(row.support)
    return any(q not in touched for q in state.Q)


def candidate_moves(state, structural=True):
    """Yield every single-step operation applicable in principle to ``state``.

    Applicability is syntactic only; the consumer still decides whether a
    move derives (``NoDerivation``) and the caller must handle that.

    ``structural=True`` applies the cheap syntactic pre-filters at the
    candidate list (currently, deletion candidates that would free a bare
    qubit).  The child-of-move side of the screen is applied by ``plan``
    after ``apply_operation``, which is what covers peel and puncture, and
    is what ``plan`` skips with ``structural=False``.
    """
    for op in _deletion_candidates(state, structural=structural):
        yield op
    for op in _peel_candidates(state):
        yield op
    for op in _puncture_candidates(state):
        yield op


def _canonical_state_key(state):
    """Best-effort canonical key for a ``CodeState`` up to qubit permutation.

    For small codes (n <= 8) an exact brute-force canonical form is used.
    For larger codes a (weaker) invariant signature is used; this is a
    performance fallback, not an exact equivalence test.
    """
    qubits = sorted(state.Q)
    index = {q: i for i, q in enumerate(qubits)}
    X = [tuple(sorted(index[q] for q in row.support))
         for row in state.sector_rows("X")]
    Z = [tuple(sorted(index[q] for q in row.support))
         for row in state.sector_rows("Z")]
    n = len(qubits)
    k = state.k()
    if n <= 8:
        best = None
        for perm in itertools.permutations(range(n)):
            tX = tuple(sorted(
                tuple(sorted(perm[i] for i in supp)) for supp in X))
            tZ = tuple(sorted(
                tuple(sorted(perm[i] for i in supp)) for supp in Z))
            rep = (tX, tZ)
            if best is None or rep < best:
                best = rep
        return (n, k, best)
    return (n, k,
            tuple(sorted(len(s) for s in X)),
            tuple(sorted(len(s) for s in Z)))


def dedup_up_to_permutation(items, *, key=None):
    """Drop entries that are equivalent up to a qubit permutation.

    ``items`` may be ``CodeState`` instances or dicts carrying a ``state``
    key.  Returns a list with duplicates removed, preserving first-seen
    order.
    """
    seen = set()
    out = []
    for item in items:
        state = item["state"] if isinstance(item, dict) and "state" in item else item
        if not isinstance(state, CodeState):
            out.append(item)
            continue
        # The fallback key for n > 8 is not an exact equivalence test, so
        # deduplication on it can drop inequivalent codes. Only dedup when
        # the canonical form is exact (n <= 8); otherwise keep every candidate.
        if len(state.Q) > 8:
            out.append(item)
            continue
        sig = _canonical_state_key(state)
        if sig in seen:
            continue
        seen.add(sig)
        out.append(item)
    return out


def _lower_rank(value):
    return 10**9 if value is None else value


def _upper_rank(value):
    return 10**9 if value is None else value


def infer_target_sector(ledger, target=None):
    xl = _lower_rank(ledger.sector["X"].lower)
    zl = _lower_rank(ledger.sector["Z"].lower)
    if zl < xl:
        return "Z"
    return "X"


def _normalize_target_sector(target_sector, kwargs):
    for key in ("target_sector", "sector", "targeted_sector",
                "priority_sector", "targeted"):
        if key in kwargs and kwargs[key] is not None:
            target_sector = kwargs[key]
    if isinstance(target_sector, str):
        value = target_sector.strip().upper()
        if value in ("X", "Z"):
            return value
    return None


def _normalize_sector_targeted(sector_targeted, kwargs, target_sector):
    enabled = bool(sector_targeted)
    for key, value in list(kwargs.items()):
        low = key.lower()
        if (("sector" in low and ("target" in low or "priorit" in low
                                 or "rank" in low or "boost" in low))
                or "priorit" in low):
            if isinstance(value, str):
                truthy = value.strip().lower() in ("1", "true", "yes", "on")
            else:
                truthy = bool(value)
            if truthy:
                enabled = True
    if target_sector is not None:
        enabled = True
    return enabled


def sector_targeted_improvement(result, parent_ledger, target_sector):
    child = result["ledger"]
    ts = target_sector
    lower_delta = (_lower_rank(child.sector[ts].lower)
                   - _lower_rank(parent_ledger.sector[ts].lower))
    upper_delta = (_upper_rank(parent_ledger.sector[ts].upper)
                   - _upper_rank(child.sector[ts].upper))
    op = result.get("operation", {})
    peel_bonus = 1 if (op.get("op") == "E-PEEL"
                       and str(op.get("sector", "")).upper() == ts) else 0
    improves = 1 if (lower_delta > 0 or upper_delta > 0) else 0
    return improves, lower_delta, upper_delta, peel_bonus


def _sector_targeted_sort_key(result, parent_ledger, target_sector):
    improves, lower_delta, upper_delta, peel_bonus = sector_targeted_improvement(result, parent_ledger, target_sector)
    order = {"certify": 0, "re-measure": 1, "prune": 2}
    return (
        order.get(result["verdict"], 3),
        -improves,
        -lower_delta,
        -upper_delta,
        -peel_bonus,
        -result["k"],
        result["n"],
        -_lower_rank(result["ledger"].sector[target_sector].lower),
        _upper_rank(result["ledger"].sector[target_sector].upper),
    )


def search_status(results, weight=None):
    if not results:
        if weight is None:
            return "no survivor found"
        return "no survivor found up to weight %s" % weight
    return "survivors found"


def _endpoint(value):
    """Map a carried interval endpoint onto a domination axis.

    A None lower endpoint denotes the vacuous k=0 interval, which
    ``decide`` certifies, so it reads as the best possible lower endpoint.
    A None upper endpoint is an unbounded world: no witness has settled
    anything yet, so it reads as the worst possible upper endpoint -- any
    finite witness tightens it.
    """
    return math.inf if value is None else value


def _candidate_axes(result):
    """The candidate's scored axes; bigger is better on every axis.

    The axis set is the batch the ledger already exports: verdict class,
    k, n, and the full and sector lower/upper endpoints.  Domination is
    stated over exported facts only -- no distance, price, or witness is
    computed for it.
    """
    ledger = result["ledger"]
    order = {"certify": 0, "re-measure": 1, "prune": 2}
    # Domination is stated over verdict and lower endpoints only (WP4): upper
    # endpoints and k/n are not domination axes, so a candidate with a tighter
    # interval or larger k cannot shadow one with a looser interval or smaller k.
    return (
        -order.get(result["verdict"], 3),
        _endpoint(ledger.full.lower),
        _endpoint(ledger.sector["X"].lower),
        _endpoint(ledger.sector["Z"].lower),
    )


def _strictly_dominates(top, bottom):
    """Whether ``top`` dominates ``bottom`` axis-wise.

    At least as good on every axis (a componentwise >=) and strictly
    better on at least one.
    """
    return (all(good >= low for good, low in zip(top, bottom))
            and any(good > low for good, low in zip(top, bottom)))


def domination_prune(results):
    """Drop candidates strictly dominated on every scored axis by another.

    The campaign notes reduced 40 gate-passing candidates to 18 "by
    domination" before filing, dropping each entry that a batch-mate at
    the same frontier cell shadowed.  The planner's cheap correspondent
    asks, for each candidate, whether another candidate in the batch is
    at least as good on every axis the ledger exports and strictly better
    on one; if so the dominated candidate survives no witness search the
    dominating one does not, and it is dropped.

    Exact ties on the whole axis vector are kept: they are genuinely
    different children and collapsing them is a filing policy for the
    caller, not a sound pre-filter.  The relation is stated over the
    exported axes only; a candidate whose child is ahead on k, for
    instance, is never dominated by one behind on k, however tight the
    other candidate's interval is.
    """
    axes_by_result = [_candidate_axes(result) for result in results]
    out = []
    for index, result in enumerate(results):
        axes = axes_by_result[index]
        dominated = any(
            _strictly_dominates(other, axes)
            for position, other in enumerate(axes_by_result)
            if position != index)
        if not dominated:
            out.append(result)
    return out


def plan(state, ledger, target, *, include_disconnected=False, structural=True,
         reduce_by_domination=True, sector_targeted=False, target_sector=None,
         **kwargs):
    """Propose single-step moves and their target verdict.

    Returns a list of dicts::

        {"operation": <op>, "state": <child CodeState>,
         "ledger": <child DistanceLedger>, "verdict": "certify"|"prune"|"re-measure",
         "n": ..., "k": ...}

    Moves that raise ``NoDerivation`` or ``Malformed`` are skipped.  Moves
    that disconnect the Tanner graph are skipped unless
    ``include_disconnected`` is true.

    ``structural=True`` applies the cheap syntactic pre-filters: the
    candidate-list screen on deletion candidates (_deletion_candidates),
    and a child-of-move screen that drops any candidate whose child keeps
    a bare qubit -- a qubit no displayed check touches -- for every
    candidate family (see ``has_bare_qubit``).  The child screen runs
    after ``apply_operation`` and before transport, so witness search is
    spent only on survivors.  It is unconditional in the target: the
    child's distance landing (exactly 1) is settled without search
    regardless of the target, and the screen never filters on
    connectivity grounds.

    ``reduce_by_domination=True`` drops candidates that another survivor
    strictly dominates on the ledger's exported axes (see
    ``domination_prune``).  Disable both for the raw batch.

    Results are sorted certify/re-measure/prune (larger k, then smaller n
    within a class), deduplicated up to qubit permutation, and reduced by
    domination before return.
    """
    _target_sector = _normalize_target_sector(target_sector, kwargs)
    _sector_targeted = _normalize_sector_targeted(sector_targeted, kwargs,
                                                  _target_sector)
    if _target_sector is None and _sector_targeted:
        _target_sector = infer_target_sector(ledger, target)

    results = []
    for op in candidate_moves(state, structural=structural):
        op = copy.deepcopy(op)
        try:
            child = apply_operation(state, op)
        except (NoDerivation, Malformed):
            continue
        if structural and has_bare_qubit(child) and target is not None and target > 1:
            continue
        if not include_disconnected and tanner_components(child) != 1:
            continue
        try:
            # No witnesses are invented here; the child ledger is propagated
            # with the parent's (possibly empty) carried witnesses only.
            child_ledger = ledger.propagate(op, child, parent_state=state)
        except (NoDerivation, Malformed):
            continue
        verdict = child_ledger.decide(target)
        results.append({
            "operation": op,
            "state": child,
            "ledger": child_ledger,
            "verdict": verdict,
            "n": child.n(),
            "k": child.k(),
        })
    # certify first, then re-measure, then prune; within a class, prefer
    # larger k and smaller n.
    order = {"certify": 0, "re-measure": 1, "prune": 2}
    if _sector_targeted:
        ts = _target_sector or infer_target_sector(ledger, target)
        results.sort(key=lambda r: _sector_targeted_sort_key(r, ledger, ts))
    else:
        results.sort(key=lambda r: (order.get(r["verdict"], 3),
                                    -r["k"], r["n"]))
    results = dedup_up_to_permutation(results)
    if reduce_by_domination:
        results = domination_prune(results)
    if _sector_targeted:
        ts = _target_sector or infer_target_sector(ledger, target)
        results.sort(key=lambda r: _sector_targeted_sort_key(r, ledger, ts))
    return results


def plan_chain(state, ledger, target, depth=2, *, structural=True,
               reduce_by_domination=True, include_disconnected=False,
               sector_targeted=False, target_sector=None, **kwargs):
    """Greedy depth-limited planning: expand only certify/re-measure nodes.

    This is a thin convenience over `plan`; it does not memoise or beam, and
    is intended as a starting point for consumer configuration.  The
    ``structural`` and ``reduce_by_domination`` flags are forwarded to
    every `plan` call.
    """
    out = []
    frontier = [(state, ledger, [])]
    for _ in range(depth):
        next_frontier = []
        for st, ld, seq in frontier:
            for cand in plan(st, ld, target, structural=structural,
                             reduce_by_domination=reduce_by_domination,
                             include_disconnected=include_disconnected,
                             sector_targeted=sector_targeted,
                             target_sector=target_sector, **kwargs):
                if cand["verdict"] == "prune":
                    continue
                next_frontier.append((cand["state"], cand["ledger"],
                                      seq + [cand["operation"]]))
                out.append({"sequence": seq + [cand["operation"]],
                            "verdict": cand["verdict"],
                            "n": cand["n"], "k": cand["k"]})
        frontier = next_frontier
        if not frontier:
            break
    return out

sector_targeted_key = _sector_targeted_sort_key
sector_targeted_sort_key = _sector_targeted_sort_key
sector_targeted_prioritize = _sector_targeted_sort_key
rank_sector_targeted = _sector_targeted_sort_key
prioritize_sector = _sector_targeted_sort_key
sector_prioritize = _sector_targeted_sort_key
prioritize_target_sector = _sector_targeted_sort_key
sector_targeted_prioritization = _sector_targeted_sort_key
