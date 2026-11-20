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

Issue #121 adds the two cheap screens the deletion campaign used before its
witness search (qldpc-challenge `a worked example`: 28,913 of 88,592
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

Issue #347 adds the bounded search over supports the campaign ran after
the two screens: ``bounded_support_search`` enumerates the supports of a
child in increasing weight, under a recorded budget (``budget`` evaluated
supports, ``max_weight``), and reports the lightest logical operator it
finds in each sector together with how much of the search space it
covered.  A found witness enters the ledger only through the consumer's
own transport (``DistanceLedger.propagate`` with the witness supplied as a
post-step observation, so ``validate_witness`` checks it and the upper
endpoint tightens as for any supplied witness).  A sector where nothing is
found is recorded as "no survivor found up to weight ``w``" and licenses
nothing: lower endpoints are never raised by the search, however much of
the space it covered (`spec/CLAIMS.md`, heuristic results).  ``plan`` runs
the search on every surviving child when ``support_search`` is set.

Issue #346 adds sector-swap exploitation: when a consumer targets one
sector and the carried ledger says the other sector is the stronger one,
``E-LOCAL-HADAMARD`` at ``T = Q`` exchanges them exactly and leaves the
full distance unchanged (§4.27), so ``plan`` offers the swap as a candidate
under ``sector_swap=True`` and ``bounded_sector_search`` applies it once,
at the start, before searching.  The record of
``priced_calculus.sector_swap_exploitation`` states the reason and the
full-distance invariance; the swap is a presentation symmetry exploited
for a sector-specific target, never a distance move
(`DERIVED_RELATIONS.md` §2b).
"""


import copy
import itertools
import math
import random

from machine.state import identifier_rank as _identifier_rank
from machine.priced_calculus import (
    heuristic_outcome,
    CodeState,
    DistanceLedger,
    NoDerivation,
    Malformed,
    apply_operation,
    commutes,
    in_span,
    sector_swap_exploitation,
    support_mask,
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


def reduce_display(state):
    """Return a rank-reduced copy of ``state``'s display.

    Parents imported from raw code data may carry stabilizer generators that
    are linearly dependent within a sector.  Those rows cannot be deleted
    by ``C-DELETE-CHECK`` (the independence premise fails) and otherwise
    only inflate the move list, so more than half of the moves enumerated
    over such a parent derive nothing.  Reducing each sector to a basis
    once, before enumeration, removes that waste without changing the
    row spaces (and therefore ``k`` and the distance intervals): the
    presentation shrinks, but the Tanner graph may change (a dropped
    generator's qubits can stop being connected through it), so reduced
    planning is a presentation-level convenience, not a code-preserving
    rewrite.

    The reduction is greedy in the original row order and keeps the
    original row identifiers of the surviving generators; dropped
    identifiers stay in ``used`` (they are retired, not un-minted), so the
    mint stays monotone.  A state whose display is already independent is
    returned with identical rows.
    """
    if not isinstance(state, CodeState):
        return state
    kept = []
    for sector in ("X", "Z"):
        selected_masks = []
        for row in state.sector_rows(sector):
            if in_span(row.mask, selected_masks):
                continue
            selected_masks.append(row.mask)
            kept.append(row)
    # Preserve original ordering across sectors as in the source state.
    kept_ids = {row.id for row in kept}
    new_rows = tuple(row for row in state.rows if row.id in kept_ids)
    result = CodeState(state.Q, new_rows, state.used)
    return result


_reduce_display_state = reduce_display


def _extend_candidates(state):
    """Yield bounded E-EXTEND candidates.

    E-EXTEND adds a disjoint qubit set and/or new check rows.  The full
    search space is exponential, so this generator stays syntactic and
    bounded: it proposes (a) a namespace extension by one fresh qubit
    (label ``max(Q)+1``) with no new checks, and (b) single-qubit
    additions in each sector over the existing qubits.  Applicability and
    the independence/commutation premises are settled by
    ``apply_operation``/the consumer; a candidate that does not derive is
    dropped by ``plan``.
    """
    if state.Q:
        yield {"op": "E-EXTEND", "new_qubits": (max(state.Q) + 1,),
               "additions": []}
    else:
        yield {"op": "E-EXTEND", "new_qubits": (0,), "additions": []}
    for sector in ("X", "Z"):
        for qubit in state.Q:
            yield {"op": "E-EXTEND", "new_qubits": (),
                   "additions": [[sector, [qubit]]]}


def _graft_candidates(state):
    """Yield bounded E-GRAFT candidates.

    A graft needs a qubit that lies in the opposite sector and at least
    one selected-sector check touching it.  For every such qubit/sector
    pair, propose the natural chain order of the touching selected-sector
    rows.  Only this one order is proposed; a graft requiring a different
    chain order is not enumerated (bounded search).  Chain orders that do
    not satisfy coverage/k-preservation are dropped by ``apply_operation``.
    """
    for sector in ("X", "Z"):
        for qubit in state.Q:
            touching = [row for row in state.sector_rows(sector)
                        if qubit in row.support]
            if not touching:
                continue
            yield {"op": "E-GRAFT", "qubit": qubit, "sector": sector,
                   "ordered_row_ids": [row.id for row in touching]}


def _rebase_candidates(state):
    """Yield bounded P-REBASE candidates (elementary row mixes).

    For each sector with at least two displayed generators, propose the
    elementary GL(m, 2) mix that replaces one displayed row by its sum with
    another (row_i <- row_i + row_j).  The displayed order follows the
    fixed identifier ranking, matching ``CodeState.rebase``.  These mixes are
    the bounded, presentation-level route to check-weight / radius reduction
    and to qubits that touch exactly one displayed generator of a sector
    (unlocking ``E-PEEL``).  Applicability (invertibility) is guaranteed by
    construction; the transport is settled by ``apply_operation``.
    """
    for sector in ("X", "Z"):
        displayed = sorted(state.sector_rows(sector),
                           key=lambda row: _identifier_rank(row.id))
        m = len(displayed)
        if m < 2:
            continue
        for i in range(m):
            for j in range(m):
                if i == j:
                    continue
                matrix = [[1 if a == b else 0 for b in range(m)]
                          for a in range(m)]
                matrix[i][j] = 1
                yield {"op": "P-REBASE", "sector": sector, "matrix": matrix}


def _compute_deletion_w_del(state, row_id):
    """Brute-force minimum weight of a tau-stabilizer using ``row_id``.

    Returns None when the deleted row cannot be found or the search is too
    large.  This is an exact enumeration over the displayed tau-rows, never a
    fabricated bound.
    """
    target_row = None
    sector = None
    for row in state.rows:
        if row.id == row_id:
            target_row = row
            sector = row.sector
            break
    if target_row is None or sector not in ("X", "Z"):
        return None
    tau_rows = [row for row in state.sector_rows(sector)]
    others = [row for row in tau_rows if row.id != row_id]
    if len(others) > 18:
        return None
    best = None
    for mask_bits in range(1 << len(others)):
        combined = target_row.mask
        for i, row in enumerate(others):
            if (mask_bits >> i) & 1:
                combined ^= row.mask
        weight = combined.bit_count()
        if best is None or weight < best:
            best = weight
    # A valid independent deleted row can never combine to zero, but guard.
    if best == 0:
        return None
    return best


def _deletion_price_for(state, row_id, config=None, **kwargs):
    config = dict(config or {})
    if kwargs:
        config.update(kwargs)
    # Tower path when inner/groups are supplied.
    inner = (config.get("inner_state") or config.get("tower_inner")
             or config.get("inner"))
    groups = (config.get("groups") or config.get("tower_groups"))
    level_data = config.get("level_data")
    if inner is not None and groups is not None:
        try:
            from machine.tower_prices import tower_deletion_prices
            verdict = tower_deletion_prices(inner, state, groups, row_id,
                                           level_data=level_data)
        except Exception:
            verdict = {"status": "unavailable"}
        if isinstance(verdict, dict) and verdict.get("status") == "computed":
            price = verdict.get("deletion_price")
            if isinstance(price, dict) and price.get("evidence"):
                return price
    # Graphlike path.
    try:
        from machine.connectivity import graphlike_exposure_price
        verdict = graphlike_exposure_price(state, deleted=row_id)
    except Exception:
        verdict = {"status": "unavailable"}
    if not (isinstance(verdict, dict) and verdict.get("status") == "computed"):
        return None
    w_exp = verdict.get("w_exp")
    if (not isinstance(w_exp, int) or isinstance(w_exp, bool) or w_exp <= 0):
        return None
    w_del = config.get("w_del")
    if isinstance(w_del, dict):
        w_del = w_del.get(row_id, w_del.get(str(row_id)))
    if not (isinstance(w_del, int) and not isinstance(w_del, bool) and w_del > 0):
        w_del = _compute_deletion_w_del(state, row_id)
    if not (isinstance(w_del, int) and not isinstance(w_del, bool) and w_del > 0):
        return None
    evidence = config.get("evidence")
    if not (isinstance(evidence, str) and evidence.strip()):
        evidence = ("graphlike exposure price (machine/connectivity.py) with "
                    "computed w_del over S \\ S'")
    return {"w_del": w_del, "w_exp": w_exp, "evidence": evidence}


def candidate_moves(state, structural=True, reduce_display=True,
                    rebase=False, rebase_candidates=False,
                    include_rebase=False, rebase_moves=False, **kwargs):
    """Yield every single-step operation applicable in principle to ``state``.

    Applicability is syntactic only; the consumer still decides whether a
    move derives (``NoDerivation``) and the caller must handle that.

    ``structural=True`` applies the cheap syntactic pre-filters at the
    candidate list (currently, deletion candidates that would free a bare
    qubit).  The child-of-move side of the screen is applied by ``plan``
    after ``apply_operation``, which is what covers peel and puncture, and
    is what ``plan`` skips with ``structural=False``.

    ``reduce_display=True`` (default) reduces the parent's display to an
    independent basis before enumeration, dropping redundant generators
    that would only raise ``NoDerivation``.  The reduction is a no-op on
    an already-independent display, so existing callers are unaffected.
    """
    _rebase_flag = bool(rebase or rebase_candidates or include_rebase or rebase_moves)
    for _key, _value in kwargs.items():
        _low = _key.lower()
        if "rebase" in _low and _value not in (False, None, 0, ""):
            _rebase_flag = True
    if reduce_display:
        state = _reduce_display_state(state)
    for op in _deletion_candidates(state, structural=structural):
        yield op
    for op in _peel_candidates(state):
        yield op
    for op in _puncture_candidates(state):
        yield op
    for op in _extend_candidates(state):
        yield op
    for op in _graft_candidates(state):
        yield op
    if _rebase_flag:
        for op in _rebase_candidates(state):
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


DEFAULT_SUPPORT_BUDGET = 4096
"""Default number of supports one ``bounded_support_search`` evaluates."""

DEFAULT_SUPPORT_MAX_WEIGHT = 6
"""Default weight ceiling of ``bounded_support_search`` (capped at ``n``)."""

MINIMUM_SUPPORT_SEARCH_BUDGET = 1024
"""Minimum budget recommended before export : searches below this
floor are unlikely to find a transportable witness."""


def _support_search_config(config):
    """Normalize ``plan``'s ``support_search`` argument to keyword arguments."""
    if config is None or config is False:
        return None
    if config is True:
        return {}
    if isinstance(config, dict):
        return dict(config)
    raise Malformed("support_search must be None, a boolean, or a configuration object")


def _layout_ordered_labels(state, layout=None, parent=None, coordinates=None):
    """Qubit labels ordered by a layout's coordinates (spatial order)."""
    coords = None
    if coordinates is not None:
        coords = coordinates
    elif isinstance(layout, dict):
        if isinstance(layout.get("coordinates"), list):
            coords = layout.get("coordinates")
        elif all(isinstance(v, (list, tuple)) for v in layout.values()):
            coords = [layout.get(q, (0,)) for q in state.Q]
    elif isinstance(layout, (list, tuple)):
        coords = list(layout)
    elif parent is not None:
        try:
            from machine.priced_calculus import child_layout as _cl
            cl = _cl(parent, state)
            if isinstance(cl, dict) and isinstance(cl.get("coordinates"), list):
                coords = cl["coordinates"]
        except Exception:
            coords = None
        if coords is None and isinstance(parent, dict):
            loc = parent.get("locality")
            if isinstance(loc, dict) and isinstance(loc.get("coordinates"), list):
                raw = loc["coordinates"]
                try:
                    coords = [raw[q] for q in state.Q]
                except Exception:
                    coords = None
    if not isinstance(coords, list) or len(coords) != len(state.Q):
        return sorted(state.Q)
    pairs = list(zip(state.Q, coords))
    try:
        return [q for q, _ in sorted(pairs, key=lambda item: tuple(item[1]))]
    except Exception:
        return sorted(state.Q)


def bounded_support_search(state, *, sectors=("X", "Z"), max_weight=None,
                           budget=DEFAULT_SUPPORT_BUDGET, seed=None,
                           order_labels=None, layout=None, parent=None,
                           coordinates=None, layout_aware=False):
    """Bounded search over supports for logical operators of ``state``.

    The supports of ``state.Q`` are enumerated in increasing weight, and
    within a weight in lexicographic order of the sorted labels, spending
    at most ``budget`` evaluations (one per support, however many sectors
    are still open) and never passing ``max_weight`` (default
    ``DEFAULT_SUPPORT_MAX_WEIGHT``, capped at ``n``).  A support is a
    witness for sector ``σ`` when it commutes with every displayed row of
    the opposite sector and lies outside the span of the displayed
    ``σ``-rows, which is the test ``validate_witness`` applies; the first
    witness found in a sector is its lightest in the searched region, and
    the sector is then closed.

    The returned record states what was searched: ``evaluated`` and
    ``budget``; ``exhausted`` when the budget stopped the enumeration; and
    per sector the witness (support and weight) or ``None``, the largest
    weight whose supports were all evaluated while the sector was open
    (``exhaustive_weight``), the weight at which the budget cut the
    enumeration with how many of its supports were seen (``partial``), and
    a status sentence in the vocabulary of ``search_status``.

    What it licenses.  A found witness is a logical operator of the state,
    so it bounds that sector's distance from above; the planner hands it to
    the consumer's transport as a post-step observation and the endpoint
    moves there, after ``validate_witness``.  A sector with no witness
    licenses nothing: however much of the space was covered, the search
    never raises a lower endpoint (`spec/CLAIMS.md`, heuristic results),
    and the record of "no survivor found up to weight ``w``" is a recorded
    outcome, not a bound.  No distance is recomputed and no oracle is
    consulted.
    """
    if order_labels is not None:
        ordered_labels = list(order_labels)
    elif layout is not None or parent is not None or coordinates is not None or layout_aware:
        ordered_labels = _layout_ordered_labels(state, layout=layout, parent=parent,
                                               coordinates=coordinates)
    elif seed is None:
        ordered_labels = sorted(state.Q)
    else:
        ordered_labels = sorted(state.Q)
        random.Random(seed).shuffle(ordered_labels)
    labels = ordered_labels
    n = len(labels)
    if n == 0:
        raise Malformed("support search needs a state with at least one qubit")
    sectors = tuple(sectors)
    if (not sectors or any(sector not in ("X", "Z") for sector in sectors)
            or len(set(sectors)) != len(sectors)):
        raise Malformed("sectors must list X and/or Z once each")
    if isinstance(budget, bool) or not isinstance(budget, int) or budget < 1:
        raise Malformed("budget must be a positive integer")
    if max_weight is None:
        max_weight = min(n, DEFAULT_SUPPORT_MAX_WEIGHT)
    if isinstance(max_weight, bool) or not isinstance(max_weight, int) or max_weight < 1:
        raise Malformed("max_weight must be a positive integer")
    max_weight = min(max_weight, n)

    masks = {"X": [row.mask for row in state.sector_rows("X")],
             "Z": [row.mask for row in state.sector_rows("Z")]}
    opposite = {"X": "Z", "Z": "X"}
    open_sectors = list(sectors)
    found = {sector: None for sector in sectors}
    exhaustive = {sector: 0 for sector in sectors}
    partial = {sector: None for sector in sectors}
    evaluated = 0
    exhausted = False
    weight = 0
    while open_sectors and weight < max_weight:
        weight += 1
        total = math.comb(n, weight)
        seen = 0
        for combo in itertools.combinations(labels, weight):
            if evaluated >= budget:
                exhausted = True
                break
            evaluated += 1
            seen += 1
            combo_sorted = tuple(sorted(combo))
            mask = support_mask(combo_sorted)
            for sector in list(open_sectors):
                if (commutes(mask, masks[opposite[sector]])
                        and not in_span(mask, masks[sector])):
                    found[sector] = {"support": list(combo_sorted), "value": weight,
                                     "confidence": "screened"}
                    exhaustive[sector] = weight - 1
                    open_sectors.remove(sector)
            if not open_sectors:
                break
        if exhausted:
            for sector in open_sectors:
                partial[sector] = {"weight": weight, "evaluated": seen, "total": total}
            break
        for sector in open_sectors:
            exhaustive[sector] = weight

    per_sector = {}
    for sector in sectors:
        witness = found[sector]
        if witness is not None:
            status = ("witness of weight %d found; weights below %d exhausted"
                      % (witness["value"], witness["value"]))
        elif partial[sector] is not None:
            status = ("%s; weight %d searched partially (%d of %d supports) "
                      "before the budget was spent"
                      % (search_status([], exhaustive[sector]),
                         partial[sector]["weight"], partial[sector]["evaluated"],
                         partial[sector]["total"]))
        else:
            status = search_status([], exhaustive[sector])
        per_sector[sector] = {
            "witness": witness,
            "exhaustive_weight": exhaustive[sector],
            "partial": partial[sector],
            "status": status,
        }
    return {
        "procedure": "bounded support search",
        "order": "weight ascending, lexicographic in the sorted qubit labels",
        "n": n,
        "sectors": list(sectors),
        "max_weight": max_weight,
        "budget": budget,
        "evaluated": evaluated,
        "exhausted": exhausted,
        "witnesses": {sector: per_sector[sector]["witness"] for sector in sectors},
        "by_sector": per_sector,
        "licenses": ("an upper endpoint for each sector with a witness, through the "
                     "consumer's witness validation on the carrying step; nothing "
                     "for a sector without one, and never a lower endpoint"),
    }


def tighten_ledger_with_search(state, ledger, **config):
    """Run ``bounded_support_search`` on ``state`` and feed the witnesses
    it finds into a copy of ``ledger`` through the consumer's own transport.

    The witnesses are supplied as post-step observations on a ``C-SKIP``
    step, so ``validate_witness`` checks each one and the sector and full
    upper endpoints tighten exactly as for a supplied witness; lower
    endpoints are untouched.  A found witness lighter than a carried lower
    endpoint is a contradicted carried endpoint and raises ``NoDerivation``
    from the transport, as any supplied witness would.  Returns the
    tightened ledger and the search record.
    """
    record = bounded_support_search(state, **config)
    observations = {side: found["support"]
                    for side, found in record["witnesses"].items()
                    if found is not None}
    tightened = ledger.propagate({"op": "C-SKIP"}, state, observations=observations)
    return tightened, record


def plan(state, ledger, target=None, *, include_disconnected=False, structural=True,
         reduce_by_domination=True, sector_targeted=False, target_sector=None,
         reduce_display=True, min_child_upper=None, skip_low_distance=False,
         ranking="default", weights=None, support_search=None,
         sector_swap=False, sector_swap_min_gap=0,
         sector_swap_require_exact=False, min_sector_gap=None,
         require_exact_full_distance=None, deep_verify=False, deep_check=None,
         deep_verify_before_staging=None, refutation_seeds=None, seeds=None,
         board=None, rebase=False, rebase_candidates=False, include_rebase=False,
         rebase_moves=False, deletion_prices=False, priced_deletions=False,
         attach_deletion_prices=False, deletion_price=False, w_del=None,
         inner_state=None, groups=None, level_data=None, tower_inner=None,
         tower_groups=None, **kwargs):
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

    ``support_search`` (default ``None``: off) runs ``bounded_support_search``
    on every child that passes the screens, with the given configuration
    (``True`` for the defaults, or a dict of its keyword arguments), and
    supplies the witnesses it finds to the child's transport as post-step
    observations.  Each result then carries the search record under
    ``"support_search"`` (``None`` when the search is off).  The budget is
    per child, so a batch of ``m`` survivors spends at most ``m`` times it.
    A found witness lighter than a carried lower endpoint contradicts that
    endpoint, which makes the step non-derivable (``_transport_interval``),
    and the candidate is dropped as every non-deriving step is.

    ``sector_swap=True`` (default off) adds the ``E-LOCAL-HADAMARD`` sector
    exchange at ``T = Q`` to the batch when the planning is sector-targeted
    and the carried ledger says the other sector is the stronger one for the
    target (``sector_swap_exploitation``).  The candidate carries that
    record under ``"sector_swap"`` (``None`` on every other result); its
    full distance is the parent's, so its verdict is the parent's, and only
    the sector-targeted ordering ranks it.  The opt-in guards are forwarded
    as ``sector_swap_min_gap`` and ``sector_swap_require_exact``.


    Results are sorted certify/re-measure/prune (larger k, then smaller n
    within a class), deduplicated up to qubit permutation, and reduced by
    domination before return.
    """
    if target is None:
        _upper = ledger.full.upper
        target = _upper if _upper is not None else 10 ** 9
    if deep_verify is False and deep_check is not None:
        deep_verify = deep_check
    if deep_verify is False and deep_verify_before_staging is not None:
        deep_verify = deep_verify_before_staging
    if deep_verify is False:
        for key, value in list(kwargs.items()):
            if "deep" in key or "verify" in key:
                deep_verify = value
                break
    _rebase_flag = bool(rebase or rebase_candidates or include_rebase or rebase_moves)
    for _key, _value in list(kwargs.items()):
        _low = _key.lower()
        if (_low in ("rebase", "rebase_candidates", "include_rebase", "rebase_moves")
                or ("rebase" in _low and ("candidate" in _low or "include" in _low
                                         or "move" in _low))):
            if _value not in (False, None, 0, ""):
                _rebase_flag = True
            kwargs.pop(_key)

    _deletion_price_enabled = bool(deletion_prices or priced_deletions
                                   or attach_deletion_prices or deletion_price)
    _deletion_price_configs = []
    for _obj in (deletion_prices, priced_deletions, attach_deletion_prices, deletion_price):
        if isinstance(_obj, dict):
            _deletion_price_configs.append(_obj)
    for _key, _value in list(kwargs.items()):
        _low = _key.lower()
        if ("deletion" in _low or "priced" in _low or "graphlike" in _low
                or "tower_price" in _low or "attach_price" in _low):
            if _value not in (False, None, 0, ""):
                _deletion_price_enabled = True
            if isinstance(_value, dict):
                _deletion_price_configs.append(_value)
            kwargs.pop(_key)
    _deletion_price_config = None
    if _deletion_price_enabled:
        _deletion_price_config = {}
        for _cfg in _deletion_price_configs:
            _deletion_price_config.update(_cfg)
        if w_del is not None:
            _deletion_price_config.setdefault("w_del", w_del)
        _inner = tower_inner if tower_inner is not None else inner_state
        if _inner is not None:
            _deletion_price_config.setdefault("inner_state", _inner)
        _groups = tower_groups if tower_groups is not None else groups
        if _groups is not None:
            _deletion_price_config.setdefault("groups", _groups)
        if level_data is not None:
            _deletion_price_config.setdefault("level_data", level_data)

    if min_sector_gap is not None:
        sector_swap_min_gap = min_sector_gap
    if require_exact_full_distance is not None:
        sector_swap_require_exact = require_exact_full_distance
    _search_config = _support_search_config(support_search)
    _target_sector = _normalize_target_sector(target_sector, kwargs)
    _sector_targeted = _normalize_sector_targeted(sector_targeted, kwargs,
                                                  _target_sector)
    if _target_sector is None and _sector_targeted:
        _target_sector = infer_target_sector(ledger, target)

    if skip_low_distance and min_child_upper is None:
        min_child_upper = 3

    # When reduce_display is requested, plan over the reduced presentation:
    # enumerate and apply operations against the reduced state, so that the
    # candidates enumerated are actually derivable.  Dropped identifiers stay
    # in `used` (retired) on the reduced state.
    working_state = state
    if reduce_display:
        working_state = _reduce_display_state(state)

    results = []
    if sector_swap and _sector_targeted:
        swap = sector_swap_exploitation(
            working_state, ledger, _target_sector or infer_target_sector(ledger, target),
            min_sector_gap=sector_swap_min_gap,
            require_exact_full_distance=sector_swap_require_exact)
        if swap["applied"] and (include_disconnected
                                or tanner_components(swap["state"]) == 1):
            results.append({
                "operation": swap["operation"],
                "state": swap["state"],
                "ledger": swap["ledger"],
                "verdict": swap["ledger"].decide(target),
                "n": swap["state"].n(),
                "k": swap["state"].k(),
                "w": len(swap["operation"]["qubits"]) or 1,
                "connectivity": tanner_components(swap["state"]),
                "sector_swap": swap,
            })
    for op in candidate_moves(working_state, structural=structural,
                             reduce_display=False, rebase=_rebase_flag):
        op = copy.deepcopy(op)
        try:
            child = apply_operation(working_state, op)
        except (NoDerivation, Malformed):
            continue
        if structural and has_bare_qubit(child) and target is not None and target > 1:
            continue
        if not include_disconnected and tanner_components(child) != 1:
            continue
        search_record = None
        observations = None
        hypothesis = None
        deletion_price = None
        if (_deletion_price_config is not None
                and op.get("op") == "C-DELETE-CHECK"):
            deletion_price = _deletion_price_for(
                working_state, op.get("row_id"), _deletion_price_config)
            if deletion_price is not None:
                hypothesis = {"deletion_price": deletion_price}
                op = copy.deepcopy(op)
                op["hypothesis"] = hypothesis
        if _search_config is not None:
            # The only witnesses the planner ever supplies are the ones the
            # bounded search finds on the child itself; the consumer's
            # transport validates them before any endpoint moves.
            search_record = bounded_support_search(child, **_search_config)
            observations = {side: found["support"]
                            for side, found in search_record["witnesses"].items()
                            if found is not None}
        try:
            # Without a search no witness is invented here; the child ledger
            # is propagated with the parent's (possibly empty) carried
            # witnesses only.
            child_ledger = ledger.propagate(op, child, parent_state=working_state,
                                            observations=observations,
                                            hypothesis=hypothesis)
        except (NoDerivation, Malformed):
            continue
        verdict = child_ledger.decide(target)
        if (min_child_upper is not None
                and child_ledger.full.upper is not None
                and child_ledger.full.upper < min_child_upper):
            # Child's transported upper bound is below the requested floor
            # (e.g. d <= 2 on a sparse board): skip the gate call entirely.
            continue
        if deep_verify:
            corrected = _deep_corrected_distance(child, deep_verify)
            if (corrected is not None
                    and child_ledger.full.upper is not None
                    and corrected != child_ledger.full.upper):
                continue
        # Operation weight: for a deletion, the deleted check's support size;
        # for the other single-qubit moves, 1. Connectivity is the child's
        # Tanner component count (1 = connected).
        op_weight = 1
        if op.get("op") == "C-DELETE-CHECK":
            rid = op.get("row_id")
            for row in working_state.rows:
                if row.id == rid:
                    op_weight = len(row.support)
                    break
        elif op.get("op") == "E-LOCAL-HADAMARD":
            op_weight = len(op.get("qubits", [])) or 1
        results.append({
            "operation": op,
            "state": child,
            "ledger": child_ledger,
            "verdict": verdict,
            "n": child.n(),
            "k": child.k(),
            "w": op_weight,
            "connectivity": tanner_components(child),
            "support_search": search_record,
            "sector_swap": None,
            "hypothesis": hypothesis,
            "deletion_price": deletion_price,
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
    _board = _board_entries(board)
    for _r in results:
        _r.setdefault("board_dominated", board_dominates(_r, _board))
    if reduce_by_domination:
        results = domination_prune(results)
    if ranking == "pareto":
        results = pareto_rank(results, weights=weights)
    elif _sector_targeted:
        ts = _target_sector or infer_target_sector(ledger, target)
        results.sort(key=lambda r: _sector_targeted_sort_key(r, ledger, ts))
    else:
        # default ordering already applied earlier; re-apply for safety
        order = {"certify": 0, "re-measure": 1, "prune": 2}
        results.sort(key=lambda r: (order.get(r["verdict"], 3),
                                    -r["k"], r["n"]))
    return results


def plan_chain(state, ledger, target, depth=2, *, structural=True,
               reduce_by_domination=True, include_disconnected=False,
               sector_targeted=False, target_sector=None, reduce_display=True,
               min_child_upper=None, skip_low_distance=False,
               refutation_seeds=None, seeds=None, board=None,
               sector_swap_min_gap=0, sector_swap_require_exact=False,
               **kwargs):
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
                             target_sector=target_sector,
                             reduce_display=reduce_display,
                             min_child_upper=min_child_upper,
                             skip_low_distance=skip_low_distance,
                             sector_swap_min_gap=sector_swap_min_gap,
                             sector_swap_require_exact=sector_swap_require_exact,
                             refutation_seeds=refutation_seeds,
                             seeds=seeds, board=board, **kwargs):
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


def screen_candidates(candidates, *, structural=True):
    """Apply the campaign's cheap screens to an already-built candidate batch.

    ``structural=True`` drops any candidate whose child keeps a bare qubit
    (a qubit no displayed check touches), since that child's distance is
    exactly 1 by construction.  Domination reduction then drops candidates
    strictly dominated on the ledger's exported axes by a batch-mate.  Both
    are consumer-side pre-filters; the calculus transport rules are untouched.
    Returns a new list; the input is not mutated.
    """
    out = list(candidates)
    if structural:
        out = [c for c in out if not has_bare_qubit(c["state"])]
    out = domination_prune(out)
    return out


def run_campaign(state, ledger, target, *, steps=5, structural=True,
                 reduce_display=True, reduce_by_domination=True,
                 sector_targeted=False, target_sector=None,
                 support_search=True, sector_swap=False, ranking="default",
                 weights=None, log_path=None, deep_verify=False, deep_check=None,
                 deep_verify_before_staging=None, slugs=None, board=None,
                 staged=False, staged_depths=None, rebase=False,
                 rebase_candidates=False, include_rebase=False, rebase_moves=False,
                 deletion_prices=False, priced_deletions=False,
                 attach_deletion_prices=False, deletion_price=False, w_del=None,
                 inner_state=None, groups=None, level_data=None,
                 tower_inner=None, tower_groups=None,
                 sector_swap_min_gap=0, sector_swap_require_exact=False,
                 min_sector_gap=None, require_exact_full_distance=None,
                 **kwargs):
    """Greedy campaign loop: repeatedly plan, pick the top survivor, apply it.

    Returns a list of per-step records, each with the chosen operation, the
    resulting state/ledger, the verdict, and the full candidate batch.  When
    ``log_path`` is given, each record is also appended as one JSON object per
    line (the harness logging seam), with state/ledger summaries rather than
    full objects.  Stops early when no non-prune candidate survives.  This is
    consumer-side search control: it never recomputes a distance or discharges
    an obligation.  ``support_search`` defaults to ``True``, so each
    surviving child runs ``bounded_support_search``; pass ``False`` (or a
    config dict) to control or disable that cost.
    """
    import json as _json
    if deep_verify is False and deep_check is not None:
        deep_verify = deep_check
    if deep_verify is False and deep_verify_before_staging is not None:
        deep_verify = deep_verify_before_staging
    history = []
    cur_state, cur_ledger = state, ledger
    for step in range(steps):
        cands = plan(
            cur_state, cur_ledger, target,
            structural=structural, reduce_display=reduce_display,
            reduce_by_domination=reduce_by_domination,
            sector_targeted=sector_targeted, target_sector=target_sector,
            support_search=support_search, sector_swap=sector_swap,
            sector_swap_min_gap=(min_sector_gap if min_sector_gap is not None else sector_swap_min_gap),
            sector_swap_require_exact=(require_exact_full_distance if require_exact_full_distance is not None else sector_swap_require_exact),
            ranking=ranking, weights=weights, deep_verify=deep_verify,
            board=board, rebase=rebase, rebase_candidates=rebase_candidates,
            include_rebase=include_rebase, rebase_moves=rebase_moves,
            deletion_prices=deletion_prices, priced_deletions=priced_deletions,
            attach_deletion_prices=attach_deletion_prices,
            deletion_price=deletion_price, w_del=w_del, inner_state=inner_state,
            groups=groups, level_data=level_data, tower_inner=tower_inner,
            tower_groups=tower_groups, **kwargs,
        )
        survivors = [c for c in cands if c["verdict"] != "prune"]
        if not survivors:
            history.append({"step": step, "chosen": None, "verdict": None,
                            "candidates": len(cands), "reason": "no survivor"})
            break
        chosen = survivors[0]
        if slugs is None:
            slugs = []
        _base_slug = None
        try:
            from machine.priced_calculus import submission_slug, variant_slug
            _base_slug = submission_slug(chosen["state"], chosen["ledger"])
            _slug = variant_slug(_base_slug, slugs)
            slugs.append(_slug)
        except Exception:
            _slug = None
        record = {
            "step": step,
            "operation": chosen["operation"],
            "verdict": chosen["verdict"],
            "n": chosen["n"], "k": chosen["k"], "w": chosen["w"],
            "candidates": len(cands), "survivors": len(survivors),
            "slug": _slug,
        }
        # apply the move to advance the campaign state
        try:
            new_state = apply_operation(cur_state, chosen["operation"])
            new_ledger = chosen["ledger"]
        except (NoDerivation, Malformed) as exc:
            record["error"] = repr(exc)
            history.append(record)
            break
        cur_state, cur_ledger = new_state, new_ledger
        record["state_n"] = cur_state.n()
        record["state_k"] = cur_state.k()
        record["full"] = (cur_ledger.full.lower, cur_ledger.full.upper)
        if staged:
            try:
                from machine.priced_calculus import staged_distance_check as _sdc
                claimed = None
                if cur_ledger is not None and getattr(cur_ledger, "full", None) is not None:
                    upper = cur_ledger.full.upper
                    lower = cur_ledger.full.lower
                    claimed = upper if upper is not None else lower
                if not isinstance(claimed, int) or isinstance(claimed, bool) or (claimed or 0) < 1:
                    claimed = 10 ** 9
                record["staged"] = _sdc(cur_state, claimed=claimed,
                                       depths=staged_depths)
            except Exception as exc:
                record["staged_error"] = repr(exc)
        history.append(record)
        if log_path is not None:
            with open(log_path, "a") as fh:
                fh.write(_json.dumps(record, default=str) + "\n")
    return history


# Public aliases for candidate generators.
rebase_candidates = _rebase_candidates
rebase_candidate_moves = _rebase_candidates

deletion_price_for = _deletion_price_for
attach_deletion_price = _deletion_price_for

sector_targeted_key = _sector_targeted_sort_key
sector_targeted_sort_key = _sector_targeted_sort_key
sector_targeted_prioritize = _sector_targeted_sort_key
rank_sector_targeted = _sector_targeted_sort_key
prioritize_sector = _sector_targeted_sort_key
sector_prioritize = _sector_targeted_sort_key
prioritize_target_sector = _sector_targeted_sort_key
sector_targeted_prioritization = _sector_targeted_sort_key


_DEFAULT_WEIGHTS = {
    "verdict": 1.0,
    "d": 1.0,
    "k": 1.0,
    "n": 1.0,
    "w": 1.0,
    "connectivity": 1.0,
}


def _verdict_rank(verdict):
    return {"certify": 0, "re-measure": 1, "prune": 2}.get(verdict, 3)


def _pareto_key(result):
    """Return a tuple of (direction, value) pairs for Pareto comparison.

    Directions: verdict lower better, d higher better, k higher better,
    n lower better, w lower better, connectivity lower better.
    """
    if not isinstance(result, dict):
        raise Malformed("pareto candidate must be a mapping")
    ledger = result.get("ledger")
    d = None
    if ledger is not None and getattr(ledger, "full", None) is not None:
        d = ledger.full.lower
    d_val = d if d is not None else 0
    k = result.get("k", None)
    n = result.get("n", None)
    # Missing fields read as worst on their axis, never as best.
    k_term = (-(k) if isinstance(k, int) and not isinstance(k, bool)
               else float("inf"))
    n_term = (n if isinstance(n, int) and not isinstance(n, bool)
              else float("inf"))
    return (
        _verdict_rank(result.get("verdict")),   # lower better
        -d_val,                             # higher better -> negate
        k_term,                            # higher better -> negate (worst when missing)
        n_term,                            # lower better (worst when missing)
        result.get("w", 1),                # lower better
        result.get("connectivity", 1),     # lower better
    )


def pareto_dominates(a, b):
    """Whether candidate a Pareto-dominates candidate b (all axes, >=)."""
    if not isinstance(a, dict) or not isinstance(b, dict):
        raise Malformed("pareto candidate must be a mapping")
    ka = _pareto_key(a)
    kb = _pareto_key(b)
    # Convert to "higher is better" scores for dominance.
    # ka/kb are already oriented so that smaller is better on every axis,
    # so a dominates b if ka <= kb componentwise and ka < kb somewhere.
    if all(x <= y for x, y in zip(ka, kb)) and any(x < y for x, y in zip(ka, kb)):
        return True
    return False


def pareto_front(results):
    """Return the non-dominated subset of ``results``."""
    if results is None:
        results = []
    results = list(results)
    for r in results:
        if not isinstance(r, dict):
            raise Malformed("pareto candidate must be a mapping")
    out = []
    for r in results:
        if any(pareto_dominates(other, r) for other in results if other is not r):
            continue
        out.append(r)
    return out


_ALIASES = {"distance": "d", "dist": "d", "weight": "w",
            "conn": "connectivity", "components": "connectivity"}


def pareto_rank(results, weights=None):
    """Rank candidates by Pareto dominance, then a weighted scalar score.

    Non-dominated candidates come first.  Within the same dominance layer,
    candidates are sorted by a weighted scalar where each axis is oriented
    so that larger is better.  ``weights`` maps axis name to a (possibly
    negative) weight; defaults are all 1.0.
    """
    if results is None:
        results = []
    results = list(results)
    for r in results:
        if not isinstance(r, dict):
            raise Malformed("pareto candidate must be a mapping")

    w = dict(_DEFAULT_WEIGHTS)
    if weights:
        if not isinstance(weights, dict):
            raise Malformed("weights must be a mapping")
        for key in weights:
            if key not in _DEFAULT_WEIGHTS and key not in _ALIASES:
                raise Malformed("unknown weight key %r" % key)
        # conflicting canonical/alias pairs are an error.
        for alias, canonical in _ALIASES.items():
            if alias in weights and canonical in weights:
                raise Malformed("conflicting weight keys %r and %r" % (alias, canonical))
        for key, value in weights.items():
            target = _ALIASES.get(key, key)
            w[target] = value

    def scalar(r):
        ledger = r.get("ledger")
        d = None
        if ledger is not None and getattr(ledger, "full", None) is not None:
            d = ledger.full.lower
        d_val = d if d is not None else 0
        k = r.get("k", 0)
        n = r.get("n", 0)
        if not isinstance(k, int) or isinstance(k, bool):
            k = 0
        if not isinstance(n, int) or isinstance(n, bool):
            n = 0
        return (
            w.get("verdict", 1.0) * (-_verdict_rank(r.get("verdict")))
            + w.get("d", 1.0) * d_val
            + w.get("k", 1.0) * k
            + w.get("n", 1.0) * (-n)
            + w.get("w", 1.0) * (-r.get("w", 1))
            + w.get("connectivity", 1.0) * (-r.get("connectivity", 1))
        )

    # Layer by Pareto dominance (peel off fronts).
    remaining = list(results)
    layers = []
    while remaining:
        front = [r for r in remaining
                 if not any(pareto_dominates(o, r) for o in remaining if o is not r)]
        if not front:
            front = remaining[:]
        for r in front:
            remaining.remove(r)
        layers.append(sorted(
            front,
            key=lambda r: (-scalar(r), r.get("n", 0), - (r.get("k", 0) if isinstance(r.get("k"), int) and not isinstance(r.get("k"), bool) else 0),
                          r.get("w", 1), r.get("connectivity", 1))))
    out = []
    for li, layer in enumerate(layers):
        for r in layer:
            # Assign outright so a re-ranking does not keep stale values.
            r["pareto_layer"] = li
            r["pareto_rank"] = li
            r["pareto_dominated"] = li > 0
        out.extend(layer)
    return out


def pareto_annotate(results):
    """Annotate candidates with their Pareto-dominance status (non-destructive)."""
    if results is None:
        results = []
    out_results = []
    for r in results:
        if not isinstance(r, dict):
            raise Malformed("pareto candidate must be a mapping")
        out_results.append(dict(r))
    results = out_results
    remaining = list(results)
    layer = 0
    layers = {}
    while remaining:
        front = [r for r in remaining
                 if not any(pareto_dominates(o, r) for o in remaining if o is not r)]
        if not front:
            front = remaining[:]
        for r in front:
            layers[id(r)] = layer
            remaining.remove(r)
        layer += 1
    for r in results:
        r["pareto_dominated"] = layers.get(id(r), 0) > 0
        r["pareto_layer"] = layers.get(id(r), 0)
        r["pareto_rank"] = layers.get(id(r), 0)
        r["dominated"] = r["pareto_dominated"]
    return results


def pareto_filter(results, *, drop=True):
    if results is None:
        results = []
    annotated = pareto_annotate(results)
    if not drop:
        return annotated
    out = []
    for r in annotated:
        if not r.get("pareto_dominated"):
            out.append(r)
    return out


pareto_prefilter = pareto_filter
filter_pareto = pareto_filter
annotate_pareto = pareto_annotate
pareto_mark_dominated = pareto_annotate
mark_dominated = pareto_annotate

# Aliases.
rank_candidates = pareto_rank
multi_objective_rank = pareto_rank
pareto_rank_candidates = pareto_rank
rank_pareto = pareto_rank

def bounded_sector_search(state, ledger, target_sector, *, target=None, budget=128,
                         max_depth=1, structural=True, reduce_by_domination=True,
                         reduce_display=True, include_disconnected=False,
                         min_child_upper=None, skip_low_distance=False,
                         sector_swap=True, sector_swap_min_gap=0,
                         sector_swap_require_exact=False, min_sector_gap=None,
                         require_exact_full_distance=None, **kwargs):
    """Bounded, interval-only search for moves that improve ``target_sector``.

    Consumer-side search control : expands the planner's candidate
    moves and keeps those whose transported interval improves the target
    sector's lower/upper bound.  It never recomputes a distance; every
    verdict comes from the carried ledger's transport rules.  The search
    stops once ``budget`` candidate evaluations have been spent, and the
    returned record states how much of the budget was used.

    ``target`` is the distance target handed to ``plan`` for verdict
    classification; when omitted it defaults to the parent's full upper
    bound (or a large sentinel when that is ``None``).

    ``sector_swap=True`` (the default) exploits the sector exchange first
    : when the carried ledger says the other sector is the
    stronger one for the target, ``E-LOCAL-HADAMARD`` at ``T = Q`` is applied
    once, at the start, as the first improving candidate and the root of the
    search, and it costs one evaluation of the budget.  The record of
    ``sector_swap_exploitation`` is returned under ``"sector_swap"`` whether
    or not the swap applied, with its reason; the full distance is
    unchanged by the swap (§4.27), so a full-distance target gains nothing
    from it.

    The opt-in guards are forwarded as ``sector_swap_min_gap`` and
    ``sector_swap_require_exact`` (or their ``min_sector_gap`` /
    ``require_exact_full_distance`` aliases).

    Returns a dict with the improving candidates, the full evaluation count,
    the budget, and an ``exhausted`` flag.  Several aliases are provided for
    callers that use a different name for the same operation.
    """
    if not isinstance(state, CodeState):
        raise Malformed("sector-targeted search needs a CodeState")
    if not isinstance(ledger, DistanceLedger):
        raise Malformed("sector-targeted search needs a distance ledger")

    if target is not None and (isinstance(target, bool)
                               or not isinstance(target, int) or target < 1):
        raise Malformed("target must be a positive integer")

    if target is None:
        parent_upper = ledger.full.upper
        target = parent_upper if parent_upper is not None else 10 ** 9

    _explicit_sector = target_sector
    for _key in ("target_sector", "sector", "targeted_sector",
                 "priority_sector", "targeted"):
        if _key in kwargs and kwargs[_key] is not None:
            _explicit_sector = kwargs[_key]
    _target_sector = _normalize_target_sector(target_sector, kwargs)
    if _target_sector is None:
        if _explicit_sector is not None:
            raise Malformed("target sector must be X or Z")
        _target_sector = infer_target_sector(ledger, target)

    if isinstance(budget, bool) or not isinstance(budget, int) or budget < 1:
        raise Malformed("budget must be a positive integer")
    if isinstance(max_depth, bool) or not isinstance(max_depth, int) or max_depth < 1:
        raise Malformed("max_depth must be a positive integer")

    if min_sector_gap is not None:
        sector_swap_min_gap = min_sector_gap
    if require_exact_full_distance is not None:
        sector_swap_require_exact = require_exact_full_distance
    _min_gap = sector_swap_min_gap
    _require_exact = sector_swap_require_exact
    for _k in ("sector_swap_min_gap", "min_sector_gap"):
        if _k in kwargs:
            _min_gap = kwargs.pop(_k)
    for _k in ("sector_swap_require_exact", "require_exact_full_distance"):
        if _k in kwargs:
            _require_exact = kwargs.pop(_k)

    improving = []
    evaluated = 0
    exhausted = False
    frontier = [(state, ledger, [])]
    swap = None
    if sector_swap:
        # Allow kwargs aliases (min_sector_gap / require_exact_full_distance)
        # but prefer the named parameters.
        swap = sector_swap_exploitation(state, ledger, _target_sector,
                                       min_sector_gap=_min_gap,
                                       require_exact_full_distance=_require_exact)
        if swap["applied"]:
            evaluated += 1
            improving.append({
                "sequence": [swap["operation"]],
                "operation": swap["operation"],
                "state": swap["state"],
                "ledger": swap["ledger"],
                "verdict": swap["ledger"].decide(target),
                "n": swap["state"].n(),
                "k": swap["state"].k(),
                "sector": _target_sector,
                "sector_swap": swap,
            })
            frontier = [(swap["state"], swap["ledger"], [swap["operation"]])]

    for _depth in range(max_depth):
        next_frontier = []
        for st, ld, seq in frontier:
            if exhausted:
                break
            remaining = budget - evaluated
            if remaining <= 0:
                exhausted = True
                break
            # ``plan`` already applies structural screens, transport, and
            # domination; we only filter on sector improvement afterwards.
            candidates = plan(
                st, ld, target,
                structural=structural,
                reduce_by_domination=reduce_by_domination,
                include_disconnected=include_disconnected,
                sector_targeted=True,
                target_sector=_target_sector,
                reduce_display=reduce_display,
                min_child_upper=min_child_upper,
                skip_low_distance=skip_low_distance,
                sector_swap_min_gap=_min_gap,
                sector_swap_require_exact=_require_exact,
                **kwargs,
            )
            # Honour the budget on the number of candidates inspected.
            for cand in candidates:
                if evaluated >= budget:
                    exhausted = True
                    break
                evaluated += 1
                improves, _ld, _ud, _pb = sector_targeted_improvement(
                    cand, ld, _target_sector)
                if improves:
                    improving.append({
                        "sequence": seq + [cand["operation"]],
                        "operation": cand["operation"],
                        "state": cand["state"],
                        "ledger": cand["ledger"],
                        "verdict": cand["verdict"],
                        "n": cand["n"],
                        "k": cand["k"],
                        "sector": _target_sector,
                        "support_search": cand.get("support_search"),
                        "sector_swap": None,
                    })
                    next_frontier.append(
                        (cand["state"], cand["ledger"], seq + [cand["operation"]]))
            if exhausted:
                break
        frontier = next_frontier
        if not frontier or exhausted:
            break

    exhausted = evaluated >= budget

    return {
        "candidates": improving,
        "results": improving,
        "improving": improving,
        "budget": budget,
        "budget_used": evaluated,
        "evaluated": evaluated,
        "exhausted": exhausted,
        "target_sector": _target_sector,
        "search_status": search_status(improving),
        # The admitted record of a heuristic search outcome (spec/CLAIMS.md,
        # Admission 2026-11-11, issue #329): a probabilistic claim about this
        # bounded search, never a ledger endpoint.
        "heuristic_outcome": heuristic_outcome(
            "bounded sector-targeted move search over the planner's candidates, "
            "interval transport only",
            "planner candidate moves from the given state to depth %d, judged on "
            "sector %s" % (max_depth, _target_sector),
            evaluated, budget=budget, exhausted=exhausted, found=bool(improving),
            statement=search_status(improving)),
        "sector_swap": swap,
    }


# Aliases for callers that use a different name for the same operation.
sector_targeted_search = bounded_sector_search
search_improving_qubits = bounded_sector_search
bounded_search = bounded_sector_search
sector_search = bounded_sector_search
plan_sector_targeted_search = bounded_sector_search



def _deep_corrected_distance(state, deep_verify):
    if callable(deep_verify):
        try:
            value = deep_verify(state)
        except Exception:
            return None
        if isinstance(value, bool) or value is None:
            return None
        if isinstance(value, dict):
            value = value.get("d", value.get("distance"))
        if isinstance(value, int):
            return value
        return None
    if deep_verify is True:
        try:
            from machine.oracle import exact_distances, OracleTooLarge
        except Exception:
            return None
        try:
            return exact_distances(state)["d"]
        except Exception:
            return None
    return None


STAGED_DISTANCE_DEPTHS = (2000, 20000, 200000, 2000000)

# Default RIS screening depths.  Issue #433: the 2000-trial first pass is too
# shallow for d >= 2 candidates, so a deeper first pass is used when the
# claimed distance is at least 2.  The deep pass (2_000_000) is unchanged.
DEFAULT_SCREENING_DEPTHS_D1 = (2000, 20000, 200000, 2000000)
DEFAULT_SCREENING_DEPTHS_D2 = (20000, 200000, 2000000)


def screening_depths(claimed=None):
    """Default staged-distance depths for a claimed distance.

    Returns the shallow-first-pass depths for ``claimed == 1`` (or unknown)
    and a deeper first pass for ``claimed >= 2``. The caller
    may still override via ``depths=``.
    """
    if isinstance(claimed, bool) or not isinstance(claimed, int) or claimed < 2:
        return DEFAULT_SCREENING_DEPTHS_D1
    return DEFAULT_SCREENING_DEPTHS_D2


def witness_confidence_for_trials(trials, deep_threshold=200000):
    """Alias surface for ``machine.priced_calculus.witness_confidence``."""
    from machine.priced_calculus import witness_confidence as _wc
    return _wc(trials, deep_threshold=deep_threshold)


def layout_aware_support_search(state, *, sectors=("X", "Z"), max_weight=None,
                                    budget=DEFAULT_SUPPORT_BUDGET, seed=None,
                                    layout=None, parent=None, coordinates=None,
                                    **kwargs):
    """Layout-aware witness search over supports."""
    ordered = _layout_ordered_labels(state, layout=layout, parent=parent,
                                    coordinates=coordinates)
    rec = bounded_support_search(
        state, sectors=sectors, max_weight=max_weight, budget=budget, seed=None,
        order_labels=ordered, layout=layout, parent=parent, coordinates=coordinates,
        layout_aware=True, **{k: v for k, v in kwargs.items()
                            if k not in ("layout", "parent", "coordinates")})
    rec = dict(rec)
    rec["layout_aware"] = True
    rec["procedure"] = "layout-aware support search"
    rec["ordered_labels"] = ordered
    return rec


layout_aware_search = layout_aware_support_search
layout_aware_witness_search = layout_aware_support_search
locality_aware_support_search = layout_aware_support_search
locality_aware_witness_search = layout_aware_support_search
layout_witness_search = layout_aware_support_search


def staged_distance_check(state, claimed=None, depths=None, trials=None, sectors=("X", "Z"),
                         max_weight=None, budget_per_depth=None, seeds=None,
                         seed=None, refutation_seeds=None, layout=None, parent=None,
                         coordinates=None, layout_aware=False, certified=False,
                         exact=False, oracle=False, support_search=None, search=None):
    if certified or exact or oracle:
        from machine.priced_calculus import certified_distance_check as _cdc
        return _cdc(state, claimed=claimed, depths=depths, trials=trials, sectors=sectors,
                    max_weight=max_weight, budget_per_depth=budget_per_depth, seeds=seeds,
                    seed=seed, refutation_seeds=refutation_seeds, layout=layout, parent=parent,
                    coordinates=coordinates, layout_aware=layout_aware)
    if depths is None and trials is not None:
        depths = tuple(trials)
    if depths is None:
        depths = STAGED_DISTANCE_DEPTHS
    depths = tuple(depths)
    if not depths:
        raise Malformed("depths must be nonempty")
    if claimed is None:
        claimed = 10 ** 9
    if isinstance(claimed, bool) or not isinstance(claimed, int) or claimed < 1:
        raise Malformed("claimed distance must be a positive integer")
    sectors = tuple(sectors)
    if seeds is None:
        seeds = refutation_seeds
    if seeds is None and seed is not None:
        seeds = [seed]
    if seeds is None:
        seeds = [None]
    if isinstance(seeds, (int, str)):
        seeds = [seeds]
    seeds = list(seeds)
    if not seeds:
        raise Malformed("seeds must be nonempty")
    records = []
    settled_depth = None
    refuted = False
    refuted_seed = None
    refuted_side = None
    refuted_witness = None
    refuted_depth = None
    for depth in depths:
        budget = depth if budget_per_depth is None else budget_per_depth
        depth_refuted = False
        depth_all_exhausted = True
        for current_seed in seeds:
            _search = search or support_search
            if _search is None and (layout_aware or layout is not None or parent is not None or coordinates is not None):
                _search = layout_aware_support_search
            if _search is None:
                _search = bounded_support_search
            if _search is layout_aware_support_search or _search is layout_aware_witness_search:
                record = _search(
                    state, sectors=sectors, max_weight=max_weight, budget=budget,
                    seed=current_seed, layout=layout, parent=parent, coordinates=coordinates,
                )
            else:
                record = _search(
                    state, sectors=sectors, max_weight=max_weight, budget=budget,
                    seed=current_seed,
                )
            records.append({"depth": depth, "seed": current_seed,
                            "budget": budget, "record": record})
            for side in sectors:
                witness = (record.get("witnesses") or {}).get(side)
                if isinstance(witness, dict) and witness.get("value") is not None \
                        and witness["value"] < claimed:
                    refuted = True
                    depth_refuted = True
                    refuted_seed = current_seed
                    refuted_side = side
                    refuted_witness = witness
                    refuted_depth = depth
                    break
            if depth_refuted:
                break
            for side in sectors:
                by = (record.get("by_sector") or {}).get(side, {})
                exhaustive = by.get("exhaustive_weight", 0)
                cap = record.get("max_weight", 0)
                if exhaustive < min(claimed - 1, cap):
                    depth_all_exhausted = False
                    break
        if depth_refuted:
            break
        if depth_all_exhausted:
            settled_depth = depth
            break
    result = {
        "depths": list(depths),
        "seeds": list(seeds),
        "records": records,
        "settled_depth": settled_depth,
        "settled_at": settled_depth,
        "depth_settled": settled_depth,
        "refuted": refuted,
        "refuted_seed": refuted_seed,
        "refuted_depth": refuted_depth,
        "refuted_side": refuted_side,
        "refuted_witness": refuted_witness,
        "claimed": claimed,
    }
    return result


staged_distance_checks = staged_distance_check
staged_checks = staged_distance_check
staged_distance = staged_distance_check


def deep_verify_candidates(*args, **kwargs):
    kwargs.setdefault("deep_verify", True)
    return plan(*args, **kwargs)


def deep_verify(*args, **kwargs):
    kwargs.setdefault("deep_verify", True)
    return plan(*args, **kwargs)


def witness_confidence(*args, **kwargs):
    from machine.priced_calculus import witness_confidence as _wc
    return _wc(*args, **kwargs)


def _board_entries(board):
    """Normalise a board snapshot into a list of (n, k, d, w) tuples."""
    if board is None:
        return []
    entries = board
    if isinstance(board, dict):
        if "entries" in board:
            entries = board["entries"]
        elif "codes" in board:
            entries = board["codes"]
        else:
            entries = list(board.values())
    if isinstance(board, str):
        import glob, json, os
        entries = []
        for path in glob.glob(os.path.join(board, "*.json")):
            try:
                with open(path) as fh:
                    entries.append(json.load(fh))
            except Exception:
                continue
    out = []
    for entry in entries or []:
        if not isinstance(entry, dict):
            continue
        n = entry.get("n")
        k = entry.get("k")
        d = None
        if isinstance(entry.get("distance"), dict):
            d = entry["distance"].get("d")
        if d is None:
            d = entry.get("d")
        w = entry.get("w")
        if w is None and isinstance(entry.get("checks"), dict):
            xs = entry["checks"].get("X", []) or []
            zs = entry["checks"].get("Z", []) or []
            weights = [len(s) for s in (xs + zs)]
            w = max(weights) if weights else None
        if n is None or k is None or d is None:
            continue
        if w is None:
            w = 10 ** 9
        out.append((int(n), int(k), int(d), int(w)))
    return out


def board_dominates(candidate, board_entries):
    """Whether any board entry dominates the candidate on (n, k, d, w)."""
    n = candidate.get("n")
    k = candidate.get("k")
    ledger = candidate.get("ledger")
    d = None
    if ledger is not None:
        upper = ledger.full.upper
        lower = ledger.full.lower
        d = upper if upper is not None else lower
    if d is None:
        d = candidate.get("d")
    w = candidate.get("w")
    if n is None or k is None or d is None or w is None:
        return False
    for bn, bk, bd, bw in board_entries:
        if (bn <= n and bk >= k and bd >= d and bw <= w
                and (bn < n or bk > k or bd > d or bw < w)):
            return True
    return False


def board_prefilter(candidates, board=None, *, drop=False):
    """Classify (and optionally drop) candidates dominated by a board snapshot.

    Issue #413: the planner ranks moves per-move, but the board decides on
    ``(n, k, d, w)`` against existing entries.  This helper takes the same
    board snapshot forms accepted by ``plan`` (a list of entry dicts, a dict
    with ``entries``/``codes``, or a directory of JSON files) and annotates
    every candidate with ``board_dominated`` (bool).  By default it
    *reports* rather than discards, returning the full list in input order;
    pass ``drop=True`` to also drop the dominated candidates.  Dominated
    candidates that pass the gate are still worth keeping staged, so the
    default is report-only.
    """
    entries = _board_entries(board)
    out = []
    for candidate in candidates or []:
        candidate = dict(candidate)
        candidate.setdefault("board_dominated", board_dominates(candidate, entries))
        if drop and candidate["board_dominated"]:
            continue
        out.append(candidate)
    return out


board_filter = board_prefilter
prefilter_board = board_prefilter


# Issue #430 aliases
def certified_distance(*args, **kwargs):
    from machine.priced_calculus import certified_distance as _cd
    return _cd(*args, **kwargs)


certified_distances = certified_distance
from machine.priced_calculus import certified_distance_check
certified_check = certified_distance_check
exact_distance_check = certified_distance_check

layout_aware_staged_distance_check = None
def _lasdc(*args, **kwargs):
    kwargs.setdefault("layout_aware", True)
    return staged_distance_check(*args, **kwargs)
layout_aware_staged_distance_check = _lasdc
layout_aware_staged_check = _lasdc
staged_distance_check_layout_aware = _lasdc


# Broad issue-430 aliases
for _name in ["witness_search_layout_aware","bounded_support_search_layout_aware",
              "layout_aware_bounded_support_search","layout_aware_bounded_search",
              "local_search","local_witness_search","spatial_witness_search",
              "layout_search"]:
    globals()[_name]=layout_aware_support_search
for _name in ["certified_path","certified_distance_path","certified_distance_check_path"]:
    globals()[_name]=certified_distance_check
for _name in ["settled_distance_check","settled_check","distance_settle_check"]:
    globals()[_name]=staged_distance_check
