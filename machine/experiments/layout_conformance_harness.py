"""Randomized conformance check for the layout cells.

The layout cells of ``spec/JUDGMENT_LAYER.md`` section 2d.5 state, for every
transition, how the layout travels (unchanged, restricted to the surviving
qubits, merged blockwise, or supplied afresh), the exact value and direction
of the interaction radius, and whether the layout's honesty (section 2d.3)
is preserved. ``machine/semantics.json`` ``layout_cells`` transcribes them.

This harness generates small random CSS states with random layouts, transits
every transition, and checks each cell's claim exactly: the radius is the
maximum squared Euclidean diameter over the displayed rows in exact rational
arithmetic, and honesty is decided by ``priced_calculus.layout_is_honest``.
Where the consumer has a path of its own (``run_sequence``, ``child_layout``,
``radius_squared_in_layout``) the harness also compares that path against the
cells, so the transcription is checked and not only the arithmetic.

It is evidence about the cells, never a proof: a run that reports no
violation failed to falsify them, and nothing here discharges
``OBL-LOCALITY-TRANSPORT``. The cells with no direction (``P-REBASE``) and the
non-transfer cases (``E-GRAFT``'s factor of two, ``C-DIRECT-SUM``'s and
``E-GLUE``'s honest-merge premise, ``E-EXTEND``'s supplied layout) are
exercised as coverage: the suite fails if it never observed a rebase
increasing and a rebase decreasing the radius, a graft increasing it, a
blockwise merge of two honest layouts that is dishonest, or a supplied
extension layout that is dishonest although the parent's was honest.

Report path: the run must not dirty a tracked file, so the JSON report goes
to ``layout_conformance_report.json`` in the system temporary directory by
default; set ``LAYOUT_CONFORMANCE_REPORT`` to another path, or to ``-`` to
skip the report. The case count defaults to ``DEFAULT_CASES`` and may be
overridden with ``LAYOUT_CONFORMANCE_CASES``.
"""

from __future__ import print_function

import itertools
import json
import os
import random
import subprocess
import sys
import tempfile
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
MACHINE = os.path.dirname(HERE)
ROOT = os.path.dirname(MACHINE)
for path in (MACHINE, ROOT, HERE):
    if path not in sys.path:
        sys.path.insert(0, path)

from machine import priced_calculus as pc  # noqa: E402
from priced_conformance_harness import random_state  # noqa: E402

MOVES = ("C-SKIP", "C-DELETE-CHECK", "C-ADD-CHECK", "C-SEQUENCE",
         "C-DIRECT-SUM", "E-GRAFT", "E-PEEL", "E-PUNCTURE",
         "E-LOCAL-HADAMARD", "P-REBASE", "E-EXTEND", "E-GLUE")

DEFAULT_CASES = 150
DEFAULT_SEED = 20261110
DEFAULT_REPORT_PATH = os.path.join(tempfile.gettempdir(),
                                   "layout_conformance_report.json")

# Moves whose radius cell is a non-increase, and moves whose cell is a
# non-decrease; a sequence drawn from one set composes to the same direction.
NON_INCREASING = ("C-SKIP", "C-DELETE-CHECK", "E-PEEL", "E-PUNCTURE",
                  "E-LOCAL-HADAMARD")
NON_DECREASING = ("C-SKIP", "C-ADD-CHECK", "E-LOCAL-HADAMARD")

HALF = Fraction(1, 2)


# --- layouts ---------------------------------------------------------------

def random_layout(rng, labels, layers, dishonest=False):
    """A random layout over ``labels``: a dict label -> (x, y) of Fractions.

    Honest by construction unless ``dishonest``: sites are integer grid
    points, so distinct sites are at least 1 apart, and at most ``layers``
    qubits are placed on one site. A dishonest layout breaks one of the two
    conditions at random: it overfills a site, or moves one site half a unit
    from another.
    """
    labels = list(labels)
    size = max(2, len(labels))
    pool = [(Fraction(x), Fraction(y)) for x in range(size) for y in range(size)]
    rng.shuffle(pool)
    occupancy = {}
    layout = {}
    for label in labels:
        for site in pool:
            if occupancy.get(site, 0) < layers:
                occupancy[site] = occupancy.get(site, 0) + 1
                layout[label] = site
                break
    if dishonest and len(labels) >= 2:
        a, b = rng.sample(labels, 2)
        if rng.random() < 0.5 and layers == 1:
            layout[b] = layout[a]
        else:
            x, y = layout[a]
            layout[b] = (x + HALF, y)
            # Overfill instead when the half step landed on nothing new.
            if layout[b] in layout.values() and layers > 1:
                for extra in labels:
                    if extra not in (a, b):
                        layout[extra] = layout[a]
                for extra in labels:
                    layout[extra] = layout[a]
    return layout


def honest(layout, layers):
    """The section 2d.3 honesty verdict of a layout dict."""
    return pc.layout_is_honest(list(layout.values()), layers)


def radius_sq(layout, state):
    """The exact squared interaction radius of ``state`` in ``layout``.

    ``interaction_radius_squared`` indexes its coordinate argument by qubit
    label, so a dict keyed by label serves as well as a list.
    """
    return pc.interaction_radius_squared(layout, [row.support for row in state.rows])


def restrict(layout, state):
    """The layout read at the state's qubits: section 2d.2's lambda | Q'."""
    return {q: layout[q] for q in state.Q}


def diam_sq(layout, support):
    return pc._diameter_squared(layout, support)


def _coordinate_json(value):
    """A Fraction as the document form the consumer reads: an int, or a
    decimal string at its exact value (only halves occur here)."""
    if value.denominator == 1:
        return int(value)
    return str(value.numerator / value.denominator)


def _minimum_logical(state, side):
    """A minimum-weight ``side`` logical of a small state, or None (k = 0).

    Brute force over supports; the harness's states have at most seven
    qubits. Used only to give the challenge-style document the witness block
    ``DistanceLedger.from_challenge`` requires, so the consumer path can run.
    """
    opposite = "Z" if side == "X" else "X"
    same = [row.mask for row in state.sector_rows(side)]
    other = [row.mask for row in state.sector_rows(opposite)]
    labels = list(state.Q)
    for weight in range(1, len(labels) + 1):
        for support in itertools.combinations(labels, weight):
            mask = pc.support_mask(support)
            if pc.commutes(mask, other) and not pc.in_span(mask, same):
                return list(support)
    return None


def document_for(state, layout, layers):
    """A challenge-style document for a root state with labels 0..n-1.

    ``CodeState.from_challenge`` reproduces ``state`` from it (the rows are
    independent and named a1.., b1.. in order), and ``run_sequence`` reads
    the layout from it, so the consumer's own path can be compared with the
    cells. Returns None when the state has no logical on some side (k = 0):
    the consumer's ledger needs a witness per side, and such a state has
    none to give.
    """
    n = len(state.Q)
    assert tuple(state.Q) == tuple(range(n))
    witnesses = {}
    for side in ("X", "Z"):
        support = _minimum_logical(state, side)
        if support is None:
            return None
        witnesses[side] = {"value": len(support), "confidence": "upper_bound",
                           "witness": support}
    return {
        "schema_version": "0.5",
        "name": "layout conformance case",
        "code_type": "CSS",
        "n": n,
        "k": state.k(),
        "checks": {
            "X": [list(row.support) for row in state.sector_rows("X")],
            "Z": [list(row.support) for row in state.sector_rows("Z")],
        },
        "distance": {"d": min(witnesses["X"]["value"], witnesses["Z"]["value"]),
                     "X": witnesses["X"], "Z": witnesses["Z"]},
        "provenance": {"authors": ["harness"], "construction": "random",
                       "date": "2026-11-10", "origin": "submission"},
        "locality": {
            "coordinates": [[_coordinate_json(c) for c in layout[q]] for q in range(n)],
            "layers": layers,
        },
    }


# --- random operands --------------------------------------------------------

def random_support(rng, labels, minimum=1):
    labels = list(labels)
    size = rng.randint(minimum, len(labels))
    return tuple(sorted(rng.sample(labels, size)))


def random_gl_matrix(rng, m):
    """A random invertible m x m matrix over F_2 (as lists of 0/1)."""
    for _ in range(200):
        rows = [[rng.randint(0, 1) for _ in range(m)] for _ in range(m)]
        masks = [sum(bit << j for j, bit in enumerate(row)) for row in rows]
        if pc.rank(masks) == m:
            return rows
    return [[1 if i == j else 0 for j in range(m)] for i in range(m)]


def graft_orders(state, qubit, sector):
    touching = [row.id for row in state.sector_rows(sector) if qubit in row.support]
    if not touching:
        return []
    return [list(order) for order in itertools.permutations(touching)]


def _shift_state(state, offset):
    """The same state with every qubit label raised by ``offset`` and the
    row identifiers moved to a disjoint block, so a direct sum applies."""
    rows = tuple(pc.Row(row.id.replace("a", "c", 1).replace("b", "d", 1), row.sector,
                        tuple(q + offset for q in row.support))
                 for row in state.rows)
    used = frozenset(row.id for row in rows)
    shifted = pc.CodeState(tuple(q + offset for q in state.Q), rows, used)
    shifted.validate()
    return shifted


# --- checks -----------------------------------------------------------------

class Case(object):
    """One random case: a root state, its layout, and the bookkeeping."""

    def __init__(self, state, layout, layers):
        self.state = state
        self.layout = layout
        self.layers = layers
        self.violations = []
        self.coverage = {}

    def transit(self, op):
        self.coverage[op] = self.coverage.get(op, 0) + 1

    def note(self, key):
        self.coverage[key] = self.coverage.get(key, 0) + 1

    def violation(self, op, claim, **detail):
        record = {"operation": op, "claim": claim,
                  "parent": _state_json(self.state),
                  "layout": {str(q): [str(c) for c in point]
                             for q, point in self.layout.items()},
                  "layers": self.layers}
        record.update(detail)
        self.violations.append(record)


def _state_json(state):
    return {"Q": list(state.Q),
            "rows": [[row.id, row.sector, list(row.support)] for row in state.rows]}


def _check_restriction(case, op, child, child_layout):
    """A restricted layout is honest when the parent's was (section 2d.3)."""
    if honest(case.layout, case.layers) and not honest(child_layout, case.layers):
        case.violation(op, "restriction of an honest layout is honest",
                       child=_state_json(child))
    if set(child_layout) != set(child.Q):
        case.violation(op, "child layout covers exactly the child's qubits",
                       child=_state_json(child))


def _check_consumer_single_step(case, op_dict, child, expected_sq, expected_honest):
    """Compare the consumer's own trace and layout transport with the cell."""
    if tuple(case.state.Q) != tuple(range(len(case.state.Q))):
        return
    document = document_for(case.state, case.layout, case.layers)
    if document is None:
        return
    case.note("consumer_path_comparisons")
    try:
        state, _ledger, trace = pc.run_sequence(document, [op_dict])
    except (pc.NoDerivation, pc.Malformed) as exc:
        case.violation(op_dict["op"], "consumer path evaluates the transition",
                       error=str(exc))
        return
    if state != child:
        case.violation(op_dict["op"], "consumer path reaches the same child",
                       consumer=_state_json(state), child=_state_json(child))
        return
    step = trace[0]
    expected_radius = pc.radius_nearest_decimal(expected_sq, 6)
    if step["interaction_radius"] != expected_radius:
        case.violation(op_dict["op"], "consumer trace radius equals the cell's value",
                       consumer=step["interaction_radius"], cell=expected_radius)
    planar = pc.layout_planar(document)
    expected_class = pc.locality_class(expected_sq, case.layers, planar=planar,
                                       honest=expected_honest)
    if step["locality_class"] != expected_class:
        case.violation(op_dict["op"], "consumer locality class follows the cell",
                       consumer=step["locality_class"], cell=expected_class)
    transported = pc.child_layout(document, child)
    if transported is None:
        case.violation(op_dict["op"], "consumer transports the layout to the child")
        return
    got = [tuple(pc._exact_coordinate(c) for c in point)
           for point in transported["coordinates"]]
    want = [case.layout[q] for q in child.Q]
    if got != want:
        case.violation(op_dict["op"], "consumer child layout is the restriction",
                       consumer=[[str(c) for c in p] for p in got],
                       cell=[[str(c) for c in p] for p in want])
    consumer_sq = pc.radius_squared_in_layout(document, child)
    if consumer_sq != expected_sq:
        case.violation(op_dict["op"], "radius_squared_in_layout equals the cell's value",
                       consumer=str(consumer_sq), cell=str(expected_sq))


def check_skip(case):
    state, layout = case.state, case.layout
    r = radius_sq(layout, state)
    child = state.skip()
    case.transit("C-SKIP")
    r2 = radius_sq(layout, child)
    if r2 != r:
        case.violation("C-SKIP", "r' = r", parent_sq=str(r), child_sq=str(r2))
    _check_consumer_single_step(case, {"op": "C-SKIP"}, child, r2,
                                honest(layout, case.layers))


def check_delete(case):
    state, layout = case.state, case.layout
    r = radius_sq(layout, state)
    for row in state.rows:
        child = state.delete_check(row.id)
        case.transit("C-DELETE-CHECK")
        r2 = radius_sq(layout, child)
        if r2 > r:
            case.violation("C-DELETE-CHECK", "r' <= r", row=row.id,
                           parent_sq=str(r), child_sq=str(r2))
        _check_consumer_single_step(case, {"op": "C-DELETE-CHECK", "row_id": row.id},
                                    child, r2, honest(layout, case.layers))


def check_add(case, rng, attempts=4):
    state, layout = case.state, case.layout
    r = radius_sq(layout, state)
    for _ in range(attempts):
        sector = rng.choice(("X", "Z"))
        support = random_support(rng, state.Q)
        try:
            child = state.add_check(sector, list(support))
        except (pc.NoDerivation, pc.Malformed):
            continue
        case.transit("C-ADD-CHECK")
        r2 = radius_sq(layout, child)
        expected = max(r, diam_sq(layout, support))
        if r2 != expected:
            case.violation("C-ADD-CHECK", "r' = max(r, diam(new row))",
                           support=list(support), parent_sq=str(r),
                           child_sq=str(r2), expected_sq=str(expected))
        if r2 < r:
            case.violation("C-ADD-CHECK", "r' >= r", support=list(support),
                           parent_sq=str(r), child_sq=str(r2))
        _check_consumer_single_step(
            case, {"op": "C-ADD-CHECK", "sector": sector, "support": list(support)},
            child, r2, honest(layout, case.layers))
        return


def check_graft(case, order_cap=6):
    state, layout = case.state, case.layout
    r = radius_sq(layout, state)
    for qubit in state.Q:
        for sector in ("X", "Z"):
            for order in graft_orders(state, qubit, sector)[:order_cap]:
                try:
                    child = state.graft(qubit, sector, order)
                except (pc.NoDerivation, pc.Malformed):
                    continue
                case.transit("E-GRAFT")
                child_layout = restrict(layout, child)
                r2 = radius_sq(child_layout, child)
                if r2 > 4 * r:
                    case.violation("E-GRAFT", "r' <= 2r", qubit=qubit, sector=sector,
                                   order=order, parent_sq=str(r), child_sq=str(r2))
                if r2 > r:
                    case.note("graft_increases")
                _check_restriction(case, "E-GRAFT", child, child_layout)
                _check_consumer_single_step(
                    case, {"op": "E-GRAFT", "qubit": qubit, "sector": sector,
                           "ordered_row_ids": order},
                    child, r2, honest(layout, case.layers))


def check_peel(case):
    state, layout = case.state, case.layout
    r = radius_sq(layout, state)
    for qubit in state.Q:
        for sector in ("X", "Z"):
            touching = [row for row in state.sector_rows(sector) if qubit in row.support]
            if len(touching) != 1:
                continue
            try:
                child = state.peel(qubit, sector, touching[0].id)
            except (pc.NoDerivation, pc.Malformed):
                continue
            case.transit("E-PEEL")
            child_layout = restrict(layout, child)
            r2 = radius_sq(child_layout, child)
            if r2 > r:
                case.violation("E-PEEL", "r' <= r", qubit=qubit, sector=sector,
                               parent_sq=str(r), child_sq=str(r2))
            _check_restriction(case, "E-PEEL", child, child_layout)
            _check_consumer_single_step(
                case, {"op": "E-PEEL", "qubit": qubit, "sector": sector,
                       "row_id": touching[0].id},
                child, r2, honest(layout, case.layers))


def check_puncture(case):
    state, layout = case.state, case.layout
    r = radius_sq(layout, state)
    for qubit in state.Q:
        try:
            child = state.puncture(qubit)
        except (pc.NoDerivation, pc.Malformed):
            continue
        case.transit("E-PUNCTURE")
        child_layout = restrict(layout, child)
        r2 = radius_sq(child_layout, child)
        if r2 > r:
            case.violation("E-PUNCTURE", "r' <= r", qubit=qubit,
                           parent_sq=str(r), child_sq=str(r2))
        _check_restriction(case, "E-PUNCTURE", child, child_layout)
        _check_consumer_single_step(case, {"op": "E-PUNCTURE", "qubit": qubit},
                                    child, r2, honest(layout, case.layers))


def check_hadamard(case):
    state, layout = case.state, case.layout
    r = radius_sq(layout, state)
    child = state.hadamard_sector_swap()
    case.transit("E-LOCAL-HADAMARD")
    r2 = radius_sq(layout, child)
    if r2 != r:
        case.violation("E-LOCAL-HADAMARD", "r' = r", parent_sq=str(r), child_sq=str(r2))
    _check_consumer_single_step(case, {"op": "E-LOCAL-HADAMARD", "qubits": list(state.Q)},
                                child, r2, honest(layout, case.layers))


def check_rebase(case, rng):
    state, layout = case.state, case.layout
    r = radius_sq(layout, state)
    for sector in ("X", "Z"):
        m = len(state.sector_rows(sector))
        if m == 0:
            continue
        matrix = random_gl_matrix(rng, m)
        try:
            child = state.rebase(sector, matrix)
        except (pc.NoDerivation, pc.Malformed):
            continue
        case.transit("P-REBASE")
        r2 = radius_sq(layout, child)
        if r2 > r:
            case.note("rebase_increases")
        elif r2 < r:
            case.note("rebase_decreases")
        else:
            case.note("rebase_unchanged")
        _check_consumer_single_step(
            case, {"op": "P-REBASE", "sector": sector, "matrix": matrix},
            child, r2, honest(layout, case.layers))


def check_extend(case, rng, attempts=4):
    state, layout, layers = case.state, case.layout, case.layers
    r = radius_sq(layout, state)
    parent_honest = honest(layout, layers)
    top = max(state.Q) + 1
    for attempt in range(attempts):
        delta = tuple(range(top, top + rng.randint(0, 2)))
        new_layout = dict(layout)
        if delta:
            # A supplied layout agreeing with lambda on Q: honest or not.
            size = max(2, len(state.Q) + len(delta))
            dishonest_supply = rng.random() < 0.35
            for label in delta:
                if dishonest_supply:
                    anchor = rng.choice(list(state.Q))
                    x, y = layout[anchor]
                    new_layout[label] = (x + HALF, y) if rng.random() < 0.5 else (x, y)
                else:
                    for _ in range(100):
                        site = (Fraction(rng.randrange(size)), Fraction(rng.randrange(size)))
                        if sum(1 for p in new_layout.values() if p == site) < layers:
                            new_layout[label] = site
                            break
                    else:
                        new_layout[label] = (Fraction(size + label), Fraction(0))
        labels = tuple(sorted(set(state.Q) | set(delta)))
        additions = []
        for _ in range(rng.randint(1, 2)):
            support = random_support(rng, labels)
            if delta and not (set(support) & set(delta)):
                support = tuple(sorted(set(support) | {rng.choice(delta)}))
            additions.append((rng.choice(("X", "Z")), list(support)))
        try:
            child = state.extend_code(delta, additions)
        except (pc.NoDerivation, pc.Malformed):
            continue
        case.transit("E-EXTEND")
        r2 = radius_sq(new_layout, child)
        added = [row for row in child.rows if row.id not in state.used]
        expected = max([r] + [diam_sq(new_layout, row.support) for row in added])
        if r2 != expected:
            case.violation("E-EXTEND", "r' = max(r, max diam of added rows)",
                           delta=list(delta), additions=additions,
                           parent_sq=str(r), child_sq=str(r2), expected_sq=str(expected))
        if r2 < r:
            case.violation("E-EXTEND", "r' >= r", delta=list(delta),
                           parent_sq=str(r), child_sq=str(r2))
        supplied_honest = honest(new_layout, layers)
        if delta:
            if parent_honest and not supplied_honest:
                case.note("extend_supplied_dishonest_from_honest_parent")
            elif supplied_honest:
                case.note("extend_supplied_honest")
        else:
            if supplied_honest != parent_honest:
                case.violation("E-EXTEND", "with Delta empty honesty is inherited")
            _check_consumer_single_step(
                case, {"op": "E-EXTEND", "new_qubits": [], "additions": additions},
                child, r2, parent_honest)
        return


def check_direct_sum_and_glue(case, rng, other, other_layout):
    """C-DIRECT-SUM and E-GLUE against a second state on a disjoint namespace.

    ``other`` lives on labels disjoint from the case's state and carries its
    own layout ``other_layout``. The merged layout is blockwise: the second
    block is translated by an offset, large enough for an honest merge when
    the two factors are honest, or zero so that sites collide.
    """
    state, layout, layers = case.state, case.layout, case.layers
    r_a = radius_sq(layout, state)
    r_b = radius_sq(other_layout, other)
    span = max([p[0] for p in layout.values()] + [Fraction(0)]) + 1
    offset = span if rng.random() < 0.6 else Fraction(0)
    merged = dict(layout)
    for q, (x, y) in other_layout.items():
        merged[q] = (x + offset, y)
    try:
        child = pc.CodeState.direct_sum(state, other)
    except (pc.NoDerivation, pc.Malformed):
        return
    case.transit("C-DIRECT-SUM")
    r2 = radius_sq(merged, child)
    if r2 != max(r_a, r_b):
        case.violation("C-DIRECT-SUM", "r = max(r_A, r_B)", r_a=str(r_a), r_b=str(r_b),
                       child_sq=str(r2), other=_state_json(other))
    factors_honest = honest(layout, layers) and honest(other_layout, layers)
    merged_honest = honest(merged, layers)
    if factors_honest and not merged_honest:
        case.note("direct_sum_dishonest_merge_from_honest_factors")
    elif merged_honest:
        case.note("direct_sum_honest_merge")
    if merged_honest and not factors_honest:
        # The merge restricts to each factor; a restriction of an honest
        # layout is honest, so an honest merge has honest factors.
        case.violation("C-DIRECT-SUM", "an honest merged layout restricts to honest factors",
                       other=_state_json(other))
    # E-GLUE: a few random seam checks over the union.
    for _ in range(6):
        seams = []
        for _ in range(rng.randint(1, 2)):
            left = random_support(rng, state.Q)
            right = random_support(rng, other.Q)
            seams.append((rng.choice(("X", "Z")), list(left + right)))
        try:
            glued = state.glue(other, seam_checks=seams)
        except (pc.NoDerivation, pc.Malformed):
            continue
        case.transit("E-GLUE")
        r3 = radius_sq(merged, glued)
        expected = max([r_a, r_b] + [diam_sq(merged, tuple(sorted(s))) for _, s in seams])
        if r3 != expected:
            case.violation("E-GLUE", "r = max(r_A, r_B, max diam of seam rows)",
                           seams=seams, child_sq=str(r3), expected_sq=str(expected),
                           other=_state_json(other))
        if r3 < max(r_a, r_b):
            case.violation("E-GLUE", "r >= max(r_A, r_B)", seams=seams,
                           child_sq=str(r3), other=_state_json(other))
        break


def _single_step_candidates(state, rng):
    """Applicable single-state moves from ``state`` as (op dict, child)."""
    candidates = [({"op": "C-SKIP"}, state.skip()),
                  ({"op": "E-LOCAL-HADAMARD", "qubits": list(state.Q)},
                   state.hadamard_sector_swap())]
    for row in state.rows:
        candidates.append(({"op": "C-DELETE-CHECK", "row_id": row.id},
                           state.delete_check(row.id)))
    for qubit in state.Q:
        try:
            candidates.append(({"op": "E-PUNCTURE", "qubit": qubit}, state.puncture(qubit)))
        except (pc.NoDerivation, pc.Malformed):
            pass
        for sector in ("X", "Z"):
            touching = [row for row in state.sector_rows(sector) if qubit in row.support]
            if len(touching) == 1:
                try:
                    candidates.append(({"op": "E-PEEL", "qubit": qubit, "sector": sector,
                                        "row_id": touching[0].id},
                                       state.peel(qubit, sector, touching[0].id)))
                except (pc.NoDerivation, pc.Malformed):
                    pass
            for order in graft_orders(state, qubit, sector)[:2]:
                try:
                    candidates.append(({"op": "E-GRAFT", "qubit": qubit, "sector": sector,
                                        "ordered_row_ids": order},
                                       state.graft(qubit, sector, order)))
                except (pc.NoDerivation, pc.Malformed):
                    pass
    for _ in range(3):
        sector = rng.choice(("X", "Z"))
        support = random_support(rng, state.Q)
        try:
            candidates.append(({"op": "C-ADD-CHECK", "sector": sector,
                                "support": list(support)},
                               state.add_check(sector, list(support))))
        except (pc.NoDerivation, pc.Malformed):
            pass
    return candidates


def check_sequence(case, rng, length=None):
    """C-SEQUENCE: per-step transport composes, on the consumer's path too."""
    state, layout, layers = case.state, case.layout, case.layers
    if tuple(state.Q) != tuple(range(len(state.Q))):
        return
    length = length or rng.randint(2, 3)
    ops = []
    current = state
    expected = []
    for _ in range(length):
        candidates = _single_step_candidates(current, rng)
        if not candidates:
            break
        op, child = rng.choice(candidates)
        ops.append(op)
        current = child
        expected.append(radius_sq(restrict(layout, child), child))
    if not ops:
        return
    case.transit("C-SEQUENCE")
    r0 = radius_sq(layout, state)
    names = [op["op"] for op in ops]
    if all(name in NON_INCREASING for name in names) and expected[-1] > r0:
        case.violation("C-SEQUENCE", "a non-increasing chain does not increase r",
                       operations=names, parent_sq=str(r0), child_sq=str(expected[-1]))
    if all(name in NON_DECREASING for name in names) and expected[-1] < r0:
        case.violation("C-SEQUENCE", "a non-decreasing chain does not decrease r",
                       operations=names, parent_sq=str(r0), child_sq=str(expected[-1]))
    document = document_for(state, layout, layers)
    if document is None:
        return
    case.note("consumer_path_comparisons")
    try:
        final, _ledger, trace = pc.run_sequence(document, ops)
    except (pc.NoDerivation, pc.Malformed) as exc:
        case.violation("C-SEQUENCE", "consumer path evaluates the sequence",
                       operations=names, error=str(exc))
        return
    if final != current:
        case.violation("C-SEQUENCE", "consumer path reaches the same child", operations=names)
        return
    for step, want in zip(trace, expected):
        if step["interaction_radius"] != pc.radius_nearest_decimal(want, 6):
            case.violation("C-SEQUENCE", "consumer trace radius equals the per-step cell",
                           operations=names, step=step["step"],
                           consumer=step["interaction_radius"],
                           cell=pc.radius_nearest_decimal(want, 6))
    transported = pc.child_layout(document, final)
    if transported is None:
        case.violation("C-SEQUENCE", "consumer transports the layout through the sequence",
                       operations=names)
        return
    got = [tuple(pc._exact_coordinate(c) for c in point)
           for point in transported["coordinates"]]
    if got != [layout[q] for q in final.Q]:
        case.violation("C-SEQUENCE", "consumer child layout is the composed restriction",
                       operations=names)


def run_case(rng, state, layout, layers, other=None, other_layout=None):
    """Transit every move from one case; return (violations, coverage)."""
    case = Case(state, layout, layers)
    if not honest(layout, layers):
        case.note("dishonest_parent_cases")
    check_skip(case)
    check_delete(case)
    check_add(case, rng)
    check_graft(case)
    check_peel(case)
    check_puncture(case)
    check_hadamard(case)
    check_rebase(case, rng)
    check_extend(case, rng)
    if other is not None:
        check_direct_sum_and_glue(case, rng, other, other_layout)
    check_sequence(case, rng)
    return case.violations, case.coverage


def seeded_graft_increase_case():
    """A graft that increases the radius, so the refutation of the naive
    non-increase (section 4.21) is exercised in every run.

    Q = {0,...,4}; X rows (0,1) and (0,2,3,4); Z rows (0,1,2) and (3,4), the
    graftable fixture of ``machine/test_priced_calculus.py``. Qubit 0 sits at
    (2,0) between qubit 1 at (0,0) and qubits 2, 3, 4 at (2,1), (3,0), (4,0):
    every parent row has diameter at most sqrt(5), and the graft at qubit 0
    in the X sector mints the row {1,2,3,4} of diameter 4.
    """
    rows = (pc.Row("a1", "X", (0, 1)), pc.Row("a2", "X", (0, 2, 3, 4)),
            pc.Row("b1", "Z", (0, 1, 2)), pc.Row("b2", "Z", (3, 4)))
    state = pc.CodeState((0, 1, 2, 3, 4), rows, frozenset(row.id for row in rows))
    state.validate()
    layout = {0: (Fraction(2), Fraction(0)), 1: (Fraction(0), Fraction(0)),
              2: (Fraction(2), Fraction(1)), 3: (Fraction(3), Fraction(0)),
              4: (Fraction(4), Fraction(0))}
    return state, layout, 1


def run_suite(cases=DEFAULT_CASES, seed=DEFAULT_SEED):
    rng = random.Random(seed)
    total_violations = 0
    violation_shapes = []
    per_op_counts = {}
    coverage = {}
    attempted = 0
    for index in range(cases):
        n = rng.randint(3, 6)
        try:
            state = random_state(rng, list(range(n)))
        except RuntimeError:
            continue
        layers = rng.choice((1, 1, 2))
        dishonest = index % 7 == 6
        layout = random_layout(rng, state.Q, layers, dishonest=dishonest)
        other = other_layout = None
        if index % 2 == 0:
            try:
                other = _shift_state(random_state(rng, list(range(rng.randint(2, 4)))), n)
                other_layout = random_layout(rng, other.Q, layers)
            except (RuntimeError, pc.Malformed, pc.NoDerivation):
                other = other_layout = None
        attempted += 1
        violations, case_coverage = run_case(rng, state, layout, layers, other, other_layout)
        total_violations += len(violations)
        for key, count in case_coverage.items():
            coverage[key] = coverage.get(key, 0) + count
        for record in violations:
            op = record["operation"]
            per_op_counts[op] = per_op_counts.get(op, 0) + 1
            if len(violation_shapes) < 20:
                violation_shapes.append(record)
    state, layout, layers = seeded_graft_increase_case()
    violations, case_coverage = run_case(rng, state, layout, layers)
    total_violations += len(violations)
    for key, count in case_coverage.items():
        coverage[key] = coverage.get(key, 0) + count
    for record in violations:
        op = record["operation"]
        per_op_counts[op] = per_op_counts.get(op, 0) + 1
        if len(violation_shapes) < 20:
            violation_shapes.append(record)
    never_transited = [op for op in MOVES if coverage.get(op, 0) == 0]
    required_observations = ("graft_increases", "rebase_increases", "rebase_decreases",
                             "direct_sum_dishonest_merge_from_honest_factors",
                             "direct_sum_honest_merge",
                             "extend_supplied_dishonest_from_honest_parent",
                             "extend_supplied_honest", "dishonest_parent_cases",
                             "consumer_path_comparisons")
    unobserved = [key for key in required_observations if coverage.get(key, 0) == 0]
    return {
        "harness": "layout_conformance_harness",
        "git_commit": _git_commit(),
        "cases_attempted": attempted,
        "total_violations": total_violations,
        "per_operation_violation_counts": per_op_counts,
        "coverage": coverage,
        "moves": list(MOVES),
        "moves_never_transited": never_transited,
        "required_observations_missing": unobserved,
        "violation_shapes": violation_shapes,
        "note": "Evidence only. Does not discharge OBL-LOCALITY-TRANSPORT.",
    }


def _git_commit():
    try:
        return subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT,
                                       stderr=subprocess.DEVNULL).decode().strip()
    except (OSError, subprocess.SubprocessError):
        return "unknown"


def _report_path():
    override = os.environ.get("LAYOUT_CONFORMANCE_REPORT")
    if override == "-":
        return None
    if override:
        return override
    return DEFAULT_REPORT_PATH


def main():
    cases = DEFAULT_CASES
    raw = os.environ.get("LAYOUT_CONFORMANCE_CASES")
    if raw:
        try:
            cases = max(1, int(raw))
        except ValueError:
            print("ignoring non-integer LAYOUT_CONFORMANCE_CASES=%r" % raw)
    report = run_suite(cases=cases)
    print(json.dumps({k: report[k] for k in (
        "cases_attempted", "total_violations", "per_operation_violation_counts",
        "coverage", "moves_never_transited", "required_observations_missing")}, indent=2))
    out_path = _report_path()
    if out_path:
        try:
            parent = os.path.dirname(os.path.abspath(out_path))
            if parent:
                os.makedirs(parent, exist_ok=True)
            with open(out_path, "w") as handle:
                json.dump(report, handle, indent=2)
            print("report written to %s" % out_path)
        except OSError as exc:
            print("report not written (%s)" % exc)
    failures = []
    if report["total_violations"]:
        failures.append("%d violations" % report["total_violations"])
    if report["moves_never_transited"]:
        failures.append("moves never transited: %s" % ", ".join(report["moves_never_transited"]))
    if report["required_observations_missing"]:
        failures.append("coverage observations missing: %s"
                        % ", ".join(report["required_observations_missing"]))
    if failures:
        raise SystemExit("; ".join(failures))


if __name__ == "__main__":
    main()
