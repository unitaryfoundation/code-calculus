"""Sector-swap exploitation via E-LOCAL-HADAMARD at T = Q (C4).

The swap exchanges the two sector distances exactly and leaves the full
distance unchanged (`spec/OPERATIONAL_SEMANTICS.md` §4.27).  The consumer
exploits it for a sector-specific target; the conjugation identity it rests
on (`DERIVED_RELATIONS.md` §2b: swapping before a move equals
swapping after the mirrored move) is checked here on random states and
moves, which is an aid, not a proof.  The input ledgers of that check
contain the states' distances, as the transport rules assume: on a parent
with no logical qubit a finite carried endpoint is a false input, and the
two paths then differ only because the swap's transport normalizes such a
ledger to +inf while a deletion's does not visit the parent.
"""

import random
import unittest

from machine.oracle import exact_distances
from machine.planner import bounded_sector_search, plan
from machine.priced_calculus import (
    CodeState,
    DistanceLedger,
    Interval,
    Malformed,
    NoDerivation,
    Row,
    apply_operation,
    in_span,
    sector_swap_exploitation,
    sector_swap_if_beneficial,
)


def lopsided_state():
    """X on all four qubits, Z on one pair: k = 2, d_X = 1, d_Z = 2."""
    state = CodeState(
        (0, 1, 2, 3),
        (Row("a1", "X", (0, 1, 2, 3)), Row("b1", "Z", (0, 1))),
        frozenset(("a1", "b1")),
    )
    state.validate()
    return state


def exact_ledger(state):
    ledger = DistanceLedger(Interval(1, 1), {"X": Interval(1, 1), "Z": Interval(2, 2)})
    ledger.record_witness(state, "X", (2,), source="X witness")
    ledger.record_witness(state, "Z", (0, 2), source="Z witness")
    return ledger


def random_css(rng, n):
    """A well-formed random CSS state on ``n`` qubits with independent rows."""
    labels = tuple(range(n))
    x_masks = []
    for _ in range(rng.randint(0, 3)):
        mask = 0
        for q in labels:
            if rng.random() < 0.5:
                mask |= 1 << q
        if mask and not in_span(mask, x_masks):
            x_masks.append(mask)
    perp = [m for m in range(1, 1 << n)
            if all((m & x).bit_count() % 2 == 0 for x in x_masks)]
    rng.shuffle(perp)
    z_masks = []
    for mask in perp[:rng.randint(0, 3)]:
        if not in_span(mask, z_masks):
            z_masks.append(mask)
    rows = []
    for index, mask in enumerate(x_masks):
        rows.append(Row("a%d" % (index + 1), "X", tuple(q for q in labels if mask >> q & 1)))
    for index, mask in enumerate(z_masks):
        rows.append(Row("b%d" % (index + 1), "Z", tuple(q for q in labels if mask >> q & 1)))
    state = CodeState(labels, tuple(rows), frozenset(row.id for row in rows))
    state.validate()
    return state


def mirrored(operation):
    """The same move with its sector parameter exchanged."""
    out = dict(operation)
    if "sector" in out:
        out["sector"] = "Z" if out["sector"] == "X" else "X"
    if "additions" in out:
        out["additions"] = [("Z" if sector == "X" else "X", support)
                            for sector, support in out["additions"]]
    return out


def candidate_operations(rng, state):
    """One move of each admitted unary family that names a sector, plus the
    sector-free deletion and puncture."""
    ops = []
    for row in state.rows:
        ops.append({"op": "C-DELETE-CHECK", "row_id": row.id})
    for q in state.Q:
        ops.append({"op": "E-PUNCTURE", "qubit": q})
        for sector in ("X", "Z"):
            touching = [row.id for row in state.sector_rows(sector) if q in row.support]
            if len(touching) == 1:
                ops.append({"op": "E-PEEL", "qubit": q, "sector": sector,
                            "row_id": touching[0]})
            if touching:
                ops.append({"op": "E-GRAFT", "qubit": q, "sector": sector,
                            "ordered_row_ids": touching})
    sector = rng.choice(("X", "Z"))
    support = sorted(rng.sample(list(state.Q), rng.randint(1, len(state.Q))))
    ops.append({"op": "C-ADD-CHECK", "sector": sector, "support": support})
    for sector in ("X", "Z"):
        m = len(state.sector_rows(sector))
        if m:
            matrix = [[1 if i == j else 0 for j in range(m)] for i in range(m)]
            if m > 1:
                matrix[0][1] = 1
            ops.append({"op": "P-REBASE", "sector": sector, "matrix": matrix})
    ops.append({"op": "E-EXTEND", "new_qubits": [max(state.Q) + 1],
                "additions": [(sector, sorted(support + [max(state.Q) + 1]))]})
    return ops


def sound_ledger(state):
    """Lower endpoints 0, upper endpoints the exact sector distances (the
    oracle is consulted by this test only), and a weight-1 witness per
    sector where one exists: a ledger that contains the state's distances,
    as the transport rules assume of their input."""
    exact = exact_distances(state)
    if exact["d"] is None:
        ledger = DistanceLedger(Interval(None, None),
                                {"X": Interval(None, None), "Z": Interval(None, None)})
    else:
        ledger = DistanceLedger(Interval(0, exact["d"]),
                                {side: Interval(0, exact[side]) for side in ("X", "Z")})
    for sector in ("X", "Z"):
        for q in state.Q:
            try:
                ledger.record_witness(state, sector, (q,), source="w")
                break
            except NoDerivation:
                continue
    return ledger


def interval_view(ledger):
    data = ledger.as_json()
    return {key: data[key] for key in ("d", "d_X", "d_Z", "witnesses")}


class SectorSwapExploitationTests(unittest.TestCase):
    def test_a_weaker_target_sector_is_swapped_and_the_full_distance_kept(self):
        state = lopsided_state()
        record = sector_swap_exploitation(state, exact_ledger(state), "X")
        self.assertTrue(record["applied"])
        self.assertEqual(record["operation"], {"op": "E-LOCAL-HADAMARD", "qubits": [0, 1, 2, 3]})
        self.assertEqual(record["after"]["X"], {"lower": 2, "upper": 2})
        self.assertEqual(record["after"]["Z"], {"lower": 1, "upper": 1})
        self.assertEqual(record["full_distance"]["before"], {"lower": 1, "upper": 1})
        self.assertEqual(record["full_distance"]["after"], {"lower": 1, "upper": 1})
        self.assertTrue(record["full_distance"]["unchanged"])
        self.assertIn("full distance is unchanged", record["reason"])
        # The witnesses changed sides and were revalidated on the child.
        self.assertEqual([w["support"] for w in record["ledger"].witnesses["X"]], [[0, 2]])
        self.assertEqual([w["support"] for w in record["ledger"].witnesses["Z"]], [[2]])
        self.assertEqual(record["state"].sector_rows("Z")[0].support, (0, 1, 2, 3))

    def test_a_stronger_target_sector_is_left_alone(self):
        state = lopsided_state()
        record = sector_swap_exploitation(state, exact_ledger(state), "Z")
        self.assertFalse(record["applied"])
        self.assertIsNone(record["operation"])
        self.assertIs(record["state"], state)
        self.assertIn("already at least as strong", record["reason"])

    def test_a_full_distance_target_gains_nothing(self):
        state = lopsided_state()
        for target in (None, "d", "full"):
            record = sector_swap_exploitation(state, exact_ledger(state), target)
            self.assertFalse(record["applied"])
            self.assertIsNone(record["target_sector"])
            self.assertIn("full distance unchanged", record["reason"])
            self.assertIn("d' = d", record["full_distance"]["invariant"])

    def test_equal_lower_endpoints_are_decided_by_the_upper_endpoints(self):
        state = lopsided_state()
        ledger = DistanceLedger(Interval(1, 2), {"X": Interval(1, 3), "Z": Interval(1, 2)})
        self.assertFalse(sector_swap_exploitation(state, ledger, "X")["applied"])
        self.assertTrue(sector_swap_exploitation(state, ledger, "Z")["applied"])
        unbounded = DistanceLedger(Interval(1, None), {"X": Interval(1, 2), "Z": Interval(1, None)})
        self.assertTrue(sector_swap_exploitation(state, unbounded, "X")["applied"])

    def test_the_two_tuple_helper_is_kept(self):
        state = CodeState((0, 1), (Row("a1", "X", (0,)),), frozenset(("a1",)))
        ledger = DistanceLedger(Interval(1, 2), {"X": Interval(1, 2), "Z": Interval(3, 3)})
        _new_state, new_ledger = sector_swap_if_beneficial(state, ledger, "X")
        self.assertEqual(new_ledger.sector["X"].lower, 3)
        ledger = DistanceLedger(Interval(2, 2), {"X": Interval(2, 2), "Z": Interval(1, 1)})
        _new_state, new_ledger = sector_swap_if_beneficial(state, ledger, "X")
        self.assertEqual(new_ledger.sector["X"].lower, 2)
        with self.assertRaises(Malformed):
            sector_swap_exploitation(state, {"X": Interval(1, 1)}, "X")


class SectorSwapGuardTests(unittest.TestCase):
    def test_require_exact_full_distance_refuses_inexact_full(self):
        state = lopsided_state()
        ledger = DistanceLedger(Interval(1, 2), {"X": Interval(1, 1), "Z": Interval(2, 2)})
        record = sector_swap_exploitation(state, ledger, "X",
                                         require_exact_full_distance=True)
        self.assertFalse(record["applied"])
        self.assertEqual(record["guard"], "require_exact_full_distance")
        self.assertEqual(record["guard_name"], "require_exact_full_distance")
        # exact full interval lets the swap apply (when ordering allows)
        ledger2 = exact_ledger(state)
        record2 = sector_swap_exploitation(state, ledger2, "X",
                                          require_exact_full_distance=True)
        self.assertTrue(record2["applied"])

    def test_min_sector_gap_uses_other_lower_minus_target_upper(self):
        state = CodeState((0, 1, 2), (Row("b1", "Z", (0, 1)),
                                     Row("b2", "Z", (1, 2))),
                          frozenset(("b1", "b2")))
        state.validate()
        ledger = DistanceLedger(Interval(1, 1),
                                {"X": Interval(1, 3), "Z": Interval(1, 8)})
        # gap = 1 - 3 = -2 < 1 -> refused
        record = sector_swap_exploitation(state, ledger, "X", min_sector_gap=1)
        self.assertFalse(record["applied"])
        self.assertEqual(record["guard"], "min_sector_gap")
        # target upper finite, other lower finite but too small -> refused
        ledger2 = DistanceLedger(Interval(1, 1),
                                {"X": Interval(1, 5), "Z": Interval(2, 8)})
        record2 = sector_swap_exploitation(state, ledger2, "X", min_sector_gap=5)
        self.assertFalse(record2["applied"])
        self.assertEqual(record2["guard"], "min_sector_gap")

    def test_guards_default_preserve_behaviour(self):
        state = lopsided_state()
        ledger = exact_ledger(state)
        record = sector_swap_exploitation(state, ledger, "X")
        self.assertTrue(record["applied"])
        self.assertIsNone(record["guard"])

    def test_validation_raises_malformed(self):
        state = lopsided_state()
        ledger = exact_ledger(state)
        with self.assertRaises(Malformed):
            sector_swap_exploitation(state, ledger, "X", min_sector_gap="lots")
        with self.assertRaises(Malformed):
            sector_swap_exploitation(state, ledger, "X", min_sector_gap=-1)
        with self.assertRaises(Malformed):
            sector_swap_exploitation(state, ledger, "X", min_sector_gap=2.5)
        with self.assertRaises(Malformed):
            sector_swap_exploitation(state, ledger, "X",
                                    require_exact_full_distance="yes")

    def test_sector_swap_if_beneficial_forwards_guards(self):
        state = CodeState((0, 1), (Row("a1", "X", (0,)),), frozenset(("a1",)))
        ledger = DistanceLedger(Interval(1, 2),
                                {"X": Interval(1, 2), "Z": Interval(3, 3)})
        _ns, nl = sector_swap_if_beneficial(state, ledger, "X", min_sector_gap=10)
        # gap = 3 - 2 = 1 < 10 -> refused, ledger unchanged
        self.assertEqual(nl.sector["X"].lower, 1)

    def test_bounded_sector_search_named_params(self):
        state = lopsided_state()
        ledger = exact_ledger(state)
        found = bounded_sector_search(state, ledger, "X", budget=6,
                                     sector_swap_min_gap=10)
        self.assertFalse(found["sector_swap"]["applied"])
        self.assertEqual(found["sector_swap"]["guard"], "min_sector_gap")
        found2 = bounded_sector_search(state, ledger, "X", budget=6,
                                       min_sector_gap=10)
        self.assertFalse(found2["sector_swap"]["applied"])

    def test_guard_does_not_mask_ordering_reason(self):
        state = lopsided_state()
        ledger = DistanceLedger(Interval(1, 2),
                                {"X": Interval(1, 3), "Z": Interval(1, 2)})
        record = sector_swap_exploitation(state, ledger, "X", min_sector_gap=5)
        self.assertFalse(record["applied"])
        self.assertIn("already at least as strong", record["reason"])
        self.assertIsNone(record["guard"])

class SwapConjugationTests(unittest.TestCase):
    def test_swapping_before_a_move_equals_swapping_after_the_mirrored_move(self):
        rng = random.Random(346)
        swap_of = lambda state: {"op": "E-LOCAL-HADAMARD", "qubits": list(state.Q)}
        compared = 0
        derived = 0
        for _ in range(60):
            state = random_css(rng, rng.randint(2, 5))
            ledger = sound_ledger(state)
            swapped = apply_operation(state, swap_of(state))
            swapped_ledger = ledger.propagate(swap_of(state), swapped, parent_state=state)
            for op in candidate_operations(rng, state):
                compared += 1
                try:
                    child = apply_operation(state, op)
                    child_ledger = ledger.propagate(op, child, parent_state=state)
                    first = (apply_operation(child, swap_of(child)),
                             child_ledger.propagate(swap_of(child),
                                                    apply_operation(child, swap_of(child)),
                                                    parent_state=child))
                except (NoDerivation, Malformed):
                    first = None
                try:
                    mirror = apply_operation(swapped, mirrored(op))
                    second = (mirror, swapped_ledger.propagate(mirrored(op), mirror,
                                                               parent_state=swapped))
                except (NoDerivation, Malformed):
                    second = None
                if first is None or second is None:
                    self.assertIsNone(first, op)
                    self.assertIsNone(second, op)
                    continue
                derived += 1
                self.assertEqual(first[0], second[0], op)
                self.assertEqual(interval_view(first[1]), interval_view(second[1]), op)
        self.assertGreater(derived, 100)
        self.assertGreater(compared, derived)


class PlannerIntegrationTests(unittest.TestCase):
    def test_plan_offers_the_swap_only_when_asked_and_targeted(self):
        state = lopsided_state()
        ledger = exact_ledger(state)
        plain = plan(state, ledger, 1, sector_targeted=True, target_sector="X")
        self.assertNotIn("E-LOCAL-HADAMARD", [r["operation"]["op"] for r in plain])
        untargeted = plan(state, ledger, 1, sector_swap=True)
        self.assertNotIn("E-LOCAL-HADAMARD", [r["operation"]["op"] for r in untargeted])
        results = plan(state, ledger, 1, sector_targeted=True, target_sector="X",
                       sector_swap=True)
        self.assertEqual(results[0]["operation"]["op"], "E-LOCAL-HADAMARD")
        self.assertTrue(results[0]["sector_swap"]["applied"])
        self.assertEqual(results[0]["verdict"], ledger.decide(1))
        self.assertEqual(results[0]["ledger"].sector["X"], Interval(2, 2))
        self.assertTrue(all(r["sector_swap"] is None for r in results[1:]))
        # The strong sector is already the target: nothing to exploit.
        for_z = plan(state, ledger, 1, sector_targeted=True, target_sector="Z",
                     sector_swap=True)
        self.assertNotIn("E-LOCAL-HADAMARD", [r["operation"]["op"] for r in for_z])

    def test_bounded_sector_search_exploits_the_swap_first(self):
        state = lopsided_state()
        ledger = exact_ledger(state)
        found = bounded_sector_search(state, ledger, "X", budget=6)
        self.assertTrue(found["sector_swap"]["applied"])
        # The swap is presentation-only: reported separately, never counted
        # as an improving candidate (qldpc-challenge #7116).
        self.assertEqual(found["presentation_candidates"][0]["sequence"],
                         [{"op": "E-LOCAL-HADAMARD", "qubits": [0, 1, 2, 3]}])
        self.assertEqual(found["presentation_candidates"][0]["ledger"].sector["X"],
                         Interval(2, 2))
        self.assertNotIn("E-LOCAL-HADAMARD",
                         [c["operation"]["op"] for c in found["candidates"]])
        self.assertGreaterEqual(found["evaluated"], 1)
        for candidate in found["candidates"]:
            self.assertEqual(candidate["sequence"][0]["op"], "E-LOCAL-HADAMARD")
            self.assertIsNone(candidate["sector_swap"])
        without = bounded_sector_search(state, ledger, "X", budget=6, sector_swap=False)
        self.assertIsNone(without["sector_swap"])
        self.assertNotIn("E-LOCAL-HADAMARD",
                         [c["operation"]["op"] for c in without["candidates"]])
        strong = bounded_sector_search(state, ledger, "Z", budget=6)
        self.assertFalse(strong["sector_swap"]["applied"])


if __name__ == "__main__":
    unittest.main()
