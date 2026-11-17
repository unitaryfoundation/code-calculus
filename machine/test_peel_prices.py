"""Sector-aware distance cells for `E-PEEL` and the recorded `E-PUNCTURE`
reduction (issue #331, the C2 follow-up of the 2026-11-10 disposition).

`spec/OPERATIONAL_SEMANTICS.md` §4.28 derives, for a peel at q in sector tau
with opposite sector sigma, the two exact relations

    d_tau'   = w_avoid,tau(q)  = min { |v| : v a parent tau logical, q not in v }
    d_sigma' = min(d_sigma, w_expose,sigma(q)),
    w_expose,sigma(q) = min { |z| - 1 : z a parent sigma logical, q in z },

so d_tau' >= d_tau and d_sigma - 1 <= d_sigma' <= d_sigma. The ledger carries
the unpriced bounds and, under `peel_price`, the exact cells. The prices in
these tests are computed by brute force from the parent, which is what a
consumer-supplied price is expected to be; the consumer itself never computes
them.
"""

import itertools
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.join(HERE, "experiments")
for path in (EXP, HERE):
    if path not in sys.path:
        sys.path.insert(0, path)

from issue21_challenge_replay import exact_distances  # noqa: E402
from machine.priced_calculus import (  # noqa: E402
    CodeState,
    DistanceLedger,
    Interval,
    NoDerivation,
    Row,
    commutes,
    in_span,
    support_mask,
)


def logicals(state, side):
    """Every ``side`` logical of a small state as (support, weight)."""
    opposite = "Z" if side == "X" else "X"
    same = [row.mask for row in state.sector_rows(side)]
    other = [row.mask for row in state.sector_rows(opposite)]
    found = []
    for weight in range(1, len(state.Q) + 1):
        for support in itertools.combinations(state.Q, weight):
            mask = support_mask(support)
            if commutes(mask, other) and not in_span(mask, same):
                found.append((support, weight))
    return found


def avoidance_minimum(state, side, qubit):
    """w_avoid,side(q): the lightest ``side`` logical avoiding ``qubit``."""
    weights = [w for support, w in logicals(state, side) if qubit not in support]
    return min(weights) if weights else None


def exposure_price(state, side, qubit):
    """w_expose,side(q): one less than the lightest ``side`` logical through ``qubit``."""
    weights = [w - 1 for support, w in logicals(state, side) if qubit in support]
    return min(weights) if weights else None


def exact_ledger(state):
    ex = exact_distances(state)
    return DistanceLedger(
        Interval(ex["d"], ex["d"]),
        {"X": Interval(ex["X"], ex["X"]), "Z": Interval(ex["Z"], ex["Z"])},
        witnesses={},
    ), ex


def peelable():
    """Q={0,1,2,3}; Z rows {0,1}, {2,3}; X row {0,1,2,3}: (d_X, d_Z) = (2, 2)."""
    return CodeState(
        (0, 1, 2, 3),
        (Row("b1", "Z", (0, 1)), Row("b2", "Z", (2, 3)), Row("a1", "X", (0, 1, 2, 3))),
        frozenset(("a1", "b1", "b2")),
    )


def witness_of_4_28():
    """§4.28's witness: Q={0,1,2}, X row {0,1}, Z row {0,1,2}; (d_X, d_Z) = (2, 1)."""
    return CodeState(
        (0, 1, 2),
        (Row("a1", "X", (0, 1)), Row("b1", "Z", (0, 1, 2))),
        frozenset(("a1", "b1")),
    )


class PeelRelationTests(unittest.TestCase):
    """The two §4.28 relations, checked against the exact oracle."""

    def check_relations(self, state, qubit, sector, row_id):
        opposite = "Z" if sector == "X" else "X"
        child = state.peel(qubit, sector, row_id)
        ex = exact_distances(state)
        ex_child = exact_distances(child)
        self.assertEqual(ex_child[sector], avoidance_minimum(state, sector, qubit))
        w_expose = exposure_price(state, opposite, qubit)
        expected = ex[opposite] if w_expose is None else min(ex[opposite], w_expose)
        self.assertEqual(ex_child[opposite], expected)
        self.assertGreaterEqual(ex_child[opposite], ex[opposite] - 1)
        self.assertLessEqual(ex_child[opposite], ex[opposite])
        self.assertGreaterEqual(ex_child[sector], ex[sector])
        return child, ex, ex_child

    def test_relations_on_the_peelable_state(self):
        child, ex, ex_child = self.check_relations(peelable(), 0, "Z", "b1")
        self.assertEqual((ex["X"], ex["Z"]), (2, 2))
        self.assertEqual((ex_child["X"], ex_child["Z"]), (1, 2))

    def test_relations_on_the_4_28_witness(self):
        child, ex, ex_child = self.check_relations(witness_of_4_28(), 2, "Z", "b1")
        self.assertEqual((ex["X"], ex["Z"]), (2, 1))
        self.assertEqual((ex_child["X"], ex_child["Z"]), (1, 2))

    def test_relations_on_every_peel_of_a_four_qubit_family(self):
        states = [
            peelable(),
            CodeState((0, 1, 2, 3),
                      (Row("a1", "X", (0, 1, 2)), Row("b1", "Z", (1, 2, 3))),
                      frozenset(("a1", "b1"))),
            CodeState((0, 1, 2, 3),
                      (Row("a1", "X", (0, 1)), Row("a2", "X", (2, 3)),
                       Row("b1", "Z", (0, 1, 2, 3))),
                      frozenset(("a1", "a2", "b1"))),
        ]
        checked = 0
        for state in states:
            for qubit in state.Q:
                for sector in ("X", "Z"):
                    touching = [row for row in state.sector_rows(sector) if qubit in row.support]
                    if len(touching) != 1:
                        continue
                    try:
                        self.check_relations(state, qubit, sector, touching[0].id)
                    except NoDerivation:
                        continue
                    checked += 1
        self.assertGreaterEqual(checked, 6)


class PeelLedgerTests(unittest.TestCase):
    def propagate(self, state, qubit, sector, row_id, hypothesis=None):
        ledger, ex = exact_ledger(state)
        child = state.peel(qubit, sector, row_id)
        out = ledger.propagate({"op": "E-PEEL", "qubit": qubit, "sector": sector,
                                "row_id": row_id}, child, hypothesis=hypothesis,
                               parent_state=state)
        return out, ex, exact_distances(child)

    def test_unpriced_bounds_on_the_4_28_witness(self):
        # Parent (d_X, d_Z) = (2, 1), peel q = 2 in Z: child (1, 2). The
        # opposite (X) lower carries less one, 2 - 1 = 1, and the full lower
        # is min(1, 1) = 1; both contain the child's exact values.
        out, ex, ex_child = self.propagate(witness_of_4_28(), 2, "Z", "b1")
        self.assertEqual(out.sector["Z"], Interval(1, None))
        self.assertEqual(out.sector["X"], Interval(1, 2))
        self.assertEqual(out.full, Interval(1, 2))
        self.assertEqual((ex_child["X"], ex_child["Z"], ex_child["d"]), (1, 2, 1))

    def test_unpriced_opposite_lower_floors_at_zero(self):
        state = witness_of_4_28()
        ledger = DistanceLedger(Interval(0, 2), {"X": Interval(0, 2), "Z": Interval(0, 1)},
                                witnesses={})
        child = state.peel(2, "Z", "b1")
        out = ledger.propagate({"op": "E-PEEL", "qubit": 2, "sector": "Z", "row_id": "b1"},
                               child, parent_state=state)
        self.assertEqual(out.sector["X"], Interval(0, 2))
        self.assertEqual(out.full, Interval(0, 2))

    def test_exposure_price_pins_the_opposite_sector(self):
        state = witness_of_4_28()
        w_expose = exposure_price(state, "X", 2)
        self.assertEqual(w_expose, 1)
        out, ex, ex_child = self.propagate(
            state, 2, "Z", "b1",
            hypothesis={"peel_price": {"w_expose": w_expose, "evidence": "test oracle"}})
        self.assertEqual(out.sector["X"], Interval(ex_child["X"], ex_child["X"]))
        self.assertEqual(out.sector["Z"], Interval(1, None))
        self.assertEqual(out.full, Interval(1, 1))
        self.assertTrue(any(c["cell"] == "E-PEEL price" and c["exposure_sector"] == "X"
                            for c in out.conditions))

    def test_avoidance_minimum_pins_the_selected_sector(self):
        state = witness_of_4_28()
        w_avoid = avoidance_minimum(state, "Z", 2)
        self.assertEqual(w_avoid, 2)
        out, ex, ex_child = self.propagate(
            state, 2, "Z", "b1",
            hypothesis={"peel_price": {"w_avoid": w_avoid, "evidence": "test oracle"}})
        self.assertEqual(out.sector["Z"], Interval(ex_child["Z"], ex_child["Z"]))
        self.assertEqual(out.sector["X"], Interval(1, 2))
        self.assertEqual(out.full, Interval(1, 2))

    def test_both_prices_give_the_exact_child_ledger(self):
        for state, qubit, sector, row_id in ((witness_of_4_28(), 2, "Z", "b1"),
                                             (peelable(), 0, "Z", "b1")):
            opposite = "Z" if sector == "X" else "X"
            price = {"w_expose": exposure_price(state, opposite, qubit),
                     "w_avoid": avoidance_minimum(state, sector, qubit),
                     "evidence": "test oracle"}
            out, ex, ex_child = self.propagate(state, qubit, sector, row_id,
                                               hypothesis={"peel_price": price})
            for side in ("X", "Z"):
                self.assertEqual(out.sector[side], Interval(ex_child[side], ex_child[side]))
            self.assertEqual(out.full, Interval(ex_child["d"], ex_child["d"]))

    def test_an_avoidance_minimum_below_the_carried_bound_is_refused(self):
        with self.assertRaises(NoDerivation):
            self.propagate(witness_of_4_28(), 2, "Z", "b1",
                           hypothesis={"peel_price": {"w_avoid": 0, "evidence": "x"}})
        with self.assertRaises(NoDerivation):
            self.propagate(peelable(), 0, "Z", "b1",
                           hypothesis={"peel_price": {"w_avoid": 1, "evidence": "x"}})

    def test_malformed_prices_are_refused(self):
        for price in ({"evidence": "x"}, {"w_expose": -1, "evidence": "x"},
                      {"w_expose": 1}, {"w_avoid": "2", "evidence": "x"}, "price"):
            with self.assertRaises(NoDerivation):
                self.propagate(witness_of_4_28(), 2, "Z", "b1",
                               hypothesis={"peel_price": price})

    def test_reset_mode_still_refuses_everything(self):
        state = witness_of_4_28()
        ledger, _ex = exact_ledger(state)
        child = state.peel(2, "Z", "b1")
        out = ledger.propagate({"op": "E-PEEL", "qubit": 2, "sector": "Z", "row_id": "b1"},
                               child, parent_state=state, lower_bound_mode="reset")
        self.assertEqual(out.full, Interval(0, None))
        self.assertEqual(out.sector["X"], Interval(0, None))
        self.assertEqual(out.sector["Z"], Interval(0, None))


class PunctureReductionTests(unittest.TestCase):
    """§4.29's recorded reduction: no unpriced direction, refusal kept."""

    def test_the_decrease_example(self):
        # Z rows {0,1} and {1,2}, no X row: d_X = 3 (the only X logical is
        # {0,1,2}). Puncturing qubit 2 drops the Z row {1,2}; the child's X
        # logical {0,1} has weight 2, so d_X falls 3 -> 2.
        state = CodeState((0, 1, 2), (Row("b1", "Z", (0, 1)), Row("b2", "Z", (1, 2))),
                          frozenset(("b1", "b2")))
        self.assertEqual(exact_distances(state)["X"], 3)
        child = state.puncture(2)
        self.assertEqual(exact_distances(child)["X"], 2)

    def test_the_increase_example_and_the_reset(self):
        state = CodeState((0, 1, 2), (Row("b1", "Z", (0, 1)),), frozenset(("b1",)))
        self.assertEqual(exact_distances(state)["X"], 1)
        child = state.puncture(2)
        self.assertEqual(exact_distances(child)["X"], 2)
        ledger, _ex = exact_ledger(state)
        out = ledger.propagate({"op": "E-PUNCTURE", "qubit": 2}, child, parent_state=state)
        self.assertEqual(out.full, Interval(0, None))
        self.assertEqual(out.sector["X"], Interval(0, None))

    def test_a_puncture_is_the_deletions_then_the_free_qubit_removal(self):
        # The child's sector distances are the lightest q-free logicals of
        # the intermediate code (every row touching q deleted): checked on
        # the decrease example and on the increase example.
        for state, q in ((CodeState((0, 1, 2), (Row("b1", "Z", (0, 1)), Row("b2", "Z", (1, 2))),
                                    frozenset(("b1", "b2"))), 2),
                         (CodeState((0, 1, 2), (Row("b1", "Z", (0, 1)),), frozenset(("b1",))), 2),
                         (peelable(), 0)):
            intermediate = state
            for row in state.rows:
                if q in row.support:
                    intermediate = intermediate.delete_check(row.id)
            child = state.puncture(q)
            ex_child = exact_distances(child)
            for side in ("X", "Z"):
                self.assertEqual(ex_child[side], avoidance_minimum(intermediate, side, q))


if __name__ == "__main__":
    unittest.main()
