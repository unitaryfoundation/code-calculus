import unittest

from machine.priced_calculus import CodeState, Interval, Malformed, NoDerivation, Row
from machine.symplectic_calculus import (
    SymplecticLedger,
    SymplecticRow,
    SymplecticState,
    apply_symplectic_operation,
    is_css,
    validate_pauli_witness,
)


def five_qubit_code():
    """The [[5,1,3]] code: XZZXI and its cyclic shifts."""
    return SymplecticState(
        (0, 1, 2, 3, 4),
        (SymplecticRow("a1", (0, 3), (1, 2)),
         SymplecticRow("a2", (1, 4), (2, 3)),
         SymplecticRow("a3", (0, 2), (3, 4)),
         SymplecticRow("a4", (1, 3), (0, 4))),
    )


class SymplecticStateTests(unittest.TestCase):
    def test_validates_a_non_css_stabilizer_code(self):
        # A non-CSS stabilizer code: single check X0 Z1 (mixed).
        # n=2, one check -> k=1. Orthogonality trivial (one row).
        st = SymplecticState((0, 1), (SymplecticRow("a1", (0,), (1,)),))
        st.validate()
        self.assertEqual(st.n(), 2)
        self.assertEqual(st.k(), 1)
        self.assertEqual(st.w(), 2)

    def test_five_qubit_code_validates_with_k_one(self):
        st = five_qubit_code()
        st.validate()
        self.assertFalse(is_css(st))
        self.assertEqual((st.n(), st.k(), st.w()), (5, 1, 4))

    def test_rejects_non_commuting_rows(self):
        rows = (
            SymplecticRow("a1", (0,), ()),
            SymplecticRow("a2", (), (0,)),
        )
        st = SymplecticState((0,), rows)
        with self.assertRaises(ValueError):
            st.validate()

    def test_rejects_dependent_rows(self):
        rows = (
            SymplecticRow("a1", (0, 1), ()),
            SymplecticRow("a2", (0, 1), ()),
        )
        st = SymplecticState((0, 1), rows)
        with self.assertRaises(ValueError):
            st.validate()

    def test_rejects_identifiers_outside_the_enumeration(self):
        st = SymplecticState((0, 1), (SymplecticRow("s1", (0,), (1,)),))
        with self.assertRaises(ValueError):
            st.validate()

    def test_weight_counts_a_y_once(self):
        st = SymplecticState((0, 1), (SymplecticRow("a1", (0, 1), (0, 1)),))
        st.validate()
        self.assertEqual(st.w(), 2)

    def test_css_round_trip(self):
        css = CodeState(
            (0, 1, 2),
            (Row("a1", "X", (0, 1)), Row("b1", "Z", (0, 1))),
            frozenset(("a1", "b1")),
        )
        sym = SymplecticState.from_css(css)
        sym.validate()
        self.assertTrue(is_css(sym))
        back = sym.to_css()
        self.assertEqual(back.Q, css.Q)
        self.assertEqual(sorted(r.id for r in back.rows),
                         sorted(r.id for r in css.rows))
        self.assertEqual(back.k(), css.k())

    def test_non_css_is_not_css(self):
        st = SymplecticState((0, 1), (SymplecticRow("a1", (0,), (1,)),))
        self.assertFalse(is_css(st))

    def test_k_for_trivial_code(self):
        st = SymplecticState((0, 1, 2), ())
        st.validate()
        self.assertEqual(st.k(), 3)

    def test_vectors_use_labels_not_positions(self):
        # Labels 0 and 2 with n = 2: a Z on label 0 must not collide with an
        # X on label 2 in the packed vector.
        st = SymplecticState((0, 2), (SymplecticRow("a1", (2,), ()),
                                      SymplecticRow("a2", (), (0,))))
        st.validate()
        self.assertEqual(st.k(), 0)


class SymplecticMoveTests(unittest.TestCase):
    def test_delete_retires_the_identifier(self):
        st = five_qubit_code()
        child = st.delete_check("a1")
        self.assertEqual([r.id for r in child.rows], ["a2", "a3", "a4"])
        self.assertEqual(child.used, st.used)
        self.assertEqual(child.k(), 2)
        with self.assertRaises(NoDerivation):
            st.delete_check("a9")

    def test_add_mints_canonically_and_checks_premises(self):
        st = five_qubit_code()
        child = st.delete_check("a1").add_check((0, 3), (1, 2))
        self.assertEqual(child.rows[-1].id, "a5")
        self.assertEqual(child.k(), 1)
        with self.assertRaises(NoDerivation):
            st.add_check((0,), ())          # anticommutes with a4
        with self.assertRaises(NoDerivation):
            st.add_check((0, 3), (1, 2))    # already displayed
        with self.assertRaises(NoDerivation):
            st.add_check((), ())            # identity
        with self.assertRaises(NoDerivation):
            st.add_check((7,), ())          # outside Q
        with self.assertRaises(Malformed):
            st.add_check((0, 0), ())        # repeated label

    def test_direct_sum_requires_disjoint_factors(self):
        st = five_qubit_code()
        other = SymplecticState((5, 6), (SymplecticRow("b1", (5, 6), ()),))
        total = SymplecticState.direct_sum(st, other)
        self.assertEqual((total.n(), total.k()), (7, 2))
        with self.assertRaises(NoDerivation):
            SymplecticState.direct_sum(st, st)
        clash = SymplecticState((5, 6), (SymplecticRow("a1", (5, 6), ()),))
        with self.assertRaises(NoDerivation):
            SymplecticState.direct_sum(st, clash)

    def test_double_gives_a_css_code_with_doubled_parameters(self):
        st = five_qubit_code()
        css = st.double()
        css.validate()
        self.assertEqual((css.n(), css.k()), (10, 2))
        self.assertEqual([r.sector for r in css.rows], ["X"] * 4 + ["Z"] * 4)
        self.assertEqual(css.rows[0].support, (0, 3, 6, 7))
        self.assertEqual(css.rows[4].support, (1, 2, 5, 8))
        self.assertTrue(st.used <= css.used)

    def test_halve_of_double_returns_the_code(self):
        st = five_qubit_code()
        css = st.double()
        back = SymplecticState.halve(css, st.doubling_pairs())
        self.assertEqual(back.Q, st.Q)
        self.assertEqual([(r.x, r.z) for r in back.rows],
                         [(r.x, r.z) for r in st.rows])
        self.assertEqual(back.k(), st.k())

    def test_halve_four_two_two(self):
        css = CodeState((0, 1, 2, 3),
                        (Row("a1", "X", (0, 1, 2, 3)), Row("b1", "Z", (0, 1, 2, 3))),
                        frozenset(("a1", "b1")))
        folded = SymplecticState.halve(css, [(0, 1), (2, 3)])
        self.assertEqual(folded.Q, (0, 2))
        self.assertEqual([(r.x, r.z) for r in folded.rows], [((0, 2), (0, 2))])
        self.assertEqual(folded.k(), 1)

    def test_halve_checks_the_involution(self):
        css = CodeState((0, 1, 2, 3),
                        (Row("a1", "X", (0, 1)), Row("b1", "Z", (0, 1, 2, 3))),
                        frozenset(("a1", "b1")))
        with self.assertRaises(NoDerivation):
            SymplecticState.halve(css, [(0, 1), (2, 3)])   # pi(S_X) != S_Z
        good = CodeState((0, 1, 2, 3),
                         (Row("a1", "X", (0, 1, 2, 3)), Row("b1", "Z", (0, 1, 2, 3))),
                         frozenset(("a1", "b1")))
        with self.assertRaises(NoDerivation):
            SymplecticState.halve(good, [(0, 0), (1, 2)])  # fixed point
        with self.assertRaises(NoDerivation):
            SymplecticState.halve(good, [(0, 1)])          # does not cover Q
        with self.assertRaises(Malformed):
            SymplecticState.halve(good, "01,23")

    def test_dispatch(self):
        st = five_qubit_code()
        self.assertIs(apply_symplectic_operation(st, {"op": "SYM-SKIP"}), st)
        self.assertEqual(
            apply_symplectic_operation(st, {"op": "SYM-DELETE-CHECK", "row_id": "a2"}).k(), 2)
        with self.assertRaises(Malformed):
            apply_symplectic_operation(st, {"op": "C-ADD-CHECK"})


class SymplecticLedgerTests(unittest.TestCase):
    def test_witness_validation(self):
        st = five_qubit_code()
        self.assertTrue(validate_pauli_witness(st, (0,), (0, 2, 3), 3))  # Y0 Z2 Z3
        with self.assertRaises(NoDerivation):
            validate_pauli_witness(st, (0,), (), 1)        # anticommutes with a4
        with self.assertRaises(NoDerivation):
            validate_pauli_witness(st, (0, 1, 2), (), 3)   # anticommutes with a2
        with self.assertRaises(NoDerivation):
            validate_pauli_witness(st, (0, 3), (1, 2), 4)  # in the span
        with self.assertRaises(NoDerivation):
            validate_pauli_witness(st, (0,), (0, 2, 3), 4) # wrong weight

    def test_add_carries_lower_and_rebuilds_upper(self):
        st = SymplecticState((0, 1), (SymplecticRow("a1", (0, 1), (0, 1)),))
        ledger = SymplecticLedger(Interval(2, 2))
        ledger.record_witness(st, (0, 1), ())
        child = st.add_check((0, 1), ())
        out = ledger.propagate({"op": "SYM-ADD-CHECK"}, child)
        self.assertEqual((out.full.lower, out.full.upper), (2, None))

    def test_delete_resets_lower_and_carries_upper(self):
        st = five_qubit_code()
        ledger = SymplecticLedger(Interval(3, 3))
        out = ledger.propagate({"op": "SYM-DELETE-CHECK"}, st.delete_check("a1"))
        self.assertEqual((out.full.lower, out.full.upper), (0, 3))

    def test_child_valid_witness_tightens_never_widens(self):
        st = five_qubit_code()
        ledger = SymplecticLedger(Interval(3, 3))
        ledger.record_witness(st, (0,), (0, 2, 3))
        child = st.delete_check("a1")
        out = ledger.propagate({"op": "SYM-DELETE-CHECK"}, child)
        self.assertLessEqual(out.full.upper, 3)

    def test_direct_sum_takes_minima(self):
        left = SymplecticLedger(Interval(3, 3))
        right = SymplecticLedger(Interval(1, 2))
        out = SymplecticLedger.direct_sum(left, right)
        self.assertEqual((out.full.lower, out.full.upper), (1, 2))

    def test_double_maps_to_twice_the_upper_endpoint(self):
        st = five_qubit_code()
        ledger = SymplecticLedger(Interval(3, 3))
        css = st.double()
        out = ledger.double(st, css)
        self.assertEqual((out.full.lower, out.full.upper), (3, 6))
        for side in ("X", "Z"):
            self.assertEqual((out.sector[side].lower, out.sector[side].upper), (3, 6))

    def test_double_converts_witnesses(self):
        st = five_qubit_code()
        ledger = SymplecticLedger(Interval(3, 3))
        ledger.record_witness(st, (0,), (0, 2, 3))
        css = st.double()
        out = ledger.double(st, css)
        self.assertEqual(out.witnesses["X"][0]["support"], [0, 5, 7, 8])
        self.assertEqual(out.witnesses["Z"][0]["support"], [0, 2, 3, 5])
        self.assertEqual((out.full.lower, out.full.upper), (3, 4))

    def test_halve_maps_to_half_the_lower_endpoint(self):
        css = CodeState((0, 1, 2, 3),
                        (Row("a1", "X", (0, 1, 2, 3)), Row("b1", "Z", (0, 1, 2, 3))),
                        frozenset(("a1", "b1")))
        pairs = [(0, 1), (2, 3)]
        folded = SymplecticState.halve(css, pairs)
        parent = __import__("machine.priced_calculus", fromlist=["DistanceLedger"]).DistanceLedger(
            Interval(2, 2), {"X": Interval(2, 2), "Z": Interval(2, 2)}, {"X": [], "Z": []}, [])
        out = SymplecticLedger.halve(parent, css, folded, pairs)
        self.assertEqual((out.full.lower, out.full.upper), (1, 2))

    def test_decide(self):
        ledger = SymplecticLedger(Interval(2, 4))
        self.assertEqual(ledger.decide(2), "certify")
        self.assertEqual(ledger.decide(5), "prune")
        self.assertEqual(ledger.decide(3), "re-measure")


if __name__ == "__main__":
    unittest.main()
