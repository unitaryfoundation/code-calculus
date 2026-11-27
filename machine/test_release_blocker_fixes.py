"""Regression tests for consumer soundness and boundary fixes."""

import unittest

from machine.css_preserving_cnot_swap import validate_u
from machine.entrypoints import strict_improvement_d1_feasible
from machine.intervals import DistanceLedger, Interval
from machine.layout import export_challenge_entry
from machine.priced_calculus import (
    CodeState,
    Malformed,
    NoDerivation,
    Row,
    apply_operation,
    construct,
    free_code,
)
from machine.symplectic_calculus import SymplecticLedger, SymplecticRow, SymplecticState


class ConsumerSoundnessRegressionTests(unittest.TestCase):
    def test_l_hgp_conditional_cell_requires_all_four_keys(self):
        state = construct({"constructor": "L-HGP", "H1": [[1, 1]], "H2": [[1, 1]]})["state"]
        with self.assertRaises(Malformed):
            DistanceLedger.for_constructed(
                state,
                constructor_cell={"constructor": "L-HGP", "d2": 5, "d2_T": 5, "source": "s"},
            )
        # Explicit None / "inf" is still accepted when all four keys are given.
        ledger = DistanceLedger.for_constructed(
            state,
            constructor_cell={
                "constructor": "L-HGP",
                "d1": None,
                "d1_T": 2,
                "d2": "inf",
                "d2_T": 2,
                "source": "explicit inf",
            },
        )
        self.assertEqual(ledger.sector["X"].lower, 2)
        self.assertEqual(ledger.sector["Z"].lower, 2)

    def test_symplectic_delete_from_k0_resets_lower_to_zero_and_decide_validates_target(self):
        # 1-qubit stabilizer state with 1 Z check -> k = 0, distance +inf.
        parent = SymplecticState((0,), (SymplecticRow("a1", (), (0,)),), frozenset({"a1"}))
        child = parent.delete_check("a1")
        ledger = SymplecticLedger(Interval(None, None))
        child_ledger = ledger.propagate({"op": "SYM-DELETE-CHECK", "row_id": "a1"}, child)
        self.assertEqual(child_ledger.full, Interval(0, None))
        self.assertEqual(child_ledger.decide(100), "re-measure")
        with self.assertRaises(Malformed):
            child_ledger.decide(0)
        with self.assertRaises(Malformed):
            child_ledger.decide(-5)

    def test_strict_improvement_d1_checks_same_sector_weight1_logicals(self):
        # 2 free qubits, adding X(0, 1): opposite-sector (Z) bare qubits are
        # all killed, but X(0) and X(1) are still weight-1 X-logicals in child.
        state = CodeState((0, 1), (), frozenset())
        res = strict_improvement_d1_feasible(
            state, [0, 1], "X", witnesses={"Z": [[0]]}, allow_enumeration=False
        )
        self.assertFalse(res["discharged"])

    def test_export_challenge_entry_with_trials_does_not_crash(self):
        state = CodeState(
            (0, 1, 2, 3),
            (
                Row("a1", "X", (0, 1, 2, 3)),
                Row("b1", "Z", (0, 1, 2, 3)),
            ),
            frozenset({"a1", "b1"}),
        )
        ledger = DistanceLedger.for_constructed(
            state,
            witnesses={"X": [[0, 1]], "Z": [[0, 2]]},
        )
        doc = export_challenge_entry(
            {"provenance": {}}, state, ledger, "[[4,2,2]]", "test", "2026-11-24", trials=100
        )
        self.assertIn("screened", doc["distance"]["X"]["confidence"])
        self.assertEqual(doc["distance"]["X"]["witness_confidence"], "screened")

    def test_for_constructed_synchronizes_full_and_sector_lowers(self):
        state = CodeState((0, 1, 2), (), frozenset())
        ledger = DistanceLedger.for_constructed(
            state,
            lower_bounds={
                "X": {"value": 3, "source": "x bound"},
                "Z": {"value": 4, "source": "z bound"},
            },
        )
        self.assertEqual(ledger.full.lower, 3)

    def test_construct_forwards_intervals_and_rejects_a_double_wiring_mismatch(self):
        s4 = CodeState(
            (0, 1, 2, 3),
            (Row("a1", "X", (0, 1, 2, 3)), Row("b1", "Z", (0, 1, 2, 3))),
            frozenset({"a1", "b1"}),
        )
        res = construct({
            "constructor": "L-FREE",
            "qubits": [0, 1],
            "intervals": {"d": {"lower": 1, "upper": 1, "source": "test interval"}},
        })
        self.assertEqual(res["ledger"].full, Interval(1, 1))
        with self.assertRaises(Malformed):
            construct({
                "constructor": "A-DOUBLE",
                "state": s4,
                "wiring": {"a1": [0], "b1": [0]},
                "constructor_cell": {
                    "constructor": "A-DOUBLE",
                    "wiring_empty": True,
                    "parent": {"X": 2, "Z": 2},
                    "source": "bad wiring flag",
                },
            })
        with self.assertRaises(NoDerivation):
            construct({
                "constructor": "A-DOUBLE",
                "state": s4,
                "wiring": {"a1": [0], "b1": [0]},
                "constructor_cell": {
                    "constructor": "A-DOUBLE",
                    "wiring_empty": False,
                    "d_X": 2,
                    "d_Z": 2,
                    "twisted_certificate": "   ",
                    "source": "blank cert",
                },
            })

    def test_free_code_and_witness_labels_reject_bad_types_as_malformed(self):
        with self.assertRaises(Malformed):
            free_code([0, "a"])
        state = free_code([0, 1])
        with self.assertRaises(Malformed):
            construct({
                "constructor": "L-FREE",
                "qubits": [0, 1],
                "witnesses": {"X": [[True]]},
            })
        with self.assertRaises(Malformed):
            DistanceLedger(Interval(0, None), {"X": Interval(0, None), "Z": Interval(0, None)}).propagate(
                {"op": "E-LOCAL-HADAMARD", "qubits": [True]}, state, parent_state=state
            )

    def test_validate_u_refuses_malformed_matrices(self):
        for bad in ([[1, 0, 0], [0, 1, 0]],  # not square
                    [1, 2],                   # rows are not lists
                    [[1.0]],                  # float entry
                    [[True]]):                # bool entry
            with self.assertRaises(ValueError, msg=repr(bad)):
                validate_u(bad)
        self.assertEqual(validate_u([[1, 1], [0, 1]]), [[1, 1], [0, 1]])

    def test_c_column_cnot_is_not_dispatched_by_the_consumer(self):
        # The command has no transcription in machine/*.json yet, so the
        # consumer does not execute it (review of this change, item 1).
        state = CodeState((0, 1), (Row("a1", "X", (0, 1)),), frozenset({"a1"}))
        u = [[1, 1], [0, 1]]
        with self.assertRaises(Malformed):
            apply_operation(state, {"op": "C-COLUMN-CNOT", "U": u})
        ledger = DistanceLedger(Interval(1, 2), {"X": Interval(1, 2), "Z": Interval(1, 2)})
        with self.assertRaises(Malformed):
            ledger.propagate({"op": "C-COLUMN-CNOT", "U": u}, state, parent_state=state)

    def test_sector_gauging_raises_lower_and_keeps_inf_at_k0(self):
        parent = CodeState(
            (0, 1, 2, 3),
            (Row("a1", "X", (0, 1, 2, 3)), Row("b1", "Z", (0, 1, 2, 3))),
            frozenset({"a1", "b1"}),
        )
        op = {"op": "C-ADD-CHECK", "sector": "Z", "support": [0, 1]}
        child = parent.add_check("Z", (0, 1))
        self.assertEqual(child.k(), 1)
        ledger = DistanceLedger(Interval(1, 2), {"X": Interval(1, 2), "Z": Interval(1, 2)})
        out = ledger.propagate(op, child, parent_state=parent, hypothesis={
            "sector_gauging": {"w_X": 2, "evidence": "test"}})
        self.assertEqual(out.sector["X"].lower, 2)
        self.assertEqual(out.sector["Z"].lower, 1)
        # Gauging the last logical: k' = 0, so every endpoint is +inf.
        small = CodeState((0, 1), (Row("a1", "X", (0, 1)),), frozenset({"a1"}))
        k0 = small.add_check("Z", (0, 1))
        self.assertEqual(k0.k(), 0)
        out = DistanceLedger(Interval(1, 2), {"X": Interval(2, 2), "Z": Interval(1, 1)}).propagate(
            {"op": "C-ADD-CHECK", "sector": "Z", "support": [0, 1]}, k0,
            parent_state=small,
            hypothesis={"sector_gauging": {"w_X": 1, "w_Z": 1, "evidence": "test"}})
        self.assertEqual(out.full, Interval(None, None))
        self.assertEqual(out.sector["X"], Interval(None, None))
        self.assertEqual(out.sector["Z"], Interval(None, None))

    def test_graft_and_peel_refuse_a_missing_sector(self):
        state = CodeState(
            (0, 1, 2, 3),
            (Row("a1", "X", (0, 1, 2, 3)), Row("b1", "Z", (0, 1, 2, 3))),
            frozenset({"a1", "b1"}),
        )
        ledger = DistanceLedger(Interval(2, 2), {"X": Interval(2, 2), "Z": Interval(2, 2)})
        for op in ({"op": "E-GRAFT", "qubit": 0, "ordered_row_ids": ["a1"]},
                   {"op": "E-GRAFT", "qubit": 0, "sector": "Y", "ordered_row_ids": ["a1"]},
                   {"op": "E-PEEL", "qubit": 0},
                   {"op": "E-PEEL", "qubit": 0, "sector": "Y"}):
            with self.assertRaises(Malformed, msg=repr(op)):
                ledger.propagate(op, state, parent_state=state)

    def test_direct_sum_extinction_full_interval_is_the_factor_distance(self):
        parent = CodeState(
            (0, 1, 2, 3, 4, 5),
            (Row("a9001", "X", (0, 1)),
             Row("a9002", "X", (2, 3, 4, 5)),
             Row("b9002", "Z", (2, 3, 4, 5))),
            frozenset(("a9001", "a9002", "b9002")),
        )
        child = parent.add_check("Z", (0, 1))
        op = {"op": "C-ADD-CHECK", "sector": "Z", "support": [0, 1]}
        hyp = {"direct_sum_extinction": {
            "base_distance": 1, "factor_distance": 2, "evidence": "test"}}
        ledger = DistanceLedger(Interval(1, 1), {"X": Interval(1, 1), "Z": Interval(1, 1)})
        # A heavier post-step witness does not widen the upper endpoint past d_B.
        out = ledger.propagate(op, child, parent_state=parent, hypothesis=hyp,
                               observations={"Z": [0, 1, 2, 3]})
        self.assertEqual(out.full, Interval(2, 2))

    def test_concat_cell_k_in_must_match_the_inner_code(self):
        outer = CodeState((0, 1), (Row("a1", "X", (0, 1)),), frozenset({"a1"}))
        inner = CodeState((0, 1, 2), (Row("b1", "Z", (0, 1)), Row("b2", "Z", (1, 2))),
                          frozenset({"b1", "b2"}))
        self.assertEqual(inner.k(), 1)
        spec = {"constructor": "A-CONCAT", "outer": outer, "inner": inner,
                "groups": [(0,), (1,)],
                "constructor_cell": {"constructor": "A-CONCAT", "k_in": 2,
                                     "outer": {"X": 1, "Z": 2},
                                     "inner": {"X": 3, "Z": 1},
                                     "source": "test"}}
        with self.assertRaisesRegex(Malformed, "k_in"):
            construct(spec)

    def test_a_double_cell_must_state_its_wiring(self):
        s4 = CodeState(
            (0, 1, 2, 3),
            (Row("a1", "X", (0, 1, 2, 3)), Row("b1", "Z", (0, 1, 2, 3))),
            frozenset({"a1", "b1"}),
        )
        with self.assertRaisesRegex(Malformed, "wiring"):
            construct({
                "constructor": "A-DOUBLE",
                "state": s4,
                "wiring": {"a1": [0], "b1": [0]},
                "constructor_cell": {"constructor": "A-DOUBLE", "d_X": 2, "d_Z": 2,
                                     "twisted_certificate": "cert", "source": "test"},
            })


if __name__ == "__main__":
    unittest.main()
