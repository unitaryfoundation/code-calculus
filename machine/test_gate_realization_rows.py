"""Tests for the gate-realization judgment rows (issues #452, #543).

The harness checks the two rows of `spec/JUDGMENT_LAYER.md` §2h,
`spec/OPERATIONAL_SEMANTICS.md` §4.37, and `GATE_REALIZATION_ROWS.md`
against a state-vector oracle, and checks the consumer-side
`DistanceLedger.equal_syndrome_weight_floor` weakening transport.
"""

import math
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(HERE, "experiments"))

from gate_realization_rows import (  # noqa: E402
    Display,
    Pauli,
    addition_survival_verdict,
    conditioned_pauli,
    deletion_instance,
    equal_syndrome,
    exact_distance,
    in_stabilizer,
    mask,
    nontrivial,
    oracle_preserves,
    pauli_from_string,
    preserves_pi4,
    shor_display,
    shor_weakening_instance,
    survives_addition,
    sweep,
    w_max,
    weight_floor,
)
from machine.intervals import DistanceLedger, Interval  # noqa: E402
from machine.state import CodeState, Row  # noqa: E402

QUARTER = math.pi / 4


class PauliAlgebra(unittest.TestCase):
    def test_y_is_hermitian_and_squares_to_identity(self):
        y = pauli_from_string("Y")
        self.assertTrue(y.is_hermitian())
        self.assertEqual(y * y, Pauli(0, 0, 0))

    def test_xz_product_phase(self):
        # X Z = -i Y, the sign lemma of ROADMAP.md.
        x, z, y = (pauli_from_string(s) for s in "XZY")
        self.assertEqual(x * z, y.scaled(3))

    def test_css_product_on_four_shared_qubits(self):
        # X^4 Z^4 = +Y^4: an overlap of four contributes (-i)^4 = 1.
        display = Display.from_supports(4, [[0, 1, 2, 3]], [[0, 1, 2, 3]])
        self.assertTrue(in_stabilizer(display, pauli_from_string("YYYY")))
        self.assertFalse(in_stabilizer(display, pauli_from_string("YYYY", sign=-1)))


class SurvivalRow(unittest.TestCase):
    def test_sign_condition_decides_preservation(self):
        display = Display.from_supports(2, [[0, 1]], [[0, 1]])
        gens = [pauli_from_string("XI"), pauli_from_string("IX")]
        for eps, expected in (([1, -1], True), ([1, 1], False)):
            self.assertEqual(preserves_pi4(display, gens, eps), expected)
            self.assertEqual(oracle_preserves(display, gens, eps, [QUARTER] * 2), expected)

    def test_commuting_generators_survive_an_addition(self):
        # Logical X X on the two-qubit Z Z code survives adding the row X X.
        parent = Display.from_supports(2, [], [[0, 1]])
        gens, eps = [pauli_from_string("XX")], [1]
        self.assertTrue(preserves_pi4(parent, gens, eps))
        self.assertTrue(survives_addition(parent, gens, eps, "X", mask([0, 1])))
        child = parent.add("X", mask([0, 1]))
        self.assertTrue(oracle_preserves(child, gens, eps, [QUARTER]))

    def test_gate_refused_at_an_added_row(self):
        # exp(i pi/4 Z_0) preserves the Z Z code and fails at the added X X.
        parent = Display.from_supports(2, [], [[0, 1]])
        gens, eps = [pauli_from_string("ZI")], [1]
        self.assertTrue(preserves_pi4(parent, gens, eps))
        self.assertFalse(survives_addition(parent, gens, eps, "X", mask([0, 1])))
        child = parent.add("X", mask([0, 1]))
        self.assertFalse(oracle_preserves(child, gens, eps, [QUARTER]))
        self.assertEqual(
            conditioned_pauli(gens, eps, Pauli(mask([0, 1]), 0)), pauli_from_string("ZI").scaled(1)
        )

    def test_deletion_does_not_carry_the_gate(self):
        parent, child, gens, eps = deletion_instance()
        self.assertTrue(oracle_preserves(parent, gens, eps, [QUARTER] * 2))
        self.assertTrue(preserves_pi4(parent, gens, eps))
        self.assertFalse(oracle_preserves(child, gens, eps, [QUARTER] * 2))
        self.assertFalse(preserves_pi4(child, gens, eps))

    def test_three_branch_addition_verdict_and_from_code_state(self):
        state = CodeState(
            Q=(0, 1),
            rows=(Row("b1", "Z", (0, 1)),),
            used=frozenset({"b1"}),
        )
        parent = Display.from_code_state(state)
        # Branch 1: commuting generator carries at any angle.
        self.assertEqual(
            addition_survival_verdict(
                parent, [pauli_from_string("XX")], [1], "X", mask([0, 1]), thetas=[math.pi / 7]
            ),
            "carries",
        )
        # Branch 2: anticommuting generator at pi/4 is decided by V_s in S(C').
        self.assertEqual(
            addition_survival_verdict(
                parent,
                [pauli_from_string("ZI"), pauli_from_string("IZ")],
                [1, -1],
                "X",
                mask([0, 1]),
                thetas=[QUARTER, QUARTER],
            ),
            "carries",
        )
        self.assertEqual(
            addition_survival_verdict(
                parent, [pauli_from_string("ZI")], [1], "X", mask([0, 1]), thetas=[QUARTER]
            ),
            "does_not_carry",
        )
        # Branch 3: anticommuting generator at angle != pi/4 is not yet defined.
        self.assertEqual(
            addition_survival_verdict(
                parent, [pauli_from_string("ZI")], [1], "X", mask([0, 1]), thetas=[math.pi / 8]
            ),
            "not_yet_defined",
        )
        # Invalid sector, non-commuting check, or dependent check is rejected.
        with self.assertRaises(ValueError):
            addition_survival_verdict(parent, [pauli_from_string("XX")], [1], "Y", mask([0, 1]))
        with self.assertRaises(ValueError):
            addition_survival_verdict(parent, [pauli_from_string("XX")], [1], "X", mask([0]))
        with self.assertRaises(ValueError):
            addition_survival_verdict(parent, [pauli_from_string("XX")], [1], "Z", mask([0, 1]))
        with self.assertRaises(ValueError):
            addition_survival_verdict(
                parent, [pauli_from_string("XX")], [1], "X", mask([0, 1]), thetas=[-0.1]
            )


class WeightRow(unittest.TestCase):
    def test_shor_distance(self):
        self.assertEqual(exact_distance(shor_display()), 3)

    def test_parent_bound_is_not_the_childs(self):
        parent, child, gens = shor_weakening_instance()
        d_parent, d_child = exact_distance(parent), exact_distance(child)
        self.assertEqual((d_parent, d_child), (3, 1))
        self.assertTrue(equal_syndrome(child, gens))
        self.assertTrue(nontrivial(child, gens))
        # The child's own bound holds and is met with equality.
        self.assertEqual(w_max(gens), weight_floor(d_child))
        # The parent's value does not transport.
        self.assertLess(w_max(gens), weight_floor(d_parent))
        # The pair is a codespace-preserving gate of the child at pi/2.
        self.assertTrue(oracle_preserves(child, gens, [1, 1], [math.pi / 2] * 2))
        # In the parent the pair does not have a common syndrome.
        self.assertFalse(equal_syndrome(parent, gens))

    def test_ledger_weakening_transport_across_transitions(self):
        state = CodeState(
            Q=(0, 1, 2, 3),
            rows=(Row("a1", "X", (0, 1, 2, 3)), Row("b1", "Z", (0, 1))),
            used=frozenset({"a1", "b1"}),
        )
        ledger = DistanceLedger(
            Interval(3, 3),
            {"X": Interval(3, 3), "Z": Interval(3, 3)},
        )
        self.assertEqual(ledger.equal_syndrome_weight_floor(), 2)
        # C-SKIP keeps L_d = 3 and floor = 2.
        after_skip = ledger.propagate({"op": "C-SKIP"}, state.skip(), parent_state=state)
        self.assertEqual(after_skip.equal_syndrome_weight_floor(), 2)
        # C-ADD-CHECK with k' = 1 > 0 carries L_d >= 3 and floor >= 2.
        added_state = state.add_check("Z", (1, 2))
        after_add = ledger.propagate(
            {"op": "C-ADD-CHECK", "sector": "Z", "support": [1, 2]},
            added_state,
            parent_state=state,
        )
        self.assertEqual(after_add.equal_syndrome_weight_floor(), 2)
        # C-ADD-CHECK reaching k'' = 0 sets L_d = None (+inf), so floor is None (+inf).
        zero_k_state = added_state.add_check("Z", (2, 3))
        after_zero_k = after_add.propagate(
            {"op": "C-ADD-CHECK", "sector": "Z", "support": [2, 3]},
            zero_k_state,
            parent_state=added_state,
        )
        self.assertIsNone(after_zero_k.equal_syndrome_weight_floor())
        # Unpriced C-DELETE-CHECK resets L_d to 0, so the floor weakens to 0.
        deleted_state = state.delete_check("b1")
        after_unpriced_del = ledger.propagate(
            {"op": "C-DELETE-CHECK", "id": "b1"},
            deleted_state,
            parent_state=state,
        )
        self.assertEqual(after_unpriced_del.equal_syndrome_weight_floor(), 0)
        # Priced C-DELETE-CHECK with min(w_del, w_exp) = 1 moves L_d to 1 and floor to ceil(1/2) = 1.
        after_priced_del = ledger.propagate(
            {"op": "C-DELETE-CHECK", "id": "b1"},
            deleted_state,
            hypothesis={"deletion_price": {"w_del": 2, "w_exp": 1, "evidence": "shor-test"}},
            parent_state=state,
        )
        self.assertEqual(after_priced_del.equal_syndrome_weight_floor(), 1)


class Sweep(unittest.TestCase):
    def test_no_disagreement(self):
        stats = sweep(seed=452, trials=300, max_n=4)
        self.assertEqual(stats["disagreements"], [])
        for key in (
            "preserving",
            "not_preserving",
            "survives",
            "does_not_survive",
            "commuting_any_angle_checked",
            "deletion_not_carried",
            "weight_checked",
        ):
            self.assertGreater(stats[key], 0, key)


if __name__ == "__main__":
    unittest.main()
