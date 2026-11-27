"""Tests for the gate-realization judgment rows (issues #452, #543, #572).

The harness checks the rows of `spec/JUDGMENT_LAYER.md` §2h,
`spec/OPERATIONAL_SEMANTICS.md` §4.37, and `GATE_REALIZATION_ROWS.md`
against a state-vector oracle, and checks the consumer-side
`DistanceLedger.equal_syndrome_weight_floor` weakening transport. Issue #572
adds the any-angle preservation test, the frame-reading predicates (frame
sector preservation, sector phase, conjugation image, addressability), and
their carry cells.
"""

import json
import math
import os
import sys
import unittest
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(HERE, "experiments"))

from gate_realization_rows import (  # noqa: E402
    Display,
    Pauli,
    StabilizerGroup,
    addition_frame_cell,
    addition_survival_verdict,
    addresses,
    conditioned_pauli,
    deletion_instance,
    direct_sum,
    entry_pauli,
    equal_syndrome,
    exact_distance,
    four_two_two_display,
    four_two_two_frame,
    frame_addition_instance,
    frame_consistent,
    frame_deletion_instance,
    frame_drop_instance,
    frame_refines,
    frame_well_formed,
    image_pi4,
    image_scalar,
    in_pi_z,
    in_stabilizer,
    mask,
    nontrivial,
    oracle_addresses,
    oracle_image,
    oracle_preserves,
    oracle_preserves_in_frame,
    oracle_sector_phase,
    pauli_from_string,
    phase_sum,
    preserves_any_angle,
    preserves_in_frame,
    preserves_pi4,
    radians,
    random_display,
    random_gate,
    realized_patterns,
    resolved_eigenvalues,
    root_of_unity,
    sector_phase,
    shift_frame,
    shor_display,
    shor_weakening_instance,
    subspace_vectors,
    survives_addition,
    survives_addition_any_angle,
    sweep,
    sweep_frames,
    theorem1_phase,
    transport_frame_add,
    w_max,
    weight_floor,
)
from machine.intervals import DistanceLedger, Interval  # noqa: E402
from machine.state import CodeState, Row  # noqa: E402

QUARTER = math.pi / 4
# Angles of the any-angle tests are rational multiples of pi (issue #572,
# review of PR #665): Q4 is pi/4 as a coefficient of pi.
Q4 = Fraction(1, 4)


def F(*args):
    return Fraction(*args)


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
        # Branch 3: anticommuting generator at an angle != pi/4 is decided by
        # the any-angle test at s for rational multiples of pi (issue #572);
        # radian angles are outside the decision domain.
        self.assertEqual(
            addition_survival_verdict(
                parent, [pauli_from_string("ZI")], [1], "X", mask([0, 1]), angles=[F(1, 8)]
            ),
            "does_not_carry",
        )
        self.assertEqual(
            addition_survival_verdict(
                parent,
                [pauli_from_string("ZI"), pauli_from_string("IZ")],
                [1, -1],
                "X",
                mask([0, 1]),
                angles=[F(1, 7), F(1, 7)],
            ),
            "carries",
        )
        self.assertEqual(
            addition_survival_verdict(
                parent, [pauli_from_string("ZI")], [1], "X", mask([0, 1]), thetas=[math.pi / 8]
            ),
            "not_yet_defined",
        )
        self.assertEqual(
            addition_survival_verdict(
                parent, [pauli_from_string("ZI")], [1], "X", mask([0, 1]), angles=[Q4]
            ),
            "does_not_carry",
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
        with self.assertRaises(ValueError):
            addition_survival_verdict(
                parent, [pauli_from_string("XX")], [1], "X", mask([0, 1]), angles=[F(-1, 10)]
            )
        with self.assertRaises(ValueError):
            addition_survival_verdict(
                parent, [pauli_from_string("XX")], [1], "X", mask([0, 1]), angles=[0.25]
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


class AnyAnglePreservation(unittest.TestCase):
    """Lemmas 5-8 of §4.37 (issue #572): the frame-free preservation test at
    every angle, and the `C-ADD-CHECK` cell it decides."""

    def test_lemma7_contains_lemma3(self):
        import random

        rng = random.Random(7)
        for _ in range(150):
            display = random_display(rng, rng.randrange(2, 5))
            gens, eps = random_gate(rng, display)
            self.assertEqual(
                preserves_any_angle(display, gens, eps, [Q4] * len(gens)),
                preserves_pi4(display, gens, eps),
            )

    def test_relation_protects_at_every_angle(self):
        # Rows XX, ZZ; X_0 X_1 in S(C) forces l_1 l_2 = +1 at the row ZZ, so
        # Phi = theta - theta = 0 for signs (+1, -1) at every angle.
        display = Display.from_supports(2, [[0, 1]], [[0, 1]])
        gens = [pauli_from_string("XI"), pauli_from_string("IX")]
        group = StabilizerGroup(display)
        self.assertEqual(sorted(realized_patterns(group, gens, [0, 1])), [(-1, -1), (1, 1)])
        for theta in (F(1, 7), F(3, 10), F(2, 3)):
            thetas = [theta, theta]
            self.assertTrue(preserves_any_angle(display, gens, [1, -1], thetas))
            self.assertTrue(oracle_preserves(display, gens, [1, -1], radians(thetas)))
            self.assertFalse(preserves_any_angle(display, gens, [1, 1], thetas))
            self.assertFalse(oracle_preserves(display, gens, [1, 1], radians(thetas)))

    def test_angle_domain_is_exact(self):
        # exp(i pi Z_0) = -I preserves the code with row X_0; an angle 1e-12
        # off pi does not, although a 1e-9 floating-point tolerance would
        # accept it (review of PR #665).
        display = Display.from_supports(1, [[0]], [])
        gens = [pauli_from_string("Z")]
        self.assertTrue(preserves_any_angle(display, gens, [1], [F(1)]))
        self.assertFalse(preserves_any_angle(display, gens, [1], [F(1) + F(1, 10**12)]))
        self.assertTrue(oracle_preserves(display, gens, [1], radians([F(1) + F(1, 10**12)])))
        # Radian floats are outside the decision domain and are refused.
        with self.assertRaises(ValueError):
            preserves_any_angle(display, gens, [1], [math.pi])

    def test_non_quarter_addition_cell(self):
        # Adding XX to the ZZ code under exp(i theta Z_0) exp(i eps_2 theta Z_1):
        # Z_0 Z_1 is in S(C'), so the realized patterns are +-(1, 1) and the
        # cell reads theta (1 + eps_2) in pi Z.
        parent = Display.from_supports(2, [], [[0, 1]])
        gens = [pauli_from_string("ZI"), pauli_from_string("IZ")]
        child = parent.add("X", mask([0, 1]))
        for eps, theta, expected in (
            ([1, -1], F(1, 7), True),
            ([1, 1], F(1, 7), False),
            ([1, 1], F(1, 2), True),
        ):
            thetas = [theta, theta]
            self.assertTrue(preserves_any_angle(parent, gens, eps, thetas))
            self.assertEqual(
                survives_addition_any_angle(parent, gens, eps, thetas, "X", mask([0, 1])), expected
            )
            self.assertEqual(oracle_preserves(child, gens, eps, radians(thetas)), expected)


class FrameReading(unittest.TestCase):
    """Lemma 8 and Rows C-F of §2h: frame consistency, frame-sector
    preservation, sector phase, conjugation image, and addressability."""

    def test_frame_consistency(self):
        display = four_two_two_display()
        frame = four_two_two_frame()
        self.assertTrue(frame_well_formed(display, frame))
        # X1 and Z1 anticommute (F1): no common eigenspace. (The oracle's
        # projections assume commuting entries, so it is not consulted here.)
        self.assertTrue(entry_pauli(frame[0]).anticommutes(entry_pauli(frame[1])))
        self.assertFalse(frame_consistent(display, frame))
        # Z1, Z2 commute; every eigenvalue choice gives a nonzero sector.
        for e1 in (1, -1):
            for e2 in (1, -1):
                zs = [("Z", mask([0, 2]), e1), ("Z", mask([0, 1]), e2)]
                self.assertTrue(frame_consistent(display, zs))
                self.assertTrue(subspace_vectors(display, zs))
        # Three Z entries whose sum is a row: their eigenvalues must multiply
        # to +1 (F2); W2 holds, since no two lie in one class.
        triple = [("Z", mask([0, 2]), 1), ("Z", mask([0, 1]), 1), ("Z", mask([0, 3]), -1)]
        self.assertTrue(frame_well_formed(display, triple))
        self.assertFalse(frame_consistent(display, triple))
        self.assertEqual(subspace_vectors(display, triple), [])
        triple[2] = ("Z", mask([0, 3]), 1)
        self.assertTrue(frame_consistent(display, triple))

    def test_eigenvalue_condition_in_a_frame(self):
        # The sector Z_0 Z_1 = eig of the child of adding X_0 X_1: the test
        # reads theta_1 + eig * theta_2 in pi Z (resolved form).
        for eig, theta, expected in (
            (1, F(1, 7), False),
            (1, F(1, 2), True),
            (-1, F(1, 7), True),
            (-1, F(1, 3), True),
        ):
            parent, sector, row, gens, eps, frame = frame_addition_instance(eig)
            child = parent.add(sector, row)
            thetas = [theta, theta]
            self.assertTrue(frame_consistent(child, frame))
            self.assertEqual(resolved_eigenvalues(child, frame, gens, [0, 1]), (1, eig))
            self.assertEqual(in_pi_z(phase_sum(eps, thetas, [0, 1], (1, eig))), expected)
            self.assertEqual(
                survives_addition_any_angle(parent, gens, eps, thetas, sector, row, frame), expected
            )
            self.assertEqual(preserves_in_frame(child, frame, gens, eps, thetas), expected)
            self.assertEqual(
                oracle_preserves_in_frame(child, frame, gens, eps, radians(thetas)), expected
            )
            # Frame-free, the child is preserved only when both sectors are.
            self.assertEqual(
                preserves_any_angle(child, gens, eps, thetas), in_pi_z(2 * theta)
            )

    def test_sector_phase_and_theorem1_form(self):
        # [[4,2,2]] with the equal-syndrome pair Z_0, Z_2 (product Z1-bar):
        # at pi/2 the gate is -Z_0 Z_2, the scalar -eig on the sector.
        display = four_two_two_display()
        gens = [pauli_from_string("ZIII"), pauli_from_string("IIZI")]
        self.assertTrue(equal_syndrome(display, gens))
        for eig in (1, -1):
            frame = [("Z", mask([0, 2]), eig)]
            # The scalar is named by r in [0, 2): z = exp(i r pi); -1 is r = 1.
            for theta, expected in ((F(1, 2), F(1) if eig == 1 else F(0)), (Q4, F(0) if eig == -1 else None)):
                thetas = [theta, theta]
                z = sector_phase(display, frame, gens, [1, 1], thetas)
                z_thm = theorem1_phase(display, frame, gens, [1, 1], thetas)
                z_oracle = oracle_sector_phase(display, frame, gens, [1, 1], radians(thetas))
                self.assertEqual(z, expected)
                self.assertEqual(z_thm, expected)
                if expected is None:
                    self.assertIsNone(z_oracle)
                else:
                    self.assertAlmostEqual(z_oracle, root_of_unity(expected))

    def test_conjugation_image(self):
        # exp(i pi/4 Z) is S^dagger up to phase: it conjugates X to Y.
        display = Display(1, [], [])
        gens, eps = [pauli_from_string("Z")], [1]
        x, y, z = (pauli_from_string(s) for s in "XYZ")
        self.assertTrue(image_pi4(display, gens, eps, x, y))
        self.assertTrue(oracle_image(display, gens, eps, [QUARTER], x, y))
        self.assertFalse(image_pi4(display, gens, eps, x, x))
        self.assertTrue(image_pi4(display, gens, eps, z, z))
        # At pi/2 the gate is i Z: X goes to -X at every such angle.
        self.assertTrue(image_scalar(display, gens, eps, [F(1, 2)], x, -1))
        self.assertTrue(oracle_image(display, gens, eps, [math.pi / 2], x, x.scaled(2)))
        self.assertFalse(image_scalar(display, gens, eps, [F(1, 3)], x, -1))
        self.assertFalse(image_scalar(display, gens, eps, [F(1, 3)], x, 1))

    def test_addressability(self):
        display = four_two_two_display()
        frame = four_two_two_frame()  # X1, Z1, X2, Z2
        z1 = [pauli_from_string("ZIZI")]  # the logical Z1-bar, at any angle
        for theta in (Q4, F(1, 8)):
            self.assertTrue(addresses(display, frame, {0, 1}, z1, [1], [theta]))
            self.assertTrue(oracle_addresses(display, frame, {0, 1}, z1, [1], radians([theta])))
            self.assertFalse(addresses(display, frame, {2, 3}, z1, [1], [theta]))
            self.assertFalse(oracle_addresses(display, frame, {2, 3}, z1, [1], radians([theta])))
        # Z1-bar Z2-bar = Z_1 Z_2 rotates both logical qubits.
        both = [pauli_from_string("IZZI")]
        self.assertFalse(addresses(display, frame, {0, 1}, both, [1], [Q4]))
        self.assertTrue(addresses(display, frame, {0, 1, 2, 3}, both, [1], [Q4]))


class FrameCarryCells(unittest.TestCase):
    """The carry cells of Rows C-F across the kernel (§2h, §4.37)."""

    def test_deletion_refutes_rows_c_to_f(self):
        parent, child, gens, eps, frame = frame_deletion_instance()
        q, rq = [Q4] * 2, [QUARTER] * 2
        z2 = entry_pauli(frame[0])
        self.assertTrue(preserves_in_frame(parent, frame, gens, eps, q))
        self.assertEqual(sector_phase(parent, frame, gens, eps, q), 0)
        self.assertTrue(image_pi4(parent, gens, eps, z2, z2))
        self.assertTrue(addresses(parent, frame, set(), gens, eps, q))
        self.assertTrue(frame_well_formed(child, frame))
        self.assertFalse(preserves_in_frame(child, frame, gens, eps, q))
        self.assertFalse(oracle_preserves_in_frame(child, frame, gens, eps, rq))
        self.assertIsNone(sector_phase(child, frame, gens, eps, q))
        self.assertIsNone(oracle_sector_phase(child, frame, gens, eps, rq))
        self.assertFalse(image_pi4(child, gens, eps, z2, z2))
        self.assertFalse(oracle_image(child, gens, eps, rq, z2, z2))
        self.assertFalse(addresses(child, frame, set(), gens, eps, q))

    def test_dropped_entry_refutes_addition_carry(self):
        parent, sector, row, gens, eps, frame = frame_drop_instance()
        child = parent.add(sector, row)
        child_frame = transport_frame_add(child, frame)
        self.assertEqual(child_frame, [])
        self.assertFalse(frame_refines(parent, frame, child, child_frame))
        self.assertTrue(preserves_in_frame(parent, frame, gens, eps, [Q4]))
        self.assertIsNotNone(sector_phase(parent, frame, gens, eps, [Q4]))
        self.assertTrue(addresses(parent, frame, {0}, gens, eps, [Q4]))
        self.assertFalse(preserves_in_frame(child, child_frame, gens, eps, [Q4]))
        self.assertIsNone(sector_phase(child, child_frame, gens, eps, [Q4]))
        self.assertFalse(addresses(child, child_frame, set(), gens, eps, [Q4]))
        # The split cell (review of PR #665): F' is consistent (empty) and the
        # inclusion fails, so the cell is refuted, not unstated.
        self.assertEqual(addition_frame_cell(parent, frame, gens, eps, [Q4], sector, row), "does_not_carry")

    def test_inconsistent_transported_frame_is_not_stated(self):
        # Three Z-entries on three free qubits whose sum becomes the added row
        # Z_0 Z_1 Z_2: the transport keeps all three (no two merge), and their
        # eigenvalues multiply to -1, so F' violates F2 on the child and Rows
        # C and D are not stated there: the cell is `not yet defined`.
        parent = Display(3, [], [])
        frame = [("Z", mask([0]), 1), ("Z", mask([1]), 1), ("Z", mask([2]), -1)]
        gens, eps = [pauli_from_string("XII")], [1]
        self.assertTrue(frame_consistent(parent, frame))
        child = parent.add("Z", mask([0, 1, 2]))
        child_frame = transport_frame_add(child, frame)
        self.assertEqual(child_frame, frame)
        self.assertFalse(frame_consistent(child, child_frame))
        self.assertEqual(subspace_vectors(child, child_frame), [])
        self.assertEqual(
            addition_frame_cell(parent, frame, gens, eps, [Q4], "Z", mask([0, 1, 2])),
            "not_yet_defined",
        )
        # With eigenvalues multiplying to +1 the frame stays consistent and the
        # cell is decided by the test at s.
        frame[2] = ("Z", mask([2]), 1)
        self.assertIn(
            addition_frame_cell(parent, frame, gens, eps, [Q4], "Z", mask([0, 1, 2])),
            ("carries", "does_not_carry"),
        )

    def test_refined_addition_carries_phase_and_survival(self):
        # Rows: Z_0 Z_1; frame Z_0 = -1, so Z_0 and Z_1 are both the scalar -1
        # on the sector. Adding Z_1 Z_2 keeps the entry, so S_F(C) lies in
        # S_F(C') and the sector phase exp(-1.3 i pi) carries unchanged.
        parent = Display.from_supports(3, [], [[0, 1]])
        frame = [("Z", mask([0]), -1)]
        gens, eps, thetas = [pauli_from_string("ZII"), pauli_from_string("IZI")], [1, 1], [F(2, 5), F(9, 10)]
        child = parent.add("Z", mask([1, 2]))
        child_frame = transport_frame_add(child, frame)
        self.assertEqual(child_frame, frame)
        self.assertTrue(frame_refines(parent, frame, child, child_frame))
        z = sector_phase(parent, frame, gens, eps, thetas)
        self.assertEqual(z, F(7, 10))  # -13/10 modulo 2
        self.assertEqual(sector_phase(child, child_frame, gens, eps, thetas), z)
        self.assertAlmostEqual(
            oracle_sector_phase(child, child_frame, gens, eps, radians(thetas)), root_of_unity(z)
        )
        self.assertTrue(
            survives_addition_any_angle(parent, gens, eps, thetas, "Z", mask([1, 2]), child_frame)
        )
        self.assertEqual(
            addition_frame_cell(parent, frame, gens, eps, thetas, "Z", mask([1, 2])), "carries"
        )

    def test_direct_sum_carries(self):
        parent, sector, row, gens, eps, frame = frame_addition_instance(-1)
        a = parent.add(sector, row)
        b = Display.from_supports(2, [[0, 1]], [])
        b_frame = [("Z", mask([0, 1]), 1)]
        total = direct_sum(a, b)
        total_frame = frame + shift_frame(b_frame, a.n)
        wide = [Pauli(g.x, g.z, g.k) for g in gens]  # supported on summand A
        thetas = [F(1, 3), F(1, 3)]
        self.assertTrue(frame_consistent(total, total_frame))
        self.assertTrue(preserves_in_frame(a, frame, gens, eps, thetas))
        self.assertTrue(preserves_in_frame(total, total_frame, wide, eps, thetas))
        self.assertEqual(
            sector_phase(total, total_frame, wide, eps, thetas),
            sector_phase(a, frame, gens, eps, thetas),
        )
        self.assertAlmostEqual(
            oracle_sector_phase(total, total_frame, wide, eps, radians(thetas)),
            root_of_unity(sector_phase(a, frame, gens, eps, thetas)),
        )
        # Rows E and F on C_1 + C_2: an entry of summand C_2 has image f_e, and
        # addressability carries for A <= F_1.
        a4 = four_two_two_display()
        a4_frame = four_two_two_frame()
        total4 = direct_sum(a4, b)
        total4_frame = a4_frame + shift_frame(b_frame, a4.n)
        z1_wide = [pauli_from_string("ZIZIII")]
        self.assertTrue(addresses(a4, a4_frame, {0, 1}, [pauli_from_string("ZIZI")], [1], [F(1, 8)]))
        self.assertTrue(addresses(total4, total4_frame, {0, 1}, z1_wide, [1], [F(1, 8)]))
        self.assertTrue(oracle_addresses(total4, total4_frame, {0, 1}, z1_wide, [1], [math.pi / 8]))
        b_entry = entry_pauli(total4_frame[4])
        self.assertTrue(image_scalar(total4, z1_wide, [1], [F(1, 8)], b_entry, 1))
        self.assertTrue(oracle_image(total4, z1_wide, [1], [math.pi / 8], b_entry, b_entry))

    def test_addition_carries_rows_e_and_f_and_refinement_edge_cases(self):
        # Rows E and F under C-ADD-CHECK on [[4,2,2]]: adding Z_0 Z_1 fixes the
        # second logical qubit and drops X2 = X_0 X_2 (anticommutes) and Z2 = Z_0 Z_1
        # (absorbed into span), keeping X1 = X_0 X_1 and Z1 = Z_0 Z_2.
        parent = four_two_two_display()
        frame = four_two_two_frame()  # X1, Z1, X2, Z2
        child = parent.add("Z", mask([0, 1]))
        child_frame = transport_frame_add(child, frame)
        self.assertEqual(child_frame, frame[:2])
        # Gate exp(i theta Z_0 Z_2) commutes with Z_0 Z_1, so Row A carries and
        # Row E/F carry on the kept entries.
        z1 = [pauli_from_string("ZIZI")]
        self.assertTrue(addresses(parent, frame, {0, 1}, z1, [1], [F(1, 8)]))
        self.assertTrue(addresses(child, child_frame, {0, 1}, z1, [1], [F(1, 8)]))
        self.assertTrue(oracle_addresses(child, child_frame, {0, 1}, z1, [1], [math.pi / 8]))
        self.assertTrue(image_scalar(child, z1, [1], [F(1, 8)], entry_pauli(child_frame[1]), 1))
        # Absorbed entry with eigenvalue +1 preserves S_F(C) <= S_{F'}(C'), while
        # eigenvalue -1 breaks it.
        f_plus = [("Z", mask([0, 1]), 1)]
        f_minus = [("Z", mask([0, 1]), -1)]
        self.assertEqual(transport_frame_add(child, f_plus), [])
        self.assertTrue(frame_refines(parent, f_plus, child, []))
        self.assertFalse(frame_refines(parent, f_minus, child, []))
        # Merged entries with agreeing eigenvalues preserve inclusion; disagreeing break it.
        # Adding Z_0 Z_1 merges Z_0 Z_2 and Z_1 Z_2 (their sum is Z_0 Z_1).
        merged_agree = [("Z", mask([0, 2]), -1), ("Z", mask([1, 2]), -1)]
        merged_disagree = [("Z", mask([0, 2]), 1), ("Z", mask([1, 2]), -1)]
        self.assertTrue(frame_well_formed(parent, merged_agree))
        self.assertTrue(frame_consistent(parent, merged_agree))
        self.assertTrue(frame_consistent(parent, merged_disagree))
        self.assertTrue(
            frame_refines(parent, merged_agree, child, transport_frame_add(child, merged_agree))
        )
        self.assertFalse(
            frame_refines(
                parent, merged_disagree, child, transport_frame_add(child, merged_disagree)
            )
        )

    def test_sequence_and_frame_validation_edges(self):
        # Two-step C-SEQUENCE of C-ADD-CHECK preserves Rows C-F by composition.
        d0 = Display(3, [], [])
        f0 = [("Z", mask([0]), -1)]
        gens, eps, thetas = [pauli_from_string("ZII"), pauli_from_string("IZI")], [1, 1], [F(2, 5), F(9, 10)]
        d1 = d0.add("Z", mask([0, 1]))
        f1 = transport_frame_add(d1, f0)
        d2 = d1.add("Z", mask([1, 2]))
        f2 = transport_frame_add(d2, f1)
        self.assertTrue(frame_refines(d0, f0, d1, f1))
        self.assertTrue(frame_refines(d1, f1, d2, f2))
        self.assertTrue(preserves_in_frame(d0, f0, gens, eps, thetas))
        self.assertTrue(survives_addition_any_angle(d0, gens, eps, thetas, "Z", mask([0, 1]), f1))
        self.assertTrue(survives_addition_any_angle(d1, gens, eps, thetas, "Z", mask([1, 2]), f2))
        self.assertAlmostEqual(
            root_of_unity(sector_phase(d2, f2, gens, eps, thetas)),
            oracle_sector_phase(d2, f2, gens, eps, radians(thetas)),
        )
        # Empty indices resolve vacuously; inconsistent or ill-formed frames are rejected.
        self.assertEqual(resolved_eigenvalues(d2, f2, gens, []), ())
        bad_frame = [("X", mask([0]), 1)]  # anticommutes with Z_0 Z_1 on d2
        with self.assertRaises(ValueError):
            survives_addition_any_angle(d1, gens, eps, thetas, "Z", mask([1, 2]), bad_frame)
        with self.assertRaises(ValueError):
            resolved_eigenvalues(d2, bad_frame, gens, [0, 1])
        with self.assertRaises(ValueError):
            preserves_in_frame(four_two_two_display(), four_two_two_frame(), [pauli_from_string("ZIZI")], [1], [Q4])
        with self.assertRaises(ValueError):
            sector_phase(four_two_two_display(), four_two_two_frame(), [pauli_from_string("ZIZI")], [1], [Q4])
        with self.assertRaises(ValueError):
            addresses(d2, bad_frame, set(), gens, eps, thetas)


class Transcription(unittest.TestCase):
    def test_consumer_json_transcribes_frame_reading(self):
        with open(os.path.join(HERE, "consumer.json"), encoding="utf-8") as fh:
            block = json.load(fh)["gate_realization"]
        rules = block["gate_survival"]["carry_rules"]
        self.assertNotIn("not yet defined (logical-witness eigenvalues)", rules["C-ADD-CHECK"])
        frame = block["frame_reading"]
        for key in ("frame", "preserves_in_frame", "sector_phase", "image", "addresses"):
            self.assertIn(key, frame)
        for key in ("preserves_in_frame", "sector_phase", "image", "addresses"):
            self.assertEqual(
                set(frame[key]["carry_rules"]),
                {"C-SKIP", "C-ADD-CHECK", "C-DELETE-CHECK", "C-DIRECT-SUM", "C-SEQUENCE"},
            )
        self.assertEqual(frame["source"], "spec/JUDGMENT_LAYER.md §2h")
        # Review of PR #665: the angle domain is stated, and the addition cell
        # of Rows C and D separates the refuted case from the unstated one.
        self.assertIn("rational", frame["angle_domain"])
        self.assertIn("rational angles", rules["C-ADD-CHECK"])
        for key in ("preserves_in_frame", "sector_phase"):
            cell = frame[key]["carry_rules"]["C-ADD-CHECK"]
            self.assertIn("does not carry", cell)
            self.assertIn("not yet defined", cell)


class Sweep(unittest.TestCase):
    def test_frame_reading_no_disagreement(self):
        stats = sweep_frames(seed=572, trials=300, max_n=4)
        self.assertEqual(stats["disagreements"], [])
        for key in (
            "preservation_any_angle",
            "frame_sector_preservation",
            "sector_phase",
            "addition_any_angle",
            "addition_in_frame",
            "addition_resolved_formula",
            "image_pi4",
            "image_scalar",
            "addressability",
            "theorem1_phase",
        ):
            self.assertGreater(stats[key]["true"], 0, key)
            self.assertGreater(stats[key]["false"], 0, key)
        self.assertGreater(stats["phase_carry_under_refinement"]["true"], 0)
        self.assertEqual(stats["phase_carry_under_refinement"]["false"], 0)

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
