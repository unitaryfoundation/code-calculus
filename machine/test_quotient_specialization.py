"""Tests for the A-QUOTIENT monomial-quotient specialization enforcement (issue #547)."""

import json
import os
import unittest

from machine.constructors import ADMITTED_CONSTRUCTORS
from machine.intervals import Interval
from machine.quotient_specialization import (
    check_parent_css_compatibility,
    classify_single_qudit_clifford,
    enforce_css_monomial_quotient,
    route_monomial_quotient,
    transfer_theorem_cell,
    validate_free_group_action,
)
from machine.state import CodeState, Malformed, NoDerivation, Row, support_mask


def z2_swap_action():
    """Free Z_2 action on 4 qubits: e = id, g = (0 2)(1 3)."""
    return {
        "e": {0: 0, 1: 1, 2: 2, 3: 3},
        "g": {0: 2, 1: 3, 2: 0, 3: 1},
    }


class CliffordClassificationTests(unittest.TestCase):
    def test_classifies_preserving_swapping_and_mixing(self):
        for c in ("I", "X", "Y", "Z", ("X", "Z"), {"X": "X", "Z": "Z"}):
            self.assertEqual(classify_single_qudit_clifford(c), "sector_preserving")
        for c in ("H", "HX", "HZ", "HY", ("Z", "X"), {"X": "Z", "Z": "X"}):
            self.assertEqual(classify_single_qudit_clifford(c), "sector_swapping")
        for c in ("S", "S_DAG", "SX", "SH", "HS", ("Y", "Z"), ("X", "Y")):
            self.assertEqual(classify_single_qudit_clifford(c), "sector_mixing")

    def test_rejects_unknown_clifford(self):
        with self.assertRaises(Malformed):
            classify_single_qudit_clifford("T_GATE")
        with self.assertRaises(Malformed):
            classify_single_qudit_clifford({"X": "X"})


class FreeActionAndConstraintTests(unittest.TestCase):
    def test_a_quotient_remains_unadmitted_in_constructors(self):
        self.assertNotIn("A-QUOTIENT", ADMITTED_CONSTRUCTORS)

    def test_pure_permutation_action_is_accepted(self):
        rec = enforce_css_monomial_quotient((0, 1, 2, 3), z2_swap_action())
        self.assertTrue(rec["accepted"])
        self.assertTrue(rec["css_preserving"])
        self.assertEqual(rec["taxonomy_id"], "A-QUOTIENT")
        self.assertEqual(rec["taxonomy_status"], "taxonomy-only")
        self.assertEqual(rec["orbits"], ((0, 2), (1, 3)))
        self.assertEqual(rec["representatives"], (0, 1))

    def test_sector_preserving_single_qudit_cliffords_are_accepted(self):
        rec = enforce_css_monomial_quotient(
            (0, 1, 2, 3),
            z2_swap_action(),
            cliffords={"e": "I", "g": "Z"},
            representatives=(2, 3),
        )
        self.assertTrue(rec["accepted"])
        self.assertTrue(rec["css_preserving"])
        self.assertEqual(rec["representatives"], (2, 3))
        self.assertEqual(rec["clifford_classes"], ("sector_preserving",))

    def test_non_free_action_and_fixed_point_clifford_are_refused(self):
        non_free = {
            "e": {0: 0, 1: 1, 2: 2},
            "g": {0: 1, 1: 0, 2: 2},
        }
        with self.assertRaises(NoDerivation):
            validate_free_group_action((0, 1, 2), non_free)
        with self.assertRaises(NoDerivation) as ctx:
            enforce_css_monomial_quotient(
                (0, 1, 2),
                non_free,
                cliffords={"e": "I", "g": {0: "I", 1: "I", 2: "H"}},
            )
        self.assertIn("fixed point", str(ctx.exception))

        # Unfaithful action where a non-identity element fixes every qubit.
        unfaithful = {"e": {0: 0, 1: 1}, "g": {0: 0, 1: 1}}
        with self.assertRaises(NoDerivation) as ctx2:
            enforce_css_monomial_quotient(
                (0, 1), unfaithful, cliffords={"e": "I", "g": "X"}, identity="e"
            )
        self.assertIn("fixed point", str(ctx2.exception))

    def test_non_group_or_bad_representatives_are_malformed(self):
        # Missing identity element.
        with self.assertRaises(Malformed):
            validate_free_group_action((0, 1), {"g": {0: 1, 1: 0}})
        # Not closed under composition (order-3 generator without its square).
        not_closed = {
            "e": {0: 0, 1: 1, 2: 2},
            "g": {0: 1, 1: 2, 2: 0},
        }
        with self.assertRaises(Malformed):
            validate_free_group_action((0, 1, 2), not_closed)
        # Representatives missing an orbit.
        with self.assertRaises(Malformed):
            enforce_css_monomial_quotient(
                (0, 1, 2, 3), z2_swap_action(), representatives=(0, 2)
            )


class DualityQuotientRoutingTests(unittest.TestCase):
    def test_duality_quotient_is_refused_and_routed_accurately(self):
        # Hadamard sector-swapping action: not CSS-preserving, refuses specialization.
        cliffords = {"e": "I", "g": "H"}
        routed = route_monomial_quotient((0, 1, 2, 3), z2_swap_action(), cliffords=cliffords)
        self.assertFalse(routed["accepted"])
        self.assertFalse(routed["css_preserving"])
        self.assertEqual(routed["route"], "extended-state-layer")
        self.assertEqual(
            routed["css_sector_swap_counterpart"],
            "E-LOCAL-HADAMARD (TAXONOMY.md §2.12, T=Q)",
        )
        self.assertIn("X-LOCAL-CLIFFORD (§4.4)", routed["extended_state_targets"])
        self.assertNotIn("not_routed_to", routed)
        self.assertNotIn("X-DRESSED-QUOTIENT", json.dumps(routed))
        self.assertIn("issue #545", routed["v0_3_0_status"])

        with self.assertRaises(NoDerivation):
            enforce_css_monomial_quotient((0, 1, 2, 3), z2_swap_action(), cliffords=cliffords)

    def test_sector_mixing_clifford_is_refused_and_routed(self):
        cliffords = {"e": "I", "g": "S"}
        routed = route_monomial_quotient((0, 1, 2, 3), z2_swap_action(), cliffords=cliffords)
        self.assertFalse(routed["accepted"])
        self.assertFalse(routed["css_preserving"])
        self.assertEqual(routed["route"], "extended-state-layer")
        self.assertNotIn("not_routed_to", routed)
        self.assertNotIn("X-DRESSED-QUOTIENT", json.dumps(routed))

        with self.assertRaises(NoDerivation):
            enforce_css_monomial_quotient((0, 1, 2, 3), z2_swap_action(), cliffords=cliffords)


class ParentCssCompatibilityTests(unittest.TestCase):
    def test_accepts_g_equivariant_css_parent_and_verifies_quotient_orthogonality(self):
        parent = CodeState(
            (0, 1, 2, 3),
            (
                Row("a1", "X", (0, 1)),
                Row("a2", "X", (2, 3)),
                Row("b1", "Z", (0, 1)),
                Row("b2", "Z", (2, 3)),
            ),
            frozenset({"a1", "a2", "b1", "b2"}),
        )
        rec = enforce_css_monomial_quotient(
            (0, 1, 2, 3),
            z2_swap_action(),
            cliffords={"e": "I", "g": "Z"},
            parent_state=parent,
        )
        self.assertTrue(rec["parent_css_compatible"])
        self.assertTrue(rec["quotient_css_orthogonal"])
        self.assertEqual(rec["quotient_x_masks"], (support_mask((0, 1)),))
        self.assertEqual(rec["quotient_z_masks"], (support_mask((0, 1)),))

        compat = check_parent_css_compatibility(
            parent,
            z2_swap_action(),
            cliffords={"e": "I", "g": "Z"},
            representatives=(2, 3),
        )
        self.assertTrue(compat["parent_css_compatible"])
        self.assertEqual(compat["quotient_x_masks"], (support_mask((2, 3)),))

        # Orbit-invariant weight-4 Z check collapses modulo 2 under Z_2 projection.
        parent_collapsed = CodeState(
            (0, 1, 2, 3),
            (
                Row("a1", "X", (0, 1)),
                Row("a2", "X", (2, 3)),
                Row("b1", "Z", (0, 1, 2, 3)),
            ),
            frozenset({"a1", "a2", "b1"}),
        )
        compat2 = check_parent_css_compatibility(parent_collapsed, z2_swap_action())
        self.assertEqual(compat2["quotient_x_masks"], (support_mask((0, 1)),))
        self.assertEqual(compat2["quotient_z_masks"], ())
        self.assertTrue(compat2["quotient_css_orthogonal"])

    def test_rejects_non_equivariant_parent_and_qubit_mismatch(self):
        non_equivariant = CodeState(
            (0, 1, 2, 3),
            (Row("a1", "X", (0, 1)), Row("b1", "Z", (0, 1))),
            frozenset({"a1", "b1"}),
        )
        with self.assertRaises(NoDerivation) as ctx:
            check_parent_css_compatibility(non_equivariant, z2_swap_action())
        self.assertIn("G-equivariant", str(ctx.exception))

        valid_parent = CodeState(
            (0, 1, 2, 3),
            (
                Row("a1", "X", (0, 1)),
                Row("a2", "X", (2, 3)),
                Row("b1", "Z", (0, 1)),
                Row("b2", "Z", (2, 3)),
            ),
            frozenset({"a1", "a2", "b1", "b2"}),
        )
        # Swapping Clifford still refused even when parent checks are G-equivariant.
        with self.assertRaises(NoDerivation):
            check_parent_css_compatibility(
                valid_parent, z2_swap_action(), cliffords={"e": "I", "g": "H"}
            )
        # Qubit mismatch between specialization and parent_state -> Malformed.
        action_2q = {"e": {0: 0, 1: 1}, "g": {0: 1, 1: 0}}
        with self.assertRaises(Malformed):
            enforce_css_monomial_quotient((0, 1), action_2q, parent_state=valid_parent)


class TransferTheoremCellTests(unittest.TestCase):
    def test_transfer_cell_defaults_to_unknown_intervals_and_requires_source(self):
        rec = enforce_css_monomial_quotient((0, 1, 2, 3), z2_swap_action())
        cell = transfer_theorem_cell(rec)
        self.assertEqual(cell["taxonomy_status"], "taxonomy-only")
        self.assertEqual(cell["cell_status"], "conditional")
        self.assertFalse(cell["computed_distance"])
        self.assertFalse(cell["usable_automatic_bound"])
        self.assertEqual(cell["intervals"]["X"], Interval(0, None))
        self.assertEqual(cell["intervals"]["Z"], Interval(0, None))
        self.assertEqual(cell["intervals"]["d"], Interval(0, None))

        # Any supplied bound or quotient count without a source is malformed.
        with self.assertRaises(Malformed):
            transfer_theorem_cell(rec, k_quotient=1)
        with self.assertRaises(Malformed):
            transfer_theorem_cell(rec, d_x_lower=2, source="  ")

    def test_transfer_cell_records_supplied_bounds_and_validates_witnesses(self):
        rec = enforce_css_monomial_quotient((0, 1, 2, 3), z2_swap_action())
        # Two-qubit quotient code on {0, 1} with Z check {0, 1}.
        q_state = CodeState((0, 1), (Row("b1", "Z", (0, 1)),), frozenset({"b1"}))
        q_state.validate()
        cell = transfer_theorem_cell(
            rec,
            k_parent=2,
            k_quotient=1,
            tate_new_logicals=0,
            d_x_lower=2,
            d_z_lower=1,
            quotient_state=q_state,
            witnesses={"X": [(0, 1)], "Z": [(0,)]},
            source="Hsin arXiv 2611.09538v1 §3.3",
        )
        self.assertFalse(cell["usable_automatic_bound"])
        self.assertEqual(cell["k_quotient"], 1)
        self.assertEqual(cell["tate_new_logicals"], 0)
        self.assertEqual(cell["intervals"]["X"], Interval(2, 2))
        self.assertEqual(cell["intervals"]["Z"], Interval(1, 1))
        self.assertEqual(cell["intervals"]["d"], Interval(1, 1))

        # Contradicting supplied lower bound > validated witness -> NoDerivation.
        with self.assertRaises(NoDerivation):
            transfer_theorem_cell(
                rec,
                d_z_lower=2,
                quotient_state=q_state,
                witnesses={"Z": [(0,)]},
                source="inconsistent bound",
            )

    def test_consumer_json_transcribes_monomial_quotient_record(self):
        here = os.path.dirname(os.path.abspath(__file__))
        with open(os.path.join(here, "consumer.json"), encoding="utf-8") as fh:
            consumer = json.load(fh)
        transfer_entry = consumer["conditional_inputs"]["monomial_quotient_transfer"]
        spec_entry = consumer["monomial_quotient_specialization"]
        self.assertEqual(transfer_entry["source"], "spec/JUDGMENT_LAYER.md §2i")
        self.assertEqual(spec_entry["source"], "spec/TAXONOMY.md §2.15")
        self.assertIn("no usable automatic", transfer_entry["claimed_rule"])
        self.assertIn("TAXONOMY.md §2.12", spec_entry["duality_quotient_routing"])
        self.assertNotIn("X-DRESSED-QUOTIENT", json.dumps(transfer_entry))
        self.assertNotIn("X-DRESSED-QUOTIENT", json.dumps(spec_entry))


if __name__ == "__main__":
    unittest.main()
