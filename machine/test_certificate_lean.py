"""The translation to the mechanized certificate checker.

`lean/CodeCalculus/CertificateChecker.lean` is the checker and `lake build`
is the authority for it. These tests do not run Lean. They pin that the
committed `lean/CodeCalculus/CertificateInstances.lean` is what the
generator emits, that the emitted terms have the shape the Lean structures
expect, and that the exporter refuses inputs whose module could not build.
"""

import copy
import unittest

from machine.certificates import (
    build_sector_lower_bound_certificate,
    build_sector_lower_bound_tree_certificate,
    lean_certificate_term,
    lean_instance_block,
    lean_state_term,
    lean_tree_instance_block,
    lean_tree_term,
)
from machine.experiments.certificate_lean_instances import (
    OUTPUT,
    cyclic_30_4_6,
    first_witness,
    generate,
    pinned_parent,
    w3_result,
)


class LeanTranslationTests(unittest.TestCase):
    def test_committed_instances_match_the_generator(self):
        self.assertEqual(OUTPUT.read_text(), generate())

    def test_state_term_uses_identifier_ranks(self):
        term = lean_state_term(w3_result())
        self.assertIn("Q := [1, 2, 3]", term)
        self.assertIn("{ id := 1, sector := Sector.X, support := [2, 3] }", term)
        self.assertIn(
            "{ id := 10000, sector := Sector.Z, support := [1, 2, 3] }", term)
        self.assertIn("used := [0, 1, 10000]", term)

    def test_certificate_term_renders_both_reasons(self):
        certificate = build_sector_lower_bound_certificate(w3_result(), "X", 2)
        term = lean_certificate_term(certificate)
        self.assertIn("sector := Sector.X", term)
        self.assertIn("bound := 2", term)
        self.assertIn(
            "{ support := [], reason := KillReason.inSpan [false] }", term)
        self.assertIn(
            "{ support := [1], reason := KillReason.oddOverlap [1, 2, 3] }",
            term)

    def test_block_states_the_bound_and_the_exact_value(self):
        state = pinned_parent()
        certificate = build_sector_lower_bound_certificate(state, "Z", 3)
        block = lean_instance_block(
            "parent", state, certificate,
            witness=first_witness(state, "Z", 3))
        self.assertIn(
            "ExtNat.finite 3 ≤ exactDistanceExt Sector.Z parent", block)
        self.assertIn("exactDistance? Sector.Z parent = some 3", block)
        self.assertEqual(block.count("(by decide)"), 3)

    def test_a_certificate_for_another_state_is_refused(self):
        certificate = build_sector_lower_bound_certificate(w3_result(), "X", 2)
        with self.assertRaises(ValueError):
            lean_instance_block("parent", pinned_parent(), certificate)

    def test_a_rejected_certificate_is_refused(self):
        state = w3_result()
        certificate = build_sector_lower_bound_certificate(state, "X", 2)
        broken = copy.deepcopy(certificate)
        broken["kills"].pop()
        with self.assertRaises(ValueError):
            lean_instance_block("w3_result", state, broken)

    def test_a_bad_witness_is_refused(self):
        state = w3_result()
        certificate = build_sector_lower_bound_certificate(state, "X", 2)
        for witness in ((1,), (2, 3), (4, 5), (1, 2, 3)):
            with self.assertRaises(ValueError):
                lean_instance_block(
                    "w3_result", state, certificate, witness=witness)


class LeanTreeTranslationTests(unittest.TestCase):
    """Pruning-tree instances (issue #574)."""

    def test_tree_term_uses_positions_and_the_lean_constructors(self):
        tree = ["branch", 7, ["need_more", 2],
                ["branch", 9, ["conflict", 0], ["in_span", [1, 0]]]]
        term = lean_tree_term(tree, [3, 7, 9])
        self.assertEqual(
            term.strip(),
            "(branch 1 (needMore 2) (branch 2 (conflict 0) "
            "(inSpan [true, false])))")
        self.assertEqual(lean_tree_term(["bound"], [0]).strip(), "bound")
        with self.assertRaises(ValueError):
            lean_tree_term(["prune"], [0])

    def test_long_tree_terms_are_wrapped(self):
        state = pinned_parent()
        certificate = build_sector_lower_bound_tree_certificate(state, "X", 3)
        lines = lean_tree_term(certificate["tree"], list(state.Q)).split("\n")
        self.assertGreater(len(lines), 3)
        for line in lines:
            self.assertTrue(line.startswith("    "))
            self.assertLess(len(line), 140)
        joined = " ".join(line.strip() for line in lines)
        self.assertEqual(joined.count("("), joined.count(")"))

    def test_block_states_the_bound_in_the_option_reading(self):
        state = pinned_parent()
        certificate = build_sector_lower_bound_tree_certificate(state, "Z", 3)
        block = lean_tree_instance_block(
            "parent", state, certificate, witness=first_witness(state, "Z", 3))
        self.assertIn("def parent_Z_tree : PruneTree :=", block)
        self.assertIn(
            "checkPruneCertificate parent Sector.Z 3 parent_Z_prune = true "
            ":= by decide +kernel", block)
        self.assertIn(
            "∀ d : Nat, exactDistance? Sector.Z parent = some d → 3 ≤ d",
            block)
        self.assertIn("exactDistance? Sector.Z parent = some 3", block)
        # The matrices are the row vectors over Q, opposite sector first.
        self.assertIn("  opp := [\n    [true, true, false, true, true,", block)
        self.assertNotIn("native_decide", block)
        self.assertNotIn("sorry", block)

    def test_tree_block_refuses_what_the_module_could_not_build(self):
        state = pinned_parent()
        certificate = build_sector_lower_bound_tree_certificate(state, "X", 3)
        with self.assertRaises(ValueError):
            lean_tree_instance_block("w3_result", w3_result(), certificate)
        broken = copy.deepcopy(certificate)
        broken["bound"] = 4
        with self.assertRaises(ValueError):
            lean_tree_instance_block("parent", state, broken)
        with self.assertRaises(ValueError):
            lean_tree_instance_block("parent", state, certificate,
                                     witness=(0, 1, 2))

    def test_committed_module_carries_the_thirty_qubit_instance(self):
        text = OUTPUT.read_text()
        state = cyclic_30_4_6()
        self.assertEqual((state.n(), state.k()), (30, 4))
        for sector in ("X", "Z"):
            stem = "cyclic_30_4_6_%s" % sector
            self.assertIn(
                "theorem %s_accepts :\n    checkPruneCertificate "
                "cyclic_30_4_6 Sector.%s 6 %s_prune = true := by "
                "decide +kernel" % (stem, sector, stem), text)
            self.assertIn(
                "theorem %s_exact :\n    exactDistance? Sector.%s "
                "cyclic_30_4_6 = some 6" % (stem, sector), text)
        # No well-formedness theorem for this term: too slow in the kernel.
        self.assertNotIn("cyclic_30_4_6_wellFormed", text)
        self.assertIn("theorem qldpc_10_2_3_b_wellFormed", text)
        state.validate()
        self.assertNotIn("native_decide", text)
        self.assertNotIn("sorry", text)


if __name__ == "__main__":
    unittest.main()
