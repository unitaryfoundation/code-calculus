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
    lean_certificate_term,
    lean_instance_block,
    lean_state_term,
)
from machine.experiments.certificate_lean_instances import (
    OUTPUT,
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


if __name__ == "__main__":
    unittest.main()
