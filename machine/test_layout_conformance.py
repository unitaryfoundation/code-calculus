"""Conformance entry point for the layout cells (issue #333).

The cells are `spec/JUDGMENT_LAYER.md` section 2d.5, transcribed in
`machine/semantics.json` under `layout_cells`; the harness is
`machine/experiments/layout_conformance_harness.py`. The honesty tests here
pin the section 2d.3 predicate the harness and the consumer share.
"""

import os
import random
import sys
import unittest
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.join(HERE, "experiments")
for path in (EXP, HERE):
    if path not in sys.path:
        sys.path.insert(0, path)

import layout_conformance_harness as harness  # noqa: E402
from machine.priced_calculus import (  # noqa: E402
    CodeState,
    layout_honest,
    layout_is_honest,
    locality_class,
    run_sequence,
)


class LayoutConformanceTests(unittest.TestCase):
    def test_seeded_graft_increases_the_radius_within_the_factor_of_two(self):
        # The naive non-increase is false and the factor-of-two bound holds:
        # the one example the suite always carries, checked on exact squares.
        state, layout, layers = harness.seeded_graft_increase_case()
        parent_sq = harness.radius_sq(layout, state)
        child = state.graft(0, "X", ["a1", "a2"])
        child_sq = harness.radius_sq(harness.restrict(layout, child), child)
        self.assertEqual(parent_sq, Fraction(5))
        self.assertEqual(child_sq, Fraction(16))
        self.assertGreater(child_sq, parent_sq)
        self.assertLessEqual(child_sq, 4 * parent_sq)
        self.assertTrue(harness.honest(harness.restrict(layout, child), layers))

    def test_small_random_run_has_no_violations(self):
        rng = random.Random(20261110)
        total = 0
        for index in range(25):
            n = rng.randint(3, 5)
            state = harness.random_state(rng, list(range(n)))
            layers = 1 + index % 2
            layout = harness.random_layout(rng, state.Q, layers, dishonest=index % 5 == 4)
            violations, _coverage = harness.run_case(rng, state, layout, layers)
            self.assertEqual(violations, [], violations[:3])
            total += len(violations)
        self.assertEqual(total, 0)

    def test_suite_transits_every_move_and_observes_every_non_transfer_case(self):
        report = harness.run_suite(cases=60, seed=7)
        self.assertEqual(report["total_violations"], 0, report["violation_shapes"][:3])
        self.assertEqual(report["moves_never_transited"], [])
        self.assertEqual(report["required_observations_missing"], [])
        # Both directions of P-REBASE occur, so no monotone cell could hold.
        self.assertGreaterEqual(report["coverage"]["rebase_increases"], 1)
        self.assertGreaterEqual(report["coverage"]["rebase_decreases"], 1)


class HonestyPredicateTests(unittest.TestCase):
    """Section 2d.3: at most `layers` qubits per site, distinct sites >= 1 apart."""

    def test_two_qubits_on_one_site_are_honest_in_two_layers_only(self):
        coordinates = [[0, 0], [0, 0], [1, 0]]
        self.assertTrue(layout_is_honest(coordinates, 2))
        self.assertFalse(layout_is_honest(coordinates, 1))

    def test_sites_closer_than_one_are_dishonest_exactly(self):
        self.assertFalse(layout_is_honest([[0, 0], ["0.5", 0]], 1))
        self.assertFalse(layout_is_honest([[0, 0], [0.999, 0]], 2))
        self.assertTrue(layout_is_honest([[0, 0], [1, 0]], 1))
        # Three-dimensional sites and exact rational strings are read exactly.
        self.assertTrue(layout_is_honest([[0, 0, 0], ["0.6", "0.8", 0]], 1))
        self.assertFalse(layout_is_honest([[0, 0, 0], ["0.6", "0.7", 0]], 1))

    def test_malformed_input_is_dishonest_rather_than_raising(self):
        self.assertFalse(layout_is_honest([[0, 0], None], 1))
        self.assertFalse(layout_is_honest([[0, 0], ["x", 0]], 1))
        self.assertFalse(layout_is_honest([[0, 0]], 0))
        self.assertFalse(layout_is_honest([[0, 0]], True))

    def test_document_honesty_reads_the_layer_count(self):
        document = {"n": 3, "locality": {"coordinates": [[0, 0], [0, 0], [1, 0]],
                                         "layers": 2}}
        self.assertTrue(layout_honest(document))
        document["locality"]["layers"] = 1
        self.assertFalse(layout_honest(document))
        document["locality"]["layers"] = 0
        self.assertFalse(layout_honest(document))
        del document["locality"]["layers"]
        self.assertFalse(layout_honest(document))
        self.assertTrue(layout_honest({"n": 3}))

    def test_a_bilayer_code_with_shared_sites_receives_the_bilayer_class(self):
        # Before 2026-11-10 the consumer read this layout as dishonest and
        # assigned `unrestricted`; section 2d.3 allows two qubits per site in
        # two layers, and the radius sqrt(2) is under the bilayer cap.
        document = {
            "schema_version": "0.5", "name": "bilayer", "code_type": "CSS",
            "n": 4, "k": 2,
            "checks": {"X": [[0, 1, 2]], "Z": [[1, 2, 3]]},
            "distance": {"d": 1,
                         "X": {"value": 1, "confidence": "upper_bound", "witness": [0]},
                         "Z": {"value": 1, "confidence": "upper_bound", "witness": [3]}},
            "provenance": {"authors": ["test"], "construction": "fixture",
                           "date": "2026-11-10", "origin": "submission"},
            "locality": {"coordinates": [[0, 0], [0, 0], [1, 1], [1, 1]], "layers": 2},
        }
        CodeState.from_challenge(document)
        _state, _ledger, trace = run_sequence(document, [{"op": "C-SKIP"}])
        self.assertEqual(trace[0]["locality_class"], "local-2d-bilayer")
        self.assertEqual(locality_class(Fraction(2), 2), "local-2d-bilayer")


if __name__ == "__main__":
    unittest.main()
