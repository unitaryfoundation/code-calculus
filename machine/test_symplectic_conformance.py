"""Conformance entry point for the symplectic move set (issue #305)."""

import os
import random
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.join(HERE, "experiments")
for path in (EXP, HERE):
    if path not in sys.path:
        sys.path.insert(0, path)

import symplectic_conformance_harness as harness


class SymplecticConformanceTests(unittest.TestCase):
    def test_fixtures_replay_without_violations(self):
        violations = harness.run_fixtures()
        self.assertEqual(violations, [], violations[:3])

    def test_small_random_run_has_no_violations(self):
        rng = random.Random(20261110)
        total = 0
        for index in range(40):
            n = rng.randint(2, 5)
            state = harness.random_stabilizer_state(rng, list(range(n)))
            violations = harness.run_case(rng, state, lower_seed=index % 3,
                                          upper_slack=index % 2)
            self.assertEqual(violations, [], violations[:3])
            total += len(violations)
        self.assertEqual(total, 0)

    def test_suite_covers_every_move_with_a_nonzero_lower_endpoint(self):
        report = harness.run_suite(cases=60, seed=7)
        self.assertEqual(report["total_violations"], 0, report["violation_shapes"][:3])
        self.assertEqual(report["moves_never_transited"], [])
        self.assertEqual(report["moves_without_nonzero_lower_case"], [])


if __name__ == "__main__":
    unittest.main()
