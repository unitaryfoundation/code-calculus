"""Conformance entry point for the priced-consumer harness ().

Scaled-up hardening entry point (): ~2000 cases per seed across
several fixed seeds, including nonzero and exact derived lower endpoints.
"""

import os
import random
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.join(HERE, "experiments")
if EXP not in sys.path:
    sys.path.insert(0, EXP)
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import priced_conformance_harness as harness


CASES = 2000
BASE_SEEDS = (12345, 54321, 999, 20261025, 42)
LOWER_SEEDS = (12345, 54321, 999)


def _run_seed(seed, cases, lower_seed):
    rng = random.Random(seed)
    total_cases = 0
    total_violations = 0
    first_violations = []
    while total_cases < cases:
        n = rng.randint(3, 7)
        q_labels = list(range(n))
        try:
            state = harness.random_state(rng, q_labels)
        except RuntimeError:
            continue
        violations = harness.run_case(rng, state, [], lower_seed=lower_seed)
        total_cases += 1
        total_violations += len(violations)
        if violations and len(first_violations) < 3:
            first_violations.extend(violations[: 3 - len(first_violations)])
    print("seed=%s lower_seed=%r cases=%d violations=%d"
          % (seed, lower_seed, total_cases, total_violations))
    return total_cases, total_violations, first_violations


class PricedConformanceHarnessTests(unittest.TestCase):
    def test_small_random_run_has_no_interval_violations(self):
        # Keep a small, fast smoke test for quick feedback.
        rng = random.Random(12345)
        total = 0
        for _ in range(30):
            n = rng.randint(3, 6)
            state = harness.random_state(rng, list(range(n)))
            violations = harness.run_case(rng, state, [])
            total += len(violations)
            self.assertEqual(violations, [], violations[:3])
        self.assertEqual(total, 0)

    def test_scaled_random_runs_have_no_interval_violations(self):
        total_violations = 0
        first_violations = []
        for seed in BASE_SEEDS:
            _cases, violations, firsts = _run_seed(seed, CASES, 0)
            total_violations += violations
            if firsts and len(first_violations) < 3:
                first_violations.extend(firsts[: 3 - len(first_violations)])
        self.assertEqual(total_violations, 0, first_violations[:3])

    def test_scaled_nonzero_lower_endpoints(self):
        total_violations = 0
        first_violations = []
        for seed in LOWER_SEEDS:
            _cases, violations, firsts = _run_seed(seed, CASES, 1)
            total_violations += violations
            if firsts and len(first_violations) < 3:
                first_violations.extend(firsts[: 3 - len(first_violations)])
        self.assertEqual(total_violations, 0, first_violations[:3])

    def test_scaled_exact_derived_lower_endpoints(self):
        total_violations = 0
        first_violations = []
        for seed in LOWER_SEEDS:
            _cases, violations, firsts = _run_seed(seed, CASES, "exact")
            total_violations += violations
            if firsts and len(first_violations) < 3:
                first_violations.extend(firsts[: 3 - len(first_violations)])
        self.assertEqual(total_violations, 0, first_violations[:3])

    def test_suite_covers_nonzero_lower_endpoints_per_operation(self):
        # : the main suite randomizes nonzero lower endpoints and
        # must transit every admitted operation at least once with a nonzero
        # lower endpoint on its input ledger, with 0 violations overall.
        report = harness.run_suite()
        self.assertEqual(report["total_violations"], 0,
                         report["violation_shapes"][:3])
        self.assertEqual(report["admitted_operations_never_transited"], [])
        self.assertEqual(
            report["admitted_operations_without_nonzero_lower_case"], [])
        nonzero_seeds = [seed for seed in report["lower_seed_counts"]
                         if seed != "0"]
        self.assertTrue(nonzero_seeds, report["lower_seed_counts"])
        for op in report["admitted_operations"]:
            self.assertGreaterEqual(
                report["coverage_by_operation"][op]["nonzero_lower_inputs"],
                1, op)


if __name__ == "__main__":
    unittest.main()
