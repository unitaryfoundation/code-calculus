"""Regression tests for the consumer input-boundary hardening pass.

Each class pins one of the fixes: sourced lower bounds, shape validation on
public entry points, and the rule that the planner never computes a distance.
"""

import unittest
from unittest.mock import patch

from machine import oracle, planner
from machine.intervals import DistanceLedger, Interval
from machine.planner import (
    _deep_corrected_distance,
    _deletion_price_for,
    deep_verify_candidates,
    plan,
)
from machine.state import CodeState, Malformed, Row


def _state():
    return CodeState(
        (0, 1, 2),
        (Row("a9001", "X", (0, 1)), Row("b9001", "Z", (0, 1))),
        frozenset(("a9001", "b9001")),
    )


def _ledger():
    return DistanceLedger(
        Interval(0, 3), {"X": Interval(0, 3), "Z": Interval(0, 3)}
    )


class SourcedLowerBounds(unittest.TestCase):
    def test_constructed_ledger_refuses_unsourced_bounds(self):
        state = _state()
        for bounds in ({"d": 2}, {"X": 3}, {"d": {"value": 2}}):
            with self.subTest(bounds=bounds), self.assertRaises(Malformed):
                DistanceLedger.for_constructed(state, lower_bounds=bounds)

    def test_constructed_ledger_records_sourced_bound(self):
        ledger = DistanceLedger.for_constructed(
            _state(),
            lower_bounds={"d": {"value": 2, "source": "external derivation"}},
        )
        self.assertEqual(ledger.full, Interval(2, None))
        self.assertEqual(ledger.conditions[0]["cell"], "input lower bound")
        self.assertEqual(ledger.conditions[0]["source"], "external derivation")

    def test_zero_bound_needs_no_source(self):
        ledger = DistanceLedger.for_constructed(_state(), lower_bounds={"d": 0})
        self.assertEqual(ledger.full, Interval(0, None))
        self.assertEqual(ledger.conditions, [])

    def test_challenge_ledger_refuses_unsourced_bounds(self):
        document = {
            "n": 5,
            "checks": {"X": [[0, 1]], "Z": [[0, 1]]},
            "k": 3,
            "distance": {
                "X": {"witness": [2, 3, 4], "value": 3},
                "Z": {"witness": [2, 3, 4], "value": 3},
            },
        }
        state = CodeState.from_challenge(document)
        for bounds in ({"X": 2}, {"X": {"value": 2}}):
            with self.subTest(bounds=bounds), self.assertRaises(Malformed):
                DistanceLedger.from_challenge(
                    state, document, lower_bounds=bounds
                )
        sourced = DistanceLedger.from_challenge(
            state, document,
            lower_bounds={"X": {"value": 2, "source": "external derivation"}},
        )
        self.assertEqual(sourced.conditions[0]["cell"], "input lower bound")


class PublicEntryPointShapes(unittest.TestCase):
    def setUp(self):
        self.state = _state()
        self.ledger = _ledger()

    def test_propagate_rejects_malformed_operation(self):
        for operation in ("C-SKIP", {}, None, 3, []):
            with self.subTest(operation=operation), self.assertRaises(Malformed):
                self.ledger.propagate(operation, self.state)

    def test_decide_requires_positive_target(self):
        for target in (0, -1, True, 1.5, "3", None):
            with self.subTest(target=target), self.assertRaises(Malformed):
                self.ledger.decide(target)

    def test_witness_labels_are_not_coerced(self):
        for support in ([1.9], ["2"], [True]):
            with self.subTest(support=support), self.assertRaises(Malformed):
                DistanceLedger.for_constructed(
                    self.state, witnesses={"X": [support]}
                )

    def test_ledger_does_not_mutate_caller_witness(self):
        witness = {"support": [2], "value": 1, "source": "external"}
        DistanceLedger(
            Interval(0, 3),
            {"X": Interval(0, 3), "Z": Interval(0, 3)},
            {"X": [witness]},
        )
        self.assertNotIn("confidence", witness)

    def test_mixed_type_supports_refused_as_malformed(self):
        with self.assertRaises(Malformed):
            self.state.add_check("X", [0, "a"])
        with self.assertRaises(Malformed):
            self.state.extend_code((), [("X", [0, "a"])])
        right = CodeState(
            (3, 4),
            (Row("a9003", "X", (3, 4)), Row("b9003", "Z", (3, 4))),
            frozenset(("a9003", "b9003")),
        )
        with self.assertRaises(Malformed):
            self.state.glue(right, seam_checks=[("X", [3, "a"])])


class ConsumerDistanceBoundary(unittest.TestCase):
    def test_deep_verify_true_is_refused(self):
        with self.assertRaises(Malformed):
            _deep_corrected_distance(_state(), True)

    def test_deep_verify_alias_requires_callable(self):
        with self.assertRaises(Malformed):
            deep_verify_candidates(None, _state(), _ledger(), 3)

    def test_default_plan_does_not_call_oracle(self):
        with patch.object(
            oracle, "exact_distances",
            side_effect=AssertionError("oracle called on consumer path"),
        ):
            plan(_state(), _ledger(), 3, structural=False)

    def test_external_verifier_does_not_write_a_ledger(self):
        ledger = _ledger()
        candidates = plan(
            _state(), ledger, 3, structural=False, deep_verify=lambda state: 3
        )
        self.assertTrue(candidates)
        self.assertEqual(ledger.full, Interval(0, 3))
        self.assertEqual(ledger.conditions, [])

    def test_price_provider_bug_is_not_swallowed(self):
        with patch(
            "machine.tower_prices.tower_deletion_prices",
            side_effect=TypeError("provider defect"),
        ):
            with self.assertRaises(TypeError):
                _deletion_price_for(
                    _state(), "a9001",
                    config={"inner_state": object(), "groups": [object()]},
                )


if __name__ == "__main__":
    unittest.main()


class ConsumerModuleBoundary(unittest.TestCase):
    def test_consumer_modules_do_not_load_oracle(self):
        import subprocess, sys
        code = (
            "import sys; "
            "import machine.priced_calculus, machine.planner, machine.entrypoints; "
            "assert 'machine.oracle' not in sys.modules, sys.modules.get('machine.oracle')"
        )
        result = subprocess.run(
            [sys.executable, "-c", code],
            capture_output=True, text=True,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
