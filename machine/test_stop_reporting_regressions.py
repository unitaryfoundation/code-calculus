"""Regressions for the descriptive stop/budget reporting fields."""

import unittest
from unittest.mock import patch

from machine import planner
from machine.intervals import DistanceLedger, Interval
from machine.planner import bounded_sector_search, run_campaign
from machine.state import CodeState, Row


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


class StopReasonAccuracy(unittest.TestCase):
    def test_exact_budget_on_real_candidates_is_not_reported_as_truncation(self):
        # Three non-improving candidates and a budget of exactly three: every
        # candidate was inspected, so the frontier ran out.  The old
        # ``evaluated >= budget`` recomputation called this budget exhaustion.
        candidates = [
            {"operation": {"op": "C-SKIP"}, "verdict": "re-measure",
             "state": _state(), "ledger": _ledger(), "n": 3, "k": 1, "w": 2}
            for _ in range(3)
        ]
        for budget, expected_declined in ((3, 0), (4, 1)):
            with self.subTest(budget=budget):
                with patch.object(planner, "plan", return_value=candidates):
                    result = bounded_sector_search(
                        _state(), _ledger(), "Z", budget=budget,
                        sector_swap=False,
                    )
                self.assertFalse(result["truncated"])
                self.assertEqual(result["exhausted"], result["budget_used"] >= result["budget"])
                self.assertEqual(result["stop_reason"], "frontier-exhausted")
                self.assertEqual(result["budget_declined"], expected_declined)

    def test_budget_really_truncating_still_reports_exhaustion(self):
        candidates = [
            {"operation": {"op": "C-SKIP"}, "verdict": "re-measure",
             "state": _state(), "ledger": _ledger(), "n": 3, "k": 1, "w": 2}
            for _ in range(5)
        ]
        with patch.object(planner, "plan", return_value=candidates):
            result = bounded_sector_search(
                _state(), _ledger(), "Z", budget=3, sector_swap=False,
            )
        self.assertTrue(result["truncated"])
        self.assertTrue(result["exhausted"])
        self.assertEqual(result["stop_reason"], "budget-exhausted")
        self.assertEqual(result["budget_declined"], 0)

    def test_campaign_error_termination_carries_stop_reason(self):
        bad = [{
            "operation": {"op": "X-BOGUS"}, "verdict": "certify",
            "state": _state(), "ledger": _ledger(), "n": 3, "k": 1, "w": 2,
        }]
        with patch.object(planner, "plan", return_value=bad):
            history = run_campaign(
                _state(), _ledger(), 3, steps=2, structural=False,
                support_search=False,
            )
        self.assertEqual(len(history), 1)
        self.assertIn("error", history[-1])
        self.assertEqual(history[-1]["stop_reason"], "operation-failed")


if __name__ == "__main__":
    unittest.main()
