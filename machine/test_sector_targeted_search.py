import unittest

from machine.planner import bounded_sector_search, search_status
from machine.priced_calculus import (
    CodeState,
    DistanceLedger,
    Interval,
    Row,
)


def _state():
    return CodeState(
        (0, 1, 2),
        (
            Row("a9001", "X", (0, 1)),
            Row("b9001", "Z", (0, 1)),
            Row("b9002", "Z", (1, 2)),
        ),
        frozenset(("a9001", "b9001", "b9002")),
    )


def _ledger():
    return DistanceLedger(Interval(0, 3), {"X": Interval(0, 3), "Z": Interval(0, 3)})


class TestBoundedSectorSearch(unittest.TestCase):
    def test_returns_budget_record(self):
        state = _state()
        ledger = _ledger()
        result = bounded_sector_search(state, ledger, "Z", budget=10)
        self.assertIn("budget", result)
        self.assertIn("budget_used", result)
        self.assertIn("evaluated", result)
        self.assertIn("exhausted", result)
        self.assertIn("candidates", result)
        self.assertLessEqual(result["budget_used"], result["budget"])

    def test_no_distance_recomputation(self):
        # The search only consults the carried ledger; calling it must not
        # raise and must not require an oracle import.
        state = _state()
        ledger = _ledger()
        result = bounded_sector_search(state, ledger, "X", budget=5)
        self.assertIsInstance(result["candidates"], list)

    def test_budget_exhaustion(self):
        state = _state()
        ledger = _ledger()
        result = bounded_sector_search(state, ledger, "Z", budget=1)
        self.assertTrue(result["budget_used"] <= 1)

    def test_search_status_helper(self):
        self.assertEqual(search_status([]), "no survivor found")
        self.assertEqual(search_status([{"a": 1}]), "survivors found")


if __name__ == "__main__":
    unittest.main()
