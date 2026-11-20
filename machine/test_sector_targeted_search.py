import unittest
from unittest.mock import patch

from machine.planner import bounded_sector_search, search_status
from machine.priced_calculus import (
    CodeState,
    DistanceLedger,
    Interval,
    Malformed,
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


def _k_ge_one_state():
    # k = 1: one X row, one Z row on three qubits.
    return CodeState(
        (0, 1, 2),
        (
            Row("a9001", "X", (0, 1)),
            Row("b9001", "Z", (0, 1)),
        ),
        frozenset(("a9001", "b9001")),
    )


def _no_improvement_state():
    # A valid state whose applicable moves do not improve the target sector.
    return CodeState(
        (0, 1, 2, 3),
        (
            Row("a9001", "X", (0, 1)),
            Row("a9002", "X", (2, 3)),
            Row("b9001", "Z", (0, 2)),
            Row("b9002", "Z", (1, 3)),
        ),
        frozenset(("a9001", "a9002", "b9001", "b9002")),
    )


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
        # The search only consults the carried ledger; replacing the exact-
        # distance oracle with one that raises must not affect it.
        state = _state()
        ledger = _ledger()
        with patch("machine.oracle.exact_distances", side_effect=RuntimeError("boom")):
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

    def test_malformed_inputs(self):
        state = _state()
        ledger = _ledger()
        # invalid target sector
        with self.assertRaises(Malformed):
            bounded_sector_search(state, ledger, "Y", budget=10)
        # non-positive budget / max_depth
        with self.assertRaises(Malformed):
            bounded_sector_search(state, ledger, "Z", budget=0)
        with self.assertRaises(Malformed):
            bounded_sector_search(state, ledger, "Z", max_depth=0)
        # non-integer budget / max_depth
        with self.assertRaises(Malformed):
            bounded_sector_search(state, ledger, "Z", budget=1.5)
        with self.assertRaises(Malformed):
            bounded_sector_search(state, ledger, "Z", max_depth=1.5)
        # non-ledger
        with self.assertRaises(Malformed):
            bounded_sector_search(state, "not-a-ledger", "Z", budget=10)
        # invalid explicit target
        with self.assertRaises(Malformed):
            bounded_sector_search(state, ledger, "Z", target=0, budget=10)
        # non-CodeState
        with self.assertRaises(Malformed):
            bounded_sector_search("not-a-state", ledger, "Z", budget=10)
        # a valid empty state is not malformed
        empty_state = CodeState((), (), frozenset())
        result = bounded_sector_search(empty_state, ledger, "Z", budget=10)
        self.assertIsInstance(result["candidates"], list)

    def test_refusal_when_no_improvement(self):
        state = _no_improvement_state()
        ledger = DistanceLedger(Interval(0, 2), {"X": Interval(0, 2), "Z": Interval(0, 2)})
        result = bounded_sector_search(state, ledger, "Z", budget=4)
        self.assertIsInstance(result["candidates"], list)
        self.assertEqual(result["candidates"], [])
        self.assertEqual(result["search_status"], "no survivor found")

    def test_success_case_finds_improving_peel(self):
        state = _k_ge_one_state()
        ledger = DistanceLedger(Interval(0, 3),
                                {"X": Interval(2, 2), "Z": Interval(0, 3)})
        result = bounded_sector_search(state, ledger, "Z", budget=10)
        self.assertTrue(result["candidates"])
        parent_z = ledger.sector["Z"]
        tighter = False
        for c in result["candidates"]:
            cz = c["ledger"].sector["Z"]
            if (cz.lower is not None and (parent_z.lower is None or cz.lower > parent_z.lower)
                    or cz.upper is not None and (parent_z.upper is None or cz.upper < parent_z.upper)):
                tighter = True
        self.assertTrue(tighter)

if __name__ == "__main__":
    unittest.main()
