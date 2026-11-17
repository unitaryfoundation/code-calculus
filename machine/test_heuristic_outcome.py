"""Heuristic search outcomes in the admitted `probabilistic` shape (issue #329).

`spec/CLAIMS.md` (*Admission*, 2026-11-11) admits the `probabilistic` claim
shape as the recorded form of a heuristic search outcome: a claim about the
search that licenses no ledger endpoint. `heuristic_outcome` builds the
record; the strict-improvement enumeration fallback and the planner's bounded
sector search attach it. `certificate-checked` is admitted to the candidate
release only and is carried by no field here; it attaches to kernel-checked
Lean theorems (issue #371).
"""

import unittest

from machine.planner import bounded_sector_search, search_status
from machine.priced_calculus import (
    CodeState,
    DistanceLedger,
    Interval,
    Malformed,
    Row,
    heuristic_outcome,
    strict_improvement_feasible,
)


class HeuristicOutcomeRecordTests(unittest.TestCase):
    def test_shape_and_defaults(self):
        record = heuristic_outcome("scan", "the universe", 7, budget=10, exhausted=False,
                                   weight=3)
        self.assertEqual(record["claim_shape"], "probabilistic")
        self.assertEqual(record["evidence_status"], "empirical")
        self.assertEqual(record["delta"], 0.0)
        self.assertFalse(record["found"])
        self.assertEqual(record["event"]["evaluated"], 7)
        self.assertEqual(record["event"]["budget"], 10)
        self.assertEqual(record["event"]["weight"], 3)
        self.assertEqual(record["statement"],
                         "no survivor found up to weight 3 among the 7 candidates evaluated")
        self.assertIn("no ledger endpoint", record["licenses"])
        self.assertIn("issue #329", record["source"])

    def test_malformed_inputs_are_refused(self):
        with self.assertRaises(Malformed):
            heuristic_outcome("scan", "u", 1, delta=1.5)
        with self.assertRaises(Malformed):
            heuristic_outcome("scan", "u", -1)
        with self.assertRaises(Malformed):
            heuristic_outcome("", "u", 1)
        with self.assertRaises(Malformed):
            heuristic_outcome("scan", "u", 1, budget=0)
        with self.assertRaises(Malformed):
            heuristic_outcome("scan", "u", 1, weight=0)

    def test_certificate_checked_is_not_a_record_status(self):
        # The status is admitted to the candidate release only; the record
        # produced here never carries it.
        record = heuristic_outcome("scan", "u", 1)
        self.assertNotEqual(record["evidence_status"], "certificate-checked")


class StrictImprovementOutcomeTests(unittest.TestCase):
    def test_enumeration_fallback_attaches_the_record(self):
        state = CodeState((0, 1), (Row("a", "X", (0,)),), frozenset(("a",)))
        result = strict_improvement_feasible(state, [1], "X", 1, allow_enumeration=True)
        outcome = result["heuristic_outcome"]
        self.assertEqual(result["reason"], "all_killed_by_enumeration")
        self.assertEqual(outcome["claim_shape"], "probabilistic")
        self.assertFalse(outcome["found"])
        self.assertEqual(outcome["event"]["weight"], 1)
        self.assertEqual(outcome["event"]["evaluated"], 2)
        self.assertIn("no survivor found up to weight 1", outcome["statement"])

    def test_a_found_survivor_is_recorded_as_found(self):
        state = CodeState((0, 1), (), frozenset())
        result = strict_improvement_feasible(state, [0], "X", 1, witnesses=None,
                                             allow_enumeration=True)
        # The cheap witness path has nothing to check, so the scan runs and
        # finds qubit 1 surviving.
        self.assertEqual(result["reason"], "survivor_found")
        self.assertTrue(result["heuristic_outcome"]["found"])

    def test_without_enumeration_no_record_is_made(self):
        state = CodeState((0, 1), (Row("a", "X", (0,)),), frozenset(("a",)))
        result = strict_improvement_feasible(state, [1], "X", 1, allow_enumeration=False)
        self.assertIsNone(result["heuristic_outcome"])


class PlannerOutcomeTests(unittest.TestCase):
    def setUp(self):
        # A valid CSS state: the X row commutes with both Z rows.
        self.state = CodeState(
            (0, 1, 2, 3),
            (Row("a9001", "X", (0, 1)), Row("b9001", "Z", (0, 1)), Row("b9002", "Z", (2, 3))),
            frozenset(("a9001", "b9001", "b9002")))
        self.state.validate()
        self.ledger = DistanceLedger(Interval(0, 3), {"X": Interval(0, 3), "Z": Interval(0, 3)})

    def test_bounded_search_carries_the_record(self):
        result = bounded_sector_search(self.state, self.ledger, "Z", budget=10)
        outcome = result["heuristic_outcome"]
        self.assertEqual(outcome["claim_shape"], "probabilistic")
        self.assertEqual(outcome["evidence_status"], "empirical")
        self.assertEqual(outcome["event"]["budget"], 10)
        self.assertEqual(outcome["event"]["evaluated"], result["budget_used"])
        self.assertEqual(outcome["event"]["exhausted"], result["exhausted"])
        self.assertEqual(outcome["found"], bool(result["candidates"]))
        self.assertEqual(outcome["statement"], search_status(result["candidates"]))

    def test_the_record_moves_no_ledger_endpoint(self):
        result = bounded_sector_search(self.state, self.ledger, "Z", budget=10)
        # Z on {0, 1, 2} commutes with the X row on {0, 1} and lies outside
        # the span of the two displayed Z rows.
        child = self.state.add_check("Z", (0, 1, 2))
        plain = self.ledger.propagate(
            {"op": "C-ADD-CHECK", "sector": "Z", "support": [0, 1, 2]}, child)
        with_record = self.ledger.propagate(
            {"op": "C-ADD-CHECK", "sector": "Z", "support": [0, 1, 2]}, child,
            hypothesis={"heuristic_outcome": result["heuristic_outcome"]})
        self.assertEqual(plain.full, with_record.full)
        self.assertEqual(plain.sector, with_record.sector)


if __name__ == "__main__":
    unittest.main()
