"""Refutation-grade conformance for the priced consumer's conditional cells."""

import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

from priced_calculus import (
    CodeState,
    DistanceLedger,
    Interval,
    NoDerivation,
    Row,
    apply_operation,
)


class ConditionalCellFailureTests(unittest.TestCase):
    def test_strict_improvement_missing_enumeration_id_is_no_derivation(self):
        state = CodeState((0, 1), (Row("a9001", "X", (0,)),), frozenset(("a9001",)))
        operation = {"op": "C-ADD-CHECK", "sector": "X", "support": [1]}
        exact_input = DistanceLedger(Interval(1, 1), {"X": Interval(1, 1), "Z": Interval(1, 1)})
        child = state.add_check("X", [1])
        with self.assertRaises(NoDerivation):
            exact_input.propagate(
                operation,
                child,
                hypothesis={"strict_improvement": {
                    "base_distance": 1,
                    "all_minimum_classes_killed": True,
                }},
            )

    def test_graft_price_missing_evidence_is_no_derivation(self):
        state = CodeState(
            (0, 1, 2, 3, 4),
            (Row("a1", "X", (0, 1)), Row("a2", "X", (0, 2, 3, 4)),
             Row("b1", "Z", (0, 1, 2)), Row("b2", "Z", (3, 4))),
            frozenset(("a1", "a2", "b1", "b2")),
        )
        operation = {
            "op": "E-GRAFT",
            "qubit": 0,
            "sector": "X",
            "ordered_row_ids": ["a1", "a2"],
        }
        child = apply_operation(state, operation)
        initial = DistanceLedger(Interval(2, 2), {"X": Interval(2, 2), "Z": Interval(2, 2)})
        with self.assertRaises(NoDerivation):
            initial.propagate(
                operation,
                child,
                hypothesis={"graft_price": {"w_expose": 2}},
            )

    def test_direct_sum_extinction_mismatched_factor_is_no_derivation(self):
        state = CodeState(
            (0, 1, 2, 3, 4, 5),
            (Row("a9001", "X", (0, 1)),
             Row("a9002", "X", (2, 3, 4, 5)),
             Row("b9002", "Z", (2, 3, 4, 5))),
            frozenset(("a9001", "a9002", "b9002")),
        )
        child = state.add_check("Z", (0, 1))
        operation = {"op": "C-ADD-CHECK", "sector": "Z", "support": [0, 1]}
        ledger = DistanceLedger(Interval(1, 1), {"X": Interval(1, 1), "Z": Interval(1, 1)})
        with self.assertRaises(NoDerivation):
            ledger.propagate(
                operation,
                child,
                hypothesis={"direct_sum_extinction": {
                    "base_distance": 1,
                    "factor_distance": 1,
                    "evidence": "not an improvement",
                }},
                parent_state=state,
            )

    def test_sector_gauging_missing_evidence_is_no_derivation(self):
        state = CodeState((0, 1), (Row("a9001", "X", (0,)),), frozenset(("a9001",)))
        operation = {"op": "C-ADD-CHECK", "sector": "X", "support": [1]}
        exact_input = DistanceLedger(Interval(1, 1), {"X": Interval(1, 1), "Z": Interval(1, 1)})
        child = state.add_check("X", [1])
        with self.assertRaises(NoDerivation):
            exact_input.propagate(
                operation,
                child,
                hypothesis={"sector_gauging": {"w_X": 2}},
            )


if __name__ == "__main__":
    unittest.main()
