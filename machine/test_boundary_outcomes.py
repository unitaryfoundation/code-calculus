"""Boundary and outcome classification guards for the consumer."""

import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

from priced_calculus import CodeState, Interval, Malformed, NoDerivation, apply_operation


class BoundaryOutcomeTests(unittest.TestCase):
    def _state(self):
        doc = {"schema_version": "0.5", "name": "x", "code_type": "CSS",
               "n": 2, "k": 1, "checks": {"X": [[0, 1]], "Z": []},
               "provenance": {"authors": ["h"], "construction": "fixture",
                              "date": "2026-10-19", "origin": "submission"}}
        return CodeState.from_challenge(doc)

    def test_apply_operation_rejects_non_object(self):
        with self.assertRaises(Malformed):
            apply_operation(self._state(), None)

    def test_apply_operation_rejects_unknown_op(self):
        with self.assertRaises(Malformed):
            apply_operation(self._state(), {"op": "NOT-AN-OP"})

    def test_interval_rejects_bool_endpoint(self):
        with self.assertRaises(ValueError):
            Interval(True, 2)

    def test_validate_rejects_bool_qubit(self):
        with self.assertRaises(Malformed):
            CodeState((True, 1), (), frozenset()).validate()

    def test_from_challenge_rejects_bad_n(self):
        doc = {"schema_version": "0.5", "name": "x", "code_type": "CSS",
               "n": 0, "k": 0, "checks": {"X": [], "Z": []},
               "provenance": {"authors": ["h"], "construction": "fixture",
                              "date": "2026-10-19", "origin": "submission"}}
        with self.assertRaises(Malformed):
            CodeState.from_challenge(doc)

    def test_mint_exhausted_raises_no_derivation(self):
        from priced_calculus import IDENTIFIERS
        st = CodeState((), (), frozenset(IDENTIFIERS))
        with self.assertRaises(NoDerivation):
            st._mint(frozenset(IDENTIFIERS))


if __name__ == "__main__":
    unittest.main()
