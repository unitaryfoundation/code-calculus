"""Regression tests for planner constructor screening and diagnostics fixes."""

import unittest

from machine.intervals import DistanceLedger, Interval
from machine.planner import bounded_sector_search, constructor_candidates, plan
from machine.priced_calculus import CodeState, Malformed, Row

HGP_REP = {"constructor": "L-HGP", "H1": [[1, 1]], "H2": [[1, 1]]}
NON_SURVIVED = ("apply_fail", "bare_qubit", "disconnected", "derive_fail",
                "min_upper", "deep_refuted", "screened", "dominated",
                "over_budget", "survived")


class PlannerScreeningAndDiagnosticsTests(unittest.TestCase):
    def _state(self):
        return CodeState(
            (0, 1, 2, 3),
            (Row("a1", "X", (0, 1, 2, 3)), Row("b1", "Z", (0, 1, 2, 3))),
            frozenset({"a1", "b1"}),
        )

    def test_disconnected_constructor_screened_when_include_disconnected_false(self):
        state = self._state()
        ledger = DistanceLedger(
            Interval(2, 2),
            {"X": Interval(2, 2), "Z": Interval(2, 2)},
        )
        res = bounded_sector_search(
            state,
            ledger,
            "X",
            target=3,
            max_depth=1,
            budget=1,
            sector_swap=False,
            include_disconnected=False,
            constructor_specs=[
                {"constructor": "L-FREE", "qubits": [0, 1]},
                {"constructor": "L-FREE", "qubits": [0]},
            ],
        )
        # Disconnected L-FREE([0, 1]) must be screened out before consuming budget,
        # so the second (1-qubit connected) spec is still evaluated within budget=1.
        records = res["constructor_candidates"]
        self.assertEqual(len(records), 2)
        self.assertFalse(records[0]["connected"])
        self.assertEqual(records[0]["screened"], "disconnected")
        self.assertTrue(records[1]["connected"])
        self.assertNotIn("screened", records[1])

    def _entry(self, spec):
        ledger = DistanceLedger(
            Interval(2, 2),
            {"X": Interval(2, 2), "Z": Interval(2, 2)},
        )
        return constructor_candidates(self._state(), ledger, [spec], target=3,
                                      objective="distance",
                                      target_sector="X")[0]

    def test_refused_ledger_input_is_not_a_failed_derivation(self):
        entry = self._entry(dict(HGP_REP, constructor_cell={
            "constructor": "L-HGP", "d2": 2, "source": "bad"}))
        self.assertTrue(entry["derived"])
        self.assertIn("ledger_refused", entry)
        self.assertNotIn("candidate", entry)
        self.assertNotIn("reason", entry)

    def test_failed_derivation_keeps_its_reason(self):
        entry = self._entry(dict(HGP_REP, H1="not a matrix",
                                 constructor_cell={"constructor": "L-HGP"}))
        self.assertFalse(entry["derived"])
        self.assertIn("reason", entry)
        self.assertNotIn("ledger_refused", entry)

    def test_supplied_interval_survives_a_second_ledger_input(self):
        interval = {"X": {"lower": 2, "upper": 2, "source": "test"}}
        alone = self._entry(dict(HGP_REP, intervals=interval))
        paired = self._entry(dict(HGP_REP, intervals=interval, lower_bounds={
            "Z": {"value": 1, "source": "test"}}))
        for entry in (alone, paired):
            x = entry["candidate"]["ledger"].sector["X"]
            self.assertEqual((x.lower, x.upper), (2, 2))

    def test_plan_refuses_a_ledger_with_zero_upper_endpoint(self):
        ledger = DistanceLedger(
            Interval(0, 0),
            {"X": Interval(0, 0), "Z": Interval(0, 0)},
        )
        with self.assertRaisesRegex(Malformed, "ledger"):
            plan(self._state(), ledger)

    def test_plan_does_not_double_count_e_local_hadamard_survived(self):
        state = CodeState(
            (0, 1, 2, 3),
            (Row("a1", "X", (0, 1, 2, 3)), Row("b1", "Z", (0, 1))),
            frozenset({"a1", "b1"}),
        )
        ledger = DistanceLedger(
            Interval(1, 2),
            {"X": Interval(3, 4), "Z": Interval(1, 2)},
        )
        diag = {}
        plan(
            state,
            ledger,
            target=3,
            sector_targeted=True,
            target_sector="Z",
            sector_swap=True,
            diagnostics=diag,
        )
        had = diag["E-LOCAL-HADAMARD"]
        self.assertEqual(had["enumerated"], 1)
        # Every enumerated swap is accounted for exactly once.
        self.assertEqual(sum(had[r] for r in NON_SURVIVED), had["enumerated"])


if __name__ == "__main__":
    unittest.main()
