import unittest

from machine.planner import pareto_rank, pareto_front, pareto_dominates
from machine.priced_calculus import (
    CodeState,
    DistanceLedger,
    Interval,
    Row,
)


class TestParetoRanking(unittest.TestCase):
    def test_pareto_front_nonempty(self):
        r1 = {"verdict": "certify", "n": 3, "k": 2,
              "ledger": DistanceLedger(Interval(2, 2),
                                     {"X": Interval(2, 2), "Z": Interval(2, 2)}),
              "w": 1, "connectivity": 1}
        r2 = {"verdict": "prune", "n": 5, "k": 1,
              "ledger": DistanceLedger(Interval(1, 1),
                                     {"X": Interval(1, 1), "Z": Interval(1, 1)}),
              "w": 2, "connectivity": 2}
        front = pareto_front([r1, r2])
        self.assertIn(r1, front)

    def test_pareto_rank_returns_list(self):
        r1 = {"verdict": "certify", "n": 3, "k": 2,
              "ledger": DistanceLedger(Interval(2, 2),
                                     {"X": Interval(2, 2), "Z": Interval(2, 2)}),
              "w": 1, "connectivity": 1}
        out = pareto_rank([r1])
        self.assertEqual(len(out), 1)

    def test_weights_accepted(self):
        r1 = {"verdict": "certify", "n": 3, "k": 2,
              "ledger": DistanceLedger(Interval(2, 2),
                                     {"X": Interval(2, 2), "Z": Interval(2, 2)}),
              "w": 1, "connectivity": 1}
        out = pareto_rank([r1], weights={"n": 5.0})
        self.assertEqual(len(out), 1)

    def test_plan_pareto_ranking(self):
        from machine.planner import plan
        state = CodeState(
            (0, 1, 2),
            (Row("a", "X", (0, 1)), Row("b", "Z", (0, 1))),
            frozenset(("a", "b")),
        )
        ledger = DistanceLedger(Interval(0, 3),
                                {"X": Interval(0, 3), "Z": Interval(0, 3)})
        res = plan(state, ledger, 3, ranking="pareto")
        self.assertIsInstance(res, list)


if __name__ == "__main__":
    unittest.main()
