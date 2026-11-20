import unittest

from machine.planner import (
    pareto_rank, pareto_front, pareto_dominates,
    pareto_annotate, pareto_filter,
)
from machine.priced_calculus import Malformed
from machine.priced_calculus import (
    CodeState,
    DistanceLedger,
    Interval,
    Row,
)


def _candidate(verdict="certify", n=3, k=2, d=2, w=1, connectivity=1):
    return {"verdict": verdict, "n": n, "k": k,
            "ledger": DistanceLedger(Interval(d, d),
                                     {"X": Interval(d, d), "Z": Interval(d, d)}),
            "w": w, "connectivity": connectivity}


class TestParetoRanking(unittest.TestCase):
    def test_pareto_front_nonempty(self):
        r1 = _candidate("certify", n=3, k=2, d=2)
        r2 = _candidate("prune", n=5, k=1, d=1, w=2, connectivity=2)
        front = pareto_front([r1, r2])
        self.assertIn(r1, front)

    def test_dominated_candidate_excluded(self):
        r1 = _candidate("certify", n=3, k=2, d=2)
        r2 = _candidate("prune", n=5, k=1, d=1, w=2, connectivity=2)
        # r2 is dominated by r1 on every axis.
        self.assertTrue(pareto_dominates(r1, r2))
        front = pareto_front([r1, r2])
        self.assertNotIn(r2, front)

    def test_pareto_rank_order_and_layer(self):
        r1 = _candidate("certify", n=3, k=2, d=2)
        r2 = _candidate("prune", n=5, k=1, d=1, w=2, connectivity=2)
        out = pareto_rank([r2, r1])
        self.assertEqual(out[0], r1)
        self.assertEqual(r1["pareto_layer"], 0)
        self.assertFalse(r1["pareto_dominated"])
        self.assertEqual(r2["pareto_layer"], 1)
        self.assertTrue(r2["pareto_dominated"])

    def test_pareto_rank_returns_list(self):
        r1 = _candidate()
        out = pareto_rank([r1])
        self.assertEqual(len(out), 1)

    def test_weights_accepted(self):
        r1 = _candidate()
        out = pareto_rank([r1], weights={"n": 5.0})
        self.assertEqual(len(out), 1)

    def test_weights_unknown_key_raises(self):
        r1 = _candidate()
        with self.assertRaises(Malformed):
            pareto_rank([r1], weights={"dd": 1.0})

    def test_weights_alias_conflict_raises(self):
        r1 = _candidate()
        with self.assertRaises(Malformed):
            pareto_rank([r1], weights={"d": 1.0, "distance": 2.0})

    def test_malformed_candidate_raises(self):
        with self.assertRaises(Malformed):
            pareto_rank(["x"])
        with self.assertRaises(Malformed):
            pareto_dominates("a", _candidate())
        with self.assertRaises(Malformed):
            pareto_annotate(["x"])

    def test_pareto_annotate_non_destructive(self):
        r1 = _candidate("certify", n=3, k=2, d=2)
        r2 = _candidate("prune", n=5, k=1, d=1, w=2, connectivity=2)
        original = [r1, r2]
        annotated = pareto_annotate(original)
        self.assertIsNot(annotated, original)
        self.assertIn("pareto_dominated", annotated[0])
        # original inputs unchanged
        self.assertNotIn("pareto_dominated", r1)

    def test_pareto_filter_drop(self):
        r1 = _candidate("certify", n=3, k=2, d=2)
        r2 = _candidate("prune", n=5, k=1, d=1, w=2, connectivity=2)
        filtered = pareto_filter([r1, r2], drop=True)
        self.assertEqual(len(filtered), 1)
        self.assertEqual(filtered[0]["verdict"], r1["verdict"])
        annotated = pareto_filter([r1, r2], drop=False)
        self.assertEqual(len(annotated), 2)

    def test_stale_annotations_refreshed(self):
        a = _candidate("certify", n=4, k=1, d=2)
        b = _candidate("certify", n=3, k=2, d=3)
        pareto_rank([a, b])  # a layer 0 maybe
        # re-rank with a new dominating candidate e
        e = _candidate("certify", n=2, k=3, d=4)
        out = pareto_rank([e, a, b])
        # a must not keep stale layer 0 if dominated by e
        if pareto_dominates(e, a):
            self.assertTrue(a["pareto_dominated"] or a["pareto_layer"] > 0)

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
