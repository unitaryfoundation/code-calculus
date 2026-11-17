import unittest

from machine.priced_calculus import CodeState, Row
from machine.oracle import (
    ORACLE_N_CEILING,
    OracleTooLarge,
    exact_distance,
    exact_distances,
)


class TestOracle(unittest.TestCase):
    def test_empty_code_distance_is_one(self):
        state = CodeState((0, 1), (), frozenset())
        result = exact_distances(state)
        self.assertEqual(result["X"], 1)
        self.assertEqual(result["Z"], 1)
        self.assertEqual(result["d"], 1)

    def test_single_check_code(self):
        state = CodeState(
            (0, 1),
            (Row("a", "X", (0,)),),
            frozenset(("a",)),
        )
        result = exact_distances(state)
        # qubit 1 is a bare logical on both sectors
        self.assertEqual(result["d"], 1)

    def test_ceiling_refusal(self):
        state = CodeState(tuple(range(ORACLE_N_CEILING + 1)), (), frozenset())
        with self.assertRaises(OracleTooLarge):
            exact_distances(state)

    def test_exact_distance_convenience(self):
        state = CodeState((0, 1), (), frozenset())
        self.assertEqual(exact_distance(state), 1)

    def test_no_consumer_import(self):
        import sys
        saved = {}
        for name in ("machine.oracle", "oracle"):
            if name in sys.modules:
                saved[name] = sys.modules.pop(name)
        try:
            import machine.priced_calculus as pc
            import machine.planner as pl
            self.assertNotIn("oracle", getattr(pc, "__dict__", {}))
            self.assertNotIn("oracle", getattr(pl, "__dict__", {}))
            self.assertNotIn("machine.oracle", sys.modules)
            self.assertNotIn("oracle", sys.modules)
        finally:
            sys.modules.update(saved)

    def test_agrees_with_replay_enumerator(self):
        import os
        import sys
        sys.path.insert(0, os.path.join(os.path.dirname(__file__), "experiments"))
        from machine.priced_calculus import CodeState, Row
        from machine.oracle import exact_distances as oracle_exact
        import issue21_challenge_replay as replay
        # simple state
        state = CodeState((0, 1, 2), (Row("r", "X", (0, 1)),), frozenset(("r",)))
        a = oracle_exact(state)
        b = replay.exact_distances(state)
        self.assertEqual(a, b)


if __name__ == "__main__":
    unittest.main()
