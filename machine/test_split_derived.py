"""The separating deletion behind a candidate `E-SPLIT`.

`the E-split proposal note` states the candidate as a derived command over
`C-DELETE-CHECK`. The experiment is `machine/experiments/split_derived.py`;
these tests pin the examples the proposal cites and a seeded sweep. They
test the oracle-side statements only: no transition is added to the
consumer, and agreement is evidence, not a proof.
"""

import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.join(HERE, "experiments")
for path in (EXP, HERE):
    if path not in sys.path:
        sys.path.insert(0, path)

import glue_class_pairs as pairs  # noqa: E402
import split_derived as split  # noqa: E402
from machine.oracle import exact_distances  # noqa: E402
from machine.priced_calculus import CodeState, NoDerivation, Row  # noqa: E402


def factor(labels, row_id):
    """Two qubits with one Z row on both: k = 1, d_X = 2, d_Z = 1."""
    a, b = labels
    state = CodeState((a, b), (Row(row_id, "Z", (a, b)),), frozenset((row_id,)))
    state.validate()
    return state


class SplitOfAGlueTests(unittest.TestCase):
    """The section 4.33 counterexample, glued and then split."""

    def setUp(self):
        self.left = factor((0, 1), "b1")
        self.right = factor((2, 3), "d1")
        self.glued = pairs.glue(self.left, self.right, [("X", [0, 1, 2, 3])])
        self.seam_ids = [row.id for row in
                         pairs.seam_rows(self.left, self.right, self.glued)]

    def test_glued_distances(self):
        exact = exact_distances(self.glued)
        self.assertEqual((self.glued.k(), exact["X"], exact["Z"]), (1, 2, 2))

    def test_split_returns_the_direct_sum_rows(self):
        child = split.split(self.glued, self.seam_ids)
        summed = CodeState.direct_sum(self.left, self.right)
        self.assertEqual(child.rows, summed.rows)
        self.assertEqual(set(child.Q), set(summed.Q))

    def test_used_grows_by_the_seam_identifier(self):
        child = split.split(self.glued, self.seam_ids)
        summed = CodeState.direct_sum(self.left, self.right)
        self.assertEqual(child.used, summed.used | frozenset(self.seam_ids))
        self.assertNotEqual(child.used, summed.used)

    def test_lower_endpoint_does_not_carry(self):
        # d_Z falls from 2 to 1: the deleted X row exposes a weight-one Z class.
        result = split.check_instance(self.glued, [0, 1])
        self.assertTrue(result["ok"])
        cell = result["sectors"]["Z"]
        self.assertEqual((cell["d_parent"], cell["d_child"]), (2, 1))
        self.assertEqual((cell["w_del"], cell["w_exp"]), (None, 1))
        self.assertEqual((cell["d_A"], cell["d_B"]), (1, 1))

    def test_promoted_row_does_not_lower_the_x_distance(self):
        result = split.check_instance(self.glued, [0, 1])
        cell = result["sectors"]["X"]
        self.assertEqual((cell["d_parent"], cell["d_child"]), (2, 2))
        self.assertEqual(cell["w_del"], 4)

    def test_glue_inverse_record(self):
        result = split.check_glue_inverse(self.left, self.right, [("X", [0, 1, 2, 3])])
        self.assertTrue(result["ok"])
        self.assertTrue(result["used_grows"])


class DisplayDependenceTests(unittest.TestCase):
    """One row space, two displays, different numbers of crossing rows."""

    def state(self, second):
        rows = (Row("a1", "X", (0, 1)), Row("a2", "X", second))
        result = CodeState((0, 1, 2, 3), rows, frozenset(("a1", "a2")))
        result.validate()
        return result

    def test_crossing_count_depends_on_the_display(self):
        crossing = self.state((0, 1, 2, 3))
        separated = self.state((2, 3))
        self.assertEqual(len(split.crossing_rows(crossing, [0, 1])), 1)
        self.assertEqual(len(split.crossing_rows(separated, [0, 1])), 0)

    def test_cut_rank_is_a_property_of_the_row_space(self):
        for second in ((0, 1, 2, 3), (2, 3)):
            self.assertEqual(split.cut_rank(self.state(second), [0, 1], "X"), 0)

    def test_split_of_the_crossing_display_costs_a_logical_qubit(self):
        parent = self.state((0, 1, 2, 3))
        result = split.check_instance(parent, [0, 1])
        self.assertTrue(result["ok"])
        self.assertEqual(result["cut"], 1)
        child = split.split(parent, ["a2"])
        self.assertEqual(child.k(), parent.k() + 1)


class ApplicabilityTests(unittest.TestCase):
    def setUp(self):
        left = factor((0, 1), "b1")
        right = factor((2, 3), "d1")
        self.glued = pairs.glue(left, right, [("X", [0, 1, 2, 3])])

    def test_undisplayed_identifier_has_no_derivation(self):
        with self.assertRaises(NoDerivation):
            split.split(self.glued, ["zz9"])

    def test_repeated_identifier_has_no_derivation(self):
        seam = [row.id for row in self.glued.rows if row.sector == "X"]
        with self.assertRaises(NoDerivation):
            split.split(self.glued, seam + seam)

    def test_cut_missing_a_crossing_row_is_not_separated(self):
        child = split.split(self.glued, ["b1"])
        self.assertFalse(split.is_separated(child, [0, 1]))

    def test_empty_cut_on_a_separated_state_is_the_identity(self):
        summed = CodeState.direct_sum(factor((0, 1), "b1"), factor((2, 3), "d1"))
        self.assertTrue(split.is_separated(summed, [0, 1]))
        self.assertEqual(split.split(summed, []), summed)


class SweepTests(unittest.TestCase):
    def test_seeded_sweep(self):
        report = split.run(seed=546, trials=120)
        self.assertEqual(report["mismatches"], [])
        self.assertEqual(report["glue_mismatches"], [])
        # The sweep is not vacuous: distances fall, extra rows are deleted,
        # and displays exceed the cut rank.
        self.assertGreater(report["strict_drops"], 0)
        self.assertGreater(report["extra_rows_deleted"], 0)
        self.assertGreater(report["above_cut_rank"], 0)


if __name__ == "__main__":
    unittest.main()
