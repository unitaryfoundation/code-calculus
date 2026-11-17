"""Class pairs under `E-GLUE` (issue #328).

`spec/OPERATIONAL_SEMANTICS.md` section 4.33: under the admitted transition
no glued logical is re-exposed (trivial on both factors), and the glued
sector distance is the least sum of factor class weights over the class
pairs that commute with the opposite-sector seam checks and are not
absorbed by the same-sector seam checks. The experiment is
`machine/experiments/glue_class_pairs.py`; these tests pin the two-qubit
factors of `test_glue_witnesses.py` under three seams and a seeded sweep.
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
from machine.oracle import exact_distances  # noqa: E402
from machine.priced_calculus import CodeState, Row  # noqa: E402


def factor(labels, row_id):
    """Two qubits with one Z row on both: k = 1, d_X = 2, d_Z = 1."""
    a, b = labels
    state = CodeState((a, b), (Row(row_id, "Z", (a, b)),), frozenset((row_id,)))
    state.validate()
    return state


class GlueClassPairTests(unittest.TestCase):
    def setUp(self):
        self.left = factor((0, 1), "b1")
        self.right = factor((2, 3), "d1")

    def glued(self, *seams):
        return pairs.glue(self.left, self.right, list(seams))

    def test_factor_class_data(self):
        data, _basis = pairs.class_data(self.left, "Z")
        self.assertEqual(sorted(weight for weight, _ in data.values()), [0, 1])
        data, _basis = pairs.class_data(self.left, "X")
        self.assertEqual(sorted(weight for weight, _ in data.values()), [0, 2])

    def test_an_x_seam_on_all_four_qubits_raises_d_z_to_two(self):
        # Every weight-one Z anticommutes with the seam, so no pure pair
        # survives and the minimum is the mixed pair (1, 1): 1 + 1 = 2.
        child = self.glued(("X", [0, 1, 2, 3]))
        formula = pairs.class_pair_distance(self.left, self.right, child, "Z")
        self.assertEqual(formula["value"], 2)
        self.assertFalse(formula["pure_minimum_survives"])
        self.assertEqual(exact_distances(child)["Z"], 2)
        self.assertEqual(pairs.re_exposed_logicals(self.left, self.right, child, "Z"), [])
        # The X sector is untouched by an X seam except for absorption; the
        # seam's class pair is (1, 1), so the pure pairs survive with d_X = 2.
        formula_x = pairs.class_pair_distance(self.left, self.right, child, "X")
        self.assertEqual(formula_x["value"], 2)
        self.assertTrue(formula_x["pure_minimum_survives"])
        self.assertEqual(exact_distances(child)["X"], 2)

    def test_a_z_seam_across_the_factors_keeps_d_z_at_one(self):
        child = self.glued(("Z", [1, 2]))
        formula = pairs.class_pair_distance(self.left, self.right, child, "Z")
        self.assertEqual(formula["value"], 1)
        self.assertTrue(formula["pure_minimum_survives"])
        self.assertEqual(exact_distances(child)["Z"], 1)
        # The seam's class pair (1, 1) is absorbed; the pure pairs are not.
        self.assertEqual(formula["absorbed"], 2)
        self.assertEqual(formula["pairs_surviving"], 2)

    def test_a_z_seam_equal_to_one_factor_witness_leaves_the_other(self):
        child = self.glued(("Z", [0]))
        formula = pairs.class_pair_distance(self.left, self.right, child, "Z")
        self.assertEqual(formula["value"], 1)
        self.assertTrue(formula["pure_minimum_survives"])
        self.assertEqual(exact_distances(child)["Z"], 1)
        # (1, 0) is absorbed; (0, 1) and (1, 1) survive.
        self.assertEqual(formula["pairs_surviving"], 2)

    def test_no_seam_is_the_direct_sum(self):
        child = self.glued()
        for sector, expected in (("X", 2), ("Z", 1)):
            formula = pairs.class_pair_distance(self.left, self.right, child, sector)
            self.assertEqual(formula["value"], expected)
            self.assertEqual(exact_distances(child)[sector], expected)

    def test_seeded_sweep_finds_no_re_exposed_class_and_no_mismatch(self):
        report = pairs.run(seed=328, trials=40)
        self.assertEqual(report["mismatches"], [])
        self.assertEqual(report["re_exposed_total"], 0)
        self.assertGreater(report["raised_above_factor_minimum"], 0)
        self.assertGreater(report["equal_to_factor_minimum"], 0)


if __name__ == "__main__":
    unittest.main()
