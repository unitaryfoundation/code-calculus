"""Tests for the mapping-cone checks of issue #449.

The harness enumerates small cones against the statements of
`design/MAPPING_CONE_CONSTRUCTOR.md`. A passing run is evidence for the
note's derivations, not a proof, and admits nothing.
"""

import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "experiments"))

from mapping_cone import (  # noqa: E402
    ChainMap,
    formula_gap_instance,
    norm_gap_instance,
    sweep,
)


class Construction(unittest.TestCase):
    def test_premise_is_checked(self):
        # d_b f1 = 1 and f0 d_a = 0: not a chain map.
        bad = ChainMap((1, 1, 1, 1), [0], [1], [1], [0])
        self.assertFalse(bad.is_chain_map())

    def test_four_two_two(self):
        cone = norm_gap_instance()
        self.assertTrue(cone.is_chain_map())
        self.assertEqual(cone.display(), ([0b1111], [0b1111]))
        self.assertEqual((cone.n(), cone.k(), cone.k_from_sequence()), (4, 2, 2))
        self.assertEqual((cone.z_distance(), cone.x_distance()), (2, 2))

    def test_zero_map_is_a_direct_sum(self):
        # f = 0: the cone is the code with Z-rows from d_a and X-rows from
        # d_b on disjoint blocks. A is the two-bit repetition check read as
        # a boundary, B is the same read as a coboundary.
        cone = ChainMap((1, 2, 2, 1), [0b11], [1, 1], [0], [0, 0])
        self.assertEqual(cone.display(), ([0b1100], [0b0011]))
        self.assertEqual(cone.k(), 2)
        self.assertEqual((cone.from_b(), cone.from_a(), cone.z_distance()), (2, 1, 1))


class RecordedFormula(unittest.TestCase):
    def test_formula_is_not_the_distance_in_general(self):
        cone = formula_gap_instance()
        self.assertTrue(cone.is_chain_map())
        self.assertFalse(cone.h0_injective())
        self.assertEqual((cone.from_b(), cone.from_a(), cone.z_distance()), (2, 1, 1))

    def test_formula_is_the_distance_when_h0_is_injective(self):
        cone = norm_gap_instance()
        self.assertFalse(cone.h0_injective())
        # Injective case: A_0 is all boundary.
        injective = ChainMap((1, 1, 2, 1), [1], [1, 1], [0b11], [0])
        self.assertTrue(injective.is_chain_map())
        self.assertTrue(injective.h0_injective())
        self.assertIsNone(injective.from_a())
        self.assertEqual(injective.z_distance(), injective.from_b())


class Pushout(unittest.TestCase):
    def test_identification_of_complexes(self):
        for cone in (formula_gap_instance(), norm_gap_instance()):
            self.assertTrue(cone.pushout_agrees())

    def test_quotient_norm_is_not_the_weight(self):
        cone = norm_gap_instance()
        cycle = cone.pack(0, 0b11)
        self.assertEqual(bin(cycle).count("1"), 2)
        self.assertEqual(cone.quotient_weight(cycle), 1)
        self.assertEqual(cone.z_distance(), 2)
        self.assertEqual(cone.z_distance_quotient_norm(), 1)


class Sweep(unittest.TestCase):
    def test_no_disagreement(self):
        stats = sweep(seed=449, trials=300, max_dim=3)
        self.assertEqual(stats["disagreements"], [])
        for key in (
            "k_positive",
            "formula_is_distance",
            "formula_is_not_distance",
            "h0_injective",
            "norm_differs",
        ):
            self.assertGreater(stats[key], 0, key)


if __name__ == "__main__":
    unittest.main()
