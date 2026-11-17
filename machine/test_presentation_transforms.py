"""Tests for the regression fixture of issue #447.

The fixture pins that Hamming weight is not invariant under a single CNOT
layer, and that the single-layer lower bound / two-layer sharpness of a
disguised direct sum hold as documented. A passing run is evidence for the
conditions in `design/PRESENTATION_TRANSFORMS.md`, not a proof, and admits
no judgment.
"""

import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "experiments"))

from presentation_transforms import (  # noqa: E402
    cnot_transform_row,
    hamming_weight,
    direct_sum_lower_bound,
    two_layer_sharpness,
)


class WeightNonInvariance(unittest.TestCase):
    def test_cnot_changes_hamming_weight(self):
        # A weight-2 Z-check on qubits {1,2}; CNOT(0 -> 1) adds qubit 0.
        row = [0, 1, 1, 0]
        transformed = cnot_transform_row(row, control=0, target=1)
        self.assertNotEqual(hamming_weight(row), hamming_weight(transformed))
        self.assertEqual(hamming_weight(transformed), 3)  # {0,1,2}

    def test_weight_can_increase(self):
        row = [0, 1, 0, 0]
        transformed = cnot_transform_row(row, control=0, target=1)
        self.assertEqual(hamming_weight(row), 1)
        self.assertEqual(hamming_weight(transformed), 2)


class DirectSumBounds(unittest.TestCase):
    def test_single_layer_lower_bound(self):
        self.assertEqual(direct_sum_lower_bound(3, 5), 3)
        self.assertEqual(direct_sum_lower_bound(7, 2), 2)

    def test_two_layer_sharpness(self):
        self.assertEqual(two_layer_sharpness(), 1)


if __name__ == "__main__":
    unittest.main()