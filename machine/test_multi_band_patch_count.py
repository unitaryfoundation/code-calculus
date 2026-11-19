"""Tests for the multi-band patch-count metadata of issue #448.

Arithmetic sanity checks of the recorded formula and of the reconstructed
display. Evidence for the note's transcription only; not a proof and not an
admission.
"""

import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "experiments"))

from multi_band_patch_count import (  # noqa: E402
    patch_count,
    reconstruct_display,
    reconstruct_check_structure,
    sweep,
)


class Formula(unittest.TestCase):
    def test_known_values(self):
        self.assertEqual(patch_count(0, 3), 0)
        self.assertEqual(patch_count(1, 3), 3 - 0)
        self.assertEqual(patch_count(2, 3), 6 - 1)
        self.assertEqual(patch_count(3, 3), 9 - 1)
        self.assertEqual(patch_count(4, 3), 12 - 2)
        self.assertEqual(patch_count(5, 2), 10 - 2)

    def test_non_negative(self):
        for rows in range(0, 12):
            for m in range(1, 8):
                self.assertGreaterEqual(patch_count(rows, m), 0)


class Reconstruction(unittest.TestCase):
    def test_logical_dim_matches_count(self):
        for rows in range(0, 8):
            for m in range(1, 6):
                n, r = reconstruct_display(rows, m)
                self.assertEqual(n - r, patch_count(rows, m))

    def test_sweep_consistent(self):
        s = sweep()
        self.assertTrue(s["all_consistent"])

    def test_check_structure_logical_dim(self):
        for rows in range(0, 8):
            for m in range(1, 6):
                cs = reconstruct_check_structure(rows, m)
                self.assertEqual(cs["logical_dim"], patch_count(rows, m))
                self.assertTrue(cs["consistent"])

    def test_check_structure_orthogonal(self):
        for rows in range(2, 8):
            for m in range(1, 6):
                cs = reconstruct_check_structure(rows, m)
                for xr in cs["x_rows"]:
                    for zr in cs["z_rows"]:
                        overlap = len(set(xr) & set(zr))
                        self.assertEqual(overlap % 2, 0)


if __name__ == "__main__":
    unittest.main()
