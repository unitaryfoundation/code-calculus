"""Tests for the CSS-preserving column CNOT/SWAP transformation (issue #570)."""

import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)
if HERE not in sys.path:
    sys.path.insert(0, HERE)

from css_preserving_cnot_swap import (
    validate_u,
    transform_matrices,
    rho_z,
    rho_z_inv,
    rho_x,
    rho_x_inv,
    k_of,
    n_of,
    distance_window,
    record,
)


class Validation(unittest.TestCase):
    def test_identity_accepted(self):
        U = [[1, 0], [0, 1]]
        self.assertEqual(validate_u(U), U)

    def test_singular_rejected(self):
        with self.assertRaises(ValueError):
            validate_u([[1, 1], [1, 1]])

    def test_n_mismatch(self):
        with self.assertRaises(ValueError):
            validate_u([[1, 0], [0, 1]], 3)


class Transform(unittest.TestCase):
    def test_identity_preserves(self):
        HX = [[1, 1, 0], [0, 1, 1]]
        HZ = [[1, 0, 1]]
        Xp, Zp = transform_matrices(HX, HZ, [[1, 0, 0], [0, 1, 0], [0, 0, 1]])
        self.assertEqual(Xp, HX)
        self.assertEqual(Zp, HZ)

    def test_n_and_k_preserved(self):
        HX = [[1, 1, 0, 0]]
        HZ = [[0, 0, 1, 1]]
        U = [[1, 1, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]
        Xp, Zp = transform_matrices(HX, HZ, U)
        self.assertEqual(n_of(Xp, Zp), n_of(HX, HZ))
        self.assertEqual(k_of(Xp, Zp), k_of(HX, HZ))

    def test_orthogonality_preserved(self):
        HX = [[1, 1, 0, 0]]
        HZ = [[0, 0, 1, 1]]
        U = [[1, 1, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]
        Xp, Zp = transform_matrices(HX, HZ, U)
        for x in Xp:
            for z in Zp:
                inter = sum(1 for a, b in zip(x, z) if a and b)
                self.assertEqual(inter % 2, 0)

    def test_hamming_weight_can_change(self):
        HX = [[1, 1, 0, 0]]
        U = [[1, 1, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]
        Xp, _ = transform_matrices(HX, [], U)
        self.assertNotEqual(sum(Xp[0]), sum(HX[0]))


class Rho(unittest.TestCase):
    def test_rho_identity(self):
        U = [[1, 0], [0, 1]]
        self.assertEqual(rho_z(U), 1)
        self.assertEqual(rho_z_inv(U), 1)
        self.assertEqual(rho_x(U), 1)
        self.assertEqual(rho_x_inv(U), 1)

    def test_distance_window(self):
        self.assertEqual(distance_window(4, 2, 2), (2, 8))


class Record(unittest.TestCase):
    def test_record_keys(self):
        rec = record(U=[[1, 0], [0, 1]], d_X=3, d_Z=5)
        self.assertTrue(rec["hamming_weight_noninvariant"])
        self.assertFalse(rec["generic_cnot_layer_zero_price"])
        self.assertEqual(rec["d_X_window"], [3, 3])
        self.assertEqual(rec["d_Z_window"], [5, 5])
        self.assertIn("rho_X", rec)
        self.assertIn("rho_X_inv", rec)

    def test_review_x_window(self):
        U = [[0, 1, 1], [0, 1, 0], [1, 1, 1]]
        rec = record(U=U, d_X=3)
        # window upper uses rho_X, lower uses rho_X_inv
        self.assertEqual(rec["d_X_window"][1], rec["rho_X"] * 3)


if __name__ == "__main__":
    unittest.main()
