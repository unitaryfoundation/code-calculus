"""Tests for the one-shot level-map transport.

Checks the conditional transport record (strict validation, no distance lower
bound, bare sheet floor distinct from block-length ceiling, Remark 39 seed
local triviality, imported-lemma hypothesis status) and the separate finite
``GF(2)`` chain-complex tensor product ``C (x) R`` probe. Evidence only; not a
proof.
"""

import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(HERE, "experiments"))

from one_shot_level_map_transport import (  # noqa: E402
    DISTANCE_LOWER_BOUND_AVAILABLE,
    TRANSPORT_DIRECTION,
    build_hollowed_tensor_level_map,
    distance_lower_bound,
    dual_hollowed_tensor_level_map,
    empirical_gamma_bar_probe,
    empirical_probe,
    imported_lemma_status,
    one_shot_level_map_transport,
    repetition_tensor_code,
    seed_locally_trivial,
    sheet_lower_floor,
    sweep,
)


class Transport(unittest.TestCase):
    def test_sheet_lower_floor(self):
        self.assertEqual(sheet_lower_floor(5, 3), 15)
        self.assertEqual(sheet_lower_floor(7, 2, levels=2), 28)
        self.assertEqual(sheet_lower_floor(3, 2, levels=3), 24)

    def test_no_distance_lower_bound(self):
        self.assertEqual(TRANSPORT_DIRECTION, "upper ceiling")
        self.assertIs(DISTANCE_LOWER_BOUND_AVAILABLE, False)
        self.assertIsNone(distance_lower_bound())

    def test_lemmas_are_hypotheses(self):
        st = imported_lemma_status()
        self.assertFalse(st["discharged"])
        self.assertFalse(st["empirical_proof"])

    def test_seed_locally_trivial_remark39(self):
        self.assertTrue(seed_locally_trivial(5, 4))
        self.assertFalse(seed_locally_trivial(4, 4))
        self.assertFalse(seed_locally_trivial(3, 4))
        for bad in ((0, 4), (4, -1), (True, 1), (4, False)):
            with self.assertRaises(ValueError):
                seed_locally_trivial(*bad)

    def test_strict_validation_refuses_invalid_inputs(self):
        for bad_args in (
            (0, 5, 2, 1),
            (-3, 1, 2, 1),
            (True, 1, 2, 1),
            (5, -1, 2, 1),
            (5, 6, 2, 1),
            (5, False, 2, 1),
            (5, 2, 1, 1),
            (5, 2, 0, 1),
            (5, 2, 2, 0),
            ("x", 2, 2, 1),
        ):
            with self.assertRaises(ValueError):
                one_shot_level_map_transport(*bad_args)

        with self.assertRaises(TypeError):
            one_shot_level_map_transport()
        with self.assertRaises(ValueError):
            sheet_lower_floor(5, 1, levels=1)
        with self.assertRaises(ValueError):
            sheet_lower_floor(0, 2, levels=1)
        with self.assertRaises(ValueError):
            one_shot_level_map_transport(5, 2, m=2, d_error=3)
        with self.assertRaises(ValueError):
            one_shot_level_map_transport(5, 2, m=2, max_x_weight=2)

    def test_transport_record(self):
        rec = one_shot_level_map_transport(
            7, 1, m=3, levels=1, d_error=3, max_x_weight=4
        )
        self.assertEqual(rec["n_source"], 7)
        self.assertEqual(rec["k_source"], 1)
        self.assertEqual(rec["k_amplified"], 1)
        self.assertTrue(rec["k_preserved"])
        self.assertIsNone(rec["n_amplified"])
        self.assertEqual(rec["n_sheet_lower_floor"], 21)
        self.assertEqual(rec["transport_direction"], "upper ceiling")
        self.assertIsNone(rec["distance_lower_bound"])
        self.assertFalse(rec["distance_lower_bound_available"])
        self.assertFalse(rec["seed_locally_trivial"])
        self.assertEqual(rec["status"], "conditional")

        multi = one_shot_level_map_transport(5, 2, m=2, levels=2)
        self.assertEqual(multi["n_sheet_lower_floor"], 20)
        self.assertIsNone(multi["n_amplified"])
        self.assertNotIn("seed_locally_trivial", multi)


class ChainComplexRepetitionTensor(unittest.TestCase):
    def test_four_qubit_code_k_preserved_and_n_exceeds_xm(self):
        out = repetition_tensor_code(
            4,
            hx_rows=[[0, 1, 2, 3]],
            hz_rows=[[0, 1, 2, 3]],
            m=3,
        )
        self.assertTrue(out["commutes"])
        self.assertEqual(out["k_source"], 2)
        self.assertEqual(out["k_amplified"], 2)
        self.assertEqual(out["n_amplified"], 3 * 4 + 2 * 1)
        self.assertGreater(out["n_amplified"], 3 * 4)
        self.assertTrue(out["k_preserved"])
        self.assertTrue(out["n_inflated"])

    def test_steane_code_k_preserved(self):
        steane_rows = [
            [0, 2, 4, 6],
            [1, 2, 5, 6],
            [3, 4, 5, 6],
        ]
        for m in (2, 3, 4):
            out = repetition_tensor_code(7, steane_rows, steane_rows, m=m)
            self.assertTrue(out["commutes"])
            self.assertEqual(out["k_source"], 1)
            self.assertEqual(out["k_amplified"], 1)
            self.assertEqual(out["n_amplified"], 7 * m + 3 * (m - 1))
            self.assertGreater(out["n_amplified"], 7 * m)

    def test_redundant_seed_checks_preserve_k(self):
        out = repetition_tensor_code(
            4,
            hx_rows=[[0, 1, 2, 3], [0, 1, 2, 3]],
            hz_rows=[[0, 1], [2, 3], [0, 1, 2, 3]],
            m=2,
        )
        self.assertTrue(out["commutes"])
        self.assertEqual(out["k_source"], 1)
        self.assertEqual(out["k_amplified"], 1)

    def test_refuses_invalid_or_noncommuting_seed(self):
        with self.assertRaises(ValueError):
            repetition_tensor_code(3, [[0, 1]], [[1, 2]], m=2)
        with self.assertRaises(ValueError):
            repetition_tensor_code(4, [[0, 0, 1, 2]], [[0, 1, 2, 3]], m=2)
        with self.assertRaises(ValueError):
            repetition_tensor_code(4, [[0, 4]], [], m=2)
        with self.assertRaises(ValueError):
            repetition_tensor_code(4, [[0, 1, 2, 3]], [[0, 1, 2, 3]], m=1)


class Empirical(unittest.TestCase):
    def test_probe_separated(self):
        p = empirical_probe(seed=1, trials=25)
        self.assertTrue(p["empirical"])
        self.assertTrue(p["all_consistent"])
        self.assertTrue(p["chain_complex_consistent"])
        self.assertIn("conditional_theorem", p)
        self.assertIn("not Def. 111/116", p["construction_scope"])
        self.assertEqual(p["transport_direction"], "upper ceiling")
        with self.assertRaises(ValueError):
            empirical_probe(seed=True, trials=10)
        with self.assertRaises(ValueError):
            empirical_probe(seed=1, trials=0)

    def test_sweep(self):
        s = sweep(seed=1, trials=25)
        self.assertTrue(s["all_consistent"])
        self.assertEqual(s["disagreements"], [])

    def test_gamma_bar_toric_preserves_homologies_and_sparsity(self):
        out = empirical_gamma_bar_probe(toric_sizes=((2, 3), (3, 3)), sheets=(2, 3))
        self.assertTrue(out["empirical"])
        self.assertTrue(out["all_consistent"])
        self.assertEqual(out["trials"], 4)
        self.assertEqual(out["transport_direction"], "upper ceiling")
        self.assertFalse(out["distance_lower_bound_available"])
        for rec in out["results"]:
            self.assertEqual(rec["k_source"], 2)
            self.assertEqual(rec["k_amplified"], 2)
            self.assertTrue(rec["commutes"])
            self.assertTrue(rec["meta_checks_commute"])
            self.assertTrue(rec["hx_preserved"])
            self.assertTrue(rec["hz_preserved"])
            self.assertTrue(rec["n_exceeds_xm"])
            self.assertTrue(rec["sparsity_within_lemma_117"])

    def test_dual_gamma_bar_and_hypotheses_refusal(self):
        # 2x3 toric seed satisfies Hypotheses 102 and 103 in both dual orientations.
        def qh(r, c):
            return (r % 2) * 3 + (c % 3)

        def qv(r, c):
            return 6 + (r % 2) * 3 + (c % 3)

        hx = [[qh(r, c), qh(r, c - 1), qv(r, c), qv(r - 1, c)]
              for r in range(2) for c in range(3)]
        hz = [[qh(r, c), qh(r + 1, c), qv(r, c), qv(r, c + 1)]
              for r in range(2) for c in range(3)]
        dual = dual_hollowed_tensor_level_map(12, hx, hz, m=2)
        self.assertTrue(dual["commutes"])
        self.assertTrue(dual["k_preserved"])
        self.assertEqual(dual["k_amplified"], 2)

        # [[4, 2, 2]] shares 4 qubits between its X and Z check, violating |x ^ z| = 2.
        with self.assertRaises(ValueError):
            build_hollowed_tensor_level_map(4, [[0, 1, 2, 3]], [[0, 1, 2, 3]], m=2)

        # Disconnected G^x (two disjoint 2-qubit plaquette overlaps) fails Hypothesis 103.
        with self.assertRaises(ValueError):
            build_hollowed_tensor_level_map(
                4,
                [[0, 1, 2, 3]],
                [[0, 1], [2, 3]],
                m=2,
            )


if __name__ == "__main__":
    unittest.main()
