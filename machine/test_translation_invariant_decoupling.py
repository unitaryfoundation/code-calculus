"""Tests for the finite-torus harness.

The harness is the finite side of `DECOUPLING_CONSTRUCTOR.md`. A
passing run is evidence for the note's derivations, not a proof, and admits
nothing.
"""

import os
import random
import sys
import unittest
from math import comb

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "experiments"))

from translation_invariant_decoupling import (  # noqa: E402
    Code,
    ZERO,
    apply_circuit,
    apply_physical,
    check_decoupling,
    coarse_grain,
    disguised_instance,
    distance_window,
    distances,
    inverse,
    logical_count,
    monomial,
    one,
    physical_gates,
    poly_add,
    relabel_rows,
    stack,
    sweep,
    toric_code,
    well_formed,
    with_ancillas,
)


class Targets(unittest.TestCase):
    def test_two_dimensional_toric_code(self):
        for periods, d in (((2, 2), 2), ((3, 2), 2), ((3, 3), 3)):
            code = toric_code(periods, 1)
            display = code.display()
            self.assertTrue(code.commutes())
            self.assertTrue(well_formed(display))
            self.assertEqual(logical_count(code.n(), display), 2)
            self.assertEqual(distances(code.n(), display), (d, d))

    def test_logical_count_of_higher_forms(self):
        # On the tori tried, the j-form code in dimension D has C(D, j)
        # logical qubits.
        for periods, j in (((2, 2, 2), 1), ((2, 2, 2), 2), ((3, 2, 2), 1), ((2, 2, 2, 2), 2)):
            code = toric_code(periods, j)
            self.assertTrue(code.commutes())
            self.assertEqual(logical_count(code.n(), code.display()), comb(len(periods), j))

    def test_stack_adds_logical_counts(self):
        periods = (2, 2, 2)
        both = stack([toric_code(periods, 1), toric_code(periods, 2)])
        self.assertTrue(both.commutes())
        self.assertEqual(logical_count(both.n(), both.display()), 6)

    def test_ancillas_change_neither_k_nor_the_distances(self):
        code = toric_code((2, 2), 1)
        extended = with_ancillas(code, plus=1, zero=0)
        self.assertEqual(logical_count(extended.n(), extended.display()), 2)
        self.assertEqual(distances(extended.n(), extended.display()), (2, 2))


class CoarseGraining(unittest.TestCase):
    def test_same_display_up_to_relabelling(self):
        for periods, j, factors in (
            ((4, 2), 1, (2, 1)),
            ((4, 2), 1, (2, 2)),
            ((4, 2, 2), 2, (2, 1, 2)),
        ):
            code = toric_code(periods, j)
            coarse, relabel = coarse_grain(code, factors)
            self.assertTrue(coarse.commutes())
            self.assertEqual(sorted(relabel), list(range(code.n())))
            fine, big = code.display(), coarse.display()
            for sector in (0, 1):
                self.assertEqual(sorted(relabel_rows(fine[sector], relabel)), sorted(big[sector]))


class Circuits(unittest.TestCase):
    def test_sum_gate_on_the_display(self):
        # One SUM with a nontrivial translation, on a torus where the
        # antipode is not the identity.
        periods = (3, 2)
        code = toric_code(periods, 1)
        circuit = [("sum", 0, 1, poly_add(one(periods), monomial((1, 0), periods)))]
        by_matrix = apply_circuit(code, circuit).display()
        by_gates = apply_physical(code.display(), physical_gates(code, circuit))
        for sector in (0, 1):
            self.assertEqual(sorted(by_matrix[sector]), sorted(by_gates[sector]))
        self.assertTrue(apply_circuit(code, circuit).commutes())

    def test_inverse(self):
        rng = random.Random(7)
        code, certificate, target = disguised_instance(rng, periods=(3, 2))
        back = apply_circuit(apply_circuit(code, certificate), inverse(certificate))
        self.assertEqual(back.hx, code.hx)
        self.assertEqual(back.hz, code.hz)


class Certificate(unittest.TestCase):
    def test_accepts_the_inverse_of_the_disguise(self):
        rng = random.Random(11)
        code, certificate, target = disguised_instance(rng, periods=(2, 2))
        record = check_decoupling(code, certificate, target)
        self.assertTrue(record["accepted"])
        self.assertEqual(record["n"], 12)
        self.assertEqual(record["k"], 2)
        self.assertEqual(
            record["input_signature"],
            {"periods": (2, 2), "q": 3, "hx_rows": 2, "hz_rows": 1, "commutes": True},
        )
        self.assertEqual(record["ancillas"], {"plus": 0, "zero": 0})

    def test_refuses_the_empty_circuit_on_a_disguised_code(self):
        periods = (2, 2)
        target = toric_code(periods, 1)
        code = apply_circuit(target, [("sum", 0, 1, one(periods))])
        self.assertFalse(check_decoupling(code, [], target)["accepted"])
        self.assertTrue(check_decoupling(code, [("sum", 0, 1, one(periods))], target)["accepted"])

    def test_ancilla_is_part_of_the_certificate(self):
        periods = (2, 2)
        target = with_ancillas(toric_code(periods, 1), plus=1)
        code = toric_code(periods, 1)
        self.assertEqual(check_decoupling(code, [], target)["reason"], "shape mismatch")
        self.assertTrue(check_decoupling(code, [], target, plus=1)["accepted"])

    def test_refuses_noncommuting_input(self):
        periods = (2, 2)
        unit = one(periods)
        bad = Code(periods, 1, [[unit]], [[unit]])
        record = check_decoupling(bad, [], bad)
        self.assertFalse(record["accepted"])
        self.assertEqual(record["reason"], "input rows do not commute")
        self.assertFalse(record["input_signature"]["commutes"])

    def test_distance_window(self):
        self.assertEqual(distance_window(4, 3, 2), (2, 12))
        self.assertEqual(distance_window(3, 1, 2), (2, 3))

    def test_a_circuit_can_change_the_distance(self):
        # The distance cell is a window, not an equality: this certificate
        # takes a code of X distance 1 to the toric code with one ancilla
        # per cell, of X distance 2.
        periods = (2, 2)
        target = with_ancillas(toric_code(periods, 1), plus=1)
        certificate = [
            ("sum", 2, 0, monomial((1, 1), periods)),
            ("sum", 0, 1, monomial((1, 1), periods)),
            ("sum", 0, 2, monomial((1, 0), periods)),
        ]
        code = apply_circuit(target, inverse(certificate))
        record = check_decoupling(code, certificate, target)
        self.assertTrue(record["accepted"])
        n = code.n()
        source, image = distances(n, code.display()), distances(n, target.display())
        self.assertEqual((source, image), ((1, 2), (2, 2)))
        f = record["factors"]
        low, high = distance_window(source[0], f["x"], f["x_inverse"])
        self.assertTrue(low <= image[0] <= high)


class ValidationAndRefusal(unittest.TestCase):
    def test_refuses_missing_translation_invariance_data(self):
        target = toric_code((2, 2), 1)
        for bad_input in (None, {"Q": [0, 1], "X": [], "Z": []}, "not-a-code"):
            rec = check_decoupling(bad_input, [], target)
            self.assertFalse(rec["accepted"])
            self.assertEqual(
                rec["reason"], "translation-invariance data required (expected Code)"
            )
            rec_target = check_decoupling(target, [], bad_input)
            self.assertFalse(rec_target["accepted"])
            self.assertEqual(
                rec_target["reason"], "translation-invariance data required (expected Code)"
            )

    def test_refuses_noncommuting_target_and_malformed_circuits(self):
        periods = (2, 2)
        unit = one(periods)
        good = Code(periods, 1, [[unit]], [])
        bad_target = Code(periods, 1, [[unit]], [[unit]])
        rec = check_decoupling(good, [], bad_target)
        self.assertFalse(rec["accepted"])
        self.assertEqual(rec["reason"], "target rows do not commute")

        tc = toric_code(periods, 1)
        for bad_circuit in (
            [("sum", 0, 0, unit)],
            [("sum", 0, 5, unit)],
            [("swap", 0, 2)],
            [("cz", 0, 1)],
        ):
            rec = check_decoupling(tc, bad_circuit, tc)
            self.assertFalse(rec["accepted"])
            self.assertTrue(rec["reason"].startswith("invalid circuit:"))
            with self.assertRaises(ValueError):
                apply_circuit(tc, bad_circuit)
            with self.assertRaises(ValueError):
                physical_gates(tc, bad_circuit)

    def test_code_and_helpers_reject_invalid_typed_inputs(self):
        periods = (2, 2)
        unit = one(periods)
        for bad_args in (
            ((), 1, [], []),
            ((0, 2), 1, [], []),
            ((True, 2), 1, [], []),
            (periods, 0, [], []),
            (periods, False, [], []),
            (periods, 2, [[unit]], []),
            (periods, 1, [[frozenset({(0,)})]], []),
        ):
            with self.assertRaises(ValueError):
                Code(*bad_args)

        tc = toric_code(periods, 1)
        with self.assertRaises(ValueError):
            with_ancillas(tc, plus=-1)
        with self.assertRaises(ValueError):
            with_ancillas(tc, zero=True)
        with self.assertRaises(ValueError):
            stack([])
        with self.assertRaises(ValueError):
            stack([tc, toric_code((3, 2), 1)])
        with self.assertRaises(ValueError):
            coarse_grain(tc, (3, 1))
        with self.assertRaises(ValueError):
            distance_window(0, 1, 1)
        with self.assertRaises(ValueError):
            distance_window(2, 0, 1)
        with self.assertRaises(ValueError):
            check_decoupling(tc, [], tc, plus=-1)


class Sweep(unittest.TestCase):
    def test_no_disagreement(self):
        stats = sweep(seed=451, trials=20)
        self.assertEqual(stats["disagreements"], [])
        self.assertEqual(stats["certificates_accepted"], 20)
        self.assertEqual(stats["tampered_accepted"], 0)
        self.assertGreater(stats["distance_windows_checked"], 0)


if __name__ == "__main__":
    unittest.main()
