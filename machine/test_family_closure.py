"""Instance checks for the Gate 7 family-closure matrix (issue #605).

The matrix and its hand derivations are in `spec/TAXONOMY.md`,
*Gate 7 decision matrices*, *Family-closure matrix*. This file checks the
derivations on instances and replays the counterexamples through the
transcription's own transitions. Agreement is evidence that the derivations
are transcribed as stated, not a proof: a closure verdict stands on its hand
derivation, and a non-closure verdict on its counterexample, which the tests
below rebuild.
"""

import itertools
import os
import random
import re
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(HERE, "experiments"))

from machine.constructors import (  # noqa: E402
    _algebra_element,
    _group_spec,
    _involution,
    hypergraph_product,
    lifted_product,
    mapping_cone,
    nested_css,
    tile_assembly,
)
from machine.state import CodeState, NoDerivation  # noqa: E402
from gate_realization_rows import (  # noqa: E402
    Display,
    mask,
    oracle_preserves,
    pauli_from_string,
    preserves_pi4,
)

S3_TABLE = [
    [0, 1, 2, 3, 4, 5],
    [1, 2, 0, 5, 3, 4],
    [2, 0, 1, 4, 5, 3],
    [3, 4, 5, 0, 1, 2],
    [4, 5, 3, 2, 0, 1],
    [5, 3, 4, 1, 2, 0],
]


def span(masks):
    """A canonical name for the row space of ``masks``: its reduced row
    echelon basis, so that two lists of masks have the same span exactly
    when their names are equal."""
    pivots = {}
    for m in masks:
        for bit, row in sorted(pivots.items(), reverse=True):
            if (m >> bit) & 1:
                m ^= row
        if m:
            top = m.bit_length() - 1
            for bit in list(pivots):
                if (pivots[bit] >> top) & 1:
                    pivots[bit] ^= m
            pivots[top] = m
    return frozenset(pivots.values())


def code(state, perm=None):
    """The code of a state: the two row spaces, as sets of bit masks over
    the positions of Q (or over ``perm`` applied to the labels)."""
    index = {q: i for i, q in enumerate(state.Q)}
    sectors = {"X": [], "Z": []}
    for row in state.rows:
        m = 0
        for q in row.support:
            m |= 1 << (perm[q] if perm is not None else index[q])
        sectors[row.sector].append(m)
    return span(sectors["X"]), span(sectors["Z"])




def rand_matrix(rng, m, n, density=0.5):
    return [[int(rng.random() < density) for _ in range(n)] for _ in range(m)]


def transpose(matrix):
    return [list(col) for col in zip(*matrix)]


def block_diagonal(a, b):
    ca, cb = len(a[0]), len(b[0])
    return [row + [0] * cb for row in a] + [[0] * ca + row for row in b]


def one_sector_invariant(state):
    """(J2) of the matrix: the X row space is zero iff the Z row space is."""
    x, z = code(state)
    return (not x) == (not z)


class HgpTypeInvariants(unittest.TestCase):
    """(J1) n >= 2 and (J2) X = 0 iff Z = 0 on HGP and lifted outputs."""

    def test_hgp_outputs_satisfy_both_invariants(self):
        rng = random.Random(605)
        for _ in range(200):
            m1, n1, m2, n2 = (rng.randint(1, 3) for _ in range(4))
            density = rng.choice([0.0, 0.2, 0.5])
            state, _ = hypergraph_product(rand_matrix(rng, m1, n1, density),
                                          rand_matrix(rng, m2, n2, density))
            self.assertGreaterEqual(len(state.Q), 2)
            self.assertTrue(one_sector_invariant(state))

    def test_lifted_outputs_satisfy_both_invariants(self):
        rng = random.Random(6050)
        for group in ((3,), (2, 2), {"table": S3_TABLE}):
            elements = _group_spec(group)["elements"]
            for _ in range(30):
                dims = [rng.randint(1, 2) for _ in range(4)]
                density = rng.choice([0.0, 0.3])

                def entry():
                    return [g for g in elements if rng.random() < density]

                A = [[entry() for _ in range(dims[1])] for _ in range(dims[0])]
                B = [[entry() for _ in range(dims[3])] for _ in range(dims[2])]
                state, _ = lifted_product(group, A, B)
                self.assertGreaterEqual(len(state.Q), 2)
                self.assertTrue(one_sector_invariant(state))

    def test_coset_lifted_outputs_satisfy_both_invariants(self):
        # Coset lifts over S3 (issue #675): H trivial, non-normal <s>, normal
        # <r>, and all of S3; B's terms are drawn from N_G(H).
        rng = random.Random(675)
        group = {"table": S3_TABLE}
        for generators, normalizer in (([], range(6)), ([3], (0, 3)),
                                       ([1], range(6)), ([1, 3], range(6))):
            for _ in range(20):
                dims = [rng.randint(1, 2) for _ in range(4)]
                density = rng.choice([0.0, 0.3, 0.6])
                A = [[[g for g in range(6) if rng.random() < density]
                      for _ in range(dims[1])] for _ in range(dims[0])]
                B = [[[g for g in normalizer if rng.random() < density]
                      for _ in range(dims[3])] for _ in range(dims[2])]
                state, _ = lifted_product(group, A, B, generators)
                self.assertGreaterEqual(len(state.Q), 2)
                self.assertTrue(one_sector_invariant(state))

    def test_the_two_qubit_hgp_codes_are_exactly_four(self):
        codes = set()
        for h1, h2 in itertools.product((0, 1), repeat=2):
            state, _ = hypergraph_product([[h1]], [[h2]])
            codes.add(code(state))
        self.assertEqual(codes, {
            (span([]), span([])),                # free on two qubits
            (span([0b01]), span([0b10])),        # X_0, Z_1
            (span([0b10]), span([0b01])),        # X_1, Z_0
            (span([0b11]), span([0b11])),        # X_0 X_1, Z_0 Z_1
        })


class HgpTypeCounterexamples(unittest.TestCase):
    """The non-closure counterexamples (H1)-(H5), replayed through the
    transcription's transitions from E0 = hgp([0],[0]) and E1 = hgp([1],[0])."""

    def setUp(self):
        self.e0, _ = hypergraph_product([[0]], [[0]])
        self.e1, _ = hypergraph_product([[1]], [[0]])

    def test_the_two_seeds(self):
        self.assertEqual(code(self.e0), (span([]), span([])))
        self.assertEqual(code(self.e1), (span([0b01]), span([0b10])))

    def test_add_check_breaks_the_one_sector_invariant(self):
        child = self.e0.add_check("X", (0,))
        self.assertFalse(one_sector_invariant(child))

    def test_delete_check_breaks_the_one_sector_invariant(self):
        z_row = [row for row in self.e1.rows if row.sector == "Z"][0]
        child = self.e1.delete_check(z_row.id)
        self.assertFalse(one_sector_invariant(child))

    def test_split_breaks_the_one_sector_invariant(self):
        z_row = [row for row in self.e1.rows if row.sector == "Z"][0]
        child = self.e1.split((0,), (z_row.id,))
        self.assertFalse(one_sector_invariant(child))

    def test_extend_breaks_the_one_sector_invariant(self):
        child = self.e0.extend_code((2,), [("X", (0,))])
        self.assertFalse(one_sector_invariant(child))

    def test_glue_breaks_the_one_sector_invariant(self):
        copy = CodeState((2, 3), (), frozenset())
        child = self.e0.glue(copy, seam_checks=[("X", (0,))])
        self.assertFalse(one_sector_invariant(child))

    def test_puncture_and_peel_leave_one_qubit(self):
        self.assertEqual(len(self.e0.puncture(0).Q), 1)
        x_row = [row for row in self.e1.rows if row.sector == "X"][0]
        self.assertEqual(len(self.e1.peel(0, "X", x_row.id).Q), 1)


class HgpTypeClosures(unittest.TestCase):
    """The closure derivations (H6)-(H8), checked on instances under the
    explicit qubit bijections of the derivations."""

    def test_hadamard_of_hgp_is_hgp_of_the_transposes(self):
        rng = random.Random(6051)
        for _ in range(200):
            m1, n1, m2, n2 = (rng.randint(1, 3) for _ in range(4))
            H1, H2 = rand_matrix(rng, m1, n1), rand_matrix(rng, m2, n2)
            left, _ = hypergraph_product(H1, H2)
            right, _ = hypergraph_product(transpose(H1), transpose(H2))
            perm = {}
            for i, j in itertools.product(range(n1), range(n2)):
                perm[i * n2 + j] = m1 * m2 + i * n2 + j
            for a, b in itertools.product(range(m1), range(m2)):
                perm[n1 * n2 + a * m2 + b] = a * m2 + b
            x, z = code(left.hadamard_sector_swap(), perm)
            self.assertEqual((x, z), code(right))

    def test_hadamard_of_lifted_is_lifted_of_the_conjugate_transposes(self):
        rng = random.Random(6052)
        for group in ((3,), (2, 2), {"table": S3_TABLE}):
            info = _group_spec(group)
            ell = len(info["elements"])
            for _ in range(30):
                mA, nA, mB, nB = (rng.randint(1, 2) for _ in range(4))

                def entry():
                    return [g for g in info["elements"] if rng.random() < 0.4]

                A = [[entry() for _ in range(nA)] for _ in range(mA)]
                B = [[entry() for _ in range(nB)] for _ in range(mB)]
                star = [[sorted(_involution(_algebra_element(x, info, "x"), info))
                         for x in row] for row in A]
                A_dual = transpose(star)
                star = [[sorted(_involution(_algebra_element(x, info, "x"), info))
                         for x in row] for row in B]
                B_dual = transpose(star)
                left, _ = lifted_product(group, A, B)
                right, _ = lifted_product(group, A_dual, B_dual)
                perm = {}
                for i, j, g in itertools.product(range(nA), range(nB), range(ell)):
                    perm[(i * nB + j) * ell + g] = mA * mB * ell + (i * nB + j) * ell + g
                for a, b, g in itertools.product(range(mA), range(mB), range(ell)):
                    perm[nA * nB * ell + (a * mB + b) * ell + g] = (a * mB + b) * ell + g
                self.assertEqual(code(left.hadamard_sector_swap(), perm), code(right))

    def test_hgp_distributes_over_a_block_diagonal_argument(self):
        # (H6): hgp(H (+) H', K) and hgp(K, H (+) H') are the direct sums of
        # the two summands, under the bijection that sends each pair to the
        # summand its block index belongs to.
        rng = random.Random(6053)
        for _ in range(100):
            p, q, pp, qp, m, n = (rng.randint(1, 3) for _ in range(6))
            H, Hp, K = (rand_matrix(rng, p, q), rand_matrix(rng, pp, qp),
                        rand_matrix(rng, m, n))
            D = block_diagonal(H, Hp)

            # First argument block diagonal: left (i, j), right (a, b).
            whole, _ = hypergraph_product(D, K)
            a, _ = hypergraph_product(H, K)
            b, _ = hypergraph_product(Hp, K)
            na = len(a.Q)
            perm = {}
            for i, j in itertools.product(range(q + qp), range(n)):
                perm[i * n + j] = (i * n + j if i < q
                                   else na + (i - q) * n + j)
            for r, c in itertools.product(range(p + pp), range(m)):
                perm[(q + qp) * n + r * m + c] = (q * n + r * m + c if r < p
                                                  else na + qp * n + (r - p) * m + c)
            self.assertEqual(code(whole, perm), self.direct_sum_code(a, b))

            # Second argument block diagonal.
            whole, _ = hypergraph_product(K, D)
            a, _ = hypergraph_product(K, H)
            b, _ = hypergraph_product(K, Hp)
            na = len(a.Q)
            perm = {}
            for i, j in itertools.product(range(n), range(q + qp)):
                perm[i * (q + qp) + j] = (i * q + j if j < q
                                          else na + i * qp + (j - q))
            for r, c in itertools.product(range(m), range(p + pp)):
                perm[n * (q + qp) + r * (p + pp) + c] = (
                    n * q + r * p + c if c < p
                    else na + n * qp + r * pp + (c - p))
            self.assertEqual(code(whole, perm), self.direct_sum_code(a, b))

    @staticmethod
    def direct_sum_code(a, b):
        x_a, z_a = code(a)
        x_b, z_b = code(b)
        shift = len(a.Q)
        return (span(list(x_a) + [v << shift for v in x_b]),
                span(list(z_a) + [v << shift for v in z_b]))


class UniversalFamilies(unittest.TestCase):
    """(U) nested, tile, and mapping cone generate every CSS code on enough
    qubits, under the explicit inputs of the derivations."""

    def random_css(self, rng, n):
        hx = rand_matrix(rng, rng.randint(1, 3), n)
        kernel = [v for v in itertools.product((0, 1), repeat=n)
                  if all(sum(x * y for x, y in zip(v, r)) % 2 == 0 for r in hx)]
        hz = [list(rng.choice(kernel)) for _ in range(rng.randint(1, 3))]
        return hx, hz

    def test_mapping_cone_realizes_every_code_on_two_or_more_qubits(self):
        rng = random.Random(6054)
        for _ in range(200):
            n = rng.randint(2, 6)
            hx, hz = self.random_css(rng, n)
            target, _ = nested_css(hx, hz)
            d_a = [row[:n - 1] for row in hz]
            f1 = [[row[n - 1]] for row in hz]
            f0 = transpose([row[:n - 1] for row in hx])
            d_b = [[row[n - 1] for row in hx]]
            cone, _ = mapping_cone(d_a, d_b, f1, f0)
            self.assertEqual(code(cone), code(target))

    def test_one_tile_realizes_its_own_code(self):
        rng = random.Random(6055)
        for _ in range(100):
            n = rng.randint(1, 6)
            hx, hz = self.random_css(rng, n)
            target, _ = nested_css(hx, hz)
            tile = {"qubits": n,
                    "X": [list(r.support) for r in target.rows if r.sector == "X"],
                    "Z": [list(r.support) for r in target.rows if r.sector == "Z"]}
            state, _ = tile_assembly([tile], [(0, list(range(n)))])
            self.assertEqual(code(state), code(target))

    def test_puncture_and_peel_at_the_boundary_leave_the_family(self):
        one = CodeState((0,), (), frozenset())
        self.assertEqual(len(one.puncture(0).Q), 0)
        x0, _ = nested_css([[1]], [[0]])
        x_row = [row for row in x0.rows if row.sector == "X"][0]
        self.assertEqual(len(x0.peel(0, "X", x_row.id).Q), 0)

    def test_graft_has_no_derivation_on_one_or_two_qubits(self):
        # The only CSS codes on at most two qubits with a qubit in rows of
        # both sectors are X0X1, Z0Z1 up to relabeling; graft at either qubit
        # leaves the other untouched by the spliced sector.
        state, _ = nested_css([[1, 1]], [[1, 1]])
        for sector in ("X", "Z"):
            ids = [row.id for row in state.rows if row.sector == sector]
            with self.assertRaises(NoDerivation):
                state.graft(0, sector, ids)


class GateRealizationCounterexamples(unittest.TestCase):
    """(GR2) and (GR3): the family of states a fixed pi/4 gate preserves is
    not closed under the sector exchange or a column SWAP."""

    def test_sector_exchange(self):
        gens, eps = [pauli_from_string("XI")], [1]
        before = Display.from_supports(2, [(0, 1)], [])
        after = Display.from_supports(2, [], [(0, 1)])
        self.assertTrue(preserves_pi4(before, gens, eps))
        self.assertFalse(preserves_pi4(after, gens, eps))
        quarter = [3.141592653589793 / 4]
        self.assertTrue(oracle_preserves(before, gens, eps, quarter))
        self.assertFalse(oracle_preserves(after, gens, eps, quarter))

    def test_column_swap(self):
        gens, eps = [pauli_from_string("IZ")], [1]
        before = Display(2, [mask((0,))], [])
        after = Display(2, [mask((1,))], [])
        self.assertTrue(preserves_pi4(before, gens, eps))
        self.assertFalse(preserves_pi4(after, gens, eps))
        quarter = [3.141592653589793 / 4]
        self.assertTrue(oracle_preserves(before, gens, eps, quarter))
        self.assertFalse(oracle_preserves(after, gens, eps, quarter))

    def test_check_addition(self):
        # (GR6): on one qubit with no rows every gate preserves the codespace;
        # adding Z_0 leaves a codespace that exp(i theta X_0) does not keep,
        # at pi/4 and at non-pi/4 angles (decided by Corollary 7.1 of §4.37).
        gens, eps = [pauli_from_string("X")], [1]
        before = Display(1, [], [])
        after = Display(1, [], [mask((0,))])
        self.assertTrue(preserves_pi4(before, gens, eps))
        self.assertFalse(preserves_pi4(after, gens, eps))
        for theta in (3.141592653589793 / 4, 3.141592653589793 / 8):
            self.assertTrue(oracle_preserves(before, gens, eps, [theta]))
            self.assertFalse(oracle_preserves(after, gens, eps, [theta]))


class MatricesCoverTheTaxonomy(unittest.TestCase):
    """Both matrices list every admitted operation they are meant to list, so
    a newly admitted identifier without a row fails here."""

    # A row's first cell is a backticked identifier, possibly followed by a
    # qualifier such as "($T = Q$)".
    ROW = re.compile(r"^\| `([A-Z][A-Z0-9-]*)`[ |]")

    @classmethod
    def setUpClass(cls):
        with open(os.path.join(ROOT, "spec", "TERM_LANGUAGE.md"), encoding="utf-8") as f:
            term = f.read()
        kinds = re.findall(
            r"^\| `([A-Z][A-Z0-9-]*)` \| (command|expression-constructor|"
            r"presentation-operation) \|", term, re.M)
        cls.kinds = dict(kinds)
        with open(os.path.join(ROOT, "spec", "TAXONOMY.md"), encoding="utf-8") as f:
            taxonomy = f.read()
        start = taxonomy.index("# Gate 7 decision matrices")
        typed = taxonomy[start:taxonomy.index("## Family-closure matrix", start)]
        closure = taxonomy[taxonomy.index("## Family-closure matrix", start):]
        closure = closure[:closure.index("\n# ")]
        cls.typed_rows = {m.group(1) for line in typed.splitlines()
                          if (m := cls.ROW.match(line))}
        cls.closure_rows = {m.group(1) for line in closure.splitlines()
                            if (m := cls.ROW.match(line))}

    def test_the_grammar_table_was_read(self):
        self.assertIn("L-HGP", self.kinds)
        self.assertIn("C-SEQUENCE", self.kinds)
        self.assertEqual(self.kinds.get("P-RELABEL"), "presentation-operation")

    def test_every_production_has_a_typed_input_row(self):
        productions = {i for i, k in self.kinds.items() if k != "presentation-operation"}
        self.assertEqual(productions - self.typed_rows, set())

    def test_every_transformation_has_a_closure_row(self):
        commands = {i for i, k in self.kinds.items() if k == "command"} - {"C-SEQUENCE"}
        expected = commands | {"C-DIRECT-SUM", "E-GLUE", "P-RELABEL"}
        self.assertEqual(expected - self.closure_rows, set())


if __name__ == "__main__":
    unittest.main()
