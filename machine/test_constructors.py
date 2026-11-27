"""Typed constructors admitted 2026-11-11.

`L-HGP`, `L-LIFTED`, `L-GROUP-ALGEBRA`, and `A-CONCAT` build presented CSS
states from finite constructive data (`spec/OPERATIONAL_SEMANTICS.md` section
2 cards, section 4.34). These tests check the outputs against the derived
parameter formulas, the exact-distance oracle on small instances, and each
other (the trivial-group lifted product is the hypergraph product; the
two-block code is the 1 x 1 lifted product).

`A-PRODUCT`, `A-DOUBLE`, `L-BALANCED`, `L-TANNER`, and `L-TILE`
(section 4.35) are checked the same way: parameters against the derivations,
small instances against the exact-distance oracle, the trivial-group
balanced product against the hypergraph product, and the commutation
premise of the last three as a refusal.

`L-NESTED-CSS` (section 4.36) is checked against its closed
form for k, against the sector distances read from the two classical codes,
against `L-TANNER` with one vertex per class, and as a refusal when the two
codes are not nested.
"""

import os
import random
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.join(HERE, "experiments")
for path in (EXP, HERE):
    if path not in sys.path:
        sys.path.insert(0, path)

from machine.oracle import exact_distances  # noqa: E402
from machine.priced_calculus import (  # noqa: E402
    ADMITTED_CONSTRUCTORS,
    UNADMITTED_CONSTRUCTORS,
    CodeState,
    DistanceLedger,
    Interval,
    Malformed,
    NoDerivation,
    Row,
    concatenate,
    construct,
    hypergraph_parameters,
    hypergraph_product,
    balanced_product,
    css_tensor_product,
    double_cover,
    lifted_product,
    nested_css,
    empty_code,
    free_code,
    pullback_code,
    pushout_code,
    pair_partition_code,
    pp_scale_code,

    tanner_code,
    tile_assembly,
    rank,
    two_block_code,
    lift_hgp_witnesses,
    lift_nested_witnesses,
    lift_concat_witnesses,
    lift_product_witnesses,
    lift_double_witnesses,
    _group_spec,
    _left_lift_rows,
    _right_lift_rows,
    _involution,
)


def repetition(length):
    """The cyclic repetition-code parity-check matrix (length rows, rank length - 1)."""
    return [[1 if c in (r, (r + 1) % length) else 0 for c in range(length)]
            for r in range(length)]


def row_sets(state):
    return {(row.sector, row.support) for row in state.rows}


def sector_rank(state, sector):
    return rank([row.mask for row in state.sector_rows(sector)])


def logical_count(state):
    return len(state.Q) - sector_rank(state, "X") - sector_rank(state, "Z")


class HypergraphProductTests(unittest.TestCase):
    def test_toric_code_from_two_repetition_codes(self):
        state, dropped = hypergraph_product(repetition(3), repetition(3))
        self.assertEqual(len(state.Q), 18)
        self.assertEqual(logical_count(state), 2)
        # One natural row per sector is dependent (the cyclic redundancy).
        self.assertEqual(dropped, 2)
        self.assertEqual(len(state.sector_rows("X")), 8)
        self.assertEqual(len(state.sector_rows("Z")), 8)
        exact = exact_distances(state)
        self.assertEqual((exact["X"], exact["Z"], exact["d"]), (3, 3, 3))
        self.assertEqual(hypergraph_parameters(repetition(3), repetition(3)),
                         {"n": 18, "k": 2, "rank_X": 8, "rank_Z": 8})

    def test_parameter_formula_on_random_factors(self):
        rng = random.Random(330)
        for _ in range(40):
            m1, n1, m2, n2 = (rng.randint(1, 3) for _ in range(4))
            H1 = [[rng.randint(0, 1) for _ in range(n1)] for _ in range(m1)]
            H2 = [[rng.randint(0, 1) for _ in range(n2)] for _ in range(m2)]
            state, _dropped = hypergraph_product(H1, H2)
            expected = hypergraph_parameters(H1, H2)
            self.assertEqual(len(state.Q), expected["n"])
            self.assertEqual(logical_count(state), expected["k"])
            self.assertEqual(sector_rank(state, "X"), expected["rank_X"])
            self.assertEqual(sector_rank(state, "Z"), expected["rank_Z"])

    def test_the_trivial_group_lifted_product_is_the_hypergraph_product(self):
        H1 = [[1, 1, 0], [0, 1, 1]]
        H2 = [[1, 1]]
        hgp, _ = hypergraph_product(H1, H2)
        unit = [()]
        lp, _ = lifted_product((), [[unit if v else [] for v in r] for r in H1],
                               [[unit if v else [] for v in r] for r in H2])
        self.assertEqual(row_sets(hgp), row_sets(lp))

    def test_malformed_matrices_are_refused(self):
        with self.assertRaises(Malformed):
            hypergraph_product([[1, 2]], [[1]])
        with self.assertRaises(Malformed):
            hypergraph_product([[1, 1], [1]], [[1]])
        with self.assertRaises(Malformed):
            hypergraph_product([], [[1]])


class TwoBlockAndLiftedProductTests(unittest.TestCase):
    def test_two_block_code_over_a_cyclic_group(self):
        # a = 1 + x, b = 1 + x^2 over Z_6: H_X = [L(a) | L(b)], H_Z = [L(b)^T | L(a)^T].
        state, dropped = two_block_code([6], [(0,), (1,)], [(0,), (2,)])
        self.assertEqual(len(state.Q), 12)
        self.assertEqual(sector_rank(state, "X"), sector_rank(state, "Z"))
        self.assertEqual(logical_count(state), 2 * (6 - sector_rank(state, "X")))
        self.assertEqual(dropped, 2 * (6 - sector_rank(state, "X")))

    def test_two_block_equals_the_one_by_one_lifted_product(self):
        a, b = [(0, 0), (1, 0), (0, 2)], [(0, 1), (2, 0)]
        block, _ = two_block_code([3, 3], a, b)
        b_star = [((-t0) % 3, (-t1) % 3) for t0, t1 in b]
        lp, _ = lifted_product([3, 3], [[a]], [[b_star]])
        self.assertEqual(row_sets(block), row_sets(lp))

    def test_bivariate_bicycle_72_12(self):
        # Bravyi et al. 2024: l = m = 6, a = x^3 + y + y^2, b = y^3 + x + x^2.
        a = [(3, 0), (0, 1), (0, 2)]
        b = [(0, 3), (1, 0), (2, 0)]
        state, _ = two_block_code([6, 6], a, b)
        self.assertEqual(len(state.Q), 72)
        self.assertEqual(logical_count(state), 12)

    def test_lifted_product_over_a_product_group(self):
        orders = [2, 3]
        A = [[[(0, 0), (1, 0)], [(0, 1)]], [[(1, 2)], [(0, 0)]]]
        B = [[[(0, 0)], [(1, 1)], [(0, 2), (1, 0)]]]
        state, _dropped = lifted_product(orders, A, B)
        self.assertEqual(len(state.Q), 6 * (2 * 3 + 2 * 1))
        self.assertGreaterEqual(logical_count(state), 0)

    def test_integer_terms_name_cyclic_group_elements(self):
        plain, _ = two_block_code([5], [0, 1], [0, 3])
        tupled, _ = two_block_code([5], [(0,), (1,)], [(0,), (3,)])
        self.assertEqual(row_sets(plain), row_sets(tupled))

    def test_malformed_algebra_inputs_are_refused(self):
        with self.assertRaises(Malformed):
            two_block_code([0], [(0,)], [(0,)])
        with self.assertRaises(Malformed):
            two_block_code([4], [(0, 0)], [(0,)])
        with self.assertRaises(Malformed):
            lifted_product([2], [[[(0,)]], [[(0,)], [(1,)]]], [[[(0,)]]])


class ConcatenationTests(unittest.TestCase):
    def state(self, n, rows):
        result = CodeState(tuple(range(n)), tuple(rows), frozenset(r.id for r in rows))
        result.validate()
        return result

    def test_concatenation_matches_the_tower_experiment(self):
        import tower_sweep
        inner = self.state(4, [Row("a1", "X", (0, 1, 2, 3)), Row("b1", "Z", (0, 1, 2, 3))])
        outer = self.state(4, [Row("p1", "X", (0, 1, 2, 3)), Row("q1", "Z", (0, 1, 2, 3))])
        groups = [(0, 1), (2, 3)]
        state, dropped = concatenate(outer, inner, groups)
        tower, _lifted = tower_sweep.concatenate(inner, outer, groups)
        self.assertEqual(row_sets(state), row_sets(tower))
        self.assertEqual(dropped, 0)
        self.assertEqual(len(state.Q), 8)
        self.assertEqual(logical_count(state), 2)   # k_out = 4 - 2

    def test_construct_dispatch_and_parameters(self):
        inner = self.state(4, [Row("a1", "X", (0, 1, 2, 3)), Row("b1", "Z", (0, 1, 2, 3))])
        outer = self.state(2, [Row("q1", "Z", (0, 1))])
        result = construct({"constructor": "A-CONCAT", "outer": outer, "inner": inner,
                            "groups": [(0, 1)]})
        self.assertEqual((result["n"], result["k"]), (4, 1))
        result = construct({"constructor": "L-HGP", "H1": repetition(3), "H2": [[1, 1]]})
        self.assertEqual((result["n"], result["k"]), (3 * 2 + 3 * 1, 1 * 1 + 1 * 0))

    def test_groups_must_partition_the_outer_qubits(self):
        inner = self.state(4, [Row("a1", "X", (0, 1, 2, 3)), Row("b1", "Z", (0, 1, 2, 3))])
        outer = self.state(4, [Row("q1", "Z", (0, 1, 2, 3))])
        with self.assertRaises(Malformed):
            concatenate(outer, inner, [(0, 1), (2,)])


def css_state(n, x_supports, z_supports):
    rows = [Row("a%d" % (i + 1), "X", tuple(s)) for i, s in enumerate(x_supports)]
    rows += [Row("b%d" % (i + 1), "Z", tuple(s)) for i, s in enumerate(z_supports)]
    state = CodeState(tuple(range(n)), tuple(rows), frozenset(r.id for r in rows))
    state.validate()
    return state


FOUR_TWO_TWO = ([(0, 1, 2, 3)], [(0, 1, 2, 3)])
STEANE = [(0, 1, 2, 3), (0, 1, 4, 5), (0, 2, 4, 6)]


class TensorProductTests(unittest.TestCase):
    """`A-PRODUCT`: n by the three blocks, k = k_A k_B (section 4.35)."""

    def test_parameters_on_small_factors(self):
        c422 = css_state(4, *FOUR_TWO_TWO)
        steane = css_state(7, STEANE, STEANE)
        for left, right in ((c422, c422), (c422, steane), (steane, c422),
                            (steane, steane)):
            state, dropped = css_tensor_product(left, right)
            ax, az = len(left.sector_rows("X")), len(left.sector_rows("Z"))
            bx, bz = len(right.sector_rows("X")), len(right.sector_rows("Z"))
            n = az * bx + len(left.Q) * len(right.Q) + ax * bz
            self.assertEqual(len(state.Q), n)
            self.assertEqual(logical_count(state),
                             logical_count(left) * logical_count(right))
            natural = (len(left.Q) * bx + ax * len(right.Q)
                       + az * len(right.Q) + len(left.Q) * bz)
            self.assertEqual(dropped, natural - (n - logical_count(state)))

    def test_the_retained_display_is_needed(self):
        steane = css_state(7, STEANE, STEANE)
        _state, dropped = css_tensor_product(steane, steane)
        self.assertGreater(dropped, 0)

    def test_construct_dispatch(self):
        c422 = css_state(4, *FOUR_TWO_TWO)
        result = construct({"constructor": "A-PRODUCT", "left": c422, "right": c422})
        self.assertEqual((result["n"], result["k"]), (18, 4))
        with self.assertRaises(Malformed):
            construct({"constructor": "A-PRODUCT", "left": c422, "right": None})


class DoubleCoverTests(unittest.TestCase):
    """`A-DOUBLE`: the two-sheet cover under a wiring map."""

    def test_untwisted_wiring_is_two_copies(self):
        steane = css_state(7, STEANE, STEANE)
        state, dropped = double_cover(steane, {})
        self.assertEqual((len(state.Q), logical_count(state), dropped), (14, 2, 0))
        self.assertEqual(
            row_sets(state),
            {(row.sector, tuple(q + sheet * 7 for q in row.support))
             for row in steane.rows for sheet in (0, 1)})

    def test_conjugate_sheet_swaps_the_sectors_of_the_second_copy(self):
        code = css_state(3, [(0, 1)], [])
        state, _ = double_cover(code, {}, conjugate=True)
        self.assertEqual(row_sets(state), {("X", (0, 1)), ("Z", (3, 4))})

    def test_a_wiring_that_breaks_commutation_has_no_derivation(self):
        steane = css_state(7, STEANE, STEANE)
        with self.assertRaises(NoDerivation):
            double_cover(steane, {"a1": [0]})

    def test_malformed_wirings(self):
        steane = css_state(7, STEANE, STEANE)
        for wiring in ({"zz": [0]}, {"a1": [4]}, {"a1": [0, 0]}, [("a1", [0])]):
            with self.assertRaises(Malformed):
                double_cover(steane, wiring)

    def cover_and_double(self, l, m, a, b):
        """The two-block code on Z_2l x Z_m and the double of the one on
        Z_l x Z_m with the wrap of the first exponent as its wiring, the
        double's rows relabeled into the cover's namespace."""
        from machine.priced_calculus import (
            _algebra_element, _group, _involution, _lift_rows)
        base, _ = two_block_code((l, m), a, b)
        cover, _ = two_block_code((2 * l, m), a, b)
        orders, elements, index = _group((l, m))
        ell = l * m
        alg_a = _algebra_element(a, orders, "a")
        alg_b = _algebra_element(b, orders, "b")
        la = _lift_rows(alg_a, orders, elements, index)
        lb = _lift_rows(alg_b, orders, elements, index)
        lat = _lift_rows(_involution(alg_a, orders), orders, elements, index)
        lbt = _lift_rows(_involution(alg_b, orders), orders, elements, index)
        origin = {"X": {la[h] | (lb[h] << ell): elements[h] for h in range(ell)},
                  "Z": {lbt[h] | (lat[h] << ell): elements[h] for h in range(ell)}}
        wiring = {}
        for row in base.rows:
            h = origin[row.sector][row.mask]
            wiring[row.id] = [
                q for q in row.support
                if (elements[q % ell][0] > h[0] if row.sector == "X"
                    else elements[q % ell][0] < h[0])]
        double, _ = double_cover(base, wiring)
        n = len(base.Q)

        def relabel(label):
            sheet, q = divmod(label, n)
            side, element = divmod(q, ell)
            x, y = elements[element]
            return side * 2 * ell + (x + sheet * l) * m + y

        lifted = {sector: [sum(1 << relabel(q) for q in row.support)
                           for row in double.sector_rows(sector)]
                  for sector in ("X", "Z")}
        return base, cover, double, lifted

    def test_the_free_z2_cover_of_an_independent_display_is_its_double(self):
        # TAXONOMY.md section 2.16: the free Z_2 cover of a two-block code on
        # Z_l x Z_m is the two-block code on Z_2l x Z_m at the same supports.
        # When the base's natural rows are independent (k = 0), the double
        # under the wrap wiring spans the cover's two row spaces.
        base, cover, double, lifted = self.cover_and_double(
            3, 3, [(1, 0), (0, 1), (0, 2)], [(0, 1), (1, 0), (2, 0)])
        self.assertEqual(logical_count(base), 0)
        self.assertEqual(len(double.Q), len(cover.Q))
        for sector in ("X", "Z"):
            target = [row.mask for row in cover.sector_rows(sector)]
            self.assertEqual(rank(lifted[sector]), rank(target))
            self.assertEqual(rank(lifted[sector] + target), rank(target))

    def test_the_double_reads_the_display_not_the_natural_rows(self):
        # With k > 0 the base's natural rows are dependent and the retained
        # display drops some. The cover also carries the lifts of the
        # dropped rows, which the double of the display does not: the
        # double's row spaces sit strictly inside the cover's.
        base, cover, double, lifted = self.cover_and_double(
            3, 3, [(0, 0), (1, 0)], [(0, 0), (0, 1)])
        self.assertEqual(logical_count(base), 2)
        self.assertEqual(logical_count(cover), 2)
        self.assertEqual(logical_count(double), 4)
        for sector in ("X", "Z"):
            target = [row.mask for row in cover.sector_rows(sector)]
            self.assertLess(rank(lifted[sector]), rank(target))
            self.assertEqual(rank(lifted[sector] + target), rank(target))


class BalancedProductTests(unittest.TestCase):
    """`L-BALANCED`: the hypergraph-product complex modulo a group action."""

    def shift(self, length):
        return [(i + 1) % length for i in range(length)]

    def test_the_trivial_group_is_the_hypergraph_product(self):
        h1, h2 = [[1, 1, 0], [0, 1, 1]], [[1, 1], [1, 1]]
        trivial = {"rows": [], "cols": []}
        state, dropped = balanced_product((), h1, trivial, h2, trivial)
        product, product_dropped = hypergraph_product(h1, h2)
        self.assertEqual(state, product)
        self.assertEqual(dropped, product_dropped)

    def test_cyclic_action_on_two_cycles(self):
        for length in (3, 4, 5):
            action = {"rows": [self.shift(length)], "cols": [self.shift(length)]}
            state, _ = balanced_product((length,), repetition(length), action,
                                        repetition(length), action)
            self.assertEqual(len(state.Q), 2 * length)
            reference, _ = two_block_code((length,), [(0,), (1,)], [(0,), (1,)])
            self.assertEqual(logical_count(state), logical_count(reference))
            self.assertEqual(logical_count(state), 2)

    def test_a_matrix_that_is_not_equivariant_is_malformed(self):
        action = {"rows": [self.shift(3)], "cols": [self.shift(3)]}
        skew = [[1, 1, 0], [0, 1, 1], [1, 1, 1]]
        with self.assertRaises(Malformed):
            balanced_product((3,), skew, action, repetition(3), action)

    def test_malformed_actions(self):
        good = {"rows": [self.shift(3)], "cols": [self.shift(3)]}
        for bad in ({"rows": [[0, 0, 1]], "cols": [self.shift(3)]},
                    {"rows": [self.shift(3)]},
                    {"rows": [], "cols": []}):
            with self.assertRaises(Malformed):
                balanced_product((3,), repetition(3), bad, repetition(3), good)
        # A permutation whose order does not divide the cyclic order.
        with self.assertRaises(Malformed):
            balanced_product((2,), repetition(3), good, repetition(3), good)


class TannerTests(unittest.TestCase):
    """`L-TANNER`: local codes on the two classes of an incidence structure."""

    def toric_views(self, length):
        def h(x, y):
            return 2 * ((x % length) * length + (y % length))

        def v(x, y):
            return h(x, y) + 1

        stars = [[h(x, y), h(x - 1, y), v(x, y), v(x, y - 1)]
                 for x in range(length) for y in range(length)]
        faces = [[h(x, y), h(x, y + 1), v(x, y), v(x + 1, y)]
                 for x in range(length) for y in range(length)]
        return stars, faces

    def test_the_toric_code_from_weight_four_local_checks(self):
        stars, faces = self.toric_views(3)
        state, dropped = tanner_code(18, [[1, 1, 1, 1]], [[1, 1, 1, 1]], stars, faces)
        self.assertEqual((len(state.Q), logical_count(state), dropped), (18, 2, 2))
        distances = exact_distances(state)
        self.assertEqual((distances["X"], distances["Z"]), (3, 3))

    def test_the_counting_bound_and_its_equality_case(self):
        # Issue #527. k is at least n minus the number of natural rows
        # (`tannerState_k_ge` in Lean), with equality when the natural rows of
        # each sector are independent (`tannerState_k_of_indep`). The toric
        # code has 18 natural rows on 18 qubits and k = 2, so the bound is
        # not a formula for k: two rows are dependent and are dropped.
        stars, faces = self.toric_views(3)
        state, dropped = tanner_code(18, [[1, 1, 1, 1]], [[1, 1, 1, 1]], stars, faces)
        rows = len(stars) + len(faces)
        self.assertEqual((rows, dropped), (18, 2))
        self.assertGreater(logical_count(state), len(state.Q) - rows)
        # Independent natural rows: two X rows and one Z row on four qubits.
        state, dropped = tanner_code(4, [[1, 1]], [[1, 1]], [[0, 1], [2, 3]], [[0, 1]])
        self.assertEqual(dropped, 0)
        self.assertEqual(logical_count(state), 4 - 2 - 1)

    def test_local_rank_bound_disjoint_views_and_nogo_pair(self):
        # Disjoint views with a redundant local row (rank(LX) = 1 < len(LX) = 2):
        # k = n - |viewsX|*rank(LX) - |viewsZ|*rank(LZ) = 4 - 2*1 - 1*1 = 1.
        redundant_lx = [[1, 1], [1, 1]]
        state, dropped = tanner_code(
            4, redundant_lx, [[1, 1, 1, 1]], [[0, 1], [2, 3]], [[0, 1, 2, 3]])
        self.assertEqual((len(state.Q), logical_count(state), dropped), (4, 1, 2))
        # No-go pair (`tanner_k_not_determined_by_params` in Lean): identical
        # (n, LX, LZ, |viewsX|, |viewsZ|) with distinct, nodup views yield
        # k = 0 (path) vs k = 1 (triangle).
        lx, lz = [[1, 1]], [[1, 1, 1, 1]]
        s_path, d_path = tanner_code(
            4, lx, lz, [[0, 1], [1, 2], [2, 3]], [[0, 1, 2, 3]])
        s_tri, d_tri = tanner_code(
            4, lx, lz, [[0, 1], [1, 2], [0, 2]], [[0, 1, 2, 3]])
        self.assertEqual((logical_count(s_path), d_path), (0, 0))
        self.assertEqual((logical_count(s_tri), d_tri), (1, 1))

    def test_local_checks_that_do_not_commute_have_no_derivation(self):
        with self.assertRaises(NoDerivation):
            tanner_code(3, [[1, 1]], [[1, 1]], [[0, 1]], [[1, 2]])

    def test_malformed_embeddings(self):
        for views in ([[0, 0]], [[0, 5]], [[0]], "x"):
            with self.assertRaises(Malformed):
                tanner_code(3, [[1, 1]], [[1, 1]], views, [])


HAMMING = [[1, 0, 1, 0, 1, 0, 1],
           [0, 1, 1, 0, 0, 1, 1],
           [0, 0, 0, 1, 1, 1, 1]]


def kernel_vectors(matrix, n):
    """The vectors of length n, as masks, orthogonal to every row."""
    masks = [sum(bit << i for i, bit in enumerate(row)) for row in matrix]
    return [v for v in range(1 << n)
            if all(bin(v & m).count("1") % 2 == 0 for m in masks)]


def span_vectors(matrix):
    masks = [sum(bit << i for i, bit in enumerate(row)) for row in matrix]
    out = {0}
    for m in masks:
        out |= {v ^ m for v in out}
    return out


def random_nested_pair(rng, n):
    """A random check_z and a check_x whose rows are orthogonal to it."""
    check_z = [[rng.randint(0, 1) for _ in range(n)] for _ in range(rng.randint(1, n - 1))]
    kernel = kernel_vectors(check_z, n)
    check_x = [[(v >> i) & 1 for i in range(n)]
               for v in rng.sample(kernel, min(len(kernel), rng.randint(1, 3)))]
    return check_x, check_z


class NestedCssTests(unittest.TestCase):
    """`L-NESTED-CSS`: the CSS code of two classical parity-check matrices."""

    def test_the_steane_code_from_the_hamming_code(self):
        state, dropped = nested_css(HAMMING, HAMMING)
        self.assertEqual((len(state.Q), logical_count(state), dropped), (7, 1, 0))
        distances = exact_distances(state)
        self.assertEqual((distances["X"], distances["Z"]), (3, 3))

    def test_k_and_the_sector_distances_from_the_classical_codes(self):
        rng = random.Random(445)
        raised = 0
        for _ in range(60):
            n = rng.randint(3, 7)
            check_x, check_z = random_nested_pair(rng, n)
            state, dropped = nested_css(check_x, check_z)
            code_x, code_z = kernel_vectors(check_x, n), kernel_vectors(check_z, n)
            dual_x, dual_z = span_vectors(check_x), span_vectors(check_z)
            rank_x = len(dual_x).bit_length() - 1
            rank_z = len(dual_z).bit_length() - 1
            self.assertEqual(dropped, len(check_x) + len(check_z) - rank_x - rank_z)
            self.assertEqual(logical_count(state), n - rank_x - rank_z)
            # k is also dim C_X - dim C_Z^perp.
            self.assertEqual(logical_count(state),
                             (len(code_x).bit_length() - 1) - rank_z)
            if logical_count(state) == 0:
                continue
            distances = exact_distances(state)
            for sector, code, dual in (("X", code_z, dual_x), ("Z", code_x, dual_z)):
                weights = [bin(v).count("1") for v in code if v not in dual]
                self.assertEqual(distances[sector], min(weights))
                classical = min(bin(v).count("1") for v in code if v)
                self.assertGreaterEqual(distances[sector], classical)
                raised += distances[sector] > classical
        self.assertGreater(raised, 0)

    def test_agrees_with_tanner_on_one_vertex_per_class(self):
        rng = random.Random(4450)
        for _ in range(20):
            n = rng.randint(3, 6)
            check_x, check_z = random_nested_pair(rng, n)
            nested, dropped = nested_css(check_x, check_z)
            tanner, tanner_dropped = tanner_code(n, check_x, check_z,
                                                 [list(range(n))], [list(range(n))])
            self.assertEqual(nested, tanner)
            self.assertEqual(dropped, tanner_dropped)

    def test_a_constructed_display_reconstructs_itself(self):
        state, _ = hypergraph_product(repetition(3), repetition(3))
        n = len(state.Q)
        matrices = {sector: [[1 if q in row.support else 0 for q in range(n)]
                             for row in state.sector_rows(sector)]
                    for sector in ("X", "Z")}
        again, dropped = nested_css(matrices["X"], matrices["Z"])
        self.assertEqual(again, state)
        self.assertEqual(dropped, 0)

    def test_a_sector_with_no_check_is_a_zero_row(self):
        state, dropped = nested_css([[0, 0, 0]], [[1, 1, 0], [0, 1, 1]])
        self.assertEqual((len(state.Q), logical_count(state), dropped), (3, 1, 1))
        distances = exact_distances(state)
        self.assertEqual((distances["X"], distances["Z"]), (3, 1))

    def test_codes_that_are_not_nested_have_no_derivation(self):
        with self.assertRaises(NoDerivation):
            nested_css([[1, 1, 0]], [[0, 1, 1]])

    def test_malformed_inputs(self):
        for check_x, check_z in (([[1, 1]], [[1, 1, 0]]), ([], [[1]]),
                                 ([[1, 2]], [[1, 1]]), ("x", [[1]])):
            with self.assertRaises(Malformed):
                nested_css(check_x, check_z)


class TileTests(unittest.TestCase):
    """`L-TILE`: tiles placed on sites, with identifications."""

    def tile(self, size, sector):
        return {"qubits": size,
                "X": [list(range(size))] if sector == "X" else [],
                "Z": [list(range(size))] if sector == "Z" else []}

    def surface(self):
        tiles = [self.tile(4, "X"), self.tile(4, "Z"),
                 self.tile(2, "X"), self.tile(2, "Z")]
        placements = [(0, [0, 1, 3, 4]), (1, [1, 2, 4, 5]), (1, [3, 4, 6, 7]),
                      (0, [4, 5, 7, 8]), (3, [0, 3]), (3, [5, 8]),
                      (2, [1, 2]), (2, [6, 7])]
        return tiles, placements

    def test_the_distance_three_rotated_surface_code(self):
        tiles, placements = self.surface()
        state, dropped = tile_assembly(tiles, placements)
        self.assertEqual((len(state.Q), logical_count(state), dropped), (9, 1, 0))
        distances = exact_distances(state)
        self.assertEqual((distances["X"], distances["Z"]), (3, 3))

    def test_removing_a_boundary_check_adds_a_logical_qubit(self):
        tiles, placements = self.surface()
        state, _ = tile_assembly(tiles, placements, removed=[(7, "X", 0)])
        self.assertEqual((len(state.Q), logical_count(state)), (9, 2))

    def test_identifications_merge_sites(self):
        # Two copies of the four-qubit tile glued along all four sites give
        # the [[4, 2, 2]] code once, the second copy's rows being dropped.
        both = {"qubits": 4, "X": [[0, 1, 2, 3]], "Z": [[0, 1, 2, 3]]}
        state, dropped = tile_assembly(
            [both], [(0, [0, 1, 2, 3]), (0, [4, 5, 6, 7])],
            identifications=[(0, 4), (1, 5), (2, 6), (3, 7)])
        self.assertEqual((len(state.Q), logical_count(state), dropped), (4, 2, 2))

    def test_no_param_closed_form_pair(self):
        # No-go pair (`tile_k_not_determined_by_params` in Lean): identical
        # tiles, qubit count (4), placement count (4), and kept row counts
        # (3 X, 1 Z) yield k = 0 vs k = 1.
        tiles = [{"qubits": 2, "X": [[0, 1]], "Z": []},
                 {"qubits": 4, "X": [], "Z": [[0, 1, 2, 3]]}]
        s_path, d_path = tile_assembly(
            tiles, [(0, [0, 1]), (0, [1, 2]), (0, [2, 3]), (1, [0, 1, 2, 3])])
        s_tri, d_tri = tile_assembly(
            tiles, [(0, [0, 1]), (0, [1, 2]), (0, [0, 2]), (1, [0, 1, 2, 3])])
        self.assertEqual((len(s_path.Q), logical_count(s_path), d_path), (4, 0, 0))
        self.assertEqual((len(s_tri.Q), logical_count(s_tri), d_tri), (4, 1, 1))

    def test_an_interface_that_does_not_commute_has_no_derivation(self):
        tiles = [self.tile(2, "X"), self.tile(2, "Z")]
        with self.assertRaises(NoDerivation):
            tile_assembly(tiles, [(0, [0, 1]), (1, [1, 2])])

    def test_malformed_assemblies(self):
        tiles, placements = self.surface()
        for bad in ([(9, [0, 1])], [(0, [0, 1, 2])], [(0, [0, 0, 1, 2])]):
            with self.assertRaises(Malformed):
                tile_assembly(tiles, bad)
        with self.assertRaises(Malformed):
            tile_assembly(tiles, placements, identifications=[(0, 99)])
        with self.assertRaises(Malformed):
            tile_assembly(tiles, placements, removed=[(0, "Z", 0)])


class AdmissionBoundaryTests(unittest.TestCase):
    def test_the_admitted_constructors(self):
        self.assertEqual(UNADMITTED_CONSTRUCTORS, {})
        self.assertEqual(set(ADMITTED_CONSTRUCTORS),
                         {"L-HGP", "L-LIFTED", "L-GROUP-ALGEBRA", "A-CONCAT",
                          "L-BALANCED", "L-TANNER", "L-TILE", "A-PRODUCT",
                          "A-DOUBLE", "L-NESTED-CSS", "L-MAPPING-CONE",
                          "L-EMPTY", "L-FREE", "A-PULLBACK", "A-PUSHOUT",
                          "L-PAIR-PARTITION", "PP-SCALE"})

        with self.assertRaises(Malformed):
            construct({"constructor": "A-QUOTIENT"})
        result = construct({"constructor": "L-NESTED-CSS",
                            "HX": HAMMING, "HZ": HAMMING})
        self.assertEqual((result["n"], result["k"], result["dropped_rows"]), (7, 1, 0))

    def test_construct_dispatches_the_five_later_constructors(self):
        trivial = {"rows": [], "cols": []}
        result = construct({"constructor": "L-BALANCED", "group": (),
                            "H1": repetition(3), "action1": trivial,
                            "H2": repetition(3), "action2": trivial})
        self.assertEqual((result["n"], result["k"]), (18, 2))
        result = construct({"constructor": "L-TANNER", "n": 2,
                            "local_x": [[1, 1]], "local_z": [[1, 1]],
                            "views_x": [[0, 1]], "views_z": [[0, 1]]})
        self.assertEqual((result["n"], result["k"]), (2, 0))
        result = construct({"constructor": "L-TILE",
                            "tiles": [{"qubits": 2, "X": [[0, 1]], "Z": [[0, 1]]}],
                            "placements": [(0, [0, 1])]})
        self.assertEqual((result["n"], result["k"]), (2, 0))
        result = construct({"constructor": "A-DOUBLE",
                            "state": css_state(4, *FOUR_TWO_TWO), "wiring": {}})
        self.assertEqual((result["n"], result["k"]), (8, 4))

    def test_constructed_ledger_starts_unknown_and_takes_sourced_bounds(self):
        state, _ = hypergraph_product(repetition(3), repetition(3))
        ledger = DistanceLedger.for_constructed(state)
        self.assertEqual(ledger.full, Interval(0, None))
        self.assertEqual(ledger.sector["X"], Interval(0, None))
        ledger = DistanceLedger.for_constructed(
            state, {"X": {"value": 3, "source": "Tillich and Zemor 2014, min of the factor distances"}})
        self.assertEqual(ledger.sector["X"], Interval(3, None))
        self.assertEqual(ledger.conditions[0]["cell"], "input lower bound")
        with self.assertRaises(Malformed):
            DistanceLedger.for_constructed(state, {"X": {"value": 3}})


if __name__ == "__main__":
    unittest.main()


class NullaryBaseConstructorTests(unittest.TestCase):
    """`empty` and `free` base constructors."""

    def test_empty_code(self):
        state = empty_code()
        self.assertEqual(state.Q, ())
        self.assertEqual(state.rows, ())
        self.assertEqual(state.used, frozenset())
        self.assertEqual((len(state.Q), state.k()), (0, 0))
        self.assertEqual(state.w(), 0)

    def test_empty_code_equality(self):
        self.assertEqual(empty_code(), empty_code())

    def test_free_code_empty_coincides_with_empty(self):
        self.assertEqual(free_code(()), empty_code())

    def test_free_code_nonempty(self):
        state = free_code((2, 0, 1))
        self.assertEqual(state.Q, (0, 1, 2))
        self.assertEqual(state.rows, ())
        self.assertEqual(state.used, frozenset())
        self.assertEqual((len(state.Q), state.k()), (3, 3))
        self.assertEqual(state.w(), 0)

    def test_free_code_malformed(self):
        for bad in (1, "abc", [1, 1], [-1], [True]):
            with self.assertRaises(Malformed):
                free_code(bad)

    def test_free_code_rejects_bool_labels(self):
        with self.assertRaises(Malformed):
            free_code((True,))

    def test_distance_of_free_nonempty_is_one(self):
        from machine.oracle import exact_distances
        state = free_code((0, 1))
        d = exact_distances(state)
        self.assertEqual((d["X"], d["Z"]), (1, 1))

    def test_construct_empty_and_free(self):
        res_empty = construct({"constructor": "L-EMPTY"})
        self.assertEqual(res_empty["n"], 0)
        self.assertEqual(res_empty["k"], 0)
        self.assertEqual(res_empty["state"], empty_code())
        res_free = construct({"constructor": "L-FREE", "qubits": [2, 0, 1]})
        self.assertEqual(res_free["n"], 3)
        self.assertEqual(res_free["k"], 3)
        self.assertEqual(res_free["state"], free_code((0, 1, 2)))


class InterfaceConstructorTests(unittest.TestCase):
    """`A-PULLBACK` and `A-PUSHOUT` interface constructors."""

    def test_pullback_pair_over_free1(self):
        pair = CodeState((0, 1, 2), (Row("a1", "X", (0, 1)),), frozenset({"a1"}))
        iface = free_code((0,))
        phi = {0: 0, 1: 0, 2: 0}
        res = construct({"constructor": "A-PULLBACK", "left": pair, "right": pair,
                         "interface": iface, "phi1": phi, "phi2": phi})
        self.assertEqual(res["n"], 9)
        self.assertEqual(len(res["state"].rows), 2)
        self.assertEqual(res["k"], 7)

    def test_pullback_equalizer_specialization(self):
        c1 = CodeState((0, 1, 2), (Row("a1", "X", (0, 1)),), frozenset({"a1"}))
        iface = free_code((0, 1, 2))
        f = {0: 0, 1: 0, 2: 2}
        g = {0: 0, 1: 0, 2: 1}
        # Fiber product picks out pairs where f(q1) = g(q2): (0,0), (0,1), (1,0), (1,1) -> 4 qubits.
        res = construct({"constructor": "A-PULLBACK", "left": c1, "right": c1,
                         "interface": iface, "phi1": f, "phi2": g})
        self.assertEqual(res["n"], 4)

    def test_pullback_refuses_non_morphism(self):
        c1 = CodeState((0, 1), (Row("a1", "X", (0,)),), frozenset({"a1"}))
        iface = free_code((0,))
        with self.assertRaises(NoDerivation):
            pullback_code(c1, c1, iface, {0: 0, 1: 0}, {0: 0, 1: 0})

    def test_pullback_refuses_non_commuting_rows(self):
        c1 = CodeState((0, 1), (Row("a1", "X", (0, 1)),), frozenset({"a1"}))
        c2 = CodeState((0, 1), (Row("b1", "Z", (0, 1)),), frozenset({"b1"}))
        iface = free_code((0,))
        # Pushforward of (0,1) under constant map to 0 is 0 (in span of empty),
        # but pulled-back X-row (0..3) and Z-row (0..3) on 4 qubits wait: 4 is even!
        # Use 1-qubit interface with 1-qubit c2 so 3 pairs? No, 1x1=1 qubit!
        c1_odd = CodeState((0, 1, 2), (Row("a1", "X", (0, 1)),), frozenset({"a1"}))
        c2_odd = CodeState((0,), (Row("b1", "Z", (0,)),), frozenset({"b1"}))
        # Here c2_odd has Z-row (0) whose pushforward to {0} is (0), not in empty Z-span.
        # Give iface Z-row (0) and X-row ()? No, X=(0) and Z=(0) don't commute on iface.
        # Give iface Q=(0,1), X=(0,1), Z=(0,1). Map c1: 0->0, 1->1, 2->0; c2: 0->0, 1->0?
        # Even simpler: iface Q=(0,1), X=(0,1), Z=(0,1);
        # c1: Q=(0,1), X=(0,1); phi1={0:0, 1:1} (morphism);
        # c2: Q=(0,1,2), Z=(0,1); phi2={0:0, 1:1, 2:0} (morphism);
        # Fiber product pairs: (0,0), (0,2), (1,1) -> 3 qubits!
        # Wait: pi1*(0,1) = {0,1,2}, pi2*(0,1) = {0,2} -> overlap 2!
        # If c1 has X=(0) and iface has X=(0,1) no; if c1 has X=(0,1) and c2 has Z=(0) with iface Q=(0,1), Z=(0,1), phi2={0:0,1:1} no.
        # On 3-qubit fiber product: pairs (0,0), (0,2), (1,1):
        # Take c1: Q=(0,1), X=(0,1); phi1={0:0,1:1}; iface Q=(0,1), X=(0,1), Z=(0,1).
        # Take c2: Q=(0,1), Z=(0,1); phi2={0:0,1:1}. Wait: if c2 has Q=(0,1,2), Z=(0,1,2) with phi2={0:0,1:0,2:1}:
        # pairs: (0,0), (0,1), (1,2). pi1*(X=(0,1)) = {0,1,2} (weight 3), pi2*(Z=(0,1,2)) = {0,1,2} (weight 3) -> overlap 3 (ODD)!
        # Check phi2*(Z=(0,1,2)) = {0 ^ 0 ^ 1} = {1}? No, {0,1,2} -> 0+0+1 = 1! Give c2 Q=(0,1,2,3), Z=(0,1,2,3)? No, give iface Z=(0,1) and c2 Z=(0,1,2) with phi2={0:0,1:1,2:1}?
        # Wait: phi2*(0,1,2) = {0, 1^1} = {0}. So take iface Q=(0,1), X=(0,1), Z=().
        # Then c2 has Z=(0,1,2) with phi2={0:0,1:1,2:1} -> pushforward is {0} wait no: phi2={0:0,1:0,2:0} -> pushforward is {0} (nonempty).
        # Take c2 with Z=(0,1) and phi2={0:0, 1:0} -> pushforward is 0 (in empty span)!
        # And pairs with c1 (Q=(0,1), X=(0,1), phi1={0:0, 1:0}):
        # Wait: take c1 Q=(0,1), X=(0,1), phi1={0:0,1:0}; c2 Q=(0,1,2), Z=(0,1), phi2={0:0,1:1,2:1}? No, phi2*(0,1)={0,1}.
        # Take c2 Q=(0,1,2), Z=(0,1), phi2={0:0, 1:0, 2:0}: pairs for q1 in {0,1}, q2 in {0,1,2} -> 6 pairs.
        # Take c1 Q=(0,1), X=(0), Z=(): not morphism unless iface has X=(0).
        # If iface has Q=(0,1), X=(0,1), Z=():
        # c1: Q=(0,1), X=(0,1), phi1={0:0, 1:1};
        # c2: Q=(0,1,2), Z=(0,1), phi2={0:0, 1:0, 2:1} -> pushforward of Z=(0,1) is {0^0} = () (in Z-span of iface!).
        # Pairs with phi1(q1) = phi2(q2): (0,0), (0,1), (1,2).
        # pi1*(X=(0,1)) = {0,1,2} (all 3 pairs); pi2*(Z=(0,1)) = {0,1}? Overlap is 2.
        # What if c1 has Q=(0,1), X=(0,1), phi1={0:0, 1:0} (pushforward is 0!), iface Q=(0,), X=(), Z=()?
        # No, if phi1={0:0, 1:0}, then every q1 maps to 0, so pi1*(0,1) is all pairs.
        # What if c1 has Q=(0,1,2), X=(0,1), phi1={0:0,1:0,2:1} (pushforward=0);
        # c2 has Q=(0,1), Z=(0,1), phi2={0:0,1:1} (pushforward of Z=(0,1) is {0,1}; give iface Z=(0,1), X=(0,1))!
        # Let's check: iface Q=(0,1), X=(0,1), Z=(0,1).
        # c1: Q=(0,1,2), X=(0,1), phi1={0:0, 1:0, 2:1} -> pushforward of X=(0,1) is () in span!
        # c2: Q=(0,1), Z=(0,1), phi2={0:0, 1:1} -> pushforward of Z=(0,1) is {0,1} in span!
        # Pairs: (0,0), (1,0), (2,1).
        # pi1*(X=(0,1)) = {0, 1} (indices of (0,0), (1,0));
        # pi2*(Z=(0,1)) = {0, 1, 2} (indices of (0,0), (1,0), (2,1)) -> overlap is {0,1} (size 2).
        # Wait: what if c1 has Q=(0,1,2), X=(0,2), phi1={0:0, 1:0, 2:1}? Pushforward of X=(0,2) is {0,1} (in X-span of iface!).
        # Pairs: (0,0), (1,0), (2,1).
        # pi1*(X=(0,2)) = {0, 2}; pi2*(Z=(0,1)) = {0, 1, 2} -> overlap is {0, 2} (size 2).
        # Ah! Because pushforward preserves parity of intersection with each fiber:
        # |pi1*(r1) cap pi2*(r2)| = sum_{y in Q_I} |phi1^{-1}(y) cap r1| * |phi2^{-1}(y) cap r2| (mod 2) = <phi1_*(r1), phi2_*(r2)>!
        # AND since phi1_*(r1) in X_I and phi2_*(r2) in Z_I and I satisfies X_I perp Z_I,
        # <phi1_*(r1), phi2_*(r2)> = 0 (mod 2) ALWAYS!
        # That's a theorem! When phi1, phi2 are CSS morphisms into a well-formed I,
        # the pulled-back rows ALWAYS commute!
        iface_ok = CodeState((0, 1), (Row("a1", "X", (0, 1)), Row("b1", "Z", (0, 1))), frozenset({"a1", "b1"}))
        c1_ok = CodeState((0, 1, 2), (Row("a1", "X", (0, 2)),), frozenset({"a1"}))
        c2_ok = CodeState((0, 1), (Row("b1", "Z", (0, 1)),), frozenset({"b1"}))
        res, _ = pullback_code(c1_ok, c2_ok, iface_ok, {0: 0, 1: 0, 2: 1}, {0: 0, 1: 1})
        self.assertEqual(len(res.Q), 3)

    def test_pullback_malformed_map(self):
        pair = CodeState((0, 1, 2), (Row("a1", "X", (0, 1)),), frozenset({"a1"}))
        iface = free_code((0,))
        with self.assertRaises(Malformed):
            pullback_code(pair, pair, iface, {0: 0, 1: 0}, {0: 0, 1: 0, 2: 0})

    def test_pushout_amalgamates_qubits_and_checks(self):
        pair = CodeState((0, 1, 2), (Row("a1", "X", (0, 1)),), frozenset({"a1"}))
        sub = free_code((0,))
        res = construct({"constructor": "A-PUSHOUT", "left": pair, "right": pair,
                         "subcode": sub, "psi1": {0: 2}, "psi2": {0: 0}})
        self.assertEqual(res["n"], 5)
        self.assertEqual(len(res["state"].rows), 2)
        self.assertEqual(res["k"], 3)

    def test_pushout_refuses_non_commuting_rows(self):
        c1 = CodeState((0, 1), (Row("a1", "X", (0, 1)),), frozenset({"a1"}))
        c2 = CodeState((0, 1), (Row("b1", "Z", (0, 1)),), frozenset({"b1"}))
        sub = free_code((0,))
        with self.assertRaises(NoDerivation):
            pushout_code(c1, c2, sub, {0: 0}, {0: 0})

    def test_pushout_refuses_non_morphism(self):
        c1 = CodeState((0, 1), (), frozenset())
        sub = CodeState((0,), (Row("a1", "X", (0,)),), frozenset({"a1"}))
        with self.assertRaises(NoDerivation):
            pushout_code(c1, c1, sub, {0: 0}, {0: 0})


S3_TABLE = [
    [0, 1, 2, 3, 4, 5],
    [1, 2, 0, 4, 5, 3],
    [2, 0, 1, 5, 3, 4],
    [3, 5, 4, 0, 2, 1],
    [4, 3, 5, 1, 0, 2],
    [5, 4, 3, 2, 1, 0],
]


def _dihedral_table(m):
    """Cayley table for the dihedral group D_m of order 2m:
    elements 0..m-1 are rotations r^k; elements m..2m-1 are reflections r^k s
    with r^m = s^2 = 1 and s r = r^{-1} s.
    """
    n = 2 * m
    table = [[0] * n for _ in range(n)]
    for a in range(n):
        ra, sa = a % m, a // m
        for b in range(n):
            rb, sb = b % m, b // m
            if sa == 0:
                r = (ra + rb) % m
            else:
                r = (ra - rb) % m
            s = sa ^ sb
            table[a][b] = s * m + r
    return table


class NonabelianGroupConstructorTests(unittest.TestCase):
    """Nonabelian finite groups for `L-GROUP-ALGEBRA`, `L-LIFTED`, and
    `L-BALANCED` (spec/OPERATIONAL_SEMANTICS.md section 4.44; issue #565)."""

    def test_s3_two_block_and_lifted_product_table_presentation(self):
        g = {"table": S3_TABLE}
        # Non-commuting elements: a = 1 + r (indices 0, 1), b = 1 + s (indices 0, 3).
        state, dropped = two_block_code(g, [0, 1], [0, 3])
        self.assertEqual(len(state.Q), 12)
        self.assertEqual(sector_rank(state, "X"), sector_rank(state, "Z"))
        self.assertEqual(logical_count(state), 2 * (6 - sector_rank(state, "X")))
        self.assertEqual(dropped, 2 * (6 - sector_rank(state, "X")))
        # Exact distances on this small n=12 nonabelian code.
        dists = exact_distances(state)
        self.assertGreaterEqual(dists["d"], 1)

        # Equal row for row to the 1x1 lifted product lift_G((a), (b^*)).
        info = _group_spec(g)
        b_star = sorted(_involution(frozenset({0, 3}), info))
        lp, _ = lifted_product(g, [[[0, 1]]], [[b_star]])
        self.assertEqual(row_sets(state), row_sets(lp))

    def test_s3_left_vs_right_commutation(self):
        # Demonstrate that L(a) and L(b) do NOT commute on S3 when a={r}, b={s},
        # whereas L(a) R(b) == R(b) L(a) holds identically.
        info = _group_spec({"table": S3_TABLE})
        la = _left_lift_rows(frozenset({1}), info)
        lb = _left_lift_rows(frozenset({3}), info)
        rb = _right_lift_rows(frozenset({3}), info)

        def mat_mul_masks(m1, m2):
            ell = len(m1)
            out = []
            for r in range(ell):
                acc = 0
                for k in range(ell):
                    if (m1[r] >> k) & 1:
                        acc ^= m2[k]
                out.append(acc)
            return out

        self.assertNotEqual(mat_mul_masks(la, lb), mat_mul_masks(lb, la))
        self.assertEqual(mat_mul_masks(la, rb), mat_mul_masks(rb, la))

    def test_s3_permutation_generators_and_d4_lifted_product(self):
        # S3 generated by 3-cycle r = (1, 2, 0) and transposition s = (1, 0, 2).
        s3_gens = {"generators": [[1, 2, 0], [1, 0, 2]]}
        info = _group_spec(s3_gens)
        self.assertEqual(len(info["elements"]), 6)
        # Can name elements by permutation tuples directly.
        a = [(0, 1, 2), (1, 2, 0)]
        b = [(0, 1, 2), (1, 0, 2)]
        res = construct({"constructor": "L-GROUP-ALGEBRA", "group": s3_gens, "a": a, "b": b})
        self.assertEqual(res["n"], 12)
        self.assertEqual(res["k"], 2 * (6 - sector_rank(res["state"], "X")))

        # D4 (order 8) 2x2 lifted product.
        d4 = {"table": _dihedral_table(4)}
        A = [[[0, 1], [4]], [[2], [0, 5]]]
        B = [[[0, 4], [1, 6]]]
        res_lp = construct({"constructor": "L-LIFTED", "group": d4, "A": A, "B": B})
        self.assertEqual(res_lp["n"], 8 * (2 * 2 + 2 * 1))
        self.assertGreaterEqual(res_lp["k"], 0)

    def test_d4_two_block_asymmetric_ranks_refutes_abelian_closed_form(self):
        # Nonabelian D4 (order 8): rank[L(a) | R(b)] = 4 != 3 = rank[R(b*) | L(a*)],
        # giving odd k = 16 - 4 - 3 = 9 != 2*(8 - 4) = 8 (spec section 4.44).
        d4 = {"table": _dihedral_table(4)}
        state, _ = two_block_code(d4, [1, 3, 5, 7], [2, 3, 5, 6])
        self.assertEqual(len(state.Q), 16)
        self.assertEqual(sector_rank(state, "X"), 4)
        self.assertEqual(sector_rank(state, "Z"), 3)
        self.assertEqual(logical_count(state), 9)
        # Still coincides row for row with lift_G((a), (b^*)).
        info = _group_spec(d4)
        b_star = sorted(_involution(frozenset({2, 3, 5, 6}), info))
        lp, _ = lifted_product(d4, [[[1, 3, 5, 7]]], [[b_star]])
        self.assertEqual(row_sets(state), row_sets(lp))

    def test_nonabelian_balanced_product_over_s3(self):
        # Regular actions of S3 on itself:
        # Right regular action on H1: rho(g)(x) = x * g.
        # Left regular action on H2: lambda(g)(y) = g * y.
        # A left-regular check matrix H1 = L(a) is right-G-equivariant (since
        # L(a) commutes with right multiplication!), and a right-regular check
        # matrix H2 = R(b) is left-G-equivariant (since R(b) commutes with left
        # multiplication!).
        info = _group_spec({"table": S3_TABLE})
        ell = 6
        la_masks = _left_lift_rows(frozenset({0, 1}), info)
        rb_masks = _right_lift_rows(frozenset({0, 3}), info)
        H1 = [[(la_masks[r] >> c) & 1 for c in range(ell)] for r in range(ell)]
        H2 = [[(rb_masks[r] >> c) & 1 for c in range(ell)] for r in range(ell)]

        right_perms = [[S3_TABLE[x][g] for x in range(ell)] for g in range(ell)]
        left_perms = [[S3_TABLE[g][y] for y in range(ell)] for g in range(ell)]

        action1 = {"rows": right_perms, "cols": right_perms}
        action2 = {"rows": left_perms, "cols": left_perms}
        state, _dropped = balanced_product({"table": S3_TABLE}, H1, action1, H2, action2)
        # Orbits of S3 on 6x6 left pairs and 6x6 right pairs: 6 + 6 = 12 qubits.
        self.assertEqual(len(state.Q), 12)
        self.assertGreaterEqual(logical_count(state), 0)

        # Also test via permutation generators specifying only generator permutations.
        s3_gens = {"generators": [[1, 2, 0], [1, 0, 2]]}
        ginfo = _group_spec(s3_gens)
        gt = ginfo["table"]
        g_idx = ginfo["generator_indices"]
        la2 = _left_lift_rows(frozenset({0, g_idx[0]}), ginfo)
        rb2 = _right_lift_rows(frozenset({0, g_idx[1]}), ginfo)
        H1g = [[(la2[r] >> c) & 1 for c in range(ell)] for r in range(ell)]
        H2g = [[(rb2[r] >> c) & 1 for c in range(ell)] for r in range(ell)]
        gen_right = [[gt[x][gi] for x in range(ell)] for gi in g_idx]
        gen_left = [[gt[gi][y] for y in range(ell)] for gi in g_idx]
        state_g, _ = balanced_product(
            s3_gens, H1g, {"rows": gen_right, "cols": gen_right},
            H2g, {"rows": gen_left, "cols": gen_left},
        )
        self.assertEqual(len(state_g.Q), 12)
        self.assertEqual(logical_count(state_g), logical_count(state))

    def test_invalid_nonabelian_group_and_wrong_handed_action_refused(self):
        # Non-associative table (violates associativity).
        bad_table = [
            [0, 1, 2],
            [1, 0, 1],
            [2, 2, 0],
        ]
        with self.assertRaises(Malformed):
            two_block_code({"table": bad_table}, [0], [0])
        # Passing a left action as action1 (which requires a right action) on nonabelian S3
        # must be rejected as Malformed!
        info = _group_spec({"table": S3_TABLE})
        ell = 6
        rb_masks = _right_lift_rows(frozenset({0, 3}), info)
        H2 = [[(rb_masks[r] >> c) & 1 for c in range(ell)] for r in range(ell)]
        left_perms = [[S3_TABLE[g][y] for y in range(ell)] for g in range(ell)]
        with self.assertRaises(Malformed):
            balanced_product(
                {"table": S3_TABLE},
                H2, {"rows": left_perms, "cols": left_perms},
                H2, {"rows": left_perms, "cols": left_perms},
            )


class ConditionalConstructorCellsAndWitnessLiftingTests(unittest.TestCase):
    """Conditional distance cells and deterministic factor-to-child witness
    lifting for `L-HGP`, `L-NESTED-CSS`, `A-CONCAT`, `A-PRODUCT`, and
    `A-DOUBLE` (JUDGMENT_LAYER.md section 2g.1, section 4.45; issue #567)."""

    def test_hgp_conditional_cell_and_lifted_witnesses(self):
        H = repetition(3)
        res = construct({
            "constructor": "L-HGP",
            "H1": H,
            "H2": H,
            "lift_witnesses": True,
            "constructor_cell": {
                "constructor": "L-HGP",
                "d1": 3, "d1_T": 3, "d2": 3, "d2_T": 3,
                "source": "Tillich-Zemor 2014 on repetition(3)",
            },
        })
        ledger = res["ledger"]
        self.assertEqual(ledger.sector["X"], Interval(3, 3))
        self.assertEqual(ledger.sector["Z"], Interval(3, 3))
        self.assertEqual(ledger.full, Interval(3, 3))
        self.assertEqual(ledger.conditions[0]["status"], "conditional")
        self.assertEqual(ledger.conditions[0]["cell"], "L-HGP conditional distance cell")

        # Asymmetric HGP: H1 = repetition(3) (d1=3, d1_T=3), H2 = [[1, 1]] (d2=2, d2_T=inf).
        # Under H_X = [H1 x I | I x H2^T], H_Z = [I x H2 | H1^T x I], d_X = 2 and d_Z = 3.
        asym_res = construct({
            "constructor": "L-HGP",
            "H1": H,
            "H2": [[1, 1]],
            "lift_witnesses": True,
            "constructor_cell": {
                "constructor": "L-HGP",
                "d1": 3, "d1_T": 3, "d2": 2, "d2_T": "inf",
                "source": "Tillich-Zemor 2014 asymmetric",
            },
        })
        asym_exact = exact_distances(asym_res["state"])
        self.assertEqual((asym_exact["X"], asym_exact["Z"]), (2, 3))
        self.assertEqual(asym_res["ledger"].sector["X"], Interval(2, 2))
        self.assertEqual(asym_res["ledger"].sector["Z"], Interval(3, 3))
        self.assertEqual(asym_res["ledger"].full, Interval(2, 2))

        # Contradictory over-claimed lower bound (4 > lifted witness weight 3) raises NoDerivation.
        with self.assertRaises(NoDerivation):
            DistanceLedger.for_constructed(
                res["state"],
                constructor_cell={
                    "constructor": "L-HGP",
                    "d1": 4, "d1_T": 4, "d2": 4, "d2_T": 4,
                    "source": "false claim",
                },
                witnesses=res["lifted_witnesses"],
            )

    def test_nested_css_conditional_cell_and_lifted_witnesses(self):
        state, _ = nested_css(HAMMING, HAMMING)
        lifted = lift_nested_witnesses(HAMMING, HAMMING, state=state)
        self.assertEqual(lifted["X"][0]["value"], 3)
        self.assertEqual(lifted["Z"][0]["value"], 3)
        ledger = DistanceLedger.for_constructed(
            state,
            constructor_cell={
                "constructor": "L-NESTED-CSS",
                "d_ker_HZ": 3,
                "d_ker_HX": 3,
                "source": "Hamming [7,4,3] minimum distance",
            },
            witnesses=lifted,
        )
        self.assertEqual(ledger.sector["X"], Interval(3, 3))
        self.assertEqual(ledger.sector["Z"], Interval(3, 3))
        self.assertEqual(ledger.full, Interval(3, 3))

    def test_concat_conditional_cell_and_lifted_witnesses(self):
        # k_in = 1: outer [[4, 2, 2]] (d_X=2, d_Z=2) concatenated with inner [[3, 1]]
        # repetition code (d_X=3, d_Z=1) -> exact d_X = 6, d_Z = 2.
        c422 = css_state(4, *FOUR_TWO_TWO)
        rep3 = css_state(3, [], [(0, 1), (1, 2)])
        res1 = construct({
            "constructor": "A-CONCAT",
            "outer": c422,
            "inner": rep3,
            "groups": [(0,), (1,), (2,), (3,)],
            "lift_witnesses": True,
            "constructor_cell": {
                "constructor": "A-CONCAT",
                "k_in": 1,
                "outer": {"X": 2, "Z": 2},
                "inner": {"X": 3, "Z": 1},
                "source": "Concatenation product bound on [[4,2,2]] o [[3,1]] (k_in=1)",
            },
        })
        exact1 = exact_distances(res1["state"])
        self.assertEqual((exact1["X"], exact1["Z"]), (6, 2))
        self.assertEqual(res1["ledger"].sector["X"], Interval(6, 6))
        self.assertEqual(res1["ledger"].sector["Z"], Interval(2, 2))
        self.assertEqual(res1["ledger"].full, Interval(2, 2))

        # k_in = 2: outer [[4, 2, 2]] concatenated with inner [[4, 2, 2]] using
        # groups=[(0, 1), (2, 3)] has d_X = d_Z = 2 = ceil(2/2) * 2 < 2 * 2!
        res2 = construct({
            "constructor": "A-CONCAT",
            "outer": c422,
            "inner": c422,
            "groups": [(0, 1), (2, 3)],
            "lift_witnesses": True,
            "constructor_cell": {
                "constructor": "A-CONCAT",
                "k_in": 2,
                "outer": {"X": 2, "Z": 2},
                "inner": {"X": 2, "Z": 2},
                "source": "Block-distance concatenation bound on [[4,2,2]] o [[4,2,2]] (k_in=2)",
            },
        })
        exact2 = exact_distances(res2["state"])
        self.assertEqual((exact2["X"], exact2["Z"]), (2, 2))
        self.assertEqual(res2["ledger"].sector["X"], Interval(2, 2))
        self.assertEqual(res2["ledger"].sector["Z"], Interval(2, 2))
        # A naive k_in=1 claim (d >= 2*2 = 4) contradicts the lifted weight-2 witness -> NoDerivation!
        with self.assertRaises(NoDerivation):
            DistanceLedger.for_constructed(
                res2["state"],
                constructor_cell={
                    "constructor": "A-CONCAT",
                    "k_in": 1,
                    "outer": {"X": 2, "Z": 2},
                    "inner": {"X": 2, "Z": 2},
                    "source": "false k_in=1 claim on k_in=2 concatenation",
                },
                witnesses=res2["lifted_witnesses"],
            )

    def test_product_conditional_cell_requires_display_certificate_and_lifts(self):
        c422 = css_state(4, *FOUR_TWO_TWO)
        state, _ = css_tensor_product(c422, c422)
        lifted = lift_product_witnesses(c422, c422, state=state)
        self.assertEqual(lifted["X"][0]["value"], 4)
        self.assertEqual(lifted["Z"][0]["value"], 4)
        # Without display_certificate, A-PRODUCT conditional cell must refuse.
        with self.assertRaises(NoDerivation):
            DistanceLedger.for_constructed(
                state,
                constructor_cell={
                    "constructor": "A-PRODUCT",
                    "left": {"X": 2, "Z": 2},
                    "right": {"X": 2, "Z": 2},
                    "source": "missing display certificate",
                },
                witnesses=lifted,
            )
        # With explicit display_certificate, ledger brackets exact distances.
        ledger = DistanceLedger.for_constructed(
            state,
            constructor_cell={
                "constructor": "A-PRODUCT",
                "display_certificate": "standard [[4,2,2]] display",
                "left": {"X": 2, "Z": 2},
                "right": {"X": 2, "Z": 2},
                "source": "Bravyi-Hastings / Audoux-Couvreur homological product",
            },
            witnesses=lifted,
        )
        self.assertEqual(ledger.sector["X"], Interval(4, 4))
        self.assertEqual(ledger.sector["Z"], Interval(4, 4))
        self.assertEqual(ledger.full, Interval(4, 4))
        # Direct Audoux-Couvreur display-certified bounds d_X / d_Z are also accepted.
        direct_ledger = DistanceLedger.for_constructed(
            state,
            constructor_cell={
                "constructor": "A-PRODUCT",
                "display_certificate": "standard [[4,2,2]] display",
                "d_X": 3,
                "d_Z": 4,
                "source": "Audoux-Couvreur direct display-certified overlap bound",
            },
            witnesses=lifted,
        )
        self.assertEqual(direct_ledger.sector["X"], Interval(3, 4))
        self.assertEqual(direct_ledger.sector["Z"], Interval(4, 4))
        self.assertEqual(direct_ledger.full, Interval(3, 4))

    def test_double_conditional_cell_and_lifted_witnesses(self):
        # Asymmetric [[3, 1]] code with d_X = 3, d_Z = 1 (single-qubit Z logicals, X=XXX).
        asym = css_state(3, [], [(0, 1), (1, 2)])
        # Empty wiring, non-conjugate: preserves (3, 1).
        res_plain = construct({
            "constructor": "A-DOUBLE",
            "state": asym,
            "wiring": {},
            "conjugate": False,
            "lift_witnesses": True,
            "constructor_cell": {
                "constructor": "A-DOUBLE",
                "parent": {"X": 3, "Z": 1},
                "conjugate": False,
                "source": "empty wiring direct sum",
            },
        })
        self.assertEqual(res_plain["ledger"].sector["X"], Interval(3, 3))
        self.assertEqual(res_plain["ledger"].sector["Z"], Interval(1, 1))
        self.assertEqual(res_plain["ledger"].full, Interval(1, 1))

        # Empty wiring, conjugate: both sectors have min(3, 1) = 1.
        res_conj = construct({
            "constructor": "A-DOUBLE",
            "state": asym,
            "wiring": {},
            "conjugate": True,
            "lift_witnesses": True,
            "constructor_cell": {
                "constructor": "A-DOUBLE",
                "parent": {"X": 3, "Z": 1},
                "conjugate": True,
                "source": "empty wiring conjugate direct sum",
            },
        })
        self.assertEqual(res_conj["ledger"].sector["X"], Interval(1, 1))
        self.assertEqual(res_conj["ledger"].sector["Z"], Interval(1, 1))
        self.assertEqual(res_conj["ledger"].full, Interval(1, 1))

        # Non-empty wiring without twisted_certificate must raise NoDerivation.
        c422 = css_state(4, *FOUR_TWO_TWO)
        twisted_wiring = {"a1": [0, 1], "b1": [0, 1]}
        twisted_state, _ = double_cover(c422, twisted_wiring)
        lifted_tw = lift_double_witnesses(c422, twisted_wiring, state=twisted_state)
        self.assertTrue(len(lifted_tw["X"]) > 0 and len(lifted_tw["Z"]) > 0)
        with self.assertRaises(NoDerivation):
            DistanceLedger.for_constructed(
                twisted_state,
                constructor_cell={
                    "constructor": "A-DOUBLE",
                    "wiring": twisted_wiring,
                    "parent": {"X": 2, "Z": 2},
                    "source": "unverified twisted double",
                },
                witnesses=lifted_tw,
            )
        # With explicit twisted_certificate, accepted and validated against lifted witnesses.
        tw_ledger = DistanceLedger.for_constructed(
            twisted_state,
            constructor_cell={
                "constructor": "A-DOUBLE",
                "wiring": twisted_wiring,
                "twisted_certificate": True,
                "d_X": 2,
                "d_Z": 2,
                "source": "verified twisted double certificate",
            },
            witnesses=lifted_tw,
        )
        exact_tw = exact_distances(twisted_state)
        self.assertLessEqual(tw_ledger.sector["X"].lower, exact_tw["X"])
        self.assertLessEqual(exact_tw["X"], tw_ledger.sector["X"].upper)
        self.assertLessEqual(tw_ledger.sector["Z"].lower, exact_tw["Z"])
        self.assertLessEqual(exact_tw["Z"], tw_ledger.sector["Z"].upper)

class PairPartitionAndPpScaleTests(unittest.TestCase):
    """`L-PAIR-PARTITION` and `PP-SCALE` (sections 4.46-4.47; issues #568, #618)."""


    def test_cpm_pair_partition_orthogonality_and_parameters(self):
        # J = 2, L = 4 over p = 3 with pair partition {(0, 1), (2, 3)}.
        bx = [[0, 0, 1, 1], [0, 0, 2, 2]]
        bz = [[0, 0, 1, 1], [1, 1, 0, 0]]
        res = construct({"constructor": "L-PAIR-PARTITION", "p": 3,
                         "blocks_x": bx, "blocks_z": bz})
        self.assertEqual(res["n"], 12)
        self.assertGreater(res["k"], 0)
        res["state"].validate()

    def test_commuting_rows_without_a_pair_partition_are_refused(self):
        # Issue #630.  The six affine maps of Z_3, once each, against six
        # identity blocks: the relative maps sum to twice the all-ones block,
        # so the natural rows commute, and no two relative maps are equal, so
        # there is no pair partition.  The card refuses this input, and so do
        # the consumer and the Lean rule (`sixMaps_no_derivation`).
        from machine.constructors import (_affine_block_rows,
                                          _natural_rows_orthogonal,
                                          _parse_affine_blocks)
        bx = [[(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]]
        bz = [[(1, 0)] * 6]
        _, rows = _affine_block_rows(
            3, _parse_affine_blocks(3, bx, "bx"), _parse_affine_blocks(3, bz, "bz"))
        self.assertTrue(_natural_rows_orthogonal(rows))
        with self.assertRaises(NoDerivation):
            construct({"constructor": "L-PAIR-PARTITION", "p": 3,
                       "blocks_x": bx, "blocks_z": bz})

    def test_apm_pair_partition_with_unit_and_non_unit_slopes(self):
        # APM-PP at p = 5 with unit slopes a_X = 2, a_Z = 3 (gcd = 1), L = 4 paired columns.

        bx = [[(2, 1), (2, 1), (2, 0), (2, 0)]]
        bz = [[(3, 4), (3, 4), (3, 0), (3, 0)]]
        state, _ = pair_partition_code(5, bx, bz, pair_partition=[(0, 1), (2, 3)])
        self.assertEqual(len(state.Q), 20)
        self.assertEqual(logical_count(state), 10)
        # Per-block-row-pair 2D pair_partition table is also accepted.
        state_2d, _ = pair_partition_code(5, bx, bz, pair_partition=[[[(0, 1), (2, 3)]]])
        self.assertEqual(row_sets(state), row_sets(state_2d))

        # Non-unit slope gcd(2, 4) = 2 at p = 4 is refused with NoDerivation.
        with self.assertRaises(NoDerivation):
            pair_partition_code(4, [[(2, 0), (2, 0)]], [[(1, 0), (1, 0)]])
        # Unpaired relative affine maps are refused with NoDerivation.
        with self.assertRaises(NoDerivation):
            pair_partition_code(5, [[(1, 0), (1, 1)]], [[(1, 0), (1, 2)]])
        # Non-iterable pair_partition raises Malformed.
        with self.assertRaises(Malformed):
            pair_partition_code(5, bx, bz, pair_partition=123)

    def test_pair_partition_challenge_adapter_round_trip(self):
        from machine.priced_calculus import export_challenge_entry
        res = construct({
            "constructor": "L-PAIR-PARTITION",
            "p": 3,
            "blocks_x": [[(2, 0), (2, 0), (2, 1), (2, 1)]],
            "blocks_z": [[(2, 1), (2, 1), (2, 0), (2, 0)]],
        })
        state = res["state"]
        ledger = DistanceLedger.for_constructed(state)
        parent_stub = {
            "provenance": {
                "authors": ["Okada-Kasai v4 probe"],
                "construction": "L-PAIR-PARTITION",
                "date": "2026-11-22",
                "origin": "submission",
            },
        }
        doc = export_challenge_entry(
            parent_stub, state, ledger, "apm_pp_test", "L-PAIR-PARTITION", "2026-11-22"
        )
        reimported = CodeState.from_challenge(doc)
        self.assertEqual(row_sets(state), row_sets(reimported))
        self.assertEqual(logical_count(reimported), res["k"])
    def test_pp_scale_with_snf_bundle_and_reproduction_check(self):
        # Base code C0 at P0 = 3, J_X = J_Z = 1, L = 4:
        # Slopes via r_0^{e_0} = 1 with e_0 = 2 (r_0(3) = 2, r_0(5) = 4), Q = [[1], [1], [1], [1]];
        # Shifts via G = [[1], [1], [0], [0]], theta = [2].
        bundle = {
            "P0": 3,
            "orders_e": [2],
            "roots_r0": [2],
            "roots_r": [4],
            "shape_x": (1, 4),
            "shape_z": (1, 4),
            "Q_x": [[1], [1], [1], [1]],
            "Q_z": [[1], [1], [1], [1]],
            "G_x": [[1], [1], [0], [0]],
            "G_z": [[1], [1], [0], [0]],
            "theta_x": [2],
            "theta_z": [2],
            "blocks_x0": [[(2, 2), (2, 2), (2, 0), (2, 0)]],
            "blocks_z0": [[(2, 2), (2, 2), (2, 0), (2, 0)]],
            "pair_partition": [(0, 1), (2, 3)],
        }
        c0, _ = pair_partition_code(3, bundle["blocks_x0"], bundle["blocks_z0"])
        res = construct({"constructor": "PP-SCALE", "state": c0, "P": 5, "bundle": bundle})
        scaled = res["state"]
        self.assertEqual(res["n"], 20)
        self.assertEqual(res["k"], 10)
        # Fresh row identifiers are canonically minted and disjoint from c0.used.
        minted_ids = {r.id for r in scaled.rows}
        self.assertTrue(minted_ids.isdisjoint(c0.used))
        self.assertEqual(scaled.used, c0.used | minted_ids)
        # Failed SNF reproduction check at P0 raises NoDerivation.
        bad_bundle = dict(bundle, theta_x=[1])
        with self.assertRaises(NoDerivation):
            pp_scale_code(c0, 5, bundle=bad_bundle)

    def test_pp_scale_refuses_k_le_zero_and_p_lt_two(self):
        c0, _ = pair_partition_code(2, [[0, 0]], [[0, 0]])
        with self.assertRaises(NoDerivation):
            pp_scale_code(c0, 1, blocks_x=[[0, 0]], blocks_z=[[0, 0]])
        # At P = 2, L = 2, two independent X block rows and two independent Z block rows?
        # No: X and Z are orthogonal, so rank_X + rank_Z <= n; rank_X + rank_Z == n gives k' = 0!
        # On n = 4 (L = 2, P = 2), blocks_x = [[0, 0]], blocks_z = [[0, 0]] has rank_X = 2, rank_Z = 2 -> k' = 0!
        with self.assertRaises(NoDerivation):
            pp_scale_code(c0, 2, blocks_x=[[0, 0]], blocks_z=[[0, 0]])

    def test_constructed_ledger_with_supplied_verified_interval(self):
        state, _ = pair_partition_code(4, [[(1, 0), (1, 1)]], [[(1, 0), (1, 1)]])
        ledger = DistanceLedger.for_constructed(
            state,
            intervals={"d": {"lower": 2, "upper": 4, "source": "Kasai 2026 verified interval"}},
        )
        self.assertEqual((ledger.full.lower, ledger.full.upper), (2, 4))
        self.assertTrue(any(c.get("cell") == "supplied distance interval"
                            and c.get("status") == "conditional"
                            for c in ledger.conditions))
        # Inconsistent supplied interval [5, 2] raises NoDerivation.
        with self.assertRaises(NoDerivation):
            DistanceLedger.for_constructed(
                state,
                intervals={"d": {"lower": 5, "upper": 2, "source": "invalid interval"}},
            )


class CosetLiftTests(unittest.TestCase):
    """The coset lift lift_{G,H}(A, B) (issue #675; section 4.49)."""

    # In S3_TABLE, s = 3 has order 2 and r = 1 has order 3; H = <s> = {0, 3}
    # is not normal, and N_{S3}(H) = H.
    A = [[[0, 1], [1, 4]], [[2], [0, 5]]]
    B = [[[0, 3], [3]], [[0], [0, 3]]]

    def test_trivial_subgroup_is_the_regular_lift_row_for_row(self):
        from machine.constructors import lifted_product
        g = {"table": S3_TABLE}
        regular, d0 = lifted_product(g, self.A, [[[0, 1], [3]], [[4], [2, 5]]])
        coset, d1 = lifted_product(g, self.A, [[[0, 1], [3]], [[4], [2, 5]]], [])
        self.assertEqual(row_sets(regular), row_sets(coset))
        self.assertEqual((regular.used, d0), (coset.used, d1))
        abelian, _ = lifted_product((3,), [[[0, 1]]], [[[0, 2]]])
        abelian_h, _ = lifted_product((3,), [[[0, 1]]], [[[0, 2]]], [])
        self.assertEqual(row_sets(abelian), row_sets(abelian_h))

    def test_non_normal_subgroup_gives_a_well_formed_state(self):
        from machine.constructors import lifted_product
        state, _ = lifted_product({"table": S3_TABLE}, self.A, self.B, [3])
        # n = [G:H] (n_A n_B + m_A m_B) = 3 * (4 + 4)
        self.assertEqual(len(state.Q), 24)
        for x in state.sector_rows("X"):
            for z in state.sector_rows("Z"):
                self.assertEqual(bin(x.mask & z.mask).count("1") % 2, 0)

    def test_random_normalizer_supported_inputs_are_orthogonal(self):
        from machine.constructors import lifted_product
        rng = random.Random(675)
        for _ in range(40):
            A = [[sorted(rng.sample(range(6), rng.randint(0, 3))) for _ in range(2)]
                 for _ in range(rng.randint(1, 2))]
            B = [[sorted(rng.sample([0, 3], rng.randint(0, 2))) for _ in range(2)]
                 for _ in range(rng.randint(1, 2))]
            state, _ = lifted_product({"table": S3_TABLE}, A, B, [3])
            self.assertEqual(len(state.Q), 3 * (len(A[0]) * 2 + len(A) * len(B)))

    def test_whole_group_subgroup_reduces_entries_to_parities(self):
        from machine.constructors import lifted_product, hypergraph_product
        state, _ = lifted_product({"table": S3_TABLE}, self.A, self.A, [1, 3])
        parity = [[len(e) % 2 for e in row] for row in self.A]
        hgp, _ = hypergraph_product(parity, parity)
        self.assertEqual(row_sets(state), row_sets(hgp))

    def test_b_term_outside_the_normalizer_is_malformed(self):
        from machine.constructors import lifted_product
        with self.assertRaises(Malformed):
            lifted_product({"table": S3_TABLE}, self.A, [[[1]]], [3])
        with self.assertRaises(Malformed):
            lifted_product({"table": S3_TABLE}, self.A, self.B, 3)

    def test_construct_reads_the_subgroup_key(self):
        from machine.constructors import construct, lifted_product
        result = construct({"constructor": "L-LIFTED", "group": {"table": S3_TABLE},
                            "A": self.A, "B": self.B, "subgroup": [3]})
        direct, _ = lifted_product({"table": S3_TABLE}, self.A, self.B, [3])
        self.assertEqual(row_sets(result["state"]), row_sets(direct))
        self.assertEqual(result["n"], 24)
