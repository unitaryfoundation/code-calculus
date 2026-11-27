"""Symplectic inner inputs for `A-CONCAT` (issue #573).

Evidence for a decision, not an admitted rule. The tests pin what the
CSS-composite guard does on the two inner codes the issue names, on CSS
inner codes written symplectically, and on the one way a non-CSS inner
code can pass the guard. Agreement of the guard with the block condition
on random inputs is evidence for the derivation in
`design/A_CONCAT_SYMPLECTIC_INNER_PROPOSAL.md` (development repository
only), not a proof of it.
"""

import random
import unittest

from machine.constructors import concatenate, two_block_code
from machine.experiments.concat_symplectic_inner import (
    INNER_8_2_3,
    INNER_8_3_3,
    _rank,
    _small_outer,
    block_groups,
    check_inner,
    css_composite_state,
    css_split,
    is_css_group,
    pauli,
    symplectic_concatenate,
    symplectic_logical_basis,
)
from machine.priced_calculus import CodeState, Malformed, NoDerivation, Row
from machine.tower_prices import tower_level_data

# The CSS [[4,2,2]] code, written as a symplectic input.
C4_STABILIZERS = [pauli(x_support=(0, 1, 2, 3)), pauli(z_support=(0, 1, 2, 3))]
C4_LOGICALS = [
    (pauli(x_support=(0, 1)), pauli(z_support=(0, 2))),
    (pauli(x_support=(0, 2)), pauli(z_support=(0, 1))),
]


def inner(table):
    stabilizers = [pauli(x, z) for x, z in table]
    return stabilizers, symplectic_logical_basis(8, stabilizers)


def c4_state():
    return _small_outer(4)


def row_space(state, sector):
    return sorted(row.mask for row in state.sector_rows(sector))


class NamedInnerCodeTests(unittest.TestCase):
    def test_the_two_named_inner_codes_are_valid_and_not_css(self):
        for table, k_in in ((INNER_8_3_3, 3), (INNER_8_2_3, 2)):
            stabilizers, logicals = inner(table)
            self.assertEqual(check_inner(8, stabilizers, logicals), k_in)
            self.assertFalse(is_css_group(8, stabilizers))

    def test_the_guard_refuses_the_named_concatenation_shape(self):
        for table, outer, groups in (
                (INNER_8_3_3, _small_outer(6), [(0, 1, 2), (3, 4, 5)]),
                (INNER_8_2_3, _small_outer(4), [(0, 1), (2, 3)])):
            stabilizers, logicals = inner(table)
            n, generators = symplectic_concatenate(
                outer, 8, stabilizers, logicals, groups)
            self.assertEqual(n, 16)
            rank, _, _ = css_split(n, generators)
            # k = k_out: every inner logical qubit is an outer qubit.
            self.assertEqual(n - rank, outer.k())
            self.assertFalse(is_css_group(n, generators))
            with self.assertRaises(NoDerivation):
                css_composite_state(outer, 8, stabilizers, logicals, groups)

    def test_no_choice_of_logical_basis_changes_the_verdict(self):
        # The inner stabilizers sit on a block whatever the logicals are,
        # and no outer stabilizer of this outer code is confined to a block.
        rng = random.Random(573)
        stabilizers, logicals = inner(INNER_8_3_3)
        outer, groups = _small_outer(6), [(0, 1, 2), (3, 4, 5)]
        for _ in range(40):
            twisted = [list(pair) for pair in logicals]
            for pair in twisted:
                for side in (0, 1):
                    s = rng.choice(stabilizers)
                    if rng.random() < 0.5:
                        pair[side] = (pair[side][0] ^ s[0], pair[side][1] ^ s[1])
                if rng.random() < 0.5:
                    pair.reverse()
            twisted = [tuple(pair) for pair in twisted]
            check_inner(8, stabilizers, twisted)
            n, generators = symplectic_concatenate(
                outer, 8, stabilizers, twisted, groups)
            self.assertFalse(is_css_group(n, generators))


class CssInnerTests(unittest.TestCase):
    def test_a_css_inner_gives_the_admitted_concatenation(self):
        outer, groups = c4_state(), [(0, 1), (2, 3)]
        composite = css_composite_state(
            outer, 4, C4_STABILIZERS, C4_LOGICALS, groups)
        representatives = {
            "X": [pair[0][0] for pair in C4_LOGICALS],
            "Z": [pair[1][1] for pair in C4_LOGICALS],
        }
        admitted, _ = concatenate(outer, c4_state(), groups,
                                  representatives=representatives)
        self.assertEqual((composite.n(), composite.k()),
                         (admitted.n(), admitted.k()))
        for sector in ("X", "Z"):
            both = row_space(composite, sector) + row_space(admitted, sector)
            self.assertEqual(_rank(both), _rank(row_space(admitted, sector)))
            self.assertEqual(_rank(both), _rank(row_space(composite, sector)))

    def test_a_swapped_logical_frame_is_the_concatenation_of_the_swapped_outer(self):
        # Lifting X-rows through Z-type logicals and Z-rows through X-type
        # ones is the admitted concatenation of the sector-swapped outer.
        outer = CodeState((0, 1, 2, 3), (
            Row("a1", "X", (0, 1, 2, 3)), Row("b1", "Z", (0, 1)),
            Row("b2", "Z", (2, 3))), frozenset({"a1", "b1", "b2"}))
        swapped_outer = CodeState((0, 1, 2, 3), (
            Row("a1", "X", (0, 1)), Row("a2", "X", (2, 3)),
            Row("b1", "Z", (0, 1, 2, 3))), frozenset({"a1", "a2", "b1"}))
        groups = [(0, 1), (2, 3)]
        swapped_frame = [(pair[1], pair[0]) for pair in C4_LOGICALS]
        composite = css_composite_state(
            outer, 4, C4_STABILIZERS, swapped_frame, groups)
        representatives = {
            "X": [pair[1][0] for pair in swapped_frame],
            "Z": [pair[0][1] for pair in swapped_frame],
        }
        admitted, _ = concatenate(swapped_outer, c4_state(), groups,
                                  representatives=representatives)
        for sector in ("X", "Z"):
            both = row_space(composite, sector) + row_space(admitted, sector)
            self.assertEqual(_rank(both), _rank(row_space(admitted, sector)))
            self.assertEqual(_rank(both), _rank(row_space(composite, sector)))

    def test_a_mixed_logical_frame_depends_on_the_outer_rows(self):
        # X-bar replaced by X-bar times Z-bar (a Y-type logical).
        mixed = [((pair[0][0] ^ pair[1][0], pair[0][1] ^ pair[1][1]), pair[1])
                 for pair in C4_LOGICALS]
        check_inner(4, C4_STABILIZERS, mixed)
        groups = [(0, 1), (2, 3)]
        # With an X-row alone the lifted row is mixed and nothing repairs it.
        x_only = CodeState((0, 1, 2, 3), (Row("a1", "X", (0, 1, 2, 3)),),
                           frozenset({"a1"}))
        with self.assertRaises(NoDerivation):
            css_composite_state(x_only, 4, C4_STABILIZERS, mixed, groups)
        # With a Z-row on the same support, the product of the two lifted
        # rows is X-type, and the composite is the one of the plain frame.
        plain = css_composite_state(c4_state(), 4, C4_STABILIZERS,
                                    C4_LOGICALS, groups)
        twisted = css_composite_state(c4_state(), 4, C4_STABILIZERS, mixed,
                                      groups)
        for sector in ("X", "Z"):
            both = row_space(plain, sector) + row_space(twisted, sector)
            self.assertEqual(_rank(both), _rank(row_space(plain, sector)))
            self.assertEqual(_rank(both), _rank(row_space(twisted, sector)))


class BlockConditionTests(unittest.TestCase):
    # The inner code with the single stabilizer YY on two qubits.
    YY = [pauli(x_support=(0, 1), z_support=(0, 1))]
    YY_LOGICALS = [(pauli(x_support=(0, 1)), pauli(x_support=(0,), z_support=(0,)))]

    def test_a_non_css_inner_passes_only_through_confined_outer_stabilizers(self):
        check_inner(2, self.YY, self.YY_LOGICALS)
        self.assertFalse(is_css_group(2, self.YY))
        # Outer qubits each fixed by a weight-1 X-row: the lift XX joins YY
        # on the block and the block group {XX, ZZ} is CSS.
        fixed = CodeState((0, 1), (Row("a1", "X", (0,)), Row("a2", "X", (1,))),
                          frozenset({"a1", "a2"}))
        groups = [(0,), (1,)]
        for block in block_groups(fixed, 2, self.YY, self.YY_LOGICALS, groups):
            self.assertEqual(len(block), 2)
            self.assertTrue(is_css_group(2, block))
        composite = css_composite_state(fixed, 2, self.YY, self.YY_LOGICALS,
                                        groups)
        self.assertEqual((composite.n(), composite.k()), (4, 0))
        self.assertEqual(row_space(composite, "X"), [0b0011, 0b1100])
        self.assertEqual(row_space(composite, "Z"), [0b0011, 0b1100])
        # The same inner code on an outer code with no confined stabilizer.
        free = _small_outer(2)
        for block in block_groups(free, 2, self.YY, self.YY_LOGICALS, groups):
            self.assertEqual(block, self.YY)
        with self.assertRaises(NoDerivation):
            css_composite_state(free, 2, self.YY, self.YY_LOGICALS, groups)

    def test_a_css_composite_has_css_block_groups(self):
        # Random outer codes, three inner codes, random logical frames. The
        # implication checked is the one derived in the note.
        rng = random.Random(5730)
        inners = [
            (2, self.YY, self.YY_LOGICALS),
            (4, C4_STABILIZERS, C4_LOGICALS),
            (1, [], [(pauli(x_support=(0,)), pauli(z_support=(0,)))]),
        ]
        css_seen = refused_seen = 0
        for _ in range(400):
            n_in, stabilizers, logicals = rng.choice(inners)
            logicals = [tuple(pair) if rng.random() < 0.7 else (pair[1], pair[0])
                        for pair in logicals]
            k_in = len(logicals)
            blocks = rng.randint(1, 3)
            n_out = k_in * blocks
            rows, used = [], set()
            for sector, prefix in (("X", "a"), ("Z", "b")):
                for index in range(rng.randint(0, 2)):
                    support = tuple(sorted(rng.sample(
                        range(n_out), rng.randint(1, n_out))))
                    rows.append(Row("%s%d" % (prefix, index + 1), sector, support))
                    used.add("%s%d" % (prefix, index + 1))
            outer = CodeState(tuple(range(n_out)), tuple(rows), frozenset(used))
            try:
                outer.validate()
            except Malformed:
                continue
            labels = list(range(n_out))
            rng.shuffle(labels)
            groups = [tuple(labels[i * k_in:(i + 1) * k_in])
                      for i in range(blocks)]
            n, generators = symplectic_concatenate(
                outer, n_in, stabilizers, logicals, groups)
            block_ok = all(
                is_css_group(n_in, block) for block in block_groups(
                    outer, n_in, stabilizers, logicals, groups))
            if is_css_group(n, generators):
                css_seen += 1
                self.assertTrue(block_ok)
            else:
                refused_seen += 1
        self.assertGreater(css_seen, 20)
        self.assertGreater(refused_seen, 20)


class InputValidationTests(unittest.TestCase):
    def test_bad_inner_inputs_are_malformed(self):
        stabilizers, logicals = inner(INNER_8_3_3)
        anticommuting = [pauli(x_support=(0,)), pauli(z_support=(0,))]
        cases = [
            (2, anticommuting, []),
            (8, stabilizers + [stabilizers[0]], logicals[:2]),
            (8, stabilizers, logicals[:2]),
            (8, stabilizers, [(pair[0], pair[0]) for pair in logicals]),
            (8, stabilizers, [(pauli(x_support=(0,)), pair[1])
                              for pair in logicals]),
            (4, stabilizers, logicals),
        ]
        for n_in, stabs, logs in cases:
            with self.assertRaises(Malformed):
                check_inner(n_in, stabs, logs)

    def test_bad_blocks_and_outer_are_malformed(self):
        stabilizers, logicals = inner(INNER_8_3_3)
        outer = _small_outer(6)
        for groups in ([(0, 1, 2)], [(0, 1), (2, 3), (4, 5)],
                       [(0, 1, 2), (2, 4, 5)], [(0, 1, 2), (3, 4, 9)]):
            with self.assertRaises(Malformed):
                symplectic_concatenate(outer, 8, stabilizers, logicals, groups)
        with self.assertRaises(Malformed):
            symplectic_concatenate({"n": 6}, 8, stabilizers, logicals,
                                   [(0, 1, 2), (3, 4, 5)])

    def test_tower_data_refuses_nothing_this_module_needs(self):
        # The admitted constructor reads the inner code as a CodeState; the
        # level data of the CSS inner used above is computable.
        self.assertEqual(tower_level_data(c4_state()).get("status"), "computed")
        self.assertEqual(two_block_code([3], [[0]], [[1]])[0].n(), 6)


if __name__ == "__main__":
    unittest.main()
