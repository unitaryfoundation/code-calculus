"""Split-subset E-LOCAL-HADAMARD (0 < |T| < |Q|), issue #571.

The transition is admitted under the decidable row-space splitting guard
(`v|_T in X` for all `v in X`, `w|_T in Z` for all `w in Z`) with the
canonical update of `spec/OPERATIONAL_SEMANTICS.md` §2 (`E-LOCAL-HADAMARD`
card) and the derivations of §4.27. These tests check the worked examples,
the refusals, the specialization to the T = Q and T = ∅ instances, and, on
random split codes, the derived facts (well-formedness, n' = n, k' = k, the
row-space identities, d' = d, and the T-split sector-distance formulas)
against the exhaustive oracle. Agreement on examples is evidence, not proof.
"""

import itertools
import random
import unittest

from machine.oracle import exact_distances
from machine.priced_calculus import (
    CodeState,
    DistanceLedger,
    Interval,
    Malformed,
    NoDerivation,
    Row,
    apply_operation,
    in_span,
    rank,
)


def _mask(support):
    value = 0
    for q in support:
        value |= 1 << q
    return value


def _support(mask):
    return tuple(q for q in range(mask.bit_length()) if (mask >> q) & 1)


def _span_equal(left, right):
    return (rank(left) == rank(right) == rank(list(left) + list(right)))


def _state(Q, rows):
    state = CodeState(tuple(Q), tuple(Row(*row) for row in rows),
                      frozenset(row[0] for row in rows))
    state.validate()
    return state


def mixed_z_state():
    """Z display {0,1,3,4}, {1,2}, {3,4}, {4,5}; T = {0,1,2} splits it."""
    return _state(range(6), [("b1", "Z", (0, 1, 3, 4)), ("b2", "Z", (1, 2)),
                             ("b3", "Z", (3, 4)), ("b4", "Z", (4, 5))])


def minting_state():
    """X display {0,1}, {0,2}, {0,1,2}: every row is mixed for T = {0}."""
    return _state(range(3), [("a1", "X", (0, 1)), ("a2", "X", (0, 2)),
                             ("a3", "X", (0, 1, 2))])


def exact_ledger(state):
    exact = exact_distances(state)
    def point(value):
        return Interval(value, value) if value is not None else Interval(None, None)
    return DistanceLedger(point(exact["d"]),
                          {"X": point(exact["X"]), "Z": point(exact["Z"])})


def _random_sector_pair(rng, qubits):
    """Independent X and Z masks over ``qubits`` with X ⊥ Z."""
    x_masks = []
    for _ in range(rng.randint(0, max(1, len(qubits) // 2))):
        mask = 0
        for q in qubits:
            if rng.random() < 0.5:
                mask |= 1 << q
        if mask and not in_span(mask, x_masks):
            x_masks.append(mask)
    z_masks = []
    for _ in range(rng.randint(0, max(1, len(qubits) // 2))):
        mask = 0
        for q in qubits:
            if rng.random() < 0.5:
                mask |= 1 << q
        if (mask and not in_span(mask, z_masks)
                and all((mask & x).bit_count() % 2 == 0 for x in x_masks)):
            z_masks.append(mask)
    return x_masks, z_masks


def _mix(rng, masks):
    """A random invertible F_2 recombination of an independent family."""
    m = len(masks)
    while True:
        rows = [rng.getrandbits(m) for _ in range(m)]
        if rank(rows) == m:
            break
    out = []
    for coeffs in rows:
        value = 0
        for j in range(m):
            if (coeffs >> j) & 1:
                value ^= masks[j]
        out.append(value)
    return out


def random_split_state(rng, n):
    """A random code on range(n) that splits along a random proper T, with a
    randomly recombined (generally mixed) display. Returns (state, T)."""
    labels = list(range(n))
    rng.shuffle(labels)
    cut = rng.randint(1, n - 1)
    T, rest = sorted(labels[:cut]), sorted(labels[cut:])
    xt, zt = _random_sector_pair(rng, T)
    xr, zr = _random_sector_pair(rng, rest)
    x_masks = _mix(rng, xt + xr)
    z_masks = _mix(rng, zt + zr)
    rows = [("a%d" % (i + 1), "X", _support(m)) for i, m in enumerate(x_masks)]
    rows += [("b%d" % (i + 1), "Z", _support(m)) for i, m in enumerate(z_masks)]
    return _state(range(n), rows), frozenset(T)


class WorkedExampleTests(unittest.TestCase):

    def test_mixed_row_keeps_its_identifier_on_the_kept_piece(self):
        state = mixed_z_state()
        child = apply_operation(state, {"op": "E-LOCAL-HADAMARD", "qubits": [0, 1, 2]})
        self.assertEqual(child.rows, (Row("b1", "X", (0, 1)), Row("b2", "X", (1, 2)),
                                      Row("b3", "Z", (3, 4)), Row("b4", "Z", (4, 5))))
        self.assertEqual(child.used, state.used)
        self.assertEqual((child.n(), child.k()), (state.n(), state.k()))

    def test_second_kept_piece_is_canonically_minted_and_a_dead_row_retires(self):
        state = minting_state()
        child = state.local_hadamard({0})
        self.assertEqual(child.rows, (Row("a1", "X", (1,)), Row("a4", "Z", (0,)),
                                      Row("a2", "X", (2,))))
        # a3 has no kept piece: retired, still in used; a4 is the first
        # identifier of the fixed enumeration not in used.
        self.assertEqual(child.used, frozenset({"a1", "a2", "a3", "a4"}))
        self.assertEqual((child.n(), child.k()), (state.n(), state.k()))

    def test_pure_display_needs_no_mint(self):
        state = _state(range(4), [("a1", "X", (0, 1)), ("a2", "X", (2, 3)),
                                  ("b1", "Z", (0, 1))])
        child = state.local_hadamard({0, 1})
        self.assertEqual(child.rows, (Row("a1", "Z", (0, 1)), Row("a2", "X", (2, 3)),
                                      Row("b1", "X", (0, 1))))
        self.assertEqual(child.used, state.used)

    def test_split_sector_distances_are_not_the_global_swap(self):
        # Z-rep codes on {0,1,2} and {3,4,5}: d_X = 3, d_Z = 1. Hadamarding
        # the first block gives d_X' = min(1, 3) = 1 and d_Z' = min(3, 1) = 1,
        # not the T = Q exchange (1, 3); d' = d = 1.
        state = _state(range(6), [("b1", "Z", (0, 1)), ("b2", "Z", (1, 2)),
                                  ("b3", "Z", (3, 4)), ("b4", "Z", (4, 5))])
        parent = exact_distances(state)
        child = exact_distances(state.local_hadamard({0, 1, 2}))
        self.assertEqual((parent["X"], parent["Z"], parent["d"]), (3, 1, 1))
        self.assertEqual((child["X"], child["Z"], child["d"]), (1, 1, 1))


class RefusalTests(unittest.TestCase):

    def test_guard_failure_has_no_derivation(self):
        state = _state(range(3), [("a1", "X", (0, 1))])
        with self.assertRaises(NoDerivation):
            apply_operation(state, {"op": "E-LOCAL-HADAMARD", "qubits": [0]})
        ledger = DistanceLedger(Interval(0, None), {"X": Interval(0, None),
                                                    "Z": Interval(0, None)})
        with self.assertRaises(NoDerivation):
            ledger.propagate({"op": "E-LOCAL-HADAMARD", "qubits": [0]}, state,
                             parent_state=state)

    def test_z_sector_guard_failure_has_no_derivation(self):
        state = _state(range(4), [("a1", "X", (2, 3)), ("b1", "Z", (0, 2, 3))])
        with self.assertRaises(NoDerivation):
            state.local_hadamard({0, 1})

    def test_subset_outside_q_has_no_derivation(self):
        state = mixed_z_state()
        with self.assertRaises(NoDerivation):
            apply_operation(state, {"op": "E-LOCAL-HADAMARD", "qubits": [0, 9]})

    def test_repeated_label_is_malformed(self):
        state = mixed_z_state()
        with self.assertRaises(Malformed):
            apply_operation(state, {"op": "E-LOCAL-HADAMARD", "qubits": [0, 0]})


class SpecializationTests(unittest.TestCase):

    def test_general_update_specializes_to_swap_and_identity(self):
        rng = random.Random(5710)
        for _ in range(150):
            state, _T = random_split_state(rng, rng.randint(2, 7))
            self.assertEqual(state.local_hadamard(set(state.Q)),
                             state.hadamard_sector_swap())
            self.assertEqual(state.local_hadamard(set()), state)


class RandomSplitTests(unittest.TestCase):

    def test_derived_facts_on_random_split_codes(self):
        rng = random.Random(571)
        checked = minted = 0
        for _ in range(400):
            state, T = random_split_state(rng, rng.randint(2, 8))
            self.assertIsNone(state.hadamard_split_guard(T))
            child = apply_operation(state, {"op": "E-LOCAL-HADAMARD",
                                            "qubits": sorted(T)})
            child.validate()
            self.assertEqual(child.Q, state.Q)
            self.assertEqual(child.k(), state.k())
            self.assertTrue(state.used <= child.used)
            minted += len(child.used - state.used)
            tmask = _mask(T)
            rmask = _mask(set(state.Q) - T)
            px = [row.mask for row in state.sector_rows("X")]
            pz = [row.mask for row in state.sector_rows("Z")]
            # X' = X|_{Q\T} ⊕ Z|_T and Z' = Z|_{Q\T} ⊕ X|_T.
            want_x = [m & rmask for m in px] + [m & tmask for m in pz]
            want_z = [m & rmask for m in pz] + [m & tmask for m in px]
            self.assertTrue(_span_equal([r.mask for r in child.sector_rows("X")],
                                        [m for m in want_x if m]))
            self.assertTrue(_span_equal([r.mask for r in child.sector_rows("Z")],
                                        [m for m in want_z if m]))
            # Every live identifier is an old one or a fresh canonical mint.
            for row in child.rows:
                self.assertIn(row.id, child.used)
            if state.k() == 0:
                continue
            parent = exact_distances(state)
            got = exact_distances(child)
            self.assertEqual(got["d"], parent["d"])
            for side in ("X", "Z"):
                self.assertGreaterEqual(got[side], parent["d"])
            # T-split decomposition: factor codes on T and on Q \ T.
            def factor(qubits):
                keep = _mask(qubits)
                rows = []
                for i, row in enumerate(state.rows):
                    piece = row.mask & keep
                    if piece and not in_span(piece, [_mask(r[2]) for r in rows
                                                     if r[1] == row.sector]):
                        rows.append(("a%d" % (i + 1), row.sector, _support(piece)))
                return exact_distances(_state(sorted(qubits), rows))
            inner = factor(T)
            outer = factor(set(state.Q) - T)

            def mn(*values):
                finite = [v for v in values if v is not None]
                return min(finite) if finite else None

            self.assertEqual(parent["X"], mn(inner["X"], outer["X"]))
            self.assertEqual(got["X"], mn(inner["Z"], outer["X"]))
            self.assertEqual(got["Z"], mn(inner["X"], outer["Z"]))
            # Ledger transport is sound against the exact child distances.
            out = exact_ledger(state).propagate(
                {"op": "E-LOCAL-HADAMARD", "qubits": sorted(T)}, child,
                parent_state=state)
            self.assertEqual(out.full, Interval(got["d"], got["d"]))
            for side in ("X", "Z"):
                interval = out.sector[side]
                self.assertLessEqual(interval.lower, got[side])
                if interval.upper is not None:
                    self.assertGreaterEqual(interval.upper, got[side])
            checked += 1
        self.assertGreater(checked, 50)
        self.assertGreater(minted, 0)

    def test_hadamard_twice_restores_the_row_spaces(self):
        rng = random.Random(5711)
        for _ in range(150):
            state, T = random_split_state(rng, rng.randint(2, 7))
            twice = state.local_hadamard(T).local_hadamard(T)
            for side in ("X", "Z"):
                self.assertTrue(_span_equal(
                    [r.mask for r in twice.sector_rows(side)],
                    [r.mask for r in state.sector_rows(side)]))

    def test_witnesses_move_with_their_block(self):
        state = _state(range(6), [("b1", "Z", (0, 1)), ("b2", "Z", (1, 2)),
                                  ("b3", "Z", (3, 4)), ("b4", "Z", (4, 5))])
        ledger = DistanceLedger(Interval(1, 1), {"X": Interval(3, 3),
                                                 "Z": Interval(1, 1)})
        ledger.record_witness(state, "Z", (0,))
        ledger.record_witness(state, "Z", (3,))
        ledger.record_witness(state, "X", (0, 1, 2))
        child = state.local_hadamard({0, 1, 2})
        out = ledger.propagate({"op": "E-LOCAL-HADAMARD", "qubits": [0, 1, 2]},
                               child, parent_state=state)
        self.assertEqual(sorted(w["support"] for w in out.witnesses["X"]), [[0]])
        self.assertEqual(sorted(w["support"] for w in out.witnesses["Z"]),
                         [[0, 1, 2], [3]])
        self.assertEqual(out.sector["X"], Interval(1, 1))
        self.assertEqual(out.sector["Z"], Interval(1, 1))
        self.assertEqual(out.full, Interval(1, 1))
        self.assertTrue(any(c["cell"] == "E-LOCAL-HADAMARD split subset"
                            for c in out.conditions))


class RowOrderInvarianceTests(unittest.TestCase):

    def test_four_row_example_all_24_permutations_agree(self):
        # Smallest counterexample to display-order dependence: Q = {0..6},
        # T = {0, 1, 2}. Reading rows in identifier order gives one child
        # across all 24 permutations, with no minting and used = {a1..a4}.
        base_rows = [
            ("a1", "X", (0, 3, 4, 5, 6)),
            ("a2", "X", (0,)),
            ("a3", "X", (0, 5, 6)),
            ("a4", "X", (0, 2, 5, 6)),
        ]
        expected_rows = frozenset({
            Row("a1", "X", (3, 4, 5, 6)),
            Row("a2", "Z", (0,)),
            Row("a3", "X", (5, 6)),
            Row("a4", "Z", (0, 2)),
        })
        expected_used = frozenset({"a1", "a2", "a3", "a4"})
        children = []
        for perm in itertools.permutations(base_rows):
            state = _state(range(7), perm)
            child = apply_operation(
                state, {"op": "E-LOCAL-HADAMARD", "qubits": [0, 1, 2]}
            )
            self.assertEqual(child.Q, tuple(range(7)))
            self.assertEqual(frozenset(child.rows), expected_rows)
            self.assertEqual(child.used, expected_used)
            children.append(child)
        self.assertEqual(len(children), 24)
        self.assertEqual(len(set(children)), 1)

    def test_random_split_states_are_row_permutation_invariant(self):
        rng = random.Random(5712)
        minted = 0
        mixed_cases = 0
        for _ in range(400):
            state, T = random_split_state(rng, rng.randint(4, 8))
            child = state.local_hadamard(T)
            tset = set(T)
            if any((set(r.support) & tset) and (set(r.support) - tset)
                   for r in state.rows):
                mixed_cases += 1
            minted += len(child.used - state.used)
            # Reversed and randomly shuffled parent row orders (same state ≡).
            for perm_rows in (
                tuple(reversed(state.rows)),
                tuple(rng.sample(state.rows, len(state.rows))),
            ):
                permuted = CodeState(state.Q, perm_rows, state.used)
                permuted.validate()
                child_p = apply_operation(
                    permuted, {"op": "E-LOCAL-HADAMARD", "qubits": sorted(T)}
                )
                self.assertEqual(child_p.Q, child.Q)
                self.assertEqual(frozenset(child_p.rows), frozenset(child.rows))
                self.assertEqual(child_p.used, child.used)
                self.assertEqual(child_p, child)
                # Global swap and empty identity also preserve ≡.
                swap_orig = state.local_hadamard(set(state.Q))
                swap_perm = permuted.local_hadamard(set(state.Q))
                self.assertEqual(frozenset(swap_perm.rows), frozenset(swap_orig.rows))
                self.assertEqual(swap_perm.used, swap_orig.used)
                id_orig = state.local_hadamard(set())
                id_perm = permuted.local_hadamard(set())
                self.assertEqual(frozenset(id_perm.rows), frozenset(id_orig.rows))
                self.assertEqual(id_perm.used, id_orig.used)
        self.assertGreater(mixed_cases, 50)
        self.assertGreater(minted, 0)


if __name__ == "__main__":
    unittest.main()
