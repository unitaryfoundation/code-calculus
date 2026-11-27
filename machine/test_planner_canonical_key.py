"""The planner's exact canonical key against the all-permutations reference.

``_canonical_state_key`` partitions qubits by signature instead of trying all
``n!`` relabelings.  Its key values differ from the reference's; what must
agree is which states receive equal keys.
"""

import itertools
import random
import unittest

from machine.planner import _canonical_state_key, dedup_up_to_permutation
from machine.priced_calculus import CodeState, Row


def _state(n, X, Z, labels=None):
    labels = list(range(n)) if labels is None else labels
    rows = []
    for sector, prefix, supports in (("X", "a", X), ("Z", "b", Z)):
        for i, supp in enumerate(supports):
            rows.append(Row("%s%d" % (prefix, i + 1), sector,
                            tuple(sorted(labels[q] for q in supp))))
    return CodeState(tuple(sorted(labels)), tuple(rows),
                     frozenset(row.id for row in rows))


def _brute_force_key(state):
    index = {q: i for i, q in enumerate(sorted(state.Q))}
    sectors = [[[index[q] for q in row.support]
                for row in state.sector_rows(sector)]
               for sector in ("X", "Z")]
    n = len(index)
    return (n, state.k(), min(
        tuple(tuple(sorted(tuple(sorted(perm[i] for i in supp))
                           for supp in supports))
              for supports in sectors)
        for perm in itertools.permutations(range(n))))


def _random_css(rng, n):
    """Random supports with every X row evenly overlapping every Z row."""
    supports = [s for w in range(1, n + 1)
                for s in itertools.combinations(range(n), w)]
    X = rng.sample(supports, rng.randint(0, min(3, len(supports))))
    commuting = [s for s in supports
                 if all(len(set(s) & set(x)) % 2 == 0 for x in X)]
    Z = rng.sample(commuting, rng.randint(0, min(3, len(commuting))))
    return X, Z


def _cycle(*qubits):
    return [(a, b) for a, b in zip(qubits, qubits[1:] + qubits[:1])]


class CanonicalKeyAgreesWithBruteForceTests(unittest.TestCase):
    def assertSameClasses(self, states):
        pairs = {(_brute_force_key(s), _canonical_state_key(s))
                 for s in states}
        references = {reference for reference, _ in pairs}
        keys = {key for _, key in pairs}
        # A one-to-one correspondence: no class split, no two classes merged.
        self.assertEqual(len(pairs), len(references))
        self.assertEqual(len(pairs), len(keys))
        return len(references)

    def _with_relabelings(self, rng, n, X, Z):
        labels = rng.sample(range(40), n)
        shuffled_X, shuffled_Z = rng.sample(X, len(X)), rng.sample(Z, len(Z))
        return [_state(n, X, Z), _state(n, shuffled_X, shuffled_Z, labels)]

    def test_random_small_css_states(self):
        rng = random.Random(577)
        states = []
        for n, trials in ((1, 10), (2, 40), (3, 80), (4, 150), (5, 150),
                          (6, 60), (7, 20), (8, 5)):
            for _ in range(trials):
                X, Z = _random_css(rng, n)
                states += self._with_relabelings(rng, n, X, Z)
                states.append(_state(n, Z, X))
                if X:
                    # Near miss: one row repeated.
                    states.append(_state(n, X + [X[0]], Z))
        classes = self.assertSameClasses(states)
        self.assertLess(classes, len(states))
        self.assertGreater(classes, 100)

    def test_every_display_with_two_rows_per_sector_on_four_qubits(self):
        supports = [s for w in range(1, 5)
                    for s in itertools.combinations(range(4), w)]
        choices = [list(c) for size in range(3)
                   for c in itertools.combinations_with_replacement(
                       supports, size)]
        self.assertSameClasses(
            [_state(4, X, Z) for X in choices for Z in choices])

    def test_symmetric_states_that_signatures_cannot_split(self):
        rng = random.Random(8)
        cases = [
            # Every qubit has the same signature in the first three.
            (8, _cycle(0, 1, 2, 3, 4, 5, 6, 7), []),
            (8, _cycle(0, 1, 2, 3) + _cycle(4, 5, 6, 7), []),
            (8, _cycle(0, 1, 2) + _cycle(3, 4, 5, 6, 7), []),
            # Same two cycles, with the sectors aligned and crossed.
            (8, _cycle(0, 1, 2, 3), _cycle(4, 5, 6, 7)),
            (8, [(0, 1), (2, 3), (4, 5), (6, 7)],
             [(0, 1), (2, 3), (4, 5), (6, 7)]),
            (8, [(0, 1), (2, 3), (4, 5), (6, 7)],
             [(1, 2), (3, 0), (5, 6), (7, 4)]),
            (8, [], []),
            (8, [tuple(range(8))], [tuple(range(8))]),
            (7, [(0, 2, 4, 6), (1, 2, 5, 6), (3, 4, 5, 6)],
             [(0, 2, 4, 6), (1, 2, 5, 6), (3, 4, 5, 6)]),
        ]
        states = []
        for n, X, Z in cases:
            states += self._with_relabelings(rng, n, X, Z)
        self.assertEqual(self.assertSameClasses(states), len(cases))

    def test_dedup_drops_a_relabeled_copy(self):
        first = _state(4, [(0, 1, 2, 3)], [(0, 1)])
        copy = _state(4, [(0, 1, 2, 3)], [(1, 3)], labels=[5, 7, 8, 9])
        other = _state(4, [(0, 1, 2, 3)], [(0, 1), (2, 3)])
        self.assertEqual(dedup_up_to_permutation([first, copy, other]),
                         [first, other])


if __name__ == "__main__":
    unittest.main()
