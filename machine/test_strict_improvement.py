import itertools
import random
import unittest

from machine.oracle import exact_distances
from machine.priced_calculus import (
    CodeState,
    Malformed,
    NoDerivation,
    Row,
    in_span,
    strict_improvement_feasible,
    validate_witness,
)


def random_css(rng, n):
    """A well-formed random CSS state on ``n`` qubits with independent rows."""
    labels = tuple(range(n))
    x_masks = []
    for _ in range(rng.randint(0, 2)):
        mask = rng.randrange(1, 1 << n)
        if not in_span(mask, x_masks):
            x_masks.append(mask)
    perp = [m for m in range(1, 1 << n)
            if all((m & x).bit_count() % 2 == 0 for x in x_masks)]
    rng.shuffle(perp)
    z_masks = []
    for mask in perp[:rng.randint(0, 2)]:
        if not in_span(mask, z_masks):
            z_masks.append(mask)
    rows = [Row("a%d" % (i + 1), "X", tuple(q for q in labels if m >> q & 1))
            for i, m in enumerate(x_masks)]
    rows += [Row("b%d" % (i + 1), "Z", tuple(q for q in labels if m >> q & 1))
             for i, m in enumerate(z_masks)]
    state = CodeState(labels, tuple(rows), frozenset(row.id for row in rows))
    state.validate()
    return state


class TestStrictImprovementFeasible(unittest.TestCase):
    def test_survivor_found(self):
        # Empty code on two qubits: distance 1. Adding an X check on qubit 0
        # leaves qubit 1 as a surviving logical (commutes? qubit 1 has zero
        # overlap with the check, so it commutes -> survives).
        state = CodeState((0, 1), (), frozenset())
        result = strict_improvement_feasible(state, [0], "X", 1)
        self.assertEqual(result["reason"], "survivor_found")
        self.assertIsNotNone(result["survivor"])

    def test_all_killed_requires_enumeration(self):
        state = CodeState((0, 1), (Row("a", "X", (0,)),), frozenset(("a",)))
        result = strict_improvement_feasible(state, [1], "X", 1,
                                             allow_enumeration=False)
        self.assertEqual(result["reason"], "all_killed_requires_enumeration")
        scanned = strict_improvement_feasible(state, [1], "X", 1)
        self.assertEqual(scanned["reason"], "all_killed_by_enumeration")

    def test_malformed_inputs(self):
        state = CodeState((0, 1), (), frozenset())
        with self.assertRaises(Exception):
            strict_improvement_feasible(state, [0], "X", 0)
        with self.assertRaises(Exception):
            strict_improvement_feasible(state, [0], "Y", 1)


    def test_result_names_the_survivor_and_its_source(self):
        state = CodeState((0, 1), (), frozenset())
        result = strict_improvement_feasible(state, [0], "X", 1)
        self.assertEqual(result["status"], "survivor_found")
        self.assertEqual(result["source"], "enumeration")
        self.assertEqual(result["survivor_support"], [1])
        self.assertIn(result["survivor_sector"], ("X", "Z"))
        self.assertTrue(result["enumeration"]["performed"])
        cheap = strict_improvement_feasible(state, [0], "X", 1,
                                            witnesses={"X": [[1]]},
                                            allow_enumeration=False)
        self.assertEqual(cheap["source"], "witness")
        self.assertEqual(cheap["survivor_support"], [1])
        self.assertFalse(cheap["enumeration"]["performed"])

    def test_a_complete_scan_with_no_survivor_says_so(self):
        # Z{0,1} on two qubits: d_X = 2 ({0,1}), d_Z = 1. Adding X{0,1}
        # kills both weight-1 Z logicals (each anticommutes with it).
        state = CodeState((0, 1), (Row("b1", "Z", (0, 1)),), frozenset(("b1",)))
        result = strict_improvement_feasible(state, [0, 1], "X", 1)
        self.assertEqual(result["reason"], "all_killed_by_enumeration")
        self.assertEqual(result["enumeration"]["supports_examined"], 2)
        cheap = strict_improvement_feasible(state, [0, 1], "X", 1,
                                            allow_enumeration=False)
        self.assertEqual(cheap["reason"], "all_killed_requires_enumeration")

    def test_inadmissible_additions_and_miscounted_witnesses(self):
        state = CodeState((0, 1), (Row("b1", "Z", (0, 1)),), frozenset(("b1",)))
        with self.assertRaises(NoDerivation):
            strict_improvement_feasible(state, [0], "X", 1)       # anticommutes
        with self.assertRaises(NoDerivation):
            strict_improvement_feasible(state, [0, 1], "Z", 1)    # in the span
        with self.assertRaises(NoDerivation):
            strict_improvement_feasible(state, [0, 5], "X", 1)    # outside Q
        with self.assertRaises(Malformed):
            strict_improvement_feasible(state, [0, 0], "X", 1)
        # A witness whose claimed value disagrees with its support is ignored.
        free = CodeState((0, 1, 2), (), frozenset())
        result = strict_improvement_feasible(
            free, [0], "X", 1, witnesses=[{"support": [1, 2], "value": 1}],
            allow_enumeration=False)
        self.assertEqual(result["reason"], "all_killed_requires_enumeration")

    def test_randomized_agreement_with_oracle(self):
        rng = random.Random(342)
        outcomes = {}
        for _ in range(300):
            n = rng.randint(2, 6)
            state = random_css(rng, n)
            exact = exact_distances(state)
            d = exact["d"]
            if d is None:
                continue
            sector = rng.choice(["X", "Z"])
            support = sorted(rng.sample(range(n), rng.randint(1, n)))
            try:
                child = state.add_check(sector, support)
            except NoDerivation:
                with self.assertRaises(NoDerivation):
                    strict_improvement_feasible(state, support, sector, d)
                continue
            d2 = exact_distances(child)["d"]
            full = strict_improvement_feasible(state, support, sector, d)
            outcomes[full["reason"]] = outcomes.get(full["reason"], 0) + 1
            if full["reason"] == "survivor_found":
                self.assertEqual(d2, d)
                side = full["survivor_sector"]
                validate_witness(child, side, tuple(full["survivor_support"]), d)
            else:
                self.assertEqual(full["reason"], "all_killed_by_enumeration")
                self.assertTrue(d2 is None or d2 >= d + 1)
            # The cheap path alone is sound: one minimum-weight witness per
            # sector, no scan. A survivor it reports is a survivor.
            witnesses = {}
            for side in ("X", "Z"):
                if exact[side] == d:
                    for combo in itertools.combinations(range(n), d):
                        try:
                            validate_witness(state, side, combo, d)
                        except NoDerivation:
                            continue
                        witnesses[side] = [list(combo)]
                        break
            cheap = strict_improvement_feasible(state, support, sector, d,
                                                witnesses=witnesses,
                                                allow_enumeration=False)
            self.assertIn(cheap["reason"],
                          ("survivor_found", "all_killed_requires_enumeration"))
            if cheap["reason"] == "survivor_found":
                self.assertEqual(d2, d)
                self.assertEqual(cheap["source"], "witness")
        self.assertGreater(outcomes.get("survivor_found", 0), 20)
        self.assertGreater(outcomes.get("all_killed_by_enumeration", 0), 5)


if __name__ == "__main__":
    unittest.main()
