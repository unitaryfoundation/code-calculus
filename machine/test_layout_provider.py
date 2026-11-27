"""Tests for the consumer-side layout provider (issue #666).

The provider synthesizes a layout beside a state; these tests pin that the
output is honest and planar by the shared section 2d.3 predicate, that its
reported metrics are the exact recomputations, that it is deterministic, and
that it never touches the state or overrides a supplied layout. Agreement on
these examples is evidence about the tooling, not a claim about any code.
"""

import copy
import json
import os
import random
import unittest
from collections import Counter
from fractions import Fraction

from machine.constructors import empty_code, free_code, hypergraph_product
from machine.layout import (
    layout_honest,
    layout_is_honest,
    layout_layers,
    layout_planar,
    locality_class,
    radius_squared_in_layout,
)
from machine.layout_provider import (
    attach_layout,
    grid_assignment,
    grid_side,
    locality_block,
    provide_layout,
    refine,
    spectral_embedding,
    total_grid_distance,
    _diameter_squared_int,
)
from machine.state import CodeState, Row

HERE = os.path.dirname(os.path.abspath(__file__))
FIXTURE = os.path.join(HERE, "fixtures", "qldpc_10_2_3_b.json")


def repetition(m):
    return [[1 if j in (i, i + 1) else 0 for j in range(m)] for i in range(m - 1)]


def cycle(m):
    return [[1 if j in (i, (i + 1) % m) else 0 for j in range(m)] for i in range(m)]


def hgp(H):
    state, _ = hypergraph_product(H, H)
    return state


def path_state(n):
    """Z checks on consecutive pairs: the qubit graph is a path."""
    rows = tuple(Row("b%d" % (i + 1), "Z", (i, i + 1)) for i in range(n - 1))
    return CodeState(tuple(range(n)), rows, frozenset(r.id for r in rows))


class ProvidedLayoutIsHonest(unittest.TestCase):
    STATES = {
        "hgp-rep3": lambda: hgp(repetition(3)),
        "hgp-rep4": lambda: hgp(repetition(4)),
        "hgp-cyc4": lambda: hgp(cycle(4)),
        "path-7": lambda: path_state(7),
    }

    def test_honest_planar_and_capped_for_every_method_and_layer_count(self):
        for name, build in self.STATES.items():
            state = build()
            for method in ("spectral", "mds"):
                for layers in (1, 2, 3):
                    with self.subTest(code=name, method=method, layers=layers):
                        provided = provide_layout(state, method=method, layers=layers)
                        coordinates = provided["coordinates"]
                        self.assertEqual(len(coordinates), state.n())
                        self.assertTrue(layout_is_honest(coordinates, layers))
                        self.assertTrue(all(len(p) == 2 and all(isinstance(v, int) for v in p)
                                            for p in coordinates))
                        occupancy = Counter(map(tuple, coordinates))
                        self.assertLessEqual(max(occupancy.values()), layers)
                        self.assertEqual(provided["metrics"]["max_site_occupancy"],
                                         max(occupancy.values()))
                        side = provided["provenance"]["grid"][0]
                        self.assertTrue(all(0 <= v < side for p in coordinates for v in p))

    def test_degenerate_namespaces(self):
        for state in (empty_code(), free_code([0]), free_code([0, 1, 2])):
            with self.subTest(n=state.n()):
                provided = provide_layout(state)
                self.assertTrue(layout_is_honest(provided["coordinates"], 1))
                self.assertEqual(provided["metrics"]["interaction_radius_squared"], "0")
                self.assertEqual(provided["metrics"]["total_grid_distance"], 0)

    def test_grid_assignment_respects_the_cap_on_arbitrary_seeds(self):
        generator = random.Random(7)
        for _ in range(50):
            n = generator.randint(1, 60)
            layers = generator.randint(1, 3)
            slack = generator.randint(0, 2)
            seed = {q: (generator.choice([0.0, 1.0, generator.random()]),
                        generator.choice([0.0, generator.random()])) for q in range(n)}
            side = grid_side(n, layers, slack)
            sites = grid_assignment(seed, layers, side)
            self.assertEqual(set(sites), set(range(n)))
            self.assertLessEqual(max(Counter(sites.values()).values()), layers)

    def test_grid_too_small_is_refused(self):
        with self.assertRaises(ValueError):
            grid_assignment({0: (0, 0), 1: (1, 1)}, 1, 1)


class ProvidedMetricsAreExact(unittest.TestCase):
    def test_radius_and_class_agree_with_the_consumer_on_an_attached_document(self):
        with open(FIXTURE) as source:
            document = json.load(source)
        for layers in (1, 2):
            with self.subTest(layers=layers):
                attached, provided = attach_layout(document, replace=True, layers=layers)
                state = CodeState.from_challenge(attached)
                squared = radius_squared_in_layout(attached, state)
                self.assertEqual(str(squared), provided["metrics"]["interaction_radius_squared"])
                self.assertTrue(layout_honest(attached))
                self.assertTrue(layout_planar(attached))
                self.assertEqual(layout_layers(attached), layers)
                self.assertEqual(
                    locality_class(squared, layout_layers(attached),
                                   planar=layout_planar(attached),
                                   honest=layout_honest(attached)),
                    provided["metrics"]["locality_class"])

    def test_total_grid_distance_on_a_hand_example(self):
        # One row on three collinear sites (0,0), (2,0), (5,1): the lower
        # median is (2, 0), so W = 2 + 0 + (3 + 1) = 6.
        rows = (Row("a1", "X", (0, 1, 2)),)
        state = CodeState((0, 1, 2), rows, frozenset({"a1"}))
        self.assertEqual(total_grid_distance(state, {0: (0, 0), 1: (2, 0), 2: (5, 1)}), 6)

    def test_refinement_never_worsens_the_objective(self):
        for H in (repetition(4), cycle(4), cycle(5)):
            state = hgp(H)
            seed = spectral_embedding(state)
            side = grid_side(state.n(), 1)
            start = grid_assignment(seed, 1, side)
            refined = refine(state, start, 1, side)

            def objective(sites):
                values = [_diameter_squared_int(sites, r.support) for r in state.rows]
                return (max(values), sum(values))

            self.assertLessEqual(objective(refined), objective(start))
            self.assertTrue(layout_is_honest([list(refined[q]) for q in state.Q], 1))

    def test_spectral_seed_orders_a_path(self):
        # The Fiedler vector of a path is monotone along it.
        seed = spectral_embedding(path_state(9))
        xs = [seed[q][0] for q in range(9)]
        self.assertTrue(xs == sorted(xs) or xs == sorted(xs, reverse=True))


class ProviderIsLedgerOnly(unittest.TestCase):
    def test_deterministic(self):
        state = hgp(cycle(4))
        for method in ("spectral", "mds"):
            with self.subTest(method=method):
                self.assertEqual(provide_layout(state, method=method),
                                 provide_layout(state, method=method))

    def test_state_and_document_are_untouched(self):
        with open(FIXTURE) as source:
            document = json.load(source)
        before = copy.deepcopy(document)
        state = CodeState.from_challenge(document)
        attached, _ = attach_layout(document, replace=True)
        self.assertEqual(document, before)
        self.assertEqual(CodeState.from_challenge(attached), state)
        self.assertEqual({k: v for k, v in attached.items() if k != "locality"},
                         {k: v for k, v in before.items() if k != "locality"})

    def test_a_supplied_layout_is_not_overridden_silently(self):
        with open(FIXTURE) as source:
            document = json.load(source)
        with self.assertRaises(ValueError):
            attach_layout(document)

    def test_no_contributor_credit_is_invented(self):
        provided = provide_layout(path_state(4))
        self.assertNotIn("contributed_by", locality_block(provided))
        credit = {"by": ["@someone"], "date": "2026-11-26"}
        self.assertEqual(locality_block(provided, credit)["contributed_by"], credit)

    def test_non_contiguous_namespace_has_no_challenge_block(self):
        rows = (Row("b1", "Z", (1, 3)),)
        state = CodeState((1, 3), rows, frozenset({"b1"}))
        provided = provide_layout(state)
        self.assertTrue(layout_is_honest(provided["coordinates"], 1))
        with self.assertRaises(ValueError):
            locality_block(provided)

    def test_invalid_parameters_are_refused(self):
        state = path_state(3)
        for kwargs in ({"layers": 0}, {"layers": True}, {"method": "umap"}, {"slack": -1}):
            with self.subTest(**kwargs):
                with self.assertRaises(ValueError):
                    provide_layout(state, **kwargs)


if __name__ == "__main__":
    unittest.main()
