"""Bounded search over supports in the planner.

The search is consumer configuration: it enumerates a child's supports by
weight under a recorded budget, hands any witness it finds to the ledger's
own transport, and records a negative outcome without raising a lower
endpoint.  The exact-distance oracle is consulted by these tests only, as
`machine/test_strict_improvement.py` does; no consumer path imports it.
"""

import random
import unittest

from machine.oracle import exact_distances
from machine.planner import (
    DEFAULT_SUPPORT_BUDGET,
    DEFAULT_SUPPORT_MAX_WEIGHT,
    bounded_sector_search,
    bounded_support_search,
    plan,
    plan_chain,
    tighten_ledger_with_search,
)
from machine.priced_calculus import (
    CodeState,
    DistanceLedger,
    Interval,
    Malformed,
    NoDerivation,
    Row,
    in_span,
    validate_witness,
)


def four_qubit_state():
    """X on all four qubits, Z on each pair: k = 1, d_X = d_Z = 2."""
    state = CodeState(
        (0, 1, 2, 3),
        (
            Row("a1", "X", (0, 1, 2, 3)),
            Row("b1", "Z", (0, 1)),
            Row("b2", "Z", (2, 3)),
        ),
        frozenset(("a1", "b1", "b2")),
    )
    state.validate()
    return state


def ledger(upper=4, lower=0):
    return DistanceLedger(Interval(lower, upper),
                          {"X": Interval(lower, upper), "Z": Interval(lower, upper)})


def random_css(rng, n):
    """A well-formed random CSS state on ``n`` qubits with independent rows."""
    labels = tuple(range(n))
    x_masks = []
    for _ in range(rng.randint(0, 3)):
        mask = 0
        for q in labels:
            if rng.random() < 0.5:
                mask |= 1 << q
        if mask and not in_span(mask, x_masks):
            x_masks.append(mask)
    perp = [m for m in range(1, 1 << n)
            if all((m & x).bit_count() % 2 == 0 for x in x_masks)]
    rng.shuffle(perp)
    z_masks = []
    for mask in perp[:rng.randint(0, 3)]:
        if not in_span(mask, z_masks):
            z_masks.append(mask)
    rows = []
    for index, mask in enumerate(x_masks):
        rows.append(Row("a%d" % (index + 1), "X", tuple(q for q in labels if mask >> q & 1)))
    for index, mask in enumerate(z_masks):
        rows.append(Row("b%d" % (index + 1), "Z", tuple(q for q in labels if mask >> q & 1)))
    state = CodeState(labels, tuple(rows), frozenset(row.id for row in rows))
    state.validate()
    return state


class BoundedSupportSearchTests(unittest.TestCase):
    def test_the_defaults_and_the_findings_are_recorded(self):
        record = bounded_support_search(four_qubit_state())
        self.assertEqual(record["budget"], DEFAULT_SUPPORT_BUDGET)
        self.assertEqual(record["max_weight"], min(4, DEFAULT_SUPPORT_MAX_WEIGHT))
        self.assertEqual(record["sectors"], ["X", "Z"])
        self.assertFalse(record["exhausted"])
        # Four weight-1 supports, then [0, 1] closes X and [0, 2] closes Z.
        self.assertEqual(record["evaluated"], 6)
        self.assertEqual(record["witnesses"]["X"], {"support": [0, 1], "value": 2, "confidence": "screened"})
        self.assertEqual(record["witnesses"]["Z"], {"support": [0, 2], "value": 2, "confidence": "screened"})
        for side in ("X", "Z"):
            by_sector = record["by_sector"][side]
            self.assertEqual(by_sector["exhaustive_weight"], 1)
            self.assertIsNone(by_sector["partial"])
            self.assertEqual(by_sector["status"],
                             "witness of weight 2 found; weights below 2 exhausted")

    def test_found_witnesses_pass_the_consumer_validation(self):
        state = four_qubit_state()
        record = bounded_support_search(state)
        for side, found in record["witnesses"].items():
            self.assertTrue(validate_witness(state, side, tuple(found["support"]),
                                             found["value"]))

    def test_the_budget_stops_the_enumeration_and_the_record_says_where(self):
        record = bounded_support_search(four_qubit_state(), budget=5)
        self.assertEqual(record["evaluated"], 5)
        self.assertTrue(record["exhausted"])
        # The fifth support, [0, 1], is an X witness; Z is still open when the
        # budget runs out, one of the six weight-2 supports seen.
        self.assertEqual(record["witnesses"]["X"], {"support": [0, 1], "value": 2, "confidence": "screened"})
        self.assertIsNone(record["witnesses"]["Z"])
        z_record = record["by_sector"]["Z"]
        self.assertEqual(z_record["exhaustive_weight"], 1)
        self.assertEqual(z_record["partial"], {"weight": 2, "evaluated": 1, "total": 6})
        self.assertEqual(
            z_record["status"],
            "no survivor found up to weight 1; weight 2 searched partially "
            "(1 of 6 supports) before the budget was spent")

    def test_the_weight_ceiling_is_a_recorded_negative_outcome(self):
        record = bounded_support_search(four_qubit_state(), max_weight=1)
        self.assertEqual(record["evaluated"], 4)
        self.assertFalse(record["exhausted"])
        for side in ("X", "Z"):
            self.assertIsNone(record["witnesses"][side])
            self.assertEqual(record["by_sector"][side]["exhaustive_weight"], 1)
            self.assertIsNone(record["by_sector"][side]["partial"])
            self.assertEqual(record["by_sector"][side]["status"],
                             "no survivor found up to weight 1")
        self.assertIn("never a lower endpoint", record["licenses"])

    def test_a_complete_search_agrees_with_the_oracle(self):
        rng = random.Random(347)
        checked = 0
        for _ in range(80):
            n = rng.randint(2, 6)
            state = random_css(rng, n)
            exact = exact_distances(state)
            record = bounded_support_search(state, max_weight=n, budget=2 ** n)
            self.assertFalse(record["exhausted"])
            for side in ("X", "Z"):
                found = record["witnesses"][side]
                if exact[side] is None:
                    self.assertIsNone(found)
                else:
                    self.assertEqual(found["value"], exact[side])
                    checked += 1
        self.assertGreater(checked, 40)

    def test_one_sector_and_malformed_configurations(self):
        state = four_qubit_state()
        record = bounded_support_search(state, sectors=("Z",))
        self.assertEqual(list(record["witnesses"]), ["Z"])
        self.assertEqual(record["evaluated"], 6)
        with self.assertRaises(Malformed):
            bounded_support_search(state, budget=0)
        with self.assertRaises(Malformed):
            bounded_support_search(state, max_weight=0)
        with self.assertRaises(Malformed):
            bounded_support_search(state, sectors=("Y",))
        with self.assertRaises(Malformed):
            bounded_support_search(state, sectors=("X", "X"))
        with self.assertRaises(Malformed):
            bounded_support_search(CodeState((), (), frozenset()))

    def test_the_search_is_deterministic(self):
        state = four_qubit_state()
        self.assertEqual(bounded_support_search(state, budget=7),
                         bounded_support_search(state, budget=7))


class TightenLedgerTests(unittest.TestCase):
    def test_found_witnesses_tighten_upper_endpoints_through_the_consumer(self):
        state = four_qubit_state()
        tightened, record = tighten_ledger_with_search(state, ledger(4))
        self.assertEqual(tightened.full, Interval(0, 2))
        self.assertEqual(tightened.sector["X"], Interval(0, 2))
        self.assertEqual(tightened.sector["Z"], Interval(0, 2))
        for side in ("X", "Z"):
            self.assertEqual([w["source"] for w in tightened.witnesses[side]],
                             ["supplied post-step logical witness"])
        self.assertEqual(record["evaluated"], 6)

    def test_no_witness_leaves_the_ledger_unchanged(self):
        state = four_qubit_state()
        original = ledger(4)
        tightened, record = tighten_ledger_with_search(state, original, max_weight=1)
        self.assertEqual(tightened.as_json(), original.as_json())
        self.assertEqual(record["by_sector"]["X"]["status"],
                         "no survivor found up to weight 1")

    def test_an_exhaustive_negative_search_never_raises_a_lower_endpoint(self):
        # Every weight-1 support is evaluated and none is logical, so the
        # distance is at least 2; the search still reports [0, 4], because a
        # lower endpoint is a supplied input, never a search outcome.
        state = four_qubit_state()
        tightened, record = tighten_ledger_with_search(state, ledger(4), max_weight=1)
        self.assertEqual(record["by_sector"]["X"]["exhaustive_weight"], 1)
        self.assertEqual(tightened.full.lower, 0)

    def test_a_witness_below_a_carried_lower_endpoint_is_no_derivation(self):
        with self.assertRaises(NoDerivation):
            tighten_ledger_with_search(four_qubit_state(), ledger(4, lower=3))


class PlanIntegrationTests(unittest.TestCase):
    def test_the_search_is_off_by_default(self):
        results = plan(four_qubit_state(), ledger(4), 2)
        self.assertTrue(results)
        for result in results:
            self.assertIsNone(result["support_search"])
            self.assertEqual(result["ledger"].full.upper, 4)
            self.assertEqual(result["verdict"], "re-measure")

    def test_the_search_tightens_every_child_and_can_flip_the_verdict(self):
        state = four_qubit_state()
        results = plan(state, ledger(4), 2, support_search=True)
        self.assertEqual([r["operation"] for r in results],
                         [r["operation"] for r in plan(state, ledger(4), 2)])
        for result in results:
            record = result["support_search"]
            self.assertEqual(record["budget"], DEFAULT_SUPPORT_BUDGET)
            found = record["witnesses"]["X"]
            self.assertEqual(found["value"], 1)
            validate_witness(result["state"], "X", tuple(found["support"]), 1)
            self.assertEqual(result["ledger"].full, Interval(0, 1))
            self.assertEqual(result["verdict"], "prune")

    def test_the_configuration_is_forwarded(self):
        results = plan(four_qubit_state(), ledger(4), 2,
                       support_search={"max_weight": 1, "budget": 3})
        for result in results:
            self.assertEqual(result["support_search"]["max_weight"], 1)
            self.assertEqual(result["support_search"]["budget"], 3)
        with self.assertRaises(Malformed):
            plan(four_qubit_state(), ledger(4), 2, support_search="yes")

    def test_a_false_input_lower_bound_drops_the_contradicted_candidates(self):
        # The carried lower endpoint 3 is false for this state (d = 2).  The
        # peel of qubit 0 in sector Z carries that endpoint into the child,
        # where the search finds a lighter witness: the step is non-derivable
        # and the candidate is dropped, while the plain plan still lists it.
        state = four_qubit_state()
        plain = plan(state, ledger(4, lower=3), 2)
        self.assertIn({"op": "E-PEEL", "qubit": 0, "sector": "Z", "row_id": "b1"},
                      [r["operation"] for r in plain])
        searched = plan(state, ledger(4, lower=3), 2, support_search=True)
        self.assertNotIn({"op": "E-PEEL", "qubit": 0, "sector": "Z", "row_id": "b1"},
                         [r["operation"] for r in searched])

    def test_chain_and_sector_search_accept_the_configuration(self):
        state = four_qubit_state()
        chain = plan_chain(state, ledger(4), 2, depth=1, support_search=True)
        self.assertIsInstance(chain, list)
        found = bounded_sector_search(state, ledger(4), "X", budget=8,
                                      support_search={"max_weight": 2})
        for candidate in found["candidates"]:
            self.assertEqual(candidate["support_search"]["max_weight"], 2)
            self.assertEqual(candidate["ledger"].sector["X"].upper, 1)


if __name__ == "__main__":
    unittest.main()
