"""The column-splitting reduction for the exposure price (issue #326).

`design/DERIVED_RELATIONS.md` section 3a: the t-fold split of a parent has
Z column weight at most three and exposure price t times the parent's. The
tests pin the gadget on hand instances and on a seeded random run; they are
evidence that the transcription matches the derivation, not a proof.
"""

import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.join(HERE, "experiments")
if EXP not in sys.path:
    sys.path.insert(0, EXP)

import weight3_split_reduction as reduction  # noqa: E402
from machine.priced_calculus import (  # noqa: E402
    CodeState,
    Row,
    column_weights,
    graphlike_exposure_price,
)


def star_parent():
    """Qubit 0 lies in four independent Z-rows (c_max = 4, so t = 2); the
    X-row {4, 5} commutes with all of them and k = 1."""
    rows = (Row("b1", "Z", (0, 1)), Row("b2", "Z", (0, 2)), Row("b3", "Z", (0, 3)),
            Row("b4", "Z", (0, 4, 5)), Row("a1", "X", (4, 5)))
    state = CodeState((0, 1, 2, 3, 4, 5), rows, frozenset(row.id for row in rows))
    state.validate()
    return state


class SplitGadgetTests(unittest.TestCase):
    def test_split_has_column_weight_at_most_three_and_scales_the_price(self):
        state = star_parent()
        self.assertEqual(reduction.split_copies(state), 2)
        child = reduction.split_state(state, 2)
        self.assertEqual(len(child.Q), 12)
        self.assertEqual(max(column_weights(child, "Z").values()), 3)
        # Deleting b1: the exposed vectors are even on b2, b3, b4 and odd on
        # b1, so {1} is one of them and the price is 1; the split doubles it
        # to the equality-joined pair of copies of qubit 1.
        parent = reduction.exposure_price_exhaustive(state, ["b1"])
        split = reduction.exposure_price_exhaustive(child, ["b1"])
        self.assertEqual(parent, 1)
        self.assertEqual(split, 2 * parent)
        # Both X-rows and equality rows are in place: the split is a valid
        # CSS state (validate ran) whose X-row takes every copy.
        x_row = next(row for row in child.rows if row.sector == "X")
        self.assertEqual(x_row.support, (8, 9, 10, 11))

    def test_a_graphlike_parent_splits_trivially_and_matches_the_provider(self):
        rows = (Row("b1", "Z", (0, 1)), Row("b2", "Z", (1, 2)), Row("b3", "Z", (2,)))
        state = CodeState((0, 1, 2), rows, frozenset(row.id for row in rows))
        self.assertEqual(reduction.split_copies(state), 1)
        child = reduction.split_state(state, 1)
        self.assertEqual(child.Q, state.Q)
        self.assertEqual(reduction.exposure_price_exhaustive(state, ["b1"]),
                         reduction.exposure_price_exhaustive(child, ["b1"]))
        verdict = graphlike_exposure_price(state, deleted="b1")
        self.assertEqual(verdict["status"], "computed")
        self.assertEqual(verdict["w_exp"], reduction.exposure_price_exhaustive(state, ["b1"]))

    def test_too_few_copies_is_refused(self):
        with self.assertRaises(ValueError):
            reduction.split_state(star_parent(), 1)

    def test_a_deleted_set_of_two_checks_scales_the_same_way(self):
        # The exposed set of a deleted set is odd against at least one of
        # its rows; the split preserves every parity, so the factor is the
        # same t for any deleted set.
        state = star_parent()
        child = reduction.split_state(state, 2)
        parent = reduction.exposure_price_exhaustive(state, ["b1", "b2"])
        self.assertEqual(reduction.exposure_price_exhaustive(child, ["b1", "b2"]), 2 * parent)
        # Deleting one check of a valid state always exposes something: the
        # displayed rows are independent, so the deleted row is outside the
        # span of the rest, and the split keeps that.
        for deleted in ("b1", "b4"):
            self.assertIsNotNone(reduction.exposure_price_exhaustive(child, [deleted]))

    def test_refusal_cites_the_recorded_reduction(self):
        verdict = graphlike_exposure_price(star_parent(), deleted="b1")
        self.assertEqual(verdict["status"], "unavailable")
        self.assertFalse(verdict["graphlike"])
        self.assertIn("NP-hard", verdict["citation_status"])
        self.assertIn("DERIVED_RELATIONS.md", verdict["citation_status"])

    def test_seeded_random_run_has_no_mismatches(self):
        report = reduction.run(seed=326, trials=40)
        self.assertEqual(report["mismatches"], [])
        self.assertEqual(report["column_weight_violations"], [])
        self.assertEqual(report["provider_mismatches"], [])
        self.assertGreater(report["nontrivial_splits"], 0)
        self.assertGreater(report["finite_prices"], 0)


if __name__ == "__main__":
    unittest.main()
