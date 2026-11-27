"""The separating deletion `E-SPLIT` (admitted 2026-11-25, issue #546).

Tests both the oracle-side derivations (`machine/experiments/split_derived.py`)
and the admitted consumer transition `CodeState.split`, `apply_operation`,
`run_sequence`, and `DistanceLedger.propagate` (unpriced and priced
`split_block_intervals`, spec/OPERATIONAL_SEMANTICS.md §2, §4.48).
"""

import json
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.join(HERE, "experiments")
for path in (EXP, HERE):
    if path not in sys.path:
        sys.path.insert(0, path)

import glue_class_pairs as pairs  # noqa: E402
import split_derived as split  # noqa: E402
from machine.oracle import exact_distances  # noqa: E402
from machine.priced_calculus import (  # noqa: E402
    CodeState,
    DistanceLedger,
    Interval,
    Malformed,
    NoDerivation,
    Row,
    apply_operation,
    run_sequence,
)


def factor(labels, row_id):
    """Two qubits with one Z row on both: k = 1, d_X = 2, d_Z = 1."""
    a, b = labels
    state = CodeState((a, b), (Row(row_id, "Z", (a, b)),), frozenset((row_id,)))
    state.validate()
    return state


class SplitOfAGlueTests(unittest.TestCase):
    """The section 4.33 counterexample, glued and then split."""

    def setUp(self):
        self.left = factor((0, 1), "b1")
        self.right = factor((2, 3), "d1")
        self.glued = pairs.glue(self.left, self.right, [("X", [0, 1, 2, 3])])
        self.seam_ids = [row.id for row in
                         pairs.seam_rows(self.left, self.right, self.glued)]

    def test_glued_distances(self):
        exact = exact_distances(self.glued)
        self.assertEqual((self.glued.k(), exact["X"], exact["Z"]), (1, 2, 2))

    def test_split_returns_the_direct_sum_rows(self):
        child = split.split(self.glued, self.seam_ids)
        summed = CodeState.direct_sum(self.left, self.right)
        self.assertEqual(child.rows, summed.rows)
        self.assertEqual(set(child.Q), set(summed.Q))

    def test_used_grows_by_the_seam_identifier(self):
        child = split.split(self.glued, self.seam_ids)
        summed = CodeState.direct_sum(self.left, self.right)
        self.assertEqual(child.used, summed.used | frozenset(self.seam_ids))
        self.assertNotEqual(child.used, summed.used)

    def test_lower_endpoint_does_not_carry(self):
        # d_Z falls from 2 to 1: the deleted X row exposes a weight-one Z class.
        result = split.check_instance(self.glued, [0, 1])
        self.assertTrue(result["ok"])
        cell = result["sectors"]["Z"]
        self.assertEqual((cell["d_parent"], cell["d_child"]), (2, 1))
        self.assertEqual((cell["w_del"], cell["w_exp"]), (None, 1))
        self.assertEqual((cell["d_A"], cell["d_B"]), (1, 1))

    def test_promoted_row_does_not_lower_the_x_distance(self):
        result = split.check_instance(self.glued, [0, 1])
        cell = result["sectors"]["X"]
        self.assertEqual((cell["d_parent"], cell["d_child"]), (2, 2))
        self.assertEqual(cell["w_del"], 4)

    def test_glue_inverse_record(self):
        result = split.check_glue_inverse(self.left, self.right, [("X", [0, 1, 2, 3])])
        self.assertTrue(result["ok"])
        self.assertTrue(result["used_grows"])


class DisplayDependenceTests(unittest.TestCase):
    """One row space, two displays, different numbers of crossing rows."""

    def state(self, second):
        rows = (Row("a1", "X", (0, 1)), Row("a2", "X", second))
        result = CodeState((0, 1, 2, 3), rows, frozenset(("a1", "a2")))
        result.validate()
        return result

    def test_crossing_count_depends_on_the_display(self):
        crossing = self.state((0, 1, 2, 3))
        separated = self.state((2, 3))
        self.assertEqual(len(split.crossing_rows(crossing, [0, 1])), 1)
        self.assertEqual(len(split.crossing_rows(separated, [0, 1])), 0)

    def test_cut_rank_is_a_property_of_the_row_space(self):
        for second in ((0, 1, 2, 3), (2, 3)):
            self.assertEqual(split.cut_rank(self.state(second), [0, 1], "X"), 0)

    def test_split_of_the_crossing_display_costs_a_logical_qubit(self):
        parent = self.state((0, 1, 2, 3))
        result = split.check_instance(parent, [0, 1])
        self.assertTrue(result["ok"])
        self.assertEqual(result["cut"], 1)
        child = split.split(parent, ["a2"])
        self.assertEqual(child.k(), parent.k() + 1)


class ApplicabilityTests(unittest.TestCase):
    def setUp(self):
        left = factor((0, 1), "b1")
        right = factor((2, 3), "d1")
        self.glued = pairs.glue(left, right, [("X", [0, 1, 2, 3])])

    def test_undisplayed_identifier_has_no_derivation(self):
        with self.assertRaises(NoDerivation):
            split.split(self.glued, ["zz9"])

    def test_repeated_identifier_has_no_derivation(self):
        seam = [row.id for row in self.glued.rows if row.sector == "X"]
        with self.assertRaises(NoDerivation):
            split.split(self.glued, seam + seam)

    def test_cut_missing_a_crossing_row_is_not_separated(self):
        child = split.split(self.glued, ["b1"])
        self.assertFalse(split.is_separated(child, [0, 1]))

    def test_empty_cut_on_a_separated_state_is_the_identity(self):
        summed = CodeState.direct_sum(factor((0, 1), "b1"), factor((2, 3), "d1"))
        self.assertTrue(split.is_separated(summed, [0, 1]))
        self.assertEqual(split.split(summed, []), summed)


class SweepTests(unittest.TestCase):
    def test_seeded_sweep(self):
        report = split.run(seed=546, trials=120)
        self.assertEqual(report["mismatches"], [])
        self.assertEqual(report["glue_mismatches"], [])
        # The sweep is not vacuous: distances fall, extra rows are deleted,
        # and displays exceed the cut rank.
        self.assertGreater(report["strict_drops"], 0)
        self.assertGreater(report["extra_rows_deleted"], 0)
        self.assertGreater(report["above_cut_rank"], 0)


class AdmittedConsumerSplitTests(unittest.TestCase):
    """Tests for the admitted E-SPLIT consumer transition and conditional cell."""

    def setUp(self):
        self.left = factor((0, 1), "b1")
        self.right = factor((2, 3), "d1")
        self.glued = pairs.glue(self.left, self.right, [("X", [0, 1, 2, 3])])
        self.seam_ids = [row.id for row in
                         pairs.seam_rows(self.left, self.right, self.glued)]

    def test_code_state_split_matches_factorized_deletions(self):
        child = self.glued.split([0, 1], self.seam_ids)
        self.assertEqual(child, split.split(self.glued, self.seam_ids))
        self.assertTrue(child.is_separated([0, 1]))
        self.assertEqual(child.n(), self.glued.n())
        self.assertEqual(child.k(), self.glued.k() + len(self.seam_ids))
        self.assertEqual(child.used, self.glued.used)

    def test_extra_non_crossing_row_in_cut_is_allowed(self):
        child = self.glued.split([0, 1], self.seam_ids + ["b1"])
        self.assertTrue(child.is_separated([0, 1]))
        self.assertEqual(child.k(), self.glued.k() + 2)
        self.assertEqual([row.id for row in child.rows], ["d1"])

    def test_inapplicable_cut_conditions_raise_no_derivation(self):
        with self.assertRaises(NoDerivation):
            self.glued.split([0, 9], self.seam_ids)
        with self.assertRaises(NoDerivation):
            self.glued.split([0, 1], self.seam_ids + ["zz9"])
        with self.assertRaises(NoDerivation):
            self.glued.split([0, 1], ["b1"])

    def test_malformed_inputs_raise_malformed(self):
        with self.assertRaises(Malformed):
            self.glued.split([0, 0], self.seam_ids)
        with self.assertRaises(Malformed):
            self.glued.split([0, 1], self.seam_ids + self.seam_ids)
        with self.assertRaises(Malformed):
            self.glued.split("01", self.seam_ids)
        with self.assertRaises(Malformed):
            self.glued.split([True], self.seam_ids)
        with self.assertRaises(Malformed):
            self.glued.split([0, 1], [123])

    def test_apply_operation_and_run_sequence_with_layout(self):
        op = {"op": "E-SPLIT", "block": [0, 1], "cut_ids": self.seam_ids}
        child = apply_operation(self.glued, op)
        self.assertEqual(child, self.glued.split([0, 1], self.seam_ids))
        document = {
            "schema_version": "0.5",
            "name": "glued_4q",
            "code_type": "CSS",
            "n": 4,
            "k": 1,
            "checks": {
                "X": [[0, 1, 2, 3]],
                "Z": [[0, 1], [2, 3]],
            },
            "distance": {
                "d": 2,
                "X": {"value": 2, "confidence": "upper_bound", "witness": [0, 1]},
                "Z": {"value": 2, "confidence": "upper_bound", "witness": [0, 2]},
            },
            "provenance": {"authors": ["test"], "construction": "fixture",
                           "date": "2026-11-25", "origin": "submission"},
            "locality": {
                "coordinates": [[0, 0], [1, 0], [4, 0], [5, 0]],
                "layers": 1,
            },
        }
        state_out, ledger_out, trace = run_sequence(
            document,
            [{
                "op": "E-SPLIT",
                "block": [0, 1],
                "cut_ids": ["a1"],
                "hypothesis": {
                    "split_block_intervals": {
                        "evidence": "exact restriction displays",
                        "X": {"A": [2, 2], "B": [2, 2]},
                        "Z": {"A": [1, 1], "B": [1, 1]},
                    },
                },
            }],
            lower_bounds={"X": {"value": 2, "source": "oracle"},
                          "Z": {"value": 2, "source": "oracle"}},
            target=2,
        )
        self.assertTrue(state_out.is_separated([0, 1]))
        self.assertEqual(state_out.k(), 2)
        self.assertEqual(ledger_out.sector["X"], Interval(2, 2))
        self.assertEqual(ledger_out.sector["Z"], Interval(1, 1))
        self.assertEqual(ledger_out.full, Interval(1, 1))
        self.assertEqual(trace[0]["verdict"], "prune")
        # Parent radius was 5 (row {0,1,2,3}); child radius drops to 1 ({0,1} and {2,3}).
        self.assertAlmostEqual(trace[0]["interaction_radius"], 1.0)
        self.assertEqual(trace[0]["locality_class"], "local-2d-single")

    def test_unpriced_ledger_resets_lower_and_carries_upper(self):
        parent_ledger = DistanceLedger(
            Interval(2, 2),
            {"X": Interval(2, 2), "Z": Interval(2, 2)},
            witnesses={
                "X": [{"support": [0, 1], "value": 2, "source": "parent"}],
                "Z": [{"support": [0, 2], "value": 2, "source": "parent"}],
            },
        )
        child = self.glued.split([0, 1], self.seam_ids)
        out = parent_ledger.propagate(
            {"op": "E-SPLIT", "block": [0, 1], "cut_ids": self.seam_ids},
            child,
            parent_state=self.glued,
        )
        self.assertEqual(out.sector["X"], Interval(0, 2))
        self.assertEqual(out.sector["Z"], Interval(0, 2))
        self.assertEqual(out.full, Interval(0, 2))
        # Adding the newly exposed weight-1 Z witness tightens Z and d to [0, 1].
        out_w = parent_ledger.propagate(
            {"op": "E-SPLIT", "block": [0, 1], "cut_ids": self.seam_ids},
            child,
            observations={"Z": [0]},
            parent_state=self.glued,
        )
        self.assertEqual(out_w.sector["Z"], Interval(0, 1))
        self.assertEqual(out_w.full, Interval(0, 1))

    def test_priced_ledger_one_sector_and_infinite_block(self):
        # One-sector priced leaves the other sector and full lower at 0.
        parent_ledger = DistanceLedger(
            Interval(2, 2),
            {"X": Interval(2, 2), "Z": Interval(2, 2)},
        )
        child = self.glued.split([0, 1], self.seam_ids)
        out_x = parent_ledger.propagate(
            {"op": "E-SPLIT", "block": [0, 1], "cut_ids": self.seam_ids},
            child,
            hypothesis={"split_block_intervals": {
                "evidence": "X-only block bounds",
                "X": {"A": [2, 3], "B": [2, 4]},
            }},
            parent_state=self.glued,
        )
        self.assertEqual(out_x.sector["X"], Interval(2, 2))  # min(3, 4, parent U=2) = 2
        self.assertEqual(out_x.sector["Z"], Interval(0, 2))
        self.assertEqual(out_x.full, Interval(0, 2))

        # Infinite block (k_A = 0): empty block Q_A = [] has d(A) = +inf.
        out_inf = parent_ledger.propagate(
            {"op": "E-SPLIT", "block": [], "cut_ids": []},
            self.glued,
            hypothesis={"split_block_intervals": {
                "evidence": "empty block A has k=0",
                "X": {"A": ["inf", "inf"], "B": [2, 2]},
                "Z": {"A": [None, None], "B": [2, 2]},
            }},
            parent_state=self.glued,
        )
        self.assertEqual(out_inf.sector["X"], Interval(2, 2))
        self.assertEqual(out_inf.sector["Z"], Interval(2, 2))
        self.assertEqual(out_inf.full, Interval(2, 2))

    def test_priced_ledger_refuses_bad_or_contradictory_hypotheses(self):
        parent_ledger = DistanceLedger(
            Interval(2, 2),
            {"X": Interval(2, 2), "Z": Interval(2, 2)},
        )
        child = self.glued.split([0, 1], self.seam_ids)
        op = {"op": "E-SPLIT", "block": [0, 1], "cut_ids": self.seam_ids}
        # Missing evidence
        with self.assertRaises(NoDerivation):
            parent_ledger.propagate(op, child, hypothesis={"split_block_intervals": {
                "X": {"A": [2, 2], "B": [2, 2]},
            }})
        # Contradictory block lower > parent upper (3 > 2)
        with self.assertRaises(NoDerivation):
            parent_ledger.propagate(op, child, hypothesis={"split_block_intervals": {
                "evidence": "bad",
                "X": {"A": [3, 3], "B": [3, 3]},
            }})
        # Contradictory against child witness (claims Z lower = 2, witness weight = 1)
        with self.assertRaises(NoDerivation):
            parent_ledger.propagate(
                op, child,
                hypothesis={"split_block_intervals": {
                    "evidence": "false claim",
                    "Z": {"A": [2, 2], "B": [2, 2]},
                }},
                observations={"Z": [0]},
            )
        # Infinite lower bound on k > 0 child refused
        with self.assertRaises(NoDerivation):
            parent_ledger.propagate(op, child, hypothesis={"split_block_intervals": {
                "evidence": "impossible inf",
                "X": {"A": [None, None], "B": [None, None]},
            }})

    def test_apply_operation_rejects_alias_missing_and_unexpected_keys(self):
        # Canonical keys are `block` and `cut_ids` only; legacy aliases and
        # typos are Malformed rather than falling through silently.
        for bad_op in (
            {"op": "E-SPLIT", "block_qubits": [0, 1], "cut_ids": self.seam_ids},
            {"op": "E-SPLIT", "Q_A": [0, 1], "cut_ids": self.seam_ids},
            {"op": "E-SPLIT", "block": [0, 1], "cut_row_ids": self.seam_ids},
            {"op": "E-SPLIT", "block": [0, 1], "row_ids": self.seam_ids},
            {"op": "E-SPLIT", "block": [0, 1], "R": self.seam_ids},
            {"op": "E-SPLIT", "block": [0, 1], "cut_ids": self.seam_ids, "Q_A": [0, 1]},
            {"op": "E-SPLIT", "block": [0, 1]},
            {"op": "E-SPLIT", "cut_ids": self.seam_ids},
        ):
            with self.assertRaises(Malformed):
                apply_operation(self.glued, bad_op)

    def test_priced_split_refuses_lower_above_validated_weight_one_logical_on_pinned_parent(self):
        fixture_path = os.path.join(HERE, "fixtures", "qldpc_10_2_3_b.json")
        with open(fixture_path, "r", encoding="utf-8") as handle:
            document = json.load(handle)
        parent = CodeState.from_challenge(document)
        block = [0, 1, 2, 3, 4]
        cut_ids = [row.id for row in parent.crossing_rows(block)]
        self.assertEqual(len(cut_ids), 7)
        child = parent.split(block, cut_ids)
        self.assertEqual(child.k(), 9)
        exact = exact_distances(child)
        self.assertEqual((exact["X"], exact["Z"], exact["d"]), (1, 1, 1))

        parent_ledger = DistanceLedger.from_challenge(
            parent,
            document,
            lower_bounds={
                "X": {"value": 3, "source": "pinned parent"},
                "Z": {"value": 3, "source": "pinned parent"},
            },
        )
        op = {"op": "E-SPLIT", "block": block, "cut_ids": cut_ids}

        # Supplying [3, 3] for both blocks in both sectors (or in either sector
        # alone) contradicts the child's validated weight-1 singleton logicals.
        for bad_hyp in (
            {
                "evidence": "false both sectors",
                "X": {"A": [3, 3], "B": [3, 3]},
                "Z": {"A": [3, 3], "B": [3, 3]},
            },
            {
                "evidence": "false X only",
                "X": {"A": [3, 3], "B": [3, 3]},
            },
            {
                "evidence": "false Z only",
                "Z": {"A": [3, 3], "B": [3, 3]},
            },
            {
                "evidence": "false block B in X",
                "X": {"A": [1, 1], "B": [3, 3]},
            },
            {
                "evidence": "false block A in Z (qubit 2 is bare Z-logical)",
                "Z": {"A": [3, 3], "B": [1, 1]},
            },
        ):
            with self.assertRaises(NoDerivation):
                parent_ledger.propagate(
                    op,
                    child,
                    hypothesis={"split_block_intervals": bad_hyp},
                    parent_state=parent,
                )

        # Truthful [1, 1] and [0, 1] bounds are accepted and stay conditional.
        out_exact = parent_ledger.propagate(
            op,
            child,
            hypothesis={"split_block_intervals": {
                "evidence": "exact restriction displays",
                "X": {"A": [1, 1], "B": [1, 1]},
                "Z": {"A": [1, 1], "B": [1, 1]},
            }},
            parent_state=parent,
        )
        self.assertEqual(out_exact.sector["X"], Interval(1, 1))
        self.assertEqual(out_exact.sector["Z"], Interval(1, 1))
        self.assertEqual(out_exact.full, Interval(1, 1))
        self.assertTrue(
            any(c.get("cell") == "E-SPLIT priced" and c.get("status") == "conditional"
                for c in out_exact.conditions)
        )

        out_loose = parent_ledger.propagate(
            op,
            child,
            hypothesis={"split_block_intervals": {
                "evidence": "loose restriction displays",
                "X": {"A": [0, 1], "B": [0, 1]},
                "Z": {"A": [0, 1], "B": [0, 1]},
            }},
            parent_state=parent,
        )
        self.assertEqual(out_loose.sector["X"], Interval(0, 1))
        self.assertEqual(out_loose.sector["Z"], Interval(0, 1))
        self.assertEqual(out_loose.full, Interval(0, 1))

    def test_weight_one_check_respects_block_boundary_and_weight_one_stabilizers(self):
        # Block A = {0} with a weight-1 X stabilizer (so qubit 0 is in no Z row,
        # yet {0} lies in span(X) and is NOT an X-logical) plus block B = {1, 2}
        # with Z row (1, 2) (so d_X(B) = 2 and d_Z(B) = 1).
        state = CodeState(
            (0, 1, 2),
            (Row("a1", "X", (0,)), Row("b1", "Z", (1, 2))),
            frozenset(("a1", "b1")),
        )
        state.validate()
        # Qubit 0 is in no Z row, but {0} IS in span(X), so it is NOT an X-logical:
        # d_X(A) = +inf, d_X(B) = 2, so d_X(state) = 2.
        self.assertEqual(exact_distances(state)["X"], 2)
        ledger = DistanceLedger(
            Interval(1, 2),
            {"X": Interval(2, 2), "Z": Interval(1, 1)},
        )
        op = {"op": "E-SPLIT", "block": [0], "cut_ids": []}
        out_x = ledger.propagate(
            op,
            state,
            hypothesis={"split_block_intervals": {
                "evidence": "weight-1 stabilizer in A is not a logical",
                "X": {"A": ["inf", "inf"], "B": [2, 2]},
            }},
            parent_state=state,
        )
        self.assertEqual(out_x.sector["X"], Interval(2, 2))

        # Now block A = {0} has NO checks (bare X- and Z-logical {0}, d_A = 1),
        # while block B = {1, 2} has Z row (1, 2) (d_X(B) = 2, no bare X-logical in B).
        state_ab = CodeState(
            (0, 1, 2),
            (Row("b1", "Z", (1, 2)),),
            frozenset(("b1",)),
        )
        state_ab.validate()
        ledger_ab = DistanceLedger(
            Interval(1, 2),
            {"X": Interval(1, 2), "Z": Interval(1, 2)},
        )
        # Truthful A=[1, 1], B=[2, 2] passes.
        out_ab = ledger_ab.propagate(
            op,
            state_ab,
            hypothesis={"split_block_intervals": {
                "evidence": "A has bare X-logical, B has d_X=2",
                "X": {"A": [1, 1], "B": [2, 2]},
            }},
            parent_state=state_ab,
        )
        self.assertEqual(out_ab.sector["X"], Interval(1, 1))
        # Swapped A=[2, 2], B=[1, 1] is refused because qubit 0 in block A is a bare X-logical.
        with self.assertRaises(NoDerivation):
            ledger_ab.propagate(
                op,
                state_ab,
                hypothesis={"split_block_intervals": {
                    "evidence": "swapped false A lower bound",
                    "X": {"A": [2, 2], "B": [1, 1]},
                }},
                parent_state=state_ab,
            )


if __name__ == "__main__":
    unittest.main()
