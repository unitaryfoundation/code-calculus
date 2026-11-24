"""Tests for the consumer-side search diagnostics and objectives (qldpc-challenge #7116).

Every record here is search control: it selects candidates and explains why
others were dropped.  None of it moves a ledger endpoint or discharges an
obligation (spec/CLAIMS.md, Admission).
"""
import unittest

from machine.constructors import structural_profile
from machine.planner import (
    bounded_sector_search,
    candidate_moves,
    constructor_candidates,
    new_applicability_record,
    objective_improvement,
)
from machine.priced_calculus import (
    CodeState,
    DistanceLedger,
    Interval,
    Row,
)


def _weight_state():
    """n=4, k=0, displayed max weight 4; deleting the wide row sheds weight."""
    rows = (
        Row("a9001", "X", (0, 1, 2, 3)),
        Row("a9002", "X", (0, 1)),
        Row("b9001", "Z", (0, 1)),
        Row("b9002", "Z", (2, 3)),
    )
    return CodeState((0, 1, 2, 3), rows, frozenset(r.id for r in rows))


def _ledger():
    # Fixed sector intervals: no distance transport can improve either side.
    return DistanceLedger(Interval(0, 2),
                          {"X": Interval(2, 2), "Z": Interval(2, 2)})


class ApplicabilityDiagnosticsTests(unittest.TestCase):
    def test_record_covers_every_family_and_accounts_for_every_drop(self):
        state = _weight_state()
        result = bounded_sector_search(state, _ledger(), "X", budget=8,
                                       sector_swap=True)
        diag = result["applicability"]
        self.assertEqual(set(diag), set(new_applicability_record()))
        self.assertFalse(diag["P-REBASE"]["enabled"])
        self.assertTrue(diag["E-LOCAL-HADAMARD"]["enabled"])
        for family, counts in diag.items():
            accounted = sum(counts[reason] for reason in (
                "apply_fail", "bare_qubit", "disconnected", "derive_fail",
                "min_upper", "deep_refuted", "screened", "dominated",
                "over_budget", "survived"))
            self.assertEqual(accounted, counts["enumerated"], family)

    def test_extend_premise_screen_leaves_no_apply_failures(self):
        state = _weight_state()
        enumerated = [op for op in candidate_moves(state)
                      if op["op"] == "E-EXTEND"]
        self.assertTrue(enumerated)
        result = bounded_sector_search(state, _ledger(), "X", budget=8,
                                       sector_swap=False)
        extend = result["applicability"]["E-EXTEND"]
        self.assertEqual(extend["apply_fail"], 0)

    def test_callers_record_is_filled_in_place(self):
        diag = new_applicability_record()
        result = bounded_sector_search(_weight_state(), _ledger(), "X",
                                       budget=4, diagnostics=diag,
                                       sector_swap=False)
        self.assertIs(result["applicability"], diag)
        self.assertGreater(diag["C-DELETE-CHECK"]["enumerated"], 0)
        # The swap was not asked for: distinct from "asked and refused".
        self.assertFalse(diag["E-LOCAL-HADAMARD"]["enabled"])
        self.assertEqual(diag["E-LOCAL-HADAMARD"]["enumerated"], 0)


class ObjectiveTests(unittest.TestCase):
    def test_distance_objective_blind_to_a_weight_gain(self):
        parent = _weight_state()
        ledger = _ledger()
        child_rows = (
            Row("a9002", "X", (0, 1)),
            Row("b9001", "Z", (0, 1)),
            Row("b9002", "Z", (2, 3)),
        )
        child = CodeState((0, 1, 2, 3), child_rows,
                          frozenset(r.id for r in child_rows))
        candidate = {"state": child, "ledger": ledger, "n": child.n(),
                     "k": child.k()}
        # Same carried interval on both sides: the distance predicate cannot
        # see the max displayed check weight falling from 4 to 2.
        self.assertFalse(objective_improvement(candidate, parent, ledger,
                                               "distance", "X"))
        self.assertTrue(objective_improvement(candidate, parent, ledger,
                                              "weight", "X"))
        self.assertTrue(objective_improvement(candidate, parent, ledger,
                                              {"axis": "weight"}, "X"))

    def test_n_k_and_target_set_objectives(self):
        parent = _weight_state()
        ledger = _ledger()
        child_rows = (Row("a9002", "X", (0, 1)), Row("b9001", "Z", (0, 1)))
        child = CodeState((0, 1, 2), child_rows,
                          frozenset(r.id for r in child_rows))
        candidate = {"state": child, "ledger": ledger, "n": child.n(),
                     "k": child.k()}
        self.assertTrue(objective_improvement(candidate, parent, ledger,
                                              "n", "X"))
        self.assertTrue(objective_improvement(candidate, parent, ledger,
                                              "k", "X"))
        self.assertTrue(objective_improvement(
            candidate, parent, ledger, {"axis": "n", "targets": {3}}, "X"))
        self.assertFalse(objective_improvement(
            candidate, parent, ledger, {"axis": "n", "targets": {5}}, "X"))

    def test_callable_objective_and_unknown_axis(self):
        parent = _weight_state()
        ledger = _ledger()
        candidate = {"state": parent, "ledger": ledger, "n": parent.n(),
                     "k": parent.k()}
        self.assertTrue(objective_improvement(
            candidate, parent, ledger, lambda child, p, l: True, "X"))
        with self.assertRaises(Exception):
            objective_improvement(candidate, parent, ledger, "bogus", "X")

    def test_search_passes_objective_through_and_separates_swap(self):
        result = bounded_sector_search(_weight_state(), _ledger(), "X",
                                       budget=8, objective="weight",
                                       sector_swap=True)
        self.assertEqual(result["objective"], "weight")
        swap_ops = [c["operation"]["op"] for c in result["presentation_candidates"]]
        improving_ops = [c["operation"]["op"] for c in result["improving"]]
        self.assertNotIn("E-LOCAL-HADAMARD", improving_ops)
        if "E-LOCAL-HADAMARD" in swap_ops:
            self.assertTrue(all(c.get("presentation_only")
                                for c in result["presentation_candidates"]))


class ConstructorScreeningTests(unittest.TestCase):
    def test_structural_profile_detects_a_direct_sum(self):
        # Two disjoint 2-qubit blocks: X on (0,1), Z on (2,3).
        rows = (Row("a9001", "X", (0, 1)), Row("b9001", "Z", (2, 3)))
        state = CodeState((0, 1, 2, 3), rows, frozenset(r.id for r in rows))
        profile = structural_profile(state)
        self.assertFalse(profile["connected"])
        self.assertEqual(profile["blocks"], 2)
        self.assertEqual(profile["block_sizes"], [2, 2])

    def test_structural_profile_of_a_connected_code(self):
        rows = (Row("a9001", "X", (0, 1, 2)),
                Row("b9001", "Z", (1, 2, 3)))
        state = CodeState((0, 1, 2, 3), rows, frozenset(r.id for r in rows))
        profile = structural_profile(state)
        self.assertTrue(profile["connected"])
        self.assertEqual(profile["blocks"], 1)

    def test_constructor_candidates_record_derivation_and_profile(self):
        state = _weight_state()
        ledger = _ledger()
        entries = constructor_candidates(
            state, ledger,
            [{"constructor": "L-HGP", "H1": [[1, 1]], "H2": [[1, 1]]},
             {"constructor": "NOT-A-CONSTRUCTOR"}],
            2, "weight", "X")
        self.assertEqual(len(entries), 2)
        self.assertTrue(entries[0]["derived"])
        self.assertIn("connected", entries[0])
        self.assertFalse(entries[1]["derived"])
        self.assertIn("reason", entries[1])

    def test_constructor_specs_are_evaluated_by_the_search(self):
        result = bounded_sector_search(
            _weight_state(), _ledger(), "X", budget=8, sector_swap=False,
            constructor_specs=[{"constructor": "L-HGP", "H1": [[1, 1]],
                               "H2": [[1, 1]]}])
        entries = result["constructor_candidates"]
        self.assertEqual(len(entries), 1)
        self.assertTrue(entries[0]["derived"])
        self.assertIn("connected", entries[0])


if __name__ == "__main__":
    unittest.main()
