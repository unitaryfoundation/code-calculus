"""Tests for the consumer-side search diagnostics and objectives (qldpc-challenge #7116).

Every record here is search control: it selects candidates and explains why
others were dropped.  None of it moves a ledger endpoint or discharges an
obligation (spec/CLAIMS.md, Admission).
"""
import unittest

import json
from pathlib import Path

from machine.constructors import structural_profile
from machine.experiments.applicability_report import render
from machine.oracle import exact_distances
from machine.planner import (
    CHILD_SCREENS,
    REPORT_FAMILIES,
    applicability_blocking,
    bounded_sector_search,
    candidate_moves,
    constructor_candidates,
    move_applicability_report,
    new_applicability_record,
    objective_improvement,
    plan,
    refusal_reason,
    run_campaign,
    weight_one_logicals,
)
from machine.priced_calculus import (
    CodeState,
    DistanceLedger,
    Interval,
    Malformed,
    NoDerivation,
    Row,
    apply_operation,
)

FIXTURE = Path(__file__).resolve().parent / "fixtures" / "qldpc_10_2_3_b.json"


def _pinned_parent():
    with open(FIXTURE) as source:
        return CodeState.from_challenge(json.load(source))


def _x_only_state():
    """Three independent X-rows on three qubits, no Z-row; every qubit is
    in at least two X-rows."""
    rows = (
        Row("a9001", "X", (0, 1)),
        Row("a9002", "X", (1, 2)),
        Row("a9003", "X", (0, 1, 2)),
    )
    return CodeState((0, 1, 2), rows, frozenset(r.id for r in rows))


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


class RefusalReasonTests(unittest.TestCase):
    """The failed premise behind an ``apply_fail`` (issue #592)."""

    def test_reason_groups_by_premise_not_by_row(self):
        self.assertEqual(
            refusal_reason(NoDerivation("Independent(a3; pres) fails")),
            refusal_reason(NoDerivation("Independent(b17; pres) fails")))
        self.assertEqual(
            refusal_reason(NoDerivation("DisplayedGenerator(a3, pres) fails")),
            "DisplayedGenerator(r, pres) fails")
        plain = "E-GRAFT coverage condition fails"
        self.assertEqual(refusal_reason(NoDerivation(plain)), plain)

    def test_search_record_names_the_premise_of_each_apply_failure(self):
        diag = new_applicability_record()
        plan(_x_only_state(), DistanceLedger(
            Interval(0, None), {"X": Interval(0, None), "Z": Interval(0, None)}),
            diagnostics=diag)
        graft = diag["E-GRAFT"]
        self.assertEqual(graft["apply_fail"], 3)
        self.assertEqual(
            graft["refusals"],
            {"E-GRAFT grafted qubit is not in the opposite sector": 3})
        for family, counts in diag.items():
            self.assertEqual(sum(counts["refusals"].values()),
                             counts["apply_fail"], family)


class MoveApplicabilityReportTests(unittest.TestCase):
    """The parent-level report (issue #592)."""

    def assertPartitioned(self, report):
        self.assertEqual(tuple(report["families"]), REPORT_FAMILIES)
        for family, entry in report["families"].items():
            refused = sum(entry["refusals"].values())
            screened = sum(entry["screens"].values())
            self.assertEqual(entry["domain"],
                             refused + screened + entry["usable"], family)
            self.assertEqual(entry["derived"],
                             screened + entry["usable"], family)
            self.assertLessEqual(set(entry["screens"]), set(CHILD_SCREENS))
            self.assertEqual(entry["blocking"] is None,
                             entry["usable"] > 0, family)
            self.assertLessEqual(
                set(entry["example"]),
                set(entry["refusals"]) | set(entry["screens"]))

    def test_every_candidate_lands_in_exactly_one_place(self):
        for state in (_pinned_parent(), _weight_state(), _x_only_state()):
            for cap in (None, 2, 4):
                self.assertPartitioned(
                    move_applicability_report(state, weight_cap=cap))

    def test_pinned_parent_peel_is_refused_by_unique_touch_only(self):
        report = move_applicability_report(_pinned_parent())
        peel = report["families"]["E-PEEL"]
        self.assertEqual(peel["domain"], 20)
        self.assertEqual(peel["usable"], 8)
        self.assertEqual(sorted(peel["refusals"].values()), [6, 6])
        for reason in peel["refusals"]:
            self.assertIn("unique-touch fails", reason)
        # Eight peels: the eight sector/qubit pairs of column weight 1.
        column = report["parent"]["column_weight"]
        self.assertEqual(column["X"]["histogram"], {1: 4, 2: 6})
        self.assertEqual(column["Z"]["histogram"], {1: 4, 2: 6})

    def test_weight_cap_explains_a_weight_shedding_campaign(self):
        parent = _pinned_parent()
        free = move_applicability_report(parent)["families"]["P-REBASE"]
        self.assertEqual((free["domain"], free["usable"]), (24, 24))
        self.assertIsNone(free["blocking"])
        capped = move_applicability_report(
            parent, weight_cap=4)["families"]["P-REBASE"]
        self.assertEqual(capped["usable"], 0)
        self.assertEqual(capped["screens"], {"over_weight_cap": 24})
        self.assertEqual(capped["blocking"], "over_weight_cap")
        # Every elementary mix of this parent raises the check weight.
        self.assertEqual(capped["best_child_w"], 6)
        self.assertEqual(parent.w(), 4)

    def test_rebase_can_be_left_out(self):
        report = move_applicability_report(_pinned_parent(), rebase=False)
        rebase = report["families"]["P-REBASE"]
        self.assertFalse(rebase["enabled"])
        self.assertEqual(rebase["domain"], 0)
        self.assertIsNone(rebase["blocking"])

    def test_a_sector_with_no_weight_one_column_has_no_peel(self):
        report = move_applicability_report(_x_only_state())
        self.assertEqual(report["parent"]["column_weight"]["X"]["min"], 2)
        peel = report["families"]["E-PEEL"]
        self.assertEqual(peel["usable"], 0)
        self.assertEqual(peel["refusals"], {
            "E-PEEL unique-touch fails: q is not in exactly one displayed "
            "X-row": 3,
            "no displayed Z-row contains the qubit": 3,
        })
        self.assertIsNotNone(peel["blocking"])
        graft = report["families"]["E-GRAFT"]
        self.assertEqual(graft["blocking"],
                         "E-GRAFT grafted qubit is not in the opposite sector")

    def test_distance_one_children_are_named_and_the_oracle_agrees(self):
        parent = _pinned_parent()
        report = move_applicability_report(parent)
        deletion = report["families"]["C-DELETE-CHECK"]
        self.assertEqual(deletion["screens"], {"weight_one_logical": 8})
        self.assertEqual(deletion["blocking"], "weight_one_logical")
        puncture = report["families"]["E-PUNCTURE"]
        self.assertEqual(puncture["screens"],
                         {"weight_one_logical": 6, "bare_qubit": 2})
        for family in ("C-DELETE-CHECK", "E-PUNCTURE"):
            entry = report["families"][family]
            for screen in entry["screens"]:
                child = apply_operation(parent, entry["example"][screen])
                found = weight_one_logicals(child)
                exact = exact_distances(child)
                for sector in ("X", "Z"):
                    self.assertEqual(bool(found[sector]),
                                     exact[sector] == 1, (family, sector))
        self.assertEqual(weight_one_logicals(parent), {"X": [], "Z": []})

    def test_bad_arguments_are_refused(self):
        for cap in (0, -1, True, 2.5, "4"):
            with self.assertRaises(Malformed):
                move_applicability_report(_pinned_parent(), weight_cap=cap)
        with self.assertRaises(Malformed):
            move_applicability_report({"n": 3})

    def test_rendered_table_has_a_line_per_family(self):
        text = render(move_applicability_report(_pinned_parent(),
                                                weight_cap=4))
        for family in REPORT_FAMILIES:
            self.assertIn(family, text)
        self.assertIn("24 x over_weight_cap", text)


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


class BlockingTests(unittest.TestCase):
    """``blocking`` in search and campaign records (issue #652)."""

    @staticmethod
    def _record(**counts):
        record = new_applicability_record()
        record["E-GRAFT"].update(counts)
        return record

    def test_a_refused_candidate_is_counted_once(self):
        # Ten refusals under two premises, seven bare-qubit children: the
        # screen is the commonest reason, not the refusal total.
        record = self._record(enumerated=17, apply_fail=10, bare_qubit=7,
                              refusals={"premise A": 6, "premise B": 4})
        applicability_blocking(record)
        self.assertEqual(record["E-GRAFT"]["blocking"], "bare_qubit")

    def test_unattributed_refusals_stay_apply_fail(self):
        record = self._record(enumerated=9, apply_fail=9,
                              refusals={"premise A": 4})
        applicability_blocking(record)
        self.assertEqual(record["E-GRAFT"]["blocking"], "apply_fail")

    def test_annotations_and_totals_are_not_reasons(self):
        record = self._record(enumerated=3, improving=50, dominated=3)
        applicability_blocking(record)
        self.assertEqual(record["E-GRAFT"]["blocking"], "dominated")

    def test_survivors_unblock_and_nothing_enumerated_is_empty(self):
        record = self._record(enumerated=2, survived=1, dominated=1)
        applicability_blocking(record)
        self.assertIsNone(record["E-GRAFT"]["blocking"])
        self.assertEqual(record["E-PEEL"]["blocking"], "empty domain")

    def test_families_not_asked_for_are_not_blocked(self):
        result = bounded_sector_search(_pinned_parent(), _ledger(), "X",
                                       budget=16, sector_swap=False)
        diag = result["applicability"]
        for family in ("P-REBASE", "E-LOCAL-HADAMARD"):
            self.assertFalse(diag[family]["enabled"])
            self.assertIsNone(diag[family]["blocking"])
        self.assertNotIn("blocking", result)
        self.assertNotIn("refusal_histogram", result)

    def test_search_blocking_is_set_for_every_family(self):
        result = bounded_sector_search(_pinned_parent(), _ledger(), "X",
                                       budget=16, sector_swap=True)
        for family, counts in result["applicability"].items():
            if counts["enabled"] and counts["survived"] == 0:
                self.assertIsNotNone(counts["blocking"], family)
                self.assertNotIn(counts["blocking"],
                                 ("improving", "enumerated", "survived"))

    @staticmethod
    def _unknown_ledger():
        return DistanceLedger(Interval(0, None), {"X": Interval(0, None),
                                                  "Z": Interval(0, None)})

    def test_verdict_pruned_children_block_a_campaign_family(self):
        diag = new_applicability_record()
        candidates = plan(_pinned_parent(), self._unknown_ledger(), 4,
                          diagnostics=diag, support_search=True)
        self.assertTrue(candidates)
        self.assertTrue(all(c["verdict"] == "prune" for c in candidates))
        applicability_blocking(diag, candidates)
        pruned = [f for f, c in diag.items() if c["verdict_prune"]]
        self.assertIn("E-GRAFT", pruned)
        for family in pruned:
            self.assertEqual(diag[family]["blocking"], "verdict_prune")
        # Read without the verdicts, the same counts say these families
        # had survivors.
        applicability_blocking(diag)
        self.assertIsNone(diag["E-GRAFT"]["blocking"])

    def test_no_survivor_record_says_why_without_a_rerun(self):
        # The pinned parent at target 4: every derived child is pruned by
        # its verdict once the support search has run.
        history = run_campaign(_pinned_parent(), self._unknown_ledger(), 4,
                               steps=3)
        self.assertEqual(len(history), 1)
        record = history[0]
        self.assertEqual(record["stop_reason"], "no-survivor")
        diag = record["applicability"]
        self.assertEqual(set(diag), set(new_applicability_record()))
        self.assertFalse(diag["P-REBASE"]["enabled"])
        self.assertIsNone(diag["P-REBASE"]["blocking"])
        self.assertEqual(diag["E-GRAFT"]["blocking"], "verdict_prune")
        for family, counts in diag.items():
            if counts["enabled"]:
                # No child survived its verdict, so every family asked for
                # names its reason.
                self.assertIsNotNone(counts["blocking"], family)
                self.assertEqual(counts["survived"], counts["verdict_prune"],
                                 family)
        json.dumps(record, default=str)

    def test_every_campaign_record_carries_its_step_record(self):
        parent = _pinned_parent()
        ledger = DistanceLedger(Interval(3, 3),
                                {"X": Interval(3, 3), "Z": Interval(3, 3)})
        history = run_campaign(parent, ledger, 4, steps=2,
                               support_search=False)
        self.assertEqual(history[-1]["stop_reason"], "step-limit-reached")
        for record in history:
            diag = record["applicability"]
            family = record["operation"]["op"]
            self.assertIsNone(diag[family]["blocking"])
            self.assertIn("verdict_prune", diag[family])
        self.assertIsNot(history[0]["applicability"],
                         history[1]["applicability"])


if __name__ == "__main__":
    unittest.main()
