"""Unit tests for the asserted discovery-loop stress battery (issue #577).

Exercises fast smoke-sized trials of the offline quadrants (oracle import-path
hygiene, Quadrant 1 over all 17 admitted constructors + Pareto/domination
brute-force + small-n oracle differential, Quadrant 3 invariant fuzzing
including plan_chain, Quadrant 4 adversarial inputs), advisory wall-clock
budgets, offline Quadrant 2 / scale-ladder plumbing, known-violation
allowlisting, reproducible failure-dump structure, CLI ``--ci`` offline
execution, and the committed baseline report without requiring an external
qldpc-challenge checkout.
"""

import json
import shutil
import tempfile
import unittest
from pathlib import Path

from machine.constructors import ADMITTED_CONSTRUCTORS
from machine.experiments import stress_campaign as sc
from machine.priced_calculus import CodeState, Row

FIXTURE_10_2_3 = Path(__file__).resolve().parent / "fixtures" / "qldpc_10_2_3_b.json"


def _synthetic_gate_report(
    *,
    earned_d: int | None,
    refuted_weight: int | None = None,
    failed_structural: tuple[str, ...] = (),
    ok: bool = True,
) -> dict:
    checks = [
        {"check": name, "ok": name not in failed_structural}
        for name in sorted(sc.REQUIRED_GATE_STRUCTURAL_CHECKS)
    ]
    if refuted_weight is not None:
        checks.append(
            {
                "check": "distance_not_refuted",
                "ok": False,
                "detail": f"found weight-{refuted_weight} logical operator",
            }
        )
    else:
        checks.append({"check": "distance_not_refuted", "ok": True, "detail": "not refuted"})
    rep = {"ok": ok and not failed_structural and refuted_weight is None, "checks": checks}
    if earned_d is not None:
        rep["earned_distance"] = {"d": {"value": earned_d}}
    return rep


class StressCampaignTests(unittest.TestCase):
    def test_oracle_import_hygiene_passes(self):
        rec = sc.ViolationRecorder(seed=sc.DEFAULT_SEED)
        metrics = sc.check_oracle_import_hygiene(rec)
        self.assertEqual(metrics["static_oracle_hits"], 0)
        self.assertEqual(metrics["runtime_oracle_modules"], [])
        self.assertIsInstance(metrics["within_budget"], bool)
        self.assertEqual(rec.unexpected, [])

    def test_quadrant_1_covers_all_admitted_constructors_and_passes(self):
        rec = sc.ViolationRecorder(seed=sc.DEFAULT_SEED)
        metrics = sc.run_quadrant_1_oracle_differential(
            rec, sc.DEFAULT_SEED, small_trials=3, pareto_trials=4
        )
        self.assertEqual(
            metrics["admitted_constructors_covered"], len(ADMITTED_CONSTRUCTORS)
        )
        self.assertEqual(
            metrics["transition_differential_owner"],
            "machine/experiments/priced_conformance_harness.py",
        )
        self.assertGreater(metrics["pareto_pairs_checked"], 0)
        self.assertGreater(metrics["small_n_planner_children_checked"], 0)
        self.assertIsInstance(metrics["within_budget"], bool)
        self.assertEqual(rec.unexpected, [])

    def test_quadrant_3_invariants_pass(self):
        rec = sc.ViolationRecorder(seed=sc.DEFAULT_SEED)
        metrics = sc.run_quadrant_3_invariant_fuzzing(
            rec, sc.DEFAULT_SEED, trials=3, chain_random_states=2
        )
        self.assertTrue(metrics["symplectic_roundtrip_ok"])
        self.assertGreater(metrics["candidates_checked"], 0)
        self.assertGreater(metrics["chains_checked"], 0)
        self.assertGreater(metrics["invalid_move_and_entrypoint_checks"], 0)
        self.assertIsInstance(metrics["within_budget"], bool)
        self.assertEqual(rec.unexpected, [])

    def test_quadrant_4_adversarial_passes(self):
        rec = sc.ViolationRecorder(seed=sc.DEFAULT_SEED)
        metrics = sc.run_quadrant_4_adversarial(rec, sc.DEFAULT_SEED)
        self.assertGreaterEqual(metrics["adversarial_checks_run"], 30)
        self.assertIsInstance(metrics["within_budget"], bool)
        self.assertEqual(rec.unexpected, [])

    def test_advisory_time_budget_overrun_is_metric_not_violation(self):
        rec = sc.ViolationRecorder(seed=sc.DEFAULT_SEED)
        metrics = sc.run_quadrant_4_adversarial(
            rec, sc.DEFAULT_SEED, budget_seconds=0.0
        )
        self.assertFalse(metrics["within_budget"])
        self.assertEqual(metrics["budget_seconds"], 0.0)
        self.assertEqual(rec.violations, [])
        self.assertEqual(rec.unexpected, [])

        report = sc.run_battery(
            seed=sc.DEFAULT_SEED,
            small_trials=1,
            pareto_trials=1,
            fuzz_trials=1,
            chain_random_states=0,
            advisory_budgets={"q4_adversarial": 0.0},
        )
        self.assertFalse(report["quadrant_4_adversarial"]["within_budget"])
        self.assertIn("q4_adversarial", report["summary"]["advisory_budget_overruns"])
        self.assertEqual(report["summary"]["total_violations"], 0)
        self.assertEqual(report["summary"]["unexpected_violations"], 0)
        self.assertTrue(report["summary"]["passed"])

    def test_violation_recorder_allowlist_and_reproducer_dump(self):
        st = CodeState((0, 1), (Row("a1", "X", (0, 1)),), frozenset({"a1"}))
        allow = {
            "known-demo-id": {"issue": "#999", "description": "tracked demo violation"}
        }
        rec = sc.ViolationRecorder(seed=12345, known_violations=allow)
        rec.record(
            "known-demo-id",
            "q3_invariant_fuzzing",
            "demo_check",
            "expected tracked violation",
            state=st,
            move_sequence=[{"op": "C-SKIP"}],
        )
        rec.record(
            "unexpected-demo-id",
            "q3_invariant_fuzzing",
            "demo_check",
            "unexpected violation",
            state=st,
            move_sequence=[{"op": "C-DELETE-CHECK", "row_id": "a1"}],
        )
        self.assertEqual(len(rec.known), 1)
        self.assertEqual(rec.known[0]["known_issue"], "#999")
        self.assertEqual(len(rec.unexpected), 1)
        dump = rec.unexpected[0]
        self.assertEqual(dump["seed"], 12345)
        self.assertEqual(dump["state"]["Q"], [0, 1])
        self.assertEqual(dump["state"]["used"], ["a1"])
        self.assertEqual(
            dump["move_sequence"], [{"op": "C-DELETE-CHECK", "row_id": "a1"}]
        )

    def test_quadrant_2_classification_and_offline_gate_plumbing(self):
        # Direct unit checks of _classify_gate_report across all outcomes.
        c_earned = sc._classify_gate_report(
            "prune", 3, _synthetic_gate_report(earned_d=2)
        )
        self.assertEqual(c_earned["outcome"], "prune_confirmed")
        self.assertEqual(c_earned["failed_struct"], [])

        c_refuted = sc._classify_gate_report(
            "prune", 3, _synthetic_gate_report(earned_d=3, refuted_weight=2)
        )
        self.assertEqual(c_refuted["outcome"], "prune_confirmed")
        self.assertEqual(c_refuted["refuted_w"], 2)

        c_contra = sc._classify_gate_report(
            "prune", 3, _synthetic_gate_report(earned_d=3)
        )
        self.assertEqual(c_contra["outcome"], "prune_contradicted")

        c_struct_fail = sc._classify_gate_report(
            "prune",
            3,
            _synthetic_gate_report(earned_d=2, failed_structural=("css_commutation",)),
        )
        self.assertEqual(c_struct_fail["outcome"], "prune_contradicted")
        self.assertEqual(c_struct_fail["failed_struct"], ["css_commutation"])

        c_rem_ref = sc._classify_gate_report(
            "re-measure", 4, _synthetic_gate_report(earned_d=4, refuted_weight=3)
        )
        self.assertEqual(c_rem_ref["outcome"], "remeasure_refuted_below_target")

        c_rem_ok = sc._classify_gate_report(
            "re-measure", 4, _synthetic_gate_report(earned_d=4)
        )
        self.assertEqual(c_rem_ok["outcome"], "remeasure_unrefuted")

        # End-to-end offline Q2 run against a synthetic verifier using fixture 10-2-3-b.
        with tempfile.TemporaryDirectory(prefix="stress-q2-offline-") as tmp:
            root = Path(tmp)
            codes = root / "codes"
            codes.mkdir()
            shutil.copy(FIXTURE_10_2_3, codes / "10-2-3-b.json")

            def confirm_verifier(_root, doc, _tmp_dir, label):
                d_val = doc["distance"]["d"]
                return {
                    "returncode": 0,
                    "report": _synthetic_gate_report(earned_d=d_val, ok=True),
                }

            rec_ok = sc.ViolationRecorder(seed=sc.DEFAULT_SEED)
            q2_ok = sc.run_quadrant_2_gate_differential(
                rec_ok,
                sc.DEFAULT_SEED,
                root,
                max_verify_per_parent=2,
                parents=("10-2-3-b.json",),
                verifier_fn=confirm_verifier,
                run_certify_check=True,
            )
            self.assertEqual(q2_ok["parents_tested"], 1)
            self.assertEqual(len(q2_ok["per_parent"]), 1)
            self.assertEqual(q2_ok["gate_exported_checked"], 2)
            self.assertEqual(q2_ok["prune_precision"], 1.0)
            self.assertEqual(q2_ok["certify_checked"], 1)
            self.assertEqual(q2_ok["certify_contradicted"], 0)
            self.assertIsInstance(q2_ok["within_budget"], bool)
            self.assertEqual(rec_ok.unexpected, [])

            def contradict_verifier(_root, _doc, _tmp_dir, _label):
                return {
                    "returncode": 0,
                    "report": _synthetic_gate_report(earned_d=99, ok=True),
                }

            rec_bad = sc.ViolationRecorder(seed=sc.DEFAULT_SEED)
            q2_bad = sc.run_quadrant_2_gate_differential(
                rec_bad,
                sc.DEFAULT_SEED,
                root,
                max_verify_per_parent=1,
                parents=("10-2-3-b.json",),
                verifier_fn=contradict_verifier,
                run_certify_check=False,
            )
            self.assertEqual(q2_bad["prune_contradicted_by_gate"], 1)
            self.assertEqual(q2_bad["prune_precision"], 0.0)
            self.assertTrue(
                any(
                    v["check"] == "gate_prune_precision" for v in rec_bad.unexpected
                )
            )

    def test_scale_ladder_offline_plumbing_and_range_check(self):
        with tempfile.TemporaryDirectory(prefix="stress-scale-offline-") as tmp:
            root = Path(tmp)
            codes = root / "codes"
            codes.mkdir()
            shutil.copy(FIXTURE_10_2_3, codes / "10-2-3-b.json")

            rec_ok = sc.ViolationRecorder(seed=sc.DEFAULT_SEED)
            metrics = sc.run_scale_ladder(
                rec_ok,
                sc.DEFAULT_SEED,
                root,
                support_budget=16,
                support_max_weight=2,
                sector_budget=4,
                children_search_cap=1,
                parents=("10-2-3-b.json",),
                enforce_n_range=False,
            )
            self.assertEqual(metrics["parents_tested"], 1)
            self.assertFalse(metrics["oracle_invoked"])
            self.assertGreater(metrics["total_candidates_checked"], 0)
            self.assertEqual(len(metrics["per_parent"]), 1)
            self.assertIn("elapsed_seconds", metrics["per_parent"][0])
            self.assertIsInstance(metrics["within_budget"], bool)
            self.assertEqual(rec_ok.unexpected, [])

            rec_range = sc.ViolationRecorder(seed=sc.DEFAULT_SEED)
            sc.run_scale_ladder(
                rec_range,
                sc.DEFAULT_SEED,
                root,
                support_budget=8,
                support_max_weight=1,
                sector_budget=2,
                children_search_cap=0,
                parents=("10-2-3-b.json",),
                enforce_n_range=True,
            )
            self.assertTrue(
                any(
                    v["violation_id"] == "scale-parent-n-out-of-range-10-2-3-b.json"
                    for v in rec_range.unexpected
                )
            )

    def test_cli_ci_offline_writes_report_and_exits_zero(self):
        with tempfile.TemporaryDirectory(prefix="stress-cli-test-") as tmp:
            out = Path(tmp) / "report.json"
            rc = sc.main(["--ci", "--output", str(out)])
            self.assertEqual(rc, 0)
            data = json.loads(out.read_text())
            self.assertTrue(data["summary"]["passed"])
            self.assertEqual(data["summary"]["unexpected_violations"], 0)
            self.assertIsInstance(data["summary"]["advisory_budget_overruns"], list)
            self.assertIsInstance(data["import_hygiene"]["within_budget"], bool)
            self.assertIsInstance(
                data["quadrant_1_oracle_differential"]["within_budget"], bool
            )
            self.assertIsInstance(
                data["quadrant_3_invariant_fuzzing"]["within_budget"], bool
            )
            self.assertIsInstance(data["quadrant_4_adversarial"]["within_budget"], bool)
            self.assertTrue(data["quadrant_2_gate_differential"]["skipped"])
            self.assertTrue(data["scale_ladder"]["skipped"])

    def test_committed_baseline_report_is_valid_json_and_clean(self):
        baseline = (
            Path(__file__).resolve().parent
            / "experiments"
            / "stress_campaign_report.json"
        )
        self.assertTrue(baseline.exists(), "committed baseline report must exist")
        data = json.loads(baseline.read_text())
        self.assertEqual(data["schema"], "stress_campaign.v1")
        self.assertEqual(data["qldpc_commit"], sc.Q_LDPC_SHA)
        self.assertTrue(data["summary"]["passed"])
        self.assertEqual(data["summary"]["unexpected_violations"], 0)
        self.assertIsInstance(data["summary"]["advisory_budget_overruns"], list)
        self.assertEqual(
            data["quadrant_1_oracle_differential"]["admitted_constructors_covered"],
            len(ADMITTED_CONSTRUCTORS),
        )
        q2 = data["quadrant_2_gate_differential"]
        self.assertFalse(q2.get("skipped", False))
        self.assertEqual(q2["parents_tested"], 5)
        self.assertEqual(len(q2["per_parent"]), 5)
        self.assertEqual(q2["prune_precision"], 1.0)
        self.assertIsInstance(q2["remeasure_rate"], (int, float))
        self.assertGreater(q2["gate_exported_checked"], 0)
        self.assertIsInstance(q2["within_budget"], bool)

        scale = data["scale_ladder"]
        self.assertFalse(scale.get("skipped", False))
        self.assertEqual(scale["parents_tested"], 5)
        self.assertEqual(len(scale["per_parent"]), 5)
        self.assertFalse(scale["oracle_invoked"])
        self.assertIsInstance(scale["within_budget"], bool)
        for entry in scale["per_parent"]:
            self.assertIsInstance(entry["elapsed_seconds"], (int, float))
            self.assertGreaterEqual(entry["elapsed_seconds"], 0.0)


if __name__ == "__main__":
    unittest.main()
