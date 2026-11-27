"""Coverage link between Lean pinned fixtures and Python fixtures."""

import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import lean_fixture_coverage as lfc


class LeanFixtureCoverageTests(unittest.TestCase):
    def test_coverage_report_runs(self):
        r = lfc.coverage_report()
        self.assertGreaterEqual(r["python_fixtures"], 1)
        self.assertGreaterEqual(r["lean_state_defs"], 1)
        self.assertGreaterEqual(r["lean_covered_fixtures"], 1)
        self.assertEqual(r["missing_theorems"], [])
        self.assertGreaterEqual(r["mismatch_count"], 0)

    def test_every_lean_def_has_well_formedness_theorem(self):
        r = lfc.coverage_report()
        self.assertEqual(r["missing_theorems"], [])

    def test_uncovered_fixtures_are_subset_of_python(self):
        r = lfc.coverage_report()
        with open(os.path.join(HERE, "fixtures", "mvp_fixtures.json")) as f:
            import json
            ids = {fx["id"] for fx in json.load(f)["fixtures"]}
        for fid in r["lean_uncovered_fixtures"]:
            self.assertIn(fid, ids)

    def test_the_one_uncovered_fixture_is_w24(self):
        # Every fixture except W24 is transcribed (direct-sum pair fixtures
        # W14, W15, W21, W26 through their per-summand defs). W24 is a
        # 119-qubit, 85-row state whose `inSpanRowsBool` independence check
        # would enumerate 2^45 coefficient vectors, so it needs a
        # bitmask-based independence test before it can be replayed. The
        # supplementary probes W25 to W29 are transcribed since issue #529.
        r = lfc.coverage_report()
        self.assertEqual(r["lean_uncovered_fixtures"], ["W24"])

    def test_transcribed_states_match_the_json(self):
        # The Lean states are hand-typed. This reads them as text and
        # compares Q, the rows as a set, and `used` with the JSON state each
        # one names, under the identifier ranks a1 = 0, b1 = 10000,
        # p1 = 50000, q1 = 60000.
        t = lfc.transcription_report()
        self.assertEqual(t["mismatched"], [])
        for name in ("fixture_W25_initial", "fixture_W26_S_L",
                     "fixture_W26_S_R_shared", "fixture_W27_initial",
                     "fixture_W28_initial", "fixture_W29_initial",
                     "fixture_W29_result"):
            self.assertIn(name, t["matched"])

    def test_states_not_compared_are_pinned(self):
        # A state is not compared when the JSON omits part of it or names an
        # identifier outside the convention. The set is pinned so that a new
        # transcription cannot fall out of the comparison unnoticed.
        t = lfc.transcription_report()
        self.assertEqual(sorted(t["not_compared"]), [
            "fixture_W14_result", "fixture_W15_S_R_prime", "fixture_W16_result",
            "fixture_W25_result", "fixture_W2_initial", "fixture_W5_result",
            "fixture_W7_result", "fixture_W9_result"])

    def test_transcription_check_detects_a_changed_state(self):
        import tempfile
        with open(lfc.LEAN_FIXTURES) as f:
            text = f.read()
        marker = "def fixture_W27_initial : CodeState := {\n  Q := [1, 2, 3],"
        self.assertIn(marker, text)
        with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as tmp:
            tmp.write(text.replace(marker, marker.replace("[1, 2, 3]", "[1, 2, 4]")))
        saved = lfc.LEAN_FIXTURES
        try:
            lfc.LEAN_FIXTURES = tmp.name
            self.assertEqual(lfc.transcription_report()["mismatched"],
                             ["fixture_W27_initial"])
        finally:
            lfc.LEAN_FIXTURES = saved
            os.unlink(tmp.name)

    def test_probe_replays_are_present(self):
        root = os.path.dirname(HERE)
        def source(name):
            with open(os.path.join(root, "lean", "CodeCalculus", name)) as f:
                return f.read()
        replay = source("FixtureReplay.lean")
        for theorem in ("fixture_W26_no_evalExpr", "fixture_W26_used_ne",
                        "fixture_W27_initial_wellFormed",
                        "fixture_W28_initial_wellFormed"):
            self.assertIn("theorem %s" % theorem, replay)
        for line in ("wellFormedBool fixture_W27_initial = false",
                     "wellFormedBool fixture_W28_initial = false"):
            self.assertIn(line, replay)
        eval_replay = source("FixtureEvalReplay.lean")
        for theorem in ("fixture_W25_eval", "fixture_W29_eval",
                        "fixture_W27_initial_not_wf", "fixture_W28_initial_not_wf"):
            self.assertIn("theorem %s" % theorem, eval_replay)
        for theorem in ("fixture_W25_certificate_accepted",
                        "fixture_W25_certificate_rejected_on_child",
                        "fixture_W25_child_distance"):
            self.assertIn("theorem %s" % theorem, eval_replay)

    def test_pair_fixtures_recognised(self):
        # The direct-sum scenario fixtures whose initial state is a named pair
        # of summands; coverage for these requires every summand def.
        r = lfc.coverage_report()
        self.assertEqual(r["pair_fixtures"], {
            "W14": ["S_L", "S_R"],
            "W15": ["S_L", "S_R_prime"],
            "W21": ["S_L", "S_R_double_prime"],
            "W26": ["S_L", "S_R_shared"],
        })


if __name__ == "__main__":
    unittest.main()
