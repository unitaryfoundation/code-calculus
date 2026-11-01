"""Coverage link between Lean pinned fixtures and Python fixtures ()."""

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

    def test_uncovered_fixtures_are_w24_and_the_new_probes(self):
        # Every fixture except W24 is transcribed (direct-sum pair fixtures
        # W14, W15, W21 through their per-summand defs). W24 is a 119-qubit,
        # 85-row state whose `inSpanRowsBool` independence check would
        # enumerate 2^45 coefficient vectors, so it needs a bitmask-based
        # independence test before it can be replayed. W25-W28 are the
        # supplementary refusal probes of : they are Python-side
        # probes and are deliberately not transcribed into Lean (transcribing
        # them is not owed by this ).
        r = lfc.coverage_report()
        self.assertEqual(r["lean_uncovered_fixtures"],
                         ["W24", "W25", "W26", "W27", "W28"])

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
