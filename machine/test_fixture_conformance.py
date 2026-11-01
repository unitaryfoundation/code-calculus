"""Conformance entry point for the MVP fixture evaluator (TODO item 2)."""

import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import fixture_conformance


class FixtureConformanceTests(unittest.TestCase):
    def test_all_fixtures_pass(self):
        data = fixture_conformance._load_fixtures()
        by_id = {f["id"]: f for f in data["fixtures"]}
        cache = {}
        mismatches = 0
        for f in data["fixtures"]:
            r = fixture_conformance.evaluate_fixture(f, by_id, cache)
            if r["mismatches"]:
                mismatches += 1
                self.fail("%s: %s" % (r["id"], r["mismatches"]))
        self.assertEqual(mismatches, 0)

    def test_refusal_probes_are_supplementary_and_execute(self):
        # : the four refusal probes exist, stay off the acceptance
        # surface, and carry the guard each was minted for; the W0-W16
        # acceptance surface keeps acceptance_surface: true throughout.
        data = fixture_conformance._load_fixtures()
        by_id = {f["id"]: f for f in data["fixtures"]}
        for fid in ("W25", "W26", "W27", "W28"):
            self.assertIn(fid, by_id)
            self.assertIs(by_id[fid]["acceptance_surface"], False, fid)
        for index in range(17):
            fid = "W%d" % index
            self.assertIn(fid, by_id)
            self.assertIs(by_id[fid]["acceptance_surface"], True, fid)
        # each probe names a distinct guard
        self.assertEqual(by_id["W25"]["category"], "certificate-inherit-inapplicable")
        self.assertEqual(by_id["W26"]["category"], "direct-sum-inapplicable")
        self.assertEqual(by_id["W27"]["category"], "state-malformed")
        self.assertEqual(by_id["W28"]["category"], "state-malformed")
        # the stale-certificate probe is transcribed with its three premises
        expected = by_id["W25"]["expected"]
        self.assertEqual(expected["certificate"], {"sector": "X", "bound": 3})
        for key in ("premise_certificate_checker_accepts",
                    "premise_certificate_state_matches_current",
                    "premise_inherited_claim_would_be_false"):
            self.assertIn(key, expected)
        # and each probe executes to its recorded outcome
        for fid in ("W25", "W26", "W27", "W28"):
            r = fixture_conformance.evaluate_fixture(by_id[fid], by_id, {})
            self.assertEqual(r["mismatches"], [], fid)
            self.assertEqual(r["actual_outcome"],
                             by_id[fid]["expected"]["outcome"], fid)


if __name__ == "__main__":
    unittest.main()