import unittest

from machine.experiments.issue21_challenge_replay import (
    exact_distance_decision_gap,
)


class TestExactDistanceDecisionGap(unittest.TestCase):
    def test_exact_distance_settles_the_verdict(self):
        gap = exact_distance_decision_gap(4, "prune", 3, "stated distance")
        self.assertEqual(gap["settled_verdict"], "prune")
        self.assertTrue(gap["agrees"])
        self.assertEqual(gap["target"], 4)
        self.assertEqual(gap["consumer_verdict"], "prune")
        self.assertEqual(gap["exact_distance"], 3)
        self.assertEqual(gap["exact_distance_source"], "stated distance")

    def test_certify_when_exact_distance_meets_target(self):
        gap = exact_distance_decision_gap(3, "certify", 3, "enumeration")
        self.assertEqual(gap["settled_verdict"], "certify")
        self.assertTrue(gap["agrees"])

    def test_disagreement_is_reported_not_hidden(self):
        gap = exact_distance_decision_gap(4, "certify", 3, "enumeration")
        self.assertEqual(gap["settled_verdict"], "prune")
        self.assertFalse(gap["agrees"])

    def test_evidence_only_note_and_no_oracle_key(self):
        gap = exact_distance_decision_gap(4, "prune", 3, "enumeration")
        self.assertIn("does not validate the consumer path", gap["note"])
        self.assertNotIn("oracle", gap)

    def test_malformed_inputs(self):
        for target in (0, True, 1.5, "4"):
            with self.assertRaises(ValueError):
                exact_distance_decision_gap(target, "prune", 3, "source")
        for distance in (0, True, 1.5, "3"):
            with self.assertRaises(ValueError):
                exact_distance_decision_gap(4, "prune", distance, "source")


if __name__ == "__main__":
    unittest.main()
