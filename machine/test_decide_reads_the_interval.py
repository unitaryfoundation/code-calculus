"""The decision rule reads the interval only (spec/JUDGMENT_LAYER.md 2b).

Issue #632: ``decide`` returned ``re-measure`` in place of ``prune`` unless
some carried witness was labeled ``deep``, and every unlabeled witness was
given that label by default, so the default decided the verdict.
"""

import unittest

from machine.intervals import DistanceLedger, Interval, WITNESS_CONFIDENCE_LABELS
from machine.state import CodeState, Malformed, Row


def _state():
    # One X row and one Z row on {0, 1}; qubit 2 is free, so [2] is a
    # weight-1 logical in both sectors.
    return CodeState(
        (0, 1, 2),
        (Row("a9001", "X", (0, 1)), Row("b9001", "Z", (0, 1))),
        frozenset(("a9001", "b9001")),
    )


def _ledger(upper, witnesses=None):
    return DistanceLedger(
        Interval(0, upper),
        {"X": Interval(0, upper), "Z": Interval(0, upper)},
        witnesses,
    )


class DecideReadsTheInterval(unittest.TestCase):
    def test_prune_needs_no_witness(self):
        self.assertEqual(_ledger(2).decide(3), "prune")

    def test_prune_with_a_screened_witness(self):
        witness = {"support": [2], "value": 1, "source": "bounded search",
                   "confidence": "screened"}
        ledger = _ledger(1, {"X": [witness]})
        self.assertFalse(ledger.has_deep_witness())
        self.assertEqual(ledger.decide(2), "prune")

    def test_verdict_is_the_same_with_and_without_a_deep_label(self):
        for target in (1, 2, 3, 4):
            verdicts = set()
            for label in (None, "screened", "deep"):
                witness = {"support": [2], "value": 1, "source": "s"}
                if label is not None:
                    witness["confidence"] = label
                verdicts.add(_ledger(2, {"Z": [witness]}).decide(target))
            self.assertEqual(len(verdicts), 1, target)

    def test_the_three_verdicts(self):
        ledger = DistanceLedger(
            Interval(2, 4), {"X": Interval(2, 4), "Z": Interval(2, 4)})
        self.assertEqual(ledger.decide(2), "certify")
        self.assertEqual(ledger.decide(3), "re-measure")
        self.assertEqual(ledger.decide(4), "re-measure")
        self.assertEqual(ledger.decide(5), "prune")
        unbounded = DistanceLedger(
            Interval(0, None), {"X": Interval(0, None), "Z": Interval(0, None)})
        self.assertEqual(unbounded.decide(5), "re-measure")


class NoInventedConfidence(unittest.TestCase):
    def test_ledger_adds_no_label(self):
        ledger = _ledger(1, {"X": [{"support": [2], "value": 1, "source": "s"}]})
        self.assertNotIn("confidence", ledger.witnesses["X"][0])
        self.assertFalse(ledger.has_deep_witness())

    def test_constructed_witness_is_unlabeled_unless_labeled(self):
        ledger = DistanceLedger.for_constructed(
            _state(),
            witnesses={"X": [[2]],
                       "Z": [{"support": [2], "confidence": "screened"}]})
        self.assertNotIn("confidence", ledger.witnesses["X"][0])
        self.assertEqual(ledger.witnesses["Z"][0]["confidence"], "screened")
        self.assertEqual(ledger.full, Interval(0, 1))
        self.assertEqual(ledger.decide(2), "prune")

    def test_recorded_witness_is_unlabeled_unless_labeled(self):
        ledger = _ledger(3)
        ledger.record_witness(_state(), "X", [2])
        ledger.record_witness(_state(), "Z", [2], confidence="deep")
        self.assertNotIn("confidence", ledger.witnesses["X"][0])
        self.assertEqual(ledger.witnesses["Z"][0]["confidence"], "deep")
        self.assertTrue(ledger.has_deep_witness())

    def test_challenge_witness_is_unlabeled(self):
        document = {
            "n": 3,
            "checks": {"X": [[0, 1]], "Z": [[0, 1]]},
            "k": 1,
            "distance": {
                "X": {"witness": [2], "value": 1},
                "Z": {"witness": [2], "value": 1},
            },
        }
        state = CodeState.from_challenge(document)
        ledger = DistanceLedger.from_challenge(state, document)
        for side in ("X", "Z"):
            self.assertNotIn("confidence", ledger.witnesses[side][0])
        self.assertEqual(ledger.decide(2), "prune")

    def test_unknown_labels_are_refused(self):
        self.assertEqual(WITNESS_CONFIDENCE_LABELS, ("deep", "screened"))
        with self.assertRaises(Malformed):
            DistanceLedger.for_constructed(
                _state(), witnesses={"X": [{"support": [2], "confidence": "sure"}]})
        with self.assertRaises(Malformed):
            _ledger(3).record_witness(_state(), "X", [2], confidence=True)

    def test_label_survives_a_copy_and_a_transport(self):
        witness = {"support": [2], "value": 1, "source": "s",
                   "confidence": "screened"}
        ledger = _ledger(1, {"X": [witness, {"support": [2], "value": 1}]})
        copied = ledger.copy()
        self.assertEqual(copied.witnesses["X"][0]["confidence"], "screened")
        kept = ledger._valid_witnesses(_state(), "X")
        self.assertEqual(len(kept), 1)
        self.assertEqual(kept[0]["confidence"], "screened")


if __name__ == "__main__":
    unittest.main()
