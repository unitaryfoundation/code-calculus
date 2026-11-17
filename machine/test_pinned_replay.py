"""Pinned-replay snapshot check (issue #125 deliverable 3)."""

import hashlib
import os
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))

PINNED_SHA256 = "51288be516ebe71acc544cc9b689b2618e1442b9337d9fbcd044a82c8b84517a"
REPLAY_PATH = os.path.join(HERE, "experiments", "issue21_challenge_replay.json")


class PinnedReplayTests(unittest.TestCase):
    def test_pinned_replay_hash_unchanged(self):
        with open(REPLAY_PATH, "rb") as f:
            actual = hashlib.sha256(f.read()).hexdigest()
        if actual != PINNED_SHA256:
            raise AssertionError(
                "the pinned report changed and requires an explicit, disjoint PR to re-pin: "
                "expected %s, got %s" % (PINNED_SHA256, actual)
            )


if __name__ == "__main__":
    unittest.main()
