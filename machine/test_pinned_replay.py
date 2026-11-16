"""Pinned-replay snapshot check."""

import hashlib
import os
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))

PINNED_SHA256 = "5078db2ff2a447b9a0f4ea387b8ab28bae0be804daaff1bee75b0a8fc8b275e3"
REPLAY_PATH = os.path.join(HERE, "experiments", "challenge_replay.json")


class PinnedReplayTests(unittest.TestCase):
    def test_pinned_replay_hash_unchanged(self):
        with open(REPLAY_PATH, "rb") as f:
            actual = hashlib.sha256(f.read()).hexdigest()
        if actual != PINNED_SHA256:
            raise AssertionError(
                "the pinned report changed and requires an explicit, disjoint  to re-pin: "
                "expected %s, got %s" % (PINNED_SHA256, actual)
            )


if __name__ == "__main__":
    unittest.main()
