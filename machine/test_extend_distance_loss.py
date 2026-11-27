"""The E-EXTEND distance-loss conditional cell (issue #677;
spec/JUDGMENT_LAYER.md section 2b, spec/OPERATIONAL_SEMANTICS.md section 4.30, *Distance-loss cell*).

With a nonempty added qubit set Delta, E-EXTEND resets every lower distance
endpoint to zero. A supplied, sourced loss ell_tau licenses
d'_tau >= max(0, L_tau - ell_tau). The consumer checks the input shape only;
these tests check the bookkeeping against the small-n exact oracle, which is
evidence about the transcription, never a check of a supplied loss.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from machine.oracle import exact_distances  # noqa: E402
from machine.priced_calculus import (  # noqa: E402
    CodeState,
    DistanceLedger,
    Interval,
    NoDerivation,
    Row,
)


def repetition_parent():
    """Q = {0, 1, 2}; Z rows {0,1}, {1,2}: (d_X, d_Z) = (3, 1), k = 1."""
    return CodeState((0, 1, 2), (Row("a1", "Z", (0, 1)), Row("a2", "Z", (1, 2))),
                     frozenset({"a1", "a2"}))


def exact_ledger(state):
    ex = exact_distances(state)
    return DistanceLedger(Interval(ex["d"], ex["d"]),
                          {"X": Interval(ex["X"], ex["X"]),
                           "Z": Interval(ex["Z"], ex["Z"])}, witnesses={})


EXTEND = {"op": "E-EXTEND", "new_qubits": (3,), "additions": []}


class ExtendDistanceLossTests(unittest.TestCase):
    def setUp(self):
        self.parent = repetition_parent()
        self.child = self.parent.extend_code((3,), [])
        self.ex_child = exact_distances(self.child)

    def propagate(self, hypothesis=None, observations=None, operation=EXTEND):
        return exact_ledger(self.parent).propagate(
            operation, self.child if operation is EXTEND else self.parent,
            hypothesis=hypothesis, observations=observations,
            parent_state=self.parent)

    def test_unpriced_lower_endpoints_reset(self):
        out = self.propagate()
        self.assertEqual(out.sector["X"].lower, 0)
        self.assertEqual(out.sector["Z"].lower, 0)
        self.assertEqual(out.full.lower, 0)

    def test_exact_loss_gives_a_sound_lower_endpoint(self):
        # The free qubit 3 brings the weight-1 logical X_3: d_X drops 3 -> 1.
        self.assertEqual((self.ex_child["X"], self.ex_child["Z"]), (1, 1))
        out = self.propagate({"extend_distance_loss": {
            "loss_X": 2, "loss_Z": 0, "evidence": "test oracle"}})
        self.assertEqual(out.sector["X"].lower, 1)
        self.assertEqual(out.sector["Z"].lower, 1)
        self.assertEqual(out.full.lower, 1)
        for side in ("X", "Z"):
            iv = out.sector[side]
            self.assertTrue(iv.lower <= self.ex_child[side]
                            and (iv.upper is None or self.ex_child[side] <= iv.upper))
        self.assertTrue(any(c["cell"] == "E-EXTEND distance loss"
                            and c["status"] == "conditional" for c in out.conditions))

    def test_one_sector_loss_leaves_the_other_and_full_at_zero(self):
        out = self.propagate({"extend_distance_loss": {"loss_X": 2, "evidence": "src"}})
        self.assertEqual(out.sector["X"].lower, 1)
        self.assertEqual(out.sector["Z"].lower, 0)
        self.assertEqual(out.full.lower, 0)

    def test_loss_larger_than_the_lower_endpoint_floors_at_zero(self):
        out = self.propagate({"extend_distance_loss": {"loss_X": 7, "evidence": "src"}})
        self.assertEqual(out.sector["X"].lower, 0)

    def test_a_false_loss_contradicted_by_a_witness_is_refused(self):
        # loss_X = 0 claims d'_X >= 3; the child witness X_3 has weight 1.
        with self.assertRaises(NoDerivation):
            self.propagate({"extend_distance_loss": {"loss_X": 0, "evidence": "wrong"}},
                           observations={"X": [3]})

    def test_malformed_inputs_are_refused(self):
        bad = [
            "not an object",
            {"loss_X": 1},
            {"loss_X": 1, "evidence": "  "},
            {"evidence": "src"},
            {"loss_X": -1, "evidence": "src"},
            {"loss_X": True, "evidence": "src"},
            {"loss_Z": 1.5, "evidence": "src"},
        ]
        for value in bad:
            with self.subTest(value=value), self.assertRaises(NoDerivation):
                self.propagate({"extend_distance_loss": value})

    def test_refused_when_delta_is_empty(self):
        operation = {"op": "E-EXTEND", "new_qubits": (), "additions": []}
        with self.assertRaises(NoDerivation):
            self.propagate({"extend_distance_loss": {"loss_X": 0, "evidence": "src"}},
                           operation=operation)

    def test_refused_without_a_parent_sector_distance(self):
        # A k = 0 parent has no distance to lose from.
        parent = CodeState((0, 1), (Row("a1", "Z", (0, 1)), Row("a2", "X", (0, 1))),
                           frozenset({"a1", "a2"}))
        ledger = DistanceLedger(Interval(None, None),
                                {"X": Interval(None, None), "Z": Interval(None, None)},
                                witnesses={})
        child = parent.extend_code((2,), [])
        with self.assertRaises(NoDerivation):
            ledger.propagate(EXTEND | {"new_qubits": (2,)}, child,
                             hypothesis={"extend_distance_loss": {"loss_X": 0,
                                                                  "evidence": "src"}},
                             parent_state=parent)


if __name__ == "__main__":
    unittest.main()
