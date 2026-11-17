"""Factor witnesses through the `E-GLUE` seam (issue #332, unblocked half).

The glued code is the direct sum with seam checks added, so a factor's
witness is a candidate upper bound in the child and nothing more: an X seam
check can anticommute with a factor's Z witness, and a seam row can pull a
factor witness into the glued span. `DistanceLedger.glue` carries both
factors' witnesses into the child and keeps those that revalidate there
(`spec/JUDGMENT_LAYER.md` §2c), which is the instance-wise reading of the
seam equality recorded in `spec/OPERATIONAL_SEMANTICS.md` §4.31: a surviving
minimum-weight Z witness closes the Z interval without the certificate's
claim, and the X and full upper endpoints, which the certificate never
licenses, come from surviving factor witnesses.
"""

import unittest

from machine.priced_calculus import (
    CodeState,
    DistanceLedger,
    Interval,
    Row,
    apply_operation,
    validate_witness,
)

CERTIFICATE = {"move_words": ["UD", "UD"], "evidence": "test seam"}


def factor(labels, row_id):
    """A two-qubit factor with one Z row on both qubits: k = 1, d_X = 2, d_Z = 1."""
    a, b = labels
    state = CodeState((a, b), (Row(row_id, "Z", (a, b)),), frozenset((row_id,)))
    state.validate()
    return state


def ledger_for(state, z_upper=1):
    """The factor's exact ledger with its two minimum-weight witnesses."""
    a, b = state.Q
    ledger = DistanceLedger(Interval(1, 1), {"X": Interval(2, 2), "Z": Interval(1, z_upper)})
    ledger.record_witness(state, "X", (a, b), source="factor X witness")
    ledger.record_witness(state, "Z", (a,), source="factor Z witness")
    return ledger


class GlueWitnessTransportTests(unittest.TestCase):
    def setUp(self):
        self.left = factor((0, 1), "b1")
        self.right = factor((2, 3), "b2")

    def glue(self, seam, z_upper=1):
        left_ledger = ledger_for(self.left, z_upper)
        right_ledger = ledger_for(self.right, z_upper)
        operation = {"op": "E-GLUE", "right_state": self.right,
                     "seam_checks": [seam], "seam_certificate": CERTIFICATE}
        child = apply_operation(self.left, operation)
        operation["right_ledger"] = right_ledger
        return child, left_ledger.propagate(operation, child)

    def test_an_x_seam_keeps_the_x_witnesses_and_drops_the_z_witnesses(self):
        child, ledger = self.glue(("X", [0, 1, 2, 3]))
        self.assertEqual(sorted(w["support"] for w in ledger.witnesses["X"]),
                         [[0, 1], [2, 3]])
        self.assertEqual(ledger.witnesses["Z"], [])
        for witness in ledger.witnesses["X"]:
            validate_witness(child, "X", tuple(witness["support"]), witness["value"])
            self.assertEqual(witness["source"],
                             "factor witness revalidated in the glued child")
        # The X upper endpoint, which the certificate never licenses, comes
        # from the surviving factor witnesses; the Z upper is the certificate's.
        self.assertEqual(ledger.sector["X"], Interval(2, 2))
        self.assertEqual(ledger.sector["Z"], Interval(1, 1))
        self.assertEqual(ledger.full, Interval(1, 1))

    def test_a_z_seam_keeps_the_z_witnesses_and_drops_the_x_witnesses(self):
        child, ledger = self.glue(("Z", [1, 2]))
        self.assertEqual(sorted(w["support"] for w in ledger.witnesses["Z"]), [[0], [2]])
        self.assertEqual(ledger.witnesses["X"], [])
        for witness in ledger.witnesses["Z"]:
            validate_witness(child, "Z", tuple(witness["support"]), witness["value"])
        self.assertEqual(ledger.sector["X"], Interval(2, None))
        self.assertEqual(ledger.sector["Z"], Interval(1, 1))

    def test_a_surviving_minimum_z_witness_closes_the_z_interval_without_the_claim(self):
        # Both factors carry Z interval [1, +inf) and a weight-1 Z witness, so
        # the certificate's min of the Z upper endpoints is +inf and licenses
        # nothing. The lower bound min(1, 1) = 1 is sound by §4.31, the
        # witness {0} is still a Z logical of the glued child, and the two
        # together give d_Z = 1 for this instance: the instance-wise equality.
        child, ledger = self.glue(("Z", [1, 2]), z_upper=None)
        self.assertEqual(ledger.sector["Z"], Interval(1, 1))
        self.assertEqual(ledger.full, Interval(1, 1))
        self.assertIn([0], [w["support"] for w in ledger.witnesses["Z"]])
        validate_witness(child, "Z", (0,), 1)

    def test_without_a_child_state_no_witness_is_carried(self):
        left_ledger = ledger_for(self.left)
        right_ledger = ledger_for(self.right)
        merged = left_ledger.glue(right_ledger, seam_certificate=CERTIFICATE)
        self.assertEqual(merged.witnesses, {"X": [], "Z": []})
        self.assertEqual(merged.sector["X"], Interval(2, None))
        self.assertEqual(merged.full, Interval(1, 1))

    def test_a_seam_row_equal_to_a_factor_witness_absorbs_it(self):
        # A seam Z check on {0} alone is admissible (it commutes with every X
        # row, there are none, and lies outside the Z span). It becomes a
        # glued row, so the factor's Z witness {0} is now a stabilizer and is
        # dropped, while the other factor's Z witness {2} survives. Of the X
        # witnesses, {0, 1} meets the new Z row {0} in one qubit and is
        # dropped; {2, 3} is disjoint from it and survives.
        child, ledger = self.glue(("Z", [0]))
        self.assertEqual([w["support"] for w in ledger.witnesses["Z"]], [[2]])
        self.assertEqual([w["support"] for w in ledger.witnesses["X"]], [[2, 3]])
        validate_witness(child, "X", (2, 3), 2)
        self.assertEqual(ledger.sector["Z"], Interval(1, 1))
        self.assertEqual(ledger.sector["X"], Interval(2, 2))

if __name__ == "__main__":
    unittest.main()
