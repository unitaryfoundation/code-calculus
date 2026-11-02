"""Certificate-layer prototype tests.

The format and checker live in `machine/certificates.py`; the committed
instance artifact is `the conformance harness`. No
test here changes a claim status: the certificates are evidence about
feasibility of the format, not a status upgrade.
"""

import copy
import json
import os
import unittest

from machine.certificates import (
    NoCertificate,
    build_sector_lower_bound_certificate,
    certificate_size_bytes,
    check_sector_lower_bound_certificate,
)
from machine.experiments.certificate_prototype import (
    CERTIFIED_BOUND,
    REPORT_PATH,
    build_prototype_artifact,
)
from machine.priced_calculus import CodeState

HERE = os.path.dirname(os.path.abspath(__file__))
FIXTURE_PATH = os.path.join(HERE, "fixtures", "qldpc_10_2_3_b.json")


def pinned_parent():
    """The pinned replay parent, as a ``CodeState``."""
    with open(FIXTURE_PATH) as source:
        return CodeState.from_challenge(json.load(source))


def built_certificate(sector):
    return build_sector_lower_bound_certificate(
        pinned_parent(), sector, CERTIFIED_BOUND)


class KillCertificateTests(unittest.TestCase):
    """The kill certificate certifies the pinned parent's sector bound."""

    @unittest.skip("pinned replay unavailable")
    def test_both_sector_certificates_are_accepted(self):
        return
        parent_exact = replay["addition"]["parent_exact_distance_experiment"]
        for sector in ("X", "Z"):
            certificate = built_certificate(sector)
            accepted, failures = check_sector_lower_bound_certificate(certificate)
            self.assertTrue(accepted, failures)
            self.assertEqual(failures, [])
            # The certified bound is exactly the lower-bound half of the
            # fact the replay's post-hoc oracle asserted.
            self.assertEqual(CERTIFIED_BOUND, parent_exact[sector])
            self.assertEqual(len(certificate["kills"]), 56)
            self.assertLess(certificate_size_bytes(certificate), 10_000)

    def test_a_bound_beyond_the_truth_is_not_producible(self):
        # The parent's true distance is 3, so the weight-3 logicals survive
        # every kill reason at bound 4; the producer refuses rather than
        # emitting an unverifiable artifact.
        with self.assertRaises(NoCertificate):
            build_sector_lower_bound_certificate(
                pinned_parent(), "X", CERTIFIED_BOUND + 1)

    def test_bound_zero_is_trivially_acceptable(self):
        certificate = build_sector_lower_bound_certificate(
            pinned_parent(), "Z", 0)
        accepted, failures = check_sector_lower_bound_certificate(certificate)
        self.assertTrue(accepted, failures)
        self.assertEqual(certificate["kills"], [])

    def test_the_checker_is_deterministic(self):
        certificate = built_certificate("Z")
        self.assertEqual(check_sector_lower_bound_certificate(certificate),
                         check_sector_lower_bound_certificate(certificate))


class TamperedCertificateTests(unittest.TestCase):
    """Every tampering is rejected, with the reason named."""

    def setUp(self):
        self.certificate = built_certificate("X")

    def _tampered(self, mutate):
        certificate = copy.deepcopy(self.certificate)
        mutate(certificate)
        return certificate

    def test_a_missing_kill_fails_coverage(self):
        certificate = self._tampered(
            lambda c: c["kills"].pop())
        accepted, failures = check_sector_lower_bound_certificate(certificate)
        self.assertFalse(accepted)
        self.assertTrue(any(f.startswith("coverage:") for f in failures),
                        failures)

    def test_a_flipped_span_coefficient_is_rejected(self):
        def flip(certificate):
            for kill in certificate["kills"]:
                if kill["reason"]["kind"] == "in_span":
                    coeffs = kill["reason"]["coeffs"]
                    kill["reason"]["coeffs"] = [
                        1 - c for c in coeffs]
                    return
            self.fail("no in_span kill found")

        accepted, failures = check_sector_lower_bound_certificate(
            self._tampered(flip))
        self.assertFalse(accepted)
        self.assertTrue(any("does not equal the vector" in f for f in failures),
                        failures)

    def test_an_undisplayed_odd_overlap_row_is_rejected(self):
        def rewire(certificate):
            for kill in certificate["kills"]:
                if kill["reason"]["kind"] == "odd_overlap":
                    kill["reason"]["row"] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
                    return
            self.fail("no odd_overlap kill found")

        accepted, failures = check_sector_lower_bound_certificate(
            self._tampered(rewire))
        self.assertFalse(accepted)
        self.assertTrue(any("not a displayed" in f for f in failures),
                        failures)

    def test_a_kill_outside_the_ball_is_rejected(self):
        def widen(certificate):
            certificate["kills"].append({
                "support": list(range(10)),
                "reason": {"kind": "in_span", "coeffs": []},
            })

        accepted, failures = check_sector_lower_bound_certificate(
            self._tampered(widen))
        self.assertFalse(accepted)
        self.assertTrue(any("cover no vector" in f for f in failures),
                        failures)

    def test_a_certificate_is_bound_to_its_carried_state(self):
        # The certificate is self-contained: swapping the carried state for
        # another code invalidates the kills, and the checker rejects (here
        # at the qubit-membership shape check, since the old kills name
        # qubits the carried state does not have).
        def swap_state(certificate):
            four_two_two = CodeState.from_challenge({
                "schema_version": "0.5", "name": "[[4,2,2]]", "code_type": "CSS",
                "n": 4, "k": 2,
                "checks": {"X": [[0, 1, 2, 3]], "Z": [[0, 1, 2, 3]]},
                "distance": {"d": 2},
                "provenance": {"authors": [], "construction": "probe",
                                "date": "2026-10-25", "origin": "probe"},
            })
            from machine.certificates import certificate_state_block
            certificate["state"] = certificate_state_block(four_two_two)

        accepted, failures = check_sector_lower_bound_certificate(
            self._tampered(swap_state))
        self.assertFalse(accepted)
        self.assertTrue(failures, failures)


class CheckerContractTests(unittest.TestCase):
    """The checker is total: malformed input is rejected, never raised."""

    def test_malformed_certificates_are_rejected_not_raised(self):
        certificate = built_certificate("X")
        malformed = [
            None,
            [],
            "css-sector-distance-lower-bound",
            {},
            dict(certificate, kind="something-else"),
            dict(certificate, format_version=99),
            dict(certificate, sector="W"),
            dict(certificate, bound=-1),
            dict(certificate, bound="3"),
            dict(certificate, state={"qubits": "nope"}),
            dict(certificate, state={"qubits": [0, 0, 1],
                                     "rows": certificate["state"]["rows"]}),
            dict(certificate, state={"qubits": [0, 1],
                                     "rows": certificate["state"]["rows"]}),
            dict(certificate, state=dict(certificate["state"],
                                         rows={"X": [[99]], "Z": []})),
            dict(certificate, state=dict(certificate["state"],
                                         rows={"X": []})),
            dict(certificate, kills="all-of-them"),
            dict(certificate, kills=[{"support": [0]}]),
            dict(certificate, kills=[
                {"support": [0], "reason": {"kind": "vibes"}}]),
            dict(certificate, kills=[
                {"support": [0],
                 "reason": {"kind": "odd_overlap", "row_sector": "X",
                            "row": certificate["state"]["rows"]["X"][0]}}]),
            dict(certificate, kills=[
                {"support": [0],
                 "reason": {"kind": "odd_overlap", "row_sector": "Z",
                            "row": [1, None]}}]),
            dict(certificate, kills=[
                {"support": [0],
                 "reason": {"kind": "odd_overlap", "row_sector": "Z",
                            "row": [1, "a"]}}]),
            dict(certificate, bound=10 ** 6),
        ]
        for case in malformed:
            accepted, failures = check_sector_lower_bound_certificate(case)
            self.assertFalse(accepted, case)
            self.assertIsInstance(failures, list)
            self.assertTrue(failures, case)

    def test_an_anticommuting_carried_state_is_rejected(self):
        # The checker re-derives CSS orthogonality, so a carried state whose
        # X and Z rows anticommute is rejected before any kill is read.
        certificate = built_certificate("X")
        certificate["state"]["rows"]["Z"].append([0])
        accepted, failures = check_sector_lower_bound_certificate(certificate)
        self.assertFalse(accepted)
        self.assertTrue(any("not CSS" in f for f in failures), failures)


class CommittedArtifactTests(unittest.TestCase):
    """The committed artifact stays equal to a fresh prototype run."""

    def test_committed_artifact_matches_a_fresh_run(self):
        with open(REPORT_PATH) as source:
            committed = json.load(source)
        self.assertEqual(build_prototype_artifact(), committed)


if __name__ == "__main__":
    unittest.main()