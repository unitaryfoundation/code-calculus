"""Certificate-layer prototype tests (first branch).

The format and checker live in `machine/certificates.py`; the committed
instance artifact is `the conformance harness`. No
test here changes a claim status: the certificates are evidence about
feasibility of the format, not a status upgrade.
"""

import copy
import json
import math
import os
import random
import unittest

from machine.certificates import (
    NoCertificate,
    build_sector_lower_bound_certificate,
    build_sector_lower_bound_tree_certificate,
    certificate_size_bytes,
    check_sector_lower_bound_certificate,
    check_sector_lower_bound_tree_certificate,
    tree_node_counts,
)
from machine.constructors import two_block_code
from machine.oracle import exact_distances
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

    def test_both_sector_certificates_are_accepted(self):
        with open(
            os.path.join(HERE, "experiments", "issue21_challenge_replay.json"),
            encoding="utf-8",
        ) as fh:
            replay = json.load(fh)
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


def cyclic_30():
    """The cyclic two-block code on 30 qubits used for the tree instances."""
    state, _ = two_block_code([15], [[0], [10], [14]], [[0], [11], [13]])
    return state


def tree_certificate(state, sector, bound):
    return build_sector_lower_bound_tree_certificate(state, sector, bound)


def first_node(tree, kind):
    """The first node of ``kind`` in depth-first order, one-branch first."""
    stack = [tree]
    while stack:
        node = stack.pop()
        if node[0] == kind:
            return node
        if node[0] == "branch":
            stack += [node[3], node[2]]
    raise AssertionError("no %s node" % kind)


class PruningTreeCertificateTests(unittest.TestCase):
    """Pruning-tree certificates (issue #574).

    The Python checker is the prototype. The mechanized checker is
    `checkPruneCertificate`, and `lake build` is the authority for the
    instances of `CertificateInstances.lean`.
    """

    def test_both_sectors_of_the_pinned_parent_are_accepted(self):
        for sector in ("X", "Z"):
            certificate = tree_certificate(pinned_parent(), sector, 3)
            accepted, failures = check_sector_lower_bound_tree_certificate(
                certificate)
            self.assertTrue(accepted, failures)
            json.dumps(certificate)

    def test_a_bound_beyond_the_truth_is_not_producible(self):
        for sector in ("X", "Z"):
            with self.assertRaises(NoCertificate):
                tree_certificate(pinned_parent(), sector, 4)

    def test_producer_reaches_exactly_the_oracle_distance(self):
        # Random small CSS states: the largest bound the producer certifies
        # is the exact sector distance, and every certificate it emits is
        # accepted. Agreement is evidence about the producer and the
        # prototype checker, not a proof of either.
        rng = random.Random(574)
        checked = 0
        while checked < 25:
            ell = rng.randint(3, 6)
            a = sorted(rng.sample(range(ell), rng.randint(1, min(3, ell))))
            b = sorted(rng.sample(range(ell), rng.randint(1, min(3, ell))))
            state, _ = two_block_code([ell], [[e] for e in a], [[e] for e in b])
            if state.k() == 0:
                continue
            exact = exact_distances(state)
            for sector in ("X", "Z"):
                distance = exact[sector]
                certificate = tree_certificate(state, sector, distance)
                self.assertEqual(
                    check_sector_lower_bound_tree_certificate(certificate),
                    (True, []))
                with self.assertRaises(NoCertificate):
                    tree_certificate(state, sector, distance + 1)
            checked += 1

    def test_tree_agrees_with_the_kill_list_on_the_same_fact(self):
        state = pinned_parent()
        for sector in ("X", "Z"):
            for bound in range(4):
                kills = build_sector_lower_bound_certificate(
                    state, sector, bound)
                tree = tree_certificate(state, sector, bound)
                self.assertEqual(kills["state"], tree["state"])
                self.assertTrue(check_sector_lower_bound_certificate(kills)[0])
                self.assertTrue(
                    check_sector_lower_bound_tree_certificate(tree)[0])

    def test_thirty_qubit_tree_is_far_smaller_than_the_ball(self):
        state = cyclic_30()
        self.assertEqual((state.n(), state.k()), (30, 4))
        ball = sum(math.comb(30, weight) for weight in range(6))
        self.assertEqual(ball, 174437)
        for sector in ("X", "Z"):
            certificate = tree_certificate(state, sector, 6)
            self.assertEqual(
                check_sector_lower_bound_tree_certificate(certificate),
                (True, []))
            nodes = sum(tree_node_counts(certificate["tree"]).values())
            self.assertLess(nodes, 5000)
            self.assertLess(30 * nodes, ball)
            with self.assertRaises(NoCertificate):
                tree_certificate(state, sector, 7)

    def test_a_tree_for_one_bound_is_rejected_for_a_larger_one(self):
        certificate = tree_certificate(pinned_parent(), "X", 3)
        certificate["bound"] = 4
        accepted, failures = check_sector_lower_bound_tree_certificate(
            certificate)
        self.assertFalse(accepted)
        self.assertTrue(any("does not reach the bound" in f for f in failures))

    def test_tampered_leaves_are_rejected(self):
        state = pinned_parent()
        base = tree_certificate(state, "X", 3)
        rows = len(base["state"]["rows"]["Z"])

        def rejected(mutate, fragment):
            certificate = copy.deepcopy(base)
            mutate(certificate)
            accepted, failures = check_sector_lower_bound_tree_certificate(
                certificate)
            self.assertFalse(accepted)
            self.assertTrue(any(fragment in f for f in failures), failures)

        def other_row(kind):
            def mutate(certificate):
                node = first_node(certificate["tree"], kind)
                node[1] = (node[1] + 1) % rows
            return mutate

        rejected(other_row("need_more"), "even overlap")
        rejected(other_row("conflict"), "")

        def flip_coefficient(certificate):
            first_node(certificate["tree"], "in_span")[1][0] ^= 1
        rejected(flip_coefficient, "not the fixed vector")

        def conflict_too_early(certificate):
            # Replace the root, where nothing is fixed, by a conflict leaf.
            certificate["tree"] = ["conflict", 0]
        rejected(conflict_too_early, "even overlap")

        def span_too_early(certificate):
            certificate["tree"] = first_node(certificate["tree"], "in_span")
        rejected(span_too_early, "free qubit")

        def drop_a_subtree(certificate):
            certificate["tree"][2] = ["bound"]
        rejected(drop_a_subtree, "below the bound")

        def branch_twice(certificate):
            tree = certificate["tree"]
            certificate["tree"] = ["branch", tree[1], tree, tree[3]]
        rejected(branch_twice, "already fixed")

        def other_sector(certificate):
            certificate["state"]["rows"]["X"][0] = [0, 1, 3, 5]
        rejected(other_sector, "")

    def test_malformed_trees_are_rejected_not_raised(self):
        base = tree_certificate(pinned_parent(), "Z", 3)
        cases = [None, [], {}, "tree", 7]
        for tree in (None, [], ["bound", 1], ["need_more"], ["need_more", -1],
                     ["need_more", 99], ["need_more", True], ["conflict", "0"],
                     ["in_span"], ["in_span", [1]], ["in_span", "111"],
                     ["branch", 0], ["branch", 99, ["bound"], ["bound"]],
                     ["branch", 0, None, ["bound"]], ["prune"], "bound", 3):
            certificate = copy.deepcopy(base)
            certificate["tree"] = tree
            cases.append(certificate)
        for key in ("kind", "format_version", "sector", "bound", "state",
                    "tree"):
            certificate = copy.deepcopy(base)
            del certificate[key]
            cases.append(certificate)
        for bad_state in ({"qubits": [0, 0], "rows": {"X": [], "Z": []}},
                          {"qubits": [0, 1], "rows": {"X": [[5]], "Z": []}},
                          {"qubits": [0, 1], "rows": {"X": []}}, [], None):
            certificate = copy.deepcopy(base)
            certificate["state"] = bad_state
            cases.append(certificate)
        for certificate in cases:
            accepted, failures = check_sector_lower_bound_tree_certificate(
                certificate)
            self.assertFalse(accepted)
            self.assertTrue(failures)

    def test_bound_zero_and_the_checker_are_deterministic(self):
        certificate = tree_certificate(pinned_parent(), "X", 0)
        self.assertEqual(certificate["tree"], ["bound"])
        self.assertEqual(
            check_sector_lower_bound_tree_certificate(certificate), (True, []))
        again = tree_certificate(pinned_parent(), "X", 3)
        self.assertEqual(again, tree_certificate(pinned_parent(), "X", 3))


class CommittedArtifactTests(unittest.TestCase):
    """The committed artifact stays equal to a fresh prototype run."""

    def test_committed_artifact_matches_a_fresh_run(self):
        with open(REPORT_PATH) as source:
            committed = json.load(source)
        self.assertEqual(build_prototype_artifact(), committed)


if __name__ == "__main__":
    unittest.main()