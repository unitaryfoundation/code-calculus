#!/usr/bin/env python3
"""Prototype run of the certificate layer on the pinned replay instance.

The qLDPC replay ( 21) established the parent's exact sector distances
by post-hoc exhaustive enumeration -- an oracle the consumer never calls.
This script turns the *lower-bound half* of that oracle into a checkable
artifact: a kill certificate per sector for ``d_sigma >= 3`` on the pinned
``an archived note`` parent, verified by the checker in
`machine/certificates.py`. It records the artifact sizes and the
kill-criterion assessment required by the 's first-branch deliverable
(`an archived note` sections 5 and 8).

The upper-bound half stays where it already was: a logical witness the
ledger validates by finite-field arithmetic. Nothing here changes a claim
status; `certificate-checked` stays reserved (`spec/CLAIMS.md`).
"""

import hashlib
import json
import math
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from machine.certificates import (  # noqa: E402
    NoCertificate,
    build_sector_lower_bound_certificate,
    certificate_size_bytes,
    check_sector_lower_bound_certificate,
)
from machine.priced_calculus import CodeState  # noqa: E402

FIXTURE = ROOT / "machine" / "fixtures" / "qldpc_10_2_3_b.json"
REPLAY_REPORT = ROOT / "machine" / "experiments" / "challenge_replay.json"
REPORT_PATH = ROOT / "machine" / "experiments" / "certificate_prototype.json"
PINNED_COMMIT = "9d30c66a43bf7c275196267d369ddab171bfd72f"

# The instance certified: the pinned replay parent. Its exact sector
# distances, recorded by the replay's post-hoc enumeration, are 3 in both
# sectors, so a bound of 3 per sector is exactly the fact the oracle
# asserted.
CERTIFIED_BOUND = 3

# The kill criterion's scaling probes: the flat ball format carries one
# kill entry per support of weight < bound, so its entry count grows as
# sum(C(n, w) for w < bound). These (n, bound) pairs size the criterion at
# the replay instance and at the challenge's larger boards.
SCALING_PROBES = [
    {"n": 10, "bound": 3},
    {"n": 14, "bound": 4},
    {"n": 100, "bound": 5},
]


def _ball_entries(n, bound):
    """sum(C(n, w) for w < bound), the flat format's entry count."""
    return sum(math.comb(n, weight) for weight in range(bound))


def build_prototype_artifact():
    """Build the committed artifact's content as a plain dict."""
    fixture_bytes = FIXTURE.read_bytes()
    document = json.loads(fixture_bytes)
    state = CodeState.from_challenge(document)
    replay = json.loads(REPLAY_REPORT.read_text())
    parent_exact = replay["addition"]["parent_exact_distance_experiment"]

    certificates = []
    for sector in ("X", "Z"):
        certificate = build_sector_lower_bound_certificate(
            state, sector, CERTIFIED_BOUND)
        accepted, failures = check_sector_lower_bound_certificate(certificate)
        if not accepted:
            raise SystemExit("checker rejected a freshly built certificate: %s"
                             % failures)
        certificates.append({
            "sector": sector,
            "bound": CERTIFIED_BOUND,
            "accepted": accepted,
            "kill_entries": len(certificate["kills"]),
            "artifact_bytes": certificate_size_bytes(certificate),
            "replay_exact_distance": parent_exact[sector],
            "certifies_the_replay_oracle_lower_bound":
                CERTIFIED_BOUND <= parent_exact[sector],
        })

    # Negative control: the parent's true distance is 3, so no producer can
    # kill every vector of weight < 4 -- the weight-3 logicals survive.
    negative_control = {"bound": CERTIFIED_BOUND + 1}
    try:
        build_sector_lower_bound_certificate(state, "X", CERTIFIED_BOUND + 1)
        negative_control["producer_refused"] = False
    except NoCertificate as exc:
        negative_control["producer_refused"] = True
        negative_control["refusal"] = str(exc)

    artifact = {
        "harness": "certificate_prototype",
        "format": "css-sector-distance-lower-bound",
        "format_version": 1,
        "instance": {
            "source": "unitaryfoundation/qldpc-challenge an archived note",
            "pinned_commit": PINNED_COMMIT,
            "fixture": "machine/fixtures/qldpc_10_2_3_b.json",
            "fixture_sha256": hashlib.sha256(fixture_bytes).hexdigest(),
            "n": state.n(),
            "k": state.k(),
        },
        "certificates": certificates,
        "negative_control": negative_control,
        "checker": {
            "module": "machine/certificates.py",
            "contract": "an archived note section 4",
            "coverage_enumeration_per_certificate":
                _ball_entries(state.n(), CERTIFIED_BOUND),
        },
        "kill_criterion": {
            "statement": "an archived note section 8",
            "verdict": "passes at this instance",
            "assessment": (
                "The prototype certifies a non-trivial lower endpoint "
                "(d_X >= 3 and d_Z >= 3 on the pinned parent) with %d kill "
                "entries and a few kilobytes per sector, and the checker is "
                "total and decidable over a small trusted base. The flat "
                "ball format's cost is sum(C(n, w), w < bound) entries; at "
                "the challenge's larger boards the same format is "
                "impractically large (see scaling_probes), so the next "
                "decision is the plan's section 9 question 1 -- search tree "
                "or covering certificate -- not a bigger flat artifact."
                % certificates[0]["kill_entries"]),
            "scaling_probes": [
                dict(probe, entries=_ball_entries(probe["n"], probe["bound"]))
                for probe in SCALING_PROBES
            ],
        },
    }
    return artifact


def main(argv=None):
    del argv
    artifact = build_prototype_artifact()
    report = json.dumps(artifact, indent=2) + "\n"
    REPORT_PATH.write_text(report)
    print(report, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())