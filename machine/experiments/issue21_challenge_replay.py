#!/usr/bin/env python3
"""Reproduce issue 21's small-code and real-deletion challenge exercises.

The qLDPC verifier is invoked unchanged. Exact enumeration is kept in this
experiment only: one small parent measurement seeds the interval, and a second
enumeration is an independent post-hoc check of the transported child bound.
The production consumer never imports or calls this distance routine.
"""

import argparse
import itertools
import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from machine.priced_calculus import (  # noqa: E402
    CodeState,
    DistanceLedger,
    NoDerivation,
    apply_operation,
    export_challenge_entry,
    run_sequence,
    support_mask,
    in_span,
)

from machine.oracle import exact_distances  # noqa: E402


Q_LDPC_SHA = "9d30c66a43bf7c275196267d369ddab171bfd72f"


def find_witness(state, side, max_weight=3):
    """Bounded low-weight witness search, not an exact distance calculation."""
    examined = 0
    for weight in range(1, max_weight + 1):
        for support in itertools.combinations(state.Q, weight):
            examined += 1
            vector = support_mask(support)
            same = [row.mask for row in state.sector_rows(side)]
            opposite = [row.mask for row in state.sector_rows("Z" if side == "X" else "X")]
            if (all(bin(vector & row).count("1") % 2 == 0 for row in opposite)
                    and not in_span(vector, same)):
                return list(support), examined
    raise RuntimeError("no witness through weight %d for side %s" % (max_weight, side))


def _run_challenge_verifier(challenge_root, document, directory, label):
    path = directory / (label + ".json")
    path.write_text(json.dumps(document, indent=2) + "\n")
    verifier = Path(challenge_root) / "verify" / "qldpc_verify.py"
    result = subprocess.run(
        [sys.executable, str(verifier), str(path)],
        check=False,
        capture_output=True,
        text=True,
    )
    try:
        report = json.loads(result.stdout)
    except (json.JSONDecodeError, ValueError) as exc:
        raise RuntimeError(
            "qLDPC verifier produced no JSON report for %s: %s\nstdout=%r\nstderr=%r"
            % (label, exc, result.stdout, result.stderr)
        ) from exc
    if result.returncode != 0 or not report.get("ok"):
        failed = [check for check in report.get("checks", []) if not check["ok"]]
        raise RuntimeError("qLDPC verifier rejected %s: %s" % (label, failed))
    return {
        "ok": report["ok"],
        "earned_distance": report.get("earned_distance"),
        "distance_not_refuted": next(
            (check["detail"] for check in report.get("checks", [])
             if check["check"] == "distance_not_refuted"),
            "not run",
        ),
        "failed_checks": [],
    }


def run_addition_replay(challenge_root, output_dir):
    parent_path = Path(challenge_root) / "codes" / "10-2-3-b.json"
    parent = json.loads(parent_path.read_text())
    initial_state = CodeState.from_challenge(parent)
    measured_parent = exact_distances(initial_state)
    lower = {
        side: {"value": measured_parent[side],
               "source": "experiment-only exhaustive enumeration of the parent"}
        for side in ("X", "Z")
    }
    lower["d"] = {"value": measured_parent["d"],
                   "source": "experiment-only exhaustive enumeration of the parent"}

    operation = {"op": "C-ADD-CHECK", "sector": "X", "support": [0, 8, 9]}
    child_state = apply_operation(initial_state, operation)
    witness_x, tries_x = find_witness(child_state, "X")
    witness_z, tries_z = find_witness(child_state, "Z")
    operation["witnesses"] = {"X": witness_x, "Z": witness_z}
    final_state, ledger, trace = run_sequence(parent, [operation], lower, target=3)

    # This oracle call is deliberately after the consumer trace. It checks the
    # candidate relation; it is not an input to the propagation decision.
    measured_child = exact_distances(final_state)
    if measured_child["d"] != ledger.full.lower or measured_child["d"] != ledger.full.upper:
        raise AssertionError("post-hoc child measurement did not close the interval")
    output = export_challenge_entry(
        parent, final_state, ledger,
        "[[10,1,3]] priced-calculus addition",
        "C-ADD-CHECK X {0,8,9} from challenge codes/10-2-3-b.json",
        "2026-10-19",
    )
    verifier = _run_challenge_verifier(challenge_root, output, output_dir, "addition")
    return {
        "parent": "codes/10-2-3-b.json",
        "parent_parameters": {"n": initial_state.n(), "k": initial_state.k()},
        "parent_exact_distance_experiment": measured_parent,
        "operation": operation,
        "child_parameters": {"n": final_state.n(), "k": final_state.k()},
        "child_exact_distance_validation_only": measured_child,
        "bounded_witness_search_candidates": {"X": tries_x, "Z": tries_z},
        "consumer_trace": trace,
        "challenge_verifier": verifier,
        "interpretation": (
            "The propagation path used the parent's exhaustive lower bound, "
            "C-ADD-CHECK monotonicity, and child logical witnesses. The second "
            "exact enumeration was an independent experiment-only check, not "
            "part of the consumer path."
        ),
    }


def run_strict_improvement_survey(challenge_root):
    """Exhaust every single-check addition to the small challenge parent."""
    parent = json.loads(
        (Path(challenge_root) / "codes" / "10-2-3-b.json").read_text()
    )
    initial = CodeState.from_challenge(parent)
    old_distance = exact_distances(initial)["d"]
    support_vectors = (1 << initial.n()) - 1
    report = {
        "parent": "codes/10-2-3-b.json",
        "parent_exact_distance_experiment": old_distance,
        "support_vectors_examined_per_sector": support_vectors,
        "exact_distance_oracle": "experiment-only; not called by the consumer; "
                                 "minimum weight over all logicals in each sector",
        "sectors": {},
    }
    for sector in ("X", "Z"):
        valid = 0
        best_distance = old_distance
        best_support = None
        for mask in range(1, 1 << initial.n()):
            support = tuple(
                q for index, q in enumerate(initial.Q) if mask & (1 << index)
            )
            try:
                child = initial.add_check(sector, support)
            except NoDerivation:
                continue
            valid += 1
            child_distance = exact_distances(child)["d"]
            if child_distance > best_distance:
                best_distance = child_distance
                best_support = list(support)
        report["sectors"][sector] = {
            "valid_single_check_additions": valid,
            "best_child_distance": best_distance,
            "best_support": best_support,
            "strict_improvement_found": best_distance > old_distance,
        }
    return report


def run_deletion_replay(challenge_root, output_dir):
    parent = json.loads((Path(challenge_root) / "codes" / "119-34-5.json").read_text())
    child1 = json.loads((Path(challenge_root) / "codes" / "119-35-3.json").read_text())
    child2 = json.loads((Path(challenge_root) / "codes" / "119-36-3.json").read_text())
    operations = [
        {"op": "C-DELETE-CHECK", "row_id": "a1",
         "witnesses": {"X": child1["distance"]["X"]["witness"],
                       "Z": child1["distance"]["Z"]["witness"]}},
        {"op": "C-DELETE-CHECK", "row_id": "a23",
         "witnesses": {"X": child2["distance"]["X"]["witness"],
                       "Z": child2["distance"]["Z"]["witness"]}},
    ]
    state, ledger, trace = run_sequence(parent, operations, target=4)
    expected = CodeState.from_challenge(child2)
    if sorted(map(tuple, state.to_challenge_checks()["X"])) != sorted(
        map(tuple, expected.to_challenge_checks()["X"])
    ) or sorted(map(tuple, state.to_challenge_checks()["Z"])) != sorted(
        map(tuple, expected.to_challenge_checks()["Z"])
    ):
        raise AssertionError("calculus deletion chain does not match the challenge entry")
    output = export_challenge_entry(
        parent, state, ledger,
        "[[119,36,3]] priced-calculus deletion replay",
        "Two C-DELETE-CHECK steps matching challenge entries 119-35-3 and 119-36-3",
        "2026-10-19",
    )
    verifier = _run_challenge_verifier(challenge_root, directory=output_dir,
                                       document=output, label="deletion")
    return {
        "parent": "codes/119-34-5.json",
        "children": ["codes/119-35-3.json", "codes/119-36-3.json"],
        "final_child_parameters": {"n": state.n(), "k": state.k()},
        "consumer_trace": trace,
        "final_interval": ledger.as_json()["d"],
        "verdict_for_target_4": ledger.decide(4),
        "exact_distance_remeasurements": 0,
        "challenge_verifier": verifier,
        "interpretation": (
            "The supplied challenge witnesses tighten the upper bound to 3, "
            "so target distance 4 is pruned without an exact distance run. "
            "The calculus does not infer a lower bound or claim the exact child distance."
        ),
    }


def run_graft_replay(challenge_root, output_dir):
    parent = json.loads(
        (Path(challenge_root) / "codes" / "10-2-3-b.json").read_text()
    )
    initial_state = CodeState.from_challenge(parent)
    operation = {
        "op": "E-GRAFT",
        "qubit": 0,
        "sector": "X",
        "ordered_row_ids": ["a1", "a2"],
    }
    candidate = apply_operation(initial_state, operation)
    witnesses = {}
    bounded_search = {}
    for side in ("X", "Z"):
        witnesses[side], bounded_search[side] = find_witness(
            candidate, side, max_weight=3
        )
    operation["witnesses"] = witnesses
    state, ledger, trace = run_sequence(parent, [operation], target=3)

    # This exact enumeration is experiment-only and occurs after the target
    # decision. It is a post-hoc cross-check of the transported bound, and it
    # also records what the source's sector-wise graft price predicts.
    measured_child = exact_distances(state)
    if ledger.full.upper is None or ledger.full.upper < measured_child["d"]:
        raise AssertionError("graft witness is not a sound child upper bound")
    measured_parent = exact_distances(initial_state)
    spliced = operation["sector"]
    other = "Z" if spliced == "X" else "X"
    sector_wise = {
        "spliced_sector": spliced,
        "parent": {spliced: measured_parent[spliced], other: measured_parent[other]},
        "child": {spliced: measured_child[spliced], other: measured_child[other]},
        "spliced_sector_unchanged": measured_child[spliced] == measured_parent[spliced],
        "other_sector_not_raised": measured_child[other] <= measured_parent[other],
        "note": (
            "The source states d'_tau = d_tau for the spliced sector and "
            "d'_sigma <= d_sigma for each sector (code-deformation rows 28.4 "
            "and 28.5). These are the measured values to compare against; "
            "agreement is evidence, never confirmation."
        ),
    }
    output = export_challenge_entry(
        parent, state, ledger,
        "[n=9,k=2] E-GRAFT witness submission",
        "E-GRAFT q=0, X chain [a1,a2] from codes/10-2-3-b.json",
        "2026-10-19",
    )
    verifier = _run_challenge_verifier(
        challenge_root, output, output_dir, "graft"
    )
    return {
        "parent": "codes/10-2-3-b.json",
        "operation": operation,
        "child_parameters": {"n": state.n(), "k": state.k()},
        "bounded_witness_search_candidates": bounded_search,
        "consumer_trace": trace,
        "child_exact_distance_validation_only": measured_child,
        "sector_wise_comparison": sector_wise,
        "challenge_verifier": verifier,
        "interpretation": (
            "The consumer prunes target 3 from a valid weight-2 upper witness. "
            "Post-hoc exhaustive enumeration finds the child's distance to be 2, "
            "so the transported upper bound is exact on this instance, and the "
            "spliced sector is unchanged at 3 as the source's sector-wise "
            "relation predicts. The randomized verifier's failure to find a "
            "lighter logical is consistent with that, and is still not a "
            "lower-bound certificate: it is a randomized refutation, and the "
            "ledger's lower endpoint remains 0."
        ),
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("challenge_root", help="checkout of unitaryfoundation/qldpc-challenge")
    parser.add_argument("--output", help="write report JSON to this path")
    args = parser.parse_args(argv)
    challenge_root = Path(args.challenge_root).resolve()
    sha = subprocess.check_output(
        ["git", "-C", str(challenge_root), "rev-parse", "HEAD"], text=True
    ).strip()
    if sha != Q_LDPC_SHA:
        raise SystemExit("expected pinned qLDPC commit %s, got %s" % (Q_LDPC_SHA, sha))
    # A modified working tree at the pinned HEAD can execute arbitrary code
    # while stamping the pinned SHA, so refuse a dirty checkout (RG-23/RC-23).
    dirty_run = subprocess.run(
        ["git", "-C", str(challenge_root), "status", "--porcelain"],
        capture_output=True, text=True,
    )
    if dirty_run.returncode != 0:
        raise SystemExit(
            "could not check the qLDPC checkout at %s with git status (%s); "
            "the pinned replay requires a git checkout of the challenge "
            "repository: %s" % (sha, dirty_run.returncode, dirty_run.stderr.strip())
        )
    dirty = dirty_run.stdout
    if dirty.strip():
        raise SystemExit(
            "qLDPC checkout at %s has local modifications; refusing to run the "
            "verifier:\n%s" % (sha, dirty)
        )
    # TODO(2026-10-29, issue #252): design/VALIDATION.md lists
    # ``verifier_source_hash`` as a required manifest field but records no
    # pinned hash yet, so there is nothing to compare against here. Once a
    # hash is recorded there, verify sha256(verify/qldpc_verify.py) against it
    # before invoking the verifier; do not treat any value as pinned before
    # that record exists.
    with tempfile.TemporaryDirectory(prefix="issue21-replay-") as temporary:
        output_dir = Path(temporary)
        report = {
            "qldpc_commit": sha,
            "addition": run_addition_replay(challenge_root, output_dir),
            "strict_improvement_survey": run_strict_improvement_survey(
                challenge_root
            ),
            "graft": run_graft_replay(challenge_root, output_dir),
            "deletion": run_deletion_replay(challenge_root, output_dir),
        }
    rendered = json.dumps(report, indent=2)
    if args.output:
        Path(args.output).write_text(rendered + "\n")
    print(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
