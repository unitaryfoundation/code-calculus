#!/usr/bin/env python3
"""Survey how the interaction radius behaves under `E-GRAFT`.

The radius is the largest Euclidean diameter of any single check's support in
a layout. It is exactly computable, so this survey measures rather than
searches. It exists to make two claims in
[`archive/notes/LAYOUT_PARAMETER_PLAN.md`](../../archive/notes/LAYOUT_PARAMETER_PLAN.md) §5
auditable instead of asserted:

* the graft does **not** preserve the radius -- some grafts increase it; and
* what is derivable is the weaker bound ``r' <= 2r``, which the triangle
  inequality gives on the graft's adjacent products.

The survey reads the challenge's own board entries and layouts. It is an
experiment, not a rule: nothing here is imported by the consumer, and a
survey result can never confirm a claim, only falsify a candidate rule.
"""

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from machine.priced_calculus import (  # noqa: E402
    CodeState,
    Malformed,
    NoDerivation,
    interaction_radius_squared,
    radius_nearest_decimal,
)


def layout_coordinates(document):
    """The document's layout coordinates, or None if it carries no usable one."""
    locality = document.get("locality")
    if not isinstance(locality, dict):
        return None
    coordinates = locality.get("coordinates")
    if not isinstance(coordinates, list) or len(coordinates) != document["n"]:
        return None
    if any(len(point) != 2 for point in coordinates):
        return None
    return [tuple(value for value in point) for point in coordinates]


def radius_sq_in(coordinates, state):
    """The squared radius of a state, measured in the parent's label space.

    The displayed rows carry the parent's qubit labels and the coordinates
    are indexed the same way, so the two can be read against each other
    directly -- before and after the graft alike. The comparison is made on
    the exact squared values, so no tolerance is involved
    (spec/JUDGMENT_LAYER.md section 2d.1, 2026-10-25).
    """
    return interaction_radius_squared(coordinates,
                                      [row.support for row in state.rows])


def graft_orders(state, qubit, sector):
    """Every ordering of the displayed sector rows touching `qubit`."""
    touching = [row.id for row in state.sector_rows(sector) if qubit in row.support]
    if not touching:
        return []
    import itertools
    return [list(order) for order in itertools.permutations(touching)]


def challenge_commit(challenge_root):
    """The challenge checkout's HEAD, when it is a git checkout."""
    import subprocess
    try:
        return subprocess.check_output(
            ["git", "-C", str(challenge_root), "rev-parse", "HEAD"],
            stderr=subprocess.DEVNULL,
        ).decode().strip()
    except (OSError, subprocess.SubprocessError):
        return None


def survey(challenge_root, max_n=14):
    """Measure every applicable graft over the board entries that carry a layout."""
    codes = Path(challenge_root) / "codes"
    entries = sorted(codes.glob("*.json"))
    scanned = 0
    applicable = 0
    increased = 0
    worst_ratio_sq = None
    worst_case = None
    violations = []
    for path in entries:
        document = json.loads(path.read_text())
        if document.get("n", 10 ** 9) > max_n:
            continue
        coordinates = layout_coordinates(document)
        if coordinates is None:
            continue
        try:
            state = CodeState.from_challenge(document)
        except (Malformed, ValueError, KeyError, TypeError):
            # A non-CSS entry, or one whose declared k disagrees with its
            # rows, is skipped: `from_challenge` reports both as `Malformed`.
            continue
        scanned += 1
        parent_sq = radius_sq_in(coordinates, state)
        if parent_sq <= 0:
            continue
        for qubit in state.Q:
            for sector in ("X", "Z"):
                for order in graft_orders(state, qubit, sector):
                    try:
                        child = state.graft(qubit, sector, order)
                    except NoDerivation:
                        continue
                    applicable += 1
                    child_sq = radius_sq_in(coordinates, child)
                    ratio_sq = child_sq / parent_sq
                    if child_sq > parent_sq:
                        increased += 1
                    if worst_ratio_sq is None or ratio_sq > worst_ratio_sq:
                        worst_ratio_sq = ratio_sq
                        worst_case = {
                            "code": path.name,
                            "qubit": qubit,
                            "sector": sector,
                            "order": list(order),
                            "parent_radius": radius_nearest_decimal(parent_sq, 4),
                            "child_radius": radius_nearest_decimal(child_sq, 4),
                            "ratio": radius_nearest_decimal(ratio_sq, 4),
                        }
                    if child_sq > 4 * parent_sq:
                        violations.append({
                            "code": path.name,
                            "qubit": qubit,
                            "sector": sector,
                            "parent_radius": radius_nearest_decimal(parent_sq, 4),
                            "child_radius": radius_nearest_decimal(child_sq, 4),
                        })
    return {
        "challenge_commit": challenge_commit(challenge_root),
        "max_n": max_n,
        "entries_with_layout_scanned": scanned,
        "applicable_grafts": applicable,
        "grafts_that_increase_the_radius": increased,
        "max_observed_ratio": None if worst_ratio_sq is None
        else radius_nearest_decimal(worst_ratio_sq, 4),
        "worst_case": worst_case,
        "bound_violations_r_gt_2r": violations,
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("challenge_root", help="path to the qLDPC challenge checkout")
    parser.add_argument("--max-n", type=int, default=14,
                        help="largest entry size to survey (default 14)")
    parser.add_argument("--output", help="optional path for the survey report")
    args = parser.parse_args(argv)
    report = survey(args.challenge_root, args.max_n)
    if args.output:
        Path(args.output).write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
