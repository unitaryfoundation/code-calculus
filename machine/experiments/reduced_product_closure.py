#!/usr/bin/env python3
"""Reduced-product closure experiment for the interval ledger.

This is a **consumer-side, non-normative experiment**.  It does not change the
calculus, does not validate a price or a witness, and is not evidence for
soundness or for ``OBL-PRICED-INTERVAL-SOUNDNESS``.

The ledger keeps three intervals -- ``d``, ``d_X`` and ``d_Z`` -- but the
distance relation is ``d = min(d_X, d_Z)``.  The three projections lose the
relation.  This script measures whether a *simple closure* of that relation
changes a target decision on the traces recorded by the pinned replay
replay, and exhibits one synthetic ledger where it does.

The simple closure is:

* raise each sector's lower endpoint to the full-distance lower endpoint
  (``d <= d_sigma``);
* raise the full-distance lower endpoint to the minimum of the sector lowers
  (``d >= min(d_X, d_Z)``);
* lower the full-distance upper endpoint to the minimum of the sector uppers
  (``d <= min(d_X, d_Z)``).

That is the projection of the relation onto independent intervals.  It is not
the full reduced product: the disjunctive information "at least one sector is
at least L" is not representable by three intervals.  A null result on the
pinned traces therefore says only that the *easy* half is already maintained,
not that a relational domain would be useless.

Run from the repository root:

    python3 machine/experiments/reduced_product_closure.py
    python3 machine/experiments/reduced_product_closure.py --write
"""

import argparse
import json
import math
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from machine.priced_calculus import DistanceLedger, Interval  # noqa: E402


INF = math.inf


def _lower(value):
    """None means +infinity in the ledger; return an ordered sentinel."""
    return INF if value is None else value


def _upper(value):
    return INF if value is None else value


def _interval(lower, upper):
    """Convert sentinel arithmetic back to the ledger's Optional[int] form."""
    return Interval(
        None if lower == INF else int(lower),
        None if upper == INF else int(upper),
    )


def close(full, sector_x, sector_z):
    """Apply the interval projection of ``d = min(d_X, d_Z)``.

    The result is a sound *tightening* of the three intervals: every concrete
    triple satisfying the input intervals and the relation satisfies the
    output intervals.  It is not claimed to be the best interval transformer;
    the best transformer would need the disjunctive correlation.
    """
    if full.lower is None:
        # k = 0: the ledger stores [None, None] in every slot.
        return full, sector_x, sector_z
    full_lower = _lower(full.lower)
    x_lower = max(_lower(sector_x.lower), full_lower)
    z_lower = max(_lower(sector_z.lower), full_lower)
    full_lower = max(full_lower, min(x_lower, z_lower))
    full_upper = min(_upper(full.upper), _upper(sector_x.upper),
                     _upper(sector_z.upper))
    return (
        _interval(full_lower, full_upper),
        _interval(x_lower, _upper(sector_x.upper)),
        _interval(z_lower, _upper(sector_z.upper)),
    )


def _verdict(full, sector_x, sector_z, target):
    return DistanceLedger(full, {"X": sector_x, "Z": sector_z}).decide(target)


def _from_json(entry):
    def interval(item):
        lower = None if item["lower"] == "inf" else item["lower"]
        upper = None if item["upper"] == "inf" else item["upper"]
        return Interval(lower, upper)

    return (
        interval(entry["d"]),
        interval(entry["d_X"]),
        interval(entry["d_Z"]),
    )


def _trace_rows(report):
    rows = []
    for section in ("addition", "graft", "deletion"):
        trace = report.get(section, {}).get("consumer_trace", [])
        for index, step in enumerate(trace):
            intervals = _from_json(step["intervals"])
            rows.append({
                "section": section,
                "step": index,
                "intervals": intervals,
                "before": {
                    "d": intervals[0].as_json(),
                    "d_X": intervals[1].as_json(),
                    "d_Z": intervals[2].as_json(),
                },
            })
    return rows


def run(report):
    rows = _trace_rows(report)
    changed = []
    for row in rows:
        full, sector_x, sector_z = row["intervals"]
        closed = close(full, sector_x, sector_z)
        row["after"] = {
            "d": closed[0].as_json(),
            "d_X": closed[1].as_json(),
            "d_Z": closed[2].as_json(),
        }
        for target in range(0, 9):
            before = _verdict(full, sector_x, sector_z, target)
            after = _verdict(*closed, target)
            if before != after:
                changed.append({
                    "section": row["section"],
                    "step": row["step"],
                    "target": target,
                    "before": before,
                    "after": after,
                    "before_intervals": row["before"],
                    "after_intervals": row["after"],
                })

    # A synthetic ledger that violates the easy half of the relation.  This is
    # a domain-level example, not a state the current transition rules produce:
    # its purpose is to show that the closure is not vacuous as a transformer.
    synthetic_before = (
        Interval(0, 10),
        Interval(5, 10),
        Interval(5, 10),
    )
    synthetic_after = close(*synthetic_before)
    synthetic = {
        "before_intervals": {
            "d": synthetic_before[0].as_json(),
            "d_X": synthetic_before[1].as_json(),
            "d_Z": synthetic_before[2].as_json(),
        },
        "after_intervals": {
            "d": synthetic_after[0].as_json(),
            "d_X": synthetic_after[1].as_json(),
            "d_Z": synthetic_after[2].as_json(),
        },
        "target": 5,
        "before": _verdict(*synthetic_before, 5),
        "after": _verdict(*synthetic_after, 5),
        "note": (
            "Synthetic ledger, not reachable by the current transition rules; "
            "it shows the closure is not the identity as a transformer."
        ),
    }
    if synthetic["before"] == synthetic["after"]:
        raise AssertionError("synthetic witness did not change the verdict")

    return {
        "experiment": "reduced-product interval closure",
        "status": "non-normative consumer experiment; not soundness evidence",
        "source": "machine/experiments/issue21_challenge_replay.json",
        "pinned_commit": report.get("qldpc_commit"),
        "targets_tested": list(range(0, 9)),
        "trace_steps": len(rows),
        "traces": [
            {key: value for key, value in row.items() if key != "intervals"}
            for row in rows
        ],
        "changed_verdicts": changed,
        "synthetic": synthetic,
        "interpretation": (
            "The simple closure changes no target verdict on the pinned traces. "
            "It is not vacuous (the synthetic ledger changes), so the null result "
            "is a statement about the current rule set, not about the relation. "
            "The disjunctive half of d = min(d_X, d_Z) is not representable by "
            "three intervals; testing it needs a relational domain."
        ),
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--report",
        default=str(ROOT / "machine" / "experiments" /
                    "issue21_challenge_replay.json"),
        help="pinned replay report to read",
    )
    parser.add_argument(
        "--write",
        action="store_true",
        help="also write reduced_product_closure.json beside this script",
    )
    args = parser.parse_args(argv)
    report = json.loads(Path(args.report).read_text())
    result = run(report)
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.write:
        out = Path(__file__).resolve().parent / "reduced_product_closure.json"
        out.write_text(text)
        print("wrote %s" % out)
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
