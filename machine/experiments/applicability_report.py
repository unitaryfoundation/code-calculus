#!/usr/bin/env python3
"""Print the move applicability report of one parent (issue #592).

    python3 machine/experiments/applicability_report.py ENTRY.json
        [--weight-cap W] [--include-disconnected] [--json]

``ENTRY.json`` is a document of the shape `CodeState.from_challenge`
accepts.  For each move family the table gives the size of the candidate
domain, how many candidates derive, how many children pass the screens, and
the reason that accounts for most of the rest.  The report is
`machine.planner.move_applicability_report`; it is search control and says
nothing about distance beyond validated weight-1 witnesses.
"""

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from machine.planner import move_applicability_report  # noqa: E402
from machine.priced_calculus import CodeState  # noqa: E402


def render(report):
    parent = report["parent"]
    lines = [
        "parent: n=%d k=%d w=%d rows X=%d Z=%d components=%d" % (
            parent["n"], parent["k"], parent["w"], parent["rows"]["X"],
            parent["rows"]["Z"], parent["components"]),
    ]
    for sector in ("X", "Z"):
        column = parent["column_weight"][sector]
        lines.append("column weight %s: min=%d max=%d histogram=%s" % (
            sector, column["min"], column["max"], column["histogram"]))
    lines.append("")
    lines.append("%-15s %7s %8s %7s  %s" % (
        "family", "domain", "derived", "usable", "reasons"))
    for family, entry in report["families"].items():
        if not entry["enabled"]:
            lines.append("%-15s not asked for" % family)
            continue
        reasons = dict(entry["refusals"])
        reasons.update(entry["screens"])
        ordered = sorted(reasons, key=lambda name: (-reasons[name], name))
        lines.append("%-15s %7d %8d %7d  %s" % (
            family, entry["domain"], entry["derived"], entry["usable"],
            "; ".join("%d x %s" % (reasons[name], name) for name in ordered)
            or "-"))
    return "\n".join(lines)


def main(argv):
    paths = [arg for arg in argv if not arg.startswith("--")]
    cap = None
    if "--weight-cap" in argv:
        cap = int(argv[argv.index("--weight-cap") + 1])
        paths.remove(str(cap))
    if len(paths) != 1:
        print(__doc__.strip())
        return 2
    with open(paths[0]) as source:
        state = CodeState.from_challenge(json.load(source))
    report = move_applicability_report(
        state, weight_cap=cap,
        include_disconnected="--include-disconnected" in argv)
    if "--json" in argv:
        print(json.dumps(report, indent=2, sort_keys=True, default=list))
    else:
        print(render(report))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
