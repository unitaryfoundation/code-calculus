#!/usr/bin/env python3
"""Measure generation and `lake build` time of formal-certificate modules (issue #653).

    python3 machine/experiments/benchmark_formal_cert.py [--codes NAME ...]
        [--timeout SECONDS] [--no-build] [--no-well-formedness]

For each code below, the module `formal_cert_from_challenge.generate`
writes is generated twice, once with `<name>_wellFormed` and once
without, and each is built with
``lake build CodeCalculus.FormalCerts.<name>``. The modules carry a
pruning-tree lower bound per sector at the code's distance and no
witness, so the times are those of the certificate and binding theorems,
plus the well-formedness theorem in the first build. Prints a markdown
table of n, retained rows per sector, bound, tree nodes, module size,
generation time, and both build times. A build that exceeds
``--timeout`` is stopped and reported as such.

Generated modules are removed afterwards. A generation that fails raises;
a build that fails is reported, and the exit status is then 1.

The bounds are the sector distances, found by certifying ascending bounds
until the producer refuses, and stated here so a run does not repeat the
search.
"""

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from machine.certificates import tree_node_counts  # noqa: E402
from machine.constructors import two_block_code  # noqa: E402
from machine.experiments.formal_cert_from_challenge import (  # noqa: E402
    LEAN_DIR,
    generate,
    module_name,
    module_path,
    write_module,
)
from machine.ingestion import retained_rows  # noqa: E402

FIXTURE = ROOT / "machine" / "fixtures" / "qldpc_10_2_3_b.json"


def _two_block(ell, a, b):
    def document():
        state, _ = two_block_code([ell], [[0], [a[0]], [a[1]]],
                                  [[0], [b[0]], [b[1]]])
        return {"n": state.n(), "k": state.k(), "checks": {
            side: [sorted(row.support) for row in state.sector_rows(side)]
            for side in ("X", "Z")}}
    return document


def _fixture():
    document = json.loads(FIXTURE.read_text())
    del document["distance"]  # no witness, as for the other codes
    return document


# name -> (document factory, bound per sector)
CODES = {
    "bench_10_2_3": (_fixture, 3),
    "bench_18_4_4": (_two_block(9, (1, 2), (1, 5)), 4),
    "bench_24_8_2": (_two_block(12, (2, 4), (2, 4)), 2),
    "bench_24_4_4": (_two_block(12, (1, 2), (1, 5)), 4),
    "bench_30_4_6": (_two_block(15, (10, 14), (11, 13)), 6),
    "bench_42_4_6": (_two_block(21, (1, 2), (1, 8)), 6),
    "bench_48_4_8": (_two_block(24, (1, 2), (2, 10)), 8),
}


def _build(name, timeout):
    """Seconds for ``lake build``, or a string saying why there is none."""
    start = time.monotonic()
    try:
        proc = subprocess.run(["lake", "build", module_name(name)],
                              cwd=str(LEAN_DIR), capture_output=True,
                              text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return "timeout > %ds" % timeout
    if proc.returncode != 0:
        lines = (proc.stdout + proc.stderr).strip().splitlines()
        tail = [line for line in lines if line.startswith("error: ")][:2]
        print("lake build %s failed:\n%s" % (name, "\n".join(tail)),
              file=sys.stderr)
        return "failed"
    return time.monotonic() - start


def _cell(value):
    return "%.2f" % value if isinstance(value, float) else str(value)


def measure(name, timeout, build, well_formedness):
    factory, bound = CODES[name]
    document = factory()
    bounds = {"X": bound, "Z": bound}
    row = {"code": name, "n": document["n"], "bound": bound}
    variants = [("without", "never")]
    if well_formedness:
        variants.append(("with", "always"))
    try:
        for label, mode in variants:
            start = time.monotonic()
            generated = generate(document, name, bounds,
                                 well_formedness=mode, allow_large=True,
                                 source="the benchmark")
            elapsed = time.monotonic() - start
            if label == "without":
                row["rows"] = retained_rows(generated["state"])
                row["nodes"] = sum(
                    sum(tree_node_counts(cert["tree"]).values())
                    for cert in generated["certificates"].values())
                row["bytes"] = len(generated["module"].encode("utf-8"))
                row["generation"] = elapsed
            write_module(name, generated["module"])
            row["build_" + label] = (_build(name, timeout) if build
                                     else "not run")
    finally:
        path = module_path(name)
        if path.exists():
            path.unlink()
    return row


def main(argv):
    parser = argparse.ArgumentParser(description=__doc__.strip().splitlines()[0])
    parser.add_argument("--codes", nargs="*", default=list(CODES),
                        choices=list(CODES))
    parser.add_argument("--timeout", type=int, default=900,
                        help="seconds allowed per lake build")
    parser.add_argument("--no-build", action="store_true")
    parser.add_argument("--no-well-formedness", action="store_true",
                        help="skip the build that includes <name>_wellFormed")
    args = parser.parse_args(argv)
    columns = ["code", "n", "rows", "bound", "nodes", "bytes", "generation",
               "build_without", "build_with"]
    print("| " + " | ".join(columns) + " |")
    print("|" + "---|" * len(columns))
    failed = False
    for name in args.codes:
        row = measure(name, args.timeout, not args.no_build,
                      not args.no_well_formedness)
        failed = failed or "failed" in (row.get("build_without"),
                                        row.get("build_with"))
        print("| " + " | ".join(_cell(row.get(c, "-")) for c in columns)
              + " |", flush=True)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
