#!/usr/bin/env python3
"""Asserted stress-test battery for the priced CSS calculus discovery loop.

Issue #577: promotes the original exploratory smoke script into an asserted,
CI-wired four-quadrant stress battery plus an ``n = 100-120`` scale ladder.

Empirical evidence only (AGENTS.md *Hard rules*): a clean run with zero
violations is a run that failed to falsify, never a proof or confirmation of
soundness.

Scope split (issue #577 review):
- Transition-level interval-transport differential testing across admitted
  transitions (``C-ADD-CHECK``, ``C-DELETE-CHECK``, ``C-DIRECT-SUM``,
  ``C-SKIP``, ``E-GRAFT``, ``E-PEEL``) is owned by
  ``machine/experiments/priced_conformance_harness.py``.
- Quadrant 1 here covers what that harness does not: all 17 admitted
  constructors in ``ADMITTED_CONSTRUCTORS``, brute-force cross-checks of
  ``domination_prune`` / ``pareto_dominates`` / ``pareto_front`` /
  ``pareto_rank`` / ``pareto_annotate``, and small-``n`` ``plan()`` +
  ``bounded_support_search()`` differential checks against
  ``machine.oracle.exact_distances``.

Report path: writes to ``<tempdir>/stress_campaign_report.json`` by default so
running the script locally never dirties a tracked file. Pass ``--output PATH``
to write elsewhere (e.g., to refresh the committed baseline report or upload as
a weekly CI artifact).
"""

from __future__ import annotations

import argparse
import ast
import copy
import json
import math
import random
import re
import subprocess
import sys
import tempfile
import time
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from machine.constructors import ADMITTED_CONSTRUCTORS, construct  # noqa: E402
from machine.entrypoints import (  # noqa: E402
    fix_support,
    heuristic_outcome,
    multi_check_strict_improvement_feasible,
    strict_improvement_feasible,
)
from machine.intervals import DistanceLedger, Interval, validate_witness  # noqa: E402
from machine.layout import export_challenge_entry  # noqa: E402
from machine.planner import (  # noqa: E402
    DEFAULT_SUPPORT_BUDGET,
    DEFAULT_SUPPORT_MAX_WEIGHT,
    bounded_sector_search,
    bounded_support_search,
    dedup_up_to_permutation,
    domination_prune,
    has_bare_qubit,
    pareto_annotate,
    pareto_dominates,
    pareto_front,
    pareto_rank,
    plan,
    plan_chain,
    reduce_display,
    tighten_ledger_with_search,
)
from machine.priced_calculus import (  # noqa: E402
    CodeState,
    Malformed,
    NoDerivation,
    Row,
    admissible_added_checks,
    apply_operation,
    commutes,
    in_span,
    support_mask,
    tanner_components,
    tower_level_data,
)
from machine.symplectic_calculus import SymplecticLedger, SymplecticState  # noqa: E402

Q_LDPC_SHA = "9d30c66a43bf7c275196267d369ddab171bfd72f"
DEFAULT_SEED = 20261125
DEFAULT_REPORT_PATH = Path(tempfile.gettempdir()) / "stress_campaign_report.json"

# Named medium-n parents from pinned qldpc-challenge (spanning below and above
# ORACLE_N_CEILING = 20 so both prune and re-measure verdicts are exercised).
MEDIUM_PARENTS = (
    "10-2-3-b.json",
    "14-2-3.json",
    "16-2-4.json",
    "24-4-4.json",
    "25-5-4.json",
)

# Named n = 100-120 CSS board parents from pinned qldpc-challenge for the scale
# ladder (Quadrant-3 invariants only; oracle is never invoked above ceiling).
SCALE_LADDER_PARENTS = (
    "100-24-5.json",
    "108-8-10.json",
    "112-12-8.json",
    "119-34-5.json",
    "120-24-8.json",
)

# Advisory per-quadrant wall-clock budgets (seconds). Elapsed time is a metric,
# not an invariant of the consumer: overruns are reported via
# ``within_budget: False`` and ``summary.advisory_budget_overruns`` and never
# recorded as invariant violations or used to fail a run.
QUADRANT_TIME_BUDGETS_SECONDS = {
    "import_hygiene": 30.0,
    "q1_oracle_differential": 120.0,
    "q2_gate_differential": 600.0,
    "q3_invariant_fuzzing": 180.0,
    "q4_adversarial": 60.0,
    "scale_ladder": 600.0,
}

REQUIRED_GATE_STRUCTURAL_CHECKS = frozenset({
    "css_commutation",
    "k_matches_rank",
    "distance_X_witness",
    "distance_Z_witness",
    "d_matches_min_side",
})


def _timing_metrics(
    phase: str, elapsed: float, budget_seconds: float | None = None
) -> dict:
    """Return advisory wall-clock timing metrics for ``phase``."""
    budget = (
        QUADRANT_TIME_BUDGETS_SECONDS[phase]
        if budget_seconds is None
        else float(budget_seconds)
    )
    return {
        "elapsed_seconds": round(elapsed, 4),
        "budget_seconds": budget,
        "within_budget": elapsed <= budget,
    }

# Consumer/planner modules that must never import machine.oracle.
CONSUMER_MODULES = (
    "machine/priced_calculus.py",
    "machine/planner.py",
    "machine/state.py",
    "machine/intervals.py",
    "machine/constructors.py",
    "machine/sequence.py",
    "machine/entrypoints.py",
    "machine/layout.py",
    "machine/connectivity.py",
    "machine/tower_prices.py",
    "machine/gf2.py",
)

# Allowlist of known pre-existing consumer/planner violations, keyed by stable
# violation_id and linked to an open GitHub issue number. Keeping bugs visible
# here instead of silently fixing them inside #577 preserves the #577 boundary.
KNOWN_VIOLATIONS: dict[str, dict[str, str]] = {}

# Operational definition of prune precision (issue #577 review, vprusso #3):
# A planner `prune` verdict asserts `child_ledger.full.upper < target`.
# Because `qldpc_verify.py` verifies exported witnesses (certifying
# `d <= earned_distance["d"]["value"]`) and runs randomized RIS refutation
# (`distance_not_refuted`), a pruned candidate exported via
# `export_challenge_entry` is classified against the gate as:
#   - `confirmed_by_gate`: structural and witness checks pass AND either
#     `earned_distance["d"]["value"] < target` or `distance_not_refuted`
#     witnessed a lighter logical `< target`.
#   - `contradicted_by_gate`: structural/witness checks fail on the exported
#     entry, OR `earned_distance["d"]["value"] >= target` with no refutation
#     below `target`.
#   - `single_side_pruned_unexported`: candidate carried a valid witness on
#     only one sector (so `export_challenge_entry`, which requires both X and
#     Z witnesses, does not emit a two-sided submission); recorded separately
#     rather than folded into the gate denominator.
# `prune_precision = confirmed_by_gate / (confirmed_by_gate + contradicted_by_gate)`.
# Randomized non-refutation on `re-measure` candidates is reported separately
# and is never treated as a lower-bound proof.
PRUNE_PRECISION_DEFINITION = (
    "confirmed_by_gate / (confirmed_by_gate + contradicted_by_gate) over "
    "exportable pruned candidates checked by pinned verify/qldpc_verify.py; "
    "confirmed_by_gate requires structural+witness pass and either "
    "earned_distance.d.value < target or distance_not_refuted witness < target; "
    "single-side pruned candidates lacking an opposite-sector witness are "
    "validated locally and tracked separately as single_side_pruned_unexported."
)


def serialize_state(state):
    """JSON-serializable snapshot of a CodeState for failure reproduction."""
    if not isinstance(state, CodeState):
        return state
    return {
        "Q": list(state.Q),
        "rows": [
            {"id": r.id, "sector": r.sector, "support": list(r.support)}
            for r in state.rows
        ],
        "used": sorted(state.used),
    }


def serialize_ledger(ledger):
    """JSON-serializable snapshot of a DistanceLedger for failure dumps."""
    if not isinstance(ledger, DistanceLedger):
        return ledger
    return ledger.as_json()


class ViolationRecorder:
    """Collects invariant violations with reproducible state/move dumps."""

    def __init__(self, seed: int, known_violations=None):
        self.seed = seed
        self.known_violations = (
            dict(KNOWN_VIOLATIONS)
            if known_violations is None
            else dict(known_violations)
        )
        self.violations: list[dict] = []

    def record(
        self,
        violation_id: str,
        quadrant: str,
        check: str,
        details: str,
        *,
        state=None,
        move_sequence=None,
        extra=None,
    ):
        known_entry = self.known_violations.get(violation_id)
        entry = {
            "violation_id": violation_id,
            "quadrant": quadrant,
            "check": check,
            "seed": self.seed,
            "state": serialize_state(state),
            "move_sequence": list(move_sequence) if move_sequence is not None else [],
            "details": details,
            "known": known_entry is not None,
            "known_issue": known_entry["issue"] if known_entry else None,
        }
        if extra is not None:
            entry["extra"] = extra
        self.violations.append(entry)

    @property
    def unexpected(self) -> list[dict]:
        return [v for v in self.violations if not v["known"]]

    @property
    def known(self) -> list[dict]:
        return [v for v in self.violations if v["known"]]


def _interval_contains(interval: Interval, value: int | None) -> bool:
    """Whether ``interval`` soundly contains exact distance ``value`` (None = +inf)."""
    if value is None:
        return interval.upper is None
    if interval.lower is None:
        return False
    if value < interval.lower:
        return False
    if interval.upper is not None and value > interval.upper:
        return False
    return True


def _gf2_rank(masks: list[int]) -> int:
    basis = []
    for mask in masks:
        v = mask
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
            basis.sort(reverse=True)
    return len(basis)


def _exact_k_from_state(state: CodeState) -> int:
    rx = _gf2_rank([r.mask for r in state.sector_rows("X")])
    rz = _gf2_rank([r.mask for r in state.sector_rows("Z")])
    return len(state.Q) - rx - rz


def _random_css_state(rng: random.Random, n: int) -> CodeState:
    """Generate a random well-formed CSS state on qubits ``0..n-1``."""
    for _ in range(500):
        mx = rng.randint(0, max(1, n // 2))
        mz = rng.randint(0, max(1, n // 2))
        xrows = []
        x_masks = []
        attempts = 0
        while len(xrows) < mx and attempts < 200:
            attempts += 1
            w = rng.randint(2 if n >= 2 else 1, n)
            supp = tuple(sorted(rng.sample(range(n), w)))
            mask = support_mask(supp)
            if in_span(mask, x_masks):
                continue
            x_masks.append(mask)
            xrows.append(supp)
        zrows = []
        z_masks = []
        attempts = 0
        while len(zrows) < mz and attempts < 300:
            attempts += 1
            w = rng.randint(2 if n >= 2 else 1, n)
            supp = tuple(sorted(rng.sample(range(n), w)))
            mask = support_mask(supp)
            if in_span(mask, z_masks):
                continue
            if not commutes(mask, x_masks):
                continue
            z_masks.append(mask)
            zrows.append(supp)
        rows = []
        used = set()
        for idx, supp in enumerate(xrows, start=1):
            rid = f"a{idx}"
            rows.append(Row(rid, "X", supp))
            used.add(rid)
        for idx, supp in enumerate(zrows, start=1):
            rid = f"b{idx}"
            rows.append(Row(rid, "Z", supp))
            used.add(rid)
        try:
            st = CodeState(tuple(range(n)), tuple(rows), frozenset(used))
            st.validate()
            return st
        except (Malformed, NoDerivation):
            continue
    return CodeState(tuple(range(n)), (), frozenset())


# ---------------------------------------------------------------------------
# Phase 0: Oracle import-path hygiene (vprusso #1)
# ---------------------------------------------------------------------------


def check_oracle_import_hygiene(
    recorder: ViolationRecorder, *, budget_seconds: float | None = None
) -> dict:
    """Assert that consumer and planner never import ``machine.oracle``."""
    t0 = time.monotonic()
    static_hits = []
    for rel in CONSUMER_MODULES:
        path = ROOT / rel
        tree = ast.parse(path.read_text(), filename=str(path))
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    if alias.name == "oracle" or alias.name.endswith(".oracle"):
                        static_hits.append({"file": rel, "import": alias.name})
            elif isinstance(node, ast.ImportFrom):
                mod = node.module or ""
                if mod == "oracle" or mod.endswith(".oracle"):
                    static_hits.append({"file": rel, "import_from": mod})
                for alias in node.names:
                    if mod == "machine" and alias.name == "oracle":
                        static_hits.append({"file": rel, "from_machine": alias.name})
    if static_hits:
        recorder.record(
            "oracle-static-import",
            "import_hygiene",
            "static_ast_oracle_import",
            f"consumer/planner modules import oracle: {static_hits}",
            extra={"hits": static_hits},
        )

    probe_code = (
        "import json, pathlib, sys\n"
        f"sys.path.insert(0, {str(ROOT)!r})\n"
        "from machine.priced_calculus import CodeState, DistanceLedger\n"
        "from machine.planner import plan, plan_chain, bounded_support_search, bounded_sector_search\n"
        "doc = json.loads(pathlib.Path('machine/fixtures/qldpc_10_2_3_b.json').read_text())\n"
        "st = CodeState.from_challenge(doc)\n"
        "ld = DistanceLedger.from_challenge(st, doc)\n"
        "plan(st, ld, target=3, structural=True, reduce_display=True, "
        "support_search={'budget': 64, 'max_weight': 3}, sector_swap=True, ranking='pareto')\n"
        "plan_chain(st, ld, target=3, depth=1, structural=True)\n"
        "bounded_support_search(st, budget=64, max_weight=3)\n"
        "bounded_sector_search(st, ld, target_sector='X', target=3, budget=32, max_depth=1)\n"
        "loaded = [m for m in sys.modules if m == 'machine.oracle' or m.endswith('.oracle')]\n"
        "print(json.dumps({'oracle_modules': loaded}))\n"
    )
    proc = subprocess.run(
        [sys.executable, "-c", probe_code],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
        check=False,
    )
    oracle_modules = None
    if proc.returncode != 0:
        recorder.record(
            "oracle-runtime-probe-failed",
            "import_hygiene",
            "runtime_import_isolation",
            f"runtime probe failed (rc={proc.returncode}): {proc.stderr.strip()}",
        )
    else:
        payload = json.loads(proc.stdout.strip().splitlines()[-1])
        oracle_modules = payload["oracle_modules"]
        if oracle_modules:
            recorder.record(
                "oracle-runtime-import",
                "import_hygiene",
                "runtime_import_isolation",
                f"consumer/planner runtime loaded oracle modules: {oracle_modules}",
                extra={"oracle_modules": oracle_modules},
            )
    elapsed = time.monotonic() - t0
    return {
        "static_modules_scanned": len(CONSUMER_MODULES),
        "static_oracle_hits": len(static_hits),
        "runtime_oracle_modules": oracle_modules if oracle_modules is not None else [],
        **_timing_metrics("import_hygiene", elapsed, budget_seconds),
    }


# ---------------------------------------------------------------------------
# Quadrant 1: Oracle differential at small n (vprusso #2)
# ---------------------------------------------------------------------------


def _constructor_battery_specs() -> list[dict]:
    """Small-n (<= ORACLE_N_CEILING) specs covering every constructor in
    ``ADMITTED_CONSTRUCTORS``."""
    small_h1 = [[1, 1, 0], [0, 1, 1]]
    small_h2 = [[1, 1]]
    rep3 = [[1, 1, 0], [0, 1, 1], [1, 0, 1]]
    hamming = [
        [1, 0, 1, 0, 1, 0, 1],
        [0, 1, 1, 0, 0, 1, 1],
        [0, 0, 0, 1, 1, 1, 1],
    ]
    four_two_two = CodeState(
        (0, 1, 2, 3),
        (Row("a1", "X", (0, 1, 2, 3)), Row("b1", "Z", (0, 1, 2, 3))),
        frozenset({"a1", "b1"}),
    )
    pair_x = CodeState((0, 1, 2), (Row("a1", "X", (0, 1)),), frozenset({"a1"}))
    free1 = construct({"constructor": "L-FREE", "qubits": [0]})["state"]
    cpm_bx = [[(1, 0), (1, 1), (1, 0), (1, 1)]]
    cpm_bz = [[(1, 0), (1, 1), (1, 0), (1, 1)]]
    cpm2_state = construct(
        {"constructor": "L-PAIR-PARTITION", "p": 2, "blocks_x": cpm_bx, "blocks_z": cpm_bz}
    )["state"]

    def _tile(size, sector):
        return {
            "qubits": size,
            "X": [list(range(size))] if sector == "X" else [],
            "Z": [list(range(size))] if sector == "Z" else [],
        }

    surface_tiles = [_tile(4, "X"), _tile(4, "Z"), _tile(2, "X"), _tile(2, "Z")]
    surface_placements = [
        (0, [0, 1, 3, 4]),
        (1, [1, 2, 4, 5]),
        (1, [3, 4, 6, 7]),
        (0, [4, 5, 7, 8]),
        (3, [0, 3]),
        (3, [5, 8]),
        (2, [1, 2]),
        (2, [6, 7]),
    ]
    shift3 = [1, 2, 0]
    action3 = {"rows": [shift3], "cols": [shift3]}

    return [
        {
            "label": "L-HGP/small+cell",
            "spec": {
                "constructor": "L-HGP",
                "H1": small_h1,
                "H2": small_h2,
                "lift_witnesses": True,
                "constructor_cell": {
                    "constructor": "L-HGP",
                    "d1": 3,
                    "d2": 2,
                    "d1_T": None,
                    "d2_T": None,
                    "source": "exact classical distances of small_h1 and small_h2",
                },
            },
        },
        {
            "label": "L-LIFTED/z3",
            "spec": {
                "constructor": "L-LIFTED",
                "group": (3,),
                "A": [[[(0,), (1,)]]],
                "B": [[[(0,), (2,)], [(1,)]]],
            },
        },
        {
            "label": "L-GROUP-ALGEBRA/z2z3",
            "spec": {
                "constructor": "L-GROUP-ALGEBRA",
                "group": (2, 3),
                "a": [(0, 0), (1, 0), (0, 1)],
                "b": [(0, 0), (1, 1), (0, 2)],
            },
        },
        {
            "label": "A-CONCAT/422+cell",
            "spec": {
                "constructor": "A-CONCAT",
                "outer": four_two_two,
                "inner": four_two_two,
                "groups": [(0, 1), (2, 3)],
                "lift_witnesses": True,
                "constructor_cell": {
                    "constructor": "A-CONCAT",
                    "k_in": 2,
                    "d_out_X": 2,
                    "d_out_Z": 2,
                    "d_in_X": 2,
                    "d_in_Z": 2,
                    "source": "exact distances of [[4,2,2]] outer and inner codes",
                },
            },
        },
        {
            "label": "L-BALANCED/z3",
            "spec": {
                "constructor": "L-BALANCED",
                "group": (3,),
                "H1": rep3,
                "action1": action3,
                "H2": rep3,
                "action2": action3,
            },
        },
        {
            "label": "L-TANNER/steane7",
            "spec": {
                "constructor": "L-TANNER",
                "n": 7,
                "local_x": hamming,
                "local_z": hamming,
                "views_x": [[0, 1, 2, 3, 4, 5, 6]],
                "views_z": [[0, 1, 2, 3, 4, 5, 6]],
            },
        },
        {
            "label": "L-TILE/rotated-surface-9",
            "spec": {
                "constructor": "L-TILE",
                "tiles": surface_tiles,
                "placements": surface_placements,
                "identifications": [],
                "removed": [],
            },
        },
        {
            "label": "A-PRODUCT/422xpair+cell",
            "spec": {
                "constructor": "A-PRODUCT",
                "left": four_two_two,
                "right": pair_x,
                "lift_witnesses": True,
                "constructor_cell": {
                    "constructor": "A-PRODUCT",
                    "display_certificate": "exact small-factor Kunneth certificate",
                    "d_A_X": 2,
                    "d_A_Z": 2,
                    "d_B_X": 1,
                    "d_B_Z": 1,
                    "source": "exact distances of [[4,2,2]] and pair_x",
                },
            },
        },
        {
            "label": "A-DOUBLE/422-untwisted+cell",
            "spec": {
                "constructor": "A-DOUBLE",
                "state": four_two_two,
                "wiring": {},
                "conjugate": False,
                "lift_witnesses": True,
                "constructor_cell": {
                    "constructor": "A-DOUBLE",
                    "wiring_empty": True,
                    "conjugate": False,
                    "d_C_X": 2,
                    "d_C_Z": 2,
                    "source": "exact distances of [[4,2,2]]",
                },
            },
        },
        {
            "label": "A-DOUBLE/422-twisted",
            "spec": {
                "constructor": "A-DOUBLE",
                "state": four_two_two,
                "wiring": {"a1": [0, 1]},
                "conjugate": False,
            },
        },
        {
            "label": "L-NESTED-CSS/steane7+cell",
            "spec": {
                "constructor": "L-NESTED-CSS",
                "HX": hamming,
                "HZ": hamming,
                "lift_witnesses": True,
                "constructor_cell": {
                    "constructor": "L-NESTED-CSS",
                    "d_ker_HZ": 3,
                    "d_ker_HX": 3,
                    "source": "exact Steane [[7,1,3]] classical kernel distances",
                },
            },
        },
        {
            "label": "L-MAPPING-CONE/small",
            "spec": {
                "constructor": "L-MAPPING-CONE",
                "d_a": [[0]],
                "d_b": [[0], [0]],
                "f1": [[0, 1]],
                "f0": [[1]],
            },
        },
        {
            "label": "L-EMPTY/nullary",
            "spec": {"constructor": "L-EMPTY"},
        },
        {
            "label": "L-FREE/3qubits",
            "spec": {"constructor": "L-FREE", "qubits": [0, 1, 2]},
        },
        {
            "label": "A-PULLBACK/pair",
            "spec": {
                "constructor": "A-PULLBACK",
                "left": pair_x,
                "right": pair_x,
                "interface": free1,
                "phi1": {0: 0, 1: 0, 2: 0},
                "phi2": {0: 0, 1: 0, 2: 0},
            },
        },
        {
            "label": "A-PUSHOUT/pair",
            "spec": {
                "constructor": "A-PUSHOUT",
                "left": pair_x,
                "right": pair_x,
                "subcode": free1,
                "psi1": {0: 2},
                "psi2": {0: 0},
            },
        },
        {
            "label": "L-PAIR-PARTITION/cpm2",
            "spec": {
                "constructor": "L-PAIR-PARTITION",
                "p": 2,
                "blocks_x": cpm_bx,
                "blocks_z": cpm_bz,
            },
        },
        {
            "label": "PP-SCALE/cpm2-to-3",
            "spec": {
                "constructor": "PP-SCALE",
                "state": cpm2_state,
                "P": 3,
                "blocks_x": cpm_bx,
                "blocks_z": cpm_bz,
            },
        },
    ]


def _ref_domination_axes(cand: dict) -> tuple:
    order = {"certify": 0, "re-measure": 1, "prune": 2}
    ld = cand["ledger"]
    return (
        -order.get(cand["verdict"], 3),
        math.inf if ld.full.lower is None else ld.full.lower,
        math.inf if ld.sector["X"].lower is None else ld.sector["X"].lower,
        math.inf if ld.sector["Z"].lower is None else ld.sector["Z"].lower,
    )


def _ref_domination_prune_indices(batch: list[dict]) -> list[int]:
    axes = [_ref_domination_axes(c) for c in batch]
    keep = []
    for i, a in enumerate(axes):
        dominated = False
        for j, b in enumerate(axes):
            if i == j:
                continue
            if all(x >= y for x, y in zip(b, a)) and any(x > y for x, y in zip(b, a)):
                dominated = True
                break
        if not dominated:
            keep.append(i)
    return keep


def _ref_pareto_tuple(cand: dict) -> tuple:
    v_rank = {"certify": 0, "re-measure": 1, "prune": 2}.get(cand.get("verdict"), 3)
    ld = cand.get("ledger")
    d = ld.full.lower if (ld is not None and ld.full is not None) else None
    d_val = d if d is not None else 0
    k = cand.get("k")
    n = cand.get("n")
    k_term = -k if (isinstance(k, int) and not isinstance(k, bool)) else float("inf")
    n_term = n if (isinstance(n, int) and not isinstance(n, bool)) else float("inf")
    return (v_rank, -d_val, k_term, n_term, cand.get("w", 1), cand.get("connectivity", 1))


def _ref_pareto_dominates(a: dict, b: dict) -> bool:
    ta, tb = _ref_pareto_tuple(a), _ref_pareto_tuple(b)
    return all(x <= y for x, y in zip(ta, tb)) and any(x < y for x, y in zip(ta, tb))


def _ref_pareto_layers(batch: list[dict]) -> dict[int, int]:
    remaining = list(range(len(batch)))
    layers = {}
    layer_idx = 0
    while remaining:
        front = [
            i
            for i in remaining
            if not any(_ref_pareto_dominates(batch[j], batch[i]) for j in remaining if j != i)
        ]
        if not front:
            front = list(remaining)
        for i in front:
            layers[i] = layer_idx
            remaining.remove(i)
        layer_idx += 1
    return layers


def run_quadrant_1_oracle_differential(
    recorder: ViolationRecorder,
    seed: int,
    *,
    small_trials: int = 25,
    pareto_trials: int = 30,
    budget_seconds: float | None = None,
) -> dict:
    """Quadrant 1: all 17 admitted constructors, Pareto/domination brute-force
    cross-check, and small-n planner/search oracle differential."""
    # Oracle is imported ONLY inside the verifier helper, never by consumer/planner.
    from machine.oracle import ORACLE_N_CEILING, exact_distances

    t0 = time.monotonic()
    rng = random.Random(seed + 101)

    # 1a. All 17 admitted constructors
    specs = _constructor_battery_specs()
    covered_constructors = set()
    constructor_checks = 0
    for item in specs:
        label = item["label"]
        spec = item["spec"]
        cname = spec["constructor"]
        covered_constructors.add(cname)
        try:
            res = construct(spec)
            st = res["state"]
            st.validate()
        except Exception as exc:
            recorder.record(
                f"q1-constructor-failed-{label}",
                "q1_oracle_differential",
                "constructor_eval",
                f"{label} raised unexpectedly: {exc!r}",
                extra={"constructor": cname},
            )
            continue
        constructor_checks += 1
        expected_k = _exact_k_from_state(st)
        if st.k() != expected_k or res["k"] != expected_k or st.n() != len(st.Q):
            recorder.record(
                f"q1-constructor-params-{label}",
                "q1_oracle_differential",
                "constructor_params",
                f"{label}: k={st.k()} res_k={res['k']} expected_k={expected_k} n={st.n()}",
                state=st,
            )

        # Bare constructed ledger must start at [0, +inf) on all three intervals.
        bare_ld = DistanceLedger.for_constructed(st)
        for name_iv, iv in (
            ("full", bare_ld.full),
            ("X", bare_ld.sector["X"]),
            ("Z", bare_ld.sector["Z"]),
        ):
            if iv != Interval(0, None):
                recorder.record(
                    f"q1-constructor-bare-ledger-{label}-{name_iv}",
                    "q1_oracle_differential",
                    "for_constructed_default",
                    f"{label}: expected [0, None] on {name_iv}, got {iv}",
                    state=st,
                )

        if st.n() > ORACLE_N_CEILING:
            recorder.record(
                f"q1-constructor-above-oracle-ceiling-{label}",
                "q1_oracle_differential",
                "constructor_oracle_ceiling",
                f"{label}: n={st.n()} exceeds ORACLE_N_CEILING={ORACLE_N_CEILING}",
                state=st,
            )
            continue

        ex = exact_distances(st)

        # Check conditional constructor cell / lifted witnesses ledger if returned.
        if "ledger" in res:
            c_ld = res["ledger"]
            for side, exact_val, iv in (
                ("d", ex["d"], c_ld.full),
                ("X", ex["X"], c_ld.sector["X"]),
                ("Z", ex["Z"], c_ld.sector["Z"]),
            ):
                if not _interval_contains(iv, exact_val):
                    recorder.record(
                        f"q1-constructor-ledger-unsound-{label}-{side}",
                        "q1_oracle_differential",
                        "constructor_ledger_oracle",
                        f"{label} {side}: ledger {iv} does not contain exact {exact_val}",
                        state=st,
                        extra={"ledger": serialize_ledger(c_ld), "exact": ex},
                    )

        # Tighten via bounded_support_search when n > 0 and verify against oracle.
        if st.n() > 0:
            tight_ld, srec = tighten_ledger_with_search(
                st, bare_ld, budget=512, max_weight=min(4, st.n())
            )
            for side, exact_val, iv in (
                ("d", ex["d"], tight_ld.full),
                ("X", ex["X"], tight_ld.sector["X"]),
                ("Z", ex["Z"], tight_ld.sector["Z"]),
            ):
                if not _interval_contains(iv, exact_val):
                    recorder.record(
                        f"q1-constructor-tightened-unsound-{label}-{side}",
                        "q1_oracle_differential",
                        "constructor_search_oracle",
                        f"{label} {side}: tightened {iv} does not contain exact {exact_val}",
                        state=st,
                        extra={"exact": ex, "search": srec},
                    )
            if st.k() == 0:
                if (
                    tight_ld.full != Interval(None, None)
                    or tight_ld.sector["X"] != Interval(None, None)
                    or tight_ld.sector["Z"] != Interval(None, None)
                ):
                    recorder.record(
                        f"q1-constructor-k0-not-vacuous-{label}",
                        "q1_oracle_differential",
                        "k0_vacuous_distance",
                        f"{label}: k=0 state did not canonicalize to [inf, inf]: {tight_ld.as_json()}",
                        state=st,
                    )
            elif (
                tight_ld.full.lower != 0
                or tight_ld.sector["X"].lower != 0
                or tight_ld.sector["Z"].lower != 0
            ):
                recorder.record(
                    f"q1-constructor-search-moved-lower-{label}",
                    "q1_oracle_differential",
                    "search_never_raises_lower",
                    f"{label}: tighten_ledger_with_search moved a lower endpoint: {tight_ld.as_json()}",
                    state=st,
                )

    missing_constructors = sorted(set(ADMITTED_CONSTRUCTORS) - covered_constructors)
    if missing_constructors:
        recorder.record(
            "q1-missing-admitted-constructors",
            "q1_oracle_differential",
            "constructor_coverage",
            f"ADMITTED_CONSTRUCTORS missing from Q1 battery: {missing_constructors}",
        )

    # 1b. Brute-force Pareto & domination cross-check
    pareto_batches_checked = 0
    pareto_pairs_checked = 0
    verdict_choices = ("certify", "re-measure", "prune")
    for trial in range(pareto_trials):
        size = rng.randint(0, 16)
        batch = []
        for idx in range(size):
            if rng.random() < 0.15:
                xl, xu = None, None
            else:
                xl = rng.randint(0, 5)
                xu = None if rng.random() < 0.4 else xl + rng.randint(0, 4)
            if rng.random() < 0.15:
                zl, zu = None, None
            else:
                zl = rng.randint(0, 5)
                zu = None if rng.random() < 0.4 else zl + rng.randint(0, 4)
            lowers = [v for v in (xl, zl) if v is not None]
            uppers = [v for v in (xu, zu) if v is not None]
            fl = min(lowers) if lowers else None
            fu = min(uppers) if uppers else None
            if fl is None:
                fu = None
            elif fu is not None and fu < fl:
                fu = fl
            ld = DistanceLedger(Interval(fl, fu), {"X": Interval(xl, xu), "Z": Interval(zl, zu)})
            cand = {
                "id": idx,
                "verdict": rng.choice(verdict_choices),
                "ledger": ld,
                "k": rng.randint(0, 6) if rng.random() > 0.1 else None,
                "n": rng.randint(2, 20) if rng.random() > 0.1 else None,
                "w": rng.randint(1, 6),
                "connectivity": rng.randint(1, 3),
            }
            batch.append(cand)

        pareto_batches_checked += 1
        # domination_prune check
        got_dom_ids = [c["id"] for c in domination_prune(batch)]
        ref_dom_ids = [batch[i]["id"] for i in _ref_domination_prune_indices(batch)]
        if got_dom_ids != ref_dom_ids:
            recorder.record(
                f"q1-domination-prune-mismatch-{trial}",
                "q1_oracle_differential",
                "domination_prune_bruteforce",
                f"trial {trial}: got {got_dom_ids} != ref {ref_dom_ids}",
            )

        # pairwise pareto_dominates check
        for a in batch:
            for b in batch:
                pareto_pairs_checked += 1
                got_d = pareto_dominates(a, b)
                ref_d = _ref_pareto_dominates(a, b)
                if got_d != ref_d:
                    recorder.record(
                        f"q1-pareto-dominates-mismatch-{trial}",
                        "q1_oracle_differential",
                        "pareto_dominates_bruteforce",
                        f"trial {trial}: a={a['id']} b={b['id']} got={got_d} ref={ref_d}",
                    )
                    break

        # pareto_front check
        ref_layers = _ref_pareto_layers(batch)
        got_front_ids = [c["id"] for c in pareto_front(batch)]
        ref_front_ids = [batch[i]["id"] for i in range(len(batch)) if ref_layers[i] == 0]
        if got_front_ids != ref_front_ids:
            recorder.record(
                f"q1-pareto-front-mismatch-{trial}",
                "q1_oracle_differential",
                "pareto_front_bruteforce",
                f"trial {trial}: got {got_front_ids} != ref {ref_front_ids}",
            )

        # pareto_annotate non-destructive & layer match
        snap_keys = [set(c.keys()) for c in batch]
        annotated = pareto_annotate(batch)
        if [set(c.keys()) for c in batch] != snap_keys:
            recorder.record(
                f"q1-pareto-annotate-mutated-{trial}",
                "q1_oracle_differential",
                "pareto_annotate_non_destructive",
                f"trial {trial}: pareto_annotate mutated input batch",
            )
        for i, item in enumerate(annotated):
            if item["pareto_layer"] != ref_layers[i] or item["pareto_dominated"] != (ref_layers[i] > 0):
                recorder.record(
                    f"q1-pareto-annotate-layer-{trial}",
                    "q1_oracle_differential",
                    "pareto_annotate_bruteforce",
                    f"trial {trial} idx {i}: got layer={item['pareto_layer']} ref={ref_layers[i]}",
                )
                break

        # pareto_rank layer monotonicity & membership
        ranked_input = [dict(c) for c in batch]
        ranked = pareto_rank(ranked_input)
        if sorted(c["id"] for c in ranked) != sorted(c["id"] for c in batch):
            recorder.record(
                f"q1-pareto-rank-membership-{trial}",
                "q1_oracle_differential",
                "pareto_rank_membership",
                f"trial {trial}: pareto_rank dropped or duplicated candidates",
            )
        layers_seen = [c["pareto_layer"] for c in ranked]
        if layers_seen != sorted(layers_seen):
            recorder.record(
                f"q1-pareto-rank-order-{trial}",
                "q1_oracle_differential",
                "pareto_rank_layer_order",
                f"trial {trial}: pareto_rank layers not non-decreasing: {layers_seen}",
            )
        for c in ranked:
            if c["pareto_layer"] != ref_layers[c["id"]]:
                recorder.record(
                    f"q1-pareto-rank-layer-{trial}",
                    "q1_oracle_differential",
                    "pareto_rank_bruteforce",
                    f"trial {trial} id={c['id']}: got layer={c['pareto_layer']} ref={ref_layers[c['id']]}",
                )
                break

    # 1c. Small-n planner + support_search oracle differential
    planner_trials_run = 0
    planner_children_checked = 0
    verdict_counts = Counter()
    for trial in range(small_trials):
        n = rng.randint(4, 8)
        st = _random_css_state(rng, n)
        if st.k() <= 0:
            continue
        ex_parent = exact_distances(st)
        if ex_parent["d"] is None:
            continue
        planner_trials_run += 1

        # Seed parent ledger soundly using exact parent bounds (mix zero and nonzero lower).
        mode = trial % 3
        if mode == 0:
            lx, lz, ld_val = 0, 0, 0
        elif mode == 1:
            lx = max(0, (ex_parent["X"] or 1) - 1)
            lz = max(0, (ex_parent["Z"] or 1) - 1)
            ld_val = min(lx, lz)
        else:
            lx = ex_parent["X"] or 0
            lz = ex_parent["Z"] or 0
            ld_val = ex_parent["d"] or 0
        ld = DistanceLedger(
            Interval(ld_val, ex_parent["d"]),
            {
                "X": Interval(lx, ex_parent["X"]),
                "Z": Interval(lz, ex_parent["Z"]),
            },
            witnesses={"X": [], "Z": []},
            conditions=[{"cell": "input lower bound", "source": "q1 small-n oracle seed"}]
            if ld_val > 0
            else [],
        )
        target = max(1 if trial % 2 == 0 else 2, ex_parent["d"])
        max_w = min(4, n)
        cands = plan(
            st,
            ld,
            target=target,
            structural=True,
            reduce_display=True,
            reduce_by_domination=False,
            include_disconnected=True,
            support_search={"budget": 512, "max_weight": max_w},
            sector_swap=True,
            sector_targeted=True,
            target_sector="X",
            ranking="pareto",
        )
        for cand in cands:
            child = cand["state"]
            cld = cand["ledger"]
            verdict = cand["verdict"]
            verdict_counts[verdict] += 1
            planner_children_checked += 1
            ex_child = exact_distances(child)

            for side, exact_val, iv in (
                ("d", ex_child["d"], cld.full),
                ("X", ex_child["X"], cld.sector["X"]),
                ("Z", ex_child["Z"], cld.sector["Z"]),
            ):
                if not _interval_contains(iv, exact_val):
                    recorder.record(
                        f"q1-plan-interval-unsound-{trial}-{side}",
                        "q1_oracle_differential",
                        "plan_interval_contains_exact",
                        f"trial {trial} op={cand['operation']} {side}: {iv} misses exact {exact_val}",
                        state=st,
                        move_sequence=[cand["operation"]],
                        extra={"child": serialize_state(child), "exact": ex_child},
                    )

            if verdict == "certify" and ex_child["d"] is not None and ex_child["d"] < target:
                recorder.record(
                    f"q1-plan-certify-contradicted-{trial}",
                    "q1_oracle_differential",
                    "plan_certify_soundness",
                    f"trial {trial}: verdict=certify for target={target} but exact d={ex_child['d']}",
                    state=st,
                    move_sequence=[cand["operation"]],
                )
            if verdict == "prune" and (ex_child["d"] is None or ex_child["d"] >= target):
                recorder.record(
                    f"q1-plan-prune-contradicted-{trial}",
                    "q1_oracle_differential",
                    "plan_prune_soundness",
                    f"trial {trial}: verdict=prune for target={target} but exact d={ex_child['d']}",
                    state=st,
                    move_sequence=[cand["operation"]],
                )

            ss = cand.get("support_search")
            if ss is not None:
                for side in ("X", "Z"):
                    wit = ss["witnesses"].get(side)
                    exact_s = ex_child[side]
                    if wit is not None:
                        if exact_s is None or wit["value"] < exact_s:
                            recorder.record(
                                f"q1-search-witness-lighter-than-exact-{trial}-{side}",
                                "q1_oracle_differential",
                                "support_search_witness_soundness",
                                f"trial {trial} {side}: witness weight {wit['value']} < exact {exact_s}",
                                state=child,
                                move_sequence=[cand["operation"]],
                            )
                        try:
                            validate_witness(child, side, tuple(wit["support"]), wit["value"])
                        except (Malformed, NoDerivation) as exc:
                            recorder.record(
                                f"q1-search-witness-invalid-{trial}-{side}",
                                "q1_oracle_differential",
                                "support_search_witness_valid",
                                f"trial {trial} {side}: witness rejected by validate_witness: {exc}",
                                state=child,
                                move_sequence=[cand["operation"]],
                            )
                    elif (
                        not ss["exhausted"]
                        and exact_s is not None
                        and exact_s <= ss["max_weight"]
                    ):
                        recorder.record(
                            f"q1-search-missed-exact-within-cap-{trial}-{side}",
                            "q1_oracle_differential",
                            "support_search_exhaustiveness",
                            f"trial {trial} {side}: non-exhausted search missed exact_d={exact_s} <= max_weight={ss['max_weight']}",
                            state=child,
                            move_sequence=[cand["operation"]],
                        )

    elapsed = time.monotonic() - t0
    return {
        "transition_differential_owner": "machine/experiments/priced_conformance_harness.py",
        "admitted_constructors_expected": len(ADMITTED_CONSTRUCTORS),
        "admitted_constructors_covered": len(covered_constructors),
        "constructor_instances_checked": constructor_checks,
        "pareto_batches_checked": pareto_batches_checked,
        "pareto_pairs_checked": pareto_pairs_checked,
        "small_n_planner_trials": planner_trials_run,
        "small_n_planner_children_checked": planner_children_checked,
        "small_n_verdict_counts": dict(sorted(verdict_counts.items())),
        **_timing_metrics("q1_oracle_differential", elapsed, budget_seconds),
    }


# ---------------------------------------------------------------------------
# Quadrant 2: Gate differential at medium n (vprusso #3)
# ---------------------------------------------------------------------------


def _verify_challenge_checkout(challenge_root: Path, allow_any_commit: bool = False) -> str:
    sha = subprocess.check_output(
        ["git", "-C", str(challenge_root), "rev-parse", "HEAD"], text=True
    ).strip()
    if not allow_any_commit and sha != Q_LDPC_SHA:
        raise RuntimeError(
            f"expected pinned qLDPC commit {Q_LDPC_SHA}, got {sha} "
            "(pass --allow-any-commit to override locally)"
        )
    dirty = subprocess.run(
        ["git", "-C", str(challenge_root), "status", "--porcelain"],
        capture_output=True,
        text=True,
        check=False,
    )
    if dirty.returncode != 0 or dirty.stdout.strip():
        raise RuntimeError(
            f"qLDPC checkout at {challenge_root} is dirty or not a git checkout"
        )
    return sha


def _invoke_pinned_verifier(challenge_root: Path, doc: dict, tmp_dir: Path, label: str) -> dict:
    path = tmp_dir / f"{label}.json"
    path.write_text(json.dumps(doc, indent=2) + "\n")
    verifier = challenge_root / "verify" / "qldpc_verify.py"
    proc = subprocess.run(
        [sys.executable, str(verifier), str(path)],
        capture_output=True,
        text=True,
        check=False,
    )
    try:
        report = json.loads(proc.stdout)
    except (json.JSONDecodeError, ValueError) as exc:
        raise RuntimeError(
            f"qldpc_verify.py produced invalid JSON for {label}: {exc}; stderr={proc.stderr!r}"
        ) from exc
    return {"returncode": proc.returncode, "report": report}


def _parse_refuted_weight(detail: str) -> int | None:
    match = re.search(r"found weight-(\d+) logical", detail or "")
    return int(match.group(1)) if match else None


def _classify_gate_report(verdict: str, target: int, rep: dict) -> dict:
    """Classify one pinned ``verify/qldpc_verify.py`` JSON report against a
    planner verdict and target distance."""
    checks_by_name = {c["check"]: c for c in rep.get("checks", [])}
    failed_struct = [
        name
        for name in sorted(REQUIRED_GATE_STRUCTURAL_CHECKS)
        if name in checks_by_name and not checks_by_name[name]["ok"]
    ]
    earned_d = (rep.get("earned_distance") or {}).get("d", {}).get("value")
    refute_chk = checks_by_name.get("distance_not_refuted")
    refuted_w = (
        _parse_refuted_weight(refute_chk.get("detail", ""))
        if (refute_chk is not None and not refute_chk.get("ok"))
        else None
    )
    outcome = "other"
    if verdict == "prune":
        if not failed_struct and (
            (earned_d is not None and earned_d < target)
            or (refuted_w is not None and refuted_w < target)
        ):
            outcome = "prune_confirmed"
        else:
            outcome = "prune_contradicted"
    elif verdict == "re-measure":
        if refuted_w is not None and refuted_w < target:
            outcome = "remeasure_refuted_below_target"
        else:
            outcome = "remeasure_unrefuted"
    return {
        "checks_by_name": checks_by_name,
        "failed_struct": failed_struct,
        "earned_d": earned_d,
        "refuted_w": refuted_w,
        "outcome": outcome,
    }


def run_quadrant_2_gate_differential(
    recorder: ViolationRecorder,
    seed: int,
    challenge_root: Path,
    *,
    max_verify_per_parent: int = 8,
    parents: tuple[str, ...] = MEDIUM_PARENTS,
    verifier_fn=None,
    run_certify_check: bool = True,
    budget_seconds: float | None = None,
) -> dict:
    """Quadrant 2: run planner on medium-n pinned challenge parents, export via
    ``export_challenge_entry``, cross-check with pinned ``verify/qldpc_verify.py``,
    and compute operational prune precision and re-measure rate."""
    t0 = time.monotonic()
    verifier = _invoke_pinned_verifier if verifier_fn is None else verifier_fn
    total_candidates = 0
    total_verdicts = Counter()
    exported_checked = 0
    structural_pass = 0
    prune_confirmed = 0
    prune_contradicted = 0
    single_side_pruned_unexported = 0
    remeasure_exported = 0
    remeasure_refuted_below_target = 0
    remeasure_unrefuted = 0
    certify_checked = 0
    certify_contradicted = 0
    per_parent = []

    with tempfile.TemporaryDirectory(prefix="stress-q2-gate-") as tmp:
        tmp_dir = Path(tmp)
        for parent_name in parents:
            doc = json.loads((challenge_root / "codes" / parent_name).read_text())
            st = CodeState.from_challenge(doc)
            ld = DistanceLedger.from_challenge(st, doc)
            target = doc["distance"]["d"]

            cands = plan(
                st,
                ld,
                target=target,
                structural=True,
                reduce_display=True,
                reduce_by_domination=False,
                support_search={"budget": 256, "max_weight": 4},
                sector_swap=True,
                ranking="pareto",
            )
            p_verdicts = Counter(c["verdict"] for c in cands)
            total_candidates += len(cands)
            total_verdicts.update(p_verdicts)

            # Separate exportable vs single-side pruned candidates.
            exportable_prune = []
            exportable_remeasure = []
            for cand in cands:
                has_both = bool(cand["ledger"].witnesses["X"] and cand["ledger"].witnesses["Z"])
                if not has_both:
                    if cand["verdict"] == "prune":
                        single_side_pruned_unexported += 1
                        # Still verify that whichever side caused upper < target has a valid witness.
                        found_valid_below = False
                        for side in ("X", "Z"):
                            for w in cand["ledger"].witnesses[side]:
                                try:
                                    validate_witness(
                                        cand["state"], side, tuple(w["support"]), w["value"]
                                    )
                                    if w["value"] < target:
                                        found_valid_below = True
                                except (Malformed, NoDerivation) as exc:
                                    recorder.record(
                                        f"q2-single-side-invalid-witness-{parent_name}",
                                        "q2_gate_differential",
                                        "single_side_witness_valid",
                                        f"{parent_name}: invalid witness {w}: {exc}",
                                        state=cand["state"],
                                        move_sequence=[cand["operation"]],
                                    )
                        if not found_valid_below:
                            recorder.record(
                                f"q2-single-side-prune-unbacked-{parent_name}",
                                "q2_gate_differential",
                                "single_side_prune_backed",
                                f"{parent_name}: pruned without a witness < target={target}",
                                state=cand["state"],
                                move_sequence=[cand["operation"]],
                            )
                    continue
                if cand["verdict"] == "prune":
                    exportable_prune.append(cand)
                elif cand["verdict"] == "re-measure":
                    exportable_remeasure.append(cand)

            # Balanced deterministic slice for verifier invocation.
            half = max(1, max_verify_per_parent // 2)
            selected = exportable_prune[:half] + exportable_remeasure[:half]
            if len(selected) < max_verify_per_parent:
                extra_pool = exportable_prune[half:] + exportable_remeasure[half:]
                selected.extend(extra_pool[: max_verify_per_parent - len(selected)])

            p_verified = 0
            p_prune_confirmed = 0
            p_prune_contradicted = 0
            for idx, cand in enumerate(selected):
                exported = export_challenge_entry(
                    doc,
                    cand["state"],
                    cand["ledger"],
                    f"stress-q2-{parent_name}-{idx}",
                    f"stress_campaign {cand['operation'].get('op')}",
                    "2026-11-25",
                )
                vres = verifier(
                    challenge_root, exported, tmp_dir, f"{parent_name.replace('.json', '')}_{idx}"
                )
                rep = vres["report"]
                exported_checked += 1
                p_verified += 1
                classified = _classify_gate_report(cand["verdict"], target, rep)
                checks_by_name = classified["checks_by_name"]
                failed_struct = classified["failed_struct"]
                earned_d = classified["earned_d"]
                refuted_w = classified["refuted_w"]
                if failed_struct:
                    recorder.record(
                        f"q2-verifier-structural-fail-{parent_name}-{idx}",
                        "q2_gate_differential",
                        "gate_structural_validity",
                        f"{parent_name} cand {idx} failed gate checks {failed_struct}",
                        state=cand["state"],
                        move_sequence=[cand["operation"]],
                        extra={"failed_checks": [checks_by_name[n] for n in failed_struct]},
                    )
                else:
                    structural_pass += 1

                if classified["outcome"] == "prune_confirmed":
                    prune_confirmed += 1
                    p_prune_confirmed += 1
                elif classified["outcome"] == "prune_contradicted":
                    prune_contradicted += 1
                    p_prune_contradicted += 1
                    recorder.record(
                        f"q2-prune-contradicted-{parent_name}-{idx}",
                        "q2_gate_differential",
                        "gate_prune_precision",
                        f"{parent_name} cand {idx}: planner pruned target={target}, "
                        f"gate earned_d={earned_d}, refuted_w={refuted_w}, failed_struct={failed_struct}",
                        state=cand["state"],
                        move_sequence=[cand["operation"]],
                    )
                elif classified["outcome"] == "remeasure_refuted_below_target":
                    remeasure_exported += 1
                    remeasure_refuted_below_target += 1
                elif classified["outcome"] == "remeasure_unrefuted":
                    remeasure_exported += 1
                    remeasure_unrefuted += 1

            per_parent.append(
                {
                    "parent": f"codes/{parent_name}",
                    "n": st.n(),
                    "k": st.k(),
                    "target": target,
                    "candidates": len(cands),
                    "verdicts": dict(sorted(p_verdicts.items())),
                    "remeasure_rate": round(
                        p_verdicts["re-measure"] / len(cands), 4
                    )
                    if cands
                    else 0.0,
                    "gate_verified": p_verified,
                    "prune_confirmed": p_prune_confirmed,
                    "prune_contradicted": p_prune_contradicted,
                }
            )

        # Sourced-certify gate consistency check on codes/10-2-3-b.json:
        # C-ADD-CHECK X [0, 8, 9] keeps d >= 3 by monotonicity; gate must NOT
        # refute target=3.
        if run_certify_check:
            doc10 = json.loads((challenge_root / "codes" / "10-2-3-b.json").read_text())
            st10 = CodeState.from_challenge(doc10)
            ld10 = DistanceLedger.from_challenge(
                st10,
                doc10,
                lower_bounds={
                    "X": {"value": 3, "source": "pinned codes/10-2-3-b.json known exact distance"},
                    "Z": {"value": 3, "source": "pinned codes/10-2-3-b.json known exact distance"},
                    "d": {"value": 3, "source": "pinned codes/10-2-3-b.json known exact distance"},
                },
            )
            add_op = {"op": "C-ADD-CHECK", "sector": "X", "support": [0, 8, 9]}
            child10 = apply_operation(st10, add_op)
            ss10 = bounded_support_search(child10, budget=512, max_weight=4)
            obs10 = {
                side: w["support"]
                for side, w in ss10["witnesses"].items()
                if w is not None
            }
            cld10 = ld10.propagate(add_op, child10, parent_state=st10, observations=obs10)
            if cld10.decide(3) != "certify":
                recorder.record(
                    "q2-certify-fixture-did-not-certify",
                    "q2_gate_differential",
                    "gate_certify_consistency",
                    f"expected certify for C-ADD-CHECK on 10-2-3-b, got {cld10.decide(3)}",
                    state=child10,
                    move_sequence=[add_op],
                )
            else:
                exp10 = export_challenge_entry(
                    doc10,
                    child10,
                    cld10,
                    "stress-q2-certify-10-1-3",
                    "C-ADD-CHECK X [0,8,9] certify consistency check",
                    "2026-11-25",
                )
                vres10 = verifier(challenge_root, exp10, tmp_dir, "certify_10_1_3")
                rep10 = vres10["report"]
                certify_checked += 1
                checks10 = {c["check"]: c for c in rep10.get("checks", [])}
                refute10 = checks10.get("distance_not_refuted")
                if not rep10.get("ok") or (refute10 is not None and not refute10.get("ok")):
                    certify_contradicted += 1
                    recorder.record(
                        "q2-certify-contradicted-by-gate",
                        "q2_gate_differential",
                        "gate_certify_consistency",
                        f"gate rejected or refuted certified child: {rep10}",
                        state=child10,
                        move_sequence=[add_op],
                    )

    denom = prune_confirmed + prune_contradicted
    prune_precision = round(prune_confirmed / denom, 4) if denom else None
    remeasure_rate = (
        round(total_verdicts["re-measure"] / total_candidates, 4)
        if total_candidates
        else 0.0
    )
    elapsed = time.monotonic() - t0
    return {
        "prune_precision_definition": PRUNE_PRECISION_DEFINITION,
        "parents_tested": len(parents),
        "total_candidates": total_candidates,
        "verdict_counts": dict(sorted(total_verdicts.items())),
        "remeasure_rate": remeasure_rate,
        "gate_exported_checked": exported_checked,
        "gate_structural_pass": structural_pass,
        "prune_confirmed_by_gate": prune_confirmed,
        "prune_contradicted_by_gate": prune_contradicted,
        "single_side_pruned_unexported": single_side_pruned_unexported,
        "prune_precision": prune_precision,
        "remeasure_exported": remeasure_exported,
        "remeasure_refuted_below_target": remeasure_refuted_below_target,
        "remeasure_unrefuted_by_gate": remeasure_unrefuted,
        "certify_checked": certify_checked,
        "certify_contradicted": certify_contradicted,
        "per_parent": per_parent,
        **_timing_metrics("q2_gate_differential", elapsed, budget_seconds),
    }


# ---------------------------------------------------------------------------
# Quadrant 3: Invariant fuzzing across all n (vprusso #7)
# ---------------------------------------------------------------------------


def _assert_heuristic_outcome_shape(recorder: ViolationRecorder, quadrant: str, label: str, outcome, state=None):
    if not isinstance(outcome, dict):
        recorder.record(
            f"{quadrant}-heuristic-missing-{label}",
            quadrant,
            "heuristic_outcome_shape",
            f"{label}: expected dict heuristic_outcome, got {type(outcome).__name__}",
            state=state,
        )
        return
    if outcome.get("claim_shape") != "probabilistic":
        recorder.record(
            f"{quadrant}-heuristic-shape-{label}",
            quadrant,
            "heuristic_outcome_shape",
            f"{label}: expected claim_shape='probabilistic', got {outcome.get('claim_shape')!r}",
            state=state,
        )
    if outcome.get("evidence_status") != "empirical":
        recorder.record(
            f"{quadrant}-heuristic-status-{label}",
            quadrant,
            "heuristic_outcome_shape",
            f"{label}: expected evidence_status='empirical', got {outcome.get('evidence_status')!r}",
            state=state,
        )
    delta = outcome.get("delta")
    if isinstance(delta, bool) or not isinstance(delta, (int, float)) or not (0 <= delta <= 1):
        recorder.record(
            f"{quadrant}-heuristic-delta-{label}",
            quadrant,
            "heuristic_outcome_shape",
            f"{label}: invalid delta={delta!r}",
            state=state,
        )
    if not isinstance(outcome.get("licenses"), str) or "no ledger endpoint" not in outcome["licenses"]:
        recorder.record(
            f"{quadrant}-heuristic-licenses-{label}",
            quadrant,
            "heuristic_outcome_shape",
            f"{label}: missing non-endpoint license statement: {outcome.get('licenses')!r}",
            state=state,
        )


def _check_plan_candidate_invariants(
    recorder: ViolationRecorder,
    quadrant: str,
    label: str,
    working_parent: CodeState,
    cand: dict,
):
    child = cand["state"]
    op = cand["operation"]
    try:
        child.validate()
    except Exception as exc:
        recorder.record(
            f"{quadrant}-child-invalid-{label}",
            quadrant,
            "child_validate",
            f"{label}: child failed validate(): {exc!r}",
            state=working_parent,
            move_sequence=[op],
        )
        return
    if cand["n"] != child.n() or cand["n"] != len(child.Q):
        recorder.record(
            f"{quadrant}-param-n-mismatch-{label}",
            quadrant,
            "planner_n_matches_state",
            f"{label}: cand n={cand['n']} != state.n()={child.n()}",
            state=working_parent,
            move_sequence=[op],
        )
    exact_k = _exact_k_from_state(child)
    if cand["k"] != child.k() or cand["k"] != exact_k:
        recorder.record(
            f"{quadrant}-param-k-mismatch-{label}",
            quadrant,
            "planner_k_matches_state",
            f"{label}: cand k={cand['k']} state.k()={child.k()} exact_k={exact_k}",
            state=working_parent,
            move_sequence=[op],
        )
    comp = tanner_components(child)
    if cand["connectivity"] != comp:
        recorder.record(
            f"{quadrant}-param-conn-mismatch-{label}",
            quadrant,
            "planner_connectivity_matches_state",
            f"{label}: cand connectivity={cand['connectivity']} != tanner_components={comp}",
            state=working_parent,
            move_sequence=[op],
        )
    # Expected planner op weight (machine/planner.py): deleted row support size
    # for C-DELETE-CHECK, len(qubits) or 1 for E-LOCAL-HADAMARD, 1 otherwise.
    op_name = op.get("op")
    expected_w = 1
    if op_name == "C-DELETE-CHECK":
        for row in working_parent.rows:
            if row.id == op.get("row_id"):
                expected_w = len(row.support)
                break
    elif op_name == "E-LOCAL-HADAMARD":
        expected_w = len(op.get("qubits", [])) or 1
    if cand["w"] != expected_w:
        recorder.record(
            f"{quadrant}-param-w-mismatch-{label}",
            quadrant,
            "planner_w_matches_op",
            f"{label}: cand w={cand['w']} != expected_w={expected_w} for {op_name}",
            state=working_parent,
            move_sequence=[op],
        )


def _check_hadamard_roundtrip(
    recorder: ViolationRecorder, quadrant: str, label: str, state: CodeState, ledger: DistanceLedger
):
    op = {"op": "E-LOCAL-HADAMARD", "qubits": list(state.Q)}
    h1 = apply_operation(state, op)
    l1 = ledger.propagate(op, h1, parent_state=state)
    h2 = apply_operation(h1, op)
    l2 = l1.propagate(op, h2, parent_state=h1)
    if h2.rows != state.rows or h2.Q != state.Q:
        recorder.record(
            f"{quadrant}-hadamard-state-roundtrip-{label}",
            quadrant,
            "hadamard_roundtrip",
            f"{label}: double E-LOCAL-HADAMARD(T=Q) did not restore state rows/Q",
            state=state,
            move_sequence=[op, op],
        )
    if state.k() == 0:
        expected_1 = (Interval(None, None), Interval(None, None), Interval(None, None))
        expected_2 = expected_1
    else:
        expected_1 = (ledger.full, ledger.sector["Z"], ledger.sector["X"])
        expected_2 = (ledger.full, ledger.sector["X"], ledger.sector["Z"])
    if (
        (l1.full, l1.sector["X"], l1.sector["Z"]) != expected_1
        or (l2.full, l2.sector["X"], l2.sector["Z"]) != expected_2
    ):
        recorder.record(
            f"{quadrant}-hadamard-ledger-roundtrip-{label}",
            quadrant,
            "hadamard_roundtrip",
            f"{label}: E-LOCAL-HADAMARD(T=Q) ledger swap/round-trip mismatch",
            state=state,
            move_sequence=[op, op],
            extra={
                "orig": serialize_ledger(ledger),
                "step1": serialize_ledger(l1),
                "step2": serialize_ledger(l2),
            },
        )


def _check_rebase_interval_inert(
    recorder: ViolationRecorder, quadrant: str, label: str, state: CodeState, ledger: DistanceLedger
) -> bool:
    for sector in ("X", "Z"):
        rows = state.sector_rows(sector)
        m = len(rows)
        if m < 2:
            continue
        matrix = [[1 if a == b else 0 for b in range(m)] for a in range(m)]
        matrix[0][1] = 1
        op = {"op": "P-REBASE", "sector": sector, "matrix": matrix}
        child = apply_operation(state, op)
        child_ld = ledger.propagate(op, child, parent_state=state)
        if child.n() != state.n() or child.k() != state.k():
            recorder.record(
                f"{quadrant}-rebase-params-{label}",
                quadrant,
                "rebase_interval_inert",
                f"{label}: P-REBASE altered n/k ({state.n()},{state.k()}) -> ({child.n()},{child.k()})",
                state=state,
                move_sequence=[op],
            )
        if state.k() == 0:
            expected_full = Interval(None, None)
            expected_sector = {"X": Interval(None, None), "Z": Interval(None, None)}
        else:
            expected_full = ledger.full
            expected_sector = ledger.sector
        if child_ld.full != expected_full or child_ld.sector != expected_sector:
            recorder.record(
                f"{quadrant}-rebase-ledger-moved-{label}",
                quadrant,
                "rebase_interval_inert",
                f"{label}: P-REBASE moved intervals {ledger.as_json()} -> {child_ld.as_json()}",
                state=state,
                move_sequence=[op],
            )
        return True
    return False


def run_quadrant_3_invariant_fuzzing(
    recorder: ViolationRecorder,
    seed: int,
    *,
    trials: int = 24,
    chain_random_states: int = 5,
    budget_seconds: float | None = None,
) -> dict:
    """Quadrant 3: structural/planner invariants, heuristic_outcome checks,
    E-LOCAL-HADAMARD round-trip, P-REBASE inertness, invalid move rejections
    across apply_operation and machine/entrypoints.py, and symplectic round-trip."""
    t0 = time.monotonic()
    rng = random.Random(seed + 303)

    states_tested = 0
    candidates_checked = 0
    chains_checked = 0
    hadamard_checks = 0
    rebase_checks = 0
    invalid_move_checks = 0

    # Fixture [[10,2,3]] + random small CSS states.
    fixture_doc = json.loads((ROOT / "machine/fixtures/qldpc_10_2_3_b.json").read_text())
    fixture_state = CodeState.from_challenge(fixture_doc)
    fixture_ledger = DistanceLedger.from_challenge(fixture_state, fixture_doc)
    test_cases = [("fixture_10_2_3", fixture_state, fixture_ledger, 3)]

    for trial in range(trials):
        n = rng.randint(3, 8)
        st = _random_css_state(rng, n)
        ld = DistanceLedger(
            Interval(0, None),
            {"X": Interval(0, None), "Z": Interval(0, None)},
            witnesses={"X": [], "Z": []},
            conditions=[],
        )
        test_cases.append((f"rand_{trial}_n{n}", st, ld, 2))

    for label, st, ld, target in test_cases:
        states_tested += 1
        reduced_parent = reduce_display(st)
        cands = plan(
            st,
            ld,
            target=target,
            structural=True,
            reduce_display=True,
            reduce_by_domination=True,
            sector_targeted=True,
            target_sector="X",
            support_search={"budget": 128, "max_weight": min(3, st.n())},
            sector_swap=True,
            ranking="pareto",
        )
        for idx, cand in enumerate(cands):
            candidates_checked += 1
            _check_plan_candidate_invariants(
                recorder, "q3_invariant_fuzzing", f"{label}_{idx}", reduced_parent, cand
            )

        # Tighten via bounded_support_search must never raise lower endpoints
        # (for k=0 codes, C-SKIP canonicalizes to the vacuous [inf, inf] interval).
        tight, _ = tighten_ledger_with_search(
            st, ld, budget=128, max_weight=min(3, st.n())
        )
        if st.k() == 0:
            if (
                tight.full != Interval(None, None)
                or tight.sector["X"] != Interval(None, None)
                or tight.sector["Z"] != Interval(None, None)
            ):
                recorder.record(
                    f"q3-k0-not-vacuous-{label}",
                    "q3_invariant_fuzzing",
                    "k0_vacuous_distance",
                    f"{label}: k=0 state did not canonicalize to [inf, inf]",
                    state=st,
                )
        elif (
            tight.full.lower != ld.full.lower
            or tight.sector["X"].lower != ld.sector["X"].lower
            or tight.sector["Z"].lower != ld.sector["Z"].lower
        ):
            recorder.record(
                f"q3-search-raised-lower-{label}",
                "q3_invariant_fuzzing",
                "search_never_raises_lower",
                f"{label}: tighten_ledger_with_search changed lower endpoints",
                state=st,
            )

        # bounded_sector_search heuristic_outcome shape + budget compliance.
        bss = bounded_sector_search(
            st, ld, target_sector="X", target=target, budget=32, max_depth=1, sector_swap=True
        )
        _assert_heuristic_outcome_shape(
            recorder, "q3_invariant_fuzzing", f"bss_{label}", bss.get("heuristic_outcome"), state=st
        )
        if bss["budget_used"] > bss["budget"]:
            recorder.record(
                f"q3-bss-budget-overflow-{label}",
                "q3_invariant_fuzzing",
                "bss_budget_bound",
                f"{label}: budget_used={bss['budget_used']} > budget={bss['budget']}",
                state=st,
            )

        # E-LOCAL-HADAMARD round-trip & P-REBASE interval-inertness.
        _check_hadamard_roundtrip(recorder, "q3_invariant_fuzzing", label, st, ld)
        hadamard_checks += 1
        if _check_rebase_interval_inert(recorder, "q3_invariant_fuzzing", label, st, ld):
            rebase_checks += 1

        # strict_improvement_feasible heuristic_outcome & non-mutation check.
        admissible = list(admissible_added_checks(st, max_weight=2, sectors=("X",)))
        if admissible and st.n() <= 8:
            supp, sec = admissible[0]
            before_rows = st.rows
            before_ld = ld.as_json()
            res = strict_improvement_feasible(
                st,
                added_support=supp,
                added_sector=sec,
                base_distance=min(2, st.n()),
                ledger=ld,
                allow_enumeration=True,
                enumeration_ceiling=8,
            )
            if st.rows != before_rows or ld.as_json() != before_ld:
                recorder.record(
                    f"q3-strict-imp-mutated-{label}",
                    "q3_invariant_fuzzing",
                    "strict_improvement_non_mutating",
                    f"{label}: strict_improvement_feasible mutated input state or ledger",
                    state=st,
                )
            if res["enumeration"]["performed"]:
                _assert_heuristic_outcome_shape(
                    recorder,
                    "q3_invariant_fuzzing",
                    f"strict_imp_{label}",
                    res.get("heuristic_outcome"),
                    state=st,
                )

    # plan_chain replayability & non-prune invariant on fixture_10_2_3 (target=2
    # so non-prune chains actually emerge) plus the first ``chain_random_states``
    # random states.
    chain_cases = [("fixture_10_2_3_t2", fixture_state, fixture_ledger, 2)] + test_cases[
        1 : 1 + max(0, chain_random_states)
    ]
    for label, st, ld, target in chain_cases:
        chains = plan_chain(
            st,
            ld,
            target=target,
            depth=2,
            structural=True,
            reduce_display=True,
            include_disconnected=(label != "fixture_10_2_3_t2"),
            support_search=None,
        )
        for idx, item in enumerate(chains[:12]):
            chains_checked += 1
            if item["verdict"] == "prune":
                recorder.record(
                    f"q3-chain-emitted-prune-{label}-{idx}",
                    "q3_invariant_fuzzing",
                    "plan_chain_no_prune",
                    f"{label}: plan_chain emitted a pruned sequence",
                    state=st,
                    move_sequence=item["sequence"],
                )
            cur = reduce_display(st)
            try:
                for move in item["sequence"]:
                    cur = apply_operation(cur, move)
            except Exception as exc:
                recorder.record(
                    f"q3-chain-replay-failed-{label}-{idx}",
                    "q3_invariant_fuzzing",
                    "plan_chain_replayable",
                    f"{label}: plan_chain sequence failed replay: {exc!r}",
                    state=st,
                    move_sequence=item["sequence"],
                )
                continue
            if cur.n() != item["n"] or cur.k() != item["k"]:
                recorder.record(
                    f"q3-chain-params-mismatch-{label}-{idx}",
                    "q3_invariant_fuzzing",
                    "plan_chain_params",
                    f"{label}: replay (n={cur.n()},k={cur.k()}) != chain ({item['n']},{item['k']})",
                    state=st,
                    move_sequence=item["sequence"],
                )

    # Invalid move & invalid entrypoint rejection checks (apply_operation + machine/entrypoints.py).
    invalid_apply_ops = [
        ("non_dict", "C-SKIP"),
        ("unknown_op", {"op": "X-UNKNOWN-MOVE"}),
        ("c_column_cnot_unimplemented", {"op": "C-COLUMN-CNOT", "matrix": [[1]]}),
        ("delete_missing_row", {"op": "C-DELETE-CHECK", "row_id": "a999"}),
        ("add_bad_sector", {"op": "C-ADD-CHECK", "sector": "Y", "support": [0]}),
        ("add_out_of_Q", {"op": "C-ADD-CHECK", "sector": "X", "support": [999]}),
        ("add_anticommuting", {"op": "C-ADD-CHECK", "sector": "X", "support": [0]}),
        ("hadamard_proper_subset", {"op": "E-LOCAL-HADAMARD", "qubits": [0]}),
        ("hadamard_duplicate_qubit", {"op": "E-LOCAL-HADAMARD", "qubits": [0, 0]}),
        ("rebase_singular", {"op": "P-REBASE", "sector": "X", "matrix": [[0] * 4 for _ in range(4)]}),
        ("glue_missing_right", {"op": "E-GLUE"}),
    ]
    for name, bad_op in invalid_apply_ops:
        invalid_move_checks += 1
        try:
            apply_operation(fixture_state, bad_op)
        except (Malformed, NoDerivation):
            pass
        except Exception as exc:
            recorder.record(
                f"q3-apply-unexpected-exc-{name}",
                "q3_invariant_fuzzing",
                "invalid_move_rejection",
                f"apply_operation({name}) raised unexpected {type(exc).__name__}: {exc}",
                state=fixture_state,
                move_sequence=[bad_op],
            )
        else:
            recorder.record(
                f"q3-apply-accepted-invalid-{name}",
                "q3_invariant_fuzzing",
                "invalid_move_rejection",
                f"apply_operation({name}) silently accepted invalid op",
                state=fixture_state,
                move_sequence=[bad_op],
            )

    invalid_entrypoint_calls = [
        ("heuristic_empty_proc", lambda: heuristic_outcome("", "u", 1)),
        ("heuristic_bad_delta", lambda: heuristic_outcome("p", "u", 1, delta=1.5)),
        ("heuristic_bad_budget", lambda: heuristic_outcome("p", "u", 1, budget=0)),
        (
            "strict_imp_base_gt_n",
            lambda: strict_improvement_feasible(fixture_state, [0, 8, 9], "X", 99),
        ),
        (
            "strict_imp_base_zero",
            lambda: strict_improvement_feasible(fixture_state, [0, 8, 9], "X", 0),
        ),
        (
            "strict_imp_bad_sector",
            lambda: strict_improvement_feasible(fixture_state, [0, 8, 9], "Y", 2),
        ),
        (
            "strict_imp_anticommuting",
            lambda: strict_improvement_feasible(fixture_state, [0], "X", 2),
        ),
        (
            "strict_imp_above_ceiling",
            lambda: strict_improvement_feasible(
                fixture_state, [0, 8, 9], "X", 2, allow_enumeration=True, enumeration_ceiling=5
            ),
        ),
        ("fix_support_out_of_Q", lambda: fix_support(fixture_state, [999], "X")),
        ("fix_support_bad_sector", lambda: fix_support(fixture_state, [0], "Y")),
        (
            "multi_strict_imp_anticommuting",
            lambda: multi_check_strict_improvement_feasible(
                fixture_state, [([0], "X")], 2
            ),
        ),
    ]
    for name, fn in invalid_entrypoint_calls:
        invalid_move_checks += 1
        try:
            fn()
        except (Malformed, NoDerivation):
            pass
        except Exception as exc:
            recorder.record(
                f"q3-entrypoint-unexpected-exc-{name}",
                "q3_invariant_fuzzing",
                "invalid_entrypoint_rejection",
                f"entrypoint {name} raised unexpected {type(exc).__name__}: {exc}",
            )
        else:
            recorder.record(
                f"q3-entrypoint-accepted-invalid-{name}",
                "q3_invariant_fuzzing",
                "invalid_entrypoint_rejection",
                f"entrypoint {name} silently accepted invalid input",
            )

    # Symplectic double/halve round-trip assertion (from original Campaign 3).
    css4 = CodeState(
        (0, 1, 2, 3),
        (
            Row("a1", "X", (0, 1)),
            Row("a2", "X", (2, 3)),
            Row("b1", "Z", (0, 1)),
            Row("b2", "Z", (2, 3)),
        ),
        frozenset({"a1", "a2", "b1", "b2"}),
    )
    sym = SymplecticState.from_css(css4).double()
    sym.validate()
    _ = SymplecticLedger(Interval(0, None))
    halved = SymplecticState.halve(sym, [(q, q + css4.n()) for q in range(css4.n())])
    symplectic_roundtrip_ok = (
        sym.n() == 2 * css4.n()
        and sym.k() == 2 * css4.k()
        and halved.n() == css4.n()
        and halved.k() == css4.k()
    )
    if not symplectic_roundtrip_ok:
        recorder.record(
            "q3-symplectic-roundtrip",
            "q3_invariant_fuzzing",
            "symplectic_double_halve",
            f"symplectic round-trip mismatch: css=({css4.n()},{css4.k()}), "
            f"doubled=({sym.n()},{sym.k()}), halved=({halved.n()},{halved.k()})",
            state=css4,
        )

    elapsed = time.monotonic() - t0
    return {
        "states_tested": states_tested,
        "candidates_checked": candidates_checked,
        "chains_checked": chains_checked,
        "hadamard_roundtrips_checked": hadamard_checks,
        "rebase_inertness_checked": rebase_checks,
        "invalid_move_and_entrypoint_checks": invalid_move_checks,
        "symplectic_roundtrip_ok": symplectic_roundtrip_ok,
        **_timing_metrics("q3_invariant_fuzzing", elapsed, budget_seconds),
    }


# ---------------------------------------------------------------------------
# Quadrant 4: Adversarial inputs
# ---------------------------------------------------------------------------


def run_quadrant_4_adversarial(
    recorder: ViolationRecorder,
    seed: int,
    *,
    budget_seconds: float | None = None,
) -> dict:
    """Quadrant 4: mismatched ledgers, stale witnesses, W13 deleted-row claims,
    constructor-premise failures, degenerate states, and unreachable targets."""
    t0 = time.monotonic()
    checks_run = 0

    def expect_raises(check_id: str, check_name: str, exc_types, fn, state=None):
        nonlocal checks_run
        checks_run += 1
        try:
            fn()
        except exc_types:
            return
        except Exception as exc:
            recorder.record(
                f"q4-wrong-exc-{check_id}",
                "q4_adversarial",
                check_name,
                f"{check_id}: expected {exc_types}, got {type(exc).__name__}: {exc}",
                state=state,
            )
        else:
            recorder.record(
                f"q4-accepted-{check_id}",
                "q4_adversarial",
                check_name,
                f"{check_id}: expected {exc_types} but call succeeded",
                state=state,
            )

    doc10 = json.loads((ROOT / "machine/fixtures/qldpc_10_2_3_b.json").read_text())
    st10 = CodeState.from_challenge(doc10)
    ld10 = DistanceLedger.from_challenge(st10, doc10)

    # 4a. Mismatched ledgers
    expect_raises("interval_lo_gt_hi", "mismatched_ledger", (ValueError,), lambda: Interval(5, 3))
    expect_raises("interval_inf_lo_fin_hi", "mismatched_ledger", (ValueError,), lambda: Interval(None, 3))
    expect_raises("interval_neg_lo", "mismatched_ledger", (ValueError,), lambda: Interval(-1, 3))
    expect_raises(
        "challenge_lower_gt_witness",
        "mismatched_ledger",
        (Malformed,),
        lambda: DistanceLedger.from_challenge(
            st10, doc10, lower_bounds={"d": {"value": 99, "source": "adversarial"}}
        ),
        state=st10,
    )
    expect_raises(
        "challenge_unsourced_lower",
        "mismatched_ledger",
        (Malformed,),
        lambda: DistanceLedger.from_challenge(st10, doc10, lower_bounds={"d": 2}),
        state=st10,
    )
    expect_raises(
        "constructed_unsourced_lower",
        "mismatched_ledger",
        (Malformed,),
        lambda: DistanceLedger.for_constructed(st10, lower_bounds={"X": 2}),
        state=st10,
    )
    # Contradictory witness lighter than carried lower endpoint -> NoDerivation
    high_ld = DistanceLedger(
        Interval(5, None), {"X": Interval(5, None), "Z": Interval(5, None)}
    )
    expect_raises(
        "propagate_contradicts_lower",
        "mismatched_ledger",
        (NoDerivation,),
        lambda: high_ld.propagate(
            {"op": "C-SKIP"},
            st10,
            parent_state=st10,
            observations={"X": doc10["distance"]["X"]["witness"]},
        ),
        state=st10,
    )

    # 4b. Stale witnesses after C-DELETE-CHECK / C-ADD-CHECK
    # Deleting row a1 leaves a1's support outside X-span, but a support that
    # fails to commute with remaining Z-rows or lies in X-span must be refused.
    del_op = {"op": "C-DELETE-CHECK", "row_id": "a1"}
    child_del = apply_operation(st10, del_op)
    x_row_a2 = list(child_del.sector_rows("X")[0].support)
    expect_raises(
        "stale_stabilizer_as_witness_after_delete",
        "stale_witness",
        (NoDerivation,),
        lambda: ld10.propagate(
            del_op, child_del, parent_state=st10, observations={"X": x_row_a2}
        ),
        state=child_del,
    )
    # Adding check X {0, 8, 9}: passing a Z-witness that anticommutes with
    # {0, 8, 9} as a post-step observation must be refused.
    add_op = {"op": "C-ADD-CHECK", "sector": "X", "support": [0, 8, 9]}
    child_add = apply_operation(st10, add_op)
    bad_z_wit = [0]  # anticommutes with X check {0, 8, 9}
    expect_raises(
        "stale_anticommuting_witness_after_add",
        "stale_witness",
        (NoDerivation,),
        lambda: ld10.propagate(
            add_op, child_add, parent_state=st10, observations={"Z": bad_z_wit}
        ),
        state=child_add,
    )
    # Carried parent witnesses invalidated by C-ADD-CHECK must not survive as
    # invalid witnesses in the child ledger.
    checks_run += 1
    ld_after_add = ld10.propagate(add_op, child_add, parent_state=st10)
    for side in ("X", "Z"):
        for w in ld_after_add.witnesses[side]:
            try:
                validate_witness(child_add, side, tuple(w["support"]), w["value"])
            except (Malformed, NoDerivation) as exc:
                recorder.record(
                    f"q4-stale-carried-witness-survived-{side}",
                    "q4_adversarial",
                    "stale_witness",
                    f"invalid carried witness survived C-ADD-CHECK: {w} ({exc})",
                    state=child_add,
                    move_sequence=[add_op],
                )

    # 4c. W13 generator-referencing / deleted-row claims & I4/I5 monotonicity
    expect_raises(
        "w13_redelete_retired_row",
        "w13_deleted_row",
        (NoDerivation,),
        lambda: apply_operation(child_del, {"op": "C-DELETE-CHECK", "row_id": "a1"}),
        state=child_del,
    )
    expect_raises(
        "w13_graft_retired_row",
        "w13_deleted_row",
        (NoDerivation, Malformed),
        lambda: apply_operation(
            child_del,
            {"op": "E-GRAFT", "qubit": 0, "sector": "X", "ordered_row_ids": ["a1"]},
        ),
        state=child_del,
    )
    expect_raises(
        "i4_live_id_not_in_used",
        "w13_used_invariant",
        (Malformed,),
        lambda: CodeState((0, 1), (Row("a1", "X", (0, 1)),), frozenset()).validate(),
    )
    # Overlapping used sets in C-DIRECT-SUM must fail.
    s_small = CodeState((0, 1), (Row("a1", "X", (0, 1)),), frozenset({"a1"}))
    s_other = CodeState((2, 3), (Row("a1", "X", (2, 3)),), frozenset({"a1"}))
    expect_raises(
        "direct_sum_overlapping_used",
        "w13_used_invariant",
        (NoDerivation, Malformed),
        lambda: CodeState.direct_sum(s_small, s_other),
        state=s_small,
    )

    # 4d. Constructor-premise failures across admitted constructors
    four_two_two = CodeState(
        (0, 1, 2, 3),
        (Row("a1", "X", (0, 1, 2, 3)), Row("b1", "Z", (0, 1, 2, 3))),
        frozenset({"a1", "b1"}),
    )
    nonassoc_table = [[0, 1, 2], [1, 0, 1], [2, 2, 0]]
    bad_constructor_specs = [
        ("hgp_ragged", {"constructor": "L-HGP", "H1": [[1, 0], [1]], "H2": [[1, 1]]}),
        (
            "lifted_nonassoc",
            {
                "constructor": "L-LIFTED",
                "group": {"table": nonassoc_table},
                "A": [[[0]]],
                "B": [[[0]]],
            },
        ),
        (
            "group_alg_nonassoc",
            {
                "constructor": "L-GROUP-ALGEBRA",
                "group": {"table": nonassoc_table},
                "a": [0],
                "b": [0],
            },
        ),
        (
            "concat_bad_groups",
            {
                "constructor": "A-CONCAT",
                "outer": four_two_two,
                "inner": four_two_two,
                "groups": [(0, 1)],  # wrong partition of 4 outer qubits
            },
        ),
        (
            "balanced_bad_perm",
            {
                "constructor": "L-BALANCED",
                "group": (3,),
                "H1": [[1, 1, 0]],
                "action1": {"rows": [[0, 0]], "cols": [[1, 2, 0]]},
                "H2": [[1, 1, 0]],
                "action2": {"rows": [[0]], "cols": [[1, 2, 0]]},
            },
        ),
        (
            "tanner_noncommuting",
            {
                "constructor": "L-TANNER",
                "n": 2,
                "local_x": [[1, 0]],
                "local_z": [[1, 0]],
                "views_x": [[0, 1]],
                "views_z": [[0, 1]],
            },
        ),
        (
            "tile_noncommuting",
            {
                "constructor": "L-TILE",
                "tiles": [{"qubits": 2, "X": [[0]], "Z": [[0]]}],
                "placements": [(0, [0, 1])],
                "identifications": [],
                "removed": [],
            },
        ),
        (
            "product_missing_cert",
            {
                "constructor": "A-PRODUCT",
                "left": four_two_two,
                "right": four_two_two,
                "constructor_cell": {
                    "constructor": "A-PRODUCT",
                    "d_X": 2,
                    "d_Z": 2,
                    "source": "missing display_certificate",
                },
            },
        ),
        (
            "double_twisted_missing_cert",
            {
                "constructor": "A-DOUBLE",
                "state": four_two_two,
                "wiring": {"a1": [0, 1]},
                "constructor_cell": {
                    "constructor": "A-DOUBLE",
                    "wiring_empty": False,
                    "d_X": 2,
                    "d_Z": 2,
                    "source": "missing twisted_certificate",
                },
            },
        ),
        (
            "nested_noncommuting",
            {"constructor": "L-NESTED-CSS", "HX": [[1, 0]], "HZ": [[1, 0]]},
        ),
        (
            "cone_noncommuting_chain_map",
            {
                "constructor": "L-MAPPING-CONE",
                "d_a": [[1]],
                "d_b": [[0]],
                "f1": [[1]],
                "f0": [[1]],
            },
        ),
        ("free_duplicate_qubits", {"constructor": "L-FREE", "qubits": [0, 0]}),
        (
            "pullback_bad_map",
            {
                "constructor": "A-PULLBACK",
                "left": four_two_two,
                "right": four_two_two,
                "interface": construct({"constructor": "L-FREE", "qubits": [0]})["state"],
                "phi1": {0: 99},
                "phi2": {0: 0},
            },
        ),
        (
            "pushout_bad_map",
            {
                "constructor": "A-PUSHOUT",
                "left": four_two_two,
                "right": four_two_two,
                "subcode": construct({"constructor": "L-FREE", "qubits": [0]})["state"],
                "psi1": {0: 99},
                "psi2": {0: 0},
            },
        ),
        (
            "pair_partition_bad_p",
            {
                "constructor": "L-PAIR-PARTITION",
                "p": 0,
                "blocks_x": [[(1, 0), (1, 0)]],
                "blocks_z": [[(1, 0), (1, 0)]],
            },
        ),
        (
            "pp_scale_bad_P",
            {
                "constructor": "PP-SCALE",
                "state": four_two_two,
                "P": 0,
                "blocks_x": [[(1, 0), (1, 0)]],
                "blocks_z": [[(1, 0), (1, 0)]],
            },
        ),
    ]
    for cid, bad_spec in bad_constructor_specs:
        expect_raises(
            f"constructor_{cid}",
            "constructor_premise_failure",
            (Malformed, NoDerivation),
            lambda s=bad_spec: construct(s),
        )

    # 4e. Degenerate states: n=0 (L-EMPTY), n=1 bare, k=0 stabilized
    empty_st = construct({"constructor": "L-EMPTY"})["state"]
    checks_run += 1
    if empty_st.n() != 0 or empty_st.k() != 0:
        recorder.record(
            "q4-empty-params",
            "q4_adversarial",
            "degenerate_n0",
            f"L-EMPTY gave n={empty_st.n()}, k={empty_st.k()}",
            state=empty_st,
        )
    expect_raises(
        "empty_support_search",
        "degenerate_n0",
        (Malformed,),
        lambda: bounded_support_search(empty_st, budget=8, max_weight=1),
        state=empty_st,
    )
    expect_raises(
        "empty_strict_imp",
        "degenerate_n0",
        (Malformed,),
        lambda: strict_improvement_feasible(empty_st, [0], "X", 1),
        state=empty_st,
    )

    n1_st = CodeState((0,), (), frozenset())
    checks_run += 1
    r_n1 = bounded_support_search(n1_st, budget=10, max_weight=1)
    if (
        n1_st.k() != 1
        or not has_bare_qubit(n1_st)
        or r_n1["witnesses"]["X"] is None
        or r_n1["witnesses"]["Z"] is None
        or r_n1["witnesses"]["X"]["value"] != 1
        or r_n1["witnesses"]["Z"]["value"] != 1
    ):
        recorder.record(
            "q4-n1-bare-search",
            "q4_adversarial",
            "degenerate_n1",
            f"n=1 bare state check failed: k={n1_st.k()}, search={r_n1}",
            state=n1_st,
        )

    k0_st = CodeState(
        (0, 1),
        (Row("a1", "X", (0,)), Row("b1", "Z", (1,))),
        frozenset({"a1", "b1"}),
    )
    checks_run += 1
    r_k0 = bounded_support_search(k0_st, budget=16, max_weight=2)
    if k0_st.k() != 0 or r_k0["witnesses"]["X"] is not None or r_k0["witnesses"]["Z"] is not None:
        recorder.record(
            "q4-k0-stabilized-search",
            "q4_adversarial",
            "degenerate_k0",
            f"k=0 state unexpectedly yielded witnesses: {r_k0}",
            state=k0_st,
        )

    # Empty lists in planner utilities
    checks_run += 1
    if domination_prune([]) != [] or dedup_up_to_permutation([]) != [] or pareto_front([]) != []:
        recorder.record(
            "q4-empty-batch-helpers",
            "q4_adversarial",
            "degenerate_empty_batch",
            "empty batch helper returned non-empty list",
        )

    # 4f. Target above every reachable parameter
    checks_run += 1
    cands_unreachable = plan(
        st10,
        ld10,
        target=1000,
        structural=True,
        reduce_display=True,
        support_search={"budget": 128, "max_weight": 3},
    )
    non_pruned = [c for c in cands_unreachable if c["verdict"] != "prune"]
    if non_pruned:
        recorder.record(
            "q4-unreachable-target-not-pruned",
            "q4_adversarial",
            "unreachable_target",
            f"target=1000 on [[10,2,3]] yielded {len(non_pruned)} non-prune candidates",
            state=st10,
        )

    elapsed = time.monotonic() - t0
    return {
        "adversarial_checks_run": checks_run,
        "unreachable_target_candidates": len(cands_unreachable),
        **_timing_metrics("q4_adversarial", elapsed, budget_seconds),
    }


# ---------------------------------------------------------------------------
# Scale ladder: n = 100-120 named board parents (vprusso #6)
# ---------------------------------------------------------------------------


def run_scale_ladder(
    recorder: ViolationRecorder,
    seed: int,
    challenge_root: Path,
    *,
    support_budget: int = 256,
    support_max_weight: int = 2,
    sector_budget: int = 24,
    children_search_cap: int = 5,
    parents: tuple[str, ...] = SCALE_LADDER_PARENTS,
    enforce_n_range: bool = True,
    budget_seconds: float | None = None,
) -> dict:
    """Quadrant-3 invariants at n = 100-120 on named pinned challenge parents.

    Oracle is NEVER called at these sizes; explicit budget overrides vs.
    ``DEFAULT_SUPPORT_BUDGET`` / ``DEFAULT_SUPPORT_MAX_WEIGHT`` are recorded.
    """
    t0 = time.monotonic()
    per_parent = []
    total_candidates = 0

    for parent_name in parents:
        tp0 = time.monotonic()
        doc = json.loads((challenge_root / "codes" / parent_name).read_text())
        st = CodeState.from_challenge(doc)
        ld = DistanceLedger.from_challenge(st, doc)
        target = doc["distance"]["d"]

        if enforce_n_range and not (100 <= st.n() <= 120):
            recorder.record(
                f"scale-parent-n-out-of-range-{parent_name}",
                "scale_ladder",
                "scale_parent_range",
                f"{parent_name}: n={st.n()} outside 100..120",
                state=st,
            )

        reduced_parent = reduce_display(st)
        cands = plan(
            st,
            ld,
            target=target,
            structural=True,
            reduce_display=True,
            reduce_by_domination=True,
            support_search=None,
            sector_swap=True,
            ranking="pareto",
        )
        total_candidates += len(cands)
        for idx, cand in enumerate(cands):
            _check_plan_candidate_invariants(
                recorder, "scale_ladder", f"{parent_name}_{idx}", reduced_parent, cand
            )

        # Tighten parent + top surviving children with recorded budget override.
        parent_tight, _ = tighten_ledger_with_search(
            st, ld, budget=support_budget, max_weight=support_max_weight
        )
        if (
            parent_tight.full.lower != ld.full.lower
            or parent_tight.sector["X"].lower != ld.sector["X"].lower
            or parent_tight.sector["Z"].lower != ld.sector["Z"].lower
        ):
            recorder.record(
                f"scale-search-raised-lower-parent-{parent_name}",
                "scale_ladder",
                "search_never_raises_lower",
                f"{parent_name}: tighten_ledger_with_search raised lower endpoint",
                state=st,
            )

        children_searched = 0
        for idx, cand in enumerate(cands[:children_search_cap]):
            children_searched += 1
            ctight, _ = tighten_ledger_with_search(
                cand["state"],
                cand["ledger"],
                budget=support_budget,
                max_weight=support_max_weight,
            )
            if (
                ctight.full.lower != cand["ledger"].full.lower
                or ctight.sector["X"].lower != cand["ledger"].sector["X"].lower
                or ctight.sector["Z"].lower != cand["ledger"].sector["Z"].lower
            ):
                recorder.record(
                    f"scale-search-raised-lower-child-{parent_name}-{idx}",
                    "scale_ladder",
                    "search_never_raises_lower",
                    f"{parent_name} child {idx}: search raised lower endpoint",
                    state=cand["state"],
                    move_sequence=[cand["operation"]],
                )

        # Bounded sector search + heuristic_outcome shape.
        bss = bounded_sector_search(
            st,
            ld,
            target_sector="X",
            target=target,
            budget=sector_budget,
            max_depth=1,
            sector_swap=True,
        )
        _assert_heuristic_outcome_shape(
            recorder, "scale_ladder", f"bss_{parent_name}", bss.get("heuristic_outcome"), state=st
        )

        # E-LOCAL-HADAMARD round-trip and P-REBASE inertness at n=100..120.
        _check_hadamard_roundtrip(recorder, "scale_ladder", parent_name, st, ld)
        rebase_ok = _check_rebase_interval_inert(recorder, "scale_ladder", parent_name, st, ld)

        p_elapsed = time.monotonic() - tp0
        per_parent.append(
            {
                "parent": f"codes/{parent_name}",
                "n": st.n(),
                "k": st.k(),
                "w": st.w(),
                "target": target,
                "candidates": len(cands),
                "children_support_searched": children_searched,
                "bss_budget_used": bss["budget_used"],
                "rebase_checked": rebase_ok,
                "elapsed_seconds": round(p_elapsed, 4),
            }
        )

    elapsed = time.monotonic() - t0
    return {
        "parents_tested": len(parents),
        "total_candidates_checked": total_candidates,
        "budget_overrides": {
            "support_budget": support_budget,
            "default_support_budget": DEFAULT_SUPPORT_BUDGET,
            "support_max_weight": support_max_weight,
            "default_support_max_weight": DEFAULT_SUPPORT_MAX_WEIGHT,
            "sector_budget": sector_budget,
            "children_search_cap": children_search_cap,
        },
        "oracle_invoked": False,
        "per_parent": per_parent,
        **_timing_metrics("scale_ladder", elapsed, budget_seconds),
    }


def run_battery(
    *,
    seed: int = DEFAULT_SEED,
    challenge_root: Path | None = None,
    allow_any_commit: bool = False,
    small_trials: int = 25,
    pareto_trials: int = 30,
    fuzz_trials: int = 24,
    chain_random_states: int = 5,
    max_verify_per_parent: int = 8,
    known_violations=None,
    advisory_budgets: dict[str, float] | None = None,
) -> dict:
    """Execute the full asserted battery and return the structured report."""
    t_total = time.monotonic()
    recorder = ViolationRecorder(seed=seed, known_violations=known_violations)
    budgets = dict(advisory_budgets) if advisory_budgets is not None else {}

    qldpc_sha = None
    if challenge_root is not None:
        challenge_root = Path(challenge_root).resolve()
        qldpc_sha = _verify_challenge_checkout(
            challenge_root, allow_any_commit=allow_any_commit
        )

    import_hygiene = check_oracle_import_hygiene(
        recorder, budget_seconds=budgets.get("import_hygiene")
    )
    q1 = run_quadrant_1_oracle_differential(
        recorder,
        seed,
        small_trials=small_trials,
        pareto_trials=pareto_trials,
        budget_seconds=budgets.get("q1_oracle_differential"),
    )
    if challenge_root is not None:
        q2 = run_quadrant_2_gate_differential(
            recorder,
            seed,
            challenge_root,
            max_verify_per_parent=max_verify_per_parent,
            budget_seconds=budgets.get("q2_gate_differential"),
        )
    else:
        q2 = {"skipped": True, "reason": "no --challenge-root supplied"}

    q3 = run_quadrant_3_invariant_fuzzing(
        recorder,
        seed,
        trials=fuzz_trials,
        chain_random_states=chain_random_states,
        budget_seconds=budgets.get("q3_invariant_fuzzing"),
    )
    q4 = run_quadrant_4_adversarial(
        recorder, seed, budget_seconds=budgets.get("q4_adversarial")
    )

    if challenge_root is not None:
        scale = run_scale_ladder(
            recorder,
            seed,
            challenge_root,
            budget_seconds=budgets.get("scale_ladder"),
        )
    else:
        scale = {"skipped": True, "reason": "no --challenge-root supplied"}

    phase_reports = (
        ("import_hygiene", import_hygiene),
        ("q1_oracle_differential", q1),
        ("q2_gate_differential", q2),
        ("q3_invariant_fuzzing", q3),
        ("q4_adversarial", q4),
        ("scale_ladder", scale),
    )
    advisory_budget_overruns = [
        phase
        for phase, metrics in phase_reports
        if not metrics.get("skipped", False) and not metrics.get("within_budget", True)
    ]

    total_elapsed = time.monotonic() - t_total
    return {
        "schema": "stress_campaign.v1",
        "issue": "#577",
        "note": (
            "Empirical discovery-loop stress battery only (AGENTS.md Hard rules): "
            "zero violations means the run failed to falsify, never a proof of soundness."
        ),
        "seed": seed,
        "qldpc_commit": qldpc_sha,
        "import_hygiene": import_hygiene,
        "quadrant_1_oracle_differential": q1,
        "quadrant_2_gate_differential": q2,
        "quadrant_3_invariant_fuzzing": q3,
        "quadrant_4_adversarial": q4,
        "scale_ladder": scale,
        "summary": {
            "total_violations": len(recorder.violations),
            "unexpected_violations": len(recorder.unexpected),
            "known_violations": len(recorder.known),
            "advisory_budget_overruns": advisory_budget_overruns,
            "passed": len(recorder.unexpected) == 0,
            "total_elapsed_seconds": round(total_elapsed, 4),
        },
        "known_violation_allowlist": recorder.known_violations,
        "violations": recorder.violations,
    }


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--challenge-root",
        type=Path,
        default=None,
        help="Path to clean pinned unitaryfoundation/qldpc-challenge checkout "
        f"(commit {Q_LDPC_SHA}) for Quadrant 2 and the n=100-120 scale ladder.",
    )
    parser.add_argument(
        "--allow-any-commit",
        action="store_true",
        help="Allow a clean qldpc-challenge checkout at a commit other than the pinned SHA.",
    )
    parser.add_argument(
        "--seed",
        type=int,
        default=DEFAULT_SEED,
        help=f"Deterministic PRNG seed (default: {DEFAULT_SEED}).",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_REPORT_PATH,
        help=f"Write JSON metrics report here (default: {DEFAULT_REPORT_PATH}). Use '-' to skip writing.",
    )
    parser.add_argument(
        "--quick",
        action="store_true",
        help="Reduced trial counts for fast local smoke checks.",
    )
    parser.add_argument(
        "--ci",
        action="store_true",
        help="Minimal smoke trial counts for fast PR CI checks.",
    )
    args = parser.parse_args(argv)

    if args.ci:
        small_trials = 3
        pareto_trials = 4
        fuzz_trials = 3
        chain_random_states = 2
        max_verify_per_parent = 2
    elif args.quick:
        small_trials = 8
        pareto_trials = 10
        fuzz_trials = 8
        chain_random_states = 3
        max_verify_per_parent = 4
    else:
        small_trials = 25
        pareto_trials = 30
        fuzz_trials = 24
        chain_random_states = 5
        max_verify_per_parent = 8

    report = run_battery(
        seed=args.seed,
        challenge_root=args.challenge_root,
        allow_any_commit=args.allow_any_commit,
        small_trials=small_trials,
        pareto_trials=pareto_trials,
        fuzz_trials=fuzz_trials,
        chain_random_states=chain_random_states,
        max_verify_per_parent=max_verify_per_parent,
    )

    rendered = json.dumps(report, indent=2) + "\n"
    if str(args.output) != "-":
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)

    summary = report["summary"]
    print(
        "stress_campaign: passed=%s unexpected_violations=%d known_violations=%d "
        "advisory_budget_overruns=%d elapsed=%.2fs report=%s"
        % (
            summary["passed"],
            summary["unexpected_violations"],
            summary["known_violations"],
            len(summary["advisory_budget_overruns"]),
            summary["total_elapsed_seconds"],
            args.output,
        )
    )
    if not summary["passed"]:
        print("UNEXPECTED VIOLATIONS (reproducible dumps):", file=sys.stderr)
        print(
            json.dumps(
                [v for v in report["violations"] if not v["known"]], indent=2
            ),
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
