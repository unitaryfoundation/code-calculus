#!/usr/bin/env python3
"""Direction-2 lower-bound transport experiment (issue #295).

Measures the pruning/soundness impact of transporting derived lower (and the
paired upper) endpoints through E-PEEL, which §4.28 already proves sound but
which the admitted calculus refused by design until 2026-11-06 (reset to
0 / +inf).  The experiment runs on small random CSS codes where exact
distances are computable, so every transported bound can be checked against
the truth rather than trusted.

Modes compared:
  - reset:       pre-admission behaviour (everything resets).
  - direction2:  carry of the selected sector's lower endpoint and the
                 opposite sector's upper endpoint (§4.28), full distance
                 lower reset and upper carries the opposite upper.

Outputs a JSON report and a one-line summary.  Nothing here is admitted by
the calculus; see the recorded disposition before promoting.
"""

import argparse
import itertools
import json
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from machine.priced_calculus import (  # noqa: E402
    CodeState,
    DistanceLedger,
    Interval,
    Row,
    apply_operation,
    support_mask,
)
from machine.experiments.issue21_challenge_replay import exact_distances  # noqa: E402


def random_code(rng, n, max_rows=3):
    """Generate a valid small CSS CodeState by rejection sampling."""
    attempts = 0
    while attempts < 2000:
        attempts += 1
        # random X rows
        nrows_x = rng.randint(0, max_rows)
        nrows_z = rng.randint(0, max_rows)
        x_supports = []
        z_supports = []
        for _ in range(nrows_x):
            w = rng.randint(1, n)
            supp = tuple(sorted(rng.sample(range(n), w)))
            x_supports.append(supp)
        for _ in range(nrows_z):
            w = rng.randint(1, n)
            supp = tuple(sorted(rng.sample(range(n), w)))
            z_supports.append(supp)
        # dedup per sector by span
        def basis(supports):
            kept = []
            masks = []
            for supp in supports:
                m = support_mask(supp)
                # independence check: reduce m by the existing basis.
                bb = {}
                for row in masks:
                    v2 = row
                    while v2:
                        p = v2.bit_length() - 1
                        if p in bb:
                            v2 ^= bb[p]
                        else:
                            bb[p] = v2
                            break
                v = m
                for p in sorted(bb, reverse=True):
                    if (v >> p) & 1:
                        v ^= bb[p]
                if v != 0:
                    masks.append(m)
                    kept.append(supp)
            return kept

        xs = basis(x_supports)
        zs = basis(z_supports)
        # orthogonality: every X row commutes with every Z row
        ok = True
        for xsupp in xs:
            xm = support_mask(xsupp)
            for zsupp in zs:
                zm = support_mask(zsupp)
                if bin(xm & zm).count("1") % 2 != 0:
                    ok = False
                    break
            if not ok:
                break
        if not ok:
            continue
        # build rows with ids
        rows = []
        used = set()
        idx = 0
        for supp in xs:
            idx += 1
            rid = "a%d" % idx
            rows.append(Row(rid, "X", supp))
            used.add(rid)
        idx = 0
        for supp in zs:
            idx += 1
            rid = "b%d" % idx
            rows.append(Row(rid, "Z", supp))
            used.add(rid)
        try:
            state = CodeState(tuple(range(n)), tuple(rows), frozenset(used))
            state.validate()
        except Exception:
            continue
        return state
    return None


def peel_candidates(state):
    out = []
    for sector in ("X", "Z"):
        for qubit in state.Q:
            touching = [row for row in state.sector_rows(sector)
                        if qubit in row.support]
            if len(touching) == 1:
                out.append((qubit, sector, touching[0].id))
    return out


def run_experiment(seed, trials, n_max):
    rng = random.Random(seed)
    stats = {
        "parents_tried": 0,
        "peels_applied": 0,
        "peels_skipped_noderivation": 0,
        "soundness_failures": {"reset": 0, "direction2": 0},
        "direction2_sound": 0,
        "direction2_unsound": 0,
        "direction2_lower_carried_positive": 0,
        "direction2_opposite_upper_carried_finite": 0,
        "prune_baseline": 0,
        "prune_direction2": 0,
        "extra_prune_from_direction2": 0,
    }
    details = []
    target = 3
    for _ in range(trials):
        n = rng.randint(4, n_max)
        state = random_code(rng, n)
        if state is None:
            continue
        stats["parents_tried"] += 1
        ex_parent = exact_distances(state)
        # ledger seeded with exact parent distances as [d, d] (lower=upper=exact)
        # to test transport containment precisely.
        ledger = DistanceLedger(
            Interval(ex_parent["d"], ex_parent["d"]),
            {"X": Interval(ex_parent["X"], ex_parent["X"]),
             "Z": Interval(ex_parent["Z"], ex_parent["Z"])},
        )
        for (qubit, sector, row_id) in peel_candidates(state):
            try:
                child = state.peel(qubit, sector, row_id)
            except Exception:
                stats["peels_skipped_noderivation"] += 1
                continue
            ex_child = exact_distances(child)
            stats["peels_applied"] += 1
            op = {"op": "E-PEEL", "qubit": qubit, "sector": sector,
                  "row_id": row_id}
            for mode in ("reset", "direction2"):
                out = ledger.propagate(op, child, parent_state=state,
                                      lower_bound_mode=mode)
                # containment checks
                sound = True
                # full distance
                L = out.full.lower if out.full.lower is not None else 0
                U = out.full.upper
                dchild = ex_child["d"]
                if dchild is not None:
                    if not (L <= dchild):
                        sound = False
                    if U is not None and not (dchild <= U):
                        sound = False
                for side in ("X", "Z"):
                    Ls = out.sector[side].lower
                    Ls = 0 if Ls is None else Ls
                    Us = out.sector[side].upper
                    ds = ex_child[side]
                    if ds is not None:
                        if not (Ls <= ds):
                            sound = False
                        if Us is not None and not (ds <= Us):
                            sound = False
                if sound:
                    if mode == "direction2":
                        stats["direction2_sound"] += 1
                else:
                    stats["soundness_failures"][mode] += 1
                    if mode == "direction2":
                        stats["direction2_unsound"] += 1
            # direction2 specifics
            out_d2 = ledger.propagate(op, child, parent_state=state,
                                     lower_bound_mode="direction2")
            sel = sector
            oth = "Z" if sector == "X" else "X"
            if (out_d2.sector[sel].lower is not None
                    and out_d2.sector[sel].lower > 0):
                stats["direction2_lower_carried_positive"] += 1
            if (out_d2.sector[oth].upper is not None):
                stats["direction2_opposite_upper_carried_finite"] += 1
            # pruning against target
            base = ledger.propagate(op, child, parent_state=state,
                                    lower_bound_mode="reset")
            # prune if upper < target
            def prunes(out):
                # full upper
                u = out.full.upper
                if u is not None and u < target:
                    return True
                # sector uppers for both? board uses full d; use full
                return False
            if prunes(base):
                stats["prune_baseline"] += 1
            if prunes(out_d2):
                stats["prune_direction2"] += 1
            if prunes(out_d2) and not prunes(base):
                stats["extra_prune_from_direction2"] += 1
            details.append({
                "n": state.n(),
                "qubit": qubit,
                "sector": sector,
                "parent_d": ex_parent["d"],
                "child_d": ex_child["d"],
                "child_X": ex_child["X"],
                "child_Z": ex_child["Z"],
            })
    return stats, details


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--trials", type=int, default=200)
    ap.add_argument("--n-max", type=int, default=6)
    ap.add_argument("--out", type=str, default=None)
    args = ap.parse_args()

    stats, details = run_experiment(args.seed, args.trials, args.n_max)
    report = {"args": vars(args), "stats": stats,
              "n_details": len(details)}
    text = json.dumps(report, indent=2)
    print(text)
    if args.out:
        Path(args.out).write_text(text + "\n")
        print("wrote", args.out, file=sys.stderr)


if __name__ == "__main__":
    main()
