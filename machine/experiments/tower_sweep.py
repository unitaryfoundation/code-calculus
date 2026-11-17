#!/usr/bin/env python3
"""Sweep of the tower price provider against exhaustive enumeration (issue #327).

`design/DERIVED_RELATIONS.md` section 2a derives that deleting the lifts of
outer checks in a concatenation tower has exposure and deletion prices that
factor through the outer code: each is the least dictionary weight of an
outer-level vector, where the dictionary weight sums, over blocks, the inner
class dictionary entry of the block's class. This script builds towers from
small inner codes (n_in = 4 with k_in = 1, 2, and 3) and random outer codes,
lifts the outer checks through randomly perturbed representatives, and
compares `tower_deletion_prices` with the prices read off the tower by
exhaustive enumeration. It also checks the unrefined dictionary (the inner
distance alone) against the refined one, and the priced deletion cell
d' = min(d, w_del, w_exp) against the exact-distance oracle on the tower.
Agreement is evidence that the derivation is transcribed as stated, not a
proof (AGENTS.md). Nothing here is a consumer path: the tower is built only
to be enumerated, and `A-CONCAT` stays a price provider in the calculus.
"""

import argparse
import json
import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
for path in (HERE, ROOT):
    if path not in sys.path:
        sys.path.insert(0, path)

from weight3_split_reduction import exposure_price_exhaustive  # noqa: E402
from machine.oracle import exact_distances  # noqa: E402
from machine.priced_calculus import (  # noqa: E402
    CodeState,
    Row,
    rank,
    tower_deletion_prices,
    tower_level_data,
)


def deletion_price_exhaustive(state, deleted_ids):
    """The deletion price of deleting ``deleted_ids``: the least weight of a
    combination of the sector's displayed rows that uses a deleted row
    (the lightest promoted stabilizer). Oracle-only: 2^m in the row count."""
    deleted_ids = set(deleted_ids)
    deleted = [row for row in state.rows if row.id in deleted_ids]
    if not deleted:
        raise ValueError("no deleted row found")
    sector = deleted[0].sector
    rows = list(state.sector_rows(sector))
    deleted_bits = sum(1 << r for r, row in enumerate(rows) if row.id in deleted_ids)
    best = None
    combination = 0
    for index in range(1, 1 << len(rows)):
        combination ^= rows[(index & -index).bit_length() - 1].mask
        if not ((index ^ (index >> 1)) & deleted_bits):
            continue
        weight = combination.bit_count()
        if best is None or weight < best:
            best = weight
    return best


def concatenate(inner, outer, groups, rng=None, prefix=("a", "b", "c", "d")):
    """The tower of ``inner`` on every block of ``outer``.

    Block ``j`` carries a copy of the inner code on labels ``j * n_in + i``
    (``i`` the index of the inner label). Every outer check is lifted block
    by block: its restriction to block ``j`` is a class ``h_j`` of the inner
    logical group, and the lift carries a representative of that class on
    the block, the canonical one from the level data plus, when ``rng`` is
    given, a random inner stabilizer of the same sector (the price does not
    depend on the choice). Returns ``(tower_state, lifted_ids)`` where
    ``lifted_ids`` maps each outer row id to its lifted row id. Experiment
    helper only: `A-CONCAT` is not a calculus constructor.
    """
    level = tower_level_data(inner)
    if level["status"] != "computed":
        raise ValueError(level["reason"])
    k_in = level["k_in"]
    inner_labels = list(inner.Q)
    n_in = len(inner_labels)
    index_of = {label: i for i, label in enumerate(inner_labels)}

    def shift(mask, block):
        out = 0
        for label in inner_labels:
            if (mask >> label) & 1:
                out |= 1 << (block * n_in + index_of[label])
        return out

    rows = []
    counters = {"X": 0, "Z": 0, "LX": 0, "LZ": 0}
    letters = {"X": prefix[0], "Z": prefix[1], "LX": prefix[2], "LZ": prefix[3]}

    def add(kind, sector, mask):
        counters[kind] += 1
        support = tuple(label for label in range(n_in * len(groups)) if (mask >> label) & 1)
        rows.append(Row("%s%d" % (letters[kind], counters[kind]), sector, support))
        return rows[-1].id

    inner_rows = {side: [row.mask for row in inner.sector_rows(side)] for side in ("X", "Z")}
    for block in range(len(groups)):
        for side in ("X", "Z"):
            for mask in inner_rows[side]:
                add(side, side, shift(mask, block))
    reps = level["logical_basis"]
    lifted_ids = {}
    for row in outer.rows:
        mask = 0
        for block, group in enumerate(groups):
            rep = 0
            for position, label in enumerate(group):
                if (row.mask >> label) & 1:
                    rep ^= reps[row.sector][position]
            if rng is not None and inner_rows[row.sector]:
                for stabilizer in inner_rows[row.sector]:
                    if rng.random() < 0.5:
                        rep ^= stabilizer
            mask |= shift(rep, block)
        lifted_ids[row.id] = add("L" + row.sector, row.sector, mask)
    tower = CodeState(tuple(range(n_in * len(groups))), tuple(rows),
                      frozenset(row.id for row in rows))
    tower.validate()
    return tower, lifted_ids


def random_css(rng, labels, x_rows, z_rows, ids=("a", "b"), attempts=60):
    """A random valid CSS state on ``labels`` with the requested numbers of
    independent, mutually commuting X and Z rows (``None`` when the draw
    fails)."""
    masks = {"X": [], "Z": []}
    rows = []
    targets = {"X": x_rows, "Z": z_rows}
    order = ["X", "Z"] if rng.random() < 0.5 else ["Z", "X"]
    for side in order:
        other = "Z" if side == "X" else "X"
        for _ in range(targets[side]):
            for _attempt in range(attempts):
                size = rng.randint(1, len(labels))
                support = tuple(sorted(rng.sample(labels, size)))
                mask = sum(1 << q for q in support)
                if (all((mask & m).bit_count() % 2 == 0 for m in masks[other])
                        and rank(masks[side] + [mask]) == len(masks[side]) + 1):
                    masks[side].append(mask)
                    letter = ids[0] if side == "X" else ids[1]
                    rows.append(Row("%s%d" % (letter, len(masks[side])), side, support))
                    break
            else:
                return None
    state = CodeState(tuple(labels), tuple(rows), frozenset(row.id for row in rows))
    state.validate()
    return state


def random_inner(rng, n_in=4, k_in=2):
    """A random inner code on ``n_in`` qubits with ``k_in`` logical qubits."""
    checks = n_in - k_in
    while True:
        x_rows = rng.randint(0, checks)
        state = random_css(rng, list(range(n_in)), x_rows, checks - x_rows)
        if state is not None:
            return state


def random_outer(rng, n_out, k_in, tau):
    """A random outer code on ``n_out`` blocks of ``k_in`` qubits with at
    least one row in the deleted sector ``tau``. Returns ``(state, groups)``."""
    labels = list(range(n_out * k_in))
    groups = [tuple(labels[j * k_in:(j + 1) * k_in]) for j in range(n_out)]
    while True:
        tau_rows = rng.randint(1, min(3, len(labels)))
        other_rows = rng.randint(0, min(2, len(labels) - tau_rows))
        x_rows, z_rows = (tau_rows, other_rows) if tau == "X" else (other_rows, tau_rows)
        state = random_css(rng, labels, x_rows, z_rows, ids=("p", "q"))
        if state is not None:
            return state, groups


def unrefined_prices(inner_level, outer, deleted_ids):
    """The prices the unrefined dictionary would give: the inner sector
    distance times the outer Hamming-weight price."""
    tau = next(row.sector for row in outer.rows if row.id in set(deleted_ids))
    sigma = "Z" if tau == "X" else "X"
    return {"w_exp": inner_level["distance"][sigma] * exposure_price_exhaustive(outer, deleted_ids),
            "w_del": inner_level["distance"][tau] * deletion_price_exhaustive(outer, deleted_ids)}


def check_instance(inner, outer, groups, deleted_ids, rng, oracle=True):
    """Compare the provider with exhaustive prices on the built tower.

    Returns a dict with both price pairs, whether they agree (``ok``),
    whether the unrefined dictionary would have disagreed
    (``refinement_needed``), and the priced-cell check against the oracle
    (``cell_ok``, ``None`` when skipped).
    """
    level = tower_level_data(inner)
    verdict = tower_deletion_prices(inner, outer, groups, deleted_ids, level_data=level)
    tower, lifted = concatenate(inner, outer, groups, rng=rng)
    lifted_deleted = [lifted[row_id] for row_id in deleted_ids]
    exhaustive = {"w_exp": exposure_price_exhaustive(tower, lifted_deleted),
                  "w_del": deletion_price_exhaustive(tower, lifted_deleted)}
    ok = (verdict["status"] == "computed"
          and verdict["w_exp"] == exhaustive["w_exp"]
          and verdict["w_del"] == exhaustive["w_del"])
    unrefined = unrefined_prices(level, outer, deleted_ids)
    result = {
        "k_in": level["k_in"], "n_out": len(groups), "tower_n": len(tower.Q),
        "deleted": list(deleted_ids), "sector": verdict.get("sector"),
        "provider": {"w_exp": verdict["w_exp"], "w_del": verdict["w_del"]},
        "exhaustive": exhaustive, "unrefined": unrefined,
        "ok": ok,
        "refinement_needed": (unrefined["w_exp"] != exhaustive["w_exp"]
                              or unrefined["w_del"] != exhaustive["w_del"]),
        "cell_ok": None,
    }
    if oracle and ok and len(tower.Q) <= 16:
        parent = exact_distances(tower)
        child = tower
        for row_id in lifted_deleted:
            child = child.delete_check(row_id)
        child_exact = exact_distances(child)
        if parent["d"] is not None:
            predicted = min(parent["d"], verdict["w_del"], verdict["w_exp"])
            result["cell_ok"] = (child_exact["d"] == predicted)
            result["cell"] = {"d": parent["d"], "d_child": child_exact["d"], "predicted": predicted}
    return result


def run(seed=327, trials=60, verbose=False, oracle=True):
    """Seeded sweep over inner codes with n_in = 4 and k_in in {1, 2, 3}."""
    rng = random.Random(seed)
    started = time.perf_counter()
    report = {"seed": seed, "trials": 0, "mismatches": [], "cell_mismatches": [],
              "cell_checks": 0, "refinement_needed": 0, "k_in_histogram": {},
              "max_tower_n": 0}
    for trial in range(trials):
        k_in = (1, 2, 2, 3)[trial % 4]
        n_out = rng.randint(2, 4 if k_in <= 2 else 3)
        tau = rng.choice(("X", "Z"))
        inner = random_inner(rng, 4, k_in)
        outer, groups = random_outer(rng, n_out, k_in, tau)
        tau_ids = [row.id for row in outer.sector_rows(tau)]
        deleted = rng.sample(tau_ids, rng.randint(1, min(2, len(tau_ids))))
        result = check_instance(inner, outer, groups, deleted, rng, oracle=oracle)
        report["trials"] += 1
        report["k_in_histogram"][str(k_in)] = report["k_in_histogram"].get(str(k_in), 0) + 1
        report["max_tower_n"] = max(report["max_tower_n"], result["tower_n"])
        if not result["ok"]:
            report["mismatches"].append(result)
        if result["refinement_needed"]:
            report["refinement_needed"] += 1
        if result["cell_ok"] is not None:
            report["cell_checks"] += 1
            if not result["cell_ok"]:
                report["cell_mismatches"].append(result)
        if verbose:
            print(json.dumps(result, sort_keys=True))
    report["elapsed_seconds"] = round(time.perf_counter() - started, 2)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--seed", type=int, default=327)
    parser.add_argument("--trials", type=int, default=60)
    parser.add_argument("--no-oracle", action="store_true",
                        help="skip the exact-distance check of the priced cell")
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()
    report = run(seed=args.seed, trials=args.trials, verbose=args.verbose,
                 oracle=not args.no_oracle)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 1 if (report["mismatches"] or report["cell_mismatches"]) else 0


if __name__ == "__main__":
    raise SystemExit(main())
