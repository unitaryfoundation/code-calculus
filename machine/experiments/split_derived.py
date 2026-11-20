#!/usr/bin/env python3
"""The separating deletion behind a candidate `E-SPLIT`.

`the E-split proposal note` states a candidate `E-SPLIT` as a derived
command: given a block of qubits and a set of displayed rows that contains
every row meeting both the block and its complement, delete those rows. The
child is separated, and the proposal derives the following for it.

1. `n' = n`, `k' = k + t` for `t` deleted rows, `used' = used`.
2. No sector distance rises.
3. Each sector distance of the child is the minimum of the distances of the
   two block restrictions.
4. Each sector distance of the child is `min(d, w_del, w_exp)`, with
   `w_del` the least weight of a parent stabilizer that is not a child
   stabilizer and `w_exp` the least weight of a vector that commutes with
   the child's opposite sector and not with the parent's.
5. A display needs at least
   `rank(S|A) + rank(S|B) - rank(S)` deletions in a sector whose row space
   is `S`, and that number is the codimension in `S` of the vectors of `S`
   that split into a part of `S` on each block.
6. Deleting the seam rows of an `E-GLUE` returns the rows and qubits of the
   direct sum, with `used` grown by the seam identifiers.

This script draws random states, blocks, and cut sets, runs the deletions
through the consumer's own `delete_check`, and compares each statement with
the exhaustive oracle. Agreement is evidence that the derivations are
transcribed as stated, not a proof (AGENTS.md). Oracle-side only: nothing
here is a consumer path, and no transition is added.
"""

import argparse
import json
import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
for path in (ROOT, HERE):
    if path not in sys.path:
        sys.path.insert(0, path)

import glue_class_pairs as pairs  # noqa: E402
from machine.oracle import exact_distances  # noqa: E402
from machine.priced_calculus import (  # noqa: E402
    CodeState,
    in_span,
    rank,
)

SECTORS = ("X", "Z")


def block_mask(block):
    return sum(1 << q for q in block)


def crossing_rows(state, block):
    """Displayed rows whose support meets both ``block`` and its complement."""
    inside = block_mask(block)
    outside = block_mask(q for q in state.Q if q not in set(block))
    return [row for row in state.rows if row.mask & inside and row.mask & outside]


def is_separated(state, block):
    return not crossing_rows(state, block)


def split(state, cut_ids):
    """The candidate transition: `C-DELETE-CHECK` at each cut identifier, in
    the order given, through the consumer's transition."""
    child = state
    for identifier in cut_ids:
        child = child.delete_check(identifier)
    return child


def restriction(state, block):
    """The display a separated state induces on ``block``: the block's qubits
    and the rows supported inside it. Oracle-side: the calculus has no
    transition that produces this state."""
    labels = tuple(q for q in state.Q if q in set(block))
    inside = block_mask(labels)
    rows = tuple(row for row in state.rows if row.mask and not row.mask & ~inside)
    result = CodeState(labels, rows, frozenset(row.id for row in rows))
    result.validate()
    return result


def least(values):
    """Minimum with ``None`` for the empty set (the `+inf` convention)."""
    finite = [value for value in values if value is not None]
    return min(finite) if finite else None


def promoted_and_exposed(parent, child, sector):
    """``(w_del, w_exp)`` for the sector, by enumeration (2^n).

    ``w_del`` is the least weight of a vector in the parent's sector span
    and outside the child's. ``w_exp`` is the least weight of a vector that
    commutes with the child's opposite-sector rows and not with the
    parent's."""
    parent_span = [row.mask for row in parent.sector_rows(sector)]
    child_span = [row.mask for row in child.sector_rows(sector)]
    parent_normalizer = set(pairs.sector_vectors(parent, sector))
    w_del = None
    w_exp = None
    for vector in pairs.sector_vectors(child, sector):
        weight = vector.bit_count()
        if vector in parent_normalizer:
            if in_span(vector, parent_span) and not in_span(vector, child_span):
                if w_del is None or weight < w_del:
                    w_del = weight
        elif w_exp is None or weight < w_exp:
            w_exp = weight
    return w_del, w_exp


def cut_rank(state, block, sector):
    """``rank(S|A) + rank(S|B) - rank(S)`` for the sector's row space ``S``."""
    inside = block_mask(block)
    outside = block_mask(q for q in state.Q if q not in set(block))
    rows = [row.mask for row in state.sector_rows(sector)]
    return (rank([m & inside for m in rows]) + rank([m & outside for m in rows])
            - rank(rows))


def decomposable_codimension(state, block, sector):
    """The codimension, in the sector's row space, of the vectors that are a
    sum of a span vector inside ``block`` and one outside it. By enumeration
    of the span (2^rank)."""
    inside = block_mask(block)
    outside = block_mask(q for q in state.Q if q not in set(block))
    rows = [row.mask for row in state.sector_rows(sector)]
    span = {0}
    for row in rows:
        span |= {vector ^ row for vector in span}
    in_a = [vector for vector in span if not vector & outside]
    in_b = [vector for vector in span if not vector & inside]
    return rank(rows) - rank(in_a) - rank(in_b)


def check_instance(state, block, extra_ids=()):
    """Split ``state`` at ``block``, deleting the crossing rows and the rows
    named by ``extra_ids``, and compare every statement with the oracle."""
    crossing = crossing_rows(state, block)
    cut_ids = [row.id for row in crossing]
    cut_ids += [identifier for identifier in extra_ids if identifier not in cut_ids]
    child = split(state, cut_ids)
    child.validate()
    complement = [q for q in state.Q if q not in set(block)]
    part_a = restriction(child, block)
    part_b = restriction(child, complement)
    exact_parent = exact_distances(state)
    exact_child = exact_distances(child)
    exact_a = exact_distances(part_a)
    exact_b = exact_distances(part_b)
    result = {
        "n": len(state.Q), "block": list(block), "cut": len(cut_ids),
        "crossing": len(crossing), "ok": True, "sectors": {},
        "structure": {
            "n": child.n() == state.n(),
            "k": child.k() == state.k() + len(cut_ids),
            "k_blocks": child.k() == part_a.k() + part_b.k(),
            "used": child.used == state.used,
            "Q": child.Q == state.Q,
            "separated": is_separated(child, block),
        },
    }
    if not all(result["structure"].values()):
        result["ok"] = False
    for sector in SECTORS:
        w_del, w_exp = promoted_and_exposed(state, child, sector)
        d_parent = exact_parent[sector]
        d_child = exact_child[sector]
        non_increase = d_parent is None or (d_child is not None and d_child <= d_parent)
        blocks = least([exact_a[sector], exact_b[sector]])
        priced = least([d_parent, w_del, w_exp])
        crossing_sector = sum(1 for row in crossing if row.sector == sector)
        lower = cut_rank(state, block, sector)
        cell = {
            "d_parent": d_parent, "d_child": d_child, "d_A": exact_a[sector],
            "d_B": exact_b[sector], "w_del": w_del, "w_exp": w_exp,
            "non_increase": non_increase,
            "block_minimum": blocks == d_child,
            "priced": priced == d_child,
            "crossing": crossing_sector, "cut_rank": lower,
            "cut_rank_bound": crossing_sector >= lower,
            "cut_rank_is_codimension":
                lower == decomposable_codimension(state, block, sector),
            "strict_drop": d_parent is not None and d_child is not None
                           and d_child < d_parent,
        }
        result["sectors"][sector] = cell
        if not (cell["non_increase"] and cell["block_minimum"] and cell["priced"]
                and cell["cut_rank_bound"] and cell["cut_rank_is_codimension"]):
            result["ok"] = False
    return result


def check_glue_inverse(left, right, seams):
    """Glue, then delete the seam rows: the rows and qubits are those of the
    direct sum and `used` has grown by the seam identifiers."""
    glued = pairs.glue(left, right, seams)
    seam_ids = [row.id for row in pairs.seam_rows(left, right, glued)]
    child = split(glued, seam_ids)
    summed = CodeState.direct_sum(left, right)
    exact_child = exact_distances(child)
    exact_glued = exact_distances(glued)
    exact_left = exact_distances(left)
    exact_right = exact_distances(right)
    result = {
        "seams": len(seam_ids),
        "rows": child.rows == summed.rows,
        "Q": set(child.Q) == set(summed.Q),
        "used": child.used == summed.used | frozenset(seam_ids),
        "used_grows": bool(seam_ids) == (child.used != summed.used),
        "separated": is_separated(child, left.Q),
        "k": child.k() == glued.k() + len(seam_ids),
    }
    for sector in SECTORS:
        factor_minimum = least([exact_left[sector], exact_right[sector]])
        result["d_" + sector] = exact_child[sector] == factor_minimum
        glued_d = exact_glued[sector]
        result["glue_bound_" + sector] = (
            glued_d is None or (factor_minimum is not None and factor_minimum <= glued_d))
    result["ok"] = all(value for key, value in result.items() if key != "seams")
    return result


def random_block(rng, labels):
    size = rng.randint(1, len(labels) - 1)
    return sorted(rng.sample(list(labels), size))


def run(seed=546, trials=200, verbose=False):
    """Seeded sweep: random states on three to seven qubits with a random
    block, and random glues on two to four qubits per factor."""
    rng = random.Random(seed)
    started = time.perf_counter()
    report = {"seed": seed, "trials": 0, "glue_trials": 0, "mismatches": [],
              "glue_mismatches": [], "strict_drops": 0, "cut_histogram": {},
              "extra_rows_deleted": 0, "above_cut_rank": 0, "max_n": 0}
    for _ in range(trials):
        n = rng.randint(3, 7)
        state = pairs.random_css(rng, list(range(n)), ("a", "b"), max_rows=3)
        block = random_block(rng, state.Q)
        crossing_ids = {row.id for row in crossing_rows(state, block)}
        others = [row.id for row in state.rows if row.id not in crossing_ids]
        extra = rng.sample(others, rng.randint(0, min(1, len(others))))
        result = check_instance(state, block, extra)
        report["trials"] += 1
        report["extra_rows_deleted"] += len(extra)
        report["max_n"] = max(report["max_n"], result["n"])
        key = str(result["cut"])
        report["cut_histogram"][key] = report["cut_histogram"].get(key, 0) + 1
        for sector in SECTORS:
            cell = result["sectors"][sector]
            report["strict_drops"] += int(cell["strict_drop"])
            report["above_cut_rank"] += int(cell["crossing"] > cell["cut_rank"])
        if not result["ok"]:
            report["mismatches"].append(result)
        if verbose:
            print(json.dumps(result, sort_keys=True))
    for _ in range(trials // 2):
        n_a = rng.randint(2, 4)
        n_b = rng.randint(2, 4)
        left = pairs.random_css(rng, list(range(n_a)), ("a", "b"))
        right = pairs.random_css(rng, list(range(n_a, n_a + n_b)), ("c", "d"))
        seams = pairs.random_seams(rng, left, right, rng.randint(0, 3))
        result = check_glue_inverse(left, right, seams)
        report["glue_trials"] += 1
        if not result["ok"]:
            report["glue_mismatches"].append(result)
        if verbose:
            print(json.dumps(result, sort_keys=True))
    report["elapsed_seconds"] = round(time.perf_counter() - started, 2)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--seed", type=int, default=546)
    parser.add_argument("--trials", type=int, default=200)
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()
    report = run(seed=args.seed, trials=args.trials, verbose=args.verbose)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 1 if (report["mismatches"] or report["glue_mismatches"]) else 0


if __name__ == "__main__":
    raise SystemExit(main())
