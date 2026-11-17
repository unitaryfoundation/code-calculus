#!/usr/bin/env python3
"""Column-splitting reduction for the exposure price (issue #326).

`design/DERIVED_RELATIONS.md` section 3a derives that the exposure price of a
check deletion is as hard at column weight three as in general: a parent
whose Z-check matrix has maximum column weight c_max is split into t copies
of every qubit, t = max(1, c_max - 2), joined by weight-two equality rows, and
the split parent has Z column weight at most three and exposure price exactly
t times the original. This script builds the split and checks the equality
against exhaustive enumeration on random small parents. Agreement is
evidence that the gadget is transcribed as derived; it is not a proof
(AGENTS.md, never claim a proof). Nothing here is a consumer path: the
enumeration is oracle-only and the consumer's provider stays weight-2-only.
"""

import argparse
import json
import os
import random
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from machine.priced_calculus import (  # noqa: E402
    CodeState,
    Row,
    column_weights,
    graphlike_exposure_price,
    is_graphlike,
    rank,
)


def exposure_price_exhaustive(state, deleted_ids):
    """The exposure price of deleting ``deleted_ids`` by exhaustive enumeration.

    The exposed set is every vector with even overlap against the remaining
    checks of the deleted rows' sector and odd overlap against at least one
    deleted row; the price is its minimum weight, ``None`` when it is empty.
    Oracle-only: 2^n in the qubit count.
    """
    deleted_ids = set(deleted_ids)
    deleted = [row for row in state.rows if row.id in deleted_ids]
    if not deleted:
        raise ValueError("no deleted row found")
    sector = deleted[0].sector
    if any(row.sector != sector for row in deleted):
        raise ValueError("deleted rows span both sectors")
    remaining = [row.mask for row in state.sector_rows(sector)
                 if row.id not in deleted_ids]
    deleted_masks = [row.mask for row in deleted]
    labels = list(state.Q)
    best = None
    for bits in range(1, 1 << len(labels)):
        mask = 0
        weight = 0
        for index, label in enumerate(labels):
            if (bits >> index) & 1:
                mask |= 1 << label
                weight += 1
        if best is not None and weight >= best:
            continue
        if any((row & mask).bit_count() & 1 for row in remaining):
            continue
        if any((row & mask).bit_count() & 1 for row in deleted_masks):
            best = weight
    return best


def split_copies(state, sector="Z"):
    """The copy count t = max(1, c_max - 2) of section 3a."""
    weights = column_weights(state, sector)
    c_max = max(weights.values(), default=0)
    return max(1, c_max - 2)


def copy_label(label, copies, index):
    """Label of copy ``index`` (0-based) of parent qubit ``label``."""
    return label * copies + index


def split_state(state, copies, sector="Z", equality_block="e", equality_base=1000):
    """The t-fold split C^(t) of section 3a, ``copies`` = t.

    Every qubit q becomes the copies q^0, ..., q^(t-1), labeled
    ``copy_label(q, t, i)``. Each parent row of ``sector`` keeps its id and
    takes exactly one copy of each of its qubits, assigned so that an end
    copy receives at most two parent rows and an inner copy at most one;
    consecutive copies are joined by the equality row {q^i, q^(i+1)}, whose
    identifier is drawn from the ``equality_block`` of the fixed identifier
    enumeration (`spec/STATE_MODEL.md` I3) starting at ``equality_base``; a
    row of the other sector takes every copy of each of its qubits. Raises
    ``ValueError`` when some qubit has more rows of ``sector`` than the
    copies can hold (c_q > t + 2 for t >= 2, c_q > 3 for t = 1), or when an
    equality identifier collides with a parent row.
    """
    if copies < 1:
        raise ValueError("copies must be positive")
    if copies == 1:
        capacity = [3]
    else:
        capacity = [2] + [1] * (copies - 2) + [2]
    labels = list(state.Q)
    slot = {q: 0 for q in labels}
    load = {q: [0] * copies for q in labels}
    assignment = {}
    for row in state.sector_rows(sector):
        for q in row.support:
            while slot[q] < copies and load[q][slot[q]] >= capacity[slot[q]]:
                slot[q] += 1
            if slot[q] >= copies:
                raise ValueError(
                    "qubit %r lies in more %s-rows than %d copies can hold"
                    % (q, sector, copies))
            load[q][slot[q]] += 1
            assignment[(row.id, q)] = copy_label(q, copies, slot[q])
    rows = []
    for row in state.rows:
        if row.sector == sector:
            support = tuple(sorted(assignment[(row.id, q)] for q in row.support))
        else:
            support = tuple(sorted(copy_label(q, copies, i)
                                   for q in row.support for i in range(copies)))
        rows.append(Row(row.id, row.sector, support))
    existing = {row.id for row in state.rows}
    for q in labels:
        for i in range(copies - 1):
            rid = "%s%d" % (equality_block, equality_base + q * copies + i)
            if rid in existing:
                raise ValueError("equality row id %r collides" % rid)
            rows.append(Row(rid, sector, (copy_label(q, copies, i),
                                          copy_label(q, copies, i + 1))))
    new_labels = tuple(sorted(copy_label(q, copies, i)
                              for q in labels for i in range(copies)))
    used = frozenset(state.used) | frozenset(row.id for row in rows)
    child = CodeState(new_labels, tuple(rows), used)
    child.validate()
    return child


def random_parent(rng, n, offset=0):
    """A random CSS parent on ``n`` qubits: one to five independent Z-rows
    and up to two independent X-rows commuting with every Z-row (the state
    model's invariants, `spec/STATE_MODEL.md`)."""
    labels = [offset + i for i in range(n)]
    rows = []
    z_masks = []
    for _ in range(rng.randint(1, 5)):
        size = rng.randint(1, n)
        support = tuple(sorted(rng.sample(labels, size)))
        mask = sum(1 << q for q in support)
        if rank(z_masks + [mask]) == len(z_masks) + 1:
            z_masks.append(mask)
            rows.append(Row("b%d" % (len(rows) + 1), "Z", support))
    x_rows = []
    x_masks = []
    for _ in range(rng.randint(0, 2)):
        for _attempt in range(20):
            size = rng.randint(1, n)
            support = tuple(sorted(rng.sample(labels, size)))
            mask = sum(1 << q for q in support)
            if (all((mask & z).bit_count() % 2 == 0 for z in z_masks)
                    and rank(x_masks + [mask]) == len(x_masks) + 1):
                x_masks.append(mask)
                x_rows.append(Row("a%d" % (len(x_rows) + 1), "X", support))
                break
    state = CodeState(tuple(labels), tuple(rows + x_rows),
                      frozenset(row.id for row in rows + x_rows))
    state.validate()
    return state


def check_instance(state, deleted_ids, copies):
    """Split ``state`` with ``copies`` and compare exposure prices.

    Returns a dict with the parent and split prices, the split's maximum Z
    column weight, and ``ok`` when the split price is ``copies`` times the
    parent price (``None`` on both sides when the exposed set is empty).
    """
    parent_price = exposure_price_exhaustive(state, deleted_ids)
    child = split_state(state, copies)
    child_price = exposure_price_exhaustive(child, deleted_ids)
    expected = None if parent_price is None else copies * parent_price
    return {
        "n": len(state.Q), "copies": copies, "split_n": len(child.Q),
        "parent_price": parent_price, "split_price": child_price,
        "split_max_column_weight": max(column_weights(child, "Z").values()),
        "ok": child_price == expected,
    }


def run(seed=326, trials=60, verbose=False):
    rng = random.Random(seed)
    report = {"seed": seed, "trials": 0, "mismatches": [],
              "column_weight_violations": [], "provider_mismatches": [],
              "nontrivial_splits": 0, "finite_prices": 0,
              "larger_copy_checks": 0, "graphlike_parents": 0}
    started = time.time()
    for trial in range(trials):
        n = rng.randint(3, 5)
        state = random_parent(rng, n, offset=rng.choice((0, 0, 7)))
        z_ids = [row.id for row in state.sector_rows("Z")]
        deleted = rng.sample(z_ids, min(len(z_ids), rng.randint(1, 2)))
        copies = split_copies(state)
        result = check_instance(state, deleted, copies)
        report["trials"] += 1
        if copies > 1:
            report["nontrivial_splits"] += 1
        if result["parent_price"] is not None:
            report["finite_prices"] += 1
        if not result["ok"]:
            report["mismatches"].append({"trial": trial, **result})
        if result["split_max_column_weight"] > 3:
            report["column_weight_violations"].append({"trial": trial, **result})
        # The equality holds for every admissible copy count, not only the
        # smallest; check one more copy where the enumeration stays small.
        if n * (copies + 1) <= 16:
            more = check_instance(state, deleted, copies + 1)
            report["larger_copy_checks"] += 1
            if not more["ok"]:
                report["mismatches"].append({"trial": trial, "larger": True, **more})
        # Sanity on the weight-2 provider (Theorem 25.1): where the parent
        # is graphlike the provider must agree with the enumeration.
        if is_graphlike(state, "Z"):
            report["graphlike_parents"] += 1
            verdict = graphlike_exposure_price(state, deleted=deleted)
            provided = verdict["w_exp"] if verdict["status"] == "computed" else None
            if provided != result["parent_price"]:
                report["provider_mismatches"].append(
                    {"trial": trial, "provider": verdict, "exhaustive": result["parent_price"]})
        if verbose:
            print(json.dumps({"trial": trial, "deleted": deleted, **result}))
    report["elapsed_seconds"] = round(time.time() - started, 2)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--seed", type=int, default=326)
    parser.add_argument("--trials", type=int, default=60)
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()
    report = run(args.seed, args.trials, args.verbose)
    print(json.dumps(report, indent=2))
    bad = report["mismatches"] or report["column_weight_violations"] or report["provider_mismatches"]
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
