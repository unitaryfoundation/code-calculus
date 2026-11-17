#!/usr/bin/env python3
"""Class pairs under `E-GLUE`: no re-exposed class, exact glued distance (issue #328).

`spec/OPERATIONAL_SEMANTICS.md` section 4.33 derives, for the admitted
`E-GLUE` transition (two factors on disjoint qubit sets plus admissible seam
checks), that every logical of the glued state restricts to a logical of at
least one factor, so no class is re-exposed by the seam, and that the glued
sector distance is the least sum of factor class weights over the class
pairs that commute with the opposite-sector seam checks and are not absorbed
by the same-sector seam checks. This script builds random glues, enumerates
the glued logicals to look for a re-exposed class, evaluates the class-pair
formula from factor data and seam data alone, and compares it with the
exact-distance oracle on the glued state. Agreement is evidence that the
derivation is transcribed as stated, not a proof (AGENTS.md). Oracle-side
only: nothing here is a consumer path.
"""

import argparse
import itertools
import json
import os
import random
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from machine.oracle import exact_distances  # noqa: E402
from machine.priced_calculus import (  # noqa: E402
    CodeState,
    Row,
    _basis,
    in_span,
    rank,
)

CERTIFICATE = {"move_words": ["U", "U"],
               "evidence": "experiment: class-pair check, consumer policy only (issue #328)"}


def reduce_modulo(vector, basis):
    """The canonical representative of ``vector`` modulo the span whose
    pivot basis is ``basis`` (as returned by ``_basis``)."""
    for pivot in sorted(basis, reverse=True):
        if (vector >> pivot) & 1:
            vector ^= basis[pivot]
    return vector


def sector_vectors(state, sector):
    """Every ``sector``-type vector on the state's qubits that commutes with
    the opposite sector's displayed rows (the sector normalizer); 2^n."""
    opposite = "Z" if sector == "X" else "X"
    rows = [row.mask for row in state.sector_rows(opposite)]
    labels = list(state.Q)
    out = []
    for bits in range(1 << len(labels)):
        mask = 0
        for index, label in enumerate(labels):
            if (bits >> index) & 1:
                mask |= 1 << label
        if all((mask & row).bit_count() % 2 == 0 for row in rows):
            out.append(mask)
    return out


def class_data(state, sector):
    """The sector's logical classes of a factor: canonical class key ->
    (least weight, a representative). Key ``0`` is the stabilizer class."""
    basis = _basis([row.mask for row in state.sector_rows(sector)])
    classes = {}
    for vector in sector_vectors(state, sector):
        key = reduce_modulo(vector, basis)
        weight = vector.bit_count()
        if key not in classes or weight < classes[key][0]:
            classes[key] = (weight, vector)
    return classes, basis


def seam_rows(left, right, child):
    """The glued state's rows that are not factor rows: the seam checks."""
    factor_ids = {row.id for row in left.rows} | {row.id for row in right.rows}
    return [row for row in child.rows if row.id not in factor_ids]


def class_pair_distance(left, right, child, sector):
    """The glued sector distance from factor class data and seam class data.

    Pairs of factor classes commuting with every opposite-sector seam check
    form ``K``; the class pairs of the same-sector seam checks span ``W``;
    the formula is the least ``mu_A + mu_B`` over ``K`` minus ``W``
    (section 4.33). Returns a dict with the value (``None`` when no pair is
    left, that is, the glued code has no logical in the sector), the factor
    distances, whether a pure pair of weight ``min(d_A, d_B)`` survives (the
    glued distance equals the factor minimum exactly then), and the pair
    counts.
    """
    opposite = "Z" if sector == "X" else "X"
    data_a, basis_a = class_data(left, sector)
    data_b, basis_b = class_data(right, sector)
    mask_a = sum(1 << q for q in left.Q)
    mask_b = sum(1 << q for q in right.Q)
    seams = seam_rows(left, right, child)
    tau_seams = [row.mask for row in seams if row.sector == opposite]
    sigma_seams = [row.mask for row in seams if row.sector == sector]
    # W: the span of the class pairs of the same-sector seam checks.
    generators = [(reduce_modulo(s & mask_a, basis_a), reduce_modulo(s & mask_b, basis_b))
                  for s in sigma_seams]
    absorbed = {(0, 0)}
    for count in range(1, len(generators) + 1):
        for subset in itertools.combinations(generators, count):
            pair_a = 0
            pair_b = 0
            for key_a, key_b in subset:
                pair_a ^= key_a
                pair_b ^= key_b
            absorbed.add((reduce_modulo(pair_a, basis_a), reduce_modulo(pair_b, basis_b)))
    best = None
    in_k = 0
    survivors = 0
    distance_a = min((w for key, (w, _) in data_a.items() if key != 0), default=None)
    distance_b = min((w for key, (w, _) in data_b.items() if key != 0), default=None)
    factor_minimum = min((w for w in (distance_a, distance_b) if w is not None), default=None)
    pure_minimum_survives = False
    for key_a, (weight_a, rep_a) in data_a.items():
        for key_b, (weight_b, rep_b) in data_b.items():
            vector = rep_a | rep_b
            if any((vector & t).bit_count() % 2 for t in tau_seams):
                continue
            in_k += 1
            if (key_a, key_b) in absorbed:
                continue
            survivors += 1
            weight = weight_a + weight_b
            if best is None or weight < best:
                best = weight
            # A pure pair of the overall factor minimum survives: this is the
            # survival statement behind the equality d = min(d_A, d_B).
            if (key_a == 0 or key_b == 0) and weight == factor_minimum:
                pure_minimum_survives = True
    return {"value": best, "d_A": distance_a, "d_B": distance_b,
            "pure_minimum_survives": pure_minimum_survives,
            "pairs": len(data_a) * len(data_b), "pairs_in_K": in_k,
            "pairs_surviving": survivors, "absorbed": len(absorbed),
            "tau_seams": len(tau_seams), "sigma_seams": len(sigma_seams)}


def re_exposed_logicals(left, right, child, sector):
    """Glued ``sector`` logicals whose restrictions to both factors are factor
    stabilizers. Section 4.33 derives that there are none; 2^n."""
    same = [row.mask for row in child.sector_rows(sector)]
    span_a = [row.mask for row in left.sector_rows(sector)]
    span_b = [row.mask for row in right.sector_rows(sector)]
    mask_a = sum(1 << q for q in left.Q)
    mask_b = sum(1 << q for q in right.Q)
    found = []
    for vector in sector_vectors(child, sector):
        if vector == 0 or in_span(vector, same):
            continue
        if in_span(vector & mask_a, span_a) and in_span(vector & mask_b, span_b):
            found.append(vector)
    return found


def random_css(rng, labels, letters, max_rows=3, attempts=60):
    """A random valid CSS state on ``labels`` with row ids from ``letters``
    (one letter per sector), zero to ``max_rows`` rows per sector."""
    masks = {"X": [], "Z": []}
    rows = []
    for side in rng.sample(["X", "Z"], 2):
        other = "Z" if side == "X" else "X"
        for _ in range(rng.randint(0, max_rows)):
            for _attempt in range(attempts):
                size = rng.randint(1, len(labels))
                support = tuple(sorted(rng.sample(labels, size)))
                mask = sum(1 << q for q in support)
                if (all((mask & m).bit_count() % 2 == 0 for m in masks[other])
                        and rank(masks[side] + [mask]) == len(masks[side]) + 1):
                    masks[side].append(mask)
                    letter = letters[0] if side == "X" else letters[1]
                    rows.append(Row("%s%d" % (letter, len(masks[side])), side, support))
                    break
    state = CodeState(tuple(labels), tuple(rows), frozenset(row.id for row in rows))
    state.validate()
    return state


def random_seams(rng, left, right, count, attempts=80):
    """Up to ``count`` admissible seam checks for the two factors, drawn at
    random: each commutes with the opposite-sector rows so far (factor rows
    and earlier seams) and lies outside the same-sector span so far."""
    labels = list(left.Q) + list(right.Q)
    rows = {"X": [row.mask for row in left.sector_rows("X")] + [row.mask for row in right.sector_rows("X")],
            "Z": [row.mask for row in left.sector_rows("Z")] + [row.mask for row in right.sector_rows("Z")]}
    seams = []
    for _ in range(count):
        for _attempt in range(attempts):
            sector = rng.choice(("X", "Z"))
            other = "Z" if sector == "X" else "X"
            size = rng.randint(1, len(labels))
            support = sorted(rng.sample(labels, size))
            mask = sum(1 << q for q in support)
            if (all((mask & m).bit_count() % 2 == 0 for m in rows[other])
                    and not in_span(mask, rows[sector])):
                rows[sector].append(mask)
                seams.append((sector, support))
                break
    return seams


def glue(left, right, seams):
    """The glued state through the consumer's transition (the certificate is
    consumer policy; the derivation does not use it)."""
    return left.glue(right, seam_checks=list(seams), seam_certificate=dict(CERTIFICATE))


def check_instance(left, right, seams):
    """Compare the class-pair formula with the oracle in both sectors and
    look for re-exposed logicals."""
    child = glue(left, right, seams)
    exact = exact_distances(child)
    result = {"n": len(child.Q), "seams": seams, "sectors": {}, "ok": True,
              "re_exposed": 0}
    for sector in ("X", "Z"):
        formula = class_pair_distance(left, right, child, sector)
        exposed = re_exposed_logicals(left, right, child, sector)
        agree = formula["value"] == exact[sector]
        finite = formula["d_A"] is not None or formula["d_B"] is not None
        factor_min = min(w for w in (formula["d_A"], formula["d_B"]) if w is not None) if finite else None
        survival_consistent = (
            formula["value"] is None
            or factor_min is None
            or ((formula["value"] == factor_min) == formula["pure_minimum_survives"]))
        result["sectors"][sector] = {
            "formula": formula["value"], "oracle": exact[sector],
            "d_A": formula["d_A"], "d_B": formula["d_B"],
            "pure_minimum_survives": formula["pure_minimum_survives"],
            "pairs": formula["pairs"], "surviving": formula["pairs_surviving"],
            "re_exposed": len(exposed), "agree": agree,
            "survival_consistent": survival_consistent}
        result["re_exposed"] += len(exposed)
        if not (agree and survival_consistent) or exposed:
            result["ok"] = False
    return result


def run(seed=328, trials=80, verbose=False):
    """Seeded sweep: random factors on two to five qubits each, zero to three
    admissible seam checks."""
    rng = random.Random(seed)
    started = time.perf_counter()
    report = {"seed": seed, "trials": 0, "mismatches": [], "re_exposed_total": 0,
              "seam_histogram": {}, "raised_above_factor_minimum": 0,
              "equal_to_factor_minimum": 0, "max_n": 0}
    for _ in range(trials):
        n_a = rng.randint(2, 5)
        n_b = rng.randint(2, 5)
        left = random_css(rng, list(range(n_a)), ("a", "b"))
        right = random_css(rng, list(range(n_a, n_a + n_b)), ("c", "d"))
        seams = random_seams(rng, left, right, rng.randint(0, 3))
        result = check_instance(left, right, seams)
        report["trials"] += 1
        key = str(len(seams))
        report["seam_histogram"][key] = report["seam_histogram"].get(key, 0) + 1
        report["max_n"] = max(report["max_n"], result["n"])
        report["re_exposed_total"] += result["re_exposed"]
        for sector in ("X", "Z"):
            cell = result["sectors"][sector]
            finite = [w for w in (cell["d_A"], cell["d_B"]) if w is not None]
            if cell["formula"] is not None and finite:
                if cell["formula"] == min(finite):
                    report["equal_to_factor_minimum"] += 1
                else:
                    report["raised_above_factor_minimum"] += 1
        if not result["ok"]:
            report["mismatches"].append(result)
        if verbose:
            print(json.dumps(result, sort_keys=True))
    report["elapsed_seconds"] = round(time.perf_counter() - started, 2)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--seed", type=int, default=328)
    parser.add_argument("--trials", type=int, default=80)
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()
    report = run(seed=args.seed, trials=args.trials, verbose=args.verbose)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 1 if (report["mismatches"] or report["re_exposed_total"]) else 0


if __name__ == "__main__":
    raise SystemExit(main())
