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
only: nothing here is a consumer path.  This module imports the exact-distance
oracle at module level; it is a verifier-side tool and must not be imported by
consumer modules (machine.priced_calculus, machine.planner, machine.entrypoints).
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


def _class_pair_distance_states(left, right, child, sector):
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


# Consumer helper: class-pair calculation from supplied factor class dictionaries.
# This does not enumerate 2^n factor logicals and does not claim lower bounds;
# it consumes caller-supplied class weights/representatives and seam data.

from machine.state import opposite_sector_name  # noqa: E402


def _as_mask(value, mask_a=None, mask_b=None):
    if isinstance(value, int):
        return value
    if isinstance(value, (list, tuple)):
        # support list -> mask over consecutive labels; fall back to summing
        return sum(1 << int(q) for q in value)
    if isinstance(value, dict):
        if "mask" in value:
            return int(value["mask"])
        if "support" in value:
            return sum(1 << int(q) for q in value["support"])
        if "qubits" in value:
            return sum(1 << int(q) for q in value["qubits"])
    # Row-like
    rid = getattr(value, "mask", None)
    if rid is not None:
        return int(rid)
    support = getattr(value, "support", None)
    if support is not None:
        return sum(1 << int(q) for q in support)
    sector = getattr(value, "sector", None)
    return None


def _normalize_class_entry(value, key=None):
    if isinstance(value, (tuple, list)):
        weight = value[0] if len(value) else 0
        rep = value[1] if len(value) > 1 else key
        return (weight, rep if rep is not None else key)
    if isinstance(value, dict):
        weight = value.get("weight", value.get("value",
                value.get("mu", value.get("min_weight", 0))))
        rep = value.get("representative", value.get("rep",
                value.get("vector", value.get("support", key))))
        if isinstance(rep, (list, tuple)):
            rep = sum(1 << int(q) for q in rep)
        if rep is None:
            rep = key
        return (weight, rep if rep is not None else key)
    # scalar weight
    return (value, key)


def _normalize_classes(classes):
    if isinstance(classes, (list, tuple)):
        out = {}
        for index, value in enumerate(classes):
            out[index] = _normalize_class_entry(value, index)
        return out
    if isinstance(classes, dict):
        out = {}
        for key, value in classes.items():
            k = key
            if isinstance(k, str):
                try:
                    k = int(k)
                except ValueError:
                    pass
            out[k] = _normalize_class_entry(value, k)
        return out
    return {}


def _reduce_modulo(vector, basis):
    if basis:
        return reduce_modulo(vector, basis)
    return vector


def _class_pair_distance_classes(classes_a, classes_b, tau_seams=None, sigma_seams=None,
                                 mask_a=None, mask_b=None, basis_a=None, basis_b=None,
                                 sector=None, seams=None, **kwargs):
    # Alias handling
    if tau_seams is None:
        tau_seams = kwargs.get("tau_seams", kwargs.get("tau", kwargs.get("opposite_seams",
                  kwargs.get("tau_checks"))))
    if sigma_seams is None:
        sigma_seams = kwargs.get("sigma_seams", kwargs.get("sigma", kwargs.get("same_seams",
                  kwargs.get("sigma_checks"))))
    if mask_a is None:
        mask_a = kwargs.get("mask_a", kwargs.get("mask_A"))
    if mask_b is None:
        mask_b = kwargs.get("mask_b", kwargs.get("mask_B"))
    if basis_a is None:
        basis_a = kwargs.get("basis_a", kwargs.get("basis_A"))
    if basis_b is None:
        basis_b = kwargs.get("basis_b", kwargs.get("basis_B"))
    if sector is None:
        sector = kwargs.get("sector")
    if seams is not None and (tau_seams is None or sigma_seams is None):
        # split seam list by sector if sector known
        tau_sector = opposite_sector_name(sector) if sector in ("X", "Z") else None
        tau_list, sigma_list = [], []
        for item in seams:
            sec = None
            if isinstance(item, (list, tuple)) and len(item) == 2 and isinstance(item[0], str):
                sec = item[0]
            elif isinstance(item, dict):
                sec = item.get("sector", item.get("side"))
            else:
                sec = getattr(item, "sector", None)
            m = _as_mask(item)
            if m is None:
                continue
            if tau_sector is not None and sec == tau_sector:
                tau_list.append(m)
            elif sector is not None and sec == sector:
                sigma_list.append(m)
            else:
                # unknown: treat as tau if not sigma? default sigma if sector matches
                sigma_list.append(m)
        if tau_seams is None:
            tau_seams = tau_list
        if sigma_seams is None:
            sigma_seams = sigma_list

    tau_masks = []
    for s in (tau_seams or []):
        m = _as_mask(s)
        if m is not None:
            tau_masks.append(m)
    sigma_masks = []
    for s in (sigma_seams or []):
        m = _as_mask(s)
        if m is not None:
            sigma_masks.append(m)

    data_a = _normalize_classes(classes_a)
    data_b = _normalize_classes(classes_b)

    # Infer masks from class representatives if missing.
    if mask_a is None:
        mask_a = 0
        for _w, rep in data_a.values():
            if isinstance(rep, int):
                mask_a |= rep
    if mask_b is None:
        mask_b = 0
        for _w, rep in data_b.values():
            if isinstance(rep, int):
                mask_b |= rep

    basis_a = basis_a or {}
    basis_b = basis_b or {}

    # W: span of class pairs of same-sector seam checks.
    generators = []
    for s in sigma_masks:
        ga = _reduce_modulo(s & (mask_a or 0), basis_a)
        gb = _reduce_modulo(s & (mask_b or 0), basis_b)
        generators.append((ga, gb))
    absorbed = {(0, 0)}
    for count in range(1, len(generators) + 1):
        for subset in itertools.combinations(generators, count):
            pair_a = 0
            pair_b = 0
            for key_a, key_b in subset:
                pair_a ^= key_a
                pair_b ^= key_b
            absorbed.add((_reduce_modulo(pair_a, basis_a), _reduce_modulo(pair_b, basis_b)))

    best = None
    in_k = 0
    survivors = 0
    distance_a = min((w for key, (w, _) in ((k, v) for k, v in data_a.items()) if key != 0), default=None)
    # Actually keys are class reps; nonzero classes are keys != 0
    distance_a = min((w for k, (w, _) in data_a.items() if k != 0), default=None)
    distance_b = min((w for k, (w, _) in data_b.items() if k != 0), default=None)
    factor_minimum = None
    finite = [w for w in (distance_a, distance_b) if w is not None]
    if finite:
        factor_minimum = min(finite)
    pure_minimum_survives = False
    for key_a, (weight_a, rep_a) in data_a.items():
        for key_b, (weight_b, rep_b) in data_b.items():
            # representative vector for class; use rep if available else key
            rep_a_vec = rep_a if isinstance(rep_a, int) else key_a
            rep_b_vec = rep_b if isinstance(rep_b, int) else key_b
            vector = rep_a_vec | rep_b_vec if isinstance(rep_a_vec, int) and isinstance(rep_b_vec, int) else 0
            # commute with tau seams
            if any(isinstance(t, int) and (vector & t).bit_count() % 2 for t in tau_masks):
                continue
            in_k += 1
            if (key_a, key_b) in absorbed:
                continue
            survivors += 1
            weight = weight_a + weight_b
            if best is None or weight < best:
                best = weight
            if (key_a == 0 or key_b == 0) and factor_minimum is not None and weight == factor_minimum:
                pure_minimum_survives = True
    pairs_count = len(data_a) * len(data_b)
    return {"value": best, "d_A": distance_a, "d_B": distance_b,
            "pure_minimum_survives": pure_minimum_survives,
            "pairs": pairs_count, "pairs_in_K": in_k,
            "pairs_surviving": survivors, "absorbed": len(absorbed),
            "tau_seams": len(tau_masks), "sigma_seams": len(sigma_masks)}


def class_pair_distance(*args, **kwargs):
    # State-based path
    if len(args) >= 3 and all(hasattr(a, "Q") and hasattr(a, "rows") for a in args[:3]):
        sector = kwargs.pop("sector", None)
        if sector is None and len(args) >= 4:
            sector = args[3]
            args = args[:3]
        return _class_pair_distance_states(args[0], args[1], args[2], sector, **kwargs)
    # kwargs-based state path
    left = kwargs.get("left", kwargs.get("factor_a", kwargs.get("factor_A", kwargs.get("a"))))
    right = kwargs.get("right", kwargs.get("factor_b", kwargs.get("factor_B", kwargs.get("b"))))
    child = kwargs.get("child", kwargs.get("glued", kwargs.get("result")))
    sector = kwargs.get("sector")
    if left is not None and right is not None and child is not None and hasattr(left, "Q"):
        return _class_pair_distance_states(left, right, child, sector, **{k: v for k, v in kwargs.items()
                if k not in ("left", "right", "child", "sector", "factor_a", "factor_b",
                             "factor_A", "factor_B", "a", "b", "glued", "result")})
    # Class-dictionary path
    # Positional: (classes_a, classes_b, tau, sigma, mask_a, mask_b, basis_a, basis_b)
    classes_a = kwargs.get("classes_a", kwargs.get("class_data_a", kwargs.get("data_a", None)))
    classes_b = kwargs.get("classes_b", kwargs.get("class_data_b", kwargs.get("data_b", None)))
    if classes_a is None and len(args) >= 1:
        classes_a = args[0]
    if classes_b is None and len(args) >= 2:
        classes_b = args[1]
    tau_seams = kwargs.get("tau_seams", kwargs.get("tau", kwargs.get("opposite_seams")))
    sigma_seams = kwargs.get("sigma_seams", kwargs.get("sigma", kwargs.get("same_seams")))
    if tau_seams is None and len(args) >= 3:
        tau_seams = args[2]
    if sigma_seams is None and len(args) >= 4:
        sigma_seams = args[3]
    mask_a = kwargs.get("mask_a", kwargs.get("mask_A"))
    mask_b = kwargs.get("mask_b", kwargs.get("mask_B"))
    if mask_a is None and len(args) >= 5:
        mask_a = args[4]
    if mask_b is None and len(args) >= 6:
        mask_b = args[5]
    basis_a = kwargs.get("basis_a", kwargs.get("basis_A"))
    basis_b = kwargs.get("basis_b", kwargs.get("basis_B"))
    if basis_a is None and len(args) >= 7:
        basis_a = args[6]
    if basis_b is None and len(args) >= 8:
        basis_b = args[7]
    sector = kwargs.get("sector", sector)
    seams = kwargs.get("seams")
    return _class_pair_distance_classes(classes_a, classes_b, tau_seams=tau_seams,
            sigma_seams=sigma_seams, mask_a=mask_a, mask_b=mask_b, basis_a=basis_a,
            basis_b=basis_b, sector=sector, seams=seams, **{k: v for k, v in kwargs.items()
            if k not in ("classes_a","class_data_a","data_a","classes_b","class_data_b","data_b",
                        "tau_seams","tau","opposite_seams","sigma_seams","sigma","same_seams",
                        "mask_a","mask_A","mask_b","mask_B","basis_a","basis_A","basis_b","basis_B",
                        "sector","seams","left","right","child","factor_a","factor_b","factor_A",
                        "factor_B","a","b","glued","result")})


# Aliases for various consumer-helper names.
# Additional aliases (broad).
for _name in ("consumer_class_pair_distance", "consumer_helper", "class_pair",
              "glue_distance_from_classes", "distance_from_class_pairs",
              "class_pair_distance_consumer", "helper_class_pair_distance"):
    globals()[_name] = class_pair_distance

class_pair_distance_from_classes = class_pair_distance
class_pair_distance_from_data = class_pair_distance
factor_class_pair_distance = class_pair_distance
glued_class_pair_distance = class_pair_distance
class_pair_distance_from_dictionaries = class_pair_distance
class_pairs_distance = class_pair_distance


# Additional consumer-helper aliases (broad naming coverage).
_extra_alias_names = [
    "extract_class_pair_distance", "compute_class_pair_distance",
    "evaluate_class_pair_distance", "calculate_class_pair_distance",
    "class_pair_distance_helper", "helper", "consumer", "distance",
    "glue_class_pair_distance", "glued_distance_from_classes",
    "class_pair_distance_from_states", "class_pair_distance_for_states",
    "E_GLUE_class_pair_distance", "e_glue_class_pair_distance",
]
for _name in _extra_alias_names:
    globals()[_name] = class_pair_distance

