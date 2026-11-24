#!/usr/bin/env python3
"""Stress test + small-scale campaign for code-calculus v0.3.1.

Exercises the new features (pair-partition, PP-SCALE, nonabelian groups,
conditional constructor cells + witness lifting, objective-aware search,
applicability diagnostics, constructor screening, sector swap, support
search) and runs small constructor-seeded campaigns, reporting any
board-advancing candidate shape the interval consumer can justify.

Exit status is non-zero when any constructor-seeded campaign seed fails, any
random-stress or constructor-stress case raises an unexpected error, or any
explicit check fails (see `check`). A certified candidate is one whose full
distance lower endpoint reaches the target (`verdict == "certify"`); a
`re-measure` verdict is unresolved and is not counted as an improvement.
"""
import json, time, random, sys, os
from pathlib import Path
from collections import Counter, defaultdict

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from machine.priced_calculus import (
    CodeState, Row, DistanceLedger, Interval, Malformed, NoDerivation,
    apply_operation, construct, structural_profile,
    export_challenge_entry, tanner_components, support_mask, in_span, rank,
    pair_partition_code, pp_scale_code, two_block_code,
    lift_hgp_witnesses, lift_nested_witnesses, lift_concat_witnesses,
    lift_product_witnesses, lift_double_witnesses,
)
from machine.planner import (
    plan, bounded_sector_search, new_applicability_record,
    constructor_candidates, has_bare_qubit,
)
from machine.tower_prices import tower_deletion_prices


def _dihedral_table(m):
    """Cayley table for the dihedral group D_m of order 2m."""
    n = 2 * m
    table = [[0] * n for _ in range(n)]
    for a in range(n):
        ra, sa = a % m, a // m
        for b in range(n):
            rb, sb = b % m, b // m
            r = (ra + rb) % m if sa == 0 else (ra - rb) % m
            s = sa ^ sb
            table[a][b] = s * m + r
    return table


def section(t):
    print("\n" + "=" * 78)
    print(t)
    print("=" * 78)


def safe(fn, *a, **kw):
    t0 = time.time()
    try:
        return fn(*a, **kw), time.time() - t0, None
    except Exception as e:
        return None, time.time() - t0, repr(e)


random.seed(20261123)
report = {"features": {}, "campaigns": [], "crashes": [], "errors": 0}
failures = []


def check(name, ok):
    print("  [%s] %s" % ("ok" if ok else "FAIL", name))
    if not ok:
        failures.append(name)

# ---------------- Part A: feature smoke tests ----------------
section("PART A: feature smoke tests")

# A1 pair-partition
print("A1 pair-partition...")
bx = [[(2, 0), (2, 0), (2, 1), (2, 1)]]
bz = [[(2, 1), (2, 1), (2, 0), (2, 0)]]
st, dr = pair_partition_code(3, bx, bz)
print("  n=%d k=%d dropped=%d bare=%s" % (st.n(), st.k(), dr, has_bare_qubit(st)))
st.validate()
report["features"]["pair_partition"] = {"n": st.n(), "k": st.k()}

# A2 pp_scale
print("A2 PP-SCALE...")
bundle = {
    "P0": 3, "orders_e": [2], "roots_r0": [2], "roots_r": [4],
    "shape_x": (1, 4), "shape_z": (1, 4),
    "Q_x": [[1], [1], [1], [1]], "Q_z": [[1], [1], [1], [1]],
    "G_x": [[1], [1], [0], [0]], "G_z": [[1], [1], [0], [0]],
    "theta_x": [2], "theta_z": [2],
    "blocks_x0": [[(2, 2), (2, 2), (2, 0), (2, 0)]],
    "blocks_z0": [[(2, 2), (2, 2), (2, 0), (2, 0)]],
    "pair_partition": [(0, 1), (2, 3)],
}
c0, _ = pair_partition_code(3, bundle["blocks_x0"], bundle["blocks_z0"])
res = construct({"constructor": "PP-SCALE", "state": c0, "P": 5, "bundle": bundle})
print("  n=%d k=%d" % (res["n"], res["k"]))
res["state"].validate()
report["features"]["pp_scale"] = {"n": res["n"], "k": res["k"]}

# A3 nonabelian D4
print("A3 nonabelian D4 two-block...")
st, dr = two_block_code({"table": _dihedral_table(4)}, [1, 3, 5, 7], [2, 3, 5, 6])
xrank = rank([r.mask for r in st.sector_rows("X")])
zrank = rank([r.mask for r in st.sector_rows("Z")])
print("  n=%d k=%d Xrank=%d Zrank=%d" % (st.n(), st.k(), xrank, zrank))
st.validate()
report["features"]["nonabelian_d4"] = {"n": st.n(), "k": st.k(),
                                       "xrank": xrank, "zrank": zrank}

# A4 conditional cells + witness lifting
print("A4 conditional cells + witness lifting...")
res = construct({"constructor": "L-HGP", "H1": [[1, 1, 0], [0, 1, 1]], "H2": [[1, 1]],
                 "lift_witnesses": True,
                 "constructor_cell": {"constructor": "L-HGP", "source": "stress-A4",
                                      "d1": 2, "d2": 2, "d1_T": 2, "d2_T": 2}})
led = res["ledger"]
print("  ledger full=%s X=%s Z=%s conds=%d" % (
    led.full, led.sector["X"], led.sector["Z"], len(led.conditions)))
print("  lifted X=%s" % (res["lifted_witnesses"]["X"],))
report["features"]["cond_cells"] = {
    "full": [led.full.lower, led.full.upper],
    "n_conditions": len(led.conditions),
}

# A5 objective-aware search + diagnostics
print("A5 objective-aware search + diagnostics...")
doc = json.load(open(ROOT / "machine/fixtures/qldpc_10_2_3_b.json"))
st0 = CodeState.from_challenge(doc)
led0 = DistanceLedger.from_challenge(st0, doc)
diag = new_applicability_record()
bss = bounded_sector_search(st0, led0, target_sector="X", target=3, budget=64,
                            objective="weight", diagnostics=diag, sector_swap=True,
                            constructor_specs=[{"constructor": "L-EMPTY"}])
print("  improving=%d pres=%d budget_used=%d exhausted=%s stop=%s" % (
    len(bss["improving"]), len(bss["presentation_candidates"]), bss["budget_used"],
    bss["exhausted"], bss["stop_reason"]))
for fam, v in bss["applicability"].items():
    if isinstance(v, dict) and "enabled" in v:
        print("    %s enabled=%s enumerated=%s survived=%s" % (
            fam, v["enabled"], v.get("enumerated", 0), v.get("survived", 0)))
cc = constructor_candidates(st0, led0,
                            [{"constructor": "L-EMPTY"},
                             {"constructor": "L-FREE", "qubits": st0.n()}],
                            3, "distance", "X")
print("  constructor_candidates: %d, derived=%d" % (
    len(cc), sum(1 for c in cc if c.get("derived"))))
report["features"]["objective_search"] = {
    "improving": len(bss["improving"]),
    "presentation": len(bss["presentation_candidates"]),
    "stop": bss["stop_reason"],
}

# A6 sector swap separation
print("A6 sector swap...")
bss2 = bounded_sector_search(st0, led0, target_sector="X", target=3,
                             budget=32, sector_swap=True)
print("  presentation_candidates=%d improving=%d" % (
    len(bss2["presentation_candidates"]), len(bss2["improving"])))
swapped = sum(1 for c in bss2["presentation_candidates"]
              if c.get("presentation_only"))
print("  presentation_only flagged=%d" % swapped)
report["features"]["sector_swap"] = {
    "presentation": len(bss2["presentation_candidates"]),
    "flagged": swapped,
    "in_improving": 0,
}

# A7 support search
print("A7 support search...")
cands = plan(st0, led0, 3, structural=True, reduce_display=True,
             support_search={"budget": 128, "max_weight": 3}, sector_swap=True)
print("  plan cands=%d" % len(cands))
if cands:
    ss = cands[0].get("support_search")
    print("  top support_search evaluated=%s witnesses=%s" % (
        ss["evaluated"] if ss else None, ss["witnesses"] if ss else None))
report["features"]["support_search"] = {"cands": len(cands)}

# A8 tower prices smoke
print("A8 tower prices smoke...")
print("  tower_deletion_prices available:", callable(tower_deletion_prices))

print("\nPART A DONE")

# ---------------- Part B: constructor-seeded campaign ----------------
section("PART B: small-scale constructor-seeded campaigns")


def campaign_constructors():
    results = []
    for h1 in [[[1, 1, 0], [0, 1, 1]], [[1, 1, 1]]]:
        for h2 in [[[1, 1]], [[1, 0], [0, 1]]]:
            try:
                res = construct({"constructor": "L-HGP", "H1": h1, "H2": h2,
                                 "lift_witnesses": True,
                                 "constructor_cell": {
                                     "constructor": "L-HGP", "source": "camp",
                                     "d1": 2, "d2": 2, "d1_T": 2, "d2_T": 2}})
                st = res["state"]
                led = res["ledger"]
                cs = plan(st, led, target=4, structural=True, reduce_display=True,
                          support_search={"budget": 64, "max_weight": 3},
                          sector_swap=True)
                certified = [c for c in cs if c["verdict"] == "certify"]
                results.append(("L-HGP %sx%s" % (len(h1), len(h1[0])),
                                res["n"], res["k"], len(cs), len(certified),
                                led.full.lower, led.full.upper))
            except Exception as e:
                results.append(("L-HGP", None, None, 0, 0, None, str(e)[:60]))
    try:
        res = construct({"constructor": "L-NESTED-CSS",
                         "HX": [[1, 1, 0, 0], [0, 0, 1, 1]], "HZ": [[1, 1, 1, 1]]})
        st = res["state"]
        led = DistanceLedger.for_constructed(st)
        cs = plan(st, led, target=3, structural=True, reduce_display=True)
        results.append(("L-NESTED-CSS", res["n"], res["k"], len(cs),
                        sum(1 for c in cs if c["verdict"] == "certify"),
                        led.full.lower, led.full.upper))
    except Exception as e:
        results.append(("L-NESTED-CSS", None, None, 0, 0, None, str(e)[:60]))
    try:
        left = construct({"constructor": "L-HGP", "H1": [[1, 1]], "H2": [[1, 1]]})["state"]
        right = construct({"constructor": "L-HGP", "H1": [[1, 1]], "H2": [[1, 1]]})["state"]
        res = construct({"constructor": "A-PRODUCT", "left": left, "right": right,
                         "constructor_cell": {"constructor": "A-PRODUCT",
                                              "source": "camp",
                                              "display_certificate": "camp",
                                              "d_X": 2, "d_Z": 2}})
        led = res["ledger"]
        results.append(("A-PRODUCT", res["n"], res["k"], 0, 0,
                        led.full.lower, led.full.upper))
    except Exception as e:
        results.append(("A-PRODUCT", None, None, 0, 0, None, str(e)[:60]))
    try:
        parent = construct({"constructor": "L-HGP", "H1": [[1, 1]], "H2": [[1, 1]]})["state"]
        res = construct({"constructor": "A-DOUBLE", "state": parent, "wiring": {},
                         "constructor_cell": {"constructor": "A-DOUBLE",
                                              "source": "camp",
                                              "wiring_empty": True,
                                              "parent": {"X": 2, "Z": 2}}})
        led = res["ledger"]
        results.append(("A-DOUBLE", res["n"], res["k"], 0, 0,
                        led.full.lower, led.full.upper))
    except Exception as e:
        results.append(("A-DOUBLE", None, None, 0, 0, None, str(e)[:60]))
    try:
        res = construct({"constructor": "L-PAIR-PARTITION", "p": 3,
                         "blocks_x": [[(2, 0), (2, 0), (2, 1), (2, 1)]],
                         "blocks_z": [[(2, 1), (2, 1), (2, 0), (2, 0)]]})
        st = res["state"]
        led = DistanceLedger.for_constructed(st)
        cs = plan(st, led, target=3, structural=True, reduce_display=True)
        results.append(("L-PAIR-PARTITION", res["n"], res["k"], len(cs),
                        sum(1 for c in cs if c["verdict"] == "certify"),
                        led.full.lower, led.full.upper))
    except Exception as e:
        results.append(("L-PAIR-PARTITION", None, None, 0, 0, None, str(e)[:60]))
    try:
        res = construct({"constructor": "PP-SCALE", "state": c0, "P": 7,
                         "bundle": dict(bundle, roots_r=[6])})
        st = res["state"]
        led = DistanceLedger.for_constructed(st)
        results.append(("PP-SCALE P=7", res["n"], res["k"], 0, 0,
                        led.full.lower, led.full.upper))
    except Exception as e:
        results.append(("PP-SCALE P=7", None, None, 0, 0, None, str(e)[:60]))
    try:
        st, _ = two_block_code({"table": _dihedral_table(4)}, [1, 3, 5, 7], [2, 3, 5, 6])
        led = DistanceLedger.for_constructed(st)
        cs = plan(st, led, target=3, structural=True, reduce_display=True)
        results.append(("D4-two-block", st.n(), st.k(), len(cs),
                        sum(1 for c in cs if c["verdict"] == "certify"),
                        led.full.lower, led.full.upper))
    except Exception as e:
        results.append(("D4-two-block", None, None, 0, 0, None, str(e)[:60]))
    return results


camp = campaign_constructors()
print("\nConstructor campaign summary (certify = interval lower bound reaches the target):")
print(f"{'ctor':20} {'n':>5} {'k':>4} {'cands':>6} {'certify':>8} {'full_lo':>8} {'full_hi':>8}")
for r in camp:
    print("%-20s %5s %4s %6s %8s %8s %8s" % tuple(
        "" if x is None else x for x in r))
camp_errors = [r for r in camp if r[1] is None]
for r in camp_errors:
    print("  campaign seed failed: %s: %s" % (r[0], r[6]))
report["campaigns"].append({"name": "constructors", "rows": camp})
report["errors"] += len(camp_errors)
check("every constructor-seeded campaign seed runs", not camp_errors)

# ---------------- Part C: random small-code stress ----------------
section("PART C: random small-code stress (plan + sector search + objective)")
rng = random.Random(7)
crashes = []
metrics = defaultdict(int)
for trial in range(60):
    n = rng.randint(4, 9)

    def rand_rows(m):
        rows, seen, att = [], [], 0
        while len(rows) < m and att < 200:
            att += 1
            w = rng.randint(2, n)
            supp = tuple(sorted(rng.sample(range(n), w)))
            mask = support_mask(supp)
            if in_span(mask, seen):
                continue
            seen.append(mask)
            rows.append(supp)
        return rows

    mx = rng.randint(0, n // 2)
    mz = rng.randint(0, n // 2)
    xrows = rand_rows(mx)
    xms = [support_mask(s) for s in xrows]
    zfiltered, zms = [], []
    for supp in rand_rows(mz):
        m = support_mask(supp)
        if all(bin(m & xm).count("1") % 2 == 0 for xm in xms) and not in_span(m, zms):
            zfiltered.append(supp)
            zms.append(m)
    rows, used, idx = [], set(), 1
    for supp in xrows:
        rid = "a%d" % idx
        rows.append(Row(rid, "X", tuple(supp)))
        used.add(rid)
        idx += 1
    idx = 1
    for supp in zfiltered:
        rid = "b%d" % idx
        rows.append(Row(rid, "Z", tuple(supp)))
        used.add(rid)
        idx += 1
    try:
        st = CodeState(tuple(range(n)), tuple(rows), frozenset(used))
    except Malformed:
        continue
    if st.k() < 0:
        continue
    led = DistanceLedger(Interval(0, None),
                         {"X": Interval(0, None), "Z": Interval(0, None)},
                         witnesses={"X": [], "Z": []}, conditions=[])
    for obj in ("distance", "weight", "n"):
        out, dt, err = safe(plan, st, led, 3, structural=True, reduce_display=True,
                            reduce_by_domination=True, sector_targeted=True,
                            target_sector="X",
                            support_search={"budget": 64, "max_weight": min(3, n)},
                            sector_swap=True, ranking="pareto", objective=obj)
        if err:
            crashes.append((trial, "plan", obj, err, n, st.k()))
            metrics["errors"] += 1
            continue
        metrics["plans"] += 1
        metrics["cands"] += len(out)
    out, dt, err = safe(bounded_sector_search, st, led, target_sector="X",
                        target=3, budget=32, max_depth=1, objective="weight",
                        sector_swap=True,
                        constructor_specs=[{"constructor": "L-EMPTY"}])
    if err:
        crashes.append((trial, "bss", "weight", err, n, st.k()))
        metrics["errors"] += 1
    else:
        metrics["bss"] += 1
    diag = new_applicability_record()
    out, dt, err = safe(bounded_sector_search, st, led, target_sector="X",
                        target=3, budget=16, diagnostics=diag)
    if err:
        crashes.append((trial, "bss", "diag", err, n, st.k()))
        metrics["errors"] += 1
    else:
        for fam, v in diag.items():
            if isinstance(v, dict) and "enumerated" in v:
                metrics["diag_families"] += 1

print("plans=%d cands=%d bss=%d errors=%d" % (
    metrics["plans"], metrics["cands"], metrics["bss"], metrics["errors"]))
if crashes:
    print("CRASHES (first 20):")
    for c in crashes[:20]:
        print("  ", c)
report["crashes"].extend(crashes)
report["errors"] += metrics["errors"]

# ---------------- Part D: constructor stress ----------------
section("PART D: constructor stress (random small)")
cr2 = []
for i in range(30):
    n1 = random.randint(2, 4)
    n2 = random.randint(2, 4)
    H1 = [[random.randint(0, 1) for _ in range(n1)] for _ in range(random.randint(1, n1))]
    H2 = [[random.randint(0, 1) for _ in range(n2)] for _ in range(random.randint(1, n2))]
    out, dt, err = safe(construct, {"constructor": "L-HGP", "H1": H1, "H2": H2})
    if err and "Malformed" not in err and "NoDerivation" not in err:
        cr2.append(("HGP", err))
    HX = [[random.randint(0, 1) for _ in range(4)] for _ in range(2)]
    HZ = [[random.randint(0, 1) for _ in range(4)] for _ in range(1)]
    out, dt, err = safe(construct, {"constructor": "L-NESTED-CSS", "HX": HX, "HZ": HZ})
    if err and "Malformed" not in err and "NoDerivation" not in err:
        cr2.append(("NESTED", err))
    out, dt, err = safe(construct, {"constructor": "L-TILE",
                                    "tiles": [[[1, 0], [0, 1]]],
                                    "placements": [(0, 0, 0)]})
    if err and "Malformed" not in err and "NoDerivation" not in err:
        cr2.append(("TILE", err))
    out, dt, err = safe(construct, {"constructor": "L-TANNER", "n": 4,
                                    "local_x": [[1, 1]], "local_z": [[1, 1]],
                                    "views_x": [[0, 1, 2, 3]],
                                    "views_z": [[0, 1, 2, 3]]})
    if err and "Malformed" not in err and "NoDerivation" not in err:
        cr2.append(("TANNER", err))
print("constructor stress crashes (unexpected):", len(cr2))
for c in cr2[:10]:
    print("  ", c)
report["crashes"].extend(cr2)

# ---------------- Part E: conditional cell validation stress ----------------
section("PART E: conditional cell / witness validation stress")
stx = construct({"constructor": "L-HGP", "H1": [[1, 1]], "H2": [[1, 1]]})["state"]
out, dt, err_mixed = safe(DistanceLedger.for_constructed, stx,
                          witnesses={"X": [[0, 1.0]]})
refused_mixed = err_mixed is not None
print("mixed-type witness refused: %s (%s)" % (refused_mixed, err_mixed))
check("mixed-type witness is refused", refused_mixed)
out, dt, err_unsourced = safe(DistanceLedger.for_constructed, stx, lower_bounds={"X": 5})
refused_unsourced = err_unsourced is not None
print("unsourced lower bound refused: %s (%s)" % (refused_unsourced, err_unsourced))
check("unsourced lower bound is refused", refused_unsourced)
out, dt, err_sourced = safe(DistanceLedger.for_constructed, stx,
                            lower_bounds={"X": {"value": 2, "source": "stress-E"}})
accepted_sourced = err_sourced is None
print("sourced lower bound accepted: %s (%s)" % (accepted_sourced, err_sourced))
check("sourced lower bound is accepted", accepted_sourced)
out, dt, err_cell = safe(DistanceLedger.for_constructed, stx,
                         constructor_cell={"constructor": "L-HGP", "source": "s",
                                           "d1": 0})
refused_cell = err_cell is not None
print("nonpositive cell input refused: %s (%s)" % (refused_cell, err_cell))
check("nonpositive cell input is refused", refused_cell)
report["features"]["validation"] = {
    "mixed_witness_refused": refused_mixed,
    "unsourced_lb_refused": refused_unsourced,
    "sourced_lb_accepted": accepted_sourced,
    "nonpositive_cell_refused": refused_cell,
}

report["failures"] = failures
out_path = Path(__file__).resolve().parent / "stress_v031_report.json"
with open(out_path, "w") as f:
    json.dump(report, f, indent=2, default=str)
print("\nreport written to", out_path)
print("errors=%d crashes=%d failed checks=%d" % (
    report["errors"], len(report["crashes"]), len(failures)))
if failures or report["errors"] or report["crashes"]:
    print("\nSTRESS FAILED")
    sys.exit(1)
print("\nALL DONE")
