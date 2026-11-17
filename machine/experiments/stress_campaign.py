#!/usr/bin/env python3
"""Stress-test campaign for the priced CSS calculus consumer.

Exercises the recently augmented functionalities over a battery of small
codes and reports crashes, timings, and summary metrics.
"""
import json, time, random
from pathlib import Path
from collections import Counter

ROOT = Path(__file__).resolve().parents[2]
import sys
sys.path.insert(0, str(ROOT))

from machine.priced_calculus import (
    CodeState, Row, DistanceLedger, NoDerivation, Malformed,
    apply_operation,
    strict_improvement_feasible,
    tanner_components, support_mask, in_span,
    export_challenge_entry, Interval,
)
from machine.planner import (plan, plan_chain, bounded_sector_search,
                            bounded_support_search, tighten_ledger_with_search,
                            has_bare_qubit, domination_prune,
                            reduce_display, dedup_up_to_permutation)
from machine.symplectic_calculus import (
    SymplecticState, SymplecticLedger,
)


def make_ledger_from_challenge(doc):
    st = CodeState.from_challenge(doc)
    ld = DistanceLedger.from_challenge(st, doc)
    return st, ld


def section(title):
    print("\n" + "=" * 70)
    print(title)
    print("=" * 70)


def safe(fn, *a, **kw):
    t0 = time.time()
    try:
        out = fn(*a, **kw)
        return out, time.time() - t0, None
    except Exception as e:
        return None, time.time() - t0, repr(e)


def campaign_1():
    section("Campaign 1: [[10,2,3]] qLDPC")
    doc = json.load(open(ROOT / "machine/fixtures/qldpc_10_2_3_b.json"))
    state, ledger = make_ledger_from_challenge(doc)
    print("parent: n=%d k=%d full=%s X=%s Z=%s" % (
        state.n(), state.k(), ledger.full, ledger.sector["X"], ledger.sector["Z"]))
    target = 3
    t0 = time.time()
    cands = plan(
        state, ledger, target,
        structural=True, reduce_display=True, reduce_by_domination=True,
        sector_targeted=True, target_sector="X",
        support_search={"budget": 512, "max_weight": 3},
        sector_swap=True, ranking="pareto",
    )
    print("plan: %d candidates in %.2fs" % (len(cands), time.time() - t0))
    print("verdicts:", Counter(c["verdict"] for c in cands))
    print("ops:", Counter(c["operation"]["op"] for c in cands))
    if cands:
        c0 = cands[0]
        print("top: op=%s verdict=%s n=%d k=%d w=%d conn=%d" % (
            c0["operation"]["op"], c0["verdict"], c0["n"], c0["k"], c0["w"], c0["connectivity"]))
        ss = c0.get("support_search")
        if ss:
            print("  support_search evaluated=%d exhausted=%s witnesses=%s" % (
                ss["evaluated"], ss["exhausted"], ss["witnesses"]))
        sw = c0.get("sector_swap")
        print("  sector_swap applied=%s" % (bool(sw and sw.get("applied"))))
    raw = plan(state, ledger, target, structural=True, reduce_display=True,
               reduce_by_domination=False, sector_targeted=False, support_search=None)
    pruned = domination_prune(raw)
    print("domination: %d raw -> %d pruned" % (len(raw), len(pruned)))
    print("parent has bare qubit? %s" % has_bare_qubit(state))
    chains = plan_chain(state, ledger, target, depth=2, structural=True,
                        reduce_display=True, support_search={"budget": 256, "max_weight": 3})
    print("plan_chain depth=2: %d sequences" % len(chains))
    bss = bounded_sector_search(state, ledger, target_sector="X", target=target,
                                budget=64, max_depth=1, sector_swap=True)
    print("bounded_sector_search: %d improving, budget_used=%d exhausted=%s" % (
        len(bss["improving"]), bss["budget_used"], bss["exhausted"]))
    print("heuristic_outcome statement:", bss["heuristic_outcome"]["statement"])
    return cands


def campaign_2():
    section("Campaign 2: stress over random small CSS codes")
    rng = random.Random(42)
    crashes = []
    metrics = {"plans": 0, "cands_total": 0, "errors": 0, "max_cands": 0}
    for trial in range(40):
        n = rng.randint(3, 8)
        def rand_rows(m):
            rows = []; seen = []; attempts = 0
            while len(rows) < m and attempts < 200:
                attempts += 1
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
        x_masks = [support_mask(s) for s in xrows]
        z_filtered = []; z_masks = []
        for supp in rand_rows(mz):
            m = support_mask(supp)
            if all(bin(m & xm).count("1") % 2 == 0 for xm in x_masks) and not in_span(m, z_masks):
                z_filtered.append(supp); z_masks.append(m)
        rows = []; used = set(); idx = 1
        for supp in xrows:
            rid = "a%d" % idx
            rows.append(Row(rid, "X", tuple(supp))); used.add(rid); idx += 1
        idx = 1
        for supp in z_filtered:
            rid = "b%d" % idx
            rows.append(Row(rid, "Z", tuple(supp))); used.add(rid); idx += 1
        Q = tuple(range(n))
        try:
            st = CodeState(Q, tuple(rows), frozenset(used))
        except Malformed:
            continue
        k = st.k()
        if k < 0:
            continue
        ld = DistanceLedger(Interval(0, None), {"X": Interval(0, None), "Z": Interval(0, None)},
                            witnesses={"X": [], "Z": []}, conditions=[])
        target = 2
        out, dt, err = safe(plan, st, ld, target,
                            structural=True, reduce_display=True, reduce_by_domination=True,
                            sector_targeted=True, target_sector="X",
                            support_search={"budget": 256, "max_weight": min(3, n)},
                            sector_swap=True, ranking="pareto")
        if err:
            crashes.append((trial, "plan", err, n, k)); metrics["errors"] += 1; continue
        metrics["plans"] += 1
        metrics["cands_total"] += len(out)
        metrics["max_cands"] = max(metrics["max_cands"], len(out))
        out2, dt2, err2 = safe(bounded_support_search, st, sectors=("X", "Z"),
                                budget=128, max_weight=min(3, n))
        if err2:
            crashes.append((trial, "bounded_support_search", err2, n, k)); metrics["errors"] += 1
        from machine.priced_calculus import admissible_added_checks
        admissible = list(admissible_added_checks(st, max_weight=2, sectors=("X",)))
        if admissible:
            supp, sec = admissible[0]
            out3, dt3, err3 = safe(strict_improvement_feasible, st,
                                   added_support=supp, added_sector=sec,
                                   base_distance=2, ledger=ld,
                                   allow_enumeration=True, enumeration_ceiling=8)
            if err3 and "NoDerivation" not in err3 and "Malformed" not in err3:
                crashes.append((trial, "strict_improvement", err3, n, k)); metrics["errors"] += 1
        out4, dt4, err4 = safe(bounded_sector_search, st, ld, target_sector="X",
                                target=target, budget=32, max_depth=1, sector_swap=True)
        if err4:
            crashes.append((trial, "bounded_sector_search", err4, n, k)); metrics["errors"] += 1
    print("trials: 40; plans ok: %d; total cands: %d; max cands: %d; errors: %d" % (
        metrics["plans"], metrics["cands_total"], metrics["max_cands"], metrics["errors"]))
    if crashes:
        print("CRASHES:")
        for c in crashes[:20]:
            print("  ", c)
    return crashes


def campaign_3():
    section("Campaign 3: symplectic double/halve round-trip")
    Q = (0, 1, 2, 3)
    rows = (Row("a1", "X", (0, 1)), Row("a2", "X", (2, 3)),
            Row("b1", "Z", (0, 1)), Row("b2", "Z", (2, 3)))
    used = frozenset({"a1", "a2", "b1", "b2"})
    css = CodeState(Q, rows, used)
    print("css: n=%d k=%d" % (css.n(), css.k()))
    sym_state = SymplecticState.from_css(css)
    sym = sym_state.double()
    print("doubled: n=%d k=%d (expect 8,%d)" % (sym.n(), sym.k(), 2 * css.k()))
    ld = SymplecticLedger(Interval(0, None))
    print("ledger full=%s" % ld.full)
    pairs = [(q, q + css.n()) for q in range(css.n())]
    try:
        halved = SymplecticState.halve(sym, pairs)
        print("halved: n=%d k=%d (expect %d,%d)" % (halved.n(), halved.k(), css.n(), css.k()))
        print("round-trip OK:", halved.n() == css.n() and halved.k() == css.k())
    except Exception as e:
        print("halve failed:", repr(e))
    try:
        sym.validate(); print("symplectic validate: OK")
    except Exception as e:
        print("validate failed:", repr(e))


def campaign_4():
    section("Campaign 4: edge cases")
    st = CodeState((0,), (), frozenset())
    print("n=1 empty state k=%d" % st.k())
    try:
        r = bounded_support_search(st, budget=10, max_weight=1)
        print("n=1 search: evaluated=%d witnesses=%s" % (r["evaluated"], r["witnesses"]))
    except Exception as e:
        print("n=1 search error:", repr(e))
    try:
        strict_improvement_feasible(st, added_support=(0,), added_sector="X", base_distance=5, ledger=None)
        print("strict_improvement base>n: NO ERROR (unexpected)")
    except Exception as e:
        print("strict_improvement base>n raised:", type(e).__name__)
    print("domination_prune([]):", domination_prune([]))
    print("dedup([]):", dedup_up_to_permutation([]))
    doc = json.load(open(ROOT / "machine/fixtures/qldpc_10_2_3_b.json"))
    st2, _ = make_ledger_from_challenge(doc)
    r2 = reduce_display(st2)
    print("reduce_display rows: %d -> %d" % (len(st2.rows), len(r2.rows)))
    print("has_bare_qubit qldpc:", has_bare_qubit(st2))
    ld0 = DistanceLedger(Interval(0, None), {"X": Interval(0, None), "Z": Interval(0, None)},
                         witnesses={"X": [], "Z": []}, conditions=[])
    cands = plan(st2, ld0, target=100, structural=True, reduce_display=True)
    print("plan target=100 on qldpc: %d cands (k=%d)" % (len(cands), st2.k()))


def main():
    campaign_1()
    crashes = campaign_2()
    campaign_3()
    campaign_4()
    print("\nDONE")

if __name__ == "__main__":
    main()
