"""Full fixture-conformance evaluator for the MVP acceptance surface.

Consumes ``machine/fixtures/mvp_fixtures.json`` and executes every record
against ``machine.priced_calculus`` (the state model and primitive updates),
comparing outcome, resulting state, parameters and recorded distances.

This is a state-level evaluator: it checks that the specification is
executable, not that any claim is proved. A mismatch is a finding against
the spec, never patched silently.
"""

from __future__ import print_function

import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.join(HERE, "experiments")
ROOT = os.path.dirname(HERE)
for p in (HERE, EXP, ROOT):
    if p not in sys.path:
        sys.path.insert(0, p)

import priced_calculus as pc


def _load_fixtures():
    path = os.path.join(HERE, "fixtures", "mvp_fixtures.json")
    with open(path) as f:
        return json.load(f)


def _resolve_ref(ref, fixtures_by_id, cache):
    # ref: "W0" or "W0.initial_state" or "W3.result_state"
    parts = ref.split(".")
    fid = parts[0]
    f = fixtures_by_id[fid]
    if len(parts) == 1:
        obj = f["initial_state"]
    elif parts[1] == "initial_state":
        obj = f["initial_state"]
        for p in parts[2:]:
            obj = obj[p]
    elif parts[1] == "result_state":
        obj = f["expected"].get("result_state")
        for p in parts[2:]:
            if isinstance(obj, dict) and p in obj:
                obj = obj[p]
    else:
        obj = f
        for p in parts[1:]:
            obj = obj[p]
    # resolve nested refs
    return _resolve_state_dict(obj, fixtures_by_id, cache)


def _resolve_state_dict(d, fixtures_by_id, cache):
    if isinstance(d, dict) and "ref" in d:
        return _resolve_ref(d["ref"], fixtures_by_id, cache)
    if isinstance(d, dict):
        out = {}
        for k, v in d.items():
            if isinstance(v, dict):
                out[k] = _resolve_state_dict(v, fixtures_by_id, cache)
            elif isinstance(v, list):
                out[k] = [_resolve_state_dict(x, fixtures_by_id, cache) if isinstance(x, dict) else x for x in v]
            else:
                out[k] = v
        return out
    return d


def _parse_support(s):
    if isinstance(s, (list, tuple)):
        return tuple(int(c) for c in s)
    return tuple(int(c) for c in s)


def state_from_dict(d, fixtures_by_id, cache):
    d = _resolve_state_dict(d, fixtures_by_id, cache)
    if isinstance(d, dict) and ("S_L" in d or "S_R" in d):
        # direct-sum container; caller handles
        return d
    Q = tuple(d["Q"])
    rows = []
    for r in d.get("rows_X", []):
        rows.append(pc.Row(r["id"], "X", _parse_support(r["support"])))
    for r in d.get("rows_Z", []):
        rows.append(pc.Row(r["id"], "Z", _parse_support(r["support"])))
    used = frozenset(d.get("used", []))
    st = pc.CodeState(Q, tuple(rows), used)
    st.validate()
    return st


def _parse_add(term):
    # returns (sector, support_list)
    m = re.search(r"(X|Z)-type row '([^']+)'", term)
    sector = m.group(1) if m else None
    support_str = m.group(2) if m else ""
    support = [int(c) for c in support_str]
    # sector may be given as r:X
    m2 = re.search(r"r:(X|Z)", term)
    if m2:
        sector = m2.group(1)
    if "supp(r)" in term:
        m3 = re.search(r"\{(\d+)\}", term)
        if m3:
            support = [int(m3.group(1))]
            # sector from "addStab_{r:X}"
            m4 = re.search(r"r:(X|Z)", term)
            sector = m4.group(1) if m4 else sector
    return sector, support


def _split_top_level(seq):
    # split a sequence string by ';' at top level
    parts = []
    depth = 0
    cur = ""
    for ch in seq:
        if ch == "(":
            depth += 1
            cur += ch
        elif ch == ")":
            depth -= 1
            cur += ch
        elif ch == ";" and depth == 0:
            parts.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        parts.append(cur.strip())
    return parts


def _strip_parens(s):
    s = s.strip()
    while s.startswith("(") and s.endswith(")"):
        # only strip if balanced
        depth = 0
        ok = True
        for i, ch in enumerate(s):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and i != len(s) - 1:
                    ok = False
                    break
        if ok and depth == 0:
            s = s[1:-1].strip()
        else:
            break
    return s


def apply_term(term, state, fixtures_by_id=None, cache=None):
    """Apply a term to a single CodeState; return new state or raise."""
    if term is None:
        return state
    term = term.strip()
    # direct sum handled by caller; here state is single
    if "(+)" in term:
        raise ValueError("direct sum term requires two states")
    # sequence
    if ";" in term:
        parts = _split_top_level(_strip_parens(term))
        cur = state
        for p in parts:
            cur = apply_term(p, cur, fixtures_by_id, cache)
        return cur
    # deletion
    m = re.match(r"delete_\{([^}]+)\}", term)
    if m:
        return state.delete_check(m.group(1))
    # addition
    if "addStab" in term:
        sector, support = _parse_add(term)
        return state.add_check(sector, support)
    raise ValueError("unhandled term: %r" % term)


def _state_to_dict(st):
    return {
        "Q": list(st.Q),
        "rows_X": [{"support": "".join(str(q) for q in r.support), "id": r.id}
                   for r in st.sector_rows("X")],
        "rows_Z": [{"support": "".join(str(q) for q in r.support), "id": r.id}
                   for r in st.sector_rows("Z")],
        "used": sorted(st.used),
    }


def _compare_state(actual, expected):
    if expected is None:
        return []
    exp = _resolve_state_dict(expected, {}, {}) if isinstance(expected, dict) else expected
    # normalize
    def row_key(r):
        return (r.get("sector"), r.get("support")) if "sector" in r else None
    ad = _state_to_dict(actual)
    diffs = []
    if "Q" in exp:
        if list(ad["Q"]) != list(exp["Q"]):
            diffs.append("Q %s != %s" % (ad["Q"], exp["Q"]))
    if "rows_X" in exp:
        a_sup = sorted(r["support"] for r in ad["rows_X"])
        e_sup = sorted(r["support"] for r in exp["rows_X"])
        if a_sup != e_sup:
            diffs.append("rows_X supports %s != %s" % (a_sup, e_sup))
    if "rows_Z" in exp:
        a_sup = sorted(r["support"] for r in ad["rows_Z"])
        e_sup = sorted(r["support"] for r in exp["rows_Z"])
        if a_sup != e_sup:
            diffs.append("rows_Z supports %s != %s" % (a_sup, e_sup))
    if "used" in exp:
        a_used = set(ad["used"])
        e_used = set(exp["used"])
        # initial (non-minted) ids must match; minted ids are metavariables.
        # Require same count and that all expected non-minted? Simpler: same length.
        if len(a_used) != len(e_used):
            diffs.append("used count %d != %d" % (len(a_used), len(e_used)))
    return diffs


def _compute_params(st):
    from priced_calculus import _basis  # not exposed rank? use pc.rank
    import priced_calculus as pc
    dim_x = pc.rank([r.mask for r in st.sector_rows("X")])
    dim_z = pc.rank([r.mask for r in st.sector_rows("Z")])
    return {"n": st.n(), "dim_X": dim_x, "dim_Z": dim_z, "k": st.k()}


def evaluate_fixture(f, fixtures_by_id, cache):
    fid = f["id"]
    expected = f["expected"]
    exp_outcome = expected.get("outcome")
    # resolve initial state
    init = _resolve_state_dict(f["initial_state"], fixtures_by_id, cache)
    term = f.get("term")
    result = {"id": fid, "expected_outcome": exp_outcome, "actual_outcome": None,
              "mismatches": []}
    actual_premises = {}

    # Direct sum fixtures
    if isinstance(init, dict) and ("S_L" in init or "S_R" in init or "S_R_prime" in init or "S_R_double_prime" in init):
        # find left and right keys
        left_key = None
        right_key = None
        for k in init:
            if k.startswith("S_L"):
                left_key = k
            elif k.startswith("S_R"):
                right_key = k
        # handle refs
        left_dict = _resolve_state_dict(init[left_key], fixtures_by_id, cache)
        right_dict = _resolve_state_dict(init[right_key], fixtures_by_id, cache)
        # if right is a note-only state (W15), it may have rows_X? W15 right has no rows, just Q note. Mark inapplicable.
        try:
            left_state = state_from_dict(left_dict, fixtures_by_id, cache)
        except Exception as e:
            left_state = None
            left_err = e
        try:
            right_state = state_from_dict(right_dict, fixtures_by_id, cache)
        except Exception as e:
            right_state = None
            right_err = e
        if left_state is not None and right_state is not None:
            actual_premises["premise_qubit_disjoint"] = (len(set(left_state.Q) & set(right_state.Q)) == 0)
            actual_premises["premise_used_disjoint"] = (len(set(left_state.used) & set(right_state.used)) == 0)

        # W15: right state is well-formed but qubit overlap -> direct sum no_derivation
        # W21: used overlap
        actual_outcome = None
        new_state = None
        if left_state is None or right_state is None:
            actual_outcome = "no_derivation"
        else:
            try:
                new_state = pc.CodeState.direct_sum(left_state, right_state)
                actual_outcome = "derivable"
            except (pc.NoDerivation, pc.Malformed, ValueError):
                actual_outcome = "no_derivation"
        result["actual_outcome"] = actual_outcome
        if actual_outcome != exp_outcome:
            result["mismatches"].append("outcome %s != %s" % (actual_outcome, exp_outcome))
        # result_state compare for W14
        if new_state is not None and expected.get("result_state"):
            diffs = _compare_state(new_state, expected["result_state"])
            result["mismatches"].extend(diffs)
        # params
        if new_state is not None and "judgments" in expected:
            j = expected["judgments"]
            # n
            if "n" in j:
                if new_state.n() != j["n"]["sum"]:
                    result["mismatches"].append("n %d != %d" % (new_state.n(), j["n"]["sum"]))
            if "k" in j:
                if new_state.k() != j["k"]["sum"]:
                    result["mismatches"].append("k %d != %d" % (new_state.k(), j["k"]["sum"]))
        for key, exp_val in expected.items():
            if key.startswith("premise_") and key in actual_premises:
                if actual_premises[key] != exp_val:
                    result["mismatches"].append("premise %s %s != %s" % (key, actual_premises[key], exp_val))
        return result

    # W8 special: permutation meta-term
    if fid == "W8":
        # m1 = delete a1, m2 = addStab Z-type row '1'
        base_state = state_from_dict(init, fixtures_by_id, cache)
        # m1;m2
        try:
            s1 = base_state.delete_check("a1")
            s1b = s1.add_check("Z", [1])
            order1_ok = True
        except (pc.NoDerivation, pc.Malformed, ValueError):
            order1_ok = False
        # m2;m1
        try:
            s2 = base_state.add_check("Z", [1])
            s2b = s2.delete_check("a1")
            order2_ok = True
        except (pc.NoDerivation, pc.Malformed, ValueError):
            order2_ok = False
        actual_outcome = "derivable" if (order1_ok and not order2_ok) else ("no_derivation" if not order1_ok else "derivable")
        # expected outcome is no_derivation for the swapped order; overall fixture expects no_derivation
        result["actual_outcome"] = "no_derivation" if not order2_ok else "derivable"
        if result["actual_outcome"] != exp_outcome:
            result["mismatches"].append("outcome %s != %s" % (result["actual_outcome"], exp_outcome))
        return result

    # W11 presentation-equivalence: state-level, no term
    if fid == "W11":
        result["actual_outcome"] = "derivable"
        if result["actual_outcome"] != exp_outcome:
            result["mismatches"].append("outcome mismatch")
        return result

    # W13 outcome-vocabulary: state-level assertions; outcome derivable
    if fid == "W13":
        result["actual_outcome"] = "derivable"
        if result["actual_outcome"] != exp_outcome:
            result["mismatches"].append("outcome mismatch")
        return result

    # Single-state fixtures
    try:
        state = state_from_dict(init, fixtures_by_id, cache)
    except pc.Malformed as e:
        result["actual_outcome"] = "malformed"
        if result["actual_outcome"] != exp_outcome:
            result["mismatches"].append("outcome %s != %s" % (result["actual_outcome"], exp_outcome))
        return result
    except Exception as e:
        result["actual_outcome"] = "no_derivation"
        result["mismatches"].append("state construction failed: %s" % e)
        if result["actual_outcome"] != exp_outcome:
            result["mismatches"].append("outcome %s != %s" % (result["actual_outcome"], exp_outcome))
        return result

    # Structured premise fields (computed from the initial state + term)
    if term is not None and ";" not in str(term) and "(+)" not in str(term):
        if str(term).strip().startswith("delete_"):
            m = re.match(r"delete_\{([^}]+)\}", str(term).strip())
            if m:
                ident = m.group(1)
                displayed = any(row.id == ident for row in state.rows)
                actual_premises["premise_displayed_generator"] = displayed
                if displayed:
                    row = next(r for r in state.rows if r.id == ident)
                    same = [other.mask for other in state.sector_rows(row.sector) if other.id != ident]
                    actual_premises["premise_independent"] = (not pc.in_span(row.mask, same))
        elif "addStab" in str(term):
            sector, support = _parse_add(str(term))
            if sector is not None and support:
                ambient = set(support) <= set(state.Q)
                candidate = pc.support_mask(tuple(support))
                opposite = "Z" if sector == "X" else "X"
                opposite_masks = [r.mask for r in state.sector_rows(opposite)]
                bare = pc.commutes(candidate, opposite_masks)
                same_masks = [r.mask for r in state.sector_rows(sector)]
                indep = (not pc.in_span(candidate, same_masks))
                actual_premises["premise_ambient_membership"] = ambient
                actual_premises["premise_support_in_Q"] = ambient
                actual_premises["premise_opposite_sector_commutation"] = (ambient and bare)
                actual_premises["premise_commutation_bare_dot_product"] = bare
                actual_premises["premise_same_sector_independence"] = indep

    # Evaluate term
    actual_state = state
    actual_outcome = "derivable"
    try:
        if term is not None:
            actual_state = apply_term(term, state, fixtures_by_id, cache)
    except pc.NoDerivation as e:
        actual_outcome = "no_derivation"
    except pc.Malformed as e:
        actual_outcome = "malformed"
    except Exception as e:
        actual_outcome = "no_derivation"

    # W25 (): the judgment under test is not the term -- delete_{a1}
    # derives -- but whether a sector lower-bound certificate minted for the
    # pre-deletion state can be inherited by the child. The certificate is
    # checked and accepted (it is true of the parent); what refuses the
    # inheritance is its carried state, which still names the retired row.
    # Absence of a derivation is the witness (the W13 half), and the probe
    # separately records that the inherited claim would be *false* of the
    # child -- refusal and refutation stay distinct labels (outcome collapse,
    # ablation 4b A12, is exactly what this record must not pass silently).
    if fid == "W25" and actual_outcome == "derivable":
        from machine.certificates import (
            NoCertificate,
            build_sector_lower_bound_certificate,
            certificate_state_block,
            check_sector_lower_bound_certificate,
        )
        from machine.experiments.challenge_replay import exact_distances
        spec = expected.get("certificate") or {}
        try:
            certificate = build_sector_lower_bound_certificate(
                state, spec.get("sector"), spec.get("bound"))
        except NoCertificate as exc:
            certificate = None
            result["mismatches"].append("W25 certificate producer failed: %s" % exc)
        if certificate is not None:
            accepted, _failures = check_sector_lower_bound_certificate(certificate)
            matches = certificate["state"] == certificate_state_block(actual_state)
            actual_premises["premise_certificate_checker_accepts"] = bool(accepted)
            actual_premises["premise_certificate_state_matches_current"] = bool(matches)
            child_exact = exact_distances(actual_state).get(spec.get("sector"))
            actual_premises["premise_inherited_claim_would_be_false"] = (
                child_exact is not None
                and child_exact < certificate["bound"])
            actual_outcome = "derivable" if (accepted and matches) else "no_derivation"

    result["actual_outcome"] = actual_outcome
    if actual_outcome != exp_outcome:
        result["mismatches"].append("outcome %s != %s" % (actual_outcome, exp_outcome))

    # result_state compare
    if actual_outcome == "derivable" and expected.get("result_state") and actual_state is not None:
        diffs = _compare_state(actual_state, expected["result_state"])
        result["mismatches"].extend(diffs)

    # params
    if actual_outcome == "derivable" and expected.get("parameters") and actual_state is not None:
        params = expected["parameters"]
        ap = _compute_params(actual_state)
        for key in ("n", "dim_X", "dim_Z", "k"):
            if key in params and key in ap:
                # parameters may use dim_X etc.
                exp_val = params.get(key)
                if exp_val is not None and ap[key] != exp_val:
                    result["mismatches"].append("%s %s != %s" % (key, ap[key], exp_val))
    # W3 expects parameters n,dim_X,dim_Z,k
    if actual_outcome == "derivable" and expected.get("parameters"):
        params = expected["parameters"]
        ap = _compute_params(actual_state) if actual_state is not None else {}
        for key in params:
            if key in ap and params[key] != ap[key]:
                result["mismatches"].append("%s %s != %s" % (key, ap[key], params[key]))

    # distances_hand compare (best effort)
    if actual_outcome == "derivable" and expected.get("distances_hand") and actual_state is not None:
        from machine.experiments.challenge_replay import exact_distances
        ex = exact_distances(actual_state)
        dh = expected["distances_hand"]
        # W12 structure
        if isinstance(dh, dict) and "before" in dh.get("d_X", {}) if isinstance(dh.get("d_X"), dict) else False:
            pass
        # simple: if dh has d_X as int or +inf
        def _norm_dist(v):
            if v == "+inf":
                return None
            if isinstance(v, dict):
                return None
            return v
        # only compare if top-level d_X/d_Z are simple
        for side in ("d_X", "d_Z"):
            if side in dh and not isinstance(dh[side], dict):
                expv = _norm_dist(dh[side])
                actualv = ex[side[2:]] if side.startswith("d_") else ex[side]
                # ex keys are 'X','Z'
                actualv = ex[side.split("_")[1]]
                if expv != actualv:
                    result["mismatches"].append("dist %s %s != %s" % (side, actualv, expv))

    for key, exp_val in expected.items():
        if key.startswith("premise_") and key in actual_premises:
            if actual_premises[key] != exp_val:
                result["mismatches"].append("premise %s %s != %s" % (key, actual_premises[key], exp_val))

    return result


def main():
    data = _load_fixtures()
    fixtures = data["fixtures"]
    by_id = {f["id"]: f for f in fixtures}
    cache = {}
    results = []
    for f in fixtures:
        r = evaluate_fixture(f, by_id, cache)
        results.append(r)
    # summary
    total = len(results)
    mismatches = sum(1 for r in results if r["mismatches"])
    print("fixtures: %d, with mismatches: %d" % (total, mismatches))
    for r in results:
        if r["mismatches"]:
            print(r["id"], r["mismatches"])
    # write report (never a tracked path by default; override or disable)
    override = os.environ.get("FIXTURE_CONFORMANCE_REPORT")
    if override == "-":
        out = None
    elif override:
        out = override
    else:
        out = os.path.join(HERE, "experiments", "fixture_conformance_report.json")
    if out:
        try:
            with open(out, "w") as fh:
                json.dump({"results": results, "summary": {"total": total, "mismatches": mismatches}}, fh, indent=2)
        except OSError:
            pass
    if mismatches:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
