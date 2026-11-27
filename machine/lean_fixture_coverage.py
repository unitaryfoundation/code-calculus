"""Lean <-> Python fixture coverage report (spike for).

This is a bounded, reversible conformance *link*, not a refinement theorem.
It does not execute Lean. It compares the set of pinned fixture states that
Lean transcribes (`lean/CodeCalculus/Fixtures.lean`) and replays for
well-formedness (`lean/CodeCalculus/FixtureReplay.lean`) against the fixture
set executed by `machine/fixture_conformance.py`, and reports:

  - how many Python fixtures Lean covers,
  - the uncovered fixture ids (the coverage gap),
  - how many Lean state definitions and well-formedness theorems exist,
  - how many of those are result states,
  - a mismatch count (uncovered fixtures).

What it cannot see is stated in the report and in
`the archived notes`. Since the Lean side
replays the single-step and two-step fixtures under `Eval` and `EvalExpr`
(`lean/CodeCalculus/FixtureEvalReplay.lean`); this report counts
well-formedness theorems only and does not read those replays. Distances and
prices are still not computed on the Lean side.
"""

import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
LEAN_FIXTURES = os.path.join(ROOT, "lean", "CodeCalculus", "Fixtures.lean")
LEAN_REPLAY = os.path.join(ROOT, "lean", "CodeCalculus", "FixtureReplay.lean")
FIXTURES_JSON = os.path.join(HERE, "fixtures", "mvp_fixtures.json")


def _load_python_fixture_ids():
    with open(FIXTURES_JSON) as f:
        data = json.load(f)
    return [fx["id"] for fx in data["fixtures"]]


def _parse_lean_state_defs(path):
    """Return list of (def_name, fixture_id, suffix) for fixture_* defs.

    The suffix is `initial`, `result`, or a fixture key of a direct-sum pair
    fixture (e.g. `S_R_prime`), so pair summands are counted too.
    """
    out = []
    with open(path) as f:
        text = f.read()
    for m in re.finditer(r"def\s+(fixture_(W\d+)_(\w+))\s*:", text):
        out.append((m.group(1), m.group(2), m.group(3)))
    return out


def _load_pair_fixture_keys():
    """Fixture ids whose initial state is a named pair of summands.

    A pair fixture's `initial_state` is a dict of fixture keys with no `Q`
    (the state itself) and no `ref` (a pointer to another fixture's state).
    Such a fixture is covered only when every summand is transcribed.
    """
    with open(FIXTURES_JSON) as f:
        data = json.load(f)
    out = {}
    for fx in data["fixtures"]:
        st = fx.get("initial_state")
        if isinstance(st, dict) and "Q" not in st and "ref" not in st:
            out[fx["id"]] = list(st.keys())
    return out


def _parse_lean_theorems(path):
    """Return set of theorem names."""
    out = set()
    with open(path) as f:
        text = f.read()
    for m in re.finditer(r"theorem\s+(\w+)\s*:", text):
        out.add(m.group(1))
    return out


# The ranks of the example-local identifiers in the pinned enumeration, as the
# Lean transcription writes them: `a1 = 0`, `b1 = 10000`, `p1 = 50000`,
# `q1 = 60000` (lean/CodeCalculus/FixtureEvalReplay.lean, module comment).
_IDENTIFIER_BASE = {"a": 0, "b": 10000, "p": 50000, "q": 60000}


def _identifier_rank(identifier):
    m = re.fullmatch(r"([a-z])(\d+)", identifier)
    if m is None or m.group(1) not in _IDENTIFIER_BASE:
        return None
    return _IDENTIFIER_BASE[m.group(1)] + int(m.group(2)) - 1


def _parse_lean_states(path):
    """Return {def_name: ("state", (Q, rows, used)) | ("alias", other_def)}."""
    with open(path) as f:
        text = f.read()

    def numbers(inner):
        return [int(x) for x in inner.replace(" ", "").split(",") if x]

    out = {}
    pattern = (r"def\s+(fixture_W\d+_\w+)\s*:\s*CodeState\s*:=\s*"
               r"(\{.*?\n\}|fixture_W\d+_\w+)")
    for m in re.finditer(pattern, text, re.S):
        name, body = m.group(1), m.group(2)
        if body.startswith("fixture_"):
            out[name] = ("alias", body)
            continue
        rows = [(int(i), sec, numbers(sup)) for (i, sec, sup) in re.findall(
            r"id := (\d+), sector := Sector\.(\w), support := \[(.*?)\]", body)]
        out[name] = ("state", (
            numbers(re.search(r"Q := \[(.*?)\]", body).group(1)),
            rows,
            numbers(re.search(r"used := \[(.*?)\]", body).group(1))))
    return out


def _resolve_lean_state(states, name):
    kind, value = states[name]
    return _resolve_lean_state(states, value) if kind == "alias" else value


def _json_state(fixtures_by_id, state):
    """The JSON state in the Lean encoding, or (None, reason).

    A state is compared only when the JSON gives `Q`, both row lists, and
    `used`, with every identifier in the transcription convention. A `ref`
    is followed to the state it names.
    """
    while isinstance(state, dict) and "ref" in state:
        ref = state["ref"]
        parts = ref.split(".")
        state = fixtures_by_id.get(parts[0])
        for key in parts[1:] or ["initial_state"]:
            if isinstance(state, dict) and key not in state and "expected" in state:
                state = state["expected"]
            state = state.get(key) if isinstance(state, dict) else None
        if state is None:
            return None, "the ref %s does not resolve" % ref
    if not isinstance(state, dict):
        return None, "the fixture records no such state"
    missing = [k for k in ("Q", "rows_X", "rows_Z", "used") if k not in state]
    if missing:
        return None, "the JSON state omits %s" % ", ".join(missing)
    rows = []
    for sector, key in (("X", "rows_X"), ("Z", "rows_Z")):
        for row in state[key]:
            rows.append((_identifier_rank(row["id"]), sector,
                         [int(c) for c in row["support"]]))
    used = [_identifier_rank(u) for u in state["used"]]
    if any(r[0] is None for r in rows) or any(u is None for u in used):
        return None, "an identifier is outside the transcription convention"
    return (list(state["Q"]), rows, used), None


def transcription_report():
    """Compare every transcribed Lean state with the JSON state it names.

    Rows are compared as a set per state, because the JSON lists the `X`
    rows before the `Z` rows and a Lean display may interleave them.
    """
    states = _parse_lean_states(LEAN_FIXTURES)
    with open(FIXTURES_JSON) as f:
        fixtures_by_id = {fx["id"]: fx for fx in json.load(f)["fixtures"]}
    matched, mismatched, not_compared = [], [], {}
    for name in sorted(states):
        m = re.fullmatch(r"fixture_(W\d+)_(\w+)", name)
        fixture = fixtures_by_id.get(m.group(1))
        if fixture is None:
            not_compared[name] = "no such fixture in the JSON"
            continue
        suffix = m.group(2)
        if suffix == "initial":
            source = fixture.get("initial_state")
        elif suffix == "result":
            source = (fixture.get("expected") or {}).get("result_state")
        else:
            source = (fixture.get("initial_state") or {}).get(suffix)
        expected, reason = _json_state(fixtures_by_id, source)
        if expected is None:
            not_compared[name] = reason
            continue
        q, rows, used = _resolve_lean_state(states, name)
        if (q == expected[0] and sorted(rows) == sorted(expected[1])
                and used == expected[2]):
            matched.append(name)
        else:
            mismatched.append(name)
    return {"matched": matched, "mismatched": mismatched,
            "not_compared": not_compared}


def _expected_theorem_name(def_name):
    # fixture_W0_initial -> fixture_W0_initial_wellFormed
    return def_name + "_wellFormed"


def coverage_report():
    py_ids = _load_python_fixture_ids()
    py_set = set(py_ids)
    defs = _parse_lean_state_defs(LEAN_FIXTURES)
    theorems = _parse_lean_theorems(LEAN_REPLAY)

    suffixes = {}
    for (_, fid, suffix) in defs:
        suffixes.setdefault(fid, set()).add(suffix)
    pair_keys = _load_pair_fixture_keys()

    covered_fixtures = []
    for fid in py_ids:
        keys = pair_keys.get(fid)
        if keys is None:
            ok = fid in suffixes
        else:
            ok = all(k in suffixes.get(fid, set()) for k in keys)
        if ok:
            covered_fixtures.append(fid)
    uncovered = sorted(py_set - set(covered_fixtures))

    # theorem coverage: every def should have a well-formedness theorem
    missing_theorems = []
    for (name, fid, kind) in defs:
        th = _expected_theorem_name(name)
        if th not in theorems:
            missing_theorems.append(name)

    result_defs = [(name, fid) for (name, fid, kind) in defs if kind == "result"]

    # python fixtures that declare a result_state
    with open(FIXTURES_JSON) as f:
        data = json.load(f)
    py_with_result = [fx["id"] for fx in data["fixtures"]
                      if isinstance(fx.get("expected"), dict)
                      and fx["expected"].get("result_state") is not None]

    report = {
        "python_fixtures": len(py_ids),
        "lean_state_defs": len(defs),
        "pair_fixtures": pair_keys,
        "lean_covered_fixtures": len(covered_fixtures),
        "lean_uncovered_fixtures": uncovered,
        "lean_result_state_defs": len(result_defs),
        "lean_result_state_fixture_ids": sorted({fid for (_, fid) in result_defs}),
        "python_fixtures_with_result_state": len(py_with_result),
        "well_formedness_theorems": len(theorems),
        "missing_theorems": missing_theorems,
        "mismatch_count": len(uncovered),
    }
    return report


def main():
    r = coverage_report()
    print("Lean <-> Python fixture coverage (spike)")
    print("  python fixtures:                  %d" % r["python_fixtures"])
    print("  lean state definitions:           %d" % r["lean_state_defs"])
    print("  lean covered fixtures:            %d" % r["lean_covered_fixtures"])
    print("  lean result-state definitions:    %d" % r["lean_result_state_defs"])
    print("  well-formedness theorems:         %d" % r["well_formedness_theorems"])
    print("  python fixtures with result_state:%d" % r["python_fixtures_with_result_state"])
    print("  uncovered fixtures (%d):          %s" % (len(r["lean_uncovered_fixtures"]),
                                                       ", ".join(r["lean_uncovered_fixtures"])))
    print("  missing theorems:                 %s" % (r["missing_theorems"] or "none"))
    print("  mismatch count (coverage gaps):   %d" % r["mismatch_count"])
    print()
    print("What this cannot see:")
    print("  - This report counts well-formedness theorems only. The Eval/EvalExpr")
    print("    replays of the single-step and two-step fixtures (positive and negative)")
    print(" live in lean/CodeCalculus/FixtureEvalReplay.lean and are")
    print("    not counted here.")
    print("  - No distance, price, or interval transport is computed on the Lean side.")
    if "W24" in r["lean_uncovered_fixtures"]:
        print("  - W24 (119 qubits, 85 rows) cannot be replayed through")
        print("    `wellFormedBool`: its independence check would enumerate 2^45")
        print("    coefficient vectors for the 46-row Z sector. Replaying it needs a")
        print("    bitmask-based independence test (the MaskRank machinery).")
    unc = r["lean_uncovered_fixtures"]
    if unc:
        print("  - The uncovered fixtures are absent from Lean entirely (%s);"
              % ", ".join(unc))
        print("    their Python outcomes are not cross-checked.")
    else:
        print("  - All fixtures are transcribed into Lean.")
    t = transcription_report()
    print("  - State encodings differ (Python uses string ids/supports; Lean uses")
    print("    integer ids/support lists). The transcription check below reads")
    print("    the Lean source as text and does not run Lean.")
    print()
    print("Transcription against the JSON (Q, rows as a set, used):")
    print("  matching Lean states:             %d" % len(t["matched"]))
    print("  mismatching Lean states:          %s"
          % (", ".join(t["mismatched"]) or "none"))
    print("  not compared (%d):" % len(t["not_compared"]))
    for name in sorted(t["not_compared"]):
        print("    %s: %s" % (name, t["not_compared"][name]))
    return 1 if t["mismatched"] else 0


if __name__ == "__main__":
    sys.exit(main())
