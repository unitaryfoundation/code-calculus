"""Conformance harness for the symplectic move set (issue #305).

Companion to ``priced_conformance_harness.py`` for the machine-side
stabilizer model of ``machine/symplectic_calculus.py``. It generates small
random stabilizer codes, applies every move of the symplectic move set
(``SYM-SKIP``, ``SYM-ADD-CHECK``, ``SYM-DELETE-CHECK``, ``SYM-DIRECT-SUM``,
``X-SYMPLECTIC-DOUBLE``, ``X-SYMPLECTIC-HALVE``), measures the exact Pauli
distance of every parent and child with the exhaustive oracle below (the
CSS child of a doubling with the CSS oracle of ``issue21_challenge_replay``),
and asserts that every interval the ledger emits contains the exact value.
It also replays the fixtures of ``machine/fixtures/symplectic_fixtures.json``.

Evidence only. The move set is not an admitted calculus rule (the
extended-state layer is a Gate 6 decision that has not been taken), and a
run with zero violations is a run that failed to falsify the interval rules
derived in ``notes/harness/symplectic_move_set_2026-11-10.md``, nothing more.
The oracle lives here and is never called by the model module.

As in the CSS harness (issue #235), lower endpoints are seeded nonzero on
most cases and a little upper-endpoint slack is added, so the lower-endpoint
rules are exercised; the suite fails if a move is never transited or never
transited with a nonzero lower endpoint on its input ledger. The JSON report
goes to an untracked path (``SYMPLECTIC_CONFORMANCE_REPORT``, default in the
system temporary directory); ``SYMPLECTIC_CONFORMANCE_CASES`` overrides the
case count.
"""

from __future__ import print_function

import json
import os
import random
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
MACHINE = os.path.dirname(HERE)
ROOT = os.path.dirname(MACHINE)
for path in (MACHINE, ROOT, HERE):
    if path not in sys.path:
        sys.path.insert(0, path)

from machine import priced_calculus as pc
from machine import symplectic_calculus as sc
from issue21_challenge_replay import exact_distances

MOVES = ("SYM-SKIP", "SYM-ADD-CHECK", "SYM-DELETE-CHECK", "SYM-DIRECT-SUM",
         "X-SYMPLECTIC-DOUBLE", "X-SYMPLECTIC-HALVE")

DEFAULT_CASES = 150
DEFAULT_SEED = 20261110
DEFAULT_REPORT_PATH = os.path.join(tempfile.gettempdir(),
                                   "symplectic_conformance_report.json")
FIXTURES_PATH = os.path.join(MACHINE, "fixtures", "symplectic_fixtures.json")


def _popcount(value):
    return bin(value).count("1")


# ---------------------------------------------------------------------------
# The exhaustive Pauli-distance oracle (external to the model)
# ---------------------------------------------------------------------------


def pauli_distance(state):
    """Exact Pauli distance of a symplectic state, with a lightest witness.

    Enumerates every Pauli operator on the state's labels (4^n of them), keeps
    those that commute with every displayed row and lie outside the
    stabilizer span, and returns ``(weight, (x, z))`` of a lightest one, or
    ``(None, None)`` when there is none (``k = 0``: the distance is +inf).
    Never called by the model module.
    """
    labels = list(state.Q)
    width = state.width()
    vectors = state.vectors()
    row_pairs = [(pc.support_mask(r.x), pc.support_mask(r.z)) for r in state.rows]
    best = None
    best_witness = None
    # Each qubit is I, X, Z, or Y: enumerate by two masks over the labels.
    subsets = [0]
    for label in labels:
        bit = 1 << label
        subsets = subsets + [m | bit for m in subsets]
    for xmask in subsets:
        for zmask in subsets:
            weight = _popcount(xmask | zmask)
            if weight == 0:
                continue
            if best is not None and weight >= best:
                continue
            if any((_popcount(xmask & rz) + _popcount(zmask & rx)) % 2
                   for rx, rz in row_pairs):
                continue
            vector = xmask | (zmask << width)
            if sc._in_span(vector, vectors):
                continue
            best = weight
            best_witness = (tuple(q for q in labels if (xmask >> q) & 1),
                            tuple(q for q in labels if (zmask >> q) & 1))
    return best, best_witness


# ---------------------------------------------------------------------------
# Random states and ledgers
# ---------------------------------------------------------------------------


def random_stabilizer_state(rng, q_labels, id_prefix="a"):
    """One well-formed random stabilizer code over the given labels: rows
    are drawn as random Paulis and kept when they commute with, and are
    independent of, the rows already chosen."""
    labels = sorted(q_labels)
    n = len(labels)
    width = (max(labels) + 1) if labels else 0
    target = rng.randrange(0, n) if n else 0
    rows = []
    vectors = []
    attempts = 0
    while len(rows) < target and attempts < 2000:
        attempts += 1
        x = []
        z = []
        for q in labels:
            pauli = rng.choice("IXZY")
            if pauli in "XY":
                x.append(q)
            if pauli in "ZY":
                z.append(q)
        if not x and not z:
            continue
        if any(sc.symplectic_inner_product((x, z), (r.x, r.z)) for r in rows):
            continue
        vector = sc._vector(x, z, width)
        if sc._in_span(vector, vectors):
            continue
        identifier = "%s%d" % (id_prefix, len(rows) + 1)
        rows.append(sc.SymplecticRow(identifier, tuple(x), tuple(z)))
        vectors.append(vector)
    state = sc.SymplecticState(tuple(labels), tuple(rows),
                               frozenset(r.id for r in rows))
    state.validate()
    return state


def _seed_lower(exact, lower_seed):
    """A lower endpoint at most ``exact`` (0 when the distance is +inf and
    the seed is numeric; the seed ``"exact"`` reads the oracle)."""
    if lower_seed == "exact":
        return 0 if exact is None else exact
    lower_seed = int(lower_seed)
    if exact is None:
        return lower_seed
    return min(max(lower_seed, 0), exact)


def init_ledger(state, lower_seed=0, upper_slack=0):
    """Seed a ledger from the oracle: lower endpoint per ``lower_seed``,
    upper endpoint the exact value plus ``upper_slack`` (+inf when there is
    no logical), and the oracle's lightest logical as a witness."""
    exact, witness = pauli_distance(state)
    lower = _seed_lower(exact, lower_seed)
    if exact is None:
        full = pc.Interval(lower, None)
    else:
        full = pc.Interval(lower, exact + upper_slack)
    ledger = sc.SymplecticLedger(full)
    if witness is not None:
        ledger.record_witness(state, witness[0], witness[1], source="oracle witness")
    return ledger, exact


def _contains(interval, exact):
    if exact is None:
        return interval.upper is None
    lower = interval.lower if interval.lower is not None else float("inf")
    if exact < lower:
        return False
    if interval.upper is not None and exact > interval.upper:
        return False
    return True


def _check_full(ledger, exact):
    if _contains(ledger.full, exact):
        return []
    return ["interval %s does not contain %s" % (ledger.full.as_json(), exact)]


def _check_css_ledger(ledger, exact):
    reasons = []
    if not _contains(ledger.full, exact["d"]):
        reasons.append("full interval %s does not contain %s"
                       % (ledger.full.as_json(), exact["d"]))
    for side in ("X", "Z"):
        if not _contains(ledger.sector[side], exact[side]):
            reasons.append("%s interval %s does not contain %s"
                           % (side, ledger.sector[side].as_json(), exact[side]))
    return reasons


def _check_decide(ledger, target):
    """A verdict must be justified by the endpoint that justifies it."""
    if target is None:
        return []
    verdict = ledger.decide(target)
    if verdict == "certify" and not (ledger.full.lower is None
                                     or ledger.full.lower >= target):
        return ["certify at target %s but lower endpoint %s" % (target, ledger.full.lower)]
    if verdict == "prune" and not (ledger.full.upper is not None
                                   and ledger.full.upper < target):
        return ["prune at target %s but upper endpoint %s" % (target, ledger.full.upper)]
    return []


def _check_state_invariants(parent, child):
    reasons = []
    try:
        child.validate()
    except (pc.Malformed, ValueError, TypeError) as exc:
        reasons.append("validate() failed: %s" % exc)
    if not set(parent.used) <= set(child.used):
        reasons.append("used shrank")
    live = [r.id for r in child.rows]
    if len(live) != len(set(live)):
        reasons.append("duplicate live row identifiers")
    if not set(live) <= set(child.used):
        reasons.append("live row identifier not in used")
    return reasons


def _has_nonzero_lower(ledger):
    return ledger.full.lower is not None and ledger.full.lower > 0


def _note_input(coverage, op, ledger):
    if coverage is None:
        return
    entry = coverage.setdefault(op, {"transports": 0, "nonzero_lower_inputs": 0})
    entry["transports"] += 1
    if _has_nonzero_lower(ledger):
        entry["nonzero_lower_inputs"] += 1


def _ceil_half(value):
    return None if value is None else (value + 1) // 2


# ---------------------------------------------------------------------------
# One random case
# ---------------------------------------------------------------------------


def run_case(rng, state, lower_seed=0, upper_slack=0, coverage=None):
    """Run one random state through every move; return the violations."""
    violations = []

    def violation(op, reasons):
        violations.append({"operation": op, "state_n": state.n(), "reasons": reasons})

    ledger, exact = init_ledger(state, lower_seed=lower_seed, upper_slack=upper_slack)
    reasons = _check_full(ledger, exact) + _check_decide(ledger, exact)
    if reasons:
        violation("initial", reasons)

    # SYM-SKIP
    _note_input(coverage, "SYM-SKIP", ledger)
    out = ledger.propagate({"op": "SYM-SKIP"}, state.skip())
    reasons = _check_full(out, exact) + _check_decide(out, exact)
    if reasons:
        violation("SYM-SKIP", reasons)

    # SYM-ADD-CHECK: a few random Paulis
    for _ in range(4):
        x = []
        z = []
        for q in state.Q:
            pauli = rng.choice("IXZY")
            if pauli in "XY":
                x.append(q)
            if pauli in "ZY":
                z.append(q)
        try:
            child = state.add_check(tuple(x), tuple(z))
        except (pc.NoDerivation, pc.Malformed, ValueError):
            continue
        inv = _check_state_invariants(state, child)
        if inv:
            violation("SYM-ADD-CHECK", inv)
            continue
        child_exact, _w = pauli_distance(child)
        _note_input(coverage, "SYM-ADD-CHECK", ledger)
        out = ledger.propagate({"op": "SYM-ADD-CHECK"}, child)
        reasons = _check_full(out, child_exact) + _check_decide(out, child_exact)
        if reasons:
            violation("SYM-ADD-CHECK", reasons)

    # SYM-DELETE-CHECK
    if state.rows:
        row = rng.choice(state.rows)
        try:
            child = state.delete_check(row.id)
        except (pc.NoDerivation, pc.Malformed, ValueError):
            child = None
        if child is not None:
            inv = _check_state_invariants(state, child)
            if inv:
                violation("SYM-DELETE-CHECK", inv)
            else:
                child_exact, _w = pauli_distance(child)
                _note_input(coverage, "SYM-DELETE-CHECK", ledger)
                out = ledger.propagate({"op": "SYM-DELETE-CHECK"}, child)
                reasons = _check_full(out, child_exact) + _check_decide(out, child_exact)
                if reasons:
                    violation("SYM-DELETE-CHECK", reasons)

    # SYM-DIRECT-SUM with a small random code on fresh labels
    offset = (max(state.Q) if state.Q else -1) + 1
    other = random_stabilizer_state(rng, [offset + i for i in range(rng.randint(1, 3))],
                                    id_prefix="c")
    try:
        total = sc.SymplecticState.direct_sum(state, other)
    except (pc.NoDerivation, pc.Malformed, ValueError) as exc:
        violation("SYM-DIRECT-SUM", ["refused on disjoint factors: %s" % exc])
        total = None
    if total is not None:
        inv = _check_state_invariants(state, total)
        if inv:
            violation("SYM-DIRECT-SUM", inv)
        else:
            other_ledger, _other_exact = init_ledger(other, lower_seed=lower_seed,
                                                     upper_slack=upper_slack)
            _note_input(coverage, "SYM-DIRECT-SUM", ledger)
            out = sc.SymplecticLedger.direct_sum(ledger, other_ledger)
            total_exact, _w = pauli_distance(total)
            reasons = _check_full(out, total_exact) + _check_decide(out, total_exact)
            if reasons:
                violation("SYM-DIRECT-SUM", reasons)

    # X-SYMPLECTIC-DOUBLE, then X-SYMPLECTIC-HALVE back along the copy swap
    try:
        css = state.double()
    except (pc.NoDerivation, pc.Malformed, ValueError) as exc:
        violation("X-SYMPLECTIC-DOUBLE", ["refused: %s" % exc])
        css = None
    if css is not None:
        reasons = []
        try:
            css.validate()
        except (pc.Malformed, ValueError) as exc:
            reasons.append("doubled CSS state does not validate: %s" % exc)
        if css.n() != 2 * state.n():
            reasons.append("n' = %d is not 2n = %d" % (css.n(), 2 * state.n()))
        if css.k() != 2 * state.k():
            reasons.append("k' = %d is not 2k = %d" % (css.k(), 2 * state.k()))
        if not set(state.used) <= set(css.used):
            reasons.append("used shrank")
        _note_input(coverage, "X-SYMPLECTIC-DOUBLE", ledger)
        css_ledger = ledger.double(state, css)
        css_exact = exact_distances(css)
        reasons += _check_css_ledger(css_ledger, css_exact)
        reasons += _check_decide(css_ledger, css_exact["d"])
        if exact is not None and css_exact["d"] is not None:
            if not (exact <= css_exact["d"] <= 2 * exact):
                reasons.append("doubled distance %s outside [%s, %s]"
                               % (css_exact["d"], exact, 2 * exact))
        elif (exact is None) != (css_exact["d"] is None):
            reasons.append("doubling changed finiteness of the distance")
        if reasons:
            violation("X-SYMPLECTIC-DOUBLE", reasons)

        pairs = state.doubling_pairs()
        try:
            back = sc.SymplecticState.halve(css, pairs)
        except (pc.NoDerivation, pc.Malformed, ValueError) as exc:
            violation("X-SYMPLECTIC-HALVE", ["refused on a doubled parent: %s" % exc])
            back = None
        if back is not None:
            reasons = []
            try:
                back.validate()
            except (pc.Malformed, ValueError) as exc:
                reasons.append("halved state does not validate: %s" % exc)
            if back.n() != state.n() or back.k() != state.k():
                reasons.append("halving the double did not return (n, k)")
            # the CSS parent ledger seeded from its own oracle, with slack
            parent_lower = _seed_lower(css_exact["d"], lower_seed)
            parent_full = (pc.Interval(parent_lower, None) if css_exact["d"] is None
                           else pc.Interval(parent_lower, css_exact["d"] + upper_slack))
            sector = {}
            for side in ("X", "Z"):
                side_lower = _seed_lower(css_exact[side], lower_seed)
                sector[side] = (pc.Interval(side_lower, None) if css_exact[side] is None
                                else pc.Interval(side_lower, css_exact[side] + upper_slack))
            parent_ledger = pc.DistanceLedger(parent_full, sector, {"X": [], "Z": []}, [])
            for side in ("X", "Z"):
                for witness in css_ledger.witnesses[side]:
                    try:
                        parent_ledger.record_witness(css, side, witness["support"],
                                                     source=witness.get("source", "witness"))
                    except pc.NoDerivation:
                        continue
            _note_input(coverage, "X-SYMPLECTIC-HALVE",
                        sc.SymplecticLedger(parent_full))
            out = sc.SymplecticLedger.halve(parent_ledger, css, back, pairs)
            back_exact, _w = pauli_distance(back)
            reasons += _check_full(out, back_exact) + _check_decide(out, back_exact)
            if back_exact != exact:
                reasons.append("halving the double changed the distance: %s to %s"
                               % (exact, back_exact))
            if reasons:
                violation("X-SYMPLECTIC-HALVE", reasons)
    return violations


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------


def _state_from_json(doc):
    """A symplectic state from ``{"Q", "rows": [{"id", "x", "z"}], "used"}``
    or a CSS state from ``{"Q", "rows_X", "rows_Z", "used"}``."""
    if "rows_X" in doc or "rows_Z" in doc:
        rows = []
        for sector in ("X", "Z"):
            for r in doc.get("rows_%s" % sector, []):
                rows.append(pc.Row(r["id"], sector, tuple(sorted(r["support"]))))
        return pc.CodeState(tuple(doc["Q"]), tuple(rows), frozenset(doc["used"]))
    rows = [sc.SymplecticRow(r["id"], tuple(sorted(r["x"])), tuple(sorted(r["z"])))
            for r in doc["rows"]]
    return sc.SymplecticState(tuple(doc["Q"]), tuple(rows), frozenset(doc["used"]))


def _exact_of(state):
    if isinstance(state, pc.CodeState):
        return exact_distances(state)["d"]
    return pauli_distance(state)[0]


def _read_distance(value):
    if value == "+inf":
        return None
    return value


def load_fixtures(path=FIXTURES_PATH):
    with open(path) as f:
        return json.load(f)


def run_fixture(record):
    """Replay one fixture record; return its violations."""
    reasons = []
    fid = record["id"]
    expected = record["expected"]
    try:
        state = _state_from_json(record["initial_state"])
        state.validate()
    except (pc.Malformed, ValueError, KeyError, TypeError) as exc:
        if expected.get("outcome") == "malformed" and record.get("operation") is None:
            return []
        return [{"fixture": fid, "reasons": ["initial state failed: %s" % exc]}]
    exact0 = _exact_of(state)
    if "distance_oracle" in expected and record.get("operation") is None:
        if exact0 != _read_distance(expected["distance_oracle"]):
            reasons.append("oracle distance %s differs from recorded %s"
                           % (exact0, expected["distance_oracle"]))
    operation = record.get("operation")
    if operation is None:
        params = expected.get("parameters", {})
        if "n" in params and state.n() != params["n"]:
            reasons.append("n = %d, recorded %d" % (state.n(), params["n"]))
        if "k" in params and state.k() != params["k"]:
            reasons.append("k = %d, recorded %d" % (state.k(), params["k"]))
        if "w" in params and state.w() != params["w"]:
            reasons.append("w = %d, recorded %d" % (state.w(), params["w"]))
        return [{"fixture": fid, "reasons": reasons}] if reasons else []
    op = dict(operation)
    right = None
    if "right_state" in op:
        right = _state_from_json(op["right_state"])
        op["right_state"] = right
    try:
        if isinstance(state, pc.CodeState):
            child = sc.SymplecticState.halve(state, op.get("pairs"))
        else:
            child = sc.apply_symplectic_operation(state, op)
        outcome = "derivable"
    except pc.NoDerivation:
        outcome = "no_derivation"
        child = None
    except (pc.Malformed, TypeError):
        outcome = "malformed"
        child = None
    if outcome != expected["outcome"]:
        reasons.append("outcome %s, recorded %s" % (outcome, expected["outcome"]))
        return [{"fixture": fid, "reasons": reasons}]
    if child is None:
        return []
    params = expected.get("parameters", {})
    if "n" in params and child.n() != params["n"]:
        reasons.append("child n = %d, recorded %d" % (child.n(), params["n"]))
    if "k" in params and child.k() != params["k"]:
        reasons.append("child k = %d, recorded %d" % (child.k(), params["k"]))
    child_exact = _exact_of(child)
    if "distance_oracle" in expected:
        if child_exact != _read_distance(expected["distance_oracle"]):
            reasons.append("child oracle distance %s differs from recorded %s"
                           % (child_exact, expected["distance_oracle"]))
    # ledger transport from the exact parent interval
    if isinstance(state, pc.CodeState):
        parent_exact = exact_distances(state)
        parent = pc.DistanceLedger(
            pc.Interval(0 if parent_exact["d"] is None else parent_exact["d"], parent_exact["d"]),
            {side: pc.Interval(0 if parent_exact[side] is None else parent_exact[side],
                               parent_exact[side]) for side in ("X", "Z")},
            {"X": [], "Z": []}, [])
        out = sc.SymplecticLedger.halve(parent, state, child, op.get("pairs"))
        reasons += _check_full(out, child_exact)
        expected_interval = expected.get("interval")
        if expected_interval is not None and out.full.as_json() != expected_interval:
            reasons.append("interval %s, recorded %s" % (out.full.as_json(), expected_interval))
    else:
        ledger, _e = init_ledger(state, lower_seed="exact")
        if op["op"] == "SYM-DIRECT-SUM":
            right_ledger, _re = init_ledger(right, lower_seed="exact")
            out = sc.SymplecticLedger.direct_sum(ledger, right_ledger)
            reasons += _check_full(out, child_exact)
            interval = out.full.as_json()
        elif op["op"] == "X-SYMPLECTIC-DOUBLE":
            out = ledger.double(state, child)
            css_exact = exact_distances(child)
            reasons += _check_css_ledger(out, css_exact)
            interval = out.full.as_json()
        else:
            out = ledger.propagate(op, child)
            reasons += _check_full(out, child_exact)
            interval = out.full.as_json()
        expected_interval = expected.get("interval")
        if expected_interval is not None and interval != expected_interval:
            reasons.append("interval %s, recorded %s" % (interval, expected_interval))
    return [{"fixture": fid, "reasons": reasons}] if reasons else []


def run_fixtures(path=FIXTURES_PATH):
    doc = load_fixtures(path)
    violations = []
    for record in doc["fixtures"]:
        violations.extend(run_fixture(record))
    return violations


# ---------------------------------------------------------------------------
# Suite
# ---------------------------------------------------------------------------


def run_suite(cases=DEFAULT_CASES, seed=DEFAULT_SEED):
    rng = random.Random(seed)
    coverage = {}
    total_violations = 0
    violation_shapes = []
    per_op = {}
    lower_seed_counts = {}
    fixture_violations = run_fixtures()
    total_violations += len(fixture_violations)
    violation_shapes.extend(fixture_violations[:20])
    for case_index in range(cases):
        if case_index < 12:
            lower_seed = 1 + (case_index % 3)
            upper_slack = case_index % 2
        else:
            lower_seed = rng.choice((0, 1, 1, 2, "exact"))
            upper_slack = rng.choice((0, 0, 1))
        lower_seed_counts[str(lower_seed)] = lower_seed_counts.get(str(lower_seed), 0) + 1
        n = rng.randint(2, 5)
        state = random_stabilizer_state(rng, list(range(n)))
        for v in run_case(rng, state, lower_seed=lower_seed, upper_slack=upper_slack,
                          coverage=coverage):
            total_violations += 1
            per_op[v["operation"]] = per_op.get(v["operation"], 0) + 1
            if len(violation_shapes) < 20:
                violation_shapes.append(v)
    never = [op for op in MOVES if coverage.get(op, {}).get("transports", 0) == 0]
    without = [op for op in MOVES
               if coverage.get(op, {}).get("nonzero_lower_inputs", 0) == 0]
    return {
        "harness": "symplectic_conformance_harness",
        "git_commit": _git_commit(),
        "cases": cases,
        "fixture_violations": len(fixture_violations),
        "total_violations": total_violations,
        "per_operation_violation_counts": per_op,
        "lower_seed_counts": lower_seed_counts,
        "coverage_by_operation": coverage,
        "moves": list(MOVES),
        "moves_never_transited": never,
        "moves_without_nonzero_lower_case": without,
        "violation_shapes": violation_shapes,
        "note": "Evidence only about a machine-side move set; the extended-state "
                "layer is not admitted and no obligation is discharged.",
    }


def _git_commit():
    try:
        return subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT,
                                       stderr=subprocess.DEVNULL).decode().strip()
    except (OSError, subprocess.SubprocessError):
        return "unknown"


def _report_path():
    override = os.environ.get("SYMPLECTIC_CONFORMANCE_REPORT")
    if override == "-":
        return None
    return override or DEFAULT_REPORT_PATH


def main():
    cases = DEFAULT_CASES
    raw = os.environ.get("SYMPLECTIC_CONFORMANCE_CASES")
    if raw:
        try:
            cases = max(1, int(raw))
        except ValueError:
            print("ignoring non-integer SYMPLECTIC_CONFORMANCE_CASES=%r" % raw)
    report = run_suite(cases=cases)
    print(json.dumps({k: report[k] for k in (
        "cases", "fixture_violations", "total_violations",
        "per_operation_violation_counts", "lower_seed_counts",
        "coverage_by_operation", "moves_never_transited",
        "moves_without_nonzero_lower_case")}, indent=2))
    out_path = _report_path()
    if out_path:
        try:
            parent = os.path.dirname(os.path.abspath(out_path))
            if parent:
                os.makedirs(parent, exist_ok=True)
            with open(out_path, "w") as f:
                json.dump(report, f, indent=2)
            print("report written to %s" % out_path)
        except OSError as exc:
            print("report not written (%s)" % exc)
    failures = []
    if report["total_violations"]:
        failures.append("%d violations" % report["total_violations"])
    if report["moves_never_transited"]:
        failures.append("moves never transited: %s" % ", ".join(report["moves_never_transited"]))
    if report["moves_without_nonzero_lower_case"]:
        failures.append("moves without a nonzero-lower-endpoint case: %s"
                        % ", ".join(report["moves_without_nonzero_lower_case"]))
    if failures:
        raise SystemExit("; ".join(failures))


if __name__ == "__main__":
    main()
