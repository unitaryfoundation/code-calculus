"""External code ingestion: a matrix presentation to a Lean `CodeState`.

The contract is `spec/REPRESENTATION.md` §9. A presentation is a document
of the shape `CodeState.from_challenge` accepts: a qubit count ``n``, a
logical count ``k``, and ``checks`` with one list of supports per sector.

Three things are produced from it.

* The ingested state (`ingest`). The rows of each sector are put in
  canonical order (each support sorted, then the rows sorted) and the
  first independent ones are retained, so two presentations with the same
  binding hash give the same state.
* The binding hash (`checks_sha256`): sha256 over the compact JSON of
  ``{"X": rows, "Z": rows}`` in canonical order. It is the
  ``checks_sha256`` of qldpc-challenge's ``verify/check_certs.py`` for a
  CSS entry, digit for digit.
* A Lean block (`lean_ingestion_block`): the presentation as a literal,
  the recorded hash, the state, and the theorem that the state is an
  ingestion of the literal (`presentationBinds`,
  `lean/CodeCalculus/Ingestion.lean`), by kernel ``decide``.

Nothing here is trusted. A wrong translation either fails ``decide`` or
yields a module whose literal has another hash. `binding_failures` is the
check for the second case: it reads the literal back out of the Lean
source, hashes it independently of the generator, and compares the result
with the recorded hash and with the hash of the source document.
"""

import hashlib
import json
import re

from machine.certificates import (
    LEAN_SECTOR,
    _lean_bool_list,
    _lean_nat_list,
    lean_state_term,
)
from machine.priced_calculus import CodeState, Malformed, support_mask

SECTORS = ("X", "Z")
LEAN_NAME = re.compile(r"[a-z][a-z0-9_]*\Z")


def canonical_checks(document):
    """The check rows in canonical order: supports sorted, then rows sorted."""
    try:
        checks = document["checks"]
        if "X" not in checks or "Z" not in checks:
            raise ValueError("checks must carry an X list and a Z list")
        canon = {}
        for side in SECTORS:
            rows = []
            for row in checks[side]:
                support = []
                for q in row:
                    if not isinstance(q, int) or isinstance(q, bool) or q < 0:
                        raise ValueError("a qubit label is not a natural number")
                    support.append(q)
                if len(set(support)) != len(support):
                    raise ValueError("a support repeats a qubit")
                rows.append(sorted(support))
            canon[side] = sorted(rows)
    except (KeyError, TypeError, ValueError) as exc:
        raise Malformed("not a CSS matrix presentation: %s" % exc)
    return canon


def _digest(canon):
    blob = json.dumps(canon, separators=(",", ":"), sort_keys=True)
    return hashlib.sha256(blob.encode("ascii")).hexdigest()


def checks_sha256(document):
    """The binding hash of a presentation."""
    return _digest(canonical_checks(document))


def ingest(document):
    """The ingested state of a presentation.

    `CodeState.from_challenge` applied to the canonically ordered rows:
    qubits ``0 .. n - 1``, the first independent rows of each sector
    retained, identifiers ``a1, a2, ...`` and ``b1, b2, ...`` in that
    order, and ``used`` the retained identifiers. Raises `Malformed` on a
    document that is not a CSS presentation, whose rows do not commute, or
    whose declared ``k`` is not the one the row ranks give.
    """
    canon = canonical_checks(document)
    try:
        ordered = {"n": document["n"], "k": document.get("k"), "checks": canon}
    except (KeyError, TypeError, AttributeError) as exc:
        raise Malformed("not a CSS matrix presentation: %s" % exc)
    return CodeState.from_challenge(ordered)


def _span_coefficients(retained, target):
    """Coefficients over ``retained`` masks whose combination is ``target``."""
    basis = []
    for index, mask in enumerate(retained):
        combo = 1 << index
        for pivot, vector, used in basis:
            if mask >> pivot & 1:
                mask ^= vector
                combo ^= used
        if mask == 0:
            raise ValueError("retained rows are dependent")
        basis.append((mask.bit_length() - 1, mask, combo))
    combo = 0
    for pivot, vector, used in basis:
        if target >> pivot & 1:
            target ^= vector
            combo ^= used
    if target != 0:
        raise ValueError("a presented row is outside the retained span")
    return [bool(combo >> index & 1) for index in range(len(retained))]


def span_coefficients(document, state):
    """For each canonical row, its coefficients over the retained rows."""
    canon = canonical_checks(document)
    result = {}
    for side in SECTORS:
        retained = [row.mask for row in state.sector_rows(side)]
        result[side] = [
            _span_coefficients(retained, support_mask(tuple(support)))
            for support in canon[side]]
    return result


def _lean_rows(rows, render):
    return "[%s]" % ", ".join(render(row) for row in rows)


def lean_ingestion_block(name, document, include_well_formedness=True):
    """Lean source binding the ingested state ``name`` to ``document``.

    Emits ``<name>_presentation``, ``<name>_checks_sha256``, the state
    ``<name>`` with ``<name>_wellFormed``, ``<name>_span``, and the theorem
    ``<name>_binds``. Returns the block and the state.

    With ``include_well_formedness`` false the ``<name>_wellFormed``
    theorem is left out. Its kernel ``decide`` enumerates every
    combination of a sector's other rows for each row, so its cost is
    exponential in the retained rows per sector
    (`well_formedness_feasible`); the binding and certificate theorems do
    not use it.
    """
    if not LEAN_NAME.match(name):
        raise ValueError("not a usable Lean name: %r" % (name,))
    canon = canonical_checks(document)
    state = ingest(document)
    coefficients = span_coefficients(document, state)
    lines = [
        "def %s_presentation : Presentation := {" % name,
        "  n := %d," % state.n(),
        "  X := %s," % _lean_rows(canon["X"], _lean_nat_list),
        "  Z := %s" % _lean_rows(canon["Z"], _lean_nat_list),
        "}",
        "",
        'def %s_checks_sha256 : String := "%s"' % (name, _digest(canon)),
        "",
        "def %s : CodeState := %s" % (name, lean_state_term(state)),
        "",
    ]
    if include_well_formedness:
        lines += [
            "theorem %s_wellFormed : EncodingWellFormed %s :=" % (name, name),
            "  encodingWellFormed_of_bool (by decide)",
            "",
        ]
    lines += [
        "def %s_span : SpanCoefficients := {" % name,
        "  X := %s," % _lean_rows(coefficients["X"], _lean_bool_list),
        "  Z := %s" % _lean_rows(coefficients["Z"], _lean_bool_list),
        "}",
        "",
        "theorem %s_binds :" % name,
        "    presentationBinds %s %s_presentation %s_span = true := by decide"
        % (name, name, name),
    ]
    return "\n".join(lines), state


def lean_ingestion_module(header, blocks, namespace="IngestedInstances"):
    """A Lean module from ingestion blocks and any certificate blocks."""
    parts = [
        "import CodeCalculus.Ingestion",
        "import CodeCalculus.WellFormedBool",
        "",
        "/-!\n%s\n-/" % header.strip(),
        "",
        "namespace CodeCalculus.%s" % namespace,
    ]
    for block in blocks:
        parts += ["", block]
    parts += ["", "end CodeCalculus.%s" % namespace, ""]
    return "\n".join(parts)


_PRESENTATION = re.compile(
    r"^def (?P<name>[a-z][a-z0-9_]*)_presentation : Presentation := \{\n"
    r"  n := (?P<n>[0-9]+),\n"
    r"  X := (?P<X>\[[0-9\[\], ]*\]),\n"
    r"  Z := (?P<Z>\[[0-9\[\], ]*\])\n"
    r"\}$", re.MULTILINE)
_RECORDED = re.compile(
    r'^def (?P<name>[a-z][a-z0-9_]*)_checks_sha256 : String := '
    r'"(?P<hash>[0-9a-f]{64})"$', re.MULTILINE)


def lean_presentations(text):
    """The presentation literals and recorded hashes of a generated module.

    Maps each name to ``{"n", "checks", "recorded"}``. This reader shares
    no code with the emitter beyond the literal's layout, which it matches
    strictly: a literal it cannot read is absent from the result.
    """
    recorded = {m.group("name"): m.group("hash")
                for m in _RECORDED.finditer(text)}
    found = {}
    for match in _PRESENTATION.finditer(text):
        name = match.group("name")
        found[name] = {
            "n": int(match.group("n")),
            "checks": {side: json.loads(match.group(side))
                       for side in SECTORS},
            "recorded": recorded.get(name),
        }
    return found


def binding_failures(text, name, document):
    """Why the Lean module ``text`` does not bind ``name`` to ``document``.

    Empty when the presentation literal of ``name`` hashes to the recorded
    hash and to the hash of ``document``, its ``n`` is the document's, and
    the module states ``<name>_binds``. That the theorem holds is checked
    by `lake build`, not here.
    """
    entry = lean_presentations(text).get(name)
    if entry is None:
        return ["no presentation literal for %s" % name]
    failures = []
    literal = checks_sha256(entry)
    if entry["recorded"] is None:
        failures.append("no recorded hash for %s" % name)
    elif entry["recorded"] != literal:
        failures.append("recorded hash %s is not the literal's hash %s"
                        % (entry["recorded"], literal))
    source = checks_sha256(document)
    if literal != source:
        failures.append("literal hash %s is not the source hash %s"
                        % (literal, source))
    if entry["n"] != document.get("n"):
        failures.append("literal n = %d is not the source n = %r"
                        % (entry["n"], document.get("n")))
    theorem = ("theorem %s_binds :\n    presentationBinds %s %s_presentation "
               "%s_span = true := by decide" % (name, name, name, name))
    if theorem not in text:
        failures.append("the module does not state %s_binds" % name)
    return failures



# Size limits for generated Lean modules (issue #653). The measurements
# behind them are in `machine/experiments/benchmark_formal_cert.py`.
#
# `<name>_wellFormed` is decided by enumerating, for each retained row, every
# combination of the other rows of its sector, so its kernel cost grows as
# rows * 2^rows. It is emitted only up to this many retained rows in the
# larger sector.
LEAN_WELL_FORMEDNESS_ROW_LIMIT = 8
# Above this many qubits the generator refuses unless asked not to. The
# certificate theorems are checked by kernel evaluation of a tree that grows
# with n and the bound; 42 qubits is the largest size whose module has been
# built here, and a 48-qubit module at bound 8 did not finish.
LEAN_GENERATION_QUBIT_LIMIT = 42


def retained_rows(state):
    """The number of retained rows in the larger sector of ``state``."""
    return max(len(state.sector_rows(side)) for side in SECTORS)


def well_formedness_feasible(state):
    """Whether `<name>_wellFormed` is emitted for ``state`` by default."""
    return retained_rows(state) <= LEAN_WELL_FORMEDNESS_ROW_LIMIT


def lean_certified_block(name, bounds, exact):
    """The theorem ``<name>_certified`` a challenge certificate names.

    One conjunction of ``<name>_binds`` and, for each sector of ``bounds``
    (a mapping from ``"X"``/``"Z"`` to the certified bound), the sector's
    ``_exact`` theorem when the sector is in ``exact`` and its
    ``_lower_bound`` theorem otherwise. The conjuncts are the theorems
    `lean_ingestion_block` and `machine.certificates.lean_tree_instance_block`
    emit under the same ``name``, so one name states the whole payload.
    """
    if not LEAN_NAME.match(name):
        raise ValueError("not a usable Lean name: %r" % (name,))
    statements = ["presentationBinds %s %s_presentation %s_span = true"
                  % (name, name, name)]
    proofs = ["%s_binds" % name]
    for side in SECTORS:
        if side not in bounds:
            continue
        sigma = LEAN_SECTOR[side]
        if side in exact:
            statements.append("exactDistance? %s %s = some %d"
                              % (sigma, name, bounds[side]))
            proofs.append("%s_%s_exact" % (name, side))
        else:
            statements.append("(∀ d : Nat, exactDistance? %s %s = some d → "
                              "%d ≤ d)" % (sigma, name, bounds[side]))
            proofs.append("%s_%s_lower_bound" % (name, side))
    lines = ["theorem %s_certified :" % name]
    lines += ["    %s%s" % (statement, " ∧" if index < len(statements) - 1
                             else " :=")
              for index, statement in enumerate(statements)]
    lines.append("  ⟨%s⟩" % ", ".join(proofs))
    return "\n".join(lines)
