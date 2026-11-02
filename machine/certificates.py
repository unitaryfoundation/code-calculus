"""Certificate format and checker prototype for sector distance lower bounds.

This module is the first branch of the certificate layer explored in
`the archived notes` (option (ii), opened 2026-10-25). It makes the *lower* endpoint of a sector distance checkable the
same way the upper endpoint already is: an untrusted producer emits a
self-contained artifact, and a small total checker accepts or rejects it
without searching.

The fact certified. For a presented CSS state with qubit set ``Q`` and
displayed rows, a sigma-type logical operator is a vector that commutes with
every displayed row of the opposite sector and lies outside the span of the
displayed sigma-sector rows. The sector distance ``d_sigma`` is the minimum
weight of a sigma-type logical. A certificate for the fact
``d_sigma >= L`` lists, for **every** vector of weight < ``L`` over ``Q``,
a checkable reason it is not a sigma-type logical:

* ``odd_overlap`` -- the vector has odd overlap with a named displayed
  opposite-sector row, so it does not commute with that row; or
* ``in_span`` -- the vector is the XOR of a named 0/1 combination of the
  displayed sigma-sector rows, so it lies in the stabilizer span.

If the checker accepts, every low-weight vector is excluded, so
``d_sigma >= L`` holds. The checker is the trusted base; the producer is
arbitrary and untrusted, exactly as for the ledger's logical witnesses.

Checker contract (`the archived notes` section 4):

1. Total and decidable: a pure predicate over a finite input; it returns
   accept/reject with reasons and never raises on malformed input.
2. No search: it enumerates the certificate's own coverage obligation --
   the ball of supports of weight < ``L``, of size sum C(n, w) for w < L --
   and never searches for a logical operator or a minimum.
3. Self-contained: the certificate carries the state it speaks about
   (qubit labels and displayed row supports); nothing is read from the
   producer's environment.
4. Small trusted base: it reuses the consumer's ``support_mask`` and the
   CSS orthogonality and membership checks the witness validator already
   performs; it adds only the certificate's syntax and the coverage
   condition. Full I1--I5 is not re-checked here because the certified
   fact needs membership and orthogonality, not independence or rank;
   whether the mechanized checker should verify more is plan section 9
   question 3, left open.
5. Per-state scope: one certificate certifies one fact about one state. It
   never certifies an operation contract (second-pass S7).

Status discipline: nothing here changes a claim status. Every fact a
certificate supports stays ``conditional`` exactly as before, and the
reserved ``certificate-checked`` status (`spec/CLAIMS.md`) is untouched --
adopting it is a later release decision (plan section 5, step 3).
"""

import itertools
import json

from machine.priced_calculus import support_mask

SECTOR_LOWER_BOUND_KIND = "css-sector-distance-lower-bound"
CERTIFICATE_FORMAT_VERSION = 1

SECTORS = ("X", "Z")


class NoCertificate(Exception):
    """The producer cannot certify the requested fact.

    Raised when some low-weight vector survives every kill reason, which
    means the requested bound is not certifiable by this producer. The
    checker never sees this exception: a failed production is simply no
    certificate.
    """


def certificate_state_block(state):
    """The certificate's self-contained state block for a ``CodeState``.

    Qubit labels and displayed row supports by sector; identifiers and the
    ``used`` set are not part of the certified fact.
    """
    return {
        "qubits": sorted(state.Q),
        "rows": {
            sector: [sorted(row.support) for row in state.sector_rows(sector)]
            for sector in SECTORS
        },
    }


def _row_space_basis(row_masks):
    """A pivot-indexed F2 basis of ``row_masks``, carrying row coefficients.

    Each basis entry maps a pivot bit to ``(reduced_mask, coefficient_mask)``
    where the coefficient mask records, as a bitmask over row indices, which
    input rows combine into the reduced mask. Reused by the producer to name
    span witnesses; the checker does not call it.
    """
    basis = {}
    for index, mask in enumerate(row_masks):
        value, coefficients = mask, 1 << index
        while value:
            pivot = value.bit_length() - 1
            if pivot in basis:
                reduced, reduced_coefficients = basis[pivot]
                value ^= reduced
                coefficients ^= reduced_coefficients
            else:
                basis[pivot] = (value, coefficients)
                break
    return basis


def _span_coefficients(target, basis):
    """A 0/1 combination of rows equal to ``target``, or ``None``.

    Returns an integer bitmask over row indices when ``target`` lies in the
    span the basis was built from.
    """
    value, coefficients = target, 0
    while value:
        pivot = value.bit_length() - 1
        if pivot not in basis:
            return None
        reduced, reduced_coefficients = basis[pivot]
        value ^= reduced
        coefficients ^= reduced_coefficients
    return coefficients


def build_sector_lower_bound_certificate(state, sector, bound):
    """Produce a certificate for ``d_sector >= bound``, or raise.

    The producer is the untrusted side of the plan's section 2 pattern: it
    may search as hard as it likes (here, an exhaustive scan of the ball of
    supports of weight < ``bound``, the same shape the replay's post-hoc
    oracle uses), and its output is only as good as the checker's verdict.
    Raises ``NoCertificate`` when some low-weight vector survives every
    kill reason.
    """
    if sector not in SECTORS:
        raise ValueError("sector must be X or Z")
    if not isinstance(bound, int) or isinstance(bound, bool) or bound < 0:
        raise ValueError("bound must be a nonnegative integer")
    opposite = "Z" if sector == "X" else "X"
    state_block = certificate_state_block(state)
    same_masks = [support_mask(support)
                  for support in state_block["rows"][sector]]
    opposite_masks = [(row.mask, sorted(row.support))
                      for row in state.sector_rows(opposite)]
    basis = _row_space_basis(same_masks)
    kills = []
    for weight in range(bound):
        for support in itertools.combinations(state.Q, weight):
            vector = support_mask(support)
            reason = None
            for row_mask, row_support in opposite_masks:
                if bin(vector & row_mask).count("1") % 2 == 1:
                    reason = {
                        "kind": "odd_overlap",
                        "row_sector": opposite,
                        "row": row_support,
                    }
                    break
            if reason is None:
                coefficients = _span_coefficients(vector, basis)
                if coefficients is None:
                    raise NoCertificate(
                        "vector of weight %d over %r is neither "
                        "non-commuting nor in the %s-sector span; "
                        "d_%s >= %d is not certifiable by this producer"
                        % (weight, list(support), sector, sector, bound))
                reason = {
                    "kind": "in_span",
                    "coeffs": [(coefficients >> index) & 1
                               for index in range(len(same_masks))],
                }
            kills.append({"support": sorted(support), "reason": reason})
    return {
        "kind": SECTOR_LOWER_BOUND_KIND,
        "format_version": CERTIFICATE_FORMAT_VERSION,
        "sector": sector,
        "bound": bound,
        "state": state_block,
        "kills": kills,
    }


def certificate_size_bytes(certificate):
    """The artifact's size, as the bytes of its canonical JSON rendering."""
    return len(json.dumps(certificate, sort_keys=True).encode("utf-8"))


def _fail(failures, message):
    failures.append(message)
    return False


def _check_shape(certificate, failures):
    """The certificate's own syntax; every failure is reported, not raised."""
    if not isinstance(certificate, dict):
        return _fail(failures, "certificate is not an object")
    if certificate.get("kind") != SECTOR_LOWER_BOUND_KIND:
        return _fail(failures, "unknown certificate kind: %r"
                     % (certificate.get("kind"),))
    if certificate.get("format_version") != CERTIFICATE_FORMAT_VERSION:
        return _fail(failures, "unsupported format_version: %r"
                     % (certificate.get("format_version"),))
    if certificate.get("sector") not in SECTORS:
        return _fail(failures, "sector must be 'X' or 'Z', got %r"
                     % (certificate.get("sector"),))
    bound = certificate.get("bound")
    if not isinstance(bound, int) or isinstance(bound, bool) or bound < 0:
        return _fail(failures, "bound must be a nonnegative integer, got %r"
                     % (bound,))
    state_block_for_bound = certificate.get("state")
    if isinstance(state_block_for_bound, dict):
        qubits_for_bound = state_block_for_bound.get("qubits")
        if (isinstance(qubits_for_bound, list)
                and all(isinstance(q, int) and not isinstance(q, bool)
                        for q in qubits_for_bound)):
            if bound > len(qubits_for_bound) + 1:
                return _fail(failures,
                             "bound %d exceeds the trivial maximum %d for %d "
                             "qubits" % (bound, len(qubits_for_bound) + 1,
                                         len(qubits_for_bound)))
    state_block = certificate.get("state")
    if not isinstance(state_block, dict):
        return _fail(failures, "state must be an object")
    qubits = state_block.get("qubits")
    if (not isinstance(qubits, list)
            or not all(isinstance(q, int) and not isinstance(q, bool) and q >= 0
                       for q in qubits)
            or len(set(qubits)) != len(qubits)):
        return _fail(failures, "state.qubits must be unique nonnegative ints")
    rows = state_block.get("rows")
    if not isinstance(rows, dict) or set(rows) != set(SECTORS):
        return _fail(failures, "state.rows must have exactly 'X' and 'Z' lists")
    qubit_set = set(qubits)
    for sector in SECTORS:
        if not isinstance(rows.get(sector), list):
            return _fail(failures, "state.rows[%r] must be a list" % sector)
        for row_support in rows[sector]:
            if (not isinstance(row_support, list)
                    or not all(isinstance(q, int) and not isinstance(q, bool)
                               for q in row_support)
                    or len(set(row_support)) != len(row_support)
                    or not set(row_support) <= qubit_set):
                return _fail(failures,
                             "state.rows[%r] entries must be repeat-free "
                             "support lists over the state's qubits" % sector)
    if not isinstance(certificate.get("kills"), list):
        return _fail(failures, "kills must be a list")
    return True


def _check_kill_reason(kill, sector, vector, row_masks, opposite_rows,
                       failures, label):
    """One kill entry's reason, re-derived by finite-field arithmetic."""
    reason = kill.get("reason") if isinstance(kill, dict) else None
    if not isinstance(reason, dict):
        return _fail(failures, "%s: kill reason must be an object" % label)
    kind = reason.get("kind")
    if kind == "odd_overlap":
        row_support = reason.get("row")
        if (not isinstance(row_support, list)
                or not all(isinstance(q, int) and not isinstance(q, bool)
                           for q in row_support)
                or reason.get("row_sector") != ("Z" if sector == "X" else "X")):
            return _fail(failures, "%s: odd_overlap must name an opposite-"
                         "sector row" % label)
        if tuple(sorted(row_support)) not in opposite_rows:
            return _fail(failures, "%s: odd_overlap row %r is not a displayed "
                         "%s-sector row" % (label, row_support,
                                            reason.get("row_sector")))
        row_mask = support_mask(sorted(row_support))
        if bin(vector & row_mask).count("1") % 2 != 1:
            return _fail(failures, "%s: overlap with the named row is even"
                         % label)
        return True
    if kind == "in_span":
        coeffs = reason.get("coeffs")
        if (not isinstance(coeffs, list)
                or len(coeffs) != len(row_masks)
                or not all(isinstance(c, int) and not isinstance(c, bool) and c in (0, 1) for c in coeffs)):
            return _fail(failures, "%s: in_span coeffs must be a 0/1 list over "
                         "the %d displayed %s-sector rows"
                         % (label, len(row_masks), sector))
        combination = 0
        for index, coefficient in enumerate(coeffs):
            if coefficient:
                combination ^= row_masks[index]
        if combination != vector:
            return _fail(failures, "%s: the named combination does not equal "
                         "the vector" % label)
        return True
    return _fail(failures, "%s: unknown kill reason kind: %r" % (label, kind))


def check_sector_lower_bound_certificate(certificate):
    """Check a certificate. Returns ``(accepted, failures)``; never raises.

    The checker validates the certificate's syntax, the CSS orthogonality of
    the carried state, and -- by enumerating the ball of supports of weight
    < ``bound`` over the state's qubits -- that every low-weight vector
    carries a valid kill reason. That enumeration is the certificate's own
    coverage obligation (bounded by sum C(n, w) for w < bound); the checker
    performs no other search and never touches a producer environment.
    """
    failures = []
    if not _check_shape(certificate, failures):
        return False, failures
    state_block = certificate["state"]
    qubits = sorted(state_block["qubits"])
    sector = certificate["sector"]
    bound = certificate["bound"]
    rows = state_block["rows"]
    row_masks = {name: [support_mask(sorted(support)) for support in rows[name]]
                 for name in SECTORS}
    # The certified fact presupposes a CSS display: every X row commutes
    # with every Z row. This is the same orthogonality the witness
    # validator relies on (I1's algebraic content), re-derived here so the
    # certificate is self-contained.
    for x_index, x_mask in enumerate(row_masks["X"]):
        for z_index, z_mask in enumerate(row_masks["Z"]):
            if bin(x_mask & z_mask).count("1") % 2 != 0:
                failures.append(
                    "state is not CSS: X row %d and Z row %d anticommute"
                    % (x_index, z_index))
    if failures:
        return False, failures
    opposite_rows = {tuple(sorted(support)) for support in rows[
        "Z" if sector == "X" else "X"]}
    kills = {}
    for position, kill in enumerate(certificate["kills"]):
        if not isinstance(kill, dict) or "support" not in kill:
            failures.append("kill %d: missing support" % position)
            continue
        support = kill["support"]
        if (not isinstance(support, list)
                or not all(isinstance(q, int) and not isinstance(q, bool)
                           for q in support)
                or len(set(support)) != len(support)
                or not set(support) <= set(qubits)):
            failures.append("kill %d: support must be a repeat-free list over "
                            "the state's qubits" % position)
            continue
        kills.setdefault(tuple(sorted(support)), []).append((position, kill))
    for weight in range(bound):
        for support in itertools.combinations(qubits, weight):
            key = tuple(sorted(support))
            vector = support_mask(key)
            entries = kills.pop(key, None)
            if not entries:
                failures.append("coverage: no kill for support %r (weight %d)"
                                % (list(key), weight))
                continue
            for position, kill in entries:
                _check_kill_reason(
                    kill, sector, vector, row_masks[sector], opposite_rows,
                    failures, "kill %d" % position)
    if kills:
        failures.append("%d kill entries cover no vector of weight < %d"
                        % (len(kills), bound))
    return not failures, failures