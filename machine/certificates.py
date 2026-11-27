"""Certificate format and checker prototype for sector distance lower bounds.

This module is the first branch of the certificate layer explored in
`the archived notes` (option (ii), opened,
2026-10-25). It makes the *lower* endpoint of a sector distance checkable the
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
   never certifies an operation contract (a second review pass).

A second format, the pruning tree, covers the ball by classes of vectors
and is described at ``SECTOR_LOWER_BOUND_TREE_KIND`` below. Its checker
walks the tree once and enumerates nothing. Points 1 and 3 to 5 of the
contract hold for it unchanged.

Status discipline: nothing this module's checker accepts changes a claim
status. It is the prototype, and every fact it supports stays
``conditional``. The mechanized checker is
`lean/CodeCalculus/CertificateChecker.lean`, whose acceptance is
proved to imply the certified fact for the exact sector distance. The
``lean_*`` functions at the end of this module translate a state and a
certificate into Lean source for that checker. The translation is untrusted:
the status ``certificate-checked`` (`spec/CLAIMS.md`, *Admission*) attaches
to the theorem the Lean kernel accepts, which is a statement about the Lean
state term in the emitted source, and to nothing this module returns.
"""

import itertools
import json

from machine.priced_calculus import (
    CodeState,
    Malformed,
    identifier_rank,
    in_span,
    support_mask,
)

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
                if (vector & row_mask).bit_count() % 2 == 1:
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
        if (vector & row_mask).bit_count() % 2 != 1:
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
            if (x_mask & z_mask).bit_count() % 2 != 0:
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

# ---------------------------------------------------------------------------
# Translation to the mechanized checker
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# Pruning-tree certificates (issue #574)
#
# The kill list names every vector of weight below the bound, so it grows
# with the ball: sum C(n, w) for w < L. A pruning tree covers the same
# vectors by classes. A class fixes some qubits to 1 (``ones``) and some to
# 0 (``zeros``) and contains every vector that agrees with both. The root
# class fixes nothing. A leaf closes its class with one reason, and a
# branch splits a class on one qubit.
#
#   ["bound"]                 at least ``bound`` qubits are fixed to 1
#   ["need_more", r]          opposite-sector row r has odd overlap with
#                             ``ones``, so a commuting vector has a further
#                             1, and one more reaches the bound
#   ["conflict", r]           opposite-sector row r has odd overlap with
#                             ``ones`` and every qubit of r is fixed
#   ["in_span", coeffs]       every qubit is fixed, so the class is the one
#                             vector ``ones``, and it is the 0/1 combination
#                             ``coeffs`` of the sector's rows
#   ["branch", q, one, zero]  ``one`` closes the class with q fixed to 1,
#                             ``zero`` the class with q fixed to 0
#
# ``r`` indexes ``state["rows"][opposite]`` and ``coeffs`` runs over
# ``state["rows"][sector]``, both in the order the state block lists them.
# ``q`` is a qubit label. The tree is nested lists, so it is JSON as it
# stands.
#
# The mechanized checker is ``checkPruneCertificate`` in
# `lean/CodeCalculus/CertificateChecker.lean`, proved to imply the bound for
# the exact sector distance. The checker below is its prototype. No
# symmetry of the code is used: two classes related by an automorphism are
# both in the tree.
# ---------------------------------------------------------------------------

SECTOR_LOWER_BOUND_TREE_KIND = "css-sector-distance-lower-bound-tree"
TREE_NODE_KINDS = ("bound", "need_more", "conflict", "in_span", "branch")


def _chain(qubits, ones, zeros, weight, close, tail):
    """Branch on each of ``qubits`` in turn, then ``tail``.

    The ``i``-th branch fixes ``qubits[i]`` to 1 with the earlier ones fixed
    to 0, which is the class of vectors whose first 1 among ``qubits`` is at
    ``qubits[i]``. ``tail`` closes the class with all of them fixed to 0.
    """
    classes = []
    for qubit in qubits:
        classes.append((qubit, ones | (1 << qubit), zeros))
        zeros |= 1 << qubit
    tree = tail
    for qubit, child_ones, child_zeros in reversed(classes):
        tree = ["branch", qubit, close(child_ones, child_zeros, weight + 1),
                tree]
    return tree


def build_sector_lower_bound_tree_certificate(state, sector, bound):
    """Produce a pruning-tree certificate for ``d_sector >= bound``, or raise.

    The search is driven by the syndrome. In a class whose fixed 1s have
    odd overlap with some opposite-sector row, a commuting vector has a
    further 1 on that row, so the producer branches on the free qubits of
    the row with the fewest of them. In a class whose fixed 1s commute with
    every opposite-sector row, the vector of the fixed 1s must be in the
    sector's span (otherwise it is a logical below the bound, and
    ``NoCertificate`` is raised), and the producer branches on every free
    qubit. The producer is untrusted and deterministic.
    """
    if sector not in SECTORS:
        raise ValueError("sector must be X or Z")
    if not isinstance(bound, int) or isinstance(bound, bool) or bound < 0:
        raise ValueError("bound must be a nonnegative integer")
    opposite = "Z" if sector == "X" else "X"
    state_block = certificate_state_block(state)
    qubits = state_block["qubits"]
    same_masks = [support_mask(support)
                  for support in state_block["rows"][sector]]
    opposite_masks = [support_mask(support)
                      for support in state_block["rows"][opposite]]
    basis = _row_space_basis(same_masks)

    def close(ones, zeros, weight):
        if weight >= bound:
            return ["bound"]
        fixed = ones | zeros
        chosen = None
        for index, row in enumerate(opposite_masks):
            if (row & ones).bit_count() % 2 == 0:
                continue
            free = row & ~fixed
            if free == 0:
                return ["conflict", index]
            if weight + 1 >= bound:
                return ["need_more", index]
            if chosen is None or free.bit_count() < chosen[0]:
                chosen = (free.bit_count(), index, free)
        if chosen is not None:
            _, index, free = chosen
            return _chain([q for q in qubits if (free >> q) & 1], ones, zeros,
                          weight, close, ["conflict", index])
        coefficients = _span_coefficients(ones, basis)
        if coefficients is None:
            raise NoCertificate(
                "the vector on %r commutes with every %s-row and is outside "
                "the %s-sector span; d_%s >= %d is not certifiable"
                % ([q for q in qubits if (ones >> q) & 1], opposite, sector,
                   sector, bound))
        leaf = ["in_span", [(coefficients >> index) & 1
                            for index in range(len(same_masks))]]
        return _chain([q for q in qubits if not (fixed >> q) & 1], ones,
                      zeros, weight, close, leaf)

    return {
        "kind": SECTOR_LOWER_BOUND_TREE_KIND,
        "format_version": CERTIFICATE_FORMAT_VERSION,
        "sector": sector,
        "bound": bound,
        "state": state_block,
        "tree": close(0, 0, 0),
    }


def tree_node_counts(tree):
    """The number of nodes of each kind in a pruning tree."""
    counts = {kind: 0 for kind in TREE_NODE_KINDS}
    stack = [tree]
    while stack:
        node = stack.pop()
        counts[node[0]] += 1
        if node[0] == "branch":
            stack += [node[2], node[3]]
    return counts


def _is_index(value, size):
    return (isinstance(value, int) and not isinstance(value, bool)
            and 0 <= value < size)


def check_sector_lower_bound_tree_certificate(certificate):
    """Check a pruning-tree certificate. Returns ``(accepted, failures)``.

    Never raises. The checker walks the tree once, carrying the two masks
    of the class, and tests each leaf's reason by finite-field arithmetic.
    It searches for nothing. It also rejects a non-CSS display and a branch
    on a qubit that is already fixed or is not a qubit of the state, which
    the mechanized checker does not need for soundness.
    """
    failures = []
    if not isinstance(certificate, dict):
        return _fail(failures, "certificate must be an object"), failures
    if certificate.get("kind") != SECTOR_LOWER_BOUND_TREE_KIND:
        _fail(failures, "kind must be %r" % SECTOR_LOWER_BOUND_TREE_KIND)
    if certificate.get("format_version") != CERTIFICATE_FORMAT_VERSION:
        _fail(failures, "unsupported format_version")
    sector = certificate.get("sector")
    if sector not in SECTORS:
        _fail(failures, "sector must be X or Z")
    bound = certificate.get("bound")
    if not isinstance(bound, int) or isinstance(bound, bool) or bound < 0:
        _fail(failures, "bound must be a nonnegative integer")
    state_block = certificate.get("state")
    rows = state_block.get("rows") if isinstance(state_block, dict) else None
    qubits = state_block.get("qubits") if isinstance(state_block, dict) else None
    if (not isinstance(qubits, list)
            or not all(isinstance(q, int) and not isinstance(q, bool)
                       and q >= 0 for q in qubits)
            or len(set(qubits)) != len(qubits)):
        _fail(failures, "state.qubits must be a repeat-free list of "
                        "nonnegative integers")
        qubits = None
    if not isinstance(rows, dict) or set(rows) != set(SECTORS):
        _fail(failures, "state.rows must carry an X list and a Z list")
        rows = None
    elif qubits is not None:
        for name in SECTORS:
            if (not isinstance(rows[name], list) or not all(
                    isinstance(support, list)
                    and all(isinstance(q, int) and not isinstance(q, bool)
                            for q in support)
                    and len(set(support)) == len(support)
                    and set(support) <= set(qubits)
                    for support in rows[name])):
                _fail(failures, "state.rows.%s must list repeat-free "
                                "supports over the state's qubits" % name)
                rows = None
                break
    if failures:
        return False, failures
    row_masks = {name: [support_mask(sorted(support)) for support in rows[name]]
                 for name in SECTORS}
    for x_index, x_mask in enumerate(row_masks["X"]):
        for z_index, z_mask in enumerate(row_masks["Z"]):
            if (x_mask & z_mask).bit_count() % 2 != 0:
                failures.append(
                    "state is not CSS: X row %d and Z row %d anticommute"
                    % (x_index, z_index))
    if failures:
        return False, failures
    same = row_masks[sector]
    opposite = row_masks["Z" if sector == "X" else "X"]
    full = support_mask(sorted(qubits))
    stack = [(certificate.get("tree"), 0, 0, "root")]
    while stack:
        node, ones, zeros, path = stack.pop()
        if (not isinstance(node, list) or not node
                or node[0] not in TREE_NODE_KINDS):
            failures.append("%s: not a tree node" % path)
            continue
        kind = node[0]
        if kind == "bound":
            if len(node) != 1:
                failures.append("%s: malformed bound leaf" % path)
            elif ones.bit_count() < bound:
                failures.append("%s: %d qubits fixed to 1, below the bound"
                                % (path, ones.bit_count()))
        elif kind in ("need_more", "conflict"):
            if len(node) != 2 or not _is_index(node[1], len(opposite)):
                failures.append("%s: %s must name an opposite-sector row"
                                % (path, kind))
                continue
            row = opposite[node[1]]
            if (row & ones).bit_count() % 2 == 0:
                failures.append("%s: row %d has even overlap with the fixed "
                                "1s" % (path, node[1]))
            elif kind == "need_more" and ones.bit_count() + 1 < bound:
                failures.append("%s: one more qubit does not reach the bound"
                                % path)
            elif kind == "conflict" and row & ~(ones | zeros):
                failures.append("%s: row %d has a free qubit" % (path, node[1]))
        elif kind == "in_span":
            coeffs = node[1] if len(node) == 2 else None
            if (not isinstance(coeffs, list) or len(coeffs) != len(same)
                    or not all(c in (0, 1) and not isinstance(c, bool)
                               for c in coeffs)):
                failures.append("%s: in_span needs one 0/1 coefficient per "
                                "%s-row" % (path, sector))
                continue
            if (ones | zeros) != full:
                failures.append("%s: in_span with a free qubit" % path)
                continue
            combination = 0
            for coefficient, mask in zip(coeffs, same):
                if coefficient:
                    combination ^= mask
            if combination != ones:
                failures.append("%s: the combination is not the fixed vector"
                                % path)
        else:
            if (len(node) != 4 or not isinstance(node[1], int)
                    or isinstance(node[1], bool) or node[1] not in qubits):
                failures.append("%s: branch must name a qubit and two "
                                "subtrees" % path)
                continue
            bit = 1 << node[1]
            if (ones | zeros) & bit:
                failures.append("%s: qubit %d is already fixed"
                                % (path, node[1]))
                continue
            stack.append((node[3], ones, zeros | bit, path + ".0"))
            stack.append((node[2], ones | bit, zeros, path + ".1"))
    return not failures, failures


LEAN_SECTOR = {"X": "Sector.X", "Z": "Sector.Z"}


def _lean_nat_list(values):
    return "[%s]" % ", ".join(str(value) for value in values)


def _lean_bool_list(bits):
    return "[%s]" % ", ".join("true" if bit else "false" for bit in bits)


def lean_state_term(state):
    """A Lean ``CodeState`` literal for ``state``.

    Qubits in the state's order, rows in display order with sorted
    supports, and identifiers as their ranks in the fixed enumeration, the
    transcription `lean/CodeCalculus/Fixtures.lean` uses.
    """
    rows = ",\n".join(
        "    { id := %d, sector := %s, support := %s }"
        % (identifier_rank(row.id), LEAN_SECTOR[row.sector],
           _lean_nat_list(sorted(row.support)))
        for row in state.rows)
    used = _lean_nat_list(sorted(identifier_rank(i) for i in state.used))
    return ("{\n  Q := %s,\n  rows := [\n%s\n  ],\n  used := %s\n}"
            % (_lean_nat_list(state.Q), rows, used))


def lean_certificate_term(certificate):
    """A Lean ``SectorCertificate`` literal for a kill certificate."""
    kills = []
    for kill in certificate["kills"]:
        reason = kill["reason"]
        if reason["kind"] == "odd_overlap":
            rendered = "KillReason.oddOverlap %s" % _lean_nat_list(
                sorted(reason["row"]))
        elif reason["kind"] == "in_span":
            rendered = "KillReason.inSpan %s" % _lean_bool_list(
                reason["coeffs"])
        else:
            raise ValueError("unknown kill reason kind: %r" % (reason["kind"],))
        kills.append("    { support := %s, reason := %s }"
                     % (_lean_nat_list(sorted(kill["support"])), rendered))
    return ("{\n  sector := %s,\n  bound := %d,\n  kills := [\n%s\n  ]\n}"
            % (LEAN_SECTOR[certificate["sector"]], certificate["bound"],
               ",\n".join(kills)))


def _witness_failure(state, sector, bound, witness):
    """Why ``witness`` is not a weight-``bound`` sector logical, or ``None``."""
    support = tuple(sorted(witness))
    if len(set(support)) != len(support) or not set(support) <= set(state.Q):
        return "witness is not a repeat-free support over the state's qubits"
    if len(support) != bound:
        return "witness weight %d is not the bound %d" % (len(support), bound)
    vector = support_mask(support)
    opposite = "Z" if sector == "X" else "X"
    if any((vector & row.mask).bit_count() % 2
           for row in state.sector_rows(opposite)):
        return "witness anticommutes with a displayed %s row" % opposite
    if in_span(vector, [row.mask for row in state.sector_rows(sector)]):
        return "witness lies in the displayed %s-sector span" % sector
    return None


def lean_instance_block(name, state, certificate, witness=None):
    """Lean source for one per-state instance of the mechanized checker.

    Emits the state, the certificate, and the theorem
    ``<name>_<sector>_lower_bound`` that the checker's acceptance implies
    ``bound <= d_sector``. With ``witness`` (a support of weight ``bound``)
    it also emits ``<name>_<sector>_exact``. The acceptance premises are
    ``by decide``, so the kernel evaluates the checker; nothing emitted
    here is trusted.

    Raises ``ValueError`` when the certificate does not carry ``state``,
    when the prototype checker rejects it, or when the witness is not a
    logical of weight ``bound``. These refusals only fail early: an emitted
    module that should not have been emitted does not build.
    """
    if certificate.get("state") != certificate_state_block(state):
        raise ValueError("certificate does not carry the given state")
    accepted, failures = check_sector_lower_bound_certificate(certificate)
    if not accepted:
        raise ValueError("certificate rejected: %s" % "; ".join(failures))
    sector = certificate["sector"]
    bound = certificate["bound"]
    stem = "%s_%s" % (name, sector)
    lines = [
        "def %s_certificate : SectorCertificate := %s"
        % (stem, lean_certificate_term(certificate)),
        "",
        "theorem %s_lower_bound :" % stem,
        "    ExtNat.finite %d ≤ exactDistanceExt %s %s :="
        % (bound, LEAN_SECTOR[sector], name),
        "  certificate_lower_bound_ext %s %s_certificate (by decide)"
        % (name, stem),
    ]
    if witness is not None:
        failure = _witness_failure(state, sector, bound, witness)
        if failure is not None:
            raise ValueError(failure)
        vector = _lean_bool_list(q in set(witness) for q in state.Q)
        lines += [
            "",
            "theorem %s_exact :" % stem,
            "    exactDistance? %s %s = some %d :="
            % (LEAN_SECTOR[sector], name, bound),
            "  certificate_equality %s %s_certificate (by decide)"
            % (name, stem),
            "    %s (by decide)" % vector,
        ]
    return "\n".join(lines)


LEAN_TREE_WIDTH = 96


def lean_tree_term(tree, qubits):
    """A Lean ``PruneTree`` term, with qubit labels turned into positions.

    The constructors are written unqualified; the emitted definition opens
    ``PruneTree``. Tokens are packed into lines of about ``LEAN_TREE_WIDTH``
    columns.
    """
    position = {q: index for index, q in enumerate(qubits)}
    tokens = []
    stack = [tree]
    while stack:
        node = stack.pop()
        if isinstance(node, str):
            tokens.append(node)
            continue
        kind = node[0]
        if kind == "bound":
            tokens.append("bound")
        elif kind == "need_more":
            tokens.append("(needMore %d)" % node[1])
        elif kind == "conflict":
            tokens.append("(conflict %d)" % node[1])
        elif kind == "in_span":
            tokens.append("(inSpan %s)" % _lean_bool_list(node[1]))
        elif kind == "branch":
            tokens.append("(branch %d" % position[node[1]])
            stack += [")", node[3], node[2]]
        else:
            raise ValueError("unknown tree node kind: %r" % (kind,))
    lines, current = [], ""
    for token in tokens:
        if token == ")":
            current += token
            continue
        if current and len(current) + 1 + len(token) > LEAN_TREE_WIDTH:
            lines.append(current)
            current = token
        else:
            current = (current + " " + token) if current else token
    lines.append(current)
    return "\n".join("    " + line for line in lines)


def _lean_matrix(state, sector):
    members = set()
    rows = []
    for row in state.sector_rows(sector):
        members = set(row.support)
        rows.append("    " + _lean_bool_list(q in members for q in state.Q))
    return "[\n%s\n  ]" % ",\n".join(rows) if rows else "[]"


def lean_tree_instance_block(name, state, certificate, witness=None):
    """Lean source for one pruning-tree instance of the mechanized checker.

    Emits ``<name>_<sector>_tree``, the certificate
    ``<name>_<sector>_prune`` carrying the two row matrices as literals,
    and the theorem ``<name>_<sector>_lower_bound``. With ``witness`` it
    also emits ``<name>_<sector>_witness`` and ``<name>_<sector>_exact``.
    The acceptance premises are separate theorems proved by
    ``decide +kernel``: the kernel evaluates the checker, and no axiom is
    added. Refusals are those of `lean_instance_block`.
    """
    if certificate.get("state") != certificate_state_block(state):
        raise ValueError("certificate does not carry the given state")
    accepted, failures = check_sector_lower_bound_tree_certificate(certificate)
    if not accepted:
        raise ValueError("certificate rejected: %s" % "; ".join(failures))
    sector = certificate["sector"]
    opposite = "Z" if sector == "X" else "X"
    bound = certificate["bound"]
    stem = "%s_%s" % (name, sector)
    sigma = LEAN_SECTOR[sector]
    lines = [
        "open PruneTree in",
        "def %s_tree : PruneTree :=" % stem,
        lean_tree_term(certificate["tree"], list(state.Q)),
        "",
        "def %s_prune : PruneCertificate := {" % stem,
        "  opp := %s," % _lean_matrix(state, opposite),
        "  same := %s," % _lean_matrix(state, sector),
        "  tree := %s_tree" % stem,
        "}",
        "",
        "set_option maxRecDepth 1000000 in",
        "theorem %s_accepts :" % stem,
        "    checkPruneCertificate %s %s %d %s_prune = true := by "
        "decide +kernel" % (name, sigma, bound, stem),
        "",
        "theorem %s_lower_bound :" % stem,
        "    ∀ d : Nat, exactDistance? %s %s = some d → %d ≤ d :="
        % (sigma, name, bound),
        "  pruneCertificate_lower_bound %s %s %d %s_prune %s_accepts"
        % (name, sigma, bound, stem, stem),
    ]
    if witness is not None:
        failure = _witness_failure(state, sector, bound, witness)
        if failure is not None:
            raise ValueError(failure)
        vector = _lean_bool_list(q in set(witness) for q in state.Q)
        lines += [
            "",
            "set_option maxRecDepth 1000000 in",
            "theorem %s_witness :" % stem,
            "    witnessValid %s %s %d" % (name, sigma, bound),
            "      %s = true := by decide +kernel" % vector,
            "",
            "theorem %s_exact :" % stem,
            "    exactDistance? %s %s = some %d :=" % (sigma, name, bound),
            "  pruneCertificate_equality %s %s %d %s_prune %s_accepts _ "
            "%s_witness" % (name, sigma, bound, stem, stem, stem),
        ]
    return "\n".join(lines)


def lean_instance_module(header, states, blocks, same_as=None,
                         namespace="CertificateInstances",
                         without_well_formedness=()):
    """A Lean module from state definitions and instance blocks.

    ``states`` maps a Lean name to a ``CodeState``; ``blocks`` are the
    strings `lean_instance_block` returns for those names. Each state gets
    a theorem ``<name>_wellFormed`` that the Lean term is a well-formed
    state, by kernel evaluation of ``wellFormedBool``. ``same_as`` maps a
    state name to an existing Lean constant the term must equal. The names
    in ``without_well_formedness`` get no ``_wellFormed`` theorem: the
    independence test of ``wellFormedBool`` enumerates every combination of
    a sector's rows, which is too slow in the kernel for a state with many
    rows, and the checker theorems do not use well-formedness.
    """
    parts = [
        "import CodeCalculus.CertificateChecker",
        "import CodeCalculus.WellFormedBool",
        "",
        "/-!\n%s\n-/" % header.strip(),
        "",
        "namespace CodeCalculus.%s" % namespace,
    ]
    for name, state in states.items():
        parts += [
            "",
            "def %s : CodeState := %s" % (name, lean_state_term(state)),
        ]
        if name not in without_well_formedness:
            parts += [
                "",
                "theorem %s_wellFormed : EncodingWellFormed %s :="
                % (name, name),
                "  encodingWellFormed_of_bool (by decide)",
            ]
        if same_as and name in same_as:
            parts += [
                "",
                "theorem %s_eq_%s : %s = %s := by decide"
                % (name, same_as[name], name, same_as[name]),
            ]
    for block in blocks:
        parts += ["", block]
    parts += ["", "end CodeCalculus.%s" % namespace, ""]
    return "\n".join(parts)


# The ``replay`` keys qldpc-challenge's ``cert.schema.json`` allows at level
# ``formal``; ``repo``, ``commit`` and ``theorem`` are required there.
CHALLENGE_REPLAY_KEYS = ("repo", "commit", "theorem", "build", "toolchain",
                         "mathlib")
CHALLENGE_REPLAY_REQUIRED = ("repo", "commit", "theorem")


def _positive_int(value):
    return isinstance(value, int) and not isinstance(value, bool) and value >= 1


def _nonempty_str(value):
    return isinstance(value, str) and value.strip() != ""


def export_challenge_certificate(document, state, certificates, *, d,
                                 d_exact, solver, checker, replay,
                                 witnesses=None, name=None, reference=None,
                                 note=None):
    """The qldpc-challenge ``certs/<slug>.json`` payload for Lean-checked bounds.

    ``document`` is the board entry the bounds are about and ``state`` its
    ingested state (`machine.ingestion.ingest`); ``certificates`` maps
    ``"X"`` and ``"Z"`` to sector lower-bound certificates (kill or
    pruning-tree) carrying that state. ``witnesses`` optionally maps a
    sector to a logical support. ``d`` is the claimed distance and
    ``d_exact`` says whether the payload is exact or partial. ``replay``
    carries the ``formal`` replay recipe (``repo``, ``commit`` and
    ``theorem`` required; ``build``, ``toolchain`` and ``mathlib``
    optional) and ``checker`` the tool that checked it. Every one of these
    is the caller's: nothing is defaulted, because a default names a proof
    nobody checked.

    The payload is at level ``formal``, the level a kernel-checked
    certificate earns, and its ``checks_sha256`` is the hash of
    ``document`` (`machine.ingestion.checks_sha256`), not of the retained
    rows, so a redundant presentation binds to its entry.

    Refused with ``ValueError``: a ``state`` that is not the ingestion of
    ``document``; a missing sector, or a certificate the prototype checker
    rejects or that carries another state; a witness that is not a logical
    of the sector, or is lighter than the sector's proven bound or than
    ``d``; a partial payload whose ``d_lower`` (the least proven bound) is
    not in ``2 .. d - 1``; an exact payload whose ``d_lower`` is not ``d``
    or with no witness of weight ``d``; and a ``replay`` or ``checker``
    that is not of the schema's shape.

    On an exact payload each side's ``proved_min`` is ``d``, as the board
    requires; a side proved above ``d`` (an asymmetric code) says so in its
    ``note``. A side's ``value`` is its witness weight and is absent when
    there is no witness. This function checks shape and consistency; the
    theorem named in ``replay`` is checked by building it, not here.
    """
    from machine.ingestion import checks_sha256, ingest

    if not isinstance(state, CodeState):
        raise ValueError("state must be a CodeState")
    try:
        ingested = ingest(document)
    except Malformed as exc:
        raise ValueError("document is not a CSS presentation: %s" % exc)
    if certificate_state_block(ingested) != certificate_state_block(state):
        raise ValueError("state is not the ingestion of document")
    if not isinstance(certificates, dict) or set(certificates) != set(SECTORS):
        raise ValueError("certificates must map exactly X and Z to a "
                         "certificate; a bound on one side bounds nothing")
    witnesses = {} if witnesses is None else witnesses
    if not isinstance(witnesses, dict) or not set(witnesses) <= set(SECTORS):
        raise ValueError("witnesses must map X and/or Z to a support")
    if not _positive_int(d):
        raise ValueError("d must be a positive integer")
    if not isinstance(d_exact, bool):
        raise ValueError("d_exact must be a boolean")
    for label, value in (("solver", solver), ("checker", checker)):
        if not _nonempty_str(value):
            raise ValueError("%s must be a nonempty string" % label)
    if not isinstance(replay, dict):
        raise ValueError("replay must be a mapping")
    unknown = sorted(set(replay) - set(CHALLENGE_REPLAY_KEYS))
    if unknown:
        raise ValueError("replay keys %s are not in the formal schema"
                         % ", ".join(unknown))
    for key in CHALLENGE_REPLAY_REQUIRED:
        if not _nonempty_str(replay.get(key)):
            raise ValueError("replay.%s must be a nonempty string" % key)
    for key, value in replay.items():
        if not _nonempty_str(value):
            raise ValueError("replay.%s must be a nonempty string" % key)

    block = certificate_state_block(state)
    proved, weights = {}, {}
    for side in SECTORS:
        certificate = certificates[side]
        if not isinstance(certificate, dict) or certificate.get("sector") != side:
            raise ValueError("the %s certificate is not an %s-sector certificate"
                             % (side, side))
        if certificate.get("state") != block:
            raise ValueError("the %s certificate does not carry the state" % side)
        if certificate.get("kind") == SECTOR_LOWER_BOUND_TREE_KIND:
            accepted, failures = check_sector_lower_bound_tree_certificate(
                certificate)
        else:
            accepted, failures = check_sector_lower_bound_certificate(
                certificate)
        if not accepted:
            raise ValueError("the %s certificate is rejected: %s"
                             % (side, "; ".join(failures)))
        proved[side] = certificate["bound"]
        if side in witnesses:
            support = witnesses[side]
            if (not isinstance(support, (list, tuple)) or not support
                    or not all(isinstance(q, int) and not isinstance(q, bool)
                               for q in support)):
                raise ValueError("the %s witness must be a nonempty list of "
                                 "qubits" % side)
            failure = _witness_failure(state, side, len(support), support)
            if failure is not None:
                raise ValueError("the %s witness: %s" % (side, failure))
            weights[side] = len(support)
            if weights[side] < proved[side]:
                raise ValueError("the %s witness has weight %d, below the "
                                 "proven bound %d"
                                 % (side, weights[side], proved[side]))
            if weights[side] < d:
                raise ValueError("the %s witness has weight %d, below d = %d"
                                 % (side, weights[side], d))

    d_lower = min(proved.values())
    if d_exact:
        if d_lower != d:
            raise ValueError("an exact payload needs d_lower = d; the proven "
                             "bounds give %d, d is %d" % (d_lower, d))
        if d not in weights.values():
            raise ValueError("an exact payload needs a witness of weight "
                             "d = %d" % d)
    else:
        if d_lower < 2:
            raise ValueError("a partial payload needs d_lower >= 2; the proven "
                             "bounds give %d" % d_lower)
        if d_lower >= d:
            raise ValueError("a partial payload needs d_lower < d; the proven "
                             "bounds give %d and d is %d; with a witness of "
                             "weight d it is exact" % (d_lower, d))

    sides = {}
    for side in SECTORS:
        # A side is exact when its witness meets its proven bound at d.
        entry = {"proved_min": d if d_exact else proved[side],
                 "exact": weights.get(side) == proved[side] == d}
        if side in weights:
            entry["value"] = weights[side]
            entry["witness"] = sorted(witnesses[side])
        if d_exact and proved[side] > d:
            entry["note"] = ("d_%s >= %d is proved; an exact certificate "
                             "records proved_min = d" % (side, proved[side]))
        sides[side] = entry

    verification = {
        "level": "formal",
        "checker": checker,
        "replay": {key: replay[key] for key in CHALLENGE_REPLAY_KEYS
                   if key in replay},
        "checks_sha256": checks_sha256(document),
    }
    if reference is not None:
        verification["reference"] = reference
    if note is not None:
        verification["note"] = note
    payload = {}
    if name is not None:
        payload["name"] = name
    payload.update({"d": d, "d_exact": d_exact, "d_lower": d_lower,
                    "solver": solver, "sides": sides,
                    "verification": verification})
    return payload
