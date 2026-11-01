"""Executable interval consumer for the priced CSS construction calculus.

This module implements finite GF(2) state transitions and interval transport.
It deliberately contains no distance search. Exact prices, lower bounds, and
minimum-weight-class enumerations enter as explicit consumer hypotheses; the
module records them as conditions and never verifies them by re-measuring.
"""

from __future__ import print_function

import copy
import json
import math
from collections import deque
from dataclasses import dataclass
from decimal import Decimal
from fractions import Fraction
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

# The fixed identifier enumeration of `spec/STATE_MODEL.md` I3.
#
# An identifier's **rank** is its index in this tuple, and the rank order is
# the enumeration order: the canonical mint takes the first element of this
# tuple not in `used`, which is the same as the least rank not in `used`.
# `lean/CodeCalculus/State.lean` models the identifier type as that rank and
# decodes it back to a name with `identifierAt?`; the two enumerations must
# stay in step, block for block.
#
# The `p` and `q` blocks carry the identifiers the acceptance surface uses
# (`W14`, `W15` and `W21` in `machine/fixtures/mvp_fixtures.json`); the
# enumeration has to contain every identifier the calculus can display, or the
# canonical mint would not skip an identifier that was already used. Recorded
IDENTIFIERS = tuple(
    ["a%d" % i for i in range(1, 10001)]
    + ["b%d" % i for i in range(1, 10001)]
    + ["c%d" % i for i in range(1, 10001)]
    + ["d%d" % i for i in range(1, 10001)]
    + ["e%d" % i for i in range(1, 10001)]
    + ["p%d" % i for i in range(1, 10001)]
    + ["q%d" % i for i in range(1, 10001)]
)

IDENTIFIER_RANK = {identifier: index for index, identifier in enumerate(IDENTIFIERS)}


def identifier_rank(identifier):
    """Canonical rank of an identifier in the fixed enumeration."""
    return IDENTIFIER_RANK.get(identifier, len(IDENTIFIERS) + hash(identifier))


class NoDerivation(Exception):
    """A well-typed operation whose premises do not hold for this state."""


class Malformed(Exception):
    """Malformed input data; no operation evaluation is attempted."""


def support_mask(support):
    mask = 0
    for q in support:
        if not isinstance(q, int) or isinstance(q, bool) or q < 0:
            raise Malformed("qubit labels must be nonnegative integers")
        mask |= 1 << q
    return mask


def _basis(rows):
    basis = {}
    for row in rows:
        value = row
        while value:
            pivot = value.bit_length() - 1
            if pivot in basis:
                value ^= basis[pivot]
            else:
                basis[pivot] = value
                break
    return basis


def rank(rows):
    return len(_basis(rows))


def in_span(value, rows):
    basis = _basis(rows)
    for pivot in sorted(basis, reverse=True):
        if (value >> pivot) & 1:
            value ^= basis[pivot]
    return value == 0


def commutes(left, right):
    return all(bin(left & row).count("1") % 2 == 0 for row in right)


def opposite_sector_name(sector):
    return "Z" if sector == "X" else "X"


def orthogonal(left_rows, right_rows):
    return all(
        bin(left & right).count("1") % 2 == 0
        for left in left_rows for right in right_rows
    )


@dataclass(frozen=True)
class Row:
    id: str
    sector: str
    support: Tuple[int, ...]

    @property
    def mask(self):
        return support_mask(self.support)


@dataclass(frozen=True)
class CodeState:
    Q: Tuple[int, ...]
    rows: Tuple[Row, ...]
    used: frozenset

    @classmethod
    def from_challenge(cls, document):
        try:
            n = document["n"]
            if (not isinstance(n, int) or isinstance(n, bool) or n < 1):
                raise ValueError("n must be a positive integer")
            checks = document["checks"]
            Q = tuple(range(n))
            rows = []
            used = set()
            for sector, prefix in (("X", "a"), ("Z", "b")):
                selected_masks = []
                index = 0
                for support in checks[sector]:
                    support = tuple(sorted(support))
                    mask = support_mask(support)
                    if in_span(mask, selected_masks):
                        continue
                    selected_masks.append(mask)
                    index += 1
                    identifier = "%s%d" % (prefix, index)
                    rows.append(Row(identifier, sector, support))
                    used.add(identifier)
            state = cls(Q, tuple(rows), frozenset(used))
        except (KeyError, TypeError, ValueError) as exc:
            raise Malformed("not a CSS qLDPC challenge document: %s" % exc)
        state.validate()
        declared_k = document.get("k")
        if (not isinstance(declared_k, int) or isinstance(declared_k, bool)
                or declared_k != state.k()):
            raise Malformed("declared k does not match the imported row ranks")
        return state

    def sector_rows(self, sector):
        return tuple(row for row in self.rows if row.sector == sector)

    def n(self):
        return len(self.Q)

    def k(self):
        return self.n() - rank([row.mask for row in self.sector_rows("X")]) - rank(
            [row.mask for row in self.sector_rows("Z")]
        )

    def w(self):
        '''Max stabilizer weight of the display (max row support size).

        A derived, exact property: it is the maximum weight of a displayed
        check in either sector. An empty sector contributes 0.
        '''
        weights = [len(row.support) for row in self.rows]
        return max(weights) if weights else 0

    def validate(self):
        if (any(isinstance(q, bool) or not isinstance(q, int) or q < 0 for q in self.Q)
                or len(set(self.Q)) != len(self.Q)
                or self.Q != tuple(sorted(self.Q))):
            raise Malformed("Q must be a finite, strictly increasing set of "
                            "nonnegative qubit labels")
        live_ids = [row.id for row in self.rows]
        if len(set(live_ids)) != len(live_ids):
            raise Malformed("live row identifiers must be unique")
        if not set(live_ids) <= set(self.used):
            raise Malformed("every live row identifier must be in used")
        if any(identifier not in IDENTIFIERS for identifier in live_ids):
            raise Malformed("live row identifiers must belong to the fixed "
                            "identifier enumeration")
        if any(identifier not in IDENTIFIERS for identifier in self.used):
            raise Malformed("used identifiers must belong to the fixed "
                            "identifier enumeration")
        qset = set(self.Q)
        for row in self.rows:
            if row.sector not in ("X", "Z"):
                raise Malformed("row sector must be X or Z")
            if len(set(row.support)) != len(row.support):
                raise Malformed("row supports may not repeat qubits")
            if tuple(sorted(row.support)) != row.support:
                raise Malformed("row supports must be sorted")
            if not set(row.support) <= qset:
                raise Malformed("row support must be contained in Q")
        for sector in ("X", "Z"):
            rows = [row.mask for row in self.sector_rows(sector)]
            if rank(rows) != len(rows):
                raise Malformed("displayed %s rows are dependent" % sector)
        if not orthogonal(
            [row.mask for row in self.sector_rows("X")],
            [row.mask for row in self.sector_rows("Z")],
        ):
            raise Malformed("X and Z row spaces are not orthogonal")
        if self.k() < 0:
            raise Malformed("CSS ranks exceed the qubit count")

    def _mint(self, used):
        for identifier in IDENTIFIERS:
            if identifier not in used:
                return identifier
        raise NoDerivation("fixed identifier enumeration exhausted")

    def skip(self):
        return self

    def delete_check(self, identifier):
        matches = [row for row in self.rows if row.id == identifier]
        if not matches:
            raise NoDerivation("DisplayedGenerator(%s, pres) fails" % identifier)
        row = matches[0]
        same = [other.mask for other in self.sector_rows(row.sector) if other.id != identifier]
        if in_span(row.mask, same):
            raise NoDerivation("Independent(%s; pres) fails" % identifier)
        result = CodeState(
            self.Q,
            tuple(other for other in self.rows if other.id != identifier),
            self.used,
        )
        result.validate()
        return result


    def add_check(self, sector, support):
        if sector not in ("X", "Z"):
            raise Malformed("C-ADD-CHECK sector must be X or Z")
        if not isinstance(support, (list, tuple)):
            raise Malformed("C-ADD-CHECK support must be a list or tuple")
        support = tuple(support)
        if support != tuple(sorted(support)):
            raise NoDerivation("C-ADD-CHECK support must be sorted")
        if len(set(support)) != len(support):
            raise Malformed("added support may not repeat qubits")
        if not set(support) <= set(self.Q):
            raise NoDerivation("added row is not in F_2^Q")
        candidate = support_mask(support)
        opposite = "Z" if sector == "X" else "X"
        if not commutes(candidate, [row.mask for row in self.sector_rows(opposite)]):
            raise NoDerivation("opposite-sector commutation fails")
        same = [row.mask for row in self.sector_rows(sector)]
        if in_span(candidate, same):
            raise NoDerivation("same-sector independence fails")
        identifier = self._mint(self.used)
        result = CodeState(
            self.Q,
            self.rows + (Row(identifier, sector, support),),
            self.used | frozenset((identifier,)),
        )
        result.validate()
        return result

    def graft(self, qubit, sector, ordered_ids):
        """Apply the explicit row-chain graft described in Theorem 28.1.

        The term must name every displayed selected-sector row touching q, in
        its chain order. The opposite-sector rows are shortened at q. Coverage,
        CSS orthogonality, independence, and k preservation are checked.
        """
        if sector not in ("X", "Z"):
            raise Malformed("E-GRAFT spliced sector must be X or Z")
        if qubit not in self.Q:
            raise NoDerivation("grafted qubit is not in Q")
        opposite = "Z" if sector == "X" else "X"
        if not any(qubit in row.support for row in self.sector_rows(opposite)):
            raise NoDerivation("E-GRAFT grafted qubit is not in the opposite sector")
        touching = [
            row for row in self.sector_rows(sector) if qubit in row.support
        ]
        if not touching:
            raise NoDerivation("E-GRAFT has no selected-sector check at q")
        if len(set(ordered_ids)) != len(ordered_ids):
            raise Malformed("E-GRAFT row order contains duplicate identifiers")
        if set(ordered_ids) != {row.id for row in touching}:
            raise NoDerivation("E-GRAFT must order every selected-sector row at q")
        by_id = {row.id: row for row in self.rows}
        chain = [by_id[identifier] for identifier in ordered_ids]
        remaining_q = tuple(q for q in self.Q if q != qubit)
        qset = set(remaining_q)
        rows = [row for row in self.rows if row.id not in set(ordered_ids)]
        shortened = []
        for row in rows:
            if row.sector != sector and qubit in row.support:
                shortened.append(
                    Row(row.id, row.sector, tuple(q for q in row.support if q != qubit))
                )
            else:
                shortened.append(row)
        minted = []
        next_used = set(self.used)
        for left, right in zip(chain, chain[1:]):
            support = tuple(sorted((set(left.support) ^ set(right.support)) & qset))
            identifier = self._mint(next_used)
            next_used.add(identifier)
            minted.append(Row(identifier, sector, support))
        result = CodeState(
            remaining_q,
            tuple(shortened + minted),
            frozenset(next_used),
        )
        result.validate()
        for remaining in remaining_q:
            for check_sector in ("X", "Z"):
                if not any(remaining in row.support for row in result.sector_rows(check_sector)):
                    raise NoDerivation("E-GRAFT coverage condition fails")
        if result.k() != self.k():
            raise NoDerivation("E-GRAFT does not preserve k")
        return result

    def to_challenge_checks(self, relabel=None):
        relabel = relabel or {q: q for q in self.Q}
        return {
            sector: [[relabel[q] for q in row.support]
                     for row in self.sector_rows(sector)]
            for sector in ("X", "Z")
        }

    @staticmethod
    def direct_sum(left, right):
        if set(left.Q) & set(right.Q):
            raise NoDerivation("C-DIRECT-SUM qubit namespaces overlap")
        if set(left.used) & set(right.used):
            raise NoDerivation("C-DIRECT-SUM used sets overlap")
        result = CodeState(
            tuple(sorted(set(left.Q) | set(right.Q))),
            left.rows + right.rows,
            left.used | right.used,
        )
        result.validate()
        return result

    def glue(self, other, seam_checks=None, seam_certificate=None, **kwargs):
        """E-GLUE: gluing of two codes along a seam ().

        Combines two disjoint-namespace CSS states and adds the seam checks
        supplied by the (consumer-provided) seam certificate. The logical-
        witness prerequisite of TAXONOMY.md section 2.10 is still unmet, so
        witness survival is not claimed by this transition; only the seam
        certificate's admissibility is consumed here.
        """
        left = self
        right = other
        if not isinstance(left, CodeState) or not isinstance(right, CodeState):
            raise Malformed("E-GLUE requires two CodeState inputs")
        if set(left.Q) & set(right.Q):
            raise NoDerivation("E-GLUE qubit namespaces overlap")
        if set(left.used) & set(right.used):
            raise NoDerivation("E-GLUE used sets overlap")

        # Accept a certificate passed positionally or under an alias.
        if isinstance(seam_checks, dict) and seam_certificate is None:
            seam_certificate = seam_checks
            seam_checks = None
        # Accept a single (sector, support) seam check passed bare.
        if (isinstance(seam_checks, (list, tuple)) and len(seam_checks) == 2
                and isinstance(seam_checks[0], str)
                and isinstance(seam_checks[1], (list, tuple))):
            seam_checks = [seam_checks]
        seam_checks = (seam_checks if seam_checks is not None
                       else kwargs.get("checks", kwargs.get("seams")))
        if seam_certificate is None:
            seam_certificate = (kwargs.get("certificate")
                                or kwargs.get("seam")
                                or kwargs.get("seam_cert"))
        if isinstance(seam_certificate, dict):
            if "move_word" in seam_certificate:
                raise Malformed("E-GLUE seam certificate must supply "
                                "move_word_A and move_word_B, not a single "
                                "move_word")
            # Consume the seam certificate's admissibility when it carries
            # the move-word fields (JUDGMENT_LAYER.md section 2e).
            words = seam_certificate.get("move_words")
            if words is None:
                words = seam_certificate.get("words")
            word_a = seam_certificate.get("move_word_A")
            word_b = seam_certificate.get("move_word_B")
            if word_a is None:
                word_a = seam_certificate.get("word_A", seam_certificate.get("word_a",
                          seam_certificate.get("c_A", seam_certificate.get("move_word_a"))))
            if word_b is None:
                word_b = seam_certificate.get("word_B", seam_certificate.get("word_b",
                          seam_certificate.get("c_B", seam_certificate.get("move_word_b"))))
            if words is not None and (word_a is None or word_b is None):
                if isinstance(words, (list, tuple)) and len(words) == 2:
                    word_a, word_b = words
            if word_a is not None or word_b is not None:
                if not (isinstance(word_a, str) and isinstance(word_b, str)):
                    raise Malformed("E-GLUE seam certificate move words must be strings")
                if not (all(ch in "UDLR" for ch in word_a)
                        and all(ch in "UDLR" for ch in word_b)):
                    raise Malformed("E-GLUE seam certificate move words must be "
                                    "strings over {U,D,L,R}^*")
                if word_a != word_b:
                    raise NoDerivation(
                        "E-GLUE seam certificate is inadmissible: move words differ")
            # Evidence is required when a certificate is supplied.
            evidence = seam_certificate.get("evidence", seam_certificate.get("source"))
            if (word_a is not None or word_b is not None or "evidence" in seam_certificate
                    or "source" in seam_certificate):
                if not (isinstance(evidence, str) and evidence.strip()):
                    raise NoDerivation("E-GLUE seam certificate requires an evidence reference")
            if seam_checks is None:
                seam_checks = (seam_certificate.get("seam_checks")
                               or seam_certificate.get("checks")
                               or seam_certificate.get("seams")
                               or seam_certificate.get("rows"))

        q = tuple(sorted(set(left.Q) | set(right.Q)))
        rows = list(left.rows) + list(right.rows)
        used = set(left.used) | set(right.used)

        def _parse_check(item):
            if isinstance(item, Row):
                sector = item.sector
                support = item.support
            elif isinstance(item, dict):
                sector = item.get("sector", item.get("side"))
                support = (item.get("support") if item.get("support") is not None
                           else item.get("qubits", item.get("row")))
            elif isinstance(item, (list, tuple)):
                if len(item) == 2 and isinstance(item[0], str):
                    sector, support = item
                else:
                    raise Malformed("E-GLUE seam check must be (sector, support)")
            else:
                raise Malformed("E-GLUE seam check must be a (sector, support) pair")
            if sector not in ("X", "Z"):
                raise Malformed("E-GLUE seam check sector must be X or Z")
            if not isinstance(support, (list, tuple)):
                raise Malformed("E-GLUE seam check support must be a list or tuple")
            support = tuple(sorted(support))
            if len(set(support)) != len(support):
                raise Malformed("E-GLUE seam check support may not repeat qubits")
            if not set(support) <= set(q):
                raise NoDerivation("E-GLUE seam check is not in F_2^Q")
            return sector, support

        for item in (seam_checks or []):
            sector, support = _parse_check(item)
            candidate = support_mask(support)
            opposite = "Z" if sector == "X" else "X"
            if not commutes(candidate, [row.mask for row in rows if row.sector == opposite]):
                raise NoDerivation("E-GLUE seam check fails opposite-sector commutation")
            same_rows = [row.mask for row in rows if row.sector == sector]
            if in_span(candidate, same_rows):
                raise NoDerivation("E-GLUE seam check fails same-sector independence")
            identifier = CodeState._mint_identifier(used)
            used.add(identifier)
            rows.append(Row(identifier, sector, support))

        result = CodeState(q, tuple(rows), frozenset(used))
        result.validate()
        return result

    @staticmethod
    def _mint_identifier(used):
        for identifier in IDENTIFIERS:
            if identifier not in used:
                return identifier
        raise NoDerivation("fixed identifier enumeration exhausted")

    e_glue = glue

    #
    # Transcribed from spec/OPERATIONAL_SEMANTICS.md §2 and §4.26–§4.30.
    # Each method checks the applicability premises its §2 card states, then
    # constructs the child and validates it; a failed output check is a
    # no-derivation, per the §2 card wording ("an output failing I1-I5 gives
    # no derivation"). E-GLUE has no admitted evaluator transition (the
    # logical-witness prerequisite is unmet): its state/ledger seam helpers live
    # above and consume the §2e certificate as a hypothesis, but no evaluator

    @staticmethod
    def _validate_matrix(matrix, size):
        if not isinstance(matrix, (list, tuple)) or len(matrix) != size:
            raise Malformed(
                "rebase matrix must be a square %d x %d list over F_2" % (size, size))
        rows = []
        for row in matrix:
            if not isinstance(row, (list, tuple)) or len(row) != size:
                raise Malformed("rebase matrix rows must have length %d" % size)
            mask = 0
            for j, entry in enumerate(row):
                if entry not in (0, 1) or isinstance(entry, bool):
                    raise Malformed("rebase matrix entries must be 0 or 1")
                if entry:
                    mask |= 1 << j
            rows.append(mask)
        if rank(rows) != size:
            raise NoDerivation("rebase matrix is singular over F_2")
        return rows

    def rebase(self, sector, matrix):
        """P-REBASE: replace a sector's display by the GL(m,2) mix (§4.26)."""
        if sector not in ("X", "Z"):
            raise Malformed("P-REBASE sector must be X or Z")
        displayed = sorted(self.sector_rows(sector),
                            key=lambda row: identifier_rank(row.id))
        if not displayed:
            raise NoDerivation("P-REBASE has no displayed rows to rebase")
        m = len(displayed)
        self._validate_matrix(matrix, m)
        next_used = set(self.used)
        minted_rows = []
        for i, coefficients in enumerate(matrix):
            support_set = set()
            for j, coefficient in enumerate(coefficients):
                if coefficient:
                    # GL(m,2) mixes are F_2 combinations: repeated qubit
                    # contributions cancel (symmetric difference), not union.
                    support_set ^= set(displayed[j].support)
            support = tuple(sorted(support_set))
            identifier = self._mint(next_used)
            next_used.add(identifier)
            minted_rows.append(Row(identifier, sector, support))
        survivors = [row for row in self.rows if row.sector != sector]
        result = CodeState(
            self.Q,
            tuple(survivors + minted_rows),
            frozenset(next_used),
        )
        result.validate()
        return result

    def hadamard_sector_swap(self):
        """E-LOCAL-HADAMARD at T=Q: the sector exchange of the whole display.

        The general split-subset instance is not admitted: a hadamard term for
        any other qubit subset has no derivation (the S1-dispositioned split
        condition's row-wise mechanics are out of scope; see
        OPERATIONAL_SEMANTICS.md §4.27).
        """
        swapped = tuple(Row(row.id, opposite_sector_name(row.sector), row.support)
                        for row in self.rows)
        result = CodeState(self.Q, swapped, self.used)
        result.validate()
        return result

    def peel(self, qubit, sector, row_id):
        """E-PEEL: remove q and the unique displayed tau-row touching it (§4.28)."""
        if sector not in ("X", "Z"):
            raise Malformed("E-PEEL selected sector must be X or Z")
        if qubit not in self.Q:
            raise NoDerivation("E-PEEL peeled qubit is not in Q")
        matches = [row for row in self.rows if row.id == row_id]
        if not matches:
            raise NoDerivation("DisplayedGenerator(%s, pres) fails" % row_id)
        row = matches[0]
        if row.sector != sector:
            raise NoDerivation("E-PEEL named row is not a displayed %s-row" % sector)
        if qubit not in row.support:
            raise NoDerivation("E-PEEL named row does not contain the peeled qubit")
        touching = [other for other in self.sector_rows(sector) if qubit in other.support]
        if touching != [row]:
            raise NoDerivation("E-PEEL unique-touch fails: q is not in exactly one displayed %s-row" % sector)
        opposite = opposite_sector_name(sector)
        if any(other.support == (qubit,) for other in self.sector_rows(opposite)):
            raise NoDerivation("E-PEEL zero-check guard fails: an opposite-sector row would collapse to the identity")
        remaining_q = tuple(q for q in self.Q if q != qubit)
        rows = []
        for other in self.rows:
            if other.id == row.id:
                continue
            if other.sector == opposite and qubit in other.support:
                rows.append(Row(other.id, other.sector,
                                tuple(q for q in other.support if q != qubit)))
            else:
                rows.append(other)
        result = CodeState(remaining_q, tuple(rows), self.used)
        try:
            result.validate()
        except Malformed as exc:
            if "dependent" in str(exc):
                raise NoDerivation(
                    "E-PEEL output is not a well-formed CSS display: %s" % exc)
            raise
        return result

    def puncture(self, qubit):
        """E-PUNCTURE: remove q and every displayed row touching it (§4.29).

        This is the admitted induced stabilizer update (the check-puncturing
        form): raw column restriction without the update is not
        CSS-preserving, exactly as spec/TAXONOMY.md §2.8 states.
        """
        if qubit not in self.Q:
            raise NoDerivation("E-PUNCTURE punctured qubit is not in Q")
        remaining_q = tuple(q for q in self.Q if q != qubit)
        surviving_rows = tuple(
            row for row in self.rows if qubit not in row.support)
        result = CodeState(remaining_q, surviving_rows, self.used)
        result.validate()
        return result

    def extend_code(self, new_qubits, additions):
        """E-EXTEND, row-added form: add a disjoint qubit set and ordered,
        canonically minted check rows over Q ∪ Δ (§4.30)."""
        new_qubits = tuple(new_qubits)
        if not isinstance(additions, (list, tuple)) or not isinstance(new_qubits, (list, tuple)):
            raise Malformed("E-EXTEND takes a new-qubit set and a list of typed additions")
        qset = set(self.Q)
        if set(new_qubits) & qset:
            raise NoDerivation("E-EXTEND new qubits must be disjoint from Q")
        if len(set(new_qubits)) != len(new_qubits):
            raise Malformed("E-EXTEND new-qubit set repeats qubits")
        result_q = tuple(sorted(qset | set(new_qubits)))
        rows = list(self.rows)
        used = set(self.used)
        for record in additions:
            if not isinstance(record, (list, tuple)) or len(record) != 2:
                raise Malformed("E-EXTEND additions are (sector, support) pairs")
            sector, support = record
            if sector not in ("X", "Z"):
                raise Malformed("E-EXTEND addition sector must be X or Z")
            if not isinstance(support, (list, tuple)):
                raise Malformed("E-EXTEND added support must be a list or tuple")
            support = tuple(support)
            if support != tuple(sorted(support)):
                raise NoDerivation("E-EXTEND added support must be sorted")
            if len(set(support)) != len(support):
                raise Malformed("E-EXTEND added support may not repeat qubits")
            if not set(support) <= set(result_q):
                raise NoDerivation("E-EXTEND added row leaves Q ∪ Δ")
            candidate = support_mask(support)
            opposite = opposite_sector_name(sector)
            if not commutes(candidate, [row.mask for row in rows if row.sector == opposite]):
                raise NoDerivation("E-EXTEND addition fails opposite-sector commutation")
            if in_span(candidate, [row.mask for row in rows if row.sector == sector]):
                raise NoDerivation("E-EXTEND addition fails same-sector independence")
            identifier = self._mint(used)
            used.add(identifier)
            rows.append(Row(identifier, sector, support))
        result = CodeState(result_q, tuple(rows), frozenset(used))
        result.validate()
        return result


@dataclass(frozen=True)
class Interval:
    """Closed integer interval; None denotes +infinity at either endpoint."""

    lower: Optional[int]
    upper: Optional[int]

    def __post_init__(self):
        for endpoint in (self.lower, self.upper):
            if endpoint is not None and (isinstance(endpoint, bool)
                                        or not isinstance(endpoint, int)):
                raise ValueError("distance endpoints must be integers")
        if self.lower is not None and self.lower < 0:
            raise ValueError("distance lower bounds are nonnegative")
        if self.upper is not None and self.upper < 0:
            raise ValueError("distance upper bounds are nonnegative")
        if self.lower is None and self.upper is not None:
            raise ValueError("an infinite lower endpoint requires an infinite upper endpoint")
        if self.lower is not None and self.upper is not None and self.lower > self.upper:
            raise ValueError("empty interval")

    def as_json(self):
        return {
            "lower": "inf" if self.lower is None else self.lower,
            "upper": "inf" if self.upper is None else self.upper,
        }


def _min_upper(left, right):
    if left is None:
        return right
    if right is None:
        return left
    return min(left, right)


def _transport_interval(lower, upper):
    """Build a transported interval, refusing a contradictory one.

    A carried endpoint contradicted by a witness or a price is a failed
    premise of the transport rule, not a crash and not a widened interval:
    it is `no_derivation`, one of the three outcomes of
    `spec/TERM_LANGUAGE.md` 5.
    """
    try:
        return Interval(lower, upper)
    except ValueError as exc:
        raise NoDerivation("interval transport is inconsistent: %s" % exc)


class DistanceLedger:
    """Consumer-side distance intervals, separate from CodeState."""

    def __init__(self, full, sector, witnesses=None, conditions=None):
        self.full = full
        self.sector = dict(sector)
        self.witnesses = {"X": list((witnesses or {}).get("X", [])),
                          "Z": list((witnesses or {}).get("Z", []))}
        self.conditions = list(conditions or [])

    @classmethod
    def from_challenge(cls, state, document, lower_bounds=None):
        lower_bounds = lower_bounds or {}
        witnesses = {"X": [], "Z": []}
        conditions = []
        uppers = {"X": None, "Z": None}
        try:
            for side in ("X", "Z"):
                item = document["distance"][side]
                support = tuple(sorted(item["witness"]))
                weight = item["value"]
                validate_witness(state, side, support, weight)
                witnesses[side].append({"support": list(support), "value": weight,
                                        "source": "qldpc-challenge witness"})
                uppers[side] = weight
        except (KeyError, TypeError) as exc:
            raise Malformed("challenge distance witness is incomplete: %s" % exc)
        side_bounds = {}
        for side in ("X", "Z"):
            raw = lower_bounds.get(side, 0)
            if isinstance(raw, dict):
                if raw.get("source"):
                    conditions.append({"cell": "input lower bound", "property": side,
                                       "source": raw["source"]})
                raw = raw.get("value", 0)
            if not isinstance(raw, int) or isinstance(raw, bool) or raw < 0:
                raise Malformed("supplied lower bounds must be nonnegative integers")
            try:
                side_bounds[side] = Interval(raw, uppers[side])
            except ValueError as exc:
                raise Malformed("supplied lower bound contradicts the witness: %s" % exc)
        d_lower = lower_bounds.get("d", 0)
        if isinstance(d_lower, dict):
            if d_lower.get("source"):
                conditions.append({"cell": "input lower bound", "property": "d",
                                   "source": d_lower["source"]})
            d_lower = d_lower.get("value", 0)
        if not isinstance(d_lower, int) or isinstance(d_lower, bool) or d_lower < 0:
            raise Malformed("supplied lower bounds must be nonnegative integers")
        side_min_lower = min(
            (bound.lower for bound in side_bounds.values() if bound.lower is not None),
            default=None,
        )
        if d_lower:
            try:
                side_bounds = {
                    side: Interval(max(bound.lower if bound.lower is not None else 0, d_lower),
                                   bound.upper)
                    for side, bound in side_bounds.items()
                }
            except ValueError as exc:
                raise Malformed("supplied lower bound contradicts the witness: %s" % exc)
        full_lower = max(d_lower, side_min_lower or 0)
        full_upper = _min_upper(uppers["X"], uppers["Z"])
        if full_upper is not None and full_lower > full_upper:
            raise Malformed("supplied lower bound contradicts the witness")
        return cls(Interval(full_lower, full_upper), side_bounds, witnesses, conditions)

    def copy(self):
        return DistanceLedger(
            self.full,
            self.sector,
            copy.deepcopy(self.witnesses),
            copy.deepcopy(self.conditions),
        )

    def record_witness(self, state, side, support, source="consumer witness"):
        support = tuple(sorted(support))
        weight = len(support)
        validate_witness(state, side, support, weight)
        self.witnesses[side].append({"support": list(support), "value": weight,
                                     "source": source})

    def _valid_witnesses(self, state, side):
        valid = []
        seen = set()
        for witness in self.witnesses[side]:
            support = tuple(sorted(witness["support"]))
            try:
                validate_witness(state, side, support, witness["value"])
            except NoDerivation:
                continue
            if support not in seen:
                valid.append({"support": list(support), "value": witness["value"],
                              "source": witness.get("source", "consumer witness")})
                seen.add(support)
        return valid

    def propagate(self, operation, new_state, hypothesis=None, observations=None,
                  parent_state=None):
        """Apply the licensed interval rule; hypotheses are never inferred.

        `parent_state` carries the state before the step, for hypothesis
        cells whose cheap structural side is computed rather than trusted
        (direct-sum extinction). Callers that supply no such hypothesis may
        omit it.
        """
        hypothesis = hypothesis or {}
        observations = observations or {}
        extinction_applied = False
        extinction_factor = None
        if not isinstance(hypothesis, dict) or not isinstance(observations, dict):
            raise Malformed("hypotheses and observations must be objects")
        out = self.copy()
        op = operation["op"]
        if op == "C-SKIP":
            pass
        elif op == "C-ADD-CHECK":
            # Every licensed addition rule only raises lower endpoints
            # (distance cannot decrease under an added check). Hypotheses on
            # one step compose by max of lower endpoints: each block reads
            # the running `out`, not the parent ledger, so a sector-aware
            # price and a rank-completion cell on the same step tighten
            # instead of overwriting.
            strict = hypothesis.get("strict_improvement")
            if strict is not None:
                if not isinstance(strict, dict):
                    raise NoDerivation("strict-improvement hypothesis must be an object")
                old = self.full
                base = strict.get("base_distance")
                if (old.lower is None or old.upper is None or old.lower != old.upper
                        or not isinstance(base, int) or isinstance(base, bool)
                        or base != old.lower
                        or strict.get("all_minimum_classes_killed") is not True
                        or not isinstance(strict.get("enumeration_id"), str)
                        or not strict.get("enumeration_id").strip()):
                    raise NoDerivation("strict-improvement hypothesis is incomplete or mismatched")
                improved = base + 1
                out.full = Interval(max(out.full.lower, improved), None)
                # Raise lower endpoints, never lower them: a sector can
                # coherently carry a lower bound above base+1, because
                # d = min(d_X, d_Z) constrains the sectors only through their
                # minimum.
                for side in ("X", "Z"):
                    carried = out.sector[side].lower
                    out.sector[side] = (
                        Interval(None, None) if carried is None
                        else Interval(max(carried, improved), None)
                    )
                out.conditions.append({"cell": "C-ADD-CHECK strict improvement",
                                       "status": "conditional",
                                       "enumeration_id": strict["enumeration_id"]})
            sector_gauging = hypothesis.get("sector_gauging")
            if sector_gauging is not None:
                if not isinstance(sector_gauging, dict):
                    raise NoDerivation("sector-gauging hypothesis must be an object")
                evidence = sector_gauging.get("evidence")
                if not isinstance(evidence, str) or not evidence.strip():
                    raise NoDerivation("sector-gauging requires an evidence reference")
                prices = {}
                for side, field in (("X", "w_X"), ("Z", "w_Z")):
                    value = sector_gauging.get(field)
                    if value is None:
                        continue
                    if (not isinstance(value, int) or isinstance(value, bool) or value < 0):
                        raise NoDerivation("sector-gauging prices must be nonnegative integers")
                    prices[side] = value
                if not prices:
                    raise NoDerivation("sector-gauging requires at least one sector price")
                for side in ("X", "Z"):
                    if side in prices:
                        carried = out.sector[side].lower
                        out.sector[side] = (
                            Interval(prices[side], None)
                            if carried is None
                            else Interval(max(carried, prices[side]), None)
                        )
                out.conditions.append({"cell": "C-ADD-CHECK sector-aware gauging",
                                       "status": "conditional",
                                       "prices": prices,
                                       "evidence": evidence})
            extinction = hypothesis.get("direct_sum_extinction")
            if extinction is not None:
                if not isinstance(extinction, dict):
                    raise NoDerivation("direct-sum extinction hypothesis must be an object")
                old = self.full
                base = extinction.get("base_distance")
                factor = extinction.get("factor_distance")
                evidence = extinction.get("evidence")
                if (old.lower is None or old.upper is None or old.lower != old.upper
                        or base != old.lower
                        or not isinstance(factor, int) or isinstance(factor, bool)
                        or factor <= base
                        or parent_state is None):
                    raise NoDerivation("direct-sum extinction hypothesis is incomplete or mismatched")
                # The cheap parts of the hypothesis are computed, not trusted
                # disjoint union, the added check must lie inside one block,
                # and gauging must extinguish that block's last logical
                # (k drops by exactly one). Only the surviving block's
                # distance d_B stays an external judgment input, covered by
                # the required evidence reference.
                if not isinstance(evidence, str) or not evidence.strip():
                    raise NoDerivation("direct-sum extinction requires an evidence reference")
                if tanner_components(parent_state) != 2 or tanner_components(new_state) != 2:
                    raise NoDerivation(
                        "direct-sum extinction: the parent is not a two-block disjoint union "
                        "or the added check merges the blocks (rank_check %r)"
                        % extinction.get("rank_check"))
                added_support = [q for q in operation.get("support", [])]
                if not added_support:
                    raise NoDerivation("direct-sum extinction: missing added-check support")
                parent_components = _tanner_component_of(parent_state)
                if any(q not in parent_components for q in added_support):
                    raise NoDerivation("direct-sum extinction: added check outside Q")
                block_root = parent_components[added_support[0]]
                if any(parent_components[q] != block_root for q in added_support):
                    raise NoDerivation("direct-sum extinction: added check spans two blocks")
                block_qs = [q for q in parent_state.Q
                            if parent_components[q] == block_root]
                other_qs = [q for q in parent_state.Q
                            if parent_components[q] != block_root]
                if _restricted_k(new_state, block_qs) != 0:
                    raise NoDerivation(
                        "direct-sum extinction: the gauged block still has logicals "
                        "(k_A' != 0)")
                if not other_qs or _restricted_k(parent_state, other_qs) < 1:
                    raise NoDerivation(
                        "direct-sum extinction: the surviving block has no logical "
                        "(d_B meaningless)")
                # A carried sector lower bound may exceed d_B = min(d_X,B, d_Z,B)
                # (: direct-sum extinction monotonicity): tightening a
                # coarse parent ledger to the exact truth must not break a
                # valid derivation. Only the full-distance lower endpoint,
                # which is <= d_B by construction, is checked.
                if out.full.lower is not None and out.full.lower > factor:
                    raise NoDerivation(
                        "direct-sum extinction: full lower bound exceeds d_B")
                extinction_applied = True
                extinction_factor = factor
                out.full = Interval(factor, factor)
                for side in ("X", "Z"):
                    carried = out.sector[side].lower
                    out.sector[side] = (
                        Interval(None, None) if carried is None
                        else Interval(max(carried, factor), None)
                    )
                out.conditions.append({"cell": "C-ADD-CHECK direct-sum extinction",
                                       "status": "conditional",
                                       "rank_check": "computed (tanner components + k drop)",
                                       "evidence": evidence})
            # Given both sector lower endpoints, the full-distance lower
            # endpoint may be raised to their minimum: d = min(d_X, d_Z) is
            endpoint_X = out.sector["X"].lower
            endpoint_Z = out.sector["Z"].lower
            if endpoint_X is not None and endpoint_Z is not None:
                current_lower = 0 if out.full.lower is None else out.full.lower
                new_lower = max(current_lower, min(endpoint_X, endpoint_Z))
                # A stale parent upper endpoint must not make a true
                if out.full.upper is not None and new_lower > out.full.upper:
                    out.full = Interval(new_lower, None)
                else:
                    out.full = Interval(new_lower, out.full.upper)
        elif op == "C-DELETE-CHECK":
            out.full = Interval(0, self.full.upper)
            out.sector = {side: Interval(0, self.sector[side].upper)
                          for side in ("X", "Z")}
            price = hypothesis.get("deletion_price")
            if price is not None:
                if not isinstance(price, dict):
                    raise NoDerivation("priced deletion hypothesis must be an object")
                if not isinstance(price.get("evidence"), str) or not price["evidence"].strip():
                    raise NoDerivation("priced deletion requires an evidence reference")
                values = (price.get("w_del"), price.get("w_exp"))
                if any(not isinstance(value, int) or isinstance(value, bool) or value <= 0
                       for value in values):
                    raise NoDerivation("priced deletion requires positive integer minima")
                low = _min_upper(self.full.lower, min(values))
                high = _min_upper(self.full.upper, min(values))
                out.full = Interval(low, high)
                # The supplied deletion price is a *full-distance* price. It
                # licenses d' = min(d, w_del, w_exp) and nothing about d_X or
                # d_Z: the source's deletion result is stated on the full
                # distance, with no sector-wise counterpart, so the sector
                # lower endpoints stay where the unpriced rule put them. A
                # sector price would need separate admission.
                out.conditions.append({"cell": "C-DELETE-CHECK priced",
                                       "status": "conditional",
                                       "evidence": price["evidence"]})
        elif op == "E-GRAFT":
            # Sector-wise graft price (code-deformation row 28.2 under the
            # corrected rules of OPERATIONAL_SEMANTICS.md §4.13):
            #   d'_sigma = min(d_sigma, w_expose,sigma) for the non-spliced
            #   sector; the spliced sector carries its lower endpoint only and
            #   drops its upper endpoint to +inf unless a child-valid witness
            #   supplies one. The scalar form d' = min(d, w_expose,tau_bar)
            #   (d' <= d) is refuted for this transition; see §4.13.
            # The non-spliced sector is where exposure happens: its lower
            # endpoint resets to zero and its upper endpoint carries, since
            # d'_sigma <= d_sigma for that sector.
            out.full = Interval(0, None)
            tau = operation["sector"]
            other = "Z" if tau == "X" else "X"
            out.sector[tau] = Interval(self.sector[tau].lower, None)
            out.sector[other] = Interval(0, self.sector[other].upper)
            price = hypothesis.get("graft_price")
            if price is not None:
                if not isinstance(price, dict):
                    raise NoDerivation("graft price hypothesis must be an object")
                value = price.get("w_expose")
                if (not isinstance(value, int) or isinstance(value, bool) or value < 0
                        or not isinstance(price.get("evidence"), str)
                        or not price["evidence"].strip()):
                    raise NoDerivation("graft price needs a nonnegative exposure minimum and evidence")
                # The exposure price is indexed to the **non-spliced**
                # sector, so it licenses that sector's exact interval as
                # well as the full distance. The spliced sector needs no
                # price and gets none.
                out.full = Interval(
                    _min_upper(self.full.lower, value),
                    value,
                )
                out.sector[other] = Interval(
                    _min_upper(self.sector[other].lower, value),
                    _min_upper(self.sector[other].upper, value),
                )
                out.conditions.append({"cell": "E-GRAFT price",
                                       "status": "conditional",
                                       "evidence": price["evidence"],
                                       "exposure_sector": other})
        elif op == "P-REBASE":
            # The row spaces are unchanged in both sectors (§4.26), so every
            # span-expressible endpoint and every witness stays valid; the
            # display-relative properties are recomputed elsewhere and need
            # no ledger action.
            out.conditions.append({"cell": "P-REBASE", "status": "structural",
                                   "sector": operation.get("sector")})
        elif op == "E-LOCAL-HADAMARD":
            if parent_state is None:
                raise NoDerivation("E-LOCAL-HADAMARD transport needs the parent state")
            qubits = sorted(operation.get("qubits", []))
            if len(set(qubits)) != len(qubits):
                raise Malformed(
                    "E-LOCAL-HADAMARD lists a qubit label twice; a list with "
                    "repeats does not name a subset")
            if set(qubits) != set() and set(qubits) != set(parent_state.Q):
                # The transport is only licensed where the state transition is
                # derivable (spec/TERM_LANGUAGE.md §2): T = Q or T = ∅, and
                # inapplicable otherwise. Swapping the sector intervals of a
                # proper subset T ⊊ Q would carry a judgment the transition
                raise NoDerivation(
                    "E-LOCAL-HADAMARD transport is admitted only for the T=Q "
                    "sector exchange and the T=∅ identity "
                    "(spec/OPERATIONAL_SEMANTICS.md §2, §4.27)")
            if qubits:
                # §4.27: the full distance carries exactly (d' = d,
                # weight-preserving conjugation), and the sector distances
                # exchange exactly (d'_X = d_Z, d'_Z = d_X). Witnesses swap
                # sides and are then revalidated against the child by the
                # shared tail below.
                out.full = self.full
                out.sector = {"X": self.sector["Z"], "Z": self.sector["X"]}
                out.witnesses = {
                    "X": copy.deepcopy(self.witnesses["Z"]),
                    "Z": copy.deepcopy(self.witnesses["X"]),
                }
            # T = ∅ is the identity on the state (card); the ledger carries
            # unchanged.
            out.conditions.append({"cell": "E-LOCAL-HADAMARD sector swap",
                                   "status": "structural",
                                   "qubits": qubits})
        elif op == "E-PEEL":
            # §4.28: no distance rule of either polarity is derivable for
            # this move (the coordinate restriction can kill the parent's
            # minimum-weight logical or lock it into the child span); the
            # honest ledger resets and keeps only child-valid witnesses.
            out.full = Interval(0, None)
            out.sector = {side: Interval(0, None) for side in ("X", "Z")}
            out.conditions.append({"cell": "E-PEEL", "status": "structural",
                                   "selected_sector": operation.get("sector")})
        elif op == "E-PUNCTURE":
            # §4.29: same disposition as the peel -- no distance rule
            # carries; in particular even the qubit-named-by-no-row instance
            # can raise the minimum (the deleted qubit's own free logical
            # can be the parent's lightest). Reset + child-witness uppers.
            out.full = Interval(0, None)
            out.sector = {side: Interval(0, None) for side in ("X", "Z")}
            out.conditions.append({"cell": "E-PUNCTURE", "status": "structural"})
        elif op == "E-EXTEND":
            if parent_state is None:
                raise NoDerivation("E-EXTEND transport needs the parent state")
            new_qubits = tuple(operation.get("new_qubits", ()))
            additions = list(operation.get("additions", ()))
            added_sectors = {record[0] for record in additions if record}
            if new_qubits:
                # §4.30: with a namespace change no distance rule is derivable;
                # every interval resets its lower endpoint and only
                # child-valid witnesses supply upper endpoints.
                out.full = Interval(0, None)
                out.sector = {side: Interval(0, None) for side in ("X", "Z")}
            else:
                # Δ = ∅: treated exactly as a C-ADD-CHECK sequence (§4.30):
                # carry the lower endpoints and rebuild every upper endpoint
                # from child-valid witnesses. Adding a check can only raise a
                # distance, and the carried (pre-change) upper endpoint is not
                # a sound bound for the child.
                out.full = Interval(self.full.lower, None)
                out.sector = {side: Interval(self.sector[side].lower, None)
                              for side in ("X", "Z")}
            out.conditions.append({"cell": "E-EXTEND", "status": "structural",
                                   "new_qubits": list(new_qubits),
                                   "additions": len(additions)})
        elif op == "E-GLUE":
            right_ledger = (operation.get("right_ledger")
                            or operation.get("right")
                            or operation.get("other_ledger"))
            if right_ledger is None and isinstance(hypothesis, dict):
                right_ledger = (hypothesis.get("right_ledger")
                                or hypothesis.get("right")
                                or hypothesis.get("other_ledger"))
            if not isinstance(right_ledger, DistanceLedger):
                raise Malformed("E-GLUE propagate requires a right_ledger DistanceLedger")
            seam_certificate = (operation.get("seam_certificate")
                                or operation.get("certificate")
                                or operation.get("seam"))
            if seam_certificate is None and isinstance(hypothesis, dict):
                seam_certificate = (hypothesis.get("seam_certificate")
                                    or hypothesis.get("certificate")
                                    or hypothesis.get("seam"))
            out = self.glue(right_ledger, hypothesis=hypothesis,
                            seam_certificate=seam_certificate)
            out.conditions = list(out.conditions)
        else:
            raise Malformed("unknown operation %s" % op)

        for side in ("X", "Z"):
            out.witnesses[side] = out._valid_witnesses(new_state, side)
            observed = observations.get(side)
            if observed:
                out.record_witness(new_state, side, observed,
                                   source="supplied post-step logical witness")
                out.witnesses[side] = out._valid_witnesses(new_state, side)
            upper = min((w["value"] for w in out.witnesses[side]), default=None)
            current = out.sector[side]
            delta_empty_extend = (op == "E-EXTEND"
                                     and not tuple(operation.get("new_qubits", ())))
            if op == "C-ADD-CHECK" or delta_empty_extend:
                # Old upper endpoints are stale; rebuild from witnesses only.
                out.sector[side] = _transport_interval(current.lower, upper)
            else:
                # Carry the licensed upper endpoint and tighten with
                # witnesses. A witness is only ever an upper bound: it may
                # tighten what the transition rule proved, and never widen or
                # discard it -- not even when the caller supplies it as an
                # observation.
                out.sector[side] = _transport_interval(
                    current.lower, _min_upper(current.upper, upper)
                )

        if new_state.k() == 0:
            out.full = Interval(None, None)
            out.sector = {side: Interval(None, None) for side in ("X", "Z")}
        else:
            sector_upper = _min_upper(out.sector["X"].upper, out.sector["Z"].upper)
            if op == "C-ADD-CHECK":
                out.full = _transport_interval(out.full.lower, sector_upper)
            else:
                out.full = _transport_interval(
                    out.full.lower, _min_upper(out.full.upper, sector_upper)
                )
        if extinction_applied and new_state.k() != 0:
            out.full = Interval(out.full.lower, extinction_factor)
        return out

    def decide(self, target):
        if not isinstance(target, int) or isinstance(target, bool):
            raise Malformed("target must be a nonnegative integer")
        if self.full.lower is None or self.full.lower >= target:
            return "certify"
        if self.full.upper is not None and self.full.upper < target:
            return "prune"
        return "re-measure"

    def as_json(self):
        return {
            "d": self.full.as_json(),
            "d_X": self.sector["X"].as_json(),
            "d_Z": self.sector["Z"].as_json(),
            "conditional_inputs": list(self.conditions),
            "witnesses": copy.deepcopy(self.witnesses),
        }

    @staticmethod
    def direct_sum(left, right):
        def min_intervals(a, b):
            lower = _min_upper(a.lower, b.lower)
            upper = _min_upper(a.upper, b.upper)
            return Interval(lower, upper)

        return DistanceLedger(
            min_intervals(left.full, right.full),
            {side: min_intervals(left.sector[side], right.sector[side])
             for side in ("X", "Z")},
            {"X": [], "Z": []},
            left.conditions + right.conditions,
        )

    def glue(self, other, hypothesis=None, seam_certificate=None, **kwargs):
        """E-GLUE ledger transport: min of the two factor intervals, conditional
        on an admissible seam certificate (JUDGMENT_LAYER.md section 2e)."""
        left = self
        right = other
        if not isinstance(left, DistanceLedger) or not isinstance(right, DistanceLedger):
            raise Malformed("E-GLUE requires two DistanceLedger inputs")
        hypothesis = hypothesis or kwargs.get("hypothesis") or {}
        if not isinstance(hypothesis, dict):
            raise Malformed("E-GLUE hypothesis must be an object")
        if seam_certificate is None:
            seam_certificate = (hypothesis.get("seam_certificate")
                                or hypothesis.get("seam")
                                or hypothesis.get("certificate")
                                or kwargs.get("seam_certificate")
                                or kwargs.get("certificate"))
        # Allow the certificate to be carried directly in the hypothesis.
        if seam_certificate is None and any(k in hypothesis for k in
                ("move_word_A", "move_word_B", "move_words", "word_A", "word_B",
                 "c_A", "c_B")):
            seam_certificate = hypothesis
        has_certificate = isinstance(seam_certificate, dict)
        if seam_certificate is not None and not has_certificate:
            raise Malformed("E-GLUE seam certificate must be an object")

        # E-GLUE is refused without an admissible seam certificate, even
        # though its lower endpoints are sound without one.
        if not has_certificate:
            raise NoDerivation("E-GLUE requires an admissible seam certificate")

        word_a = None
        word_b = None
        evidence = None
        if has_certificate:
            words = seam_certificate.get("move_words", seam_certificate.get("words"))
            word_a = seam_certificate.get("move_word_A")
            if word_a is None:
                word_a = seam_certificate.get("word_A", seam_certificate.get("word_a",
                          seam_certificate.get("c_A", seam_certificate.get("move_word_a"))))
            word_b = seam_certificate.get("move_word_B")
            if word_b is None:
                word_b = seam_certificate.get("word_B", seam_certificate.get("word_b",
                          seam_certificate.get("c_B", seam_certificate.get("move_word_b"))))
            if words is not None and (word_a is None or word_b is None):
                if isinstance(words, (list, tuple)) and len(words) == 2:
                    word_a, word_b = words
            if not (isinstance(word_a, str) and isinstance(word_b, str)):
                raise Malformed("E-GLUE seam certificate move words must be strings")
            if not (all(ch in "UDLR" for ch in word_a)
                    and all(ch in "UDLR" for ch in word_b)):
                raise Malformed("E-GLUE seam certificate move words must be "
                                "strings over {U,D,L,R}^*")
            if word_a != word_b:
                raise NoDerivation("E-GLUE seam certificate is inadmissible: move words differ")
            evidence = seam_certificate.get("evidence", seam_certificate.get("source"))
            if not (isinstance(evidence, str) and evidence.strip()):
                raise NoDerivation("E-GLUE seam certificate requires an evidence reference")

        # Lower endpoints are sound without any certificate (adding seam
        # checks never lowers a distance); the seam certificate of §2e
        # licenses only the Z sector's upper endpoint, d_Z(Q) =
        # min(d_A, d_B). The X and full upper endpoints are not licensed
        # and are left to child-valid witnesses.
        merged_full_lower = _min_upper(left.full.lower, right.full.lower)
        merged = DistanceLedger(
            Interval(merged_full_lower, None),
            {"X": Interval(_min_upper(left.sector["X"].lower,
                                      right.sector["X"].lower), None),
             "Z": Interval(_min_upper(left.sector["Z"].lower,
                                      right.sector["Z"].lower),
                           _min_upper(left.sector["Z"].upper,
                                      right.sector["Z"].upper))},
            {"X": [], "Z": []},
            left.conditions + right.conditions,
        )
        if has_certificate:
            merged.conditions.append({
                "cell": "E-GLUE seam certificate",
                "status": "conditional",
                "move_word": word_a,
                "evidence": evidence,
            })
        return merged

    e_glue = glue


def validate_witness(state, side, support, claimed_weight):
    if side not in ("X", "Z"):
        raise Malformed("witness side must be X or Z")
    if len(set(support)) != len(support) or not set(support) <= set(state.Q):
        raise NoDerivation("witness support is not a subset of Q")
    if len(support) != claimed_weight or not support:
        raise NoDerivation("witness weight does not match its support")
    vector = support_mask(support)
    same = "X" if side == "X" else "Z"
    opposite = "Z" if side == "X" else "X"
    if not commutes(vector, [row.mask for row in state.sector_rows(opposite)]):
        raise NoDerivation("witness does not commute with opposite-sector checks")
    if in_span(vector, [row.mask for row in state.sector_rows(same)]):
        raise NoDerivation("witness lies in the same-sector stabilizer span")
    return True


def apply_operation(state, operation):
    if not isinstance(operation, dict):
        raise Malformed("operation must be an object")
    op = operation.get("op")
    if op == "C-SKIP":
        return state.skip()
    if op == "C-DELETE-CHECK":
        return state.delete_check(operation.get("row_id"))
    if op == "C-ADD-CHECK":
        return state.add_check(operation.get("sector"), operation.get("support", []))
    if op == "E-GRAFT":
        return state.graft(operation.get("qubit"), operation.get("sector"),
                           operation.get("ordered_row_ids", []))
    if op == "P-REBASE":
        return state.rebase(operation.get("sector"), operation.get("matrix"))
    if op == "E-LOCAL-HADAMARD":
        qubits = operation.get("qubits")
        if qubits is None or not isinstance(qubits, (list, tuple)):
            raise Malformed("E-LOCAL-HADAMARD names a qubit subset T")
        qset = set(qubits)
        if len(qset) != len(qubits):
            # A list that repeats a label does not name a subset: the term is
            # ill-typed rather than inapplicable (spec/TERM_LANGUAGE.md §2,
            raise Malformed(
                "E-LOCAL-HADAMARD lists a qubit label twice; a list with "
                "repeats does not name a subset")
        if qset != set(state.Q) and qset != set():
            raise NoDerivation(
                "E-LOCAL-HADAMARD is admitted only for the T=Q sector exchange; "
                "the general split-subset instance has no admitted transition "
                "(spec/OPERATIONAL_SEMANTICS.md §2, §4.27)")
        if not qset:
            return state.skip()
        return state.hadamard_sector_swap()
    if op == "E-PEEL":
        return state.peel(operation.get("qubit"), operation.get("sector"),
                          operation.get("row_id"))
    if op == "E-PUNCTURE":
        return state.puncture(operation.get("qubit"))
    if op == "E-EXTEND":
        return state.extend_code(operation.get("new_qubits", ()),
                                 operation.get("additions", ()))
    if op == "E-GLUE":
        right_state = (operation.get("right_state")
                      or operation.get("other_state")
                      or operation.get("right")
                      or operation.get("other")
                      or operation.get("factor"))
        hypothesis = operation.get("hypothesis")
        if right_state is None and isinstance(hypothesis, dict):
            right_state = (hypothesis.get("right_state")
                          or hypothesis.get("other_state")
                          or hypothesis.get("right")
                          or hypothesis.get("other")
                          or hypothesis.get("factor"))
        if not isinstance(right_state, CodeState):
            raise Malformed("E-GLUE requires a right_state CodeState")
        seam_checks = (operation.get("seam_checks")
                      or operation.get("seams")
                      or operation.get("checks"))
        seam_certificate = (operation.get("seam_certificate")
                           or operation.get("certificate")
                           or operation.get("seam"))
        if seam_certificate is None and isinstance(hypothesis, dict):
            seam_certificate = (hypothesis.get("seam_certificate")
                               or hypothesis.get("certificate")
                               or hypothesis.get("seam"))
        if seam_checks is None and isinstance(hypothesis, dict):
            seam_checks = (hypothesis.get("seam_checks")
                          or hypothesis.get("seams")
                          or hypothesis.get("checks"))
        return state.glue(right_state, seam_checks=seam_checks,
                          seam_certificate=seam_certificate)
    raise Malformed("operation is outside the admitted evaluator subset: %s" % op)


# --- Layout ---------------------------------------------------------------
#
# A layout is a geometric placement of the qubits: one coordinate per qubit,
# a layer count, and optionally a module id per qubit. It is *ledger* data,
# not state data: it is supplied per code, it is not minted, it does not enter
# state identity, and it is not transported by `used`.
#
# The one quantity derived from it that the qLDPC board prices is the
# interaction radius -- the largest Euclidean diameter of any single check's
# support. It is recomputed from the child, never copied from the parent:
# the radius is a function of the check set, and every transition that
# changes the check set changes it.
#
# the coordinates are read as exact rationals and every comparison is made
# on *squared* diameters, so no verdict depends on a square root or a
# floating-point tolerance. A JSON float is read at its exact binary value
# (the value the JSON parser produced) and a decimal string at its exact
# decimal value. A decimal radius is a rounding of the square root of the
# exact maximum squared diameter, computed by integer arithmetic, and is
# never the quantity the cap comparison uses: the exported qLDPC claim
# rounds *up* (an upper bound on the real value, see `radius_decimal`),
# while trace and report displays round to nearest
# (`radius_nearest_decimal`).


def _exact_coordinate(value):
    """The exact rational value of one layout coordinate.

    A ``Fraction`` passes through, an ``int`` is exact, a ``float`` is read
    at its exact binary value, and a string or ``Decimal`` is read at its
    exact decimal value.
    """
    if isinstance(value, Fraction):
        return value
    if isinstance(value, str):
        return Fraction(Decimal(value))
    return Fraction(value)


def _squared_distance(a, b):
    """Exact squared Euclidean distance between two layout points."""
    return sum((x - y) ** 2 for x, y in zip(a, b))


def _diameter_squared(coordinates, support):
    """Largest squared distance between two points of a check's support."""
    points = [tuple(_exact_coordinate(value) for value in coordinates[q])
              for q in support]
    widest = Fraction(0)
    for index, left in enumerate(points):
        for right in points[index + 1:]:
            span = _squared_distance(left, right)
            if span > widest:
                widest = span
    return widest


def interaction_radius_squared(coordinates, supports):
    """The exact maximum squared Euclidean diameter over a set of supports.

    The interaction radius is the square root of this quantity, and every
    comparison against a cap is made on the squared values
    (``r <= c`` iff ``r*r <= c*c`` for ``c >= 0``), so no square root is
    ever taken for a verdict. ``coordinates`` is a list indexed the same way
    as the qubit indices in ``supports``. Exactly computable: no search is
    involved, and nothing is trusted.
    """
    widest = Fraction(0)
    for support in supports:
        span = _diameter_squared(coordinates, support)
        if span > widest:
            widest = span
    return widest


def radius_decimal(squared, decimals):
    """The decimal round-up of the radius, computed exactly.

    ``squared`` is the exact maximum squared diameter. The result is the
    float nearest to the least decimal ``k / 10**decimals`` that is at
    least the exact radius ``sqrt(squared)``, where ``k`` is computed by
    integer arithmetic on the rational squared value. The *decimal* is an
    upper bound on the real radius -- not on a floating-point measurement
    of it -- and the verifier parses the same decimal, so the claim and the
    entry cannot drift apart. The float nearest that decimal can sit one
    ulp below it; no comparison in this module reads the float.
    """
    if squared <= 0:
        return 0.0
    numerator = squared.numerator * 10 ** (2 * decimals)
    denominator = squared.denominator
    # The least integer k with k*k >= numerator/denominator is
    # isqrt((numerator - 1) // denominator) + 1.
    k = math.isqrt((numerator - 1) // denominator) + 1
    return k / 10 ** decimals


def radius_nearest_decimal(squared, decimals):
    """A decimal nearest-rounding of the radius, computed exactly.

    ``squared`` is the exact maximum squared diameter. The result is the
    nearest decimal ``k / 10**decimals`` to the exact radius
    ``sqrt(squared)`` (ties round up), computed by integer arithmetic on the
    rational squared value. This is a display convention only: no comparison
    reads it. The exported claim uses ``radius_decimal``, which rounds up
    so that it bounds the real value.
    """
    if squared <= 0:
        return 0.0
    numerator = squared.numerator * 10 ** (2 * decimals)
    denominator = squared.denominator
    # floor(sqrt(numerator/denominator)) == isqrt(numerator // denominator).
    k = math.isqrt(numerator // denominator)
    # Nearest rounding, ties round up: round up when the squared radius is
    # at least (k + 1/2)^2 in units of 1/10**decimals, i.e.
    # 4 * numerator >= (4*k*k + 4*k + 1) * denominator.
    if 4 * numerator >= (4 * k * k + 4 * k + 1) * denominator:
        k += 1
    return k / 10 ** decimals


def _radius_claim(squared):
    """Round the exact radius *up* to four decimals, for the qLDPC claim.

    The claim is an upper bound on the exact radius, and the qLDPC verifier
    compares the claim against the radius at full precision, so rounding
    down could reject an honest entry. Because the round-up is computed on
    the exact squared diameter (see ``radius_decimal``), it bounds the real
    value and not merely a floating-point measurement of it.
    """
    return radius_decimal(squared, 4)


def child_layout(parent, state):
    """The child's layout: the parent's layout restricted to the surviving qubits.

    Every transition either preserves the qubit namespace (`C-SKIP`,
    `C-DELETE-CHECK`, `C-ADD-CHECK`) or removes one qubit from it
    (`E-GRAFT`), and the state keeps the parent's qubit labels, so the
    child's coordinates are the parent's coordinates read at the child's
    qubits. Returns ``None`` when the parent carries no usable layout.
    """
    locality = parent.get("locality")
    if not isinstance(locality, dict):
        return None
    coordinates = locality.get("coordinates")
    if not isinstance(coordinates, list) or len(coordinates) != parent["n"]:
        return None
    for qubit in state.Q:
        if qubit >= len(coordinates):
            return None
    child = {"coordinates": [[_coordinate_to_number(value) for value in coordinates[qubit]]
                            for qubit in state.Q]}
    layers = locality.get("layers")
    if isinstance(layers, int):
        child["layers"] = layers
    modules = locality.get("modules")
    if isinstance(modules, list) and len(modules) == parent["n"]:
        child["modules"] = [modules[qubit] for qubit in state.Q]
    if "contributed_by" in locality:
        child["contributed_by"] = copy.deepcopy(locality["contributed_by"])
    return child


def radius_squared_in_layout(parent, state):
    """The squared interaction radius of a state in the parent's layout, or None.

    The state's rows carry the parent's qubit labels and the parent's
    coordinates are indexed the same way, so the two can be read against
    each other directly -- before and after a transition alike. As in
    `child_layout`, a state whose qubits fall outside the parent's layout has
    no radius here, rather than an out-of-range read. The exact squared
    value is returned so callers can compare against caps without a square
    root.
    """
    locality = parent.get("locality")
    if not isinstance(locality, dict):
        return None
    coordinates = locality.get("coordinates")
    if not isinstance(coordinates, list) or len(coordinates) != parent["n"]:
        return None
    for qubit in state.Q:
        if qubit >= len(coordinates):
            return None
    return interaction_radius_squared(coordinates, [row.support for row in state.rows])


# The consumer's locality-class caps. These are the qLDPC challenge's
# constants, not the calculus's: the class is a consumer-side verdict, not a
# calculus property (spec/JUDGMENT_LAYER.md §2d.4). They are configuration,
# and machine/consumer.json records them.
LOCALITY_CLASS_CAPS = (
    (1, 4.0, "local-2d-single"),
    (2, 7.0, "local-2d-bilayer"),
)


def _coordinate_to_number(value):
    """Convert a layout coordinate to an int or float when it is textual."""
    if isinstance(value, bool):
        return value
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        return value
    if isinstance(value, str):
        text = value.strip()
        try:
            if "." in text or "e" in text.lower():
                return float(text)
            return int(text)
        except ValueError:
            return value
    return value


def layout_honest(parent):
    """Whether the parent's layout satisfies the honesty requirements (2d.3)."""
    locality = parent.get("locality") if isinstance(parent, dict) else None
    if not isinstance(locality, dict):
        return True
    coordinates = locality.get("coordinates")
    if not isinstance(coordinates, list):
        return True
    points = [tuple(point) for point in coordinates if isinstance(point, (list, tuple))]
    return len(points) == len(coordinates) and len(set(points)) == len(points)


def layout_planar(parent):
    """Whether the parent's layout is two-dimensional (2d.4)."""
    locality = parent.get("locality") if isinstance(parent, dict) else None
    if not isinstance(locality, dict):
        return True
    coordinates = locality.get("coordinates")
    if not isinstance(coordinates, list):
        return True
    for point in coordinates:
        if not isinstance(point, (list, tuple)) or len(point) > 2:
            return False
    return True


def locality_class(radius_squared, layers, *, planar=True, honest=True):
    """The consumer's locality class for a squared radius and a layer count.

    The tightest class the caps admit; `unrestricted` otherwise, and also
    for a state with no layout at all. The classes nest by radius, not by
    layer count: a code qualifies for every class whose layer cap and radius
    cap it satisfies, and the caps are checked tightest first.

    The comparison is exact: the squared radius is compared against the
    squared cap (``r <= c`` iff ``r*r <= c*c`` for ``c >= 0``), so neither a
    square root nor a tolerance is involved
    (spec/JUDGMENT_LAYER.md section 2d.1, 2026-10-25).

    The class is assigned only when the layout is planar and honest
    (section 2d.3-2d.4); otherwise the verdict is `unrestricted`.
    """
    if radius_squared is None or layers is None or not planar or not honest:
        return "unrestricted"
    for max_layers, cap, name in LOCALITY_CLASS_CAPS:
        if layers <= max_layers and radius_squared <= cap * cap:
            return name
    return "unrestricted"


def layout_layers(parent):
    """The parent's layer count, or 1 when it states none.

    A boolean or non-positive layer count is not a valid layer count, so it
    yields ``None`` and the layout receives no locality class.
    """
    locality = parent.get("locality")
    if not isinstance(locality, dict):
        return 1
    layers = locality.get("layers")
    if isinstance(layers, bool) or not isinstance(layers, int) or layers <= 0:
        return None
    return layers


def export_challenge_entry(parent, state, ledger, name, construction, date):
    """Export only witness-backed upper bounds; interval lower bounds stay local."""
    relabel = {q: index for index, q in enumerate(state.Q)}
    side_witnesses = {}
    for side in ("X", "Z"):
        valid = ledger._valid_witnesses(state, side)
        if not valid:
            raise ValueError("qLDPC export needs a current %s logical witness" % side)
        best = min(valid, key=lambda witness: witness["value"])
        side_witnesses[side] = {
            "value": best["value"],
            "confidence": "upper_bound",
            "witness": [relabel[q] for q in best["support"]],
        }
    exported = {
        "schema_version": "0.5",
        "name": name,
        "code_type": "CSS",
        "n": state.n(),
        "k": state.k(),
        "checks": state.to_challenge_checks(relabel),
        "distance": {
            "d": min(side_witnesses["X"]["value"], side_witnesses["Z"]["value"]),
            "X": side_witnesses["X"],
            "Z": side_witnesses["Z"],
        },
        "provenance": copy.deepcopy(parent["provenance"]),
    }
    exported["provenance"]["construction"] = construction
    exported["provenance"]["date"] = date
    exported["provenance"]["notes"] = (
        "Generated by the priced construction calculus. Distance is reported "
        "only with witness-backed upper bounds; lower interval bounds are kept "
        "in the separate local ledger."
    )
    exported["provenance"]["origin"] = "submission"
    # The layout is inherited from the parent and restricted to the qubits the
    # child kept, and the interaction radius is recomputed against the child's
    # own check set -- it is a function of that check set, so a parent's claim
    # cannot be carried into a child whose checks differ. The radius is
    # measured on the exported entry, in the same index space the verifier
    # reads, so the claim and the entry cannot drift apart.
    layout = child_layout(parent, state)
    if layout is not None:
        supports = exported["checks"]["X"] + exported["checks"]["Z"]
        layout["interaction_radius"] = _radius_claim(
            interaction_radius_squared(layout["coordinates"], supports)
        )
        exported["locality"] = layout
        if layout["coordinates"] != parent["locality"]["coordinates"]:
            exported["provenance"]["notes"] += (
                " The layout is inherited from the parent and restricted to the "
                "qubits the child kept."
            )
        else:
            exported["provenance"]["notes"] += (
                " The layout is inherited from the parent; its interaction "
                "radius was recomputed against this entry's own checks."
            )
    return exported


def run_sequence(document, operations, lower_bounds=None, target=None):
    state = CodeState.from_challenge(document)
    ledger = DistanceLedger.from_challenge(state, document, lower_bounds)
    # The layer count is read once, from the parent. Restriction (E-GRAFT) and
    # the check transitions never change it, so it holds for every step; a
    # transition that did would have to re-read it here.
    layers = layout_layers(document)
    planar = layout_planar(document)
    honest = layout_honest(document)
    trace = []
    for index, operation in enumerate(operations):
        before = state
        state = apply_operation(state, operation)
        ledger = ledger.propagate(
            operation,
            state,
            hypothesis=operation.get("hypothesis"),
            observations=operation.get("witnesses"),
            parent_state=before,
        )
        radius_squared = radius_squared_in_layout(document, state)
        trace.append({
            "step": index + 1,
            "operation": operation["op"],
            "n": state.n(),
            "k": state.k(),
            "intervals": ledger.as_json(),
            "verdict": ledger.decide(target) if target is not None else None,
            "state_changed": before != state,
            # The interaction radius is recomputed against the child's own
            # check set; the locality class is the consumer's verdict on it.
            "interaction_radius": None if radius_squared is None
            else radius_nearest_decimal(radius_squared, 6),
            "locality_class": locality_class(radius_squared, layers,
                                                  planar=planar, honest=honest),
        })
    return state, ledger, trace


#
# For graphlike codes (every qubit in at most two checks of the relevant
# sector) the source gives a polynomial closed form (Theorem 25.1 +
# pairwise dual distance plus the outer face. The provider below computes
# that value as a consumer-side aid. It does not validate supplied
# hypotheses, does not mutate state, and does not establish any proof. A
# non-graphlike input, or one with no finite exposed operator, is refused
# with a recorded reason. The pending citation concerns only the
# beyond-graphlike case (column weight 3), never the graphlike closed form
# itself.

def column_weights(state, sector="Z"):
    """Column weights (number of checks of ``sector`` per qubit)."""
    return _sector_column_weights(state, sector)


def z_column_weights(state):
    """Number of displayed Z-checks each qubit belongs to, keyed by label.

    Keyed by label, not by position: `Q` keeps the parent's labels after
    `E-GRAFT` (graft filters the namespace), so labels can exceed `n() - 1`
    and position indexing would miss them (the  trap recorded in
    the conformance harness).
    """
    counts = {q: 0 for q in state.Q}
    for row in state.sector_rows("Z"):
        for qubit in row.support:
            counts[qubit] += 1
    return counts


def is_graphlike(state, sector="Z"):
    """Whether every qubit is in at most two displayed checks of ``sector``."""
    weights = (_sector_column_weights(state, sector)
               if sector in ("X", "Z") else z_column_weights(state))
    return all(count <= 2 for count in weights.values())


def graphlike_status(state, sector="Z"):
    """Detection result for the graphlike condition, with a recorded reason."""
    if sector in ("X", "Z"):
        gstatus = _graphlike_sector_status(state, sector)
        return {"graphlike": gstatus["graphlike"],
                "max_column_weight": gstatus["max_column_weight"],
                "max_z_column_weight": gstatus["max_column_weight"],
                "sector": sector,
                "reason": gstatus["reason"]}
    weights = z_column_weights(state)
    max_weight = max(weights.values(), default=0)
    graphlike = max_weight <= 2
    if graphlike:
        reason = ("graphlike: every qubit is in at most two Z-checks "
                  "(max column weight %d)" % max_weight)
    else:
        reason = ("not graphlike: a qubit is in %d Z-checks, above the "
                  "column-weight-2 bound" % max_weight)
    return {"graphlike": graphlike, "max_z_column_weight": max_weight,
            "reason": reason}


def _sector_column_weights(state, sector):
    """Column weights (number of checks of ``sector`` per qubit)."""
    counts = {q: 0 for q in state.Q}
    for row in state.sector_rows(sector):
        for qubit in row.support:
            counts[qubit] += 1
    return counts


def _resolve_deleted_rows(state, deleted):
    """Resolve a deleted-check specification into (sector, list of Row)."""
    if deleted is None:
        return None, []
    if isinstance(deleted, Row):
        deleted = [deleted]
    if isinstance(deleted, str):
        deleted = [deleted]
    if not isinstance(deleted, (list, tuple, set, frozenset)):
        deleted = [deleted]
    rows_by_id = {row.id: row for row in state.rows}
    resolved = []
    sector = None
    for item in deleted:
        if isinstance(item, Row):
            row = item
        elif isinstance(item, str):
            row = rows_by_id.get(item)
            if row is None:
                return None, None
        else:
            rid = getattr(item, "id", None)
            if rid is None and isinstance(item, dict):
                rid = item.get("row_id") or item.get("id")
            row = rows_by_id.get(rid) if rid is not None else None
            if row is None:
                return None, None
        if sector is None:
            sector = row.sector
        elif sector != row.sector:
            return None, None
        resolved.append(row)
    if not resolved:
        return None, []
    return sector, resolved


def _graphlike_sector_status(state, sector):
    weights = _sector_column_weights(state, sector)
    max_weight = max(weights.values(), default=0)
    graphlike = max_weight <= 2
    if graphlike:
        reason = ("graphlike: every qubit is in at most two %s-checks "
                  "(max column weight %d)" % (sector, max_weight))
    else:
        reason = ("not graphlike: a qubit is in %d %s-checks, above the "
                  "column-weight-2 bound" % (max_weight, sector))
    return {"graphlike": graphlike, "max_column_weight": max_weight,
            "sector": sector, "reason": reason}


def _sector_graph(state, sector):
    """Build the (sector)-check incidence graph.

    Vertices are the displayed checks of ``sector``; qubits incident to two
    checks become edges between those vertices, qubits incident to one check
    become edges to a special outer vertex ``None``.
    """
    rows = list(state.sector_rows(sector))
    row_ids = [row.id for row in rows]
    incidence = {q: [] for q in state.Q}
    for row in rows:
        for q in row.support:
            incidence[q].append(row.id)
    adj = {rid: set() for rid in row_ids}
    adj[None] = set()
    for q, ids in incidence.items():
        ids = list(ids)
        if len(ids) == 2:
            a, b = ids[0], ids[1]
            if a != b:
                adj[a].add(b)
                adj[b].add(a)
        elif len(ids) == 1:
            rid = ids[0]
            adj[rid].add(None)
            adj[None].add(rid)
    return {k: list(v) for k, v in adj.items()}


def _shortest_path(adj, src, dst):
    if src == dst:
        return 0
    seen = {src}
    dq = deque([(src, 0)])
    while dq:
        node, dist = dq.popleft()
        for nb in adj.get(node, []):
            if nb in seen:
                continue
            if nb == dst:
                return dist + 1
            seen.add(nb)
            dq.append((nb, dist + 1))
    return None


def graphlike_exposure_price(state, deleted=None, deleted_check=None,
                            deleted_checks=None, deleted_check_id=None,
                            deleted_id=None, check=None, row_id=None):
    """Consumer-side provider for the graphlike exposure price w_exp.

    For graphlike inputs (every qubit in at most two checks of the relevant
    sector) this computes the exposure minimum using the minimum pairwise
    dual distance plus the outer face (Theorem 25.1 + Corollary 25.2 of
    *code-deformation*), over the set of deleted checks supplied. For
    non-graphlike inputs, or when no finite exposed operator exists, it
    refuses with a recorded reason. It is a price provider only: it does not
    mutate state and does not establish any proof.
    """
    spec = deleted
    if spec is None:
        spec = deleted_check
    if spec is None:
        spec = deleted_checks
    if spec is None:
        spec = deleted_check_id
    if spec is None:
        spec = deleted_id
    if spec is None:
        spec = check
    if spec is None:
        spec = row_id
    sector, resolved = _resolve_deleted_rows(state, spec)
    if resolved is None:
        return {
            "status": "unavailable",
            "reason": "deleted check not found in state, or mixed sectors",
            "graphlike": None,
            "w_exp": None,
            "value": None,
        }
    # De-duplicate repeated deleted checks: a repeated terminal would create a
    # zero-length path and a spurious w_exp of 0.
    if resolved:
        seen_ids = set()
        unique = []
        for row in resolved:
            if row.id in seen_ids:
                continue
            seen_ids.add(row.id)
            unique.append(row)
        resolved = unique
    if not resolved:
        return {
            "status": "unavailable",
            "reason": ("no deleted check specified; the exposure price requires "
                       "at least one deleted check to name the exposure set"),
            "graphlike": None,
            "w_exp": None,
            "value": None,
        }
    sector = sector or resolved[0].sector
    gstatus = _graphlike_sector_status(state, sector)
    if not gstatus["graphlike"]:
        return {
            "status": "unavailable",
            "reason": gstatus["reason"],
            "graphlike": False,
            "max_column_weight": gstatus["max_column_weight"],
            "sector": sector,
            "w_exp": None,
            "value": None,
        }
    adj = _sector_graph(state, sector)
    deleted_ids = [row.id for row in resolved]
    terminals = deleted_ids + [None]
    best = None
    for i in range(len(terminals)):
        for j in range(i + 1, len(terminals)):
            d = _shortest_path(adj, terminals[i], terminals[j])
            if d is None:
                continue
            if best is None or d < best:
                best = d
    if best is None:
        return {
            "status": "unavailable",
            "reason": ("graphlike input, but no finite exposed operator: no path "
                       "between the deleted check(s) and the outer boundary or "
                       "another deleted check"),
            "graphlike": True,
            "max_column_weight": gstatus["max_column_weight"],
            "sector": sector,
            "deleted_checks": deleted_ids,
            "w_exp": None,
            "value": None,
        }
    return {
        "status": "computed",
        "w_exp": best,
        "value": best,
        "reason": ("graphlike: minimum pairwise dual distance plus outer face "
                   "= %d" % best),
        "graphlike": True,
        "max_column_weight": gstatus["max_column_weight"],
        "sector": sector,
        "deleted_checks": deleted_ids,
    }


# Historical name.
w_exp_graphlike = graphlike_exposure_price


#
# The combined X+Z Tanner graph is a bipartite graph between qubit nodes and
# check nodes. Its connected components are exactly computable by union-find;
# no search is involved. This is a property of the *displayed* rows, so it is
# display-relative, like w and r, and it carries per primitive as recorded in
# spec/JUDGMENT_LAYER.md section 2. The stronger stabilizer-group connectivity
# is not implemented here.


def tanner_components(state):
    """Number of connected components of the combined X+Z Tanner graph."""
    qubits = list(state.Q)
    checks = list(state.rows)
    if not qubits and not checks:
        return 0
    parent = {}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    for q in qubits:
        parent[("q", q)] = ("q", q)
    for index, row in enumerate(checks):
        node = ("c", index)
        parent[node] = node
        for q in row.support:
            union(node, ("q", q))
    roots = set()
    for node in parent:
        roots.add(find(node))
    return len(roots)


def is_tanner_connected(state):
    """Whether the combined X+Z Tanner graph has exactly one component."""
    components = tanner_components(state)
    if not state.Q and not state.rows:
        return True
    return components == 1


def _tanner_component_of(state):
    """Map each qubit to its Tanner-component root (combined X+Z graph)."""
    parent = {}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    for q in state.Q:
        parent[("q", q)] = ("q", q)
    for index, row in enumerate(state.rows):
        node = ("c", index)
        parent[node] = node
        for q in row.support:
            union(node, ("q", q))
    return {q: find(("q", q)) for q in state.Q}


def _restricted_k(state, qubits):
    """Logical qubit count of the sub-code on `qubits` (rows contained in it)."""
    qset = set(qubits)
    rows_x = [row.mask for row in state.sector_rows("X")
              if set(row.support) <= qset]
    rows_z = [row.mask for row in state.sector_rows("Z")
              if set(row.support) <= qset]
    return len(qset) - rank(rows_x) - rank(rows_z)


#
# Strictly stronger than Tanner connectivity: the stabilizer-group row space
# must not split into blocks on disjoint qubit sets. Computed as the verifier's
# `_stabilizer_block_count` does: reduce H_X and H_Z *separately* (reducing the
# combined matrix XORs X rows into Z rows and can erase a genuine block), then
# union the supports of both reduced row sets. A redundant cross-block check
# can make the Tanner graph connected while this check still fails.


def _rref_masks(masks, width):
    """RREF of integer masks; `width` bounds the bit positions, keyed by label."""
    rows = [m for m in masks]
    r = 0
    for col in range(width):
        sel = None
        for i in range(r, len(rows)):
            if (rows[i] >> col) & 1:
                sel = i
                break
        if sel is None:
            continue
        rows[r], rows[sel] = rows[sel], rows[r]
        for i in range(len(rows)):
            if i != r and ((rows[i] >> col) & 1):
                rows[i] ^= rows[r]
        r += 1
        if r == len(rows):
            break
    return rows[:r]


def stabilizer_group_components(state):
    """Faces of the stabilizer-group block decomposition over `state.Q`.

    The X and Z displayed row spaces are reduced separately and the supports
    of both reduced row sets are unioned. Reducing the combined X+Z mask
    matrix would mix the sectors and over-split (the verifier's gate reports
    one block where the combined reduction reports two).
    """
    parent = {q: q for q in state.Q}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    width = (max(state.Q) + 1) if state.Q else 0
    for sector in ("X", "Z"):
        masks = [row.mask for row in state.sector_rows(sector)]
        for mask in _rref_masks(masks, width):
            qs = [q for q in state.Q if (mask >> q) & 1]
            for q in qs[1:]:
                union(qs[0], q)
    roots = {find(q) for q in state.Q}
    if not state.Q:
        return 0
    return len(roots)


def is_stabilizer_group_connected(state):
    if not state.Q:
        return True
    return stabilizer_group_components(state) == 1


def _main(argv=None):
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("parent", help="qLDPC challenge JSON file")
    parser.add_argument("plan", help="JSON file with operations, lower_bounds, target")
    parser.add_argument("output", help="path for the generated qLDPC JSON")
    parser.add_argument("--ledger", help="optional path for the local interval ledger")
    args = parser.parse_args(argv)
    with open(args.parent) as source:
        parent = json.load(source)
    with open(args.plan) as plan_file:
        plan = json.load(plan_file)
    state, ledger, trace = run_sequence(
        parent, plan.get("operations", []), plan.get("lower_bounds"), plan.get("target")
    )
    output = export_challenge_entry(
        parent, state, ledger, plan["name"], plan["construction"], plan["date"]
    )
    with open(args.output, "w") as target_file:
        json.dump(output, target_file, indent=2)
        target_file.write("\n")
    report = {"trace": trace, "ledger": ledger.as_json(),
              "n": state.n(), "k": state.k()}
    radius_squared = radius_squared_in_layout(parent, state)
    report["geometry"] = {
        "interaction_radius": None if radius_squared is None
        else radius_nearest_decimal(radius_squared, 6),
        "locality_class": locality_class(radius_squared, layout_layers(parent),
                                        planar=layout_planar(parent),
                                        honest=layout_honest(parent)),
        "layers": layout_layers(parent),
    }
    if args.ledger:
        with open(args.ledger, "w") as ledger_file:
            json.dump(report, ledger_file, indent=2)
            ledger_file.write("\n")
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(_main())
