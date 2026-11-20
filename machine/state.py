"""Extracted module from machine/priced_calculus.py."""

import copy
import re
import itertools
import json
import math
from collections import deque
from dataclasses import dataclass
from decimal import Decimal
from fractions import Fraction
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

from machine.gf2 import *

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
    return IDENTIFIER_RANK.get(identifier, len(IDENTIFIERS))

class NoDerivation(Exception):
    """A well-typed operation whose premises do not hold for this state."""

class Malformed(Exception):
    """Malformed input data; no operation evaluation is attempted."""

def _validate_output(result):
    """Validate a transition's output state.

    A child state that fails I1-I5 is a failed premise of the transition
    (no derivation), not malformed input: the inputs were already validated,
    so any failure here belongs to the operation, not the caller.
    """
    try:
        result.validate()
    except Malformed as exc:
        raise NoDerivation(
            "transition output is not a well-formed CSS display: %s" % exc)

def support_mask(support):
    mask = 0
    for q in support:
        if not isinstance(q, int) or isinstance(q, bool) or q < 0:
            raise Malformed("qubit labels must be nonnegative integers")
        mask |= 1 << q
    return mask

def commutes(left, right):
    return all((left & row).bit_count() % 2 == 0 for row in right)

def opposite_sector_name(sector):
    return "Z" if sector == "X" else "X"

def orthogonal(left_rows, right_rows):
    return all(
        (left & right).bit_count() % 2 == 0
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

    def relabel_identifiers(self, used=None):
        """Return a copy of this state whose row identifiers are re-minted
        from the fixed enumeration so that none of them collide with ``used``
        .

        The state's qubit namespace, supports, and sectors are unchanged;
        only the row identifiers (and the ``used`` set) are replaced.  This
        is the "fixed identifier minting" helper that lets two factors with
        overlapping identifier blocks be brought into disjoint ``used`` sets
        before ``E-GLUE`` / ``C-DIRECT-SUM``.  ``used`` defaults to the
        empty set, so a state can be re-minted into a fresh block.
        """
        reserved = set() if used is None else set(used)
        new_rows = []
        new_used = set()
        occupied = set(reserved)
        for row in self.rows:
            identifier = CodeState._mint_identifier(occupied)
            occupied.add(identifier)
            new_used.add(identifier)
            new_rows.append(Row(identifier, row.sector, row.support))
        return CodeState(self.Q, tuple(new_rows), frozenset(new_used))

    fresh_identifiers = relabel_identifiers
    mint_fresh_identifiers = relabel_identifiers

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
        _validate_output(result)
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
        _validate_output(result)
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
        _validate_output(result)
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
        _validate_output(result)
        return result

    def glue(self, other, seam_checks=None, seam_certificate=None, **kwargs):
        """E-GLUE: gluing of two codes along a seam.

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
        _validate_output(result)
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
    # no derivation"). E-GLUE is a binary-only expression constructor
    # (TERM_LANGUAGE.md §1-§2,; contract-stated, Gate 6 unchecked):
    # its binary state/ledger helpers live above (OPERATIONAL_SEMANTICS.md §4.31).

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
        _validate_output(result)
        return result

    def hadamard_sector_swap(self):
        """E-LOCAL-HADAMARD at T=Q: the sector exchange of the whole display.

        The general split-subset instance is not admitted: a hadamard term for
        any other qubit subset has no derivation (the review-dispositioned split
        condition's row-wise mechanics are out of scope; see
        OPERATIONAL_SEMANTICS.md §4.27).
        """
        swapped = tuple(Row(row.id, opposite_sector_name(row.sector), row.support)
                        for row in self.rows)
        result = CodeState(self.Q, swapped, self.used)
        _validate_output(result)
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
        _validate_output(result)
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
        _validate_output(result)
        return result

    def extend_code(self, new_qubits, additions):
        """E-EXTEND, row-added form: add a disjoint qubit set and ordered,
        canonically minted check rows over Q ∪ Δ (§4.30)."""
        try:
            new_qubits = tuple(new_qubits)
        except TypeError:
            raise Malformed("E-EXTEND takes a new-qubit set and a list of typed additions")
        if not isinstance(additions, (list, tuple)) or not isinstance(new_qubits, (list, tuple)):
            raise Malformed("E-EXTEND takes a new-qubit set and a list of typed additions")
        if any(isinstance(q, bool) or not isinstance(q, int) or q < 0 for q in new_qubits):
            raise Malformed("E-EXTEND new qubits must be nonnegative integers")
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
        _validate_output(result)
        return result


__all__ = [
    'IDENTIFIERS',
    'IDENTIFIER_RANK',
    'identifier_rank',
    'NoDerivation',
    'Malformed',
    '_validate_output',
    'support_mask',
    'commutes',
    'opposite_sector_name',
    'orthogonal',
    'Row',
    'CodeState',
]
