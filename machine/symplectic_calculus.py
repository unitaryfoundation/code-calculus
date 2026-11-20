"""Symplectic state model, move set, and distance ledger for general
(non-CSS) stabilizer codes.

Consumer/model companion to ``machine/priced_calculus.py`` (issue #294 for the
state slice, issue #305 for the move set, the ledger, and the conformance
fixtures). It is not normative. The extended-state layer is a Gate 6 decision
that has not been taken (``spec/GATES.md``, ``SCOPE.md`` section 4), so
nothing in this module is an admitted calculus rule: the moves are
consumer-side operations whose preconditions are checked here and whose
interval rules are derived in
``the symplectic move set (2026-11-10)``. The conformance harness
``machine/experiments/symplectic_conformance_harness.py`` is evidence about
those rules, never a proof.

Representation. A stabilizer code on the qubit labels ``Q`` is a display of
rows, each a Pauli operator up to phase given by its X support and its Z
support (a qubit in both supports carries a Y). ``validate`` checks the list
level (sorted, repeat-free labels and supports inside ``Q``; unique live
identifiers from the fixed enumeration, all in ``used``), pairwise commutation
(even symplectic inner product), and independence over F_2. No distance search
lives in this module; the exhaustive Pauli-distance oracle is in the harness.

Moves. ``SYM-SKIP``, ``SYM-DELETE-CHECK``, ``SYM-ADD-CHECK``, and
``SYM-DIRECT-SUM`` are the symplectic counterparts of the CSS kernel; the
``SYM-`` labels are machine-side names, not taxonomy IDs. The two cross-layer
moves carry the taxonomy IDs of ``spec/TAXONOMY.md`` section 4.3:
``X-SYMPLECTIC-DOUBLE`` (stabilizer code to CSS ``CodeState`` on twice the
qubits) and ``X-SYMPLECTIC-HALVE`` (CSS ``CodeState`` with a fixed-point-free
qubit involution exchanging the sector row spaces, to a stabilizer code on
half the qubits). Both sit at the ``taxonomy-only`` rung; the helpers here
are consumer-side, as ``CodeState.glue`` was before ``E-GLUE``'s transition.

Ledger. ``SymplecticLedger`` carries one interval for the Pauli distance ``d``
(the sector distances ``d_X`` and ``d_Z`` have no meaning off the CSS layer)
and a list of Pauli witnesses. Transport: skip is the identity; an added
check carries the lower endpoint and rebuilds the upper endpoint from
witnesses valid in the child; a deleted check resets the lower endpoint to
zero and carries the upper endpoint; a direct sum takes the minimum of the
endpoints; doubling maps the interval ``[L, U]`` to ``[L, 2U]`` on the full
and both sector intervals of the CSS child; halving maps the CSS full
interval ``[L, U]`` to ``[ceil(L / 2), U]``. A witness is revalidated in the
child before it tightens an upper endpoint, and never widens one.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Tuple

from machine.priced_calculus import (
    IDENTIFIERS,
    CodeState,
    DistanceLedger,
    Interval,
    Malformed,
    NoDerivation,
    Row,
    _min_upper,
    _transport_interval,
    in_span,
    support_mask,
)


# ---------------------------------------------------------------------------
# F_2 vectors
# ---------------------------------------------------------------------------


def _width(Q):
    """Bit width of one Pauli half over the labels ``Q`` (labels, not
    positions, index the bits, so the width is one more than the largest
    label)."""
    return (max(Q) + 1) if Q else 0


def _vector(x_support, z_support, width):
    """Pack an (X support, Z support) pair into one integer: the X half in
    the low ``width`` bits, the Z half in the next ``width`` bits."""
    value = 0
    for q in x_support:
        value |= 1 << q
    for q in z_support:
        value |= 1 << (width + q)
    return value




from machine.gf2 import (  # noqa: E402
    _basis_tuple as _basis_tuple,
    _basis as _basis,
    _rank as _rank,
    _in_span as _in_span,
)


def symplectic_inner_product(a, b):
    """Symplectic inner product, modulo 2, of two (X support, Z support)
    pairs: zero exactly when the two Pauli operators commute."""
    return (len(set(a[0]) & set(b[1])) + len(set(a[1]) & set(b[0]))) % 2


def pauli_weight(x_support, z_support):
    """Weight of the Pauli operator with the given supports: the number of
    qubits it acts on, a Y counted once."""
    return len(set(x_support) | set(z_support))


def _normalize_support(support, what):
    """Shape-check one support the way ``CodeState.add_check`` does: a list
    or tuple (else malformed), sorted (else no derivation), repeat-free (else
    malformed)."""
    if not isinstance(support, (list, tuple)):
        raise Malformed("%s support must be a list or tuple" % what)
    support = tuple(support)
    for q in support:
        if isinstance(q, bool) or not isinstance(q, int) or q < 0:
            raise Malformed("qubit labels must be nonnegative integers")
    if support != tuple(sorted(support)):
        raise NoDerivation("%s support must be sorted" % what)
    if len(set(support)) != len(support):
        raise Malformed("%s support may not repeat qubits" % what)
    return support


def _validate_output(result):
    """A child display that fails validation is a failed premise of the
    move, not malformed input (the inputs were validated already)."""
    try:
        result.validate()
    except ValueError as exc:
        raise NoDerivation(
            "transition output is not a well-formed stabilizer display: %s"
            % exc)


# ---------------------------------------------------------------------------
# State
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SymplecticRow:
    id: str
    x: Tuple[int, ...]
    z: Tuple[int, ...]

    def vector(self, width):
        return _vector(self.x, self.z, width)

    @property
    def weight(self):
        return pauli_weight(self.x, self.z)


class SymplecticState:
    """A presented stabilizer code: labels ``Q``, displayed rows, and the
    ``used`` identifier set (live and retired)."""

    def __init__(self, Q, rows, used=None):
        self.Q = tuple(sorted(Q))
        norm = []
        for r in rows:
            if not isinstance(r, SymplecticRow):
                r = SymplecticRow(r[0], tuple(sorted(r[1])), tuple(sorted(r[2])))
            else:
                r = SymplecticRow(r.id, tuple(sorted(r.x)), tuple(sorted(r.z)))
            norm.append(r)
        self.rows = tuple(norm)
        if used is None:
            used = frozenset(r.id for r in self.rows)
        self.used = frozenset(used)

    # ---- basic properties ----
    def n(self):
        return len(self.Q)

    def width(self):
        return _width(self.Q)

    def vectors(self):
        width = self.width()
        return [r.vector(width) for r in self.rows]

    def k(self):
        return self.n() - _rank(self.vectors())

    def w(self):
        ws = [r.weight for r in self.rows]
        return max(ws) if ws else 0

    def row_by_id(self, identifier):
        for r in self.rows:
            if r.id == identifier:
                return r
        return None

    def validate(self):
        Q = self.Q
        if (any(isinstance(q, bool) or not isinstance(q, int) or q < 0 for q in Q)
                or len(set(Q)) != len(Q)
                or Q != tuple(sorted(Q))):
            raise ValueError("Q must be a finite, strictly increasing set of "
                             "nonnegative qubit labels")
        qset = set(Q)
        live_ids = [r.id for r in self.rows]
        if len(set(live_ids)) != len(live_ids):
            raise ValueError("live row identifiers must be unique")
        if not set(live_ids) <= set(self.used):
            raise ValueError("every live row identifier must be in used")
        if any(identifier not in IDENTIFIERS for identifier in live_ids):
            raise ValueError("live row identifiers must belong to the fixed "
                             "identifier enumeration")
        if any(identifier not in IDENTIFIERS for identifier in self.used):
            raise ValueError("used identifiers must belong to the fixed "
                             "identifier enumeration")
        for r in self.rows:
            for side in (r.x, r.z):
                if any(isinstance(q, bool) or not isinstance(q, int) for q in side):
                    raise ValueError("qubit labels must be integers")
                if len(set(side)) != len(side):
                    raise ValueError("supports may not repeat qubits")
                if tuple(sorted(side)) != side:
                    raise ValueError("supports must be sorted")
            if not (set(r.x) | set(r.z)) <= qset:
                raise ValueError("row support must be contained in Q")
            if not r.x and not r.z:
                raise ValueError("a displayed row may not be the identity")
        # independence: rank == number of rows
        vecs = self.vectors()
        if _rank(vecs) != len(vecs):
            raise ValueError("displayed rows are dependent")
        # symplectic orthogonality: rows commute pairwise
        for i, ri in enumerate(self.rows):
            for rj in self.rows[i + 1:]:
                if symplectic_inner_product((ri.x, ri.z), (rj.x, rj.z)):
                    raise ValueError("symplectic orthogonality violated: rows "
                                     "%s and %s do not commute" % (ri.id, rj.id))
        if self.k() < 0:
            raise ValueError("rank exceeds qubit count")
        return True

    # ---- identifiers ----
    @staticmethod
    def _mint(used):
        """Canonical mint: the first identifier of the enumeration not in
        ``used`` (``spec/STATE_MODEL.md`` I3)."""
        for identifier in IDENTIFIERS:
            if identifier not in used:
                return identifier
        raise NoDerivation("fixed identifier enumeration exhausted")

    # ---- the symplectic kernel moves ----
    def skip(self):
        """``SYM-SKIP``: the identity."""
        return self

    def delete_check(self, identifier):
        """``SYM-DELETE-CHECK``: retire a displayed generator. Its identifier
        stays in ``used``. The deleted generator becomes a logical of the
        child, so the distance cannot rise."""
        row = self.row_by_id(identifier)
        if row is None:
            raise NoDerivation("DisplayedGenerator(%s, pres) fails" % identifier)
        width = self.width()
        others = [r.vector(width) for r in self.rows if r.id != identifier]
        if _in_span(row.vector(width), others):
            raise NoDerivation("Independent(%s; pres) fails" % identifier)
        result = SymplecticState(
            self.Q,
            tuple(r for r in self.rows if r.id != identifier),
            self.used,
        )
        _validate_output(result)
        return result

    def add_check(self, x_support, z_support):
        """``SYM-ADD-CHECK``: display a new generator. It must act on some
        qubit of ``Q``, commute with every displayed row, and lie outside
        their span; its identifier is the canonical mint."""
        x = _normalize_support(x_support, "added X")
        z = _normalize_support(z_support, "added Z")
        if not set(x) <= set(self.Q) or not set(z) <= set(self.Q):
            raise NoDerivation("added row is not a Pauli operator on Q")
        if not x and not z:
            raise NoDerivation("added row is the identity")
        for r in self.rows:
            if symplectic_inner_product((x, z), (r.x, r.z)):
                raise NoDerivation("added row does not commute with displayed "
                                   "row %s" % r.id)
        width = self.width()
        if _in_span(_vector(x, z, width), self.vectors()):
            raise NoDerivation("added row lies in the stabilizer span")
        identifier = self._mint(self.used)
        result = SymplecticState(
            self.Q,
            self.rows + (SymplecticRow(identifier, x, z),),
            self.used | frozenset((identifier,)),
        )
        _validate_output(result)
        return result

    @staticmethod
    def direct_sum(left, right):
        """``SYM-DIRECT-SUM``: disjoint qubit namespaces and disjoint
        ``used`` sets; rows and ``used`` are united."""
        if not isinstance(left, SymplecticState) or not isinstance(right, SymplecticState):
            raise Malformed("SYM-DIRECT-SUM requires two SymplecticState inputs")
        if set(left.Q) & set(right.Q):
            raise NoDerivation("SYM-DIRECT-SUM qubit namespaces overlap")
        if set(left.used) & set(right.used):
            raise NoDerivation("SYM-DIRECT-SUM used sets overlap")
        result = SymplecticState(
            tuple(sorted(set(left.Q) | set(right.Q))),
            left.rows + right.rows,
            left.used | right.used,
        )
        _validate_output(result)
        return result

    # ---- the cross-layer moves of spec/TAXONOMY.md section 4.3 ----
    def doubling_pairs(self):
        """The qubit pairing ``X-SYMPLECTIC-DOUBLE`` creates: each label
        ``q`` is paired with its copy ``q + width``. The copy-swap involution
        always makes the doubled code halvable back."""
        width = self.width()
        return tuple((q, q + width) for q in self.Q)

    def double(self):
        """``X-SYMPLECTIC-DOUBLE``: the CSS code on two copies of ``Q`` whose
        X checks are the rows ``(A | B)`` and whose Z checks are the rows
        ``(B | A)`` of the symplectic check matrix ``H = (A | B)``. The
        output is a ``CodeState``; its identifiers are minted canonically
        over this state's ``used`` set, X half first."""
        width = self.width()
        Q2 = tuple(sorted(self.Q + tuple(q + width for q in self.Q)))
        used = set(self.used)
        rows = []
        for r in self.rows:
            support = tuple(sorted(tuple(r.x) + tuple(q + width for q in r.z)))
            identifier = self._mint(used)
            used.add(identifier)
            rows.append(Row(identifier, "X", support))
        for r in self.rows:
            support = tuple(sorted(tuple(r.z) + tuple(q + width for q in r.x)))
            identifier = self._mint(used)
            used.add(identifier)
            rows.append(Row(identifier, "Z", support))
        result = CodeState(Q2, tuple(rows), frozenset(used))
        try:
            result.validate()
        except Malformed as exc:
            raise NoDerivation(
                "doubled display is not a well-formed CSS display: %s" % exc)
        return result

    @staticmethod
    def _involution(css, pairs):
        """Read the typed halving data: a fixed-point-free involution of the
        CSS state's qubits, given as pairs. Returns the map from a label to
        its partner and the map from a label to its pair's representative
        (the smaller label)."""
        if not isinstance(pairs, (list, tuple)):
            raise Malformed("halving data must be a list of qubit pairs")
        partner = {}
        rep = {}
        for pair in pairs:
            if (not isinstance(pair, (list, tuple)) or len(pair) != 2
                    or any(isinstance(q, bool) or not isinstance(q, int) for q in pair)):
                raise Malformed("each halving pair must be two integer labels")
            a, b = pair
            if a == b:
                raise NoDerivation("halving involution has a fixed point: %s" % a)
            if a in partner or b in partner:
                raise NoDerivation("halving pairs name a qubit twice")
            partner[a] = b
            partner[b] = a
            lo = min(a, b)
            rep[a] = lo
            rep[b] = lo
        if set(partner) != set(css.Q):
            raise NoDerivation("halving pairs do not cover the qubit set exactly")
        return partner, rep

    @classmethod
    def halve(cls, css, pairs):
        """``X-SYMPLECTIC-HALVE``: fold a CSS ``CodeState`` along a
        fixed-point-free involution that exchanges the two sector row spaces.
        Each pair ``{q, q'}`` (``q < q'``) becomes the qubit ``q``; a parent
        X check with support ``s`` becomes the row with X support
        ``s ∩ reps`` and Z support ``{q : q' ∈ s}``. The folded rows are
        minted canonically over the parent's ``used`` set."""
        if not isinstance(css, CodeState):
            raise Malformed("X-SYMPLECTIC-HALVE requires a CodeState input")
        css.validate()
        partner, rep = cls._involution(css, pairs)
        x_masks = [row.mask for row in css.sector_rows("X")]
        z_masks = [row.mask for row in css.sector_rows("Z")]
        for row in css.sector_rows("X"):
            image = support_mask(tuple(sorted(partner[q] for q in row.support)))
            if not in_span(image, z_masks):
                raise NoDerivation("the involution does not map the X row "
                                   "space into the Z row space (row %s)" % row.id)
        for row in css.sector_rows("Z"):
            image = support_mask(tuple(sorted(partner[q] for q in row.support)))
            if not in_span(image, x_masks):
                raise NoDerivation("the involution does not map the Z row "
                                   "space into the X row space (row %s)" % row.id)
        reps = tuple(sorted(set(rep.values())))
        used = set(css.used)
        rows = []
        for row in css.sector_rows("X"):
            x = tuple(sorted(q for q in row.support if rep[q] == q))
            z = tuple(sorted(rep[q] for q in row.support if rep[q] != q))
            identifier = cls._mint(used)
            used.add(identifier)
            rows.append(SymplecticRow(identifier, x, z))
        result = cls(reps, tuple(rows), frozenset(used))
        _validate_output(result)
        return result

    # ---- CSS interop (issue #294) ----
    @classmethod
    def from_css(cls, state):
        """Convert a CSS ``CodeState`` to a symplectic state (display order
        X rows, then Z rows)."""
        if not isinstance(state, CodeState):
            raise TypeError("expected a CodeState")
        rows = []
        for r in state.rows:
            if r.sector == "X":
                rows.append(SymplecticRow(r.id, tuple(r.support), ()))
            elif r.sector == "Z":
                rows.append(SymplecticRow(r.id, (), tuple(r.support)))
        return cls(state.Q, rows, state.used)

    def to_css(self):
        """Return a CSS ``CodeState`` if every check is pure X or pure Z."""
        rows = []
        for r in self.rows:
            if r.z and r.x:
                raise ValueError("not a CSS code: mixed X/Z check")
            if r.x and not r.z:
                rows.append(Row(r.id, "X", r.x))
            elif r.z and not r.x:
                rows.append(Row(r.id, "Z", r.z))
        return CodeState(self.Q, tuple(rows), self.used)

    def as_json(self):
        return {
            "Q": list(self.Q),
            "rows": [{"id": r.id, "x": list(r.x), "z": list(r.z)} for r in self.rows],
            "used": sorted(self.used),
        }

    def __repr__(self):
        return ("SymplecticState(n=%d, k=%d, rows=%d)"
                % (self.n(), self.k(), len(self.rows)))


def is_css(state):
    return all((not r.x or not r.z) for r in state.rows)


# ---------------------------------------------------------------------------
# Witnesses and the ledger
# ---------------------------------------------------------------------------


def validate_pauli_witness(state, x_support, z_support, claimed_weight):
    """A Pauli witness is an upper bound on the distance: it commutes with
    every displayed row, lies outside the stabilizer span, and has the
    claimed weight. Anything else is a failed premise, not a widened
    interval."""
    x = tuple(sorted(x_support))
    z = tuple(sorted(z_support))
    if (len(set(x)) != len(x) or len(set(z)) != len(z)
            or not set(x) <= set(state.Q) or not set(z) <= set(state.Q)):
        raise NoDerivation("witness support is not a subset of Q")
    if not x and not z:
        raise NoDerivation("witness is the identity")
    if pauli_weight(x, z) != claimed_weight:
        raise NoDerivation("witness weight does not match its support")
    for r in state.rows:
        if symplectic_inner_product((x, z), (r.x, r.z)):
            raise NoDerivation("witness does not commute with displayed row %s" % r.id)
    if _in_span(_vector(x, z, state.width()), state.vectors()):
        raise NoDerivation("witness lies in the stabilizer span")
    return True


class SymplecticLedger:
    """Consumer-side interval for the Pauli distance of a symplectic state,
    with Pauli witnesses and recorded conditions."""

    MOVES = ("SYM-SKIP", "SYM-ADD-CHECK", "SYM-DELETE-CHECK")

    def __init__(self, full, witnesses=None, conditions=None):
        if not isinstance(full, Interval):
            raise Malformed("ledger interval must be an Interval")
        self.full = full
        self.witnesses = [dict(w) for w in (witnesses or [])]
        self.conditions = list(conditions or [])

    def copy(self):
        return SymplecticLedger(self.full,
                                [dict(w) for w in self.witnesses],
                                list(self.conditions))

    def record_witness(self, state, x_support, z_support, source="consumer witness"):
        x = tuple(sorted(x_support))
        z = tuple(sorted(z_support))
        weight = pauli_weight(x, z)
        validate_pauli_witness(state, x, z, weight)
        self.witnesses.append({"x": list(x), "z": list(z), "value": weight,
                               "source": source})

    def _valid_witnesses(self, state):
        valid = []
        seen = set()
        for witness in self.witnesses:
            x = tuple(sorted(witness["x"]))
            z = tuple(sorted(witness["z"]))
            try:
                validate_pauli_witness(state, x, z, witness["value"])
            except NoDerivation:
                continue
            if (x, z) not in seen:
                valid.append({"x": list(x), "z": list(z), "value": witness["value"],
                              "source": witness.get("source", "consumer witness")})
                seen.add((x, z))
        return valid

    def _tightened(self, state, interval):
        """Tighten the upper endpoint by the lightest witness valid in
        ``state``; never widen."""
        valid = self._valid_witnesses(state)
        if not valid:
            return interval
        best = min(w["value"] for w in valid)
        return _transport_interval(interval.lower, _min_upper(interval.upper, best))

    def propagate(self, operation, new_state):
        """Transport through one unary move of the symplectic kernel."""
        if not isinstance(operation, dict):
            raise Malformed("operation must be an object")
        op = operation.get("op")
        out = self.copy()
        if op == "SYM-SKIP":
            pass
        elif op == "SYM-ADD-CHECK":
            # An added check never lowers the distance (the child's logicals
            # are logicals of the parent): the lower endpoint carries, the
            # upper endpoint is rebuilt from witnesses valid in the child.
            out.full = Interval(self.full.lower, None)
        elif op == "SYM-DELETE-CHECK":
            # A deleted generator is a logical of the child, so the
            # distance cannot rise: the upper endpoint carries, the lower
            # endpoint resets to zero.
            out.full = Interval(0 if self.full.lower is not None else None,
                                self.full.upper)
        else:
            raise Malformed("operation is outside the symplectic move set: %s" % op)
        out.full = out._tightened(new_state, out.full)
        return out

    @staticmethod
    def direct_sum(left, right):
        """``SYM-DIRECT-SUM``: the distance of a direct sum is the minimum
        of the factors' distances, so both endpoints combine by ``min``. A
        factor's witness, extended by the identity, is a witness of the
        sum."""
        if not isinstance(left, SymplecticLedger) or not isinstance(right, SymplecticLedger):
            raise Malformed("SYM-DIRECT-SUM requires two SymplecticLedger inputs")
        return SymplecticLedger(
            Interval(_min_upper(left.full.lower, right.full.lower),
                     _min_upper(left.full.upper, right.full.upper)),
            left.witnesses + right.witnesses,
            left.conditions + right.conditions,
        )

    def double(self, state, css_state):
        """``X-SYMPLECTIC-DOUBLE`` transport into a CSS ``DistanceLedger``.
        Every X logical of the doubled code is a logical of the parent read
        in the two copies, and a parent logical of weight ``w`` gives an X
        and a Z logical of the double of weight at most ``2w``; so each
        sector distance and the full distance lie in ``[d, 2d]``, and
        ``[L, U]`` maps to ``[L, 2U]``. Parent witnesses are converted and
        revalidated in the child."""
        lower = self.full.lower
        upper = None if self.full.upper is None else 2 * self.full.upper
        interval = Interval(lower, upper)
        ledger = DistanceLedger(interval, {"X": interval, "Z": interval},
                                witnesses={"X": [], "Z": []},
                                conditions=list(self.conditions))
        width = state.width()
        for witness in self._valid_witnesses(state):
            x = witness["x"]
            z = witness["z"]
            x_side = tuple(sorted(set(x) | {q + width for q in z}))
            z_side = tuple(sorted(set(z) | {q + width for q in x}))
            for side, support in (("X", x_side), ("Z", z_side)):
                try:
                    ledger.record_witness(css_state, side, support,
                                          source="doubled %s" % witness.get("source", "witness"))
                except NoDerivation:
                    continue
        for side in ("X", "Z"):
            valid = ledger._valid_witnesses(css_state, side)
            if valid:
                best = min(w["value"] for w in valid)
                ledger.sector[side] = _transport_interval(
                    ledger.sector[side].lower,
                    _min_upper(ledger.sector[side].upper, best))
        ledger.full = _transport_interval(
            ledger.full.lower,
            _min_upper(ledger.full.upper,
                       _min_upper(ledger.sector["X"].upper, ledger.sector["Z"].upper)))
        ledger.conditions.append({
            "cell": "X-SYMPLECTIC-DOUBLE interval",
            "status": "machine-side",
            "source": "the symplectic move set (2026-11-10)",
        })
        return ledger

    @classmethod
    def halve(cls, css_ledger, css_state, sym_state, pairs):
        """``X-SYMPLECTIC-HALVE`` transport from a CSS ``DistanceLedger``.
        The parent is the double of the child up to relabeling, so the
        parent's distance lies in ``[d', 2d']``; hence ``[L, U]`` on the
        parent's full distance maps to ``[ceil(L / 2), U]``. Parent sector
        witnesses fold to Pauli witnesses and are revalidated in the
        child."""
        if not isinstance(css_ledger, DistanceLedger):
            raise Malformed("X-SYMPLECTIC-HALVE requires a DistanceLedger input")
        lower = css_ledger.full.lower
        if lower is not None:
            lower = (lower + 1) // 2
        interval = Interval(lower, css_ledger.full.upper)
        out = cls(interval, conditions=list(css_ledger.conditions))
        _partner, rep = SymplecticState._involution(css_state, pairs)
        for side in ("X", "Z"):
            for witness in css_ledger._valid_witnesses(css_state, side):
                support = witness["support"]
                on_reps = tuple(sorted(q for q in support if rep[q] == q))
                on_partners = tuple(sorted(rep[q] for q in support if rep[q] != q))
                if side == "X":
                    x, z = on_reps, on_partners
                else:
                    x, z = on_partners, on_reps
                try:
                    out.record_witness(sym_state, x, z,
                                       source="halved %s" % witness.get("source", "witness"))
                except NoDerivation:
                    continue
        out.full = out._tightened(sym_state, out.full)
        out.conditions.append({
            "cell": "X-SYMPLECTIC-HALVE interval",
            "status": "machine-side",
            "source": "the symplectic move set (2026-11-10)",
        })
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
            "conditional_inputs": list(self.conditions),
            "witnesses": [dict(w) for w in self.witnesses],
        }


# ---------------------------------------------------------------------------
# Operation dispatch (fixtures)
# ---------------------------------------------------------------------------


def apply_symplectic_operation(state, operation):
    """Apply one move named by an operation object; the cross-layer moves
    change the state type (``X-SYMPLECTIC-DOUBLE`` returns a ``CodeState``,
    ``X-SYMPLECTIC-HALVE`` takes one)."""
    if not isinstance(operation, dict):
        raise Malformed("operation must be an object")
    op = operation.get("op")
    if op == "SYM-SKIP":
        return state.skip()
    if op == "SYM-DELETE-CHECK":
        return state.delete_check(operation.get("row_id"))
    if op == "SYM-ADD-CHECK":
        return state.add_check(operation.get("x", []), operation.get("z", []))
    if op == "SYM-DIRECT-SUM":
        return SymplecticState.direct_sum(state, operation.get("right_state"))
    if op == "X-SYMPLECTIC-DOUBLE":
        return state.double()
    if op == "X-SYMPLECTIC-HALVE":
        return SymplecticState.halve(state, operation.get("pairs"))
    raise Malformed("operation is outside the symplectic move set: %s" % op)
