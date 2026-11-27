#!/usr/bin/env python3
"""Falsification harness for the two gate-realization rows (issues #452, #543).

`GATE_REALIZATION_ROWS.md` and `spec/JUDGMENT_LAYER.md` §2h state two
judgment rows drawn from arXiv 2610.17612 and derive each from the CSS display
alone. This script checks the derived criteria against an oracle that does not
use them:

* Survival row. A gate is a product of commuting Pauli rotations
  exp(i eps_j theta_j G_j). At theta_j = pi/4 the note derives that the gate
  preserves the codespace iff, for every displayed row g, the Pauli
  V_g = prod over the generators that anticommute with g of (i eps_j G_j)
  is an element of the stabilizer group, and that a gate preserving the
  parent's codespace survives `C-ADD-CHECK` iff that one condition holds at
  the added row. `oracle_preserves` decides preservation by applying the
  rotations to state vectors, with no Pauli-group reasoning.
* Weight row. For generators with one common syndrome, some product
  G_1 G_j outside the stabilizer group up to sign forces
  w_max >= ceil(d / 2). `exact_distance` enumerates logicals.
* Frame-reading extension (issue #572, `stdCSS-3` / `v0.3.2`). Lemmas 5-11 of
  `spec/OPERATIONAL_SEMANTICS.md` §4.37 decide preservation at every angle
  from the sign patterns a stabilizer group realizes, and read the
  logical-witness frame `log` (`spec/STATE_MODEL.md` §1a) for frame-sector
  preservation, the logical action of a gate (sector phase and conjugation
  image), and addressability. `oracle_*` functions decide the same
  predicates on state vectors.

Angle domain (review of PR #665). The any-angle tests are decision
procedures only for angles that are rational multiples of pi. The derived
functions of the frame-reading extension take `thetas` as those multiples,
`int` or `Fraction` coefficients with theta_j = thetas[j] * pi, and decide
Phi(l) in pi Z as the integrality of a rational, with no floating-point
tolerance; any other angle is outside the decision domain (`not yet
defined`) and is refused. The oracles take radians (`radians(thetas)`) and
stay floating-point: they are evidence, not the decision.

Agreement on the sweep is evidence that the criteria are derived and
transcribed as stated, not a proof (AGENTS.md).
"""

import argparse
import cmath
import itertools
import json
import math
import random
import sys
from fractions import Fraction


def popcount(x):
    return bin(x).count("1")


class Pauli:
    """The operator i^k X(x) Z(z), with `x` and `z` bitmasks over the qubits."""

    __slots__ = ("x", "z", "k")

    def __init__(self, x, z, k=0):
        self.x = x
        self.z = z
        self.k = k % 4

    def __mul__(self, other):
        # Z(z1) X(x2) = (-1)^{|z1 & x2|} X(x2) Z(z1).
        k = self.k + other.k + 2 * popcount(self.z & other.x)
        return Pauli(self.x ^ other.x, self.z ^ other.z, k)

    def __eq__(self, other):
        return (self.x, self.z, self.k) == (other.x, other.z, other.k)

    def __hash__(self):
        return hash((self.x, self.z, self.k))

    def __repr__(self):
        return f"Pauli(x={self.x:b}, z={self.z:b}, k={self.k})"

    def is_hermitian(self):
        return (self.k - popcount(self.x & self.z)) % 2 == 0

    def anticommutes(self, other):
        return (popcount(self.x & other.z) + popcount(self.z & other.x)) % 2 == 1

    def weight(self):
        return popcount(self.x | self.z)

    def scaled(self, k):
        return Pauli(self.x, self.z, self.k + k)


IDENTITY = Pauli(0, 0, 0)


def pauli_from_string(text, sign=1):
    """A Hermitian Pauli from a string over I, X, Y, Z; qubit 0 is leftmost."""
    x = z = k = 0
    for i, letter in enumerate(text):
        if letter in "XY":
            x |= 1 << i
        if letter in "ZY":
            z |= 1 << i
        if letter == "Y":
            k += 1  # Y = i X Z
    if sign == -1:
        k += 2
    return Pauli(x, z, k)


def mask(support):
    out = 0
    for q in support:
        out |= 1 << q
    return out


class Display:
    """A CSS display: `n` qubits and the X-row and Z-row supports as bitmasks."""

    def __init__(self, n, x_rows, z_rows):
        self.n = n
        self.x_rows = list(x_rows)
        self.z_rows = list(z_rows)

    @classmethod
    def from_supports(cls, n, x_supports, z_supports):
        return cls(n, [mask(s) for s in x_supports], [mask(s) for s in z_supports])

    @classmethod
    def from_code_state(cls, state):
        """Build a Display from a consumer CodeState, indexing qubits in state.Q order."""
        q_index = {q: idx for idx, q in enumerate(state.Q)}
        x_supports = [[q_index[q] for q in r.support] for r in state.sector_rows("X")]
        z_supports = [[q_index[q] for q in r.support] for r in state.sector_rows("Z")]
        return cls.from_supports(len(state.Q), x_supports, z_supports)

    def rows(self):
        return [Pauli(m, 0) for m in self.x_rows] + [Pauli(0, m) for m in self.z_rows]

    def well_formed(self):
        return all(popcount(a & b) % 2 == 0 for a in self.x_rows for b in self.z_rows)

    def add(self, sector, row):
        if sector == "X":
            return Display(self.n, self.x_rows + [row], self.z_rows)
        return Display(self.n, self.x_rows, self.z_rows + [row])

    def delete(self, sector, index):
        if sector == "X":
            return Display(self.n, self.x_rows[:index] + self.x_rows[index + 1:], self.z_rows)
        return Display(self.n, self.x_rows, self.z_rows[:index] + self.z_rows[index + 1:])


def reduce_basis(masks):
    """An echelon basis of the GF(2) span of `masks`, keyed by leading bit."""
    basis = {}
    for m in masks:
        while m:
            lead = m.bit_length() - 1
            if lead not in basis:
                basis[lead] = m
                break
            m ^= basis[lead]
    return basis


def in_span(basis, m):
    while m:
        lead = m.bit_length() - 1
        if lead not in basis:
            return False
        m ^= basis[lead]
    return True


def rank(masks):
    return len(reduce_basis(masks))


def in_stabilizer(display, pauli):
    """Whether `pauli` is an element of the stabilizer group of the display.

    Every product of displayed rows is X(a) Z(b) with phase exponent 0, `a`
    in the span of the X-rows and `b` in the span of the Z-rows.
    """
    return (
        pauli.k == 0
        and in_span(reduce_basis(display.x_rows), pauli.x)
        and in_span(reduce_basis(display.z_rows), pauli.z)
    )


def in_stabilizer_up_to_sign(display, pauli):
    return in_span(reduce_basis(display.x_rows), pauli.x) and in_span(
        reduce_basis(display.z_rows), pauli.z
    )


def check_gate(gens, eps):
    assert len(gens) == len(eps)
    assert all(e in (1, -1) for e in eps)
    assert all(g.is_hermitian() for g in gens)
    assert all(not a.anticommutes(b) for a in gens for b in gens)


def conditioned_pauli(gens, eps, row):
    """V_row at theta = pi/4: the product of i eps_j G_j over the generators
    that anticommute with `row`. Then U^dagger row U = row V_row."""
    out = IDENTITY
    for g, e in zip(gens, eps):
        if g.anticommutes(row):
            out = out * g.scaled(1 if e == 1 else 3)
    return out


def preserves_pi4(display, gens, eps):
    """The derived criterion: the gate prod exp(i eps_j (pi/4) G_j) preserves
    the codespace iff V_g is a stabilizer for every displayed row g."""
    check_gate(gens, eps)
    return all(in_stabilizer(display, conditioned_pauli(gens, eps, g)) for g in display.rows())


def survives_addition(display, gens, eps, sector, row):
    """The survival test at theta = pi/4. For a gate that preserves the
    codespace of `display`, whether it preserves the codespace after
    `C-ADD-CHECK` adds `row` in `sector`: one stabilizer-membership test at
    the added row."""
    check_gate(gens, eps)
    added = Pauli(row, 0) if sector == "X" else Pauli(0, row)
    return in_stabilizer(display.add(sector, row), conditioned_pauli(gens, eps, added))


def addition_survival_verdict(display, gens, eps, sector, row, thetas=None, angles=None):
    """Evaluate the `C-ADD-CHECK` gate-survival cell of
    `spec/JUDGMENT_LAYER.md` §2h for a gate preserving `display`. `thetas`
    are angles in radians (floating point); `angles` are the same angles as
    rational multiples of pi (`int` or `Fraction`, theta_j = angles[j] * pi),
    the decision domain of Corollary 7.1. Pass at most one of them.

    * If every generator commutes with the added row: returns `"carries"`
      (holds at every angle theta_j >= 0).
    * Else if the angles are omitted or every angle is pi/4: returns
      `"carries"` when V_s is in the child stabilizer group and
      `"does_not_carry"` otherwise.
    * Else, with rational `angles`: the any-angle test of Corollary 7.1
      (§4.37, issue #572) at the added row, `"carries"` when
      sum_{j in J(s)} eps_j a_j l_j is an integer for every sign pattern l
      the child stabilizer group realizes on J(s), `"does_not_carry"`
      otherwise.
    * Else (radian `thetas`, not all pi/4): `"not_yet_defined"`, since the
      angles are not given in the decision domain.
    """
    check_gate(gens, eps)
    if sector not in ("X", "Z"):
        raise ValueError("sector must be 'X' or 'Z'")
    if not isinstance(row, int) or isinstance(row, bool) or row <= 0 or row >= (1 << display.n):
        raise ValueError("added row mask must be a nonzero bitmask within display.n qubits")
    opposite = display.z_rows if sector == "X" else display.x_rows
    same = display.x_rows if sector == "X" else display.z_rows
    if any(popcount(row & r) % 2 == 1 for r in opposite):
        raise ValueError("added row does not commute with opposite-sector display rows")
    if in_span(reduce_basis(same), row):
        raise ValueError("added row is not independent of same-sector display rows")
    if thetas is not None and angles is not None:
        raise ValueError("pass radian thetas or rational angles, not both")
    if thetas is not None:
        if len(thetas) != len(gens) or any(
            isinstance(t, bool) or not isinstance(t, (int, float)) or t < 0 for t in thetas
        ):
            raise ValueError("thetas must be a sequence of len(gens) nonnegative numbers")
    if angles is not None:
        check_angles(gens, angles)
    added = Pauli(row, 0) if sector == "X" else Pauli(0, row)
    if all(not g.anticommutes(added) for g in gens):
        return "carries"
    if angles is not None:
        quarter = all(Fraction(a) == Fraction(1, 4) for a in angles)
    else:
        quarter = thetas is None or all(
            math.isclose(t, math.pi / 4, rel_tol=0.0, abs_tol=1e-12) for t in thetas
        )
    if quarter:
        return "carries" if survives_addition(display, gens, eps, sector, row) else "does_not_carry"
    if angles is None:
        return "not_yet_defined"
    return (
        "carries"
        if survives_addition_any_angle(display, gens, eps, angles, sector, row)
        else "does_not_carry"
    )


def syndrome(display, pauli):
    return tuple(pauli.anticommutes(g) for g in display.rows())


def equal_syndrome(display, gens):
    """All generators have one common nonzero syndrome."""
    first = syndrome(display, gens[0])
    return any(first) and all(syndrome(display, g) == first for g in gens)


def nontrivial(display, gens):
    """Some product G_1 G_j is outside the stabilizer group up to sign."""
    return any(not in_stabilizer_up_to_sign(display, gens[0] * g) for g in gens[1:])


def w_max(gens):
    return max(g.weight() for g in gens)


def weight_floor(d):
    """The candidate weight row's bound: ceil(d / 2)."""
    return (d + 1) // 2


def exact_distance(display):
    """The least weight of a logical of either sector, or None when k = 0."""
    x_basis = reduce_basis(display.x_rows)
    z_basis = reduce_basis(display.z_rows)
    best = None
    for m in range(1, 1 << display.n):
        w = popcount(m)
        if best is not None and w >= best:
            continue
        x_logical = all(popcount(m & r) % 2 == 0 for r in display.z_rows) and not in_span(
            x_basis, m
        )
        z_logical = all(popcount(m & r) % 2 == 0 for r in display.x_rows) and not in_span(
            z_basis, m
        )
        if x_logical or z_logical:
            best = w
    return best


# The oracle: state vectors, no Pauli-group reasoning.


def apply_pauli(pauli, vec):
    phase = (1, 1j, -1, -1j)[pauli.k]
    out = [0j] * len(vec)
    for b, amp in enumerate(vec):
        if amp != 0:
            sign = -1 if popcount(pauli.z & b) % 2 else 1
            out[b ^ pauli.x] += phase * sign * amp
    return out


def apply_rotation(pauli, angle, vec):
    """exp(i angle P) for a Hermitian Pauli P: cos(angle) + i sin(angle) P."""
    moved = apply_pauli(pauli, vec)
    c, s = math.cos(angle), 1j * math.sin(angle)
    return [c * a + s * b for a, b in zip(vec, moved)]


def codespace_vectors(display):
    """A spanning set of the codespace: the projections of the basis states."""
    out = []
    for b in range(1 << display.n):
        vec = [0j] * (1 << display.n)
        vec[b] = 1
        for g in display.rows():
            moved = apply_pauli(g, vec)
            vec = [(a + m) / 2 for a, m in zip(vec, moved)]
        if any(abs(a) > 1e-12 for a in vec):
            out.append(vec)
    return out


def oracle_preserves(display, gens, eps, thetas, tol=1e-9):
    """Whether prod exp(i eps_j theta_j G_j) maps the codespace into itself."""
    for vec in codespace_vectors(display):
        image = vec
        for g, e, t in zip(gens, eps, thetas):
            image = apply_rotation(g, e * t, image)
        for row in display.rows():
            moved = apply_pauli(row, image)
            if any(abs(a - b) > tol for a, b in zip(image, moved)):
                return False
    return True


# Frame-reading extension (issue #572, `stdCSS-3` / `v0.3.2`): Lemmas 5-11 of
# `spec/OPERATIONAL_SEMANTICS.md` §4.37 and the predicates of
# `spec/JUDGMENT_LAYER.md` §2h, Rows C-F.
#
# A frame is a list of entries (sector, mask, eig): the logical-witness field
# `log` of `spec/STATE_MODEL.md` §1a, with `eig` in {+1, -1} the eigenvalue.
# A gate is (gens, eps, thetas) as above.


def inverse(pauli):
    """(i^k X(x) Z(z))^{-1} = i^{-k} (-1)^{|x & z|} X(x) Z(z)."""
    return Pauli(pauli.x, pauli.z, -pauli.k + 2 * popcount(pauli.x & pauli.z))


def sector_pauli(sector, m):
    return Pauli(m, 0) if sector == "X" else Pauli(0, m)


def entry_pauli(entry):
    sector, m, _ = entry
    return sector_pauli(sector, m)


def is_logical(display, sector, m):
    """A sigma-vector is a sigma-logical: even overlap with every row of the
    other sector, and outside the span of the rows of its own sector."""
    opposite = display.z_rows if sector == "X" else display.x_rows
    same = display.x_rows if sector == "X" else display.z_rows
    return (
        m != 0
        and all(popcount(m & r) % 2 == 0 for r in opposite)
        and not in_span(reduce_basis(same), m)
    )


def frame_well_formed(display, frame):
    """(W1) every entry is a logical of its sector of `display`, and (W2) no
    two entries of one sector lie in one class (STATE_MODEL.md §1a)."""
    for sector, m, eig in frame:
        if sector not in ("X", "Z") or eig not in (1, -1):
            return False
        if not is_logical(display, sector, m):
            return False
    for i, (s1, m1, _) in enumerate(frame):
        same = reduce_basis(display.x_rows if s1 == "X" else display.z_rows)
        for s2, m2, _ in frame[i + 1:]:
            if s1 == s2 and in_span(same, m1 ^ m2):
                return False
    return True


def frame_commuting(frame):
    """(F1) every X-entry has even overlap with every Z-entry."""
    xs = [m for s, m, _ in frame if s == "X"]
    zs = [m for s, m, _ in frame if s == "Z"]
    return all(popcount(a & b) % 2 == 0 for a in xs for b in zs)


class SignedSpan:
    """A GF(2) span whose generators carry a sign bit. `consistent` is False
    once some combination of generators sums to zero with sign bit 1 (F2)."""

    def __init__(self):
        self.basis = {}
        self.consistent = True

    def reduce(self, m, bit=0):
        while m:
            lead = m.bit_length() - 1
            if lead not in self.basis:
                return m, bit
            bm, bb = self.basis[lead]
            m ^= bm
            bit ^= bb
        return 0, bit

    def add(self, m, bit=0):
        m, bit = self.reduce(m, bit)
        if m == 0:
            if bit:
                self.consistent = False
            return
        self.basis[m.bit_length() - 1] = (m, bit)


class StabilizerGroup:
    """S(C), or the frame group S_F(C) generated by S(C) and the operators
    eig * sigma(v) of the frame entries (Lemma 8). Every element is
    chi_X(a) chi_Z(b) X(a) Z(b), with chi read off the sign bits."""

    def __init__(self, display, frame=()):
        self.x = SignedSpan()
        self.z = SignedSpan()
        for m in display.x_rows:
            self.x.add(m)
        for m in display.z_rows:
            self.z.add(m)
        for sector, m, eig in frame:
            (self.x if sector == "X" else self.z).add(m, 0 if eig == 1 else 1)
        self.consistent = self.x.consistent and self.z.consistent and frame_commuting(frame)

    def sign(self, pauli):
        """The c in {+1, -1} with c * pauli in the group, or None when
        neither sign is. Meaningful only on a consistent group."""
        rx, bx = self.x.reduce(pauli.x)
        rz, bz = self.z.reduce(pauli.z)
        if rx or rz or pauli.k % 2:
            return None
        return -1 if ((bx ^ bz) + pauli.k // 2) % 2 else 1

    def contains(self, pauli):
        return self.sign(pauli) == 1


def frame_consistent(display, frame):
    """Lemma 8: the frame sector V_F(C) is nonzero iff the frame is well
    formed, its entries commute pairwise (F1), and its eigenvalues respect
    every relation among entries of one sector modulo the rows (F2)."""
    return frame_well_formed(display, frame) and StabilizerGroup(display, frame).consistent


def gate_product(gens, subset):
    out = IDENTITY
    for j in subset:
        out = out * gens[j]
    return out


def realized_patterns(group, gens, indices):
    """Lemma 6. The sign patterns l in {+1, -1}^indices whose joint
    eigenspace E_l of the generators meets the codespace V* of `group`: those
    with prod_{j in T} l_j = c_T for every subset T whose product P_T has
    c_T P_T in the group. Brute force over 2^|indices| patterns."""
    indices = list(indices)
    m = len(indices)
    constraints = []
    for bits in range(1, 1 << m):
        c = group.sign(gate_product(gens, [indices[i] for i in range(m) if bits >> i & 1]))
        if c is not None:
            constraints.append((bits, c))
    out = []
    for lbits in range(1 << m):
        if all((-1) ** popcount(lbits & bits) == c for bits, c in constraints):
            out.append(tuple(-1 if lbits >> i & 1 else 1 for i in range(m)))
    return out


def phase_sum(eps, thetas, indices, pattern):
    """Phi(l) / pi = sum_{j in indices} eps_j a_j l_j, exactly, for angles
    theta_j = a_j pi given by their rational coefficients a_j."""
    return sum((eps[j] * Fraction(thetas[j]) * l for j, l in zip(indices, pattern)), Fraction(0))


def in_pi_z(r):
    """Phi = r pi lies in pi Z iff the rational r is an integer."""
    return Fraction(r).denominator == 1


def half_turns(r):
    """The representative of r modulo 2 in [0, 2): exp(i r pi) is the root of
    unity it names."""
    return Fraction(r) % 2


def root_of_unity(r):
    """exp(i r pi) as a complex number, for comparison with the oracles."""
    return cmath.exp(1j * math.pi * float(half_turns(r)))


def radians(thetas):
    """The radian angles of rational multiples of pi, for the oracles."""
    return [float(t) * math.pi for t in thetas]


def check_angles(gens, thetas):
    """The decision domain: one nonnegative rational multiple of pi per
    generator, given as an `int` or `Fraction` coefficient. A float is
    refused: membership of Phi in pi Z is not decided on it."""
    if len(thetas) != len(gens) or any(
        isinstance(t, bool) or not isinstance(t, (int, Fraction)) or t < 0 for t in thetas
    ):
        raise ValueError(
            "angles must be len(gens) nonnegative rational multiples of pi "
            "(int or Fraction coefficients); other angles are outside the "
            "decision domain (not yet defined)"
        )


def anticommuting(gens, pauli):
    """J(P): the indices of the generators that anticommute with P."""
    return [j for j, g in enumerate(gens) if g.anticommutes(pauli)]


def w_scalar(group, gens, eps, thetas, indices, eta=1):
    """Lemma 6, scalar form, for W = prod_{j in indices} exp(2i eps_j theta_j G_j):
    W acts on V* as the scalar eta iff exp(2i Phi(l)) = eta for every
    realized pattern l, that is 2 Phi(l) / pi is even (eta = 1) or odd
    (eta = -1). With eta = 1 this is "W fixes V* pointwise"."""
    want = Fraction(0) if eta == 1 else Fraction(1)
    return all(
        half_turns(2 * phase_sum(eps, thetas, indices, l)) == want
        for l in realized_patterns(group, gens, indices)
    )


def w_fixes(group, gens, eps, thetas, indices):
    return all(in_pi_z(phase_sum(eps, thetas, indices, l)) for l in realized_patterns(group, gens, indices))


def preserves_any_angle(display, gens, eps, thetas):
    """Lemma 7: the gate preserves V(C) iff W_g fixes V(C) for every
    displayed row g, decided by the patterns S(C) realizes on J(g)."""
    check_gate(gens, eps)
    check_angles(gens, thetas)
    group = StabilizerGroup(display)
    return all(w_fixes(group, gens, eps, thetas, anticommuting(gens, g)) for g in display.rows())


def survives_addition_any_angle(display, gens, eps, thetas, sector, row, frame=()):
    """The `C-ADD-CHECK` test at the added row s at every angle (Corollary
    7.1 of §4.37, or Corollary 9.1 when `frame` is given): for a gate that
    preserves the parent (or its frame sector, under the inclusion
    S_F(C) <= S_{F'}(C')), whether W_s fixes V(C') (or V_{F'}(C') for the
    transported frame `frame`)."""
    check_gate(gens, eps)
    check_angles(gens, thetas)
    child = display.add(sector, row)
    group = StabilizerGroup(child, frame)
    if not frame_well_formed(child, frame) or not group.consistent:
        raise ValueError("frame is not consistent on the child")
    return w_fixes(group, gens, eps, thetas, anticommuting(gens, sector_pauli(sector, row)))


def preserves_in_frame(display, frame, gens, eps, thetas):
    """Lemma 9: preserves_U(C | F), the gate maps the frame sector V_F(C)
    into V(C), iff W_g fixes V_F(C) for every displayed row g."""
    check_gate(gens, eps)
    check_angles(gens, thetas)
    group = StabilizerGroup(display, frame)
    if not frame_well_formed(display, frame) or not group.consistent:
        raise ValueError("frame is not consistent on the display")
    return all(w_fixes(group, gens, eps, thetas, anticommuting(gens, g)) for g in display.rows())


def resolved_eigenvalues(display, frame, gens, indices):
    """When the frame resolves J = `indices` (every L_j = G_{j0} G_j, with
    j0 the first index, acts on V_F(C) as a scalar), the eigenvalues
    l_j^(F) of the L_j on V_F(C), with l_{j0} = 1; otherwise None."""
    indices = list(indices)
    group = StabilizerGroup(display, frame)
    if not frame_well_formed(display, frame) or not group.consistent:
        raise ValueError("frame is not consistent on the display")
    if not indices:
        return ()
    out = [1]
    for j in indices[1:]:
        c = group.sign(gens[indices[0]] * gens[j])
        if c is None:
            return None
        out.append(c)
    return tuple(out)


def sector_phase(display, frame, gens, eps, thetas):
    """Lemma 10: phase_U(C | F) = z, the gate acts on the frame sector
    V_F(C) as the scalar z, iff exp(i Phi(l)) = z for every pattern l that
    S_F(C) realizes on all q generators. Returns r in [0, 2) with
    z = exp(i r pi) (see `root_of_unity`), or None when the gate is not a
    scalar on the sector."""
    check_gate(gens, eps)
    check_angles(gens, thetas)
    group = StabilizerGroup(display, frame)
    if not frame_well_formed(display, frame) or not group.consistent:
        raise ValueError("frame is not consistent on the display")
    indices = range(len(gens))
    values = {half_turns(phase_sum(eps, thetas, indices, l)) for l in realized_patterns(group, gens, indices)}
    return values.pop() if len(values) == 1 else None


def image_pi4(display, gens, eps, logical, target):
    """Lemma 11 at all angles pi/4: U^dag L U = P on V(C) iff
    P^{-1} L V_L is an element of S(C) (Lemma 1)."""
    check_gate(gens, eps)
    return in_stabilizer(display, inverse(target) * (logical * conditioned_pauli(gens, eps, logical)))


def image_scalar(display, gens, eps, thetas, logical, eta):
    """Lemma 11 at every angle: U^dag L U = eta L on V(C), eta = +1 or -1,
    iff W_L acts on V(C) as eta."""
    check_gate(gens, eps)
    check_angles(gens, thetas)
    return w_scalar(
        StabilizerGroup(display), gens, eps, thetas, anticommuting(gens, logical), eta
    )


def addresses(display, frame, addressed, gens, eps, thetas):
    """addresses_U(C; F, A): the gate preserves V(C) and commutes on V(C)
    with sigma(v_e) for every entry e of F outside A (`addressed` is a set
    of indices into `frame`)."""
    if not frame_well_formed(display, frame):
        raise ValueError("frame is not well formed on the display")
    if not preserves_any_angle(display, gens, eps, thetas):
        return False
    return all(
        image_scalar(display, gens, eps, thetas, entry_pauli(e), 1)
        for i, e in enumerate(frame)
        if i not in addressed
    )


def transport_frame_add(child, frame):
    """The logical-witness transport of STATE_MODEL.md §1a across
    `C-ADD-CHECK`: discard the entries that are not logicals of the child,
    then keep one entry of least weight per class, the earliest on ties."""
    chosen = []
    for entry in frame:
        sector, m, _ = entry
        if not is_logical(child, sector, m):
            continue
        basis = reduce_basis(child.x_rows if sector == "X" else child.z_rows)
        rival = next(
            (i for i, c in enumerate(chosen) if c[0] == sector and in_span(basis, c[1] ^ m)), None
        )
        if rival is None:
            chosen.append(entry)
        elif popcount(m) < popcount(chosen[rival][1]):
            chosen[rival] = entry
    return chosen


def frame_refines(parent, frame, child, child_frame):
    """S_F(C) is contained in S_{F'}(C'): every parent row, and every parent
    entry with its eigenvalue, is an element of the child's frame group. Then
    V_{F'}(C') is contained in V_F(C)."""
    group = StabilizerGroup(child, child_frame)
    if not frame_well_formed(child, child_frame) or not group.consistent:
        return False
    return all(group.contains(r) for r in parent.rows()) and all(
        group.sign(entry_pauli(e)) == e[2] for e in frame
    )


def addition_frame_cell(parent, frame, gens, eps, thetas, sector, row):
    """The `C-ADD-CHECK` cell of Row C (§2h) for a gate with
    preserves_U(C | F), split as in the review of PR #665:

    * `"not_yet_defined"` when the transported frame F' is not consistent on
      the child: the predicate is not stated there;
    * `"does_not_carry"` when F' is consistent but S_F(C) is not contained in
      S_{F'}(C'): the cell licenses nothing (the one-qubit counterexample
      refutes carry), and Lemma 9 at the child decides it;
    * otherwise `"carries"` or `"does_not_carry"` by the test of
      Corollary 9.1 at the added row.
    """
    child = parent.add(sector, row)
    child_frame = transport_frame_add(child, frame)
    if not frame_consistent(child, child_frame):
        return "not_yet_defined"
    if not frame_refines(parent, frame, child, child_frame):
        return "does_not_carry"
    return (
        "carries"
        if survives_addition_any_angle(parent, gens, eps, thetas, sector, row, child_frame)
        else "does_not_carry"
    )


def direct_sum(a, b):
    """The direct sum of two displays, B's qubits shifted past A's."""
    shift = a.n
    return Display(
        a.n + b.n,
        a.x_rows + [m << shift for m in b.x_rows],
        a.z_rows + [m << shift for m in b.z_rows],
    )


def shift_frame(frame, shift):
    return [(s, m << shift, e) for s, m, e in frame]


# Frame-reading oracles: state vectors, no Pauli-group reasoning.


def apply_gate(gens, eps, thetas, vec, adjoint=False):
    for g, e, t in zip(gens, eps, thetas):
        vec = apply_rotation(g, -e * t if adjoint else e * t, vec)
    return vec


def subspace_vectors(display, frame=()):
    """A spanning set of the frame sector V_F(C) (V(C) for an empty frame):
    the projections of the basis states by (1 + g)/2 over the rows and
    (1 + eig sigma(v))/2 over the entries."""
    ops = [(g, 1) for g in display.rows()] + [(entry_pauli(e), e[2]) for e in frame]
    out = []
    for b in range(1 << display.n):
        vec = [0j] * (1 << display.n)
        vec[b] = 1
        for p, s in ops:
            moved = apply_pauli(p, vec)
            vec = [(a + s * m) / 2 for a, m in zip(vec, moved)]
        if any(abs(a) > 1e-12 for a in vec):
            out.append(vec)
    return out


def _fixed_by_rows(display, vec, tol):
    return all(
        all(abs(a - b) <= tol for a, b in zip(vec, apply_pauli(g, vec))) for g in display.rows()
    )


def oracle_preserves_in_frame(display, frame, gens, eps, thetas, tol=1e-9):
    return all(
        _fixed_by_rows(display, apply_gate(gens, eps, thetas, vec), tol)
        for vec in subspace_vectors(display, frame)
    )


def oracle_sector_phase(display, frame, gens, eps, thetas, tol=1e-9):
    z = None
    for vec in subspace_vectors(display, frame):
        image = apply_gate(gens, eps, thetas, vec)
        i = max(range(len(vec)), key=lambda t: abs(vec[t]))
        zv = image[i] / vec[i]
        if any(abs(a - zv * b) > tol for a, b in zip(image, vec)):
            return None
        if z is not None and abs(z - zv) > tol:
            return None
        z = zv
    return z


def oracle_image(display, gens, eps, thetas, logical, target, tol=1e-9):
    for vec in subspace_vectors(display):
        out = apply_gate(gens, eps, thetas, apply_pauli(logical, apply_gate(gens, eps, thetas, vec)), adjoint=True)
        want = apply_pauli(target, vec)
        if any(abs(a - b) > tol for a, b in zip(out, want)):
            return False
    return True


def oracle_addresses(display, frame, addressed, gens, eps, thetas):
    if not oracle_preserves(display, gens, eps, thetas):
        return False
    return all(
        oracle_image(display, gens, eps, thetas, entry_pauli(e), entry_pauli(e))
        for i, e in enumerate(frame)
        if i not in addressed
    )


# Named instances.


def shor_display():
    z_supports = [[0, 1], [1, 2], [3, 4], [4, 5], [6, 7], [7, 8]]
    x_supports = [[0, 1, 2, 3, 4, 5], [3, 4, 5, 6, 7, 8]]
    return Display.from_supports(9, x_supports, z_supports)


def shor_weakening_instance():
    """The parent's bound is not the child's: deleting the first X-row of the
    nine-qubit Shor code leaves a nontrivial equal-syndrome pair of weight
    one, below ceil(3 / 2) = 2."""
    parent = shor_display()
    child = parent.delete("X", 0)
    gens = [Pauli(0, mask([3])), Pauli(0, mask([6]))]
    return parent, child, gens


def deletion_instance():
    """A gate that does not survive a deletion: on the two-qubit display with
    rows XX and ZZ, exp(i pi/4 X_0) exp(-i pi/4 X_1) preserves the
    codespace, and stops doing so once XX is deleted."""
    parent = Display.from_supports(2, [[0, 1]], [[0, 1]])
    gens = [pauli_from_string("XI"), pauli_from_string("IX")]
    return parent, parent.delete("X", 0), gens, [1, -1]


def frame_addition_instance(eig):
    """The non-pi/4 addition cell read in a frame (§4.37, Lemma 9): adding
    s = X_0 X_1 to the empty display on two qubits, with generators Z_0 and
    Z_1 at signs (+1, +1). Both anticommute with s and L = Z_0 Z_1 is a
    zero-syndrome Z-logical of the child. In the sector Z_0 Z_1 = eig the
    test reads theta_1 + eig * theta_2 in pi Z."""
    parent = Display(2, [], [])
    row = mask([0, 1])
    gens = [pauli_from_string("ZI"), pauli_from_string("IZ")]
    frame = [("Z", mask([0, 1]), eig)]
    return parent, "X", row, gens, [1, 1], frame


def four_two_two_display():
    """The [[4,2,2]] code: rows X^4 and Z^4."""
    return Display.from_supports(4, [[0, 1, 2, 3]], [[0, 1, 2, 3]])


def four_two_two_frame():
    """A logical basis of [[4,2,2]] as frame entries: X1 = X_0 X_1,
    Z1 = Z_0 Z_2, X2 = X_0 X_2, Z2 = Z_0 Z_1 (all eigenvalues +1; entries
    0 and 1 anticommute, as do 2 and 3, so the list is not consistent and
    is read only by addressability and the conjugation image)."""
    return [
        ("X", mask([0, 1]), 1),
        ("Z", mask([0, 2]), 1),
        ("X", mask([0, 2]), 1),
        ("Z", mask([0, 1]), 1),
    ]


def frame_deletion_instance():
    """One deletion refutes Rows C-F at once (§4.37): on three qubits with
    rows X_0 X_1 and Z_0 Z_1 and the frame entry (Z, {2}, +1), the gate
    exp(i pi/4 X_0 X_2) exp(-i pi/4 X_1 X_2) preserves the codespace, acts
    on V(C) as the identity, and commutes with Z_2 there; after deleting
    X_0 X_1 it does none of these."""
    parent = Display.from_supports(3, [[0, 1]], [[0, 1]])
    gens = [pauli_from_string("XIX"), pauli_from_string("IXX")]
    frame = [("Z", mask([2]), 1)]
    return parent, parent.delete("X", 0), gens, [1, -1], frame


def frame_drop_instance():
    """A frame entry dropped by the transport refutes carry (§4.37): on one
    qubit with no rows and frame (Z, {0}, +1), exp(i pi/4 Z_0) acts on the
    sector |0> as exp(i pi/4); adding X_0 drops the entry and the gate does
    not preserve the child codespace |+>."""
    parent = Display(1, [], [])
    gens = [pauli_from_string("Z")]
    frame = [("Z", mask([0]), 1)]
    return parent, "X", mask([0]), gens, [1], frame


# The sweep.


def random_display(rng, n):
    x_rows = [rng.randrange(1, 1 << n) for _ in range(rng.randrange(0, n))]
    dual = [m for m in range(1, 1 << n) if all(popcount(m & r) % 2 == 0 for r in x_rows)]
    z_rows = [rng.choice(dual) for _ in range(rng.randrange(0, n))] if dual else []
    return Display(n, x_rows, z_rows)


def random_pauli(rng, n):
    x, z = rng.randrange(1 << n), rng.randrange(1 << n)
    return Pauli(x, z, popcount(x & z) + 2 * rng.randrange(2))


def random_stabilizer(rng, display):
    out = IDENTITY
    for g in display.rows():
        if rng.randrange(2):
            out = out * g
    return out


def random_gate(rng, display):
    """A commuting family, biased toward families that preserve the codespace:
    half the time each new generator is an earlier one times a stabilizer."""
    n = display.n
    gens = []
    for _ in range(rng.randrange(1, 5)):
        if gens and rng.randrange(2):
            cand = rng.choice(gens) * random_stabilizer(rng, display)
        else:
            cand = random_pauli(rng, n)
        if cand.is_hermitian() and all(not cand.anticommutes(g) for g in gens):
            gens.append(cand)
    if not gens:
        gens = [Pauli(1, 0)]
    eps = [rng.choice((1, -1)) for _ in gens]
    return gens, eps


def random_addable_row(rng, display):
    sector = rng.choice("XZ")
    opposite = display.z_rows if sector == "X" else display.x_rows
    same = display.x_rows if sector == "X" else display.z_rows
    basis = reduce_basis(same)
    options = [
        m
        for m in range(1, 1 << display.n)
        if all(popcount(m & r) % 2 == 0 for r in opposite) and not in_span(basis, m)
    ]
    if not options:
        return None
    return sector, rng.choice(options)


def random_equal_syndrome_family(rng, display):
    """A commuting family G_1, G_1 N_2, ... with the N_j in the normalizer,
    so that every member has the syndrome of G_1. None when sampling fails."""
    n = display.n
    rows = display.rows()
    first = random_pauli(rng, n)
    if not any(syndrome(display, first)):
        return None
    gens = [first]
    for _ in range(rng.randrange(1, 4)):
        factor = random_pauli(rng, n)
        if any(factor.anticommutes(g) for g in rows):
            continue
        cand = first * factor
        if cand.is_hermitian() and all(not cand.anticommutes(g) for g in gens):
            gens.append(cand)
    return gens if len(gens) >= 2 else None


def sweep(seed=452, trials=400, max_n=4):
    rng = random.Random(seed)
    stats = {
        "seed": seed,
        "trials": trials,
        "preservation_checked": 0,
        "preserving": 0,
        "not_preserving": 0,
        "survival_checked": 0,
        "survives": 0,
        "does_not_survive": 0,
        "commuting_any_angle_checked": 0,
        "deletion_checked": 0,
        "deletion_not_carried": 0,
        "weight_checked": 0,
        "weight_tight": 0,
        "disagreements": [],
    }
    for trial in range(trials):
        display = random_display(rng, rng.randrange(2, max_n + 1))
        gens, eps = random_gate(rng, display)
        quarter = [math.pi / 4] * len(gens)

        predicted = preserves_pi4(display, gens, eps)
        observed = oracle_preserves(display, gens, eps, quarter)
        stats["preservation_checked"] += 1
        stats["preserving" if observed else "not_preserving"] += 1
        if predicted != observed:
            stats["disagreements"].append({"trial": trial, "row": "preservation"})

        if observed:
            choice = random_addable_row(rng, display)
            if choice is not None:
                sector, row = choice
                child = display.add(sector, row)
                predicted = survives_addition(display, gens, eps, sector, row)
                observed_child = oracle_preserves(child, gens, eps, quarter)
                stats["survival_checked"] += 1
                stats["survives" if observed_child else "does_not_survive"] += 1
                if predicted != observed_child:
                    stats["disagreements"].append({"trial": trial, "row": "survival"})
                added = Pauli(row, 0) if sector == "X" else Pauli(0, row)
                if all(not g.anticommutes(added) for g in gens):
                    # Sufficient at every angle: the generators commute with
                    # the added row. Checked where the parent is preserved
                    # at the sampled angles.
                    thetas = [rng.uniform(0, math.pi) for _ in gens]
                    if oracle_preserves(display, gens, eps, thetas):
                        stats["commuting_any_angle_checked"] += 1
                        if not oracle_preserves(child, gens, eps, thetas):
                            stats["disagreements"].append(
                                {"trial": trial, "row": "commuting-any-angle"}
                            )

            for sector, rows in (("X", display.x_rows), ("Z", display.z_rows)):
                for index in range(len(rows)):
                    child = display.delete(sector, index)
                    stats["deletion_checked"] += 1
                    if not oracle_preserves(child, gens, eps, quarter):
                        stats["deletion_not_carried"] += 1

        family = random_equal_syndrome_family(rng, display)
        if family is not None and nontrivial(display, family):
            gens = family
            assert equal_syndrome(display, gens)
            d = exact_distance(display)
            stats["weight_checked"] += 1
            if d is None or w_max(gens) < weight_floor(d):
                stats["disagreements"].append({"trial": trial, "row": "weight"})
            elif w_max(gens) == weight_floor(d):
                stats["weight_tight"] += 1
    return stats


def random_frame(rng, display, size, commuting):
    """Up to `size` entries, each a random logical with a random eigenvalue,
    kept while the list stays well formed (and commuting, when asked)."""
    frame = []
    for _ in range(8 * size):
        if len(frame) >= size:
            break
        cand = frame + [(rng.choice("XZ"), rng.randrange(1, 1 << display.n), rng.choice((1, -1)))]
        if frame_well_formed(display, cand) and (not commuting or frame_commuting(cand)):
            frame = cand
    return frame


def resolving_frame(rng, display, gens):
    """Entries from the sector parts of the products L_j = G_1 G_j that are
    logicals, with random eigenvalues: a frame that often resolves the
    generators, so that the eigenvalue reading decides the verdicts."""
    frame = []
    for g in gens[1:]:
        product = gens[0] * g
        for sector, m in (("X", product.x), ("Z", product.z)):
            if m and is_logical(display, sector, m):
                cand = frame + [(sector, m, rng.choice((1, -1)))]
                if frame_well_formed(display, cand):
                    frame = cand
    return frame


def theorem1_phase(display, frame, gens, eps, thetas):
    """The source's Theorem 1 form of Lemma 10 (§4.37, Corollary 10.1): for
    an equal-syndrome family that the frame resolves, the gate is a scalar
    on V_F(C) iff Phi = sum_j eps_j theta_j l_j^(F) lies in pi Z, and the
    scalar is (-1)^(Phi / pi). Returns Phi / pi modulo 2 (0 for +1, 1 for
    -1, in the convention of `sector_phase`), or None when it is not a
    scalar."""
    signs = resolved_eigenvalues(display, frame, gens, range(len(gens)))
    assert signs is not None and equal_syndrome(display, gens)
    r = phase_sum(eps, thetas, range(len(gens)), signs)
    return half_turns(r) if in_pi_z(r) else None


def random_angles(rng, count):
    """Rational multiples of pi: equal multiples of pi/8 up to 2 pi (so that
    sign patterns cancel and Phi in pi Z has nontrivial solutions), or
    independent multiples of pi/8 up to 2 pi, or rationals with
    denominators up to 12."""
    choice = rng.randrange(3)
    if choice == 0:
        return [Fraction(rng.randrange(0, 17), 8)] * count
    if choice == 1:
        return [Fraction(rng.randrange(0, 17), 8) for _ in range(count)]
    return [Fraction(rng.randrange(0, 25), rng.randrange(1, 13)) for _ in range(count)]


def _close(a, b, tol=1e-7):
    if a is None or b is None:
        return a is None and b is None
    return abs(a - b) < tol


def sweep_frames(seed=572, trials=400, max_n=4):
    """Compare Lemmas 7-11 with the state-vector oracles on random displays,
    frames, gates, and additions."""
    rng = random.Random(seed)
    keys = (
        "preservation_any_angle",
        "frame_sector_preservation",
        "sector_phase",
        "addition_any_angle",
        "addition_in_frame",
        "addition_resolved_formula",
        "phase_carry_under_refinement",
        "image_pi4",
        "image_scalar",
        "addressability",
        "theorem1_phase",
    )
    stats = {
        "seed": seed,
        "trials": trials,
        "frame_decides": 0,
        "addition_frame_not_stated": 0,
        "disagreements": [],
    }
    for key in keys:
        stats[key] = {"true": 0, "false": 0}

    def record(key, trial, predicted, observed):
        stats[key]["true" if observed else "false"] += 1
        if predicted != observed:
            stats["disagreements"].append({"trial": trial, "row": key})

    for trial in range(trials):
        display = random_display(rng, rng.randrange(1, max_n + 1))
        family = None
        if rng.randrange(2):
            gens, eps = random_gate(rng, display)
        else:
            family = random_equal_syndrome_family(rng, display)
            gens = family or random_gate(rng, display)[0]
            eps = [rng.choice((1, -1)) for _ in gens]
        thetas = random_angles(rng, len(gens))
        rad = radians(thetas)
        if family is not None and rng.randrange(4):
            frame = resolving_frame(rng, display, gens)
        else:
            frame = random_frame(rng, display, rng.randrange(0, 3), commuting=bool(rng.randrange(4)))

        observed = oracle_preserves(display, gens, eps, rad)
        record("preservation_any_angle", trial, preserves_any_angle(display, gens, eps, thetas), observed)

        consistent = frame_consistent(display, frame)
        if consistent:
            in_frame = oracle_preserves_in_frame(display, frame, gens, eps, rad)
            record(
                "frame_sector_preservation",
                trial,
                preserves_in_frame(display, frame, gens, eps, thetas),
                in_frame,
            )
            if in_frame and not observed:
                stats["frame_decides"] += 1
            z_pred = sector_phase(display, frame, gens, eps, thetas)
            z_obs = oracle_sector_phase(display, frame, gens, eps, rad)
            stats["sector_phase"]["true" if z_obs is not None else "false"] += 1
            if not _close(None if z_pred is None else root_of_unity(z_pred), z_obs):
                stats["disagreements"].append({"trial": trial, "row": "sector_phase"})
            if (
                family is not None
                and equal_syndrome(display, gens)
                and resolved_eigenvalues(display, frame, gens, range(len(gens))) is not None
            ):
                z_thm = theorem1_phase(display, frame, gens, eps, thetas)
                stats["theorem1_phase"]["true" if z_obs is not None else "false"] += 1
                if not _close(None if z_thm is None else root_of_unity(z_thm), z_obs):
                    stats["disagreements"].append({"trial": trial, "row": "theorem1_phase"})

        for entry in frame:
            logical = entry_pauli(entry)
            for eta in (1, -1):
                target = logical if eta == 1 else logical.scaled(2)
                record(
                    "image_scalar",
                    trial,
                    image_scalar(display, gens, eps, thetas, logical, eta),
                    oracle_image(display, gens, eps, rad, logical, target),
                )
            quarter = [math.pi / 4] * len(gens)
            for target in (logical, logical * conditioned_pauli(gens, eps, logical), random_pauli(rng, display.n)):
                record(
                    "image_pi4",
                    trial,
                    image_pi4(display, gens, eps, logical, target),
                    oracle_image(display, gens, eps, quarter, logical, target),
                )

        if frame:
            addressed = {i for i in range(len(frame)) if rng.randrange(2)}
            record(
                "addressability",
                trial,
                addresses(display, frame, addressed, gens, eps, thetas),
                oracle_addresses(display, frame, addressed, gens, eps, rad),
            )

        choice = random_addable_row(rng, display)
        if choice is None:
            continue
        sector, row = choice
        child = display.add(sector, row)
        added = sector_pauli(sector, row)
        if observed:
            record(
                "addition_any_angle",
                trial,
                survives_addition_any_angle(display, gens, eps, thetas, sector, row),
                oracle_preserves(child, gens, eps, rad),
            )
        if not consistent:
            continue
        child_frame = transport_frame_add(child, frame)
        if not frame_consistent(child, child_frame):
            stats["addition_frame_not_stated"] += 1
            continue
        if not frame_refines(display, frame, child, child_frame):
            continue
        if preserves_in_frame(display, frame, gens, eps, thetas):
            observed_child = oracle_preserves_in_frame(child, child_frame, gens, eps, rad)
            record(
                "addition_in_frame",
                trial,
                addition_frame_cell(display, frame, gens, eps, thetas, sector, row) == "carries",
                observed_child,
            )
            indices = anticommuting(gens, added)
            if indices:
                signs = resolved_eigenvalues(child, child_frame, gens, indices)
                if signs is not None:
                    record(
                        "addition_resolved_formula",
                        trial,
                        in_pi_z(phase_sum(eps, thetas, indices, signs)),
                        observed_child,
                    )
        z = sector_phase(display, frame, gens, eps, thetas)
        if z is not None:
            z_child = oracle_sector_phase(child, child_frame, gens, eps, rad)
            record("phase_carry_under_refinement", trial, True, _close(root_of_unity(z), z_child))
    return stats


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--seed", type=int, default=452)
    parser.add_argument("--frame-seed", type=int, default=572)
    parser.add_argument("--trials", type=int, default=400)
    parser.add_argument("--max-n", type=int, default=4)
    args = parser.parse_args(argv)
    stats = sweep(seed=args.seed, trials=args.trials, max_n=args.max_n)
    frames = sweep_frames(seed=args.frame_seed, trials=args.trials, max_n=args.max_n)
    json.dump({"rows_a_b": stats, "frame_reading": frames}, sys.stdout, indent=2)
    sys.stdout.write("\n")
    return 1 if stats["disagreements"] or frames["disagreements"] else 0


if __name__ == "__main__":
    sys.exit(main())
