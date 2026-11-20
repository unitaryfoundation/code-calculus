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

Agreement on the sweep is evidence that the criteria are derived and
transcribed as stated, not a proof (AGENTS.md).
"""

import argparse
import cmath
import json
import math
import random
import sys


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


def addition_survival_verdict(display, gens, eps, sector, row, thetas=None):
    """Evaluate the three-branch `C-ADD-CHECK` gate-survival cell of
    `spec/JUDGMENT_LAYER.md` §2h for a gate preserving `display`:

    * If every generator commutes with the added row: returns `"carries"`
      (holds at every angle theta_j >= 0).
    * Else if `thetas` is omitted or every angle is pi/4: returns `"carries"`
      when V_s is in the child stabilizer group and `"does_not_carry"`
      otherwise.
    * Else (some generator anticommutes with the added row and some angle is
      not pi/4): returns `"not_yet_defined"`.
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
    if thetas is not None:
        if len(thetas) != len(gens) or any(
            isinstance(t, bool) or not isinstance(t, (int, float)) or t < 0 for t in thetas
        ):
            raise ValueError("thetas must be a sequence of len(gens) nonnegative numbers")
    added = Pauli(row, 0) if sector == "X" else Pauli(0, row)
    if all(not g.anticommutes(added) for g in gens):
        return "carries"
    if thetas is None or all(
        math.isclose(t, math.pi / 4, rel_tol=0.0, abs_tol=1e-12) for t in thetas
    ):
        return "carries" if survives_addition(display, gens, eps, sector, row) else "does_not_carry"
    return "not_yet_defined"


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


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--seed", type=int, default=452)
    parser.add_argument("--trials", type=int, default=400)
    parser.add_argument("--max-n", type=int, default=4)
    args = parser.parse_args(argv)
    stats = sweep(seed=args.seed, trials=args.trials, max_n=args.max_n)
    json.dump(stats, sys.stdout, indent=2)
    sys.stdout.write("\n")
    return 1 if stats["disagreements"] else 0


if __name__ == "__main__":
    sys.exit(main())
