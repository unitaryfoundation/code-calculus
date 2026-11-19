#!/usr/bin/env python3
"""Finite-torus harness for the decoupling candidate of issue #451 / #542.

`design/DECOUPLING_CONSTRUCTOR.md` proposes to read the decoupling of
arXiv 2610.40592 as a certificate-checked relation between two presented
states, not as a constructor that runs the paper's algorithm. This script
is the finite side of that proposal for qubits (p = 2):

* a translation-invariant CSS code on a finite torus as a typed finite
  object (`Code`: periods, sites per cell, and two matrices over the group
  algebra of the torus), with its typed input signature and presented
  display;
* the higher-form toric codes from the Koszul complex, stacks, ancillas,
  and coarse-graining on a superlattice;
* translation-invariant SUM and SWAP circuits, applied both to the
  polynomial matrices and gate by gate to the presented display;
* `check_decoupling`, which refuses missing translation-invariance data,
  non-commuting inputs/targets, shape mismatches, or invalid circuits, and
  accepts a supplied circuit when the transformed display spans the target's
  rows, sector by sector;
* the distance factors of a circuit, checked against exhaustive distances.

Translation-triviality and gluing-vanishing remain the source paper's
admission hypotheses (not checked by this finite-torus certificate check).
Nothing here runs the paper's decoupling algorithm, and nothing is a
consumer path. Circuit verification is evidence only, not a calculus rule
(AGENTS.md).
"""

import argparse
import itertools
import json
import random
import sys
from math import comb


def popcount(x):
    return bin(x).count("1")


def _validate_int(value, name, minimum=1):
    if isinstance(value, bool) or not isinstance(value, int) or value < minimum:
        if minimum == 1:
            raise ValueError(f"{name} must be a positive integer")
        if minimum == 0:
            raise ValueError(f"{name} must be a non-negative integer")
        raise ValueError(f"{name} must be an integer >= {minimum}")
    return value


def _validate_periods(periods):
    if not isinstance(periods, (tuple, list)) or len(periods) == 0:
        raise ValueError("periods must be a non-empty tuple or list of positive integers")
    return tuple(_validate_int(p, "period", 1) for p in periods)


def _validate_poly_entry(entry, periods, label="entry"):
    if not isinstance(entry, (frozenset, set)):
        raise ValueError(f"{label} must be a frozenset or set of exponent tuples")
    dim = len(periods)
    out = set()
    for alpha in entry:
        if not isinstance(alpha, tuple) or len(alpha) != dim:
            raise ValueError(f"exponent {alpha!r} in {label} must have length {dim}")
        coords = []
        for coord, p in zip(alpha, periods):
            if isinstance(coord, bool) or not isinstance(coord, int):
                raise ValueError(f"exponent coordinate {coord!r} in {label} must be an integer")
            coords.append(coord % p)
        out ^= {tuple(coords)}
    return frozenset(out)


def _validate_poly_matrix(matrix, q, periods, name):
    if not isinstance(matrix, (list, tuple)):
        raise ValueError(f"{name} must be a list or tuple of rows")
    rows = []
    for row_idx, row in enumerate(matrix):
        if not isinstance(row, (list, tuple)) or len(row) != q:
            raise ValueError(f"{name}[{row_idx}] must have length {q}")
        rows.append([
            _validate_poly_entry(entry, periods, f"{name}[{row_idx}][{col_idx}]")
            for col_idx, entry in enumerate(row)
        ])
    return rows


# The group algebra F_2[Z_{L_1} x ... x Z_{L_D}]: an element is a frozenset
# of exponent tuples.

ZERO = frozenset()


def monomial(exponent, periods):
    periods = _validate_periods(periods)
    if not isinstance(exponent, (tuple, list)) or len(exponent) != len(periods):
        raise ValueError(f"exponent must have length {len(periods)}")
    coords = []
    for e, p in zip(exponent, periods):
        if isinstance(e, bool) or not isinstance(e, int):
            raise ValueError("exponent coordinates must be integers")
        coords.append(e % p)
    return frozenset([tuple(coords)])


def one(periods):
    periods = _validate_periods(periods)
    return monomial((0,) * len(periods), periods)


def poly_add(f, g):
    return f ^ g


def poly_mul(f, g, periods):
    out = set()
    for a in f:
        for b in g:
            out ^= {tuple((x + y) % p for x, y, p in zip(a, b, periods))}
    return frozenset(out)


def antipode(f, periods):
    return frozenset(tuple((-x) % p for x, p in zip(a, periods)) for a in f)


class Code:
    """A translation-invariant CSS code on the torus with the given periods:
    `q` sites per cell and matrices `hx`, `hz` over the group algebra, one
    row per check type and one column per site."""

    def __init__(self, periods, q, hx, hz):
        self.periods = _validate_periods(periods)
        self.q = _validate_int(q, "q", 1)
        self.hx = _validate_poly_matrix(hx, self.q, self.periods, "hx")
        self.hz = _validate_poly_matrix(hz, self.q, self.periods, "hz")

    def cells(self):
        return list(itertools.product(*[range(p) for p in self.periods]))

    def n(self):
        return self.q * len(self.cells())

    def commutes(self):
        """H_X H_Z^dagger = 0, the dagger being transpose with antipode."""
        for rx in self.hx:
            for rz in self.hz:
                acc = ZERO
                for a in range(self.q):
                    acc = poly_add(acc, poly_mul(rx[a], antipode(rz[a], self.periods), self.periods))
                if acc:
                    return False
        return True

    def signature(self):
        """Typed input signature `(L, q, H_X, H_Z)` and commutation premise."""
        return {
            "periods": self.periods,
            "q": self.q,
            "hx_rows": len(self.hx),
            "hz_rows": len(self.hz),
            "commutes": self.commutes(),
        }

    def qubit(self, cell, site):
        index = 0
        for c, p in zip(cell, self.periods):
            index = index * p + c % p
        return index * self.q + site

    def _rows(self, matrix):
        rows = []
        for row in matrix:
            for g in self.cells():
                m = 0
                for a in range(self.q):
                    for alpha in row[a]:
                        cell = tuple(x - y for x, y in zip(g, alpha))
                        m ^= 1 << self.qubit(cell, a)
                rows.append(m)
        return rows

    def display(self):
        """The presented rows as bitmasks: for check type `i` and cell `g`,
        the support {(g - alpha, a) : alpha in H[i][a]}."""
        return self._rows(self.hx), self._rows(self.hz)


# GF(2) linear algebra on bitmasks.


def reduce_basis(masks):
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


def same_span(rows_a, rows_b):
    basis_a, basis_b = reduce_basis(rows_a), reduce_basis(rows_b)
    return all(in_span(basis_b, m) for m in rows_a) and all(in_span(basis_a, m) for m in rows_b)


def well_formed(display):
    xs, zs = display
    return all(popcount(a & b) % 2 == 0 for a in xs for b in zs)


def logical_count(n, display):
    xs, zs = display
    return n - rank(xs) - rank(zs)


def sector_distance(n, same, opposite):
    """The least weight of a vector that has even overlap with every row of
    `opposite` and is outside the span of `same`; None when there is none."""
    basis = reduce_basis(same)
    best = None
    for m in range(1, 1 << n):
        w = popcount(m)
        if best is not None and w >= best:
            continue
        if all(popcount(m & r) % 2 == 0 for r in opposite) and not in_span(basis, m):
            best = w
    return best


def distances(n, display):
    xs, zs = display
    return sector_distance(n, xs, zs), sector_distance(n, zs, xs)


# Targets: higher-form toric codes, stacks, ancillas.


def toric_code(periods, j):
    """The j-form toric code on the torus of dimension D = len(periods),
    1 <= j <= D - 1, from the Koszul complex on w_i = x_i + 1: one site per
    j-subset of the directions, H_X = d_j and H_Z^dagger = d_{j+1}."""
    periods = _validate_periods(periods)
    dim = len(periods)
    if isinstance(j, bool) or not isinstance(j, int) or not (1 <= j <= dim - 1):
        raise ValueError(f"form degree j must satisfy 1 <= j <= {dim - 1}")

    def w(i):
        exponent = tuple(1 if k == i else 0 for k in range(dim))
        return poly_add(monomial(exponent, periods), one(periods))

    def subsets(k):
        return list(itertools.combinations(range(dim), k))

    def boundary(k):
        # Matrix of d_k : K_k -> K_{k-1}, rows indexed by (k-1)-subsets.
        rows = []
        for small in subsets(k - 1):
            row = []
            for big in subsets(k):
                extra = set(big) - set(small)
                row.append(w(extra.pop()) if set(small) <= set(big) else ZERO)
            rows.append(row)
        return rows

    hx = boundary(j)
    d_next = boundary(j + 1)  # rows j-subsets, columns (j+1)-subsets
    hz = [[antipode(d_next[a][b], periods) for a in range(len(subsets(j)))]
          for b in range(len(subsets(j + 1)))]
    return Code(periods, comb(dim, j), hx, hz)


def stack(codes):
    """The direct sum of codes on one torus."""
    if not isinstance(codes, (list, tuple)) or len(codes) == 0:
        raise ValueError("codes must be a non-empty sequence of Code instances")
    for c in codes:
        if not isinstance(c, Code):
            raise ValueError("every element of codes must be a Code instance")
    periods = codes[0].periods
    if any(c.periods != periods for c in codes):
        raise ValueError("all codes in a stack must share the same periods")
    q = sum(c.q for c in codes)
    hx, hz, offset = [], [], 0
    for c in codes:
        for src, dst in ((c.hx, hx), (c.hz, hz)):
            for row in src:
                dst.append([ZERO] * offset + list(row) + [ZERO] * (q - offset - c.q))
        offset += c.q
    return Code(periods, q, hx, hz)


def with_ancillas(code, plus=0, zero=0):
    """Add `plus` sites per cell stabilized by X and `zero` stabilized by Z."""
    if not isinstance(code, Code):
        raise ValueError("code must be a Code instance")
    _validate_int(plus, "plus", 0)
    _validate_int(zero, "zero", 0)
    q = code.q + plus + zero
    unit = one(code.periods)
    hx = [list(row) + [ZERO] * (plus + zero) for row in code.hx]
    hz = [list(row) + [ZERO] * (plus + zero) for row in code.hz]
    for a in range(plus):
        hx.append([unit if s == code.q + a else ZERO for s in range(q)])
    for a in range(zero):
        hz.append([unit if s == code.q + plus + a else ZERO for s in range(q)])
    return Code(code.periods, q, hx, hz)


# Coarse-graining on the superlattice of index `factors`.


def coarse_grain(code, factors):
    """The same code read on the superlattice with `factors[i]` cells of the
    original lattice per cell in direction `i`. Returns the coarse code and
    the relabelling of qubits, a list `new_index[old_index]`."""
    if not isinstance(code, Code):
        raise ValueError("code must be a Code instance")
    if not isinstance(factors, (tuple, list)) or len(factors) != len(code.periods):
        raise ValueError(f"factors must have length {len(code.periods)}")
    factors = tuple(_validate_int(m, "factor", 1) for m in factors)
    if any(p % m != 0 for p, m in zip(code.periods, factors)):
        raise ValueError("each factor must divide the corresponding period")
    periods = tuple(p // m for p, m in zip(code.periods, factors))
    cosets = list(itertools.product(*[range(m) for m in factors]))
    index = {beta: i for i, beta in enumerate(cosets)}
    size = len(cosets)

    def lift(matrix):
        out = []
        for row in matrix:
            for beta_r in cosets:
                new_row = [set() for _ in range(code.q * size)]
                for a in range(code.q):
                    for alpha in row[a]:
                        beta_c = tuple((b - x) % m for b, x, m in zip(beta_r, alpha, factors))
                        gamma = tuple(
                            ((x - b + c) // m) % p
                            for x, b, c, m, p in zip(alpha, beta_r, beta_c, factors, periods)
                        )
                        new_row[a * size + index[beta_c]] ^= {gamma}
                out.append([frozenset(s) for s in new_row])
        return out

    coarse = Code(periods, code.q * size, lift(code.hx), lift(code.hz))
    relabel = [None] * code.n()
    for g in code.cells():
        big = tuple(x // m for x, m in zip(g, factors))
        beta = tuple(x % m for x, m in zip(g, factors))
        for a in range(code.q):
            relabel[code.qubit(g, a)] = coarse.qubit(big, a * size + index[beta])
    return coarse, relabel


def relabel_rows(rows, relabel):
    out = []
    for m in rows:
        new = 0
        for old, target in enumerate(relabel):
            if m >> old & 1:
                new |= 1 << target
        out.append(new)
    return out


# Circuits. A gate is ("sum", c, t, f) or ("swap", a, b). The gate
# ("sum", c, t, f) is the matrix U = I + f e_t e_c^T over the group algebra
# with c != t, acting as Z(v) -> Z(U v) and X(u) -> X((U^dagger)^{-1} u).


def _validate_site(site, q, name):
    if isinstance(site, bool) or not isinstance(site, int) or not (0 <= site < q):
        raise ValueError(f"{name} must be an integer in 0..{q - 1}")
    return site


def _validate_circuit(circuit, q, periods):
    if not isinstance(circuit, (list, tuple)):
        raise ValueError("circuit must be a list or tuple of gates")
    validated = []
    for idx, gate in enumerate(circuit):
        if not isinstance(gate, (list, tuple)) or len(gate) == 0:
            raise ValueError(f"gate {idx} must be a non-empty tuple")
        kind = gate[0]
        if kind == "swap":
            if len(gate) != 3:
                raise ValueError(f"swap gate {idx} must have 3 elements")
            a = _validate_site(gate[1], q, f"gate {idx} site a")
            b = _validate_site(gate[2], q, f"gate {idx} site b")
            validated.append(("swap", a, b))
        elif kind == "sum":
            if len(gate) != 4:
                raise ValueError(f"sum gate {idx} must have 4 elements")
            c = _validate_site(gate[1], q, f"gate {idx} site c")
            t = _validate_site(gate[2], q, f"gate {idx} site t")
            if c == t:
                raise ValueError(f"sum gate {idx} requires c != t")
            f = _validate_poly_entry(gate[3], periods, f"gate {idx} polynomial")
            validated.append(("sum", c, t, f))
        else:
            raise ValueError(f"unknown gate kind {kind!r} at index {idx}")
    return validated


def apply_circuit(code, circuit):
    """The circuit on the polynomial matrices: H_Z U^dagger and H_X U^{-1}."""
    if not isinstance(code, Code):
        raise ValueError("code must be a Code instance")
    gates = _validate_circuit(circuit, code.q, code.periods)
    hx = [list(row) for row in code.hx]
    hz = [list(row) for row in code.hz]
    periods = code.periods
    for gate in gates:
        if gate[0] == "swap":
            _, a, b = gate
            for row in hx + hz:
                row[a], row[b] = row[b], row[a]
        else:
            _, c, t, f = gate
            bar = antipode(f, periods)
            for row in hz:
                row[t] = poly_add(row[t], poly_mul(row[c], bar, periods))
            for row in hx:
                row[c] = poly_add(row[c], poly_mul(row[t], f, periods))
    return Code(periods, code.q, hx, hz)


def physical_gates(code, circuit):
    """The circuit as CNOT and SWAP gates on the qubits of the torus. A
    CNOT is ("cnot", control, target); the gates of one SUM commute."""
    if not isinstance(code, Code):
        raise ValueError("code must be a Code instance")
    validated = _validate_circuit(circuit, code.q, code.periods)
    gates = []
    for gate in validated:
        if gate[0] == "swap":
            _, a, b = gate
            gates.extend(("swap", code.qubit(g, a), code.qubit(g, b)) for g in code.cells())
        else:
            _, c, t, f = gate
            for g in code.cells():
                for alpha in f:
                    # Z on (g, c) acquires Z on (g + alpha, t), so (g, c) is
                    # the target.
                    control = code.qubit(tuple(x + y for x, y in zip(g, alpha)), t)
                    gates.append(("cnot", control, code.qubit(g, c)))
    return gates


def apply_physical(display, gates):
    """CNOT(c, t) maps X_c to X_c X_t and Z_t to Z_c Z_t."""
    xs, zs = list(display[0]), list(display[1])
    for kind, a, b in gates:
        if kind == "swap":
            def swap(m):
                if (m >> a & 1) != (m >> b & 1):
                    m ^= (1 << a) | (1 << b)
                return m
            xs, zs = [swap(m) for m in xs], [swap(m) for m in zs]
        elif kind == "cnot":
            xs = [m ^ (1 << b) if m >> a & 1 else m for m in xs]
            zs = [m ^ (1 << a) if m >> b & 1 else m for m in zs]
        else:
            raise ValueError(f"unknown physical gate kind {kind!r}")
    return xs, zs


def inverse(circuit):
    """Over F_2 each gate is its own inverse."""
    return list(reversed(circuit))


def spread(code, circuit):
    """The distance factors of a circuit: the largest weight of the image of
    a single-qubit X, and of a single-qubit Z."""
    n = code.n()
    singles = [1 << i for i in range(n)]
    xs, zs = apply_physical((singles, singles), physical_gates(code, circuit))
    return max(popcount(m) for m in xs), max(popcount(m) for m in zs)


def check_decoupling(code, circuit, target, plus=0, zero=0):
    """The certificate check.

    Requires ``code`` and ``target`` to carry translation-invariance data as
    typed ``Code`` objects (refusing inputs without it), checks commutation
    and shape compatibility, validates ``circuit``, and accepts when the
    transformed display spans the target's rows in each sector.
    Translation-triviality and gluing-vanishing remain admission hypotheses
    not checked by this function; acceptance is circuit evidence, not a
    calculus rule.
    """
    record = {"accepted": False, "reason": None}
    if not isinstance(code, Code):
        record["reason"] = "translation-invariance data required (expected Code)"
        return record
    record["input_signature"] = code.signature()
    if not isinstance(target, Code):
        record["reason"] = "translation-invariance data required (expected Code)"
        return record
    _validate_int(plus, "plus", 0)
    _validate_int(zero, "zero", 0)
    if not code.commutes():
        record["reason"] = "input rows do not commute"
        return record
    if not target.commutes():
        record["reason"] = "target rows do not commute"
        return record
    extended = with_ancillas(code, plus=plus, zero=zero)
    if extended.periods != target.periods or extended.q != target.q:
        record["reason"] = "shape mismatch"
        return record
    try:
        validated_circuit = _validate_circuit(circuit, extended.q, extended.periods)
    except ValueError as exc:
        record["reason"] = f"invalid circuit: {exc}"
        return record
    image = apply_physical(extended.display(), physical_gates(extended, validated_circuit))
    goal = target.display()
    if not (same_span(image[0], goal[0]) and same_span(image[1], goal[1])):
        record["reason"] = "image does not span the target rows"
        return record
    n = extended.n()
    rho_x, rho_z = spread(extended, validated_circuit)
    inv_x, inv_z = spread(extended, inverse(validated_circuit))
    record.update(
        accepted=True,
        n=n,
        k=logical_count(n, goal),
        factors={"x": rho_x, "z": rho_z, "x_inverse": inv_x, "z_inverse": inv_z},
        target_signature=target.signature(),
        ancillas={"plus": plus, "zero": zero},
    )
    return record


def distance_window(d, forward, backward):
    """The interval for the image's sector distance given the source's
    exact distance `d`: ceil(d / backward) <= d' <= forward * d."""
    _validate_int(d, "d", 1)
    _validate_int(forward, "forward", 1)
    _validate_int(backward, "backward", 1)
    return -(-d // backward), forward * d


# Named instances and the sweep.


def random_poly(rng, periods, terms=2):
    f = ZERO
    for _ in range(rng.randrange(1, terms + 1)):
        f = poly_add(f, monomial(tuple(rng.randrange(p) for p in periods), periods))
    return f


def random_circuit(rng, code, gates=3):
    out = []
    for _ in range(gates):
        a, b = rng.sample(range(code.q), 2)
        if rng.randrange(4) == 0:
            out.append(("swap", a, b))
        else:
            f = random_poly(rng, code.periods)
            if f:
                out.append(("sum", a, b, f))
    return out


def disguised_instance(rng, periods=(2, 2), plus=1, zero=0, gates=3):
    """A code whose decoupling is known by construction: the image of a
    toric-code stack with ancillas under a random circuit. The certificate
    is the inverse circuit."""
    target = with_ancillas(toric_code(periods, 1), plus=plus, zero=zero)
    scramble = random_circuit(rng, target, gates=gates)
    return apply_circuit(target, scramble), inverse(scramble), target


def sweep(seed=451, trials=30):
    rng = random.Random(seed)
    stats = {
        "seed": seed,
        "trials": trials,
        "routes_compared": 0,
        "certificates_accepted": 0,
        "tampered_refused": 0,
        "tampered_accepted": 0,
        "distance_windows_checked": 0,
        "distance_changed": 0,
        "disagreements": [],
    }
    for trial in range(trials):
        periods = rng.choice([(2, 2), (3, 2), (2, 3)])
        code, certificate, target = disguised_instance(rng, periods=periods)
        if not code.commutes():
            stats["disagreements"].append({"trial": trial, "what": "commutation"})

        # The polynomial route and the gate-by-gate route agree.
        by_matrix = apply_circuit(code, certificate).display()
        by_gates = apply_physical(code.display(), physical_gates(code, certificate))
        stats["routes_compared"] += 1
        if sorted(by_matrix[0]) != sorted(by_gates[0]) or sorted(by_matrix[1]) != sorted(by_gates[1]):
            stats["disagreements"].append({"trial": trial, "what": "routes"})

        record = check_decoupling(code, certificate, target)
        if record["accepted"]:
            stats["certificates_accepted"] += 1
        else:
            stats["disagreements"].append({"trial": trial, "what": "certificate refused"})
            continue
        n = code.n()
        if record["k"] != logical_count(n, code.display()):
            stats["disagreements"].append({"trial": trial, "what": "k"})

        # A tampered certificate is refused unless it happens to be valid.
        tampered = certificate + [("sum", 0, 1, one(code.periods))]
        outcome = check_decoupling(code, tampered, target)
        stats["tampered_accepted" if outcome["accepted"] else "tampered_refused"] += 1

        if n <= 12:
            dx, dz = distances(n, code.display())
            tx, tz = distances(n, target.display())
            f = record["factors"]
            for d, t, forward, backward in (
                (dx, tx, f["x"], f["x_inverse"]),
                (dz, tz, f["z"], f["z_inverse"]),
            ):
                stats["distance_windows_checked"] += 1
                low, high = distance_window(d, forward, backward)
                if not low <= t <= high:
                    stats["disagreements"].append({"trial": trial, "what": "distance window"})
                if d != t:
                    stats["distance_changed"] += 1
    return stats


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--seed", type=int, default=451)
    parser.add_argument("--trials", type=int, default=30)
    args = parser.parse_args(argv)
    stats = sweep(seed=args.seed, trials=args.trials)
    json.dump(stats, sys.stdout, indent=2)
    sys.stdout.write("\n")
    return 1 if stats["disagreements"] else 0


if __name__ == "__main__":
    sys.exit(main())
