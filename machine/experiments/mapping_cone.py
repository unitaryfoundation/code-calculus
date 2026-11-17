#!/usr/bin/env python3
"""Exhaustive checks for the mapping-cone candidate of issue #449.

`design/MAPPING_CONE_CONSTRUCTOR.md` states the cone of a chain map between
two two-term complexes over F_2 as a typed constructor candidate and derives
its cells. This script builds the cone from explicit matrices and checks
each derived statement by enumeration on small instances:

* the logical count from the long exact sequence;
* the split of the Z distance into the classes that come from H_1(B) and
  the classes that map to a nonzero element of H_0(A), and the scope of the
  one-line formula recorded in `design/LEFT_IN_PAPERS.md` (claim 6.2b);
* the bounds computable from the factors;
* the X distance as the Z distance of the cone of the transposed map;
* the identification of the cone with the strict pushout of B and the cone
  of the identity of A, as complexes, and the failure of that
  identification to preserve the quotient norm.

Agreement is evidence that the derivations are transcribed as stated, not a
proof (AGENTS.md). Nothing here is a consumer path, and no constructor is
admitted by this script.

Conventions. A vector is a bitmask. A linear map is the list of the images
of the standard basis vectors of its source.
"""

import argparse
import json
import random
import sys


def popcount(x):
    return bin(x).count("1")


def apply(m, v):
    out = 0
    for j, image in enumerate(m):
        if v >> j & 1:
            out ^= image
    return out


def transpose(m, target_dim):
    return [sum(1 << j for j, image in enumerate(m) if image >> i & 1) for i in range(target_dim)]


def reduce_basis(vectors):
    basis = {}
    for v in vectors:
        while v:
            lead = v.bit_length() - 1
            if lead not in basis:
                basis[lead] = v
                break
            v ^= basis[lead]
    return basis


def in_span(basis, v):
    while v:
        lead = v.bit_length() - 1
        if lead not in basis:
            return False
        v ^= basis[lead]
    return True


def rank(vectors):
    return len(reduce_basis(vectors))


def kernel(m, source_dim):
    """All vectors of the source with zero image (small dimensions only)."""
    return [v for v in range(1 << source_dim) if apply(m, v) == 0]


def kernel_basis(m, source_dim):
    return list(reduce_basis(kernel(m, source_dim)).values())


def coordinates(basis, v):
    """The coefficient mask of `v` in the list `basis`, or None."""
    pivots = {}
    for index, b in enumerate(basis):
        combo = 1 << index
        while b:
            lead = b.bit_length() - 1
            if lead not in pivots:
                pivots[lead] = (b, combo)
                break
            other, other_combo = pivots[lead]
            b ^= other
            combo ^= other_combo
    out = 0
    while v:
        lead = v.bit_length() - 1
        if lead not in pivots:
            return None
        b, combo = pivots[lead]
        v ^= b
        out ^= combo
    return out


def map_from_basis(basis, images, dim):
    """The linear map sending `basis[i]` to `images[i]`, on standard vectors."""
    out = []
    for j in range(dim):
        coeffs = coordinates(basis, 1 << j)
        assert coeffs is not None
        value = 0
        for i, image in enumerate(images):
            if coeffs >> i & 1:
                value ^= image
        out.append(value)
    return out


def complete(vectors, dim):
    """Extend independent `vectors` to a basis with standard vectors."""
    out = list(vectors)
    for j in range(dim):
        if rank(out + [1 << j]) > len(out):
            out.append(1 << j)
    return out


class ChainMap:
    """A chain map f : A -> B between two-term complexes over F_2.

    A is d_a : A_1 -> A_0, B is d_b : B_1 -> B_0, and f = (f1, f0) with
    f1 : A_1 -> B_1 and f0 : A_0 -> B_0. `dims` is (a1, a0, b1, b0).
    """

    def __init__(self, dims, d_a, d_b, f1, f0):
        self.a1, self.a0, self.b1, self.b0 = dims
        self.d_a, self.d_b, self.f1, self.f0 = d_a, d_b, f1, f0
        assert len(d_a) == self.a1 and len(f1) == self.a1
        assert len(d_b) == self.b1 and len(f0) == self.a0

    def is_chain_map(self):
        return all(
            apply(self.d_b, self.f1[j]) == apply(self.f0, self.d_a[j]) for j in range(self.a1)
        )

    # The cone. Qubits are the basis of A_0 (low bits) and B_1 (high bits).

    def n(self):
        return self.a0 + self.b1

    def pack(self, a0_vec, b1_vec):
        return a0_vec | (b1_vec << self.a0)

    def unpack(self, v):
        return v & ((1 << self.a0) - 1), v >> self.a0

    def delta2(self):
        """C_2 = A_1 -> C_1: a_1 -> (d_a a_1, f1 a_1). The Z-rows."""
        return [self.pack(self.d_a[j], self.f1[j]) for j in range(self.a1)]

    def delta1(self):
        """C_1 -> C_0 = B_0: (a_0, b_1) -> f0 a_0 + d_b b_1."""
        return list(self.f0) + list(self.d_b)

    def display(self):
        """X-rows (one per basis element of B_0) and Z-rows (one per basis
        element of A_1), as supports over the qubits."""
        return transpose(self.delta1(), self.b0), self.delta2()

    def well_formed(self):
        xs, zs = self.display()
        return all(popcount(a & b) % 2 == 0 for a in xs for b in zs)

    def k(self):
        xs, zs = self.display()
        return self.n() - rank(xs) - rank(zs)

    def k_from_sequence(self):
        """dim coker(H_1 A -> H_1 B) + dim ker(H_0 A -> H_0 B)."""
        ker_a = kernel_basis(self.d_a, self.a1)
        ker_b = kernel_basis(self.d_b, self.b1)
        cokernel = len(ker_b) - rank([apply(self.f1, v) for v in ker_a])
        return cokernel + self.h0_kernel_dim()

    def h0_kernel_dim(self):
        """dim ker(f_* : A_0 / im d_a -> B_0 / im d_b)."""
        im_b = reduce_basis(self.d_b)
        preimage = [v for v in range(1 << self.a0) if in_span(im_b, apply(self.f0, v))]
        return rank(preimage) - rank(self.d_a)

    def h0_injective(self):
        return self.h0_kernel_dim() == 0

    # Distances, by enumeration.

    def cycles(self):
        d1 = self.delta1()
        return [v for v in range(1, 1 << self.n()) if apply(d1, v) == 0]

    def z_distance(self):
        """The least weight of a 1-cycle of the cone that is not a boundary."""
        boundaries = reduce_basis(self.delta2())
        weights = [popcount(v) for v in self.cycles() if not in_span(boundaries, v)]
        return min(weights) if weights else None

    def from_b(self):
        """D_B: the least weight of (d_a a_1, f1 a_1 + b_1) over a_1 in A_1
        and cycles b_1 of B outside f1(ker d_a). The formula of claim 6.2b."""
        image = reduce_basis([apply(self.f1, v) for v in kernel(self.d_a, self.a1)])
        best = None
        for b1 in kernel(self.d_b, self.b1):
            if in_span(image, b1):
                continue
            for a1 in range(1 << self.a1):
                w = popcount(apply(self.d_a, a1)) + popcount(apply(self.f1, a1) ^ b1)
                if best is None or w < best:
                    best = w
        return best

    def from_a(self):
        """D_A: the least weight of a cycle (a_0, b_1) with a_0 outside the
        image of d_a."""
        im_a = reduce_basis(self.d_a)
        weights = [popcount(v) for v in self.cycles() if not in_span(im_a, self.unpack(v)[0])]
        return min(weights) if weights else None

    def b_relative_distance(self):
        """The least weight of a cycle of B outside f1(ker d_a): an upper
        bound on D_B computed in B alone."""
        image = reduce_basis([apply(self.f1, v) for v in kernel(self.d_a, self.a1)])
        weights = [
            popcount(b1) for b1 in kernel(self.d_b, self.b1) if b1 and not in_span(image, b1)
        ]
        return min(weights) if weights else None

    def a_kernel_distance(self):
        """The least weight of a_0 outside im d_a with f0 a_0 in im d_b: a
        lower bound on D_A computed without B_1."""
        im_a, im_b = reduce_basis(self.d_a), reduce_basis(self.d_b)
        weights = [
            popcount(v)
            for v in range(1, 1 << self.a0)
            if not in_span(im_a, v) and in_span(im_b, apply(self.f0, v))
        ]
        return min(weights) if weights else None

    def transposed(self):
        """The chain map f^T : B^T -> A^T, whose cone has this cone's X-rows
        as its Z-rows, with the two blocks of qubits exchanged."""
        return ChainMap(
            (self.b0, self.b1, self.a0, self.a1),
            transpose(self.d_b, self.b0),
            transpose(self.d_a, self.a0),
            transpose(self.f0, self.b0),
            transpose(self.f1, self.b1),
        )

    def x_distance(self):
        xs, zs = self.display()
        x_basis = reduce_basis(xs)
        weights = [
            popcount(v)
            for v in range(1, 1 << self.n())
            if all(popcount(v & z) % 2 == 0 for z in zs) and not in_span(x_basis, v)
        ]
        return min(weights) if weights else None

    # The strict pushout of B <- A -> Cone(id_A), in degree 1:
    # (B_1 + A_0 + A_1) / {(f1 a, 0, a)}.

    def pushout_agrees(self):
        """phi(b_1, a_0, a_1) = (a_0, b_1 + f1 a_1) is onto the cone's C_1,
        its kernel is the relation subspace, and it intertwines the
        differentials in both degrees."""
        total = self.b1 + self.a0 + self.a1

        def split(v):
            b1 = v & ((1 << self.b1) - 1)
            a0 = (v >> self.b1) & ((1 << self.a0) - 1)
            a1 = v >> (self.b1 + self.a0)
            return b1, a0, a1

        def phi(v):
            b1, a0, a1 = split(v)
            return self.pack(a0, b1 ^ apply(self.f1, a1))

        images = [phi(1 << j) for j in range(total)]
        if rank(images) != self.n():
            return False
        relations = [
            apply(self.f1, 1 << j) | (1 << (self.b1 + self.a0 + j)) for j in range(self.a1)
        ]
        if any(phi(r) for r in relations) or total - rank(relations) != self.n():
            return False
        d1 = self.delta1()
        for j in range(total):
            b1, a0, a1 = split(1 << j)
            # Degree 1 -> 0 in the pushout, read in B_0 through
            # (b_0, a_0) -> b_0 + f0 a_0.
            down = apply(self.d_b, b1) ^ apply(self.f0, a0 ^ apply(self.d_a, a1))
            if down != apply(d1, images[j]):
                return False
        for j in range(self.a1):
            # Degree 2 -> 1: a_1 -> the class of (0, d_a a_1, a_1).
            up = (self.d_a[j] << self.b1) | (1 << (self.b1 + self.a0 + j))
            if phi(up) != self.delta2()[j]:
                return False
        return True

    def quotient_weight(self, v):
        """The quotient norm of the class of the cone element `v` in the
        pushout: the least weight of a representative in B_1 + A_0 + A_1."""
        a0, b1 = self.unpack(v)
        return popcount(a0) + min(
            popcount(b1 ^ apply(self.f1, a)) + popcount(a) for a in range(1 << self.a1)
        )

    def z_distance_quotient_norm(self):
        boundaries = reduce_basis(self.delta2())
        weights = [
            self.quotient_weight(v) for v in self.cycles() if not in_span(boundaries, v)
        ]
        return min(weights) if weights else None


def random_chain_map(rng, max_dim=3):
    a1, a0, b1, b0 = (rng.randrange(1, max_dim + 1) for _ in range(4))
    d_a = [rng.randrange(1 << a0) for _ in range(a1)]
    d_b = [rng.randrange(1 << b0) for _ in range(b1)]
    ker_a = kernel_basis(d_a, a1)
    ker_b = kernel(d_b, b1)
    basis1 = complete(ker_a, a1)
    images1 = [rng.choice(ker_b) for _ in ker_a] + [
        rng.randrange(1 << b1) for _ in range(a1 - len(ker_a))
    ]
    f1 = map_from_basis(basis1, images1, a1)
    # f0 is forced on im d_a and free on a complement.
    rest = basis1[len(ker_a):]
    forced = [apply(d_a, v) for v in rest]
    basis0 = complete(forced, a0)
    images0 = [apply(d_b, apply(f1, v)) for v in rest] + [
        rng.randrange(1 << b0) for _ in range(a0 - len(forced))
    ]
    f0 = map_from_basis(basis0, images0, a0)
    return ChainMap((a1, a0, b1, b0), d_a, d_b, f1, f0)


def formula_gap_instance():
    """The recorded formula is not the distance. A is 0 -> F and B is
    F^2 -> F with d_b(e_0) = d_b(e_1) = 1, and f0 = 0. The generator of A_0
    is not a boundary and maps to zero, so it is a cycle of weight 1 on its
    own, while the one class that comes from H_1(B) has weight 2."""
    return ChainMap((0, 1, 2, 1), [], [1, 1], [], [0])


def norm_gap_instance():
    """The pushout identification does not preserve the quotient norm. A is
    F -> F^2 with d_a(e) = 11, B is F^2 -> F with d_b(e_0) = d_b(e_1) = 1,
    f1(e) = 11, and f0(e_0) = f0(e_1) = 1. The cone is the [[4, 2, 2]] code
    with rows XXXX and ZZZZ, of Z distance 2. The cycle (0, 11) has weight 2
    in the cone and its class has quotient norm 1, through the
    representative with b_1 = 0 and a_1 = e."""
    return ChainMap((1, 2, 2, 1), [0b11], [1, 1], [0b11], [1, 1])


def sweep(seed=449, trials=600, max_dim=3):
    rng = random.Random(seed)
    stats = {
        "seed": seed,
        "trials": trials,
        "k_positive": 0,
        "formula_is_distance": 0,
        "formula_is_not_distance": 0,
        "h0_injective": 0,
        "x_distance_checked": 0,
        "norm_differs": 0,
        "disagreements": [],
    }

    def fail(trial, what):
        stats["disagreements"].append({"trial": trial, "what": what})

    for trial in range(trials):
        c = random_chain_map(rng, max_dim=max_dim)
        if not c.is_chain_map() or not c.well_formed():
            fail(trial, "chain map")
            continue
        if c.k() != c.k_from_sequence():
            fail(trial, "k")
        if not c.pushout_agrees():
            fail(trial, "pushout")
        d_z, d_b, d_a = c.z_distance(), c.from_b(), c.from_a()
        parts = [x for x in (d_b, d_a) if x is not None]
        if d_z != (min(parts) if parts else None):
            fail(trial, "split")
        if c.h0_injective():
            stats["h0_injective"] += 1
            if d_a is not None or d_z != d_b:
                fail(trial, "injective case")
        if d_z is not None:
            stats["k_positive"] += 1
            stats["formula_is_distance" if d_z == d_b else "formula_is_not_distance"] += 1
        rel, ker = c.b_relative_distance(), c.a_kernel_distance()
        if (d_b is None) != (rel is None) or (d_b is not None and d_b > rel):
            fail(trial, "upper bound")
        if (d_a is None) != (ker is None) or (d_a is not None and d_a < ker):
            fail(trial, "lower bound")
        if c.x_distance() != c.transposed().z_distance():
            fail(trial, "duality")
        stats["x_distance_checked"] += 1
        quotient = c.z_distance_quotient_norm()
        if d_z is not None:
            if quotient > d_z:
                fail(trial, "quotient norm exceeds weight")
            if quotient < d_z:
                stats["norm_differs"] += 1
    return stats


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--seed", type=int, default=449)
    parser.add_argument("--trials", type=int, default=600)
    parser.add_argument("--max-dim", type=int, default=3)
    args = parser.parse_args(argv)
    stats = sweep(seed=args.seed, trials=args.trials, max_dim=args.max_dim)
    json.dump(stats, sys.stdout, indent=2)
    sys.stdout.write("\n")
    return 1 if stats["disagreements"] else 0


if __name__ == "__main__":
    sys.exit(main())
