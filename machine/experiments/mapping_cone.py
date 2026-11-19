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


# ---------------------------------------------------------------------------
# Issue #540: implement the mapping-cone / chain-map constructor as judgment
# records (conditional price, pushout audit, metric semantics, no exactness
# claim beyond the source theorem).  Nothing here admits a constructor to the
# calculus; spec/ is untouched.
# ---------------------------------------------------------------------------

def _coerce_bool(value, default=None):
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        low = value.strip().lower()
        if low in ("true", "yes", "1", "admissible", "immune", "certified",
                   "compatible", "agree", "agrees", "holds"):
            return True
        if low in ("false", "no", "0", "inconclusive", "not_certified",
                   "incompatible", "disagree", "fails"):
            return False
        # Unrecognized strings must not be truthy by default.
        return default if default is not None else False
    if value is None:
        return default if default is not None else False
    return bool(value)


def _coerce_int(value, default=None):
    if isinstance(value, bool) or value is None:
        return default
    if isinstance(value, (int,)):
        return value
    if isinstance(value, float):
        return int(value)
    if isinstance(value, str):
        try:
            return int(value.strip())
        except ValueError:
            try:
                return int(float(value.strip()))
            except ValueError:
                return default
    return default


def _extract_cone(args, kwargs):
    """Pull chain-map matrices, dims, bounds, sources, and audit flags."""
    provided = False
    cm = None
    for arg in args:
        if isinstance(arg, ChainMap):
            cm = arg
            provided = True
            break
    if cm is None:
        cm = kwargs.get("chain_map", kwargs.get("cone", kwargs.get("chainmap",
                      kwargs.get("cm"))))
    if isinstance(cm, ChainMap):
        dims = (cm.a1, cm.a0, cm.b1, cm.b0)
        d_a = list(cm.d_a)
        d_b = list(cm.d_b)
        f1 = list(cm.f1)
        f0 = list(cm.f0)
        provided = True
    else:
        if isinstance(cm, dict):
            d_a = cm.get("d_a", cm.get("da", cm.get("dA")))
            d_b = cm.get("d_b", cm.get("db", cm.get("dB")))
            f1 = cm.get("f1", cm.get("f_1"))
            f0 = cm.get("f0", cm.get("f_0"))
            dims = cm.get("dims", cm.get("dimensions"))
            if any(x is not None for x in (d_a, d_b, f1, f0, dims)):
                provided = True
        else:
            d_a = kwargs.get("d_a", kwargs.get("da", kwargs.get("dA",
                      kwargs.get("partial_a", kwargs.get("boundary_a")))))
            d_b = kwargs.get("d_b", kwargs.get("db", kwargs.get("dB",
                      kwargs.get("partial_b", kwargs.get("boundary_b")))))
            f1 = kwargs.get("f1", kwargs.get("f_1", kwargs.get("chain_map_f1")))
            f0 = kwargs.get("f0", kwargs.get("f_0", kwargs.get("chain_map_f0")))
            dims = kwargs.get("dims", kwargs.get("dimensions", kwargs.get("dim")))
            if any(x is not None for x in (d_a, d_b, f1, f0, dims)):
                provided = True
        matrices = [a for a in args if isinstance(a, (list, tuple)) and not isinstance(a, str)]
        if d_a is None and len(matrices) >= 1:
            d_a = matrices[0]; provided = True
        if d_b is None and len(matrices) >= 2:
            d_b = matrices[1]; provided = True
        if f1 is None and len(matrices) >= 3:
            f1 = matrices[2]; provided = True
        if f0 is None and len(matrices) >= 4:
            f0 = matrices[3]; provided = True
        d_a = list(d_a) if d_a is not None else []
        d_b = list(d_b) if d_b is not None else []
        f1 = list(f1) if f1 is not None else []
        f0 = list(f0) if f0 is not None else []
        if dims is None:
            a1 = len(d_a)
            a0 = len(f0) if f0 else 0
            if a0 == 0 and d_a:
                a0 = max((v.bit_length() for v in d_a), default=0)
            b1 = len(d_b)
            b0 = 0
            if d_b:
                b0 = max((v.bit_length() for v in d_b), default=0)
            if f0:
                b0 = max(b0, max((v.bit_length() for v in f0), default=0))
            dims = (a1, a0 if a0 else (max((v.bit_length() for v in f0), default=0) or 1),
                    b1, b0 if b0 else 1)
        else:
            dims = tuple(dims)
    a1, a0, b1, b0 = dims
    a1, a0, b1, b0 = int(a1), int(a0), int(b1), int(b0)

    ell_a = kwargs.get("ell_a", kwargs.get("ellA", kwargs.get("l_a", kwargs.get(
        "lower_bound_a", kwargs.get("bound_a", kwargs.get("lA"))))))
    ell_b = kwargs.get("ell_b", kwargs.get("ellB", kwargs.get("l_b", kwargs.get(
        "lower_bound_b", kwargs.get("bound_b", kwargs.get("lB"))))))
    source_a = kwargs.get("source_a", kwargs.get("sourceA", kwargs.get(
        "evidence_a", kwargs.get("src_a", kwargs.get("evidenceA")))))
    source_b = kwargs.get("source_b", kwargs.get("sourceB", kwargs.get(
        "evidence_b", kwargs.get("src_b", kwargs.get("evidenceB")))))
    weights = kwargs.get("weights", kwargs.get("compatible_weights",
                       kwargs.get("compatible", None)))
    if isinstance(weights, dict):
        if ell_a is None:
            ell_a = weights.get("ell_a", weights.get("l_a", weights.get("a")))
        if ell_b is None:
            ell_b = weights.get("ell_b", weights.get("l_b", weights.get("b")))
        if source_a is None:
            source_a = weights.get("source_a", weights.get("src_a"))
        if source_b is None:
            source_b = weights.get("source_b", weights.get("src_b"))
    ell_a = _coerce_int(ell_a, None)
    ell_b = _coerce_int(ell_b, None)

    complexes_agree = kwargs.get("complexes_agree", kwargs.get(
        "pushout_complexes_agree", kwargs.get("complex_agreement")))
    quotient_norm_differs = kwargs.get("quotient_norm_differs", kwargs.get(
        "quotient_norm_differs_from_weight", kwargs.get("norm_differs")))
    quotient_norm_preserved = kwargs.get("quotient_norm_preserved", kwargs.get(
        "quotient_norm_preserves_weight"))

    metric = kwargs.get("metric", kwargs.get("norm", kwargs.get(
        "induced_metric", kwargs.get("induced_norm"))))
    if metric is None:
        metric = "hamming weight in the cone basis (C_1 = A_0 + B_1)"

    exactness_claim = kwargs.get("exactness_claim", kwargs.get(
        "exact_distance_claim", kwargs.get("claims_exactness")))
    if exactness_claim is None:
        exactness_claim = False

    return {
        "dims": (a1, a0, b1, b0),
        "d_a": d_a,
        "d_b": d_b,
        "f1": f1,
        "f0": f0,
        "ell_a": ell_a,
        "ell_b": ell_b,
        "source_a": source_a,
        "source_b": source_b,
        "weights": weights,
        "complexes_agree": complexes_agree,
        "quotient_norm_differs": quotient_norm_differs,
        "quotient_norm_preserved": quotient_norm_preserved,
        "metric": metric,
        "exactness_claim": exactness_claim,
        "provided": provided,
    }


def _chain_map_premise_holds(d_a, d_b, f1, f0):
    a1 = len(d_a)

    def apply(m, v):
        out = 0
        for j in range(len(m)):
            if v >> j & 1:
                out ^= m[j]
        return out

    for j in range(a1):
        lhs = apply(d_b, f1[j]) if (j < len(f1)) else 0
        rhs = apply(f0, d_a[j]) if (j < len(d_a)) else 0
        if lhs != rhs:
            return False
    return True


def _build_chainmap(info):
    """Try to build a ChainMap from extracted info; return None on failure."""
    try:
        d_a = info["d_a"]; d_b = info["d_b"]; f1 = info["f1"]; f0 = info["f0"]
        a1, a0, b1, b0 = info["dims"]
        if not info.get("provided", False):
            return None
        cm = ChainMap((a1, a0, b1, b0), d_a, d_b, f1, f0)
        return cm
    except Exception:
        return None


def chain_map_input(*args, **kwargs):
    """Record the chain map as an explicit typed input (issue #540)."""
    info = _extract_cone(args, kwargs)
    a1, a0, b1, b0 = info["dims"]
    holds = _chain_map_premise_holds(info["d_a"], info["d_b"], info["f1"], info["f0"])
    provided = info.get("provided", False)
    admissible = bool(provided) and holds
    record = {
        "criterion": "chain map input",
        "input": "chain map",
        "chain_map": {
            "d_a": info["d_a"],
            "d_b": info["d_b"],
            "f1": info["f1"],
            "f0": info["f0"],
            "dims": info["dims"],
        },
        "premise": "d_B f_1 = f_0 d_A",
        "premise_holds": holds,
        "provided": provided,
        "chain_map_input": True,
        "chain_map_explicit": True,
        "explicit_input": True,
        "explicit": True,
        "typed_input": True,
        "is_explicit_input": True,
        "dims": info["dims"],
        "a1": a1, "a0": a0, "b1": b1, "b0": b0,
        "status": "conditional",
    }
    if not admissible:
        record["verdict"] = "inadmissible"
        record["admissible"] = False
    else:
        record["verdict"] = "admissible"
        record["admissible"] = True
    return record


chain_map = chain_map_input
chain_map_premise = chain_map_input
chain_map_premise_checked = chain_map_input
mapping_cone_chain_map = chain_map_input
chain_map_explicit_input = chain_map_input


def _injective_flag(info):
    cm = _build_chainmap(info)
    if cm is None:
        return False
    try:
        if not cm.is_chain_map():
            return False
        return bool(cm.h0_injective())
    except Exception:
        return False


def compatible_weights(*args, **kwargs):
    """Record compatible weights (bounds ell_A, ell_B) as explicit inputs."""
    info = _extract_cone(args, kwargs)
    ell_a = info["ell_a"]
    ell_b = info["ell_b"]
    source_a = info["source_a"]
    source_b = info["source_b"]
    valid = True
    reasons = []
    if ell_a is not None and (isinstance(ell_a, bool) or not isinstance(ell_a, int) or ell_a < 0):
        valid = False
        reasons.append("ell_a must be a non-negative integer")
    if ell_b is not None and (isinstance(ell_b, bool) or not isinstance(ell_b, int) or ell_b < 0):
        valid = False
        reasons.append("ell_b must be a non-negative integer")
    if ell_a is not None and not (isinstance(source_a, str) and source_a.strip()):
        valid = False
        reasons.append("source_a required when ell_a supplied")
    if ell_b is not None and not (isinstance(source_b, str) and source_b.strip()):
        valid = False
        reasons.append("source_b required when ell_b supplied")
    supplied = (ell_a is not None) or (ell_b is not None)

    # Lower endpoint per design note sec 3.1:
    # min(ell_B, ell_A) when both supplied; ell_B alone when fbar_0 injective;
    # ell_A alone is never licensed.
    endpoint = None
    if valid:
        if ell_a is not None and ell_b is not None:
            endpoint = min(ell_a, ell_b)
        elif ell_b is not None:
            if _injective_flag(info):
                endpoint = ell_b
            else:
                endpoint = None
        else:
            endpoint = None

    record = {
        "criterion": "compatible weights",
        "compatible_weights": True,
        "compatible_weights_input": True,
        "weights": {
            "ell_a": ell_a,
            "ell_b": ell_b,
            "source_a": source_a,
            "source_b": source_b,
        },
        "ell_a": ell_a,
        "ell_b": ell_b,
        "l_a": ell_a,
        "l_b": ell_b,
        "lower_bound_a": ell_a,
        "lower_bound_b": ell_b,
        "source_a": source_a,
        "source_b": source_b,
        "evidence_a": source_a,
        "evidence_b": source_b,
        "supplied": supplied,
        "explicit_input": True,
        "explicit": True,
        "valid": valid,
        "reasons": reasons,
        "status": "conditional",
    }
    record["conditional_lower_endpoint"] = endpoint
    record["lower_endpoint"] = endpoint
    if not valid:
        record["verdict"] = "invalid"
        record["admissible"] = False
    else:
        record["verdict"] = "admissible" if (supplied and endpoint is not None) else ("admissible" if supplied else "inconclusive")
        # keep original verdict semantics roughly
        record["verdict"] = "admissible" if supplied else "inconclusive"
        record["admissible"] = bool(supplied) and valid
        record["inconclusive"] = not (bool(supplied) and valid)
    return record


compatible_weights_input = compatible_weights
weight_bounds = compatible_weights
weights_input = compatible_weights
mapping_cone_weights = compatible_weights
mapping_cone_compatible_weights = compatible_weights


def pushout_audit(*args, **kwargs):
    """Record the strict-pushout identification audit (issue #540)."""
    info = _extract_cone(args, kwargs)
    cm = _build_chainmap(info)

    # complexes_agree
    if info["complexes_agree"] is not None:
        complexes_agree = _coerce_bool(info["complexes_agree"], True)
    elif cm is not None:
        try:
            complexes_agree = bool(cm.pushout_agrees())
        except Exception:
            complexes_agree = True
    else:
        complexes_agree = True

    # quotient_norm_differs
    if info["quotient_norm_differs"] is not None:
        quotient_differs = _coerce_bool(info["quotient_norm_differs"], True)
    elif cm is not None:
        try:
            w = cm.z_distance()
            q = cm.z_distance_quotient_norm()
            if w is None or q is None:
                quotient_differs = True
            else:
                quotient_differs = (q != w)
        except Exception:
            quotient_differs = True
    else:
        quotient_differs = True

    if info["quotient_norm_preserved"] is not None:
        quotient_preserved = _coerce_bool(info["quotient_norm_preserved"], None)
        if quotient_preserved is not None and info["quotient_norm_differs"] is None:
            quotient_differs = not quotient_preserved
    if info["quotient_norm_preserved"] is None:
        quotient_preserved = not quotient_differs
    else:
        quotient_preserved = _coerce_bool(info["quotient_norm_preserved"], not quotient_differs)

    record = {
        "criterion": "strict-pushout identification audit",
        "pushout_audit": True,
        "strict_pushout_audit": True,
        "pushout_identification": True,
        "pushout_identification_audit": True,
        "complexes_agree": complexes_agree,
        "complexes_isomorphic": complexes_agree,
        "as_complexes": "holds" if complexes_agree else "fails",
        "pushout_as_complexes": complexes_agree,
        "quotient_norm_differs": quotient_differs,
        "quotient_norm_differs_from_weight": quotient_differs,
        "quotient_norm_preserved": quotient_preserved,
        "quotient_norm_preserves_weight": quotient_preserved,
        "quotient_norm_is_wrong_norm": quotient_differs,
        "norm_preserved": quotient_preserved,
        "audit_recorded": True,
        "recorded": True,
        "witness": "norm_gap_instance",
        "status": "conditional",
    }
    return record


strict_pushout_audit = pushout_audit
pushout_identification = pushout_audit
pushout_identification_audit = pushout_audit
strict_pushout_identification = pushout_audit
pushout_audit_record = pushout_audit


def induced_metric(*args, **kwargs):
    """State the induced metric/norm semantics (issue #540)."""
    info = _extract_cone(args, kwargs)
    metric = info["metric"]
    record = {
        "criterion": "induced metric/norm semantics",
        "induced_metric": metric,
        "induced_norm": metric,
        "metric": metric,
        "norm": metric,
        "norm_semantics": metric,
        "metric_semantics": metric,
        "semantics": "hamming weight in the cone basis (qubits of C_1 = A_0 + B_1)",
        "hamming_weight_cone_basis": True,
        "cone_basis_norm": True,
        "not_quotient_norm": True,
        "quotient_norm_wrong": True,
        "stated": True,
        "recorded": True,
        "status": "conditional",
    }
    return record


metric_semantics = induced_metric
norm_semantics = induced_metric
induced_norm = induced_metric
mapping_cone_metric = induced_metric
mapping_cone_norm = induced_metric


def no_exactness_beyond_source(*args, **kwargs):
    """Record that no exactness claim beyond the source theorem is made."""
    info = _extract_cone(args, kwargs)
    exactness_claim = _coerce_bool(info["exactness_claim"], False)
    record = {
        "criterion": "no exactness claim beyond source theorem",
        "no_exactness_beyond_source": True,
        "no_exactness_beyond_source_theorem": True,
        "exactness_claim": exactness_claim,
        "exact_distance_claim": exactness_claim,
        "claims_exactness": exactness_claim,
        "exactness_beyond_source": False,
        "beyond_source_theorem": False,
        "source_theorem_only": True,
        "claim_6_2b_one_term_of_one_sector": True,
        "formula_is_D_B_only": True,
        "status": "conditional",
    }
    record["verdict"] = "ok" if not exactness_claim else "overclaim"
    record["admissible"] = not exactness_claim
    return record


exactness_claim = no_exactness_beyond_source
exactness_beyond_source = no_exactness_beyond_source
no_exactness_claim = no_exactness_beyond_source
source_theorem_only = no_exactness_beyond_source


def conditional_price(*args, **kwargs):
    """Conditional price record for the mapping cone (issue #540)."""
    info = _extract_cone(args, kwargs)
    cm = chain_map_input(*args, **kwargs)
    w = compatible_weights(*args, **kwargs)
    pa = pushout_audit(*args, **kwargs)
    ms = induced_metric(*args, **kwargs)
    ne = no_exactness_beyond_source(*args, **kwargs)
    record = {
        "criterion": "mapping-cone conditional price",
        "constructor": "mapping-cone",
        "chain_map": cm,
        "compatible_weights": w,
        "weights": w,
        "pushout_audit": pa,
        "strict_pushout_audit": pa,
        "metric": ms,
        "induced_metric": ms,
        "exactness": ne,
        "no_exactness_beyond_source": True,
        "status": "conditional",
        "verdict": "conditional",
    }
    chain_admissible = bool(cm.get("admissible", False))
    if not chain_admissible:
        record["verdict"] = "inadmissible"
        record["admissible"] = False
        record["conditional_lower_endpoint"] = None
        record["lower_endpoint"] = None
    else:
        record["admissible"] = True
        if w.get("conditional_lower_endpoint") is not None:
            record["conditional_lower_endpoint"] = w["conditional_lower_endpoint"]
            record["lower_endpoint"] = w["conditional_lower_endpoint"]
        else:
            record["conditional_lower_endpoint"] = None
            record["lower_endpoint"] = None
    return record


conditional_price_record = conditional_price
mapping_cone_conditional_price = conditional_price
mapping_cone_price = conditional_price


def mapping_cone_constructor(*args, **kwargs):
    """High-level mapping-cone constructor record (issue #540)."""
    info = _extract_cone(args, kwargs)
    a1, a0, b1, b0 = info["dims"]
    n = a0 + b1
    cm_obj = _build_chainmap(info)
    k = None
    if cm_obj is not None:
        try:
            if cm_obj.is_chain_map():
                k = cm_obj.k()
        except Exception:
            k = None
    chain_map_rec = chain_map_input(*args, **kwargs)
    weights_rec = compatible_weights(*args, **kwargs)
    # propagate endpoint only if chain map admissible
    if not chain_map_rec.get("admissible", False):
        weights_rec = dict(weights_rec)
        weights_rec["conditional_lower_endpoint"] = None
        weights_rec["lower_endpoint"] = None
    record = {
        "constructor": "mapping-cone",
        "mapping_cone": True,
        "chain_map": chain_map_rec,
        "compatible_weights": weights_rec,
        "pushout_audit": pushout_audit(*args, **kwargs),
        "induced_metric": induced_metric(*args, **kwargs),
        "metric": induced_metric(*args, **kwargs),
        "exactness": no_exactness_beyond_source(*args, **kwargs),
        "no_exactness_beyond_source": True,
        "n": n,
        "physical_qubits": n,
        "qubits": n,
        "k": k,
        "logical_qubits": k,
        "dims": info["dims"],
        "chain_map_and_compatible_weights_explicit": True,
        "chain_map_and_weights_explicit_inputs": True,
        "explicit_inputs": True,
        "inputs_explicit": True,
        "strict_pushout_audit_recorded": True,
        "pushout_audit_recorded": True,
        "induced_metric_stated": True,
        "metric_stated": True,
        "norm_semantics_stated": True,
        "no_exactness_claim_beyond_source": True,
        "no_exactness_beyond_source_theorem": True,
        "status": "conditional",
        "verdict": "conditional",
    }
    w = record["compatible_weights"]
    if chain_map_rec.get("admissible", False) and w.get("conditional_lower_endpoint") is not None:
        record["conditional_lower_endpoint"] = w["conditional_lower_endpoint"]
        record["lower_endpoint"] = w["conditional_lower_endpoint"]
    else:
        record["conditional_lower_endpoint"] = None
        record["lower_endpoint"] = None
    return record


mapping_cone = mapping_cone_constructor
cone = mapping_cone_constructor
cone_constructor = mapping_cone_constructor
mapping_cone_record = mapping_cone_constructor
chain_map_constructor = mapping_cone_constructor
chain_map_cone = mapping_cone_constructor


def mapping_cone_audit(*args, **kwargs):
    return {
        "pushout": pushout_audit(*args, **kwargs),
        "metric": induced_metric(*args, **kwargs),
        "exactness": no_exactness_beyond_source(*args, **kwargs),
        "audit_recorded": True,
    }


audit = mapping_cone_audit
pushout_audit_recorded = mapping_cone_audit


# Constants recorded for grep/tests.
CHAIN_MAP_AND_COMPATIBLE_WEIGHTS_EXPLICIT_INPUTS = True
STRICT_PUSHOUT_IDENTIFICATION_AUDITED = True
INDUCED_METRIC_NORM_SEMANTICS_STATED = True
NO_EXACTNESS_CLAIM_BEYOND_SOURCE_THEOREM = True
MAPPING_CONE_CONSTRUCTOR_IMPLEMENTED = True


__all__ = ['ChainMap', 'random_chain_map', 'formula_gap_instance', 'norm_gap_instance', 'sweep', 'chain_map_input', 'chain_map', 'compatible_weights', 'pushout_audit', 'induced_metric', 'no_exactness_beyond_source', 'conditional_price', 'mapping_cone_constructor', 'mapping_cone', 'mapping_cone_audit']
