"""Falsification probe for the L-BRUHAT candidate (issue #672).

Builds the full Bruhat order of the symmetric group S_n (type A_{n-1}),
grades it by length, takes the GF(2) cover-incidence maps between
consecutive ranks, and checks that each composite of two consecutive maps
vanishes over GF(2). For every middle rank i it also reports the CSS
parameters (n, k) of the code with H_X = d_i (rank i -> rank i-1, read as
rows indexed by rank i-1) and H_Z = d_{i+1}^T.

It then compares unions of two intervals, which need not be convex, with
down-closed unions [e, w1] u [e, w2], which are, on S_4: for each, whether a
composite is nonzero and whether some middle rank has k > 0.

This is evidence only: a vanishing composite on small cases can falsify the
orthogonality claim but never confirms it. Not referenced by CI.
"""
from __future__ import annotations

import itertools
import sys


def inversions(p):
    return sum(1 for i, j in itertools.combinations(range(len(p)), 2) if p[i] > p[j])


def bruhat_ranks(n):
    perms = list(itertools.permutations(range(n)))
    ranks = {}
    for p in perms:
        ranks.setdefault(inversions(p), []).append(p)
    return ranks


def covers(u, w):
    # u is covered by w iff w = u * transposition and length(w) = length(u) + 1
    if inversions(w) != inversions(u) + 1:
        return False
    diff = [i for i in range(len(u)) if u[i] != w[i]]
    return len(diff) == 2 and u[diff[0]] == w[diff[1]] and u[diff[1]] == w[diff[0]]


def incidence(lower, upper):
    return [[1 if covers(u, w) else 0 for w in upper] for u in lower]


def gf2_rank(rows):
    rows = [int("".join(map(str, r)) or "0", 2) for r in rows]
    rank = 0
    while rows:
        pivot = max(rows)
        if pivot == 0:
            break
        rows.remove(pivot)
        top = pivot.bit_length() - 1
        rows = [r ^ pivot if (r >> top) & 1 else r for r in rows]
        rank += 1
    return rank


def matmul2(a, b):
    return [[sum(a[i][t] & b[t][j] for t in range(len(b))) % 2
             for j in range(len(b[0]))] for i in range(len(a))]


def probe(n):
    ranks = bruhat_ranks(n)
    top = max(ranks)
    ok = True
    for i in range(1, top):
        d_i = incidence(ranks[i - 1], ranks[i])        # rank i-1 x rank i
        d_ip1 = incidence(ranks[i], ranks[i + 1])      # rank i x rank i+1
        composite = matmul2(d_i, d_ip1)
        zero = all(v == 0 for row in composite for v in row)
        ok &= zero
        qubits = len(ranks[i])
        rx = gf2_rank(d_i)
        rz = gf2_rank([list(col) for col in zip(*d_ip1)])
        print(f"S_{n} rank {i}: composite zero={zero} n={qubits} "
              f"k={qubits - rx - rz} rank(H_X)={rx} rank(H_Z)={rz}")
    return ok


def bruhat_leq(n):
    """The Bruhat order on S_n as the reflexive-transitive closure of covers."""
    perms = list(itertools.permutations(range(n)))
    up = {u: {w for w in perms if covers(u, w)} for u in perms}
    leq = {}
    for u in perms:
        seen, stack = {u}, [u]
        while stack:
            for w in up[stack.pop()]:
                if w not in seen:
                    seen.add(w)
                    stack.append(w)
        leq[u] = seen
    return perms, leq


def subposet_report(elements):
    """For a subposet, whether every consecutive composite of the restricted
    cover maps vanishes over GF(2), and the largest k over middle ranks."""
    ranks = {}
    for p in elements:
        ranks.setdefault(inversions(p), []).append(p)
    present = sorted(ranks)
    zero, best_k = True, 0
    for r in present:
        if r - 1 not in ranks or r + 1 not in ranks:
            continue
        d_r = incidence(ranks[r - 1], ranks[r])
        d_rp1 = incidence(ranks[r], ranks[r + 1])
        if any(v for row in matmul2(d_r, d_rp1) for v in row):
            zero = False
        k = (len(ranks[r]) - gf2_rank(d_r)
             - gf2_rank([list(col) for col in zip(*d_rp1)]))
        best_k = max(best_k, k)
    return zero, best_k


def unions_probe(n=4, trials=2000, seed=683):
    """Unions of two intervals (convexity not guaranteed) against down-closed
    unions [e, w1] u [e, w2] (convex), on S_n."""
    import random
    rng = random.Random(seed)
    perms, leq = bruhat_leq(n)
    geq = {w: {u for u in perms if w in leq[u]} for w in perms}

    def interval(u, w):
        return leq[u] & geq[w]

    pairs = [(u, w) for u in perms for w in leq[u] if inversions(w) - inversions(u) >= 2]
    bad = 0
    for _ in range(trials):
        (u1, w1), (u2, w2) = rng.choice(pairs), rng.choice(pairs)
        zero, _ = subposet_report(interval(u1, w1) | interval(u2, w2))
        bad += not zero
    e = tuple(range(n))
    down_bad, down_k = 0, 0
    for w1, w2 in itertools.combinations(perms, 2):
        zero, k = subposet_report(interval(e, w1) | interval(e, w2))
        down_bad += not zero
        down_k += k > 0
    total = len(perms) * (len(perms) - 1) // 2
    print(f"S_{n} unions of two intervals: {bad}/{trials} with a nonzero composite")
    print(f"S_{n} down-closed unions [e,w1] u [e,w2]: {down_bad}/{total} nonzero "
          f"composite, {down_k}/{total} with k > 0 at some middle rank")
    return down_bad == 0


if __name__ == "__main__":
    sizes = [int(a) for a in sys.argv[1:]] or [3, 4]
    ok = all(probe(n) for n in sizes)
    ok &= unions_probe(4)
    sys.exit(0 if ok else 1)
