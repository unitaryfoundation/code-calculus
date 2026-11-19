"""One-shot level-map transport (issue #450 / #541).

Records the one-shot level-map construction of Yuan (arXiv:2610.02137v1) as
a conditional family-level transport rule (`spec/JUDGMENT_LAYER.md` §2j): an
``[[n, k]]`` CSS code maps under the ``m``-sheet hollowed-tensor level map
``bar Gamma`` (Defs. 104/106/111/113/116, Eq. 249) with ``k' = k`` preserved
(Lemma 118, hypothesis) and ``n`` inflated far beyond ``m`` per tower level.
The transport direction is an *upper ceiling* on failure probability
(Theorem 81 Eq. (1)), not a lower guarantee on distance and not a block-length
ceiling; amplified distance lower bounds are ``unavailable``. Imported
framework lemmas (Lemma 118, Theorem 81, Remark 39, Definitions 104–116)
remain conditional hypotheses, not discharged facts.

Empirical checks here probe both Yuan's finite ``GF(2)`` hollowed-tensor
complex ``bar Gamma(C)`` on seeds satisfying Hypotheses 102–103
(``build_hollowed_tensor_level_map``, ``empirical_gamma_bar_probe``) and the
ordinary ``C (x) R`` tensor product (``repetition_tensor_code``,
``empirical_probe``), all marked ``empirical: True`` separately from the
conditional judgment.
"""

from __future__ import annotations

import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
MACHINE_DIR = os.path.dirname(HERE)
ROOT = os.path.dirname(MACHINE_DIR)
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from machine.gf2 import rank as gf2_rank  # noqa: E402
from machine.state import support_mask  # noqa: E402


TRANSPORT_DIRECTION = "upper ceiling"
DISTANCE_LOWER_BOUND_AVAILABLE = False


def _popcount(value: int) -> int:
    return bin(value).count("1")


def _validate_int(value: object, name: str, minimum: int = 1) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < minimum:
        if minimum == 1:
            raise ValueError(f"{name} must be a positive integer")
        if minimum == 0:
            raise ValueError(f"{name} must be a non-negative integer")
        raise ValueError(f"{name} must be an integer >= {minimum}")
    return value


def sheet_lower_floor(n: int, m: int = 2, levels: int = 1) -> int:
    """Naive ``n * m**levels`` sheet-multiplication lower scale factor.

    Per ``design/ONE_SHOT_LEVEL_MAP_TRANSPORT.md`` §1, one tower level of
    ``bar Gamma`` inflates ``n`` far beyond ``n * m``. This value is only the
    bare sheet-count floor, not the amplified block length and not an upper
    ceiling on block length.
    """
    _validate_int(n, "n", 1)
    _validate_int(m, "m", 2)
    _validate_int(levels, "levels", 1)
    return n * (m ** levels)


def distance_lower_bound() -> None:
    """No distance lower bound is claimed for the amplified code."""
    return None


def seed_locally_trivial(d_error: int, max_x_weight: int) -> bool:
    """Remark 39 seed local-triviality premise: ``d_error > max_x_weight``."""
    _validate_int(d_error, "d_error", 1)
    _validate_int(max_x_weight, "max_x_weight", 0)
    return d_error > max_x_weight


def imported_lemma_status() -> dict:
    """Status of the source paper's framework lemmas (all hypotheses)."""
    return {
        "hypotheses_102_103": "hypothesis (|x ^ z| = 2 when x < z; local graphs G^x, G^z connected)",
        "definitions_104_111_116": "hypothesis (transcribed in spec/JUDGMENT_LAYER.md §2j and constructed finitely for seeds)",
        "definitions_104_106_111_113_116_eq249": "hypothesis (Appendix A finite hollowed-tensor level map)",
        "lemma_117": "hypothesis (Eqs. (250)-(257) uniform sparsity bounds)",
        "lemma_118": "hypothesis (citation-based proof; Eq. (258) cohomology isomorphism)",
        "theorem_81": "hypothesis (Eq. (1) upper ceiling on RG failure probability)",
        "remark_39": "hypothesis (tower constants Eqs. (58)-(59) and seed local triviality)",
        "discharged": False,
        "empirical_proof": False,
    }


def _clean_support_rows(rows: object, n: int, label: str) -> list[list[int]]:
    if not isinstance(rows, (list, tuple)):
        raise ValueError(f"{label} must be a list or tuple of supports")
    cleaned: list[list[int]] = []
    for row in rows:
        if not isinstance(row, (list, tuple)):
            raise ValueError(f"each row in {label} must be a list or tuple of qubit indices")
        seen: set[int] = set()
        for q in row:
            if isinstance(q, bool) or not isinstance(q, int) or q < 0 or q >= n:
                raise ValueError(f"qubit index in {label} out of range 0..{n - 1}")
            if q in seen:
                raise ValueError(f"duplicate qubit index {q} in {label}")
            seen.add(q)
        cleaned.append(sorted(seen))
    return cleaned


def repetition_tensor_code(
    n: int,
    hx_rows: list[list[int]] | tuple[tuple[int, ...], ...],
    hz_rows: list[list[int]] | tuple[tuple[int, ...], ...],
    m: int = 2,
) -> dict:
    """Finite ``GF(2)`` chain-complex tensor product ``C (x) R``.

    Given a commuting ``n``-qubit CSS seed with X-check supports ``hx_rows``
    (``m_X`` rows) and Z-check supports ``hz_rows`` (``m_Z`` rows), forms the
    tensor product with the ``m``-vertex repetition chain complex ``R_1 -> R_0``
    (``dim R_0 = m``, ``dim R_1 = m - 1``, ``m >= 2``):

    - amplified qubits: ``n' = m * n + (m - 1) * m_X``;
    - amplified X-checks: ``m * m_X`` rows;
    - amplified Z-checks: ``m * m_Z + (m - 1) * n`` rows.

    This probes the ordinary tensor product ``C (x) R`` over ``GF(2)`` (via
    ``gf2.rank``); it is not Yuan's Def. 111/116 local-cone hollowed-tensor
    ``bar Gamma`` and does not discharge Lemma 118.
    """
    _validate_int(n, "n", 1)
    _validate_int(m, "m", 2)

    x_seed = _clean_support_rows(hx_rows, n, "hx_rows")
    z_seed = _clean_support_rows(hz_rows, n, "hz_rows")

    seed_x_masks = [support_mask(r) for r in x_seed]
    seed_z_masks = [support_mask(r) for r in z_seed]
    for xm in seed_x_masks:
        for zm in seed_z_masks:
            if _popcount(xm & zm) % 2 != 0:
                raise ValueError("seed rows do not commute")

    m_x = len(x_seed)
    n_amp = m * n + (m - 1) * m_x

    # Qubit indexing:
    # - block 0 (C_Q (x) R_0): qubit (q, s) -> q * m + s, 0 <= q < n, 0 <= s < m
    # - block 1 (C_X (x) R_1): check-edge (i, e) -> m * n + i * (m - 1) + e,
    #   0 <= i < m_X, 0 <= e < m - 1
    amp_x_rows: list[list[int]] = []
    for i, supp in enumerate(x_seed):
        for s in range(m):
            row = [q * m + s for q in supp]
            for e in range(m - 1):
                if s == e or s == e + 1:
                    row.append(m * n + i * (m - 1) + e)
            amp_x_rows.append(sorted(row))

    amp_z_rows: list[list[int]] = []
    for supp in z_seed:
        for s in range(m):
            amp_z_rows.append(sorted(q * m + s for q in supp))

    for q in range(n):
        incident_x = [i for i, supp in enumerate(x_seed) if q in supp]
        for e in range(m - 1):
            row = [q * m + e, q * m + (e + 1)]
            for i in incident_x:
                row.append(m * n + i * (m - 1) + e)
            amp_z_rows.append(sorted(row))

    amp_x_masks = [support_mask(r) for r in amp_x_rows]
    amp_z_masks = [support_mask(r) for r in amp_z_rows]
    commutes = all(
        _popcount(xm & zm) % 2 == 0
        for xm in amp_x_masks
        for zm in amp_z_masks
    )

    rank_x_seed = gf2_rank(seed_x_masks) if seed_x_masks else 0
    rank_z_seed = gf2_rank(seed_z_masks) if seed_z_masks else 0
    k_seed = n - rank_x_seed - rank_z_seed

    rank_x_amp = gf2_rank(amp_x_masks) if amp_x_masks else 0
    rank_z_amp = gf2_rank(amp_z_masks) if amp_z_masks else 0
    k_amp = n_amp - rank_x_amp - rank_z_amp

    return {
        "n_source": n,
        "k_source": k_seed,
        "m": m,
        "n_amplified": n_amp,
        "k_amplified": k_amp,
        "x_rows": amp_x_rows,
        "z_rows": amp_z_rows,
        "rank_x": rank_x_amp,
        "rank_z": rank_z_amp,
        "commutes": commutes,
        "k_preserved": k_amp == k_seed,
        "n_inflated": n_amp >= n * m > n,
    }


def _connected_local_graph(nodes_left: list, nodes_right: list, edges: list[tuple]) -> bool:
    """Check connectivity of a finite bipartite local graph ``G^u``."""
    nodes = [("L", u) for u in nodes_left] + [("R", v) for v in nodes_right]
    if not nodes:
        return False
    adj: dict[tuple, set[tuple]] = {node: set() for node in nodes}
    for u, v in edges:
        adj[("L", u)].add(("R", v))
        adj[("R", v)].add(("L", u))
    seen = {nodes[0]}
    stack = [nodes[0]]
    while stack:
        cur = stack.pop()
        for nb in adj[cur]:
            if nb not in seen:
                seen.add(nb)
                stack.append(nb)
    return len(seen) == len(nodes)


def build_hollowed_tensor_level_map(
    n: int,
    hx_rows: list[list[int]] | tuple[tuple[int, ...], ...],
    hz_rows: list[list[int]] | tuple[tuple[int, ...], ...],
    m: int = 2,
) -> dict:
    """Yuan's finite hollowed-tensor level map ``bar Gamma(C)`` (Eq. (249)).

    Implements Appendix A Definitions 104, 106, 111, 113, and 116 of
    Yuan (arXiv:2610.02137v1) for a finite CSS seed ``C`` satisfying
    Hypotheses 102 and 103:

    - every pair ``(x, z)`` of checks shares either 0 or 2 qubits
      (``|x ^ z| = 2`` whenever ``x < z``);
    - local graphs ``G^x`` (vertices ``q, z > x``) and ``G^z`` (vertices
      ``x, q < z``) are non-empty and connected for all checks.

    Returns an empirical dictionary describing ``X(Gamma) -> Q(Gamma) ->
    Z(Gamma) -> MZ(bar Gamma)``, commutativity, ``gf2.rank`` cohomology
    counts ``(H_X, H_Q, H_Z)``, and Lemma 117 weight/degree checks.
    """
    _validate_int(n, "n", 1)
    _validate_int(m, "m", 2)

    x_seed = _clean_support_rows(hx_rows, n, "hx_rows")
    z_seed = _clean_support_rows(hz_rows, n, "hz_rows")
    if not x_seed or not z_seed:
        raise ValueError("seed must contain at least one X-check and one Z-check")
    if any(not row for row in x_seed) or any(not row for row in z_seed):
        raise ValueError("checks must have non-empty support (Hypothesis 103)")

    num_x = len(x_seed)
    num_z = len(z_seed)
    x_to_q = [set(s) for s in x_seed]
    z_to_q = [set(s) for s in z_seed]
    q_to_x: list[set[int]] = [set() for _ in range(n)]
    q_to_z: list[set[int]] = [set() for _ in range(n)]
    for x, qs in enumerate(x_to_q):
        for q in qs:
            q_to_x[q].add(x)
    for z, qs in enumerate(z_to_q):
        for q in qs:
            q_to_z[q].add(z)

    # Hypothesis 102: |x ^ z| = 2 whenever x < z (also verifies CSS commutation).
    xz_overlap: dict[tuple[int, int], tuple[int, int]] = {}
    for x in range(num_x):
        for z in range(num_z):
            ov = sorted(x_to_q[x] & z_to_q[z])
            if ov:
                if len(ov) % 2 != 0:
                    raise ValueError("seed rows do not commute")
                if len(ov) != 2:
                    raise ValueError(
                        f"Hypothesis 102 requires |x ^ z| = 2 whenever x < z "
                        f"(got {len(ov)} for x={x}, z={z})"
                    )
                xz_overlap[(x, z)] = (ov[0], ov[1])

    # Hypothesis 103: local graphs G^x and G^z connected for every check.
    for x in range(num_x):
        qs = sorted(x_to_q[x])
        zs = sorted(z for z in range(num_z) if (x, z) in xz_overlap)
        edges = [(q, z) for z in zs for q in xz_overlap[(x, z)]]
        if not _connected_local_graph(qs, zs, edges):
            raise ValueError(f"Hypothesis 103 requires connected local graph G^x (failed at x={x})")
    for z in range(num_z):
        xs = sorted(x for x in range(num_x) if (x, z) in xz_overlap)
        qs = sorted(z_to_q[z])
        edges = [(x, q) for x in xs for q in xz_overlap[(x, z)]]
        if not _connected_local_graph(xs, qs, edges):
            raise ValueError(f"Hypothesis 103 requires connected local graph G^z (failed at z={z})")

    def _cycle_basis_gx(x: int) -> list[tuple[tuple[int, ...], tuple[tuple[int, int], ...]]]:
        qs = sorted(x_to_q[x])
        zs = sorted(z for z in range(num_z) if (x, z) in xz_overlap)
        adj: dict[tuple, list[tuple]] = {("q", q): [] for q in qs}
        for z in zs:
            adj[("z", z)] = []
        edges: list[tuple[int, int]] = []
        for z in zs:
            for q in xz_overlap[(x, z)]:
                edges.append((q, z))
                adj[("q", q)].append(("z", z))
                adj[("z", z)].append(("q", q))
        root = ("q", qs[0])
        parent: dict[tuple, tuple | None] = {root: None}
        tree_edges: set[tuple[int, int]] = set()
        stack = [root]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if v not in parent:
                    parent[v] = u
                    edge = (u[1], v[1]) if u[0] == "q" else (v[1], u[1])
                    tree_edges.add(edge)
                    stack.append(v)
        cycles = []
        for q, z in edges:
            if (q, z) in tree_edges:
                continue
            p1, u = [], ("q", q)
            while u is not None:
                p1.append(u)
                u = parent[u]
            p2, u = [], ("z", z)
            while u is not None:
                p2.append(u)
                u = parent[u]
            s2 = set(p2)
            lca = next(node for node in p1 if node in s2)
            qz_set = {(q, z)}
            for path in (p1[:p1.index(lca) + 1], p2[:p2.index(lca) + 1]):
                for a, b in zip(path, path[1:]):
                    edge = (a[1], b[1]) if a[0] == "q" else (b[1], a[1])
                    qz_set ^= {edge}
            z_set = {zz for _, zz in qz_set}
            cycles.append((tuple(sorted(z_set)), tuple(sorted(qz_set))))
        return cycles

    vertices = list(range(m))
    edges_r = list(range(m - 1))

    x_cells: list[tuple] = []
    q_cells: list[tuple] = []
    z_cells: list[tuple] = []
    mz_cells: list[tuple] = []

    for x in range(num_x):
        qs = sorted(x_to_q[x])
        zs = sorted(z for z in range(num_z) if (x, z) in xz_overlap)
        cyc_basis = _cycle_basis_gx(x)
        for v in vertices:
            x_cells.append(("x", x, "x", x, v))
            for q in qs:
                x_cells.append(("x", x, "q", q, v))
            for z in zs:
                x_cells.append(("x", x, "z", z, v))
            for q in qs:
                q_cells.append(("x", x, "xq", q, v))
            for z in zs:
                for q in xz_overlap[(x, z)]:
                    q_cells.append(("x", x, "qz", (q, z), v))
            for z in zs:
                z_cells.append(("x", x, "xz", z, v))
        for e in edges_r:
            for q in qs:
                q_cells.append(("x", x, "qe", q, e))
            for z in zs:
                q_cells.append(("x", x, "ze", z, e))
            for z in zs:
                for q in xz_overlap[(x, z)]:
                    z_cells.append(("x", x, "qze", (q, z), e))
            for cid, (z_tup, qz_tup) in enumerate(cyc_basis):
                mz_cells.append(("x", x, "c", (cid, z_tup, qz_tup), e))

    for q in range(n):
        zs = sorted(q_to_z[q])
        for v in vertices:
            q_cells.append(("q", q, "q", q, v))
            for z in zs:
                q_cells.append(("q", q, "z", z, v))
                z_cells.append(("q", q, "qz", z, v))
        if zs:
            z0 = zs[0]
            for e in edges_r:
                for z in zs:
                    z_cells.append(("q", q, "ze", z, e))
                for zi in zs[1:]:
                    mz_cells.append(("q", q, "gamma", (z0, zi), e))

    for z in range(num_z):
        for v in vertices:
            z_cells.append(("z", z, "z", z, v))
        for e in edges_r:
            mz_cells.append(("z", z, "ze", z, e))

    q_idx = {cell: idx for idx, cell in enumerate(q_cells)}
    z_idx = {cell: idx for idx, cell in enumerate(z_cells)}

    hx_supports: list[list[int]] = []
    for cell in x_cells:
        _, x, typ, val, v = cell
        sup = []
        if typ == "x":
            for q in sorted(x_to_q[x]):
                sup.append(q_idx[("x", x, "xq", q, v)])
        elif typ == "q":
            q = val
            sup.append(q_idx[("x", x, "xq", q, v)])
            for z in sorted(q_to_z[q]):
                if (x, z) in xz_overlap:
                    sup.append(q_idx[("x", x, "qz", (q, z), v)])
            for e in edges_r:
                if v in (e, e + 1):
                    sup.append(q_idx[("x", x, "qe", q, e)])
            sup.append(q_idx[("q", q, "q", q, v)])
        elif typ == "z":
            z = val
            for q in xz_overlap[(x, z)]:
                sup.append(q_idx[("x", x, "qz", (q, z), v)])
                sup.append(q_idx[("q", q, "z", z, v)])
            for e in edges_r:
                if v in (e, e + 1):
                    sup.append(q_idx[("x", x, "ze", z, e)])
        hx_supports.append(sorted(sup))

    hz_supports: list[list[int]] = []
    for cell in z_cells:
        layer = cell[0]
        sup = []
        if layer == "x":
            _, x, typ, val, ve = cell
            if typ == "xz":
                z, v = val, ve
                q0, q1 = xz_overlap[(x, z)]
                sup.extend([
                    q_idx[("x", x, "xq", q0, v)],
                    q_idx[("x", x, "xq", q1, v)],
                    q_idx[("x", x, "qz", (q0, z), v)],
                    q_idx[("x", x, "qz", (q1, z), v)],
                ])
            elif typ == "qze":
                (q, z), e = val, ve
                sup.extend([
                    q_idx[("x", x, "qz", (q, z), e)],
                    q_idx[("x", x, "qz", (q, z), e + 1)],
                    q_idx[("x", x, "qe", q, e)],
                    q_idx[("x", x, "ze", z, e)],
                ])
        elif layer == "q":
            _, q, typ, val, ve = cell
            if typ == "qz":
                z, v = val, ve
                sup.extend([q_idx[("q", q, "q", q, v)], q_idx[("q", q, "z", z, v)]])
                for x in sorted(q_to_x[q]):
                    sup.append(q_idx[("x", x, "qz", (q, z), v)])
            elif typ == "ze":
                z, e = val, ve
                sup.extend([q_idx[("q", q, "z", z, e)], q_idx[("q", q, "z", z, e + 1)]])
                for x in sorted(q_to_x[q]):
                    sup.append(q_idx[("x", x, "ze", z, e)])
        elif layer == "z":
            _, z, _, _, v = cell
            for q in sorted(z_to_q[z]):
                sup.append(q_idx[("q", q, "z", z, v)])
        hz_supports.append(sorted(sup))

    mz_supports: list[list[int]] = []
    for cell in mz_cells:
        layer = cell[0]
        sup = []
        if layer == "x":
            _, x, _, (_, z_tup, qz_tup), e = cell
            for z in z_tup:
                sup.append(z_idx[("x", x, "xz", z, e)])
                sup.append(z_idx[("x", x, "xz", z, e + 1)])
            for q, z in qz_tup:
                sup.append(z_idx[("x", x, "qze", (q, z), e)])
        elif layer == "q":
            _, q, _, (z0, zi), e = cell
            for z in (z0, zi):
                sup.append(z_idx[("q", q, "qz", z, e)])
                sup.append(z_idx[("q", q, "qz", z, e + 1)])
                sup.append(z_idx[("q", q, "ze", z, e)])
                for x in sorted(q_to_x[q]):
                    sup.append(z_idx[("x", x, "qze", (q, z), e)])
        elif layer == "z":
            _, z, _, _, e = cell
            sup.append(z_idx[("z", z, "z", z, e)])
            sup.append(z_idx[("z", z, "z", z, e + 1)])
            for q in sorted(z_to_q[z]):
                sup.append(z_idx[("q", q, "ze", z, e)])
        mz_supports.append(sorted(sup))

    hx_masks = [support_mask(s) for s in hx_supports]
    hz_masks = [support_mask(s) for s in hz_supports]
    commutes = all(
        _popcount(xm & zm) % 2 == 0
        for xm in hx_masks
        for zm in hz_masks
    )
    meta_checks_commute = all(
        _xor_masks([hz_masks[zi] for zi in mz_sup]) == 0
        for mz_sup in mz_supports
    )

    seed_x_masks = [support_mask(r) for r in x_seed]
    seed_z_masks = [support_mask(r) for r in z_seed]
    rank_x_seed = gf2_rank(seed_x_masks)
    rank_z_seed = gf2_rank(seed_z_masks)
    k_seed = n - rank_x_seed - rank_z_seed
    dim_hx_seed = len(x_seed) - rank_x_seed
    dim_hz_seed = len(z_seed) - rank_z_seed

    n_amp = len(q_cells)
    rank_x_amp = gf2_rank(hx_masks)
    rank_z_amp = gf2_rank(hz_masks)
    rank_mz_amp = gf2_rank([support_mask(s) for s in mz_supports]) if mz_supports else 0
    k_amp = n_amp - rank_x_amp - rank_z_amp
    dim_hx_amp = len(x_cells) - rank_x_amp
    dim_hz_amp = len(z_cells) - rank_z_amp - rank_mz_amp

    # Seed & amplified sparsity parameters for Lemma 117 Eqs. (250)-(255).
    w_x_seed = max(len(r) for r in x_seed)
    w_z_seed = max(len(r) for r in z_seed)
    d_x_seed = max((len(qs) for qs in q_to_x), default=0)
    d_z_seed = max((len(qs) for qs in q_to_z), default=0)

    q_deg_x = [0] * n_amp
    for sup in hx_supports:
        for q in sup:
            q_deg_x[q] += 1
    q_deg_z = [0] * n_amp
    for sup in hz_supports:
        for q in sup:
            q_deg_z[q] += 1
    z_deg_mz = [0] * len(z_cells)
    for sup in mz_supports:
        for zi in sup:
            z_deg_mz[zi] += 1

    w_x_amp = max((len(s) for s in hx_supports), default=0)
    w_z_amp = max((len(s) for s in hz_supports), default=0)
    d_x_amp = max(q_deg_x, default=0)
    d_z_amp = max(q_deg_z, default=0)
    w_mz_amp = max((len(s) for s in mz_supports), default=0)
    d_mz_amp = max(z_deg_mz, default=0)

    c_sheet = 3 if m == 2 else 4
    r_star = max((len(_cycle_basis_gx(x)) for x in range(num_x)), default=0)
    lemma_117_bounds = {
        "w_x_bound": max(w_x_seed, d_z_seed + c_sheet, 2 + c_sheet),
        "d_z_bound": max(d_z_seed, 4),
        "d_z_eq_251_printed": max(d_z_seed, c_sheet),
        "w_z_bound": max(w_z_seed, d_x_seed + 2, 4),
        "d_x_bound": max(d_x_seed, 2),
        "w_mz_bound": max(4 * w_x_seed, 6 + 2 * d_x_seed, 2 + w_z_seed),
        "d_mz_bound": 2 * max(r_star, d_z_seed - 1, 1),
        "r_star": r_star,
        "r_star_bound": (w_x_seed * d_z_seed) // 2,
    }
    sparsity_ok = (
        w_x_amp <= lemma_117_bounds["w_x_bound"]
        and d_z_amp <= lemma_117_bounds["d_z_bound"]
        and w_z_amp <= lemma_117_bounds["w_z_bound"]
        and d_x_amp <= lemma_117_bounds["d_x_bound"]
        and w_mz_amp <= lemma_117_bounds["w_mz_bound"]
        and d_mz_amp <= lemma_117_bounds["d_mz_bound"]
        and r_star <= lemma_117_bounds["r_star_bound"]
    )

    return {
        "construction": "Yuan Appendix A bar Gamma(C) (Defs. 104/106/111/113/116, Eq. 249)",
        "n_source": n,
        "k_source": k_seed,
        "m": m,
        "n_amplified": n_amp,
        "k_amplified": k_amp,
        "n_sheet_lower_floor": n * m,
        "n_exceeds_xm": n_amp > n * m,
        "x_rows": hx_supports,
        "z_rows": hz_supports,
        "mz_rows": mz_supports,
        "rank_x": rank_x_amp,
        "rank_z": rank_z_amp,
        "rank_mz": rank_mz_amp,
        "dim_hx_source": dim_hx_seed,
        "dim_hx_amplified": dim_hx_amp,
        "dim_hz_source": dim_hz_seed,
        "dim_hz_amplified": dim_hz_amp,
        "commutes": commutes,
        "meta_checks_commute": meta_checks_commute,
        "k_preserved": k_amp == k_seed,
        "hx_preserved": dim_hx_amp == dim_hx_seed,
        "hz_preserved": dim_hz_amp == dim_hz_seed,
        "weights": {
            "w_x": w_x_amp, "w_z": w_z_amp,
            "d_x": d_x_amp, "d_z": d_z_amp,
            "w_mz": w_mz_amp, "d_mz": d_mz_amp,
        },
        "lemma_117_bounds": lemma_117_bounds,
        "sparsity_within_lemma_117": sparsity_ok,
        "empirical": True,
    }


def _xor_masks(masks: list[int]) -> int:
    acc = 0
    for m_val in masks:
        acc ^= m_val
    return acc


def dual_hollowed_tensor_level_map(
    n: int,
    hx_rows: list[list[int]] | tuple[tuple[int, ...], ...],
    hz_rows: list[list[int]] | tuple[tuple[int, ...], ...],
    m: int = 2,
) -> dict:
    """Dual hollowed-tensor map ``bar Gamma_*(C) = bar Gamma(C^T)^T``."""
    transposed = build_hollowed_tensor_level_map(n, hz_rows, hx_rows, m=m)
    return {
        **transposed,
        "construction": "Yuan Appendix A dual bar Gamma_*(C) = bar Gamma(C^T)^T",
        "x_rows": transposed["z_rows"],
        "z_rows": transposed["x_rows"],
        "mx_rows": transposed["mz_rows"],
        "mz_rows": [],
        "rank_x": transposed["rank_z"],
        "rank_z": transposed["rank_x"],
        "dim_hx_source": transposed["dim_hz_source"],
        "dim_hz_source": transposed["dim_hx_source"],
        "dim_hx_amplified": transposed["dim_hz_amplified"],
        "dim_hz_amplified": transposed["dim_hx_amplified"],
    }


def _toric_seed(l1: int, l2: int) -> tuple[int, list[list[int]], list[list[int]]]:
    def qh(r: int, c: int) -> int:
        return (r % l1) * l2 + (c % l2)

    def qv(r: int, c: int) -> int:
        return l1 * l2 + (r % l1) * l2 + (c % l2)

    hx = []
    hz = []
    for r in range(l1):
        for c in range(l2):
            hx.append([qh(r, c), qh(r, c - 1), qv(r, c), qv(r - 1, c)])
            hz.append([qh(r, c), qh(r + 1, c), qv(r, c), qv(r, c + 1)])
    return 2 * l1 * l2, hx, hz


def empirical_gamma_bar_probe(
    toric_sizes: tuple[tuple[int, int], ...] = ((2, 3), (3, 3)),
    sheets: tuple[int, ...] = (2, 3),
) -> dict:
    """Separated empirical probe of Yuan's finite ``bar Gamma(C)`` construction.

    Checks ``build_hollowed_tensor_level_map`` (Defs. 104/106/111/113/116,
    Eq. (249)) on finite toric seeds satisfying Hypotheses 102–103. Marked
    ``empirical: True`` and separated from ``spec/JUDGMENT_LAYER.md`` §2j;
    never discharges Lemma 118 or establishes any distance bound.
    """
    results = []
    for l1, l2 in toric_sizes:
        n_seed, hx_seed, hz_seed = _toric_seed(l1, l2)
        for m in sheets:
            out = build_hollowed_tensor_level_map(n_seed, hx_seed, hz_seed, m=m)
            results.append({
                "seed_name": f"toric_{l1}x{l2}",
                "m": m,
                "n_source": out["n_source"],
                "k_source": out["k_source"],
                "n_amplified": out["n_amplified"],
                "k_amplified": out["k_amplified"],
                "commutes": out["commutes"],
                "meta_checks_commute": out["meta_checks_commute"],
                "k_preserved": out["k_preserved"],
                "hx_preserved": out["hx_preserved"],
                "hz_preserved": out["hz_preserved"],
                "n_exceeds_xm": out["n_exceeds_xm"],
                "sparsity_within_lemma_117": out["sparsity_within_lemma_117"],
            })

    all_ok = bool(results) and all(
        r["commutes"]
        and r["meta_checks_commute"]
        and r["k_preserved"]
        and r["hx_preserved"]
        and r["hz_preserved"]
        and r["n_exceeds_xm"]
        and r["sparsity_within_lemma_117"]
        for r in results
    )
    return {
        "trials": len(results),
        "all_consistent": all_ok,
        "empirical": True,
        "construction_scope": "Yuan Appendix A bar Gamma(C) on Hypotheses 102-103 seeds",
        "conditional_theorem": (
            "k' = k (Lemma 118, hypothesis); failure probability upper ceiling "
            "(Theorem 81, hypothesis); n inflated beyond m per level"
        ),
        "transport_direction": TRANSPORT_DIRECTION,
        "distance_lower_bound_available": DISTANCE_LOWER_BOUND_AVAILABLE,
        "results": results,
    }


def one_shot_level_map_transport(
    n: int,
    k: int,
    m: int = 2,
    levels: int = 1,
    *,
    d_error: int | None = None,
    max_x_weight: int | None = None,
) -> dict:
    """Conditional family-level transport record (issue #541).

    Validates all inputs strictly. Records exact ``k`` preservation (Lemma 118,
    hypothesis), ``n_amplified = None`` (one tower level inflates ``n`` far
    beyond ``n * m`` and the local-cone ``bar Gamma`` block length is not
    computed here), the bare sheet lower scale ``n * m**levels``, the
    Theorem 81 failure-probability ``upper ceiling`` transport direction with
    ``distance_lower_bound = None``, and hypothesis status of the imported
    lemmas.
    """
    _validate_int(n, "n", 1)
    if isinstance(k, bool) or not isinstance(k, int) or k < 0 or k > n:
        raise ValueError("k must satisfy 0 <= k <= n")
    floor = sheet_lower_floor(n, m=m, levels=levels)

    record = {
        "n_source": n,
        "k_source": k,
        "m": m,
        "levels": levels,
        "k_amplified": k,
        "k_preserved": True,
        "n_amplified": None,
        "n_sheet_lower_floor": floor,
        "transport_direction": TRANSPORT_DIRECTION,
        "distance_lower_bound": distance_lower_bound(),
        "distance_lower_bound_available": DISTANCE_LOWER_BOUND_AVAILABLE,
        "imported_lemmas": imported_lemma_status(),
        "status": "conditional",
    }
    if d_error is not None or max_x_weight is not None:
        if d_error is None or max_x_weight is None:
            raise ValueError("d_error and max_x_weight must be supplied together")
        record["seed_locally_trivial"] = seed_locally_trivial(d_error, max_x_weight)
    return record


def _mask_to_row(mask: int, n: int) -> list[int]:
    return [q for q in range(n) if (mask >> q) & 1]


def empirical_probe(seed: int = 450, trials: int = 25) -> dict:
    """Empirical probe over finite ``GF(2)`` CSS codes via ``C (x) R``.

    Samples ``trials`` random commuting CSS seeds (with ``Z``-checks drawn from
    ``ker H_X``) and checks ``repetition_tensor_code`` (ordinary ``C (x) R``,
    not Yuan's Def. 111/116 local-cone ``bar Gamma``). Marked ``empirical: True``
    and kept separate from the conditional theorem; never upgrades or
    discharges the imported lemmas.
    """
    if isinstance(seed, bool) or not isinstance(seed, int):
        raise ValueError("seed must be an integer")
    _validate_int(trials, "trials", 1)

    rng = random.Random(seed)
    complex_results = []
    for _ in range(trials):
        n = rng.randint(3, 8)
        m = rng.randint(2, 4)
        num_x = rng.randint(1, max(1, n // 2))
        x_masks = [rng.randint(1, (1 << n) - 1) for _ in range(num_x)]
        orth_space = [
            v for v in range(1, 1 << n)
            if all(_popcount(v & xm) % 2 == 0 for xm in x_masks)
        ]
        if orth_space:
            num_z = rng.randint(0, min(3, len(orth_space)))
            z_masks = [rng.choice(orth_space) for _ in range(num_z)]
        else:
            z_masks = []
        hx_rows = [_mask_to_row(xm, n) for xm in x_masks]
        hz_rows = [_mask_to_row(zm, n) for zm in z_masks]
        out = repetition_tensor_code(n, hx_rows, hz_rows, m=m)
        complex_results.append({
            "n": n,
            "m": m,
            "m_x": len(hx_rows),
            "k_source": out["k_source"],
            "n_amplified": out["n_amplified"],
            "k_amplified": out["k_amplified"],
            "commutes": out["commutes"],
            "k_preserved": out["k_preserved"],
            "n_inflated": out["n_inflated"],
        })

    complex_ok = all(
        r["commutes"] and r["k_preserved"] and r["n_inflated"]
        for r in complex_results
    )
    return {
        "trials": trials,
        "seed": seed,
        "chain_complex_consistent": complex_ok,
        "all_consistent": complex_ok,
        "empirical": True,
        "construction_scope": "ordinary C (x) R over GF(2), not Def. 111/116 bar Gamma",
        "conditional_theorem": (
            "k' = k (Lemma 118, hypothesis); failure probability upper ceiling "
            "(Theorem 81, hypothesis); n inflated beyond m per level"
        ),
        "transport_direction": TRANSPORT_DIRECTION,
        "distance_lower_bound_available": DISTANCE_LOWER_BOUND_AVAILABLE,
        "results": complex_results,
    }


def sweep(seed: int = 450, trials: int = 25) -> dict:
    """Run ``empirical_probe`` and collect any disagreements."""
    out = empirical_probe(seed=seed, trials=trials)
    out["disagreements"] = [
        r for r in out["results"]
        if not (r["commutes"] and r["k_preserved"] and r["n_inflated"])
    ]
    return out


__all__ = [
    "TRANSPORT_DIRECTION",
    "DISTANCE_LOWER_BOUND_AVAILABLE",
    "sheet_lower_floor",
    "distance_lower_bound",
    "seed_locally_trivial",
    "imported_lemma_status",
    "repetition_tensor_code",
    "build_hollowed_tensor_level_map",
    "dual_hollowed_tensor_level_map",
    "empirical_gamma_bar_probe",
    "one_shot_level_map_transport",
    "empirical_probe",
    "sweep",
]


if __name__ == "__main__":
    s = sweep()
    print("chain-complex trials:", s["trials"], "consistent:", s["chain_complex_consistent"])
    print("transport direction:", s["transport_direction"])
    print("distance lower bound available:", s["distance_lower_bound_available"])
