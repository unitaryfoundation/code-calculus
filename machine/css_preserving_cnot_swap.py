"""CSS-preserving column CNOT/SWAP transformation."""

from __future__ import annotations

import math
from typing import List, Sequence, Tuple


def _as_matrix(U, n=None):
    if not isinstance(U, (list, tuple)) or not U:
        raise ValueError("U must be a non-empty square matrix")
    rows = [list(r) for r in U]
    if any(not isinstance(r, (list, tuple)) for r in rows):
        raise ValueError("U rows must be lists")
    width = len(rows[0])
    if any(len(r) != width for r in rows):
        raise ValueError("U must be square")
    if n is not None and (len(rows) != n or width != n):
        raise ValueError("U must be %dx%d" % (n, n))
    if any(isinstance(v, bool) or v not in (0, 1) for r in rows for v in r):
        raise ValueError("U entries must be 0 or 1")
    return rows


def _gf2_inv(U):
    n = len(U)
    U = [row[:] + [1 if i == j else 0 for j in range(n)] for i, row in enumerate(U)]
    for col in range(n):
        pivot = None
        for r in range(col, n):
            if U[r][col] & 1:
                pivot = r
                break
        if pivot is None:
            raise ValueError("U is not invertible over F2")
        U[col], U[pivot] = U[pivot], U[col]
        for r in range(n):
            if r != col and (U[r][col] & 1):
                U[r] = [a ^ b for a, b in zip(U[r], U[col])]
    return [row[n:] for row in U]


def _gf2_transpose(U):
    n = len(U)
    return [[U[j][i] for j in range(n)] for i in range(n)]


def validate_u(U, n=None):
    M = _as_matrix(U, n)
    _gf2_inv(M)
    return M


def _max_col_weight(M):
    n = len(M)
    if n == 0:
        return 0
    widths = [sum(1 for i in range(n) if M[i][j]) for j in range(n)]
    return max(widths)


def _max_row_weight(M):
    if not M:
        return 0
    return max(sum(1 for v in row if v) for row in M)


def rho_z(U):
    M = _as_matrix(U)
    return _max_col_weight(M)


def rho_z_inv(U):
    M = _as_matrix(U)
    return _max_col_weight(_gf2_inv(M))


def rho_x(U):
    M = _as_matrix(U)
    return _max_row_weight(_gf2_inv(M))


def rho_x_inv(U):
    M = _as_matrix(U)
    return _max_row_weight(M)


def rho(U):
    return rho_z(U)


def rho_inv(U):
    return rho_z_inv(U)


def transform_matrix_row(row, U, sector="Z"):
    row = list(row)
    n = len(row)
    M = _as_matrix(U, n)
    if sector.upper() == "X":
        Minv = _gf2_inv(M)
        out = [0] * n
        for i in range(n):
            if row[i]:
                for j in range(n):
                    out[j] ^= Minv[i][j]
        return out
    else:
        Mt = _gf2_transpose(M)
        out = [0] * n
        for i in range(n):
            if row[i]:
                for j in range(n):
                    out[j] ^= Mt[i][j]
        return out


def transform_matrices(H_X, H_Z, U):
    n = None
    if H_X:
        n = len(H_X[0])
    elif H_Z:
        n = len(H_Z[0])
    M = validate_u(U, n)
    n = len(M)
    Xp = [transform_matrix_row(r, M, "X") for r in (H_X or [])]
    Zp = [transform_matrix_row(r, M, "Z") for r in (H_Z or [])]
    return Xp, Zp


def gf2_rank(rows, ncols):
    M = [list(r) for r in rows]
    rank = 0
    r = 0
    nrows = len(M)
    for c in range(ncols):
        piv = None
        for rr in range(r, nrows):
            if M[rr][c] & 1:
                piv = rr
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        for rr in range(nrows):
            if rr != r and (M[rr][c] & 1):
                M[rr] = [a ^ b for a, b in zip(M[rr], M[r])]
        r += 1
        rank += 1
        if r == nrows:
            break
    return rank


def n_of(H_X, H_Z):
    if H_X:
        return len(H_X[0])
    if H_Z:
        return len(H_Z[0])
    return 0


def k_of(H_X, H_Z):
    n = n_of(H_X, H_Z)
    rx = gf2_rank(H_X, n) if H_X else 0
    rz = gf2_rank(H_Z, n) if H_Z else 0
    return n - rx - rz


def hamming_weight(row):
    return sum(1 for b in row if b)


def recomputed_w(H_X, H_Z):
    ws = [hamming_weight(r) for r in (H_X or []) + (H_Z or [])]
    return max(ws) if ws else 0


def distance_window(d, rho_val, rho_inv_val):
    if rho_inv_val <= 0:
        raise ValueError("rho_inv must be positive")
    lower = (d + rho_inv_val - 1) // rho_inv_val
    upper = rho_val * d
    return lower, upper


def record(U=None, H_X=None, H_Z=None, d_X=None, d_Z=None, **kw):
    rec = {
        "kind": "css_preserving_column_cnot_swap",
        "hamming_weight_noninvariant": True,
        "generic_cnot_layer_zero_price": False,
        "universal_equality_tail_open": True,
        "status": "conditional",
    }
    if H_X is not None or H_Z is not None:
        rec["n"] = n_of(H_X or [], H_Z or [])
        rec["k"] = k_of(H_X or [], H_Z or [])
    if U is not None:
        M = validate_u(U)
        rec["rho_Z"] = rho_z(M)
        rec["rho_Z_inv"] = rho_z_inv(M)
        rec["rho_X"] = rho_x(M)
        rec["rho_X_inv"] = rho_x_inv(M)
    if d_X is not None:
        rec["d_X"] = d_X
        if U is not None:
            lo, hi = distance_window(d_X, rho_x(U), rho_x_inv(U))
            rec["d_X_window"] = [lo, hi]
    if d_Z is not None:
        rec["d_Z"] = d_Z
        if U is not None:
            lo, hi = distance_window(d_Z, rho_z(U), rho_z_inv(U))
            rec["d_Z_window"] = [lo, hi]
    for key in ("depth", "sector", "d_a", "d_b", "depth_sector"):
        if key in kw:
            rec[key] = kw[key]
    return rec


__all__ = [
    "validate_u",
    "rho_z",
    "rho_z_inv",
    "rho_x",
    "rho_x_inv",
    "rho",
    "rho_inv",
    "transform_matrix_row",
    "transform_matrices",
    "gf2_rank",
    "n_of",
    "k_of",
    "hamming_weight",
    "recomputed_w",
    "distance_window",
    "record",
]
