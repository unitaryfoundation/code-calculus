"""Multi-band dense-packing patch count (issue #448).

Records the patch-count formula k = rows*m - floor(rows/2) as construction
metadata for a logical dimension. This is arithmetic sanity-checking of the
recorded formula and a small linear-algebra reconstruction of a fused
display; it is not a distance certificate and admits nothing.
"""

from __future__ import annotations
import math


def patch_count(rows: int, m: int) -> int:
    """Recorded formula: k = rows*m - floor(rows/2)."""
    if rows < 0:
        raise ValueError("rows must be non-negative")
    if m < 1:
        raise ValueError("m must be a positive integer")
    return rows * m - (rows // 2)


def reconstruct_display(rows: int, m: int):
    """Reconstruct a minimal fused display from the constructor parameters.

    Returns (n_qubits, n_checks) for a toy construction where each band
    contributes `rows` patches of one qubit each and the fusion removes
    floor(rows/2) redundant checks. The logical dimension is then
    n_qubits - rank, which equals patch_count(rows, m) by construction.
    """
    if m < 1:
        raise ValueError("m must be a positive integer")
    n_qubits = rows * m
    rank = rows * m - patch_count(rows, m)  # independent checks
    return n_qubits, rank


def reconstruct_check_structure(rows: int, m: int) -> dict:
    """Toy reconstruction of a check structure from the constructor parameters.

    This is a small display whose independent check count is chosen so that
    the resulting logical dimension agrees with ``patch_count(rows, m)``.
    It is not derived from the dense-packing constructor's geometry (band,
    patch, or notch layout), which is not available in this repository; the
    ranks are computed with ``gf2.rank`` on the displayed supports. The
    count is construction metadata: it determines the logical dimension, and
    says nothing about ``d_X`` or ``d_Z``.
    """
    if rows < 0:
        raise ValueError("rows must be non-negative")
    if m < 1:
        raise ValueError("m must be a positive integer")
    n = rows * m
    num_checks = rows // 2
    x_count = (num_checks + 1) // 2
    z_count = num_checks - x_count
    x_rows = []
    z_rows = []
    cursor = 0
    for i in range(x_count):
        x_rows.append([cursor, cursor + 1])
        cursor += 2
    for i in range(z_count):
        z_rows.append([cursor, cursor + 1])
        cursor += 2
    from machine.state import support_mask
    from machine.gf2 import rank as gf2_rank
    rank_x = gf2_rank([support_mask(r) for r in x_rows]) if x_rows else 0
    rank_z = gf2_rank([support_mask(r) for r in z_rows]) if z_rows else 0
    return {
        "n_qubits": n,
        "x_rows": x_rows,
        "z_rows": z_rows,
        "rank_x": rank_x,
        "rank_z": rank_z,
        "logical_dim": n - rank_x - rank_z,
        "patch_count": patch_count(rows, m),
        "consistent": (n - rank_x - rank_z == patch_count(rows, m)),
    }


def sweep() -> dict:
    results = []
    for rows in range(0, 8):
        for m in range(1, 6):
            k = patch_count(rows, m)
            n, r = reconstruct_display(rows, m)
            ld = n - r
            results.append({
                "rows": rows, "m": m, "k": k,
                "n": n, "rank": r, "logical_dim": ld,
                "consistent": (ld == k),
            })
    return {
        "all_consistent": all(x["consistent"] for x in results),
        "results": results,
    }


if __name__ == "__main__":
    s = sweep()
    print("all consistent:", s["all_consistent"])
    for r in s["results"][:10]:
        print(r)
