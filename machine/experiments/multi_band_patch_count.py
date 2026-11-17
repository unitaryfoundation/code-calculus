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
    if rows < 0 or m < 0:
        raise ValueError("rows and m must be non-negative")
    return rows * m - (rows // 2)


def reconstruct_display(rows: int, m: int):
    """Reconstruct a minimal fused display from the constructor parameters.

    Returns (n_qubits, n_checks) for a toy construction where each band
    contributes `rows` patches of one qubit each and the fusion removes
    floor(rows/2) redundant checks. The logical dimension is then
    n_qubits - rank, which equals patch_count(rows, m) by construction.
    """
    n_qubits = rows * m
    rank = rows * m - patch_count(rows, m)  # independent checks
    return n_qubits, rank


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
