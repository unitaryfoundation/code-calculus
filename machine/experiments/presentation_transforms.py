"""Regression fixture for the presentation-transform judgments of issue #447.

A single CNOT layer between two qubits changes the Hamming weight of a
check row: weight is not invariant under Clifford conjugation. This module
pins that fact as a regression example. It is evidence for the conditions
in `design/PRESENTATION_TRANSFORMS.md`, not a proof, and admits no
judgment.
"""

from __future__ import annotations


def cnot_transform_row(row: list[int], control: int, target: int) -> list[int]:
    """Apply a CNOT(control->target) to a binary (Z-type) check row.

    A Z-check row is a subset of qubits; conjugation by CNOT(control,target)
    maps a Z on the target to Z_target * Z_control, so the row gains the
    control qubit when the target was present.
    """
    out = list(row)
    if out[target] == 1 and out[control] == 0:
        out[control] = 1
    # If both present, they cancel on control.
    if row[target] == 1 and row[control] == 1:
        out[control] = 0
    return out


def hamming_weight(row: list[int]) -> int:
    return sum(1 for b in row if b == 1)


def direct_sum_lower_bound(d_a: int, d_b: int) -> int:
    """Single-layer lower bound for a disguised direct sum."""
    return min(d_a, d_b)


def two_layer_sharpness() -> int:
    """Two-layer construction reaches distance 1."""
    return 1