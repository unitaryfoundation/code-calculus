"""Regression fixture for the presentation-transform judgments.

A single CNOT layer between two qubits changes the Hamming weight of a
check row: weight is not invariant under Clifford conjugation. This module
pins that fact as a regression example. It is evidence for the conditions
in `the presentation-transforms note`, not a proof, and admits no
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



# ---------------------------------------------------------------------------
# Issue #538: CNOT-disguised direct sums and depth-one equality judgments.
# Judgment records that preserve the depth and sector hypotheses. These are
# consumer-side records: they track hypotheses and never model a generic CNOT
# layer as zero-price. They admit no calculus rule.
# ---------------------------------------------------------------------------


def _validate_depth(value):
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValueError("depth must be a positive integer")
    if value < 1:
        raise ValueError("depth must be >= 1")
    return value


def _validate_sector(value):
    if isinstance(value, str):
        s = value.strip().upper()
        if s not in ("X", "Z"):
            raise ValueError("sector must be 'X' or 'Z'")
        return s
    if isinstance(value, (list, tuple)):
        if len(value) == 0:
            raise ValueError("sector list must be non-empty")
        out = [_validate_sector(v) for v in value]
        return out if isinstance(value, list) else tuple(out)
    raise ValueError("sector must be 'X', 'Z', or a non-empty list of these")


def _validate_distance(value):
    if value is None:
        return None
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValueError("distance must be a non-negative integer")
    if value < 0:
        raise ValueError("distance must be >= 0")
    return value


def _record(depth, sector, d_a, d_b, kind):
    depth = _validate_depth(depth)
    sector = _validate_sector(sector)
    d_a = _validate_distance(d_a)
    d_b = _validate_distance(d_b)

    record = {
        "depth": depth,
        "sector": sector,
        "hamming_weight_noninvariant": True,
        "universal_equality_tail_open": True,
        "generic_cnot_layer_zero_price": False,
        "kind": kind,
        "status": "conditional",
    }
    if d_a is not None:
        record["d_a"] = d_a
    if d_b is not None:
        record["d_b"] = d_b
    if d_a is not None and d_b is not None:
        record["min_distance"] = min(d_a, d_b)
    # Single-layer lower bound is licensed only for a depth-one transform.
    if depth == 1 and d_a is not None and d_b is not None:
        record["lower_bound"] = min(d_a, d_b)
    record["two_layer_sharpness"] = 1
    if kind == "depth_one_equality":
        record["depth_one_equality"] = (
            depth == 1 and d_a is not None and d_b is not None and d_a == d_b
        )
    return record


def cnot_disguised_direct_sum(depth, sector, d_a=None, d_b=None, **_ignored):
    """Judgment record for a CNOT-disguised direct sum.

    Preserves the depth and sector hypotheses; records Hamming-weight
    non-invariance; keeps the universal equality tail open; never models a
    generic CNOT layer as zero-price. The single-layer lower bound is
    recorded only when ``depth == 1``.
    """
    return _record(depth, sector, d_a, d_b, "cnot_disguised_direct_sum")


def depth_one_equality(depth, sector, d_a=None, d_b=None, **_ignored):
    """Judgment record for depth-one equality (balanced sectors).

    Preserves the supplied depth; the equality flag is set only when the
    transform is depth-one and the two distances agree (balanced sectors).
    """
    return _record(depth, sector, d_a, d_b, "depth_one_equality")


def presentation_transform(depth, sector, d_a=None, d_b=None, **_ignored):
    """Generic presentation-transform judgment record."""
    return _record(depth, sector, d_a, d_b, "presentation_transform")


def depth_sector_hypotheses(depth, sector, d_a=None, d_b=None, **_ignored):
    """Record the depth and sector hypotheses alone."""
    depth = _validate_depth(depth)
    sector = _validate_sector(sector)
    return {
        "depth": depth,
        "sector": sector,
    }


__all__ = [
    "cnot_transform_row",
    "hamming_weight",
    "direct_sum_lower_bound",
    "two_layer_sharpness",
    "cnot_disguised_direct_sum",
    "depth_one_equality",
    "presentation_transform",
    "depth_sector_hypotheses",
]
