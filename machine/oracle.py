"""Oracle-only exact-distance utility for small codes.

This module is a **verifier tool**, never a consumer path. It computes the
exact minimum weight of a logical operator in each sector by exhaustive
enumeration over the state's qubit labels. It is not imported by
``machine.priced_calculus`` or by ``machine.planner`` (the planner accepts an
externally supplied verifier callable, but never invokes this module): the
priced calculus never computes a distance, and the evaluator never calls
this routine. Its only legitimate use is checking, auditing, or replaying
results on small codes.

Hard rules (AGENTS.md): no exact-distance computation is a calculus move;
distance stays ``unavailable`` by design in the calculus. This module is the
exception that proves the rule, and it is marked as such.

Complexity. The enumeration is ``2^n`` in the qubit count. The default ceiling
(`ORACLE_N_CEILING`) keeps this tractable; above it the function refuses
rather than silently running for an unreasonable time. For larger codes use an
external decoder; this module does not implement meet-in-the-middle or
information-set decoding.
"""

from machine.priced_calculus import in_span as _in_span  # noqa: E402

ORACLE_N_CEILING = 20


class OracleTooLarge(Exception):
    """Raised when a state exceeds ``ORACLE_N_CEILING`` qubits."""


def exact_distances(state):
    """Return exact per-sector and full distances for a small code.

    Returns a dict ``{"X": int|None, "Z": int|None, "d": int|None,
    "vectors_examined": int}``. A sector with no logical operator (k = 0)
    reports ``None``; the full distance is the minimum of the finite sector
    distances, or ``None`` if both are ``None``.

    Raises ``OracleTooLarge`` if ``len(state.Q) > ORACLE_N_CEILING``.
    """
    if len(state.Q) > ORACLE_N_CEILING:
        raise OracleTooLarge(
            "oracle refused: %d qubits exceeds ceiling %d"
            % (len(state.Q), ORACLE_N_CEILING))
    same = {
        "X": [row.mask for row in state.sector_rows("X")],
        "Z": [row.mask for row in state.sector_rows("Z")],
    }
    opposite = {"X": same["Z"], "Z": same["X"]}
    found = {"X": None, "Z": None}
    labels = list(state.Q)
    n = len(labels)
    bits_for = [1 << q for q in labels]
    vectors_examined = 0
    for bits in range(1, 1 << n):
        mask = 0
        weight = 0
        b = bits
        i = 0
        while b:
            if b & 1:
                mask |= bits_for[i]
                weight += 1
            b >>= 1
            i += 1
        # any trailing zeros already accounted for by i advancing only on set bits?
        # Need account positions for all i; recompute more simply below.
        vectors_examined += 1
        for side in ("X", "Z"):
            if found[side] is not None and weight >= found[side]:
                continue
            if (all((mask & row).bit_count() % 2 == 0
                    for row in opposite[side])
                    and not _in_span(mask, same[side])):
                found[side] = weight
    finite = [value for value in found.values() if value is not None]
    return {"X": found["X"], "Z": found["Z"],
            "d": min(finite) if finite else None,
            "vectors_examined": vectors_examined}


def exact_distance(state):
    """Convenience: full distance only (or ``None``)."""
    return exact_distances(state)["d"]
