"""Extracted module from machine/priced_calculus.py (issue #378)."""

import copy
import re
import itertools
import json
import math
from collections import deque
from dataclasses import dataclass
from decimal import Decimal
from fractions import Fraction
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

from machine.gf2 import *
from machine.state import *
from machine.connectivity import *

def tower_cost_table_size(k_in):
    """Size of the tower factorization cost table for a given ``k_in``.

    The generalization to ``k_in > 1`` (Theorem 27.8) carries cost tables of
    size ``2 ** (2 * k_in)``. This helper records that size for sweep
    bookkeeping; it is a provider-side quantity, not a calculus move. The
    in-repository derivation of the provider (`design/DERIVED_RELATIONS.md`
    section 2a, issue #327) uses two class dictionaries of ``2 ** k_in``
    entries each; this helper keeps recording the source's figure.
    """
    if not isinstance(k_in, int) or isinstance(k_in, bool) or k_in < 1:
        raise Malformed("k_in must be a positive integer")
    return 2 ** (2 * k_in)

TOWER_LEVEL_CEILING = 20

TOWER_OUTER_CEILING = 22

TOWER_EVIDENCE = ("tower factorization from level data, "
                  "design/DERIVED_RELATIONS.md section 2a (2026-11-11, issue #327)")

def _reduced_pivots(rows):
    """Fully reduced row echelon form as a map pivot bit -> row mask."""
    pivots = {}
    for row in rows:
        for column, pivot_row in pivots.items():
            if (row >> column) & 1:
                row ^= pivot_row
        if row == 0:
            continue
        column = (row & -row).bit_length() - 1
        for other in list(pivots):
            if (pivots[other] >> column) & 1:
                pivots[other] ^= row
        pivots[column] = row
    return pivots

def _kernel_basis(rows, labels):
    """A basis of the vectors over ``labels`` orthogonal to every row."""
    pivots = _reduced_pivots(rows)
    basis = []
    for free in labels:
        if free in pivots:
            continue
        vector = 1 << free
        for column, pivot_row in pivots.items():
            if (pivot_row >> free) & 1:
                vector |= 1 << column
        basis.append(vector)
    return basis

def _quotient_basis(vectors, modulo):
    """Representatives of a basis of ``span(vectors)`` modulo ``span(modulo)``."""
    pivots = dict(_reduced_pivots(modulo))
    out = []
    for vector in vectors:
        for column, pivot_row in list(pivots.items()):
            if (vector >> column) & 1:
                vector ^= pivot_row
        if vector == 0:
            continue
        column = (vector & -vector).bit_length() - 1
        for other in list(pivots):
            if (pivots[other] >> column) & 1:
                pivots[other] ^= vector
        pivots[column] = vector
        out.append(vector)
    return out

def _invert_binary_matrix(matrix):
    """Inverse of a square matrix over F_2 given as a list of row masks."""
    size = len(matrix)
    rows = [matrix[i] | (1 << (size + i)) for i in range(size)]
    for column in range(size):
        pivot = next((r for r in range(column, size) if (rows[r] >> column) & 1), None)
        if pivot is None:
            raise Malformed("logical pairing matrix is singular")
        rows[column], rows[pivot] = rows[pivot], rows[column]
        for r in range(size):
            if r != column and (rows[r] >> column) & 1:
                rows[r] ^= rows[column]
    return [row >> size for row in rows]

def _class_index(vector, duals):
    """The logical class of ``vector`` as an integer: bit ``a`` is its
    overlap parity with the ``a``-th dual representative."""
    index = 0
    for position, dual in enumerate(duals):
        if (vector & dual).bit_count() & 1:
            index |= 1 << position
    return index

def tower_level_data(inner_state, ceiling=TOWER_LEVEL_CEILING):
    """The level data of an inner code: its class dictionary per sector.

    For a CSS inner code with ``k_in`` logical qubits this computes dual
    logical bases (X-representatives ``xs`` and Z-representatives ``zs`` with
    ``<xs[a], zs[b]> = [a == b]``) and, per sector, the minimum weight of a
    vector in each of the ``2 ** k_in`` logical classes: ``X[c]`` is the least
    weight of an X-type vector commuting with every inner Z-check whose class
    is ``c`` (class ``0`` is the X-stabilizer coset, weight ``0``), and
    likewise ``Z[c]``. These two tables are the level data the tower price
    provider consumes (`design/DERIVED_RELATIONS.md` section 2a). The
    enumeration runs over the kernel of the opposite sector's checks and
    refuses above ``ceiling`` kernel dimensions. Oracle-side bookkeeping for
    the inner code only; it never enumerates a tower.
    """
    labels = list(inner_state.Q)
    rows = {side: [row.mask for row in inner_state.sector_rows(side)]
            for side in ("X", "Z")}
    kernels = {"X": _kernel_basis(rows["Z"], labels),   # X-type, commutes with Z-checks
               "Z": _kernel_basis(rows["X"], labels)}   # Z-type, commutes with X-checks
    k_in = len(labels) - rank(rows["X"]) - rank(rows["Z"])
    if k_in < 1:
        return {"status": "unavailable",
                "reason": "the inner code has no logical qubit (k_in = 0); a tower "
                          "needs k_in >= 1",
                "k_in": k_in, "n_in": len(labels)}
    xs = _quotient_basis(kernels["X"], rows["X"])
    zs = _quotient_basis(kernels["Z"], rows["Z"])
    if len(xs) != k_in or len(zs) != k_in:
        raise Malformed("logical quotient dimensions disagree with k_in")
    pairing = [sum(((xs[a] & zs[b]).bit_count() & 1) << b for b in range(k_in))
               for a in range(k_in)]
    inverse = _invert_binary_matrix(pairing)
    # zs'[b] = sum_c N[b][c] zs[c] with N = (M^{-1})^T gives <xs[a], zs'[b]> = [a == b].
    duals = []
    for b in range(k_in):
        vector = 0
        for c in range(k_in):
            if (inverse[c] >> b) & 1:
                vector ^= zs[c]
        duals.append(vector)
    for a in range(k_in):
        for b in range(k_in):
            if ((xs[a] & duals[b]).bit_count() & 1) != (1 if a == b else 0):
                raise Malformed("dual logical bases failed to pair")
    too_large = max(len(kernels["X"]), len(kernels["Z"]))
    if too_large > ceiling:
        return {"status": "unavailable",
                "reason": "inner kernel dimension %d exceeds the level-data ceiling %d"
                          % (too_large, ceiling),
                "k_in": k_in, "n_in": len(labels)}
    tables = {}
    examined = 0
    test_basis = {"X": duals, "Z": xs}
    for side in ("X", "Z"):
        table = [None] * (1 << k_in)
        table[0] = 0
        basis = kernels[side]
        vector = 0
        for index in range(1, 1 << len(basis)):
            vector ^= basis[(index & -index).bit_length() - 1]
            weight = vector.bit_count()
            cls = _class_index(vector, test_basis[side])
            if table[cls] is None or weight < table[cls]:
                table[cls] = weight
        examined += (1 << len(basis)) - 1
        if any(entry is None for entry in table):
            raise Malformed("a logical class of the inner code has no representative")
        tables[side] = table
    return {
        "status": "computed",
        "n_in": len(labels),
        "k_in": k_in,
        "X": tables["X"],
        "Z": tables["Z"],
        "distance": {side: min(tables[side][1:]) for side in ("X", "Z")},
        "logical_basis": {"X": xs, "Z": duals},
        "dictionary_entries": 2 * (1 << k_in),
        "cost_table_size": tower_cost_table_size(k_in),
        "vectors_examined": examined,
    }

def _tower_groups(outer_state, groups, k_in):
    """Validate the block structure: ``groups`` partitions the outer qubits
    into blocks of ``k_in`` labels; position ``a`` of a block is the outer
    qubit encoded as inner logical ``a``. Returns label -> (block, position)."""
    if not isinstance(groups, (list, tuple)) or not groups:
        raise Malformed("tower groups must be a non-empty list of label tuples")
    position = {}
    for block, group in enumerate(groups):
        if not isinstance(group, (list, tuple)) or len(group) != k_in:
            raise Malformed("every tower group must list exactly k_in = %d outer qubits"
                            % k_in)
        for index, label in enumerate(group):
            if label in position:
                raise Malformed("outer qubit %r appears in two tower groups" % (label,))
            position[label] = (block, index)
    if set(position) != set(outer_state.Q):
        raise Malformed("tower groups must partition the outer qubits exactly")
    return position

def _tower_class_weight(vector, groups, table):
    """The dictionary weight of an outer-level vector: the sum over blocks of
    the table entry of the block's class."""
    total = 0
    for group in groups:
        cls = 0
        for index, label in enumerate(group):
            if (vector >> label) & 1:
                cls |= 1 << index
        total += table[cls]
    return total

def tower_deletion_prices(inner_state, outer_state, groups, deleted,
                          level_data=None, outer_ceiling=TOWER_OUTER_CEILING):
    """Price provider for deleting lifted outer checks of a concatenation tower.

    The tower is the inner code on every block of the outer code plus each
    outer check lifted through inner logical representatives
    (`design/DERIVED_RELATIONS.md` section 2a). Deleting the lifts of the
    outer checks ``deleted`` (one sector, tau) has exposure price the least
    dictionary weight of an outer-level vector exposed by the same deletion
    in the outer code, and deletion price the least dictionary weight of an
    outer tau-stabilizer that uses a deleted row; the dictionary weight of
    an outer-level vector is the sum over blocks of the inner class
    dictionary entry of the block's class (``level_data``, computed from
    ``inner_state`` when not supplied). The search runs at the outer level
    and never enumerates the tower. For ``k_in = 1`` both prices are the
    inner sector distance times the outer price.

    Returns a verdict dict with ``status`` ``"computed"`` or
    ``"unavailable"``; a computed verdict carries ``w_exp``, ``w_del``, the
    minimizing outer-level vectors, and a ``deletion_price`` object ready
    for the ledger's priced `C-DELETE-CHECK` cell. Price provider only: no
    tower state is built and nothing is proved.
    """
    level = level_data if level_data is not None else tower_level_data(inner_state)
    if level.get("status") != "computed":
        return {"status": "unavailable",
                "reason": "level data unavailable: %s" % level.get("reason"),
                "w_exp": None, "w_del": None}
    k_in = level["k_in"]
    _tower_groups(outer_state, groups, k_in)
    groups = [tuple(group) for group in groups]
    sector, resolved = _resolve_deleted_rows(outer_state, deleted)
    if resolved is None:
        return {"status": "unavailable",
                "reason": "deleted outer check not found in the outer state, or mixed sectors",
                "w_exp": None, "w_del": None}
    deleted_ids = []
    for row in resolved:
        if row.id not in deleted_ids:
            deleted_ids.append(row.id)
    if not deleted_ids:
        return {"status": "unavailable",
                "reason": "no deleted outer check specified",
                "w_exp": None, "w_del": None}
    tau = sector
    sigma = opposite_sector_name(tau)
    tau_rows = list(outer_state.sector_rows(tau))
    remaining = [row.mask for row in tau_rows if row.id not in deleted_ids]
    deleted_masks = [row.mask for row in tau_rows if row.id in deleted_ids]
    labels = list(outer_state.Q)

    # Exposure: outer-level sigma-type vectors even on the remaining tau rows
    # and odd on a deleted one, weighted by the sigma dictionary.
    basis = _kernel_basis(remaining, labels)
    if len(basis) > outer_ceiling or len(tau_rows) > outer_ceiling:
        return {"status": "unavailable",
                "reason": "outer-level search dimension %d exceeds the ceiling %d"
                          % (max(len(basis), len(tau_rows)), outer_ceiling),
                "w_exp": None, "w_del": None}
    best_exp = None
    witness_exp = None
    vector = 0
    for index in range(1, 1 << len(basis)):
        vector ^= basis[(index & -index).bit_length() - 1]
        if not any((vector & mask).bit_count() & 1 for mask in deleted_masks):
            continue
        weight = _tower_class_weight(vector, groups, level[sigma])
        if best_exp is None or weight < best_exp:
            best_exp, witness_exp = weight, vector
    outer_vectors = (1 << len(basis)) - 1

    # Promotion: outer tau-stabilizers that use a deleted row, weighted by the
    # tau dictionary.
    deleted_bits = sum(1 << r for r, row in enumerate(tau_rows) if row.id in deleted_ids)
    best_del = None
    witness_del = None
    combination = 0
    for index in range(1, 1 << len(tau_rows)):
        combination ^= tau_rows[(index & -index).bit_length() - 1].mask
        if not ((index ^ (index >> 1)) & deleted_bits):
            continue
        weight = _tower_class_weight(combination, groups, level[tau])
        if best_del is None or weight < best_del:
            best_del, witness_del = weight, combination
    span_elements = (1 << len(tau_rows)) - 1
    if best_exp is None or best_del is None:
        return {"status": "unavailable",
                "reason": "no exposed or no promoted outer-level vector; the outer "
                          "rows are not independent",
                "w_exp": best_exp, "w_del": best_del}

    def support(mask):
        return [label for label in labels if (mask >> label) & 1]

    return {
        "status": "computed",
        "sector": tau,
        "w_exp": best_exp,
        "w_del": best_del,
        "value": min(best_exp, best_del),
        "deleted_outer_checks": deleted_ids,
        "witness_outer_vectors": {"w_exp": support(witness_exp),
                                  "w_del": support(witness_del)},
        "k_in": k_in,
        "n_in": level["n_in"],
        "n_out": len(groups),
        "tower_n": level["n_in"] * len(groups),
        "dictionary_entries": level["dictionary_entries"],
        "cost_table_size": level["cost_table_size"],
        "outer_vectors_examined": outer_vectors,
        "outer_span_elements_examined": span_elements,
        "reason": ("tower factorization: outer-level search weighted by the "
                   "inner class dictionary; w_exp = %d, w_del = %d"
                   % (best_exp, best_del)),
        "citation_status": ("derived in this repository (design/DERIVED_RELATIONS.md "
                            "section 2a, issue #327); Theorems 27.2 / 27.5 / 27.8 of "
                            "code-deformation are cited, not reproduced"),
        "deletion_price": {"w_del": best_del, "w_exp": best_exp,
                           "evidence": TOWER_EVIDENCE},
    }


__all__ = [
    'tower_cost_table_size',
    'TOWER_LEVEL_CEILING',
    'TOWER_OUTER_CEILING',
    'TOWER_EVIDENCE',
    '_reduced_pivots',
    '_kernel_basis',
    '_quotient_basis',
    '_invert_binary_matrix',
    '_class_index',
    'tower_level_data',
    '_tower_groups',
    '_tower_class_weight',
    'tower_deletion_prices',
]
