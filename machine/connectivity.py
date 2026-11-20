"""Extracted module from machine/priced_calculus.py."""

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

def column_weights(state, sector="Z"):
    """Column weights (number of checks of ``sector`` per qubit)."""
    return _sector_column_weights(state, sector)

def z_column_weights(state):
    """Number of displayed Z-checks each qubit belongs to, keyed by label.

    Keyed by label, not by position: `Q` keeps the parent's labels after
    `E-GRAFT` (graft filters the namespace), so labels can exceed `n() - 1`
    and position indexing would miss them (the #45 trap recorded in
    the conformance harness).
    """
    counts = {q: 0 for q in state.Q}
    for row in state.sector_rows("Z"):
        for qubit in row.support:
            counts[qubit] += 1
    return counts

def is_graphlike(state, sector="Z"):
    """Whether every qubit is in at most two displayed checks of ``sector``."""
    weights = (_sector_column_weights(state, sector)
               if sector in ("X", "Z") else z_column_weights(state))
    return all(count <= 2 for count in weights.values())

def graphlike_status(state, sector="Z"):
    """Detection result for the graphlike condition, with a recorded reason."""
    if sector in ("X", "Z"):
        gstatus = _graphlike_sector_status(state, sector)
        return {"graphlike": gstatus["graphlike"],
                "max_column_weight": gstatus["max_column_weight"],
                "max_z_column_weight": gstatus["max_column_weight"],
                "sector": sector,
                "reason": gstatus["reason"]}
    weights = z_column_weights(state)
    max_weight = max(weights.values(), default=0)
    graphlike = max_weight <= 2
    if graphlike:
        reason = ("graphlike: every qubit is in at most two Z-checks "
                  "(max column weight %d)" % max_weight)
    else:
        reason = ("not graphlike: a qubit is in %d Z-checks, above the "
                  "column-weight-2 bound" % max_weight)
    return {"graphlike": graphlike, "max_z_column_weight": max_weight,
            "reason": reason}

def _sector_column_weights(state, sector):
    """Column weights (number of checks of ``sector`` per qubit)."""
    counts = {q: 0 for q in state.Q}
    for row in state.sector_rows(sector):
        for qubit in row.support:
            counts[qubit] += 1
    return counts

def _resolve_deleted_rows(state, deleted):
    """Resolve a deleted-check specification into (sector, list of Row)."""
    if deleted is None:
        return None, []
    if isinstance(deleted, Row):
        deleted = [deleted]
    if isinstance(deleted, str):
        deleted = [deleted]
    if not isinstance(deleted, (list, tuple, set, frozenset)):
        deleted = [deleted]
    rows_by_id = {row.id: row for row in state.rows}
    resolved = []
    sector = None
    for item in deleted:
        if isinstance(item, Row):
            row = item
        elif isinstance(item, str):
            row = rows_by_id.get(item)
            if row is None:
                return None, None
        else:
            rid = getattr(item, "id", None)
            if rid is None and isinstance(item, dict):
                rid = item.get("row_id") or item.get("id")
            row = rows_by_id.get(rid) if rid is not None else None
            if row is None:
                return None, None
        if sector is None:
            sector = row.sector
        elif sector != row.sector:
            return None, None
        resolved.append(row)
    if not resolved:
        return None, []
    return sector, resolved

def _graphlike_sector_status(state, sector):
    weights = _sector_column_weights(state, sector)
    max_weight = max(weights.values(), default=0)
    graphlike = max_weight <= 2
    if graphlike:
        reason = ("graphlike: every qubit is in at most two %s-checks "
                  "(max column weight %d)" % (sector, max_weight))
    else:
        reason = ("not graphlike: a qubit is in %d %s-checks, above the "
                  "column-weight-2 bound" % (max_weight, sector))
    citation_status = (
        "settled (Theorem 25.1)" if graphlike
        else "settled (NP-hard at column weight 3: column-splitting reduction, "
             "DERIVED_RELATIONS.md section 3a, 2026-11-10, issue #326)")
    return {"graphlike": graphlike, "max_column_weight": max_weight,
            "sector": sector, "reason": reason,
            "citation_status": citation_status}

def _sector_graph(state, sector):
    """Build the (sector)-check incidence graph.

    Vertices are the displayed checks of ``sector``; qubits incident to two
    checks become edges between those vertices, qubits incident to one check
    become edges to a special outer vertex ``None``.
    """
    rows = list(state.sector_rows(sector))
    row_ids = [row.id for row in rows]
    incidence = {q: [] for q in state.Q}
    for row in rows:
        for q in row.support:
            incidence[q].append(row.id)
    adj = {rid: set() for rid in row_ids}
    adj[None] = set()
    for q, ids in incidence.items():
        ids = list(ids)
        if len(ids) == 2:
            a, b = ids[0], ids[1]
            if a != b:
                adj[a].add(b)
                adj[b].add(a)
        elif len(ids) == 1:
            rid = ids[0]
            adj[rid].add(None)
            adj[None].add(rid)
    return {k: list(v) for k, v in adj.items()}

def _shortest_path(adj, src, dst):
    if src == dst:
        return 0
    seen = {src}
    dq = deque([(src, 0)])
    while dq:
        node, dist = dq.popleft()
        for nb in adj.get(node, []):
            if nb in seen:
                continue
            if nb == dst:
                return dist + 1
            seen.add(nb)
            dq.append((nb, dist + 1))
    return None

def graphlike_exposure_price(state, deleted=None, deleted_check=None,
                            deleted_checks=None, deleted_check_id=None,
                            deleted_id=None, check=None, row_id=None):
    """Consumer-side provider for the graphlike exposure price w_exp.

    For graphlike inputs (every qubit in at most two checks of the relevant
    sector) this computes the exposure minimum using the minimum pairwise
    dual distance plus the outer face (Theorem 25.1 + Corollary 25.2 of
    *code-deformation*), over the set of deleted checks supplied. For
    non-graphlike inputs, or when no finite exposed operator exists, it
    refuses with a recorded reason; beyond column weight 2 the price is
    NP-hard (`DERIVED_RELATIONS.md` section 3a), so that refusal is
    by design. It is a price provider only: it does not mutate state and
    does not establish any proof.

    Status vocabulary note: the non-graphlike refusal returns ``status:
    "unavailable"``, the machine-level token for "no computed price", and
    a ``citation_status`` naming the section 3a reduction, the claim-level
    reason; both are reported so neither is hidden.
    """
    spec = deleted
    if spec is None:
        spec = deleted_check
    if spec is None:
        spec = deleted_checks
    if spec is None:
        spec = deleted_check_id
    if spec is None:
        spec = deleted_id
    if spec is None:
        spec = check
    if spec is None:
        spec = row_id
    sector, resolved = _resolve_deleted_rows(state, spec)
    if resolved is None:
        return {
            "status": "unavailable",
            "reason": "deleted check not found in state, or mixed sectors",
            "graphlike": None,
            "w_exp": None,
            "value": None,
        }
    # De-duplicate repeated deleted checks: a repeated terminal would create a
    # zero-length path and a spurious w_exp of 0.
    if resolved:
        seen_ids = set()
        unique = []
        for row in resolved:
            if row.id in seen_ids:
                continue
            seen_ids.add(row.id)
            unique.append(row)
        resolved = unique
    if not resolved:
        return {
            "status": "unavailable",
            "reason": ("no deleted check specified; the exposure price requires "
                       "at least one deleted check to name the exposure set"),
            "graphlike": None,
            "w_exp": None,
            "value": None,
        }
    sector = sector or resolved[0].sector
    gstatus = _graphlike_sector_status(state, sector)
    if not gstatus["graphlike"]:
        return {
            "status": "unavailable",
            "reason": gstatus["reason"],
            "graphlike": False,
            "max_column_weight": gstatus["max_column_weight"],
            "citation_status": gstatus["citation_status"],
            "sector": sector,
            "w_exp": None,
            "value": None,
        }
    adj = _sector_graph(state, sector)
    deleted_ids = [row.id for row in resolved]
    terminals = deleted_ids + [None]
    best = None
    for i in range(len(terminals)):
        for j in range(i + 1, len(terminals)):
            d = _shortest_path(adj, terminals[i], terminals[j])
            if d is None:
                continue
            if best is None or d < best:
                best = d
    if best is None:
        return {
            "status": "unavailable",
            "reason": ("graphlike input, but no finite exposed operator: no path "
                       "between the deleted check(s) and the outer boundary or "
                       "another deleted check"),
            "graphlike": True,
            "max_column_weight": gstatus["max_column_weight"],
            "sector": sector,
            "deleted_checks": deleted_ids,
            "w_exp": None,
            "value": None,
        }
    return {
        "status": "computed",
        "w_exp": best,
        "value": best,
        "reason": ("graphlike: minimum pairwise dual distance plus outer face "
                   "= %d" % best),
        "graphlike": True,
        "max_column_weight": gstatus["max_column_weight"],
        "sector": sector,
        "deleted_checks": deleted_ids,
    }

w_exp_graphlike = graphlike_exposure_price

def tanner_components(state):
    """Number of connected components of the combined X+Z Tanner graph."""
    qubits = list(state.Q)
    checks = list(state.rows)
    if not qubits and not checks:
        return 0
    q_index = {q: i for i, q in enumerate(qubits)}
    node_count = len(qubits) + len(checks)
    parent = list(range(node_count))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    for ci, row in enumerate(checks):
        node = len(qubits) + ci
        for q in row.support:
            if q in q_index:
                union(node, q_index[q])
    roots = {find(i) for i in range(node_count)}
    return len(roots)

def is_tanner_connected(state):
    """Whether the combined X+Z Tanner graph has exactly one component."""
    components = tanner_components(state)
    if not state.Q and not state.rows:
        return True
    return components == 1

def _tanner_component_of(state):
    """Map each qubit to its Tanner-component root (combined X+Z graph)."""
    qubits = list(state.Q)
    q_index = {q: i for i, q in enumerate(qubits)}
    node_count = len(qubits) + len(state.rows)
    parent = list(range(node_count))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    for ci, row in enumerate(state.rows):
        node = len(qubits) + ci
        for q in row.support:
            if q in q_index:
                union(node, q_index[q])
    return {q: find(q_index[q]) for q in state.Q}

def _restricted_k(state, qubits):
    """Logical qubit count of the sub-code on `qubits` (rows contained in it)."""
    qset = set(qubits)
    rows_x = [row.mask for row in state.sector_rows("X")
              if set(row.support) <= qset]
    rows_z = [row.mask for row in state.sector_rows("Z")
              if set(row.support) <= qset]
    return len(qset) - rank(rows_x) - rank(rows_z)

def _rref_masks(masks, width):
    """RREF of integer masks; `width` bounds the bit positions, keyed by label."""
    rows = [m for m in masks]
    r = 0
    for col in range(width):
        sel = None
        for i in range(r, len(rows)):
            if (rows[i] >> col) & 1:
                sel = i
                break
        if sel is None:
            continue
        rows[r], rows[sel] = rows[sel], rows[r]
        for i in range(len(rows)):
            if i != r and ((rows[i] >> col) & 1):
                rows[i] ^= rows[r]
        r += 1
        if r == len(rows):
            break
    return rows[:r]

def stabilizer_group_components(state):
    """Faces of the stabilizer-group block decomposition over `state.Q`.

    The X and Z displayed row spaces are reduced separately and the supports
    of both reduced row sets are unioned. Reducing the combined X+Z mask
    matrix would mix the sectors and over-split (the verifier's gate reports
    one block where the combined reduction reports two).
    """
    parent = {q: q for q in state.Q}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    width = (max(state.Q) + 1) if state.Q else 0
    for sector in ("X", "Z"):
        masks = [row.mask for row in state.sector_rows(sector)]
        for mask in _rref_masks(masks, width):
            qs = [q for q in state.Q if (mask >> q) & 1]
            for q in qs[1:]:
                union(qs[0], q)
    roots = {find(q) for q in state.Q}
    if not state.Q:
        return 0
    return len(roots)

def is_stabilizer_group_connected(state):
    if not state.Q:
        return True
    return stabilizer_group_components(state) == 1


__all__ = [
    'column_weights',
    'z_column_weights',
    'is_graphlike',
    'graphlike_status',
    '_sector_column_weights',
    '_resolve_deleted_rows',
    '_graphlike_sector_status',
    '_sector_graph',
    '_shortest_path',
    'graphlike_exposure_price',
    'w_exp_graphlike',
    'tanner_components',
    'is_tanner_connected',
    '_tanner_component_of',
    '_restricted_k',
    '_rref_masks',
    'stabilizer_group_components',
    'is_stabilizer_group_connected',
]
