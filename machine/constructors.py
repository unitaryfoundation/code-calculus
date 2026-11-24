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
from machine.connectivity import *
from machine.layout import *
from machine.tower_prices import *
from machine.intervals import *

ADMITTED_CONSTRUCTORS = ("L-HGP", "L-LIFTED", "L-GROUP-ALGEBRA", "A-CONCAT",
                         "L-BALANCED", "L-TANNER", "L-TILE", "A-PRODUCT",
                         "A-DOUBLE", "L-NESTED-CSS", "L-MAPPING-CONE",
                         "L-EMPTY", "L-FREE", "A-PULLBACK", "A-PUSHOUT",
                         "L-PAIR-PARTITION", "PP-SCALE")

UNADMITTED_CONSTRUCTORS = {}

def _binary_matrix(matrix, name):
    """Validate a binary matrix given as a list of equal-length 0/1 rows."""
    if not isinstance(matrix, (list, tuple)) or not matrix:
        raise Malformed("%s must be a non-empty list of rows" % name)
    width = None
    out = []
    for row in matrix:
        if not isinstance(row, (list, tuple)) or not row:
            raise Malformed("%s rows must be non-empty lists" % name)
        if width is None:
            width = len(row)
        if len(row) != width:
            raise Malformed("%s rows must have equal length" % name)
        if any(isinstance(v, bool) or v not in (0, 1) for v in row):
            raise Malformed("%s entries must be 0 or 1" % name)
        out.append(tuple(int(v) for v in row))
    return out

def _group(orders):
    """A finite abelian group as a product of cyclic groups of the given orders.

    Returns (orders, elements, index): the elements are exponent tuples in
    a fixed order and ``index`` maps each to its position. The empty tuple
    of orders is the trivial group with one element ``()``.
    """
    if not isinstance(orders, (list, tuple)):
        raise Malformed("group orders must be a list of positive integers")
    orders = tuple(orders)
    if any(isinstance(o, bool) or not isinstance(o, int) or o < 1 for o in orders):
        raise Malformed("group orders must be positive integers")
    import itertools
    elements = [tuple(e) for e in itertools.product(*[range(o) for o in orders])]
    return orders, elements, {g: i for i, g in enumerate(elements)}


def _validate_cayley_table(table, name="group multiplication table"):
    """Validate an ell x ell Cayley table on 0..ell-1 (closure, unique identity,
    two-sided inverses, associativity). Returns (table_tuples, e_idx, inv_map).
    """
    if not isinstance(table, (list, tuple)) or not table:
        raise Malformed("%s must be a non-empty square matrix" % name)
    ell = len(table)
    out = []
    for row in table:
        if not isinstance(row, (list, tuple)) or len(row) != ell:
            raise Malformed("%s must be an %d x %d square table" % (name, ell, ell))
        if any(isinstance(v, bool) or not isinstance(v, int) or not (0 <= v < ell)
               for v in row):
            raise Malformed("%s entries must be integers in 0..%d" % (name, ell - 1))
        out.append(tuple(int(v) for v in row))
    identities = [
        e for e in range(ell)
        if all(out[e][g] == g and out[g][e] == g for g in range(ell))
    ]
    if len(identities) != 1:
        raise Malformed("%s does not have a unique identity element" % name)
    e_idx = identities[0]
    inv_map = {}
    for g in range(ell):
        invs = [h for h in range(ell) if out[g][h] == e_idx and out[h][g] == e_idx]
        if len(invs) != 1:
            raise Malformed("%s: element %d does not have a unique two-sided inverse"
                            % (name, g))
        inv_map[g] = invs[0]
    for a in range(ell):
        row_a = out[a]
        for b in range(ell):
            ab = row_a[b]
            row_ab = out[ab]
            row_b = out[b]
            for c in range(ell):
                if row_ab[c] != row_a[row_b[c]]:
                    raise Malformed("%s is not associative at (%d, %d, %d)"
                                    % (name, a, b, c))
    return tuple(out), e_idx, inv_map


def _group_spec(group):
    """Normalize a finite group presentation (spec/OPERATIONAL_SEMANTICS.md
    section 4.44):
    - Abelian cyclic orders: a list or tuple of positive integers ``(o_1, ..., o_r)``
      (with ``()`` for the trivial group).
    - Explicit multiplication table: ``{"table": [[...], ...]}`` (or a 2D list
      of rows when the first element is a list/tuple).
    - Permutation generators: ``{"generators": [perm_1, ...]}`` (with optional
      ``"degree": d``), generating a subgroup of S_d in lexicographic order.
    """
    if isinstance(group, dict) and {"kind", "elements", "index", "mul", "inv"} <= set(group):
        return group
    if isinstance(group, dict):
        if "table" in group and "generators" not in group:
            table, e_idx, inv_map = _validate_cayley_table(group["table"])
            ell = len(table)
            elements = list(range(ell))
            return {
                "kind": "table",
                "orders": None,
                "elements": elements,
                "index": {g: g for g in elements},
                "identity": e_idx,
                "table": table,
                "inv_map": inv_map,
                "mul": lambda g, h, _t=table: _t[g][h],
                "inv": lambda g, _i=inv_map: _i[g],
            }
        if "generators" in group and "table" not in group:
            gens_raw = group["generators"]
            if not isinstance(gens_raw, (list, tuple)):
                raise Malformed("group generators must be a list of permutations")
            degree = group.get("degree")
            if degree is not None:
                if isinstance(degree, bool) or not isinstance(degree, int) or degree < 1:
                    raise Malformed("group degree must be a positive integer")
            elif gens_raw:
                if not isinstance(gens_raw[0], (list, tuple)) or not gens_raw[0]:
                    raise Malformed("group generators must be non-empty permutations")
                degree = len(gens_raw[0])
            else:
                degree = 1
            gens = [tuple(_permutation(g, degree, "group generator")) for g in gens_raw]
            id_perm = tuple(range(degree))
            seen = {id_perm}
            queue = deque([id_perm])
            while queue:
                cur = queue.popleft()
                for gen in gens:
                    prod = tuple(cur[gen[x]] for x in range(degree))
                    if prod not in seen:
                        seen.add(prod)
                        queue.append(prod)
            perms = sorted(seen)
            perm_to_idx = {p: i for i, p in enumerate(perms)}
            ell = len(perms)
            table = tuple(
                tuple(perm_to_idx[tuple(p[q[x]] for x in range(degree))] for q in perms)
                for p in perms
            )
            e_idx = perm_to_idx[id_perm]
            inv_map = {
                i: perm_to_idx[tuple(p.index(x) for x in range(degree))]
                for i, p in enumerate(perms)
            }
            # Record words in the generators for each element (by BFS) for action extension.
            gen_indices = [perm_to_idx[g] for g in gens]
            words = {e_idx: ()}
            word_q = deque([e_idx])
            while word_q:
                cur_i = word_q.popleft()
                for g_pos, g_idx in enumerate(gen_indices):
                    nxt_i = table[cur_i][g_idx]
                    if nxt_i not in words:
                        words[nxt_i] = words[cur_i] + (g_pos,)
                        word_q.append(nxt_i)
            elements = list(range(ell))
            return {
                "kind": "generators",
                "orders": None,
                "degree": degree,
                "perms": perms,
                "perm_to_index": perm_to_idx,
                "generator_indices": gen_indices,
                "words": words,
                "elements": elements,
                "index": {g: g for g in elements},
                "identity": e_idx,
                "table": table,
                "inv_map": inv_map,
                "mul": lambda g, h, _t=table: _t[g][h],
                "inv": lambda g, _i=inv_map: _i[g],
            }
        raise Malformed("group dict must specify either 'table' or 'generators'")
    if (isinstance(group, (list, tuple)) and group
            and isinstance(group[0], (list, tuple))):
        return _group_spec({"table": group})
    orders, elements, index = _group(group)
    return {
        "kind": "abelian",
        "orders": orders,
        "elements": elements,
        "index": index,
        "identity": tuple(0 for _ in orders),
        "mul": lambda g, h, _o=orders: tuple((gi + hi) % o for gi, hi, o in zip(g, h, _o)),
        "inv": lambda g, _o=orders: tuple((-gi) % o for gi, o in zip(g, _o)),
    }


def _algebra_element(value, group_or_orders, name):
    """An element of F_2[G] as a frozenset of group elements (terms cancel mod 2)."""
    info = _group_spec(group_or_orders)
    if not isinstance(value, (list, tuple, set, frozenset)):
        raise Malformed("%s must be a list of group elements" % name)
    terms = set()
    if info["kind"] == "abelian":
        orders = info["orders"]
        for term in value:
            if isinstance(term, int) and not isinstance(term, bool) and len(orders) == 1:
                term = (term,)
            if not isinstance(term, (list, tuple)) or len(orders) != len(term):
                raise Malformed("%s terms must be exponent tuples of length %d"
                                % (name, len(orders)))
            if any(isinstance(t, bool) or not isinstance(t, int) for t in term):
                raise Malformed("%s exponents must be integers" % name)
            key = tuple(t % o for t, o in zip(term, orders))
            if key in terms:
                terms.remove(key)
            else:
                terms.add(key)
        return frozenset(terms)
    ell = len(info["elements"])
    perm_to_index = info.get("perm_to_index")
    for term in value:
        if isinstance(term, int) and not isinstance(term, bool):
            if not (0 <= term < ell):
                raise Malformed("%s element index %d out of range 0..%d"
                                % (name, term, ell - 1))
            key = term
        elif isinstance(term, (list, tuple)):
            if len(term) == 1 and isinstance(term[0], int) and not isinstance(term[0], bool):
                idx = term[0]
                if not (0 <= idx < ell):
                    raise Malformed("%s element index %d out of range 0..%d"
                                    % (name, idx, ell - 1))
                key = idx
            elif perm_to_index is not None and tuple(term) in perm_to_index:
                key = perm_to_index[tuple(term)]
            else:
                raise Malformed("%s term %r is not a valid element of G" % (name, term))
        else:
            raise Malformed("%s term %r is not a valid element of G" % (name, term))
        if key in terms:
            terms.remove(key)
        else:
            terms.add(key)
    return frozenset(terms)


def _algebra_matrix(matrix, group_or_orders, name):
    info = _group_spec(group_or_orders)
    if not isinstance(matrix, (list, tuple)) or not matrix:
        raise Malformed("%s must be a non-empty list of rows" % name)
    width = None
    out = []
    for r, row in enumerate(matrix):
        if not isinstance(row, (list, tuple)) or not row:
            raise Malformed("%s rows must be non-empty lists" % name)
        if width is None:
            width = len(row)
        if len(row) != width:
            raise Malformed("%s rows must have equal length" % name)
        out.append([_algebra_element(v, info, "%s[%d][%d]" % (name, r, c))
                    for c, v in enumerate(row)])
    return out


def _involution(element, group_or_orders):
    """The group-algebra antipode involution g -> g^{-1} (additively g -> -g),
    applied termwise."""
    info = _group_spec(group_or_orders)
    inv = info["inv"]
    return frozenset(inv(term) for term in element)


def _lift_rows(element, orders, elements, index):
    """The regular representation of an algebra element over an abelian group:
    row h of L(x) has a one at h' exactly when h - h' is a term of x. Returned
    as bit masks over the group index."""
    rows = []
    for h in elements:
        mask = 0
        for g in element:
            shifted = tuple((hi - gi) % o for hi, gi, o in zip(h, g, orders))
            mask |= 1 << index[shifted]
        rows.append(mask)
    return rows


def _left_lift_rows(element, group_info):
    """The left regular representation L(x) over a finite group G:
    L(x)[h, k] = 1 iff h k^{-1} in x, i.e., k = g^{-1} h for g in x."""
    elements = group_info["elements"]
    index = group_info["index"]
    mul = group_info["mul"]
    inv = group_info["inv"]
    inv_terms = [inv(g) for g in element]
    rows = []
    for h in elements:
        mask = 0
        for g_inv in inv_terms:
            k = mul(g_inv, h)
            mask ^= 1 << index[k]
        rows.append(mask)
    return rows


def _right_lift_rows(element, group_info):
    """The right regular representation R(y) over a finite group G:
    R(y)[h, k] = 1 iff k^{-1} h in y, i.e., k = h g^{-1} for g in y.
    When G is abelian, R(y) = L(y) entry for entry."""
    elements = group_info["elements"]
    index = group_info["index"]
    mul = group_info["mul"]
    inv = group_info["inv"]
    inv_terms = [inv(g) for g in element]
    rows = []
    for h in elements:
        mask = 0
        for g_inv in inv_terms:
            k = mul(h, g_inv)
            mask ^= 1 << index[k]
        rows.append(mask)
    return rows

def _retained_display(rows):
    """The retained independent display: within each sector, rows kept in
    order when they lie outside the span of the rows of that sector kept
    before them (spec/OPERATIONAL_SEMANTICS.md section 4.34). Returns the
    kept (sector, mask) pairs and the drop count."""
    bases = {"X": {}, "Z": {}}
    kept = []
    dropped = 0
    for sector, mask in rows:
        basis = bases[sector]
        value = mask
        while value:
            pivot = value.bit_length() - 1
            if pivot in basis:
                value ^= basis[pivot]
            else:
                basis[pivot] = value
                break
        if value:
            kept.append((sector, mask))
        else:
            dropped += 1
    return kept, dropped

def _constructed_state(n, rows, initial_used=()):
    """A presented state on labels 0..n-1 from (sector, mask) rows: the
    retained display with canonically minted identifiers, validated."""
    kept, dropped = _retained_display(rows)
    used = set(initial_used)
    display = []
    for sector, mask in kept:
        identifier = CodeState._mint_identifier(used)
        used.add(identifier)
        support = tuple(q for q in range(n) if (mask >> q) & 1)
        display.append(Row(identifier, sector, support))
    state = CodeState(tuple(range(n)), tuple(display), frozenset(used))
    _validate_output(state)
    return state, dropped

def lifted_product(group, A, B):
    """`L-LIFTED`: the lifted product of base matrices over F_2[G], G a finite
    group (abelian by cyclic orders, or nonabelian by multiplication table or
    permutation generators; spec/OPERATIONAL_SEMANTICS.md sections 4.34, 4.44).

    With ``A`` of shape m_A x n_A and ``B`` of shape m_B x n_B over F_2[G],
    the qubits are the left block (i, j, g) and the right block (a, b, g);
    the X-checks, indexed by (a, j, h), carry ``L(A[a][i])`` on the left qubits
    (i, j, .) and ``R(B[b][j]^*)`` on the right qubits (a, b, .); the Z-checks,
    indexed by (i, b, h), carry ``R(B[b][j])`` on the left and ``L(A[a][i]^*)``
    on the right, where ``*`` is the antipode involution g -> g^{-1}.
    Orthogonality holds because left and right regular representations commute
    (L(x) R(y) = R(y) L(x) over F_2; section 4.44). When G is abelian, R = L.
    The trivial group gives the hypergraph product. Returns (state, dropped_rows).
    """
    info = _group_spec(group)
    A = _algebra_matrix(A, info, "A")
    B = _algebra_matrix(B, info, "B")
    ell = len(info["elements"])
    m_a, n_a = len(A), len(A[0])
    m_b, n_b = len(B), len(B[0])
    left = n_a * n_b * ell
    n = left + m_a * m_b * ell

    def left_offset(i, j):
        return (i * n_b + j) * ell

    def right_offset(a, b):
        return left + (a * m_b + b) * ell

    left_lifts = {}
    right_lifts = {}

    def left_lift(element):
        if element not in left_lifts:
            left_lifts[element] = _left_lift_rows(element, info)
        return left_lifts[element]

    def right_lift(element):
        if element not in right_lifts:
            right_lifts[element] = _right_lift_rows(element, info)
        return right_lifts[element]

    rows = []
    for a in range(m_a):
        for j in range(n_b):
            for h in range(ell):
                mask = 0
                for i in range(n_a):
                    mask |= left_lift(A[a][i])[h] << left_offset(i, j)
                for b in range(m_b):
                    mask |= right_lift(_involution(B[b][j], info))[h] << right_offset(a, b)
                rows.append(("X", mask))
    for i in range(n_a):
        for b in range(m_b):
            for h in range(ell):
                mask = 0
                for j in range(n_b):
                    mask |= right_lift(B[b][j])[h] << left_offset(i, j)
                for a in range(m_a):
                    mask |= left_lift(_involution(A[a][i], info))[h] << right_offset(a, b)
                rows.append(("Z", mask))
    return _constructed_state(n, rows)

def hypergraph_product(H1, H2):
    """`L-HGP`: the hypergraph product of two binary parity-check matrices.

    Qubits are the pairs (i, j) of column indices, then the pairs (a, b) of
    row indices; X-check (a, j) is row a of ``H1`` on the left qubits (., j)
    with column j of ``H2`` on the right qubits (a, .); Z-check (i, b) is row
    b of ``H2`` on the left qubits (i, .) with column i of ``H1`` on the
    right qubits (., b). The output has n = n1 n2 + m1 m2 qubits and
    k = k1 k2 + k1^T k2^T logical qubits (section 4.34); it is the lifted
    product over the trivial group. Returns (state, dropped_rows).
    """
    H1 = _binary_matrix(H1, "H1")
    H2 = _binary_matrix(H2, "H2")
    unit = [()]
    A = [[unit if v else [] for v in row] for row in H1]
    B = [[unit if v else [] for v in row] for row in H2]
    return lifted_product((), A, B)

def hypergraph_parameters(H1, H2):
    """The exact n and k of the hypergraph product from the factor ranks."""
    H1 = _binary_matrix(H1, "H1")
    H2 = _binary_matrix(H2, "H2")
    m1, n1 = len(H1), len(H1[0])
    m2, n2 = len(H2), len(H2[0])
    r1 = rank([sum(1 << c for c, v in enumerate(row) if v) for row in H1])
    r2 = rank([sum(1 << c for c, v in enumerate(row) if v) for row in H2])
    return {"n": n1 * n2 + m1 * m2,
            "k": (n1 - r1) * (n2 - r2) + (m1 - r1) * (m2 - r2),
            "rank_X": m1 * n2 - (m1 - r1) * (n2 - r2),
            "rank_Z": n1 * m2 - (n1 - r1) * (m2 - r2)}

def two_block_code(group, a, b):
    """`L-GROUP-ALGEBRA`: the two-block code of a, b in F_2[G], G a finite
    group (abelian by cyclic orders, or nonabelian by multiplication table or
    permutation generators; spec/OPERATIONAL_SEMANTICS.md sections 4.34, 4.44).

    H_X = [L(a) | R(b)] and H_Z = [R(b)^T | L(a)^T] = [R(b^*) | L(a^*)] over
    2|G| qubits, with L the left regular representation and R the right regular
    representation (when G is abelian, R = L); the rows commute because
    L(a) R(b) = R(b) L(a) over F_2. The logical dimension is
    k = 2|G| - rank[L(a) | R(b)] - rank[L(b) | R(a)] in general, reducing to
    k = 2(|G| - rank[L(a) | L(b)]) when G is abelian (sections 4.34 and 4.44).
    Equal, row for row, to the lifted product of the 1 x 1 base matrices (a)
    and (b^*). Returns (state, dropped_rows).
    """
    info = _group_spec(group)
    a = _algebra_element(a, info, "a")
    b = _algebra_element(b, info, "b")
    ell = len(info["elements"])
    la = _left_lift_rows(a, info)
    rb = _right_lift_rows(b, info)
    lat = _left_lift_rows(_involution(a, info), info)   # L(a)^T = L(a^*)
    rbt = _right_lift_rows(_involution(b, info), info)  # R(b)^T = R(b^*)
    rows = [("X", la[h] | (rb[h] << ell)) for h in range(ell)]
    rows += [("Z", rbt[h] | (lat[h] << ell)) for h in range(ell)]
    return _constructed_state(2 * ell, rows)

def concatenate(outer, inner, groups, representatives=None):
    """`A-CONCAT`: the inner CSS code on every block of the outer CSS code.

    ``groups`` partitions the outer qubits into blocks of k_in labels, the
    position of a label in its block naming the inner logical it encodes.
    Block j carries a copy of the inner code on labels j n_in + (index of the
    inner label); each outer row is lifted block by block through the
    representatives (by default the dual logical bases of the inner level
    data, `tower_level_data`). Well-formedness, n = n_in n_out, and k = k_out
    are derived in `DERIVED_RELATIONS.md` section 2a and
    `spec/OPERATIONAL_SEMANTICS.md` section 4.34. Returns (state, dropped_rows)
    with ``dropped_rows`` always 0 (the natural display is independent).
    """
    if not isinstance(outer, CodeState) or not isinstance(inner, CodeState):
        raise Malformed("A-CONCAT takes two CodeState inputs")
    level = tower_level_data(inner)
    if level.get("status") != "computed":
        raise Malformed("A-CONCAT inner code: %s" % level.get("reason"))
    k_in = level["k_in"]
    _tower_groups(outer, groups, k_in)
    groups = [tuple(group) for group in groups]
    reps = representatives if representatives is not None else level["logical_basis"]
    for side in ("X", "Z"):
        if side not in reps or len(reps[side]) != k_in:
            raise Malformed("A-CONCAT representatives must give k_in masks per sector")
    inner_labels = list(inner.Q)
    n_in = len(inner_labels)
    index_of = {label: i for i, label in enumerate(inner_labels)}

    def shift(mask, block):
        out = 0
        for label in inner_labels:
            if (mask >> label) & 1:
                out |= 1 << (block * n_in + index_of[label])
        return out

    rows = []
    for block in range(len(groups)):
        for row in inner.rows:
            rows.append((row.sector, shift(row.mask, block)))
    for row in outer.rows:
        mask = 0
        for block, group in enumerate(groups):
            rep = 0
            for position, label in enumerate(group):
                if (row.mask >> label) & 1:
                    rep ^= reps[row.sector][position]
            mask |= shift(rep, block)
        rows.append((row.sector, mask))
    return _constructed_state(n_in * len(groups), rows)

def _natural_rows_orthogonal(rows):
    """Whether the natural rows of the two sectors have pairwise even overlap."""
    x_rows = [mask for sector, mask in rows if sector == "X"]
    z_rows = [mask for sector, mask in rows if sector == "Z"]
    return all(bin(x & z).count("1") % 2 == 0 for x in x_rows for z in z_rows)

def _label_list(value, name):
    if (not isinstance(value, (list, tuple))
            or any(isinstance(q, bool) or not isinstance(q, int) or q < 0
                   for q in value)):
        raise Malformed("%s must be a list of nonnegative integers" % name)
    return tuple(value)

def css_tensor_product(a, b):
    """`A-PRODUCT`: the CSS tensor product of two well-formed CSS states.

    Each factor is read as the chain complex Z-rows -> qubits -> X-rows, and
    the output is the middle of the total complex of the tensor product. The
    qubits are the pairs (Z-row of A, X-row of B), then (qubit of A, qubit of
    B), then (X-row of A, Z-row of B); the natural X-rows are indexed by
    (qubit of A, X-row of B) and then (X-row of A, qubit of B), the natural
    Z-rows by (Z-row of A, qubit of B) and then (qubit of A, Z-row of B).
    The natural rows commute because the total differential squares to
    zero, and k = k_A k_B (`spec/OPERATIONAL_SEMANTICS.md` section 4.35).
    Returns (state, dropped_rows).
    """
    if not isinstance(a, CodeState) or not isinstance(b, CodeState):
        raise Malformed("A-PRODUCT takes two CodeState inputs")
    a.validate()
    b.validate()
    ax, az = a.sector_rows("X"), a.sector_rows("Z")
    bx, bz = b.sector_rows("X"), b.sector_rows("Z")
    na, nb = len(a.Q), len(b.Q)
    index_a = {q: i for i, q in enumerate(a.Q)}
    index_b = {q: i for i, q in enumerate(b.Q)}

    def members(row, index):
        return [index[q] for q in row.support]

    first = len(az) * len(bx)
    second = first + na * nb
    n = second + len(ax) * len(bz)

    def zx(z, x):
        return z * len(bx) + x

    def qq(i, j):
        return first + i * nb + j

    def xz(x, z):
        return second + x * len(bz) + z

    rows = []
    for i in range(na):
        for x, row in enumerate(bx):
            mask = 0
            for z, zrow in enumerate(az):
                if a.Q[i] in zrow.support:
                    mask |= 1 << zx(z, x)
            for j in members(row, index_b):
                mask |= 1 << qq(i, j)
            rows.append(("X", mask))
    for x, row in enumerate(ax):
        for j in range(nb):
            mask = 0
            for i in members(row, index_a):
                mask |= 1 << qq(i, j)
            for z, zrow in enumerate(bz):
                if b.Q[j] in zrow.support:
                    mask |= 1 << xz(x, z)
            rows.append(("X", mask))
    for z, row in enumerate(az):
        for j in range(nb):
            mask = 0
            for i in members(row, index_a):
                mask |= 1 << qq(i, j)
            for x, xrow in enumerate(bx):
                if b.Q[j] in xrow.support:
                    mask |= 1 << zx(z, x)
            rows.append(("Z", mask))
    for i in range(na):
        for z, row in enumerate(bz):
            mask = 0
            for x, xrow in enumerate(ax):
                if a.Q[i] in xrow.support:
                    mask |= 1 << xz(x, z)
            for j in members(row, index_b):
                mask |= 1 << qq(i, j)
            rows.append(("Z", mask))
    return _constructed_state(n, rows)

def double_cover(state, wiring, conjugate=False):
    """`A-DOUBLE`: the two-sheet cover of a CSS state under a wiring map.

    ``wiring`` maps a row identifier to the qubits of that row's support
    whose incidence is twisted (an omitted row has no twisted incidence).
    The qubits are the pairs (q, s), sheet s in {0, 1}, at label s n + (index
    of q); row r lifts to the two rows (r, t), with (r, t) supported on
    (q, t) for an untwisted incidence and on (q, 1 - t) for a twisted one.
    With ``conjugate`` the rows of sheet 1 take the opposite sector (the
    sector-duality choice). Applicability: the natural rows of the two
    sectors have pairwise even overlap; a wiring that breaks it gives no
    derivation. Returns (state, dropped_rows).
    """
    if not isinstance(state, CodeState):
        raise Malformed("A-DOUBLE takes a CodeState input")
    state.validate()
    if not isinstance(wiring, dict):
        raise Malformed("A-DOUBLE wiring maps row identifiers to twisted qubits")
    if not isinstance(conjugate, bool):
        raise Malformed("A-DOUBLE conjugate must be a boolean")
    by_id = {row.id: row for row in state.rows}
    twisted = {}
    for identifier, qubits in wiring.items():
        if identifier not in by_id:
            raise Malformed("A-DOUBLE wiring names a row that is not displayed: %r"
                            % (identifier,))
        qubits = _label_list(qubits, "A-DOUBLE twisted qubits")
        if len(set(qubits)) != len(qubits) or not set(qubits) <= set(by_id[identifier].support):
            raise Malformed("A-DOUBLE twisted qubits must be a repeat-free "
                            "subset of the row's support")
        twisted[identifier] = set(qubits)
    n = len(state.Q)
    index = {q: i for i, q in enumerate(state.Q)}
    rows = []
    for row in state.rows:
        for sheet in (0, 1):
            mask = 0
            for q in row.support:
                target = sheet ^ (1 if q in twisted.get(row.id, ()) else 0)
                mask |= 1 << (target * n + index[q])
            sector = row.sector
            if conjugate and sheet == 1:
                sector = opposite_sector_name(sector)
            rows.append((sector, mask))
    if not _natural_rows_orthogonal(rows):
        raise NoDerivation("A-DOUBLE: the wiring does not give commuting natural rows")
    return _constructed_state(2 * n, rows)

def _permutation(value, size, name):
    value = _label_list(value, name)
    if sorted(value) != list(range(size)):
        raise Malformed("%s must be a permutation of 0..%d" % (name, size - 1))
    return value

def _group_action(orders, perms, size, name):
    """One permutation of 0..size-1 per cyclic generator, forming an action."""
    if not isinstance(perms, (list, tuple)) or len(perms) != len(orders):
        raise Malformed("%s must give one permutation per cyclic generator" % name)
    perms = [_permutation(p, size, name) for p in perms]
    for perm, order in zip(perms, orders):
        point = list(range(size))
        for _ in range(order):
            point = [perm[x] for x in point]
        if point != list(range(size)):
            raise Malformed("%s: a generator's permutation does not have order "
                            "dividing its cyclic order" % name)
    for s in range(len(perms)):
        for t in range(s + 1, len(perms)):
            if any(perms[s][perms[t][x]] != perms[t][perms[s][x]] for x in range(size)):
                raise Malformed("%s: the generators' permutations do not commute" % name)
    return perms

def _orbits(first_size, second_size, first_perms, second_perms):
    """Orbits of the pairs (x, y) under (x, y) -> (g x, g^{-1} y), in the
    order of their least pair. Returns (orbit index of each pair, orbits)."""
    inverses = [[perm.index(y) for y in range(second_size)] for perm in second_perms]
    orbit_of = {}
    orbits = []
    for x in range(first_size):
        for y in range(second_size):
            if (x, y) in orbit_of:
                continue
            members = []
            stack = [(x, y)]
            orbit_of[(x, y)] = len(orbits)
            while stack:
                u, v = stack.pop()
                members.append((u, v))
                for forward, backward in zip(first_perms, inverses):
                    image = (forward[u], backward[v])
                    if image not in orbit_of:
                        orbit_of[image] = len(orbits)
                        stack.append(image)
            orbits.append(sorted(members))
    return orbit_of, orbits

def _nonabelian_group_action(group_info, perms, size, is_right, name):
    """Validate and expand a permutation action of a finite group ``group_info``
    on ``0..size-1``.

    ``perms`` may be:
    - a list/tuple of ``|G|`` permutations indexed by ``0..|G|-1`` (or a dict
      mapping ``0..|G|-1`` to permutations), or
    - when ``group_info["kind"] == "generators"``, a list/tuple of one
      permutation per group generator.
    When ``is_right`` is True (``action1``), checks the right-action law
    ``rho(g * h)(x) == rho(h)(rho(g)(x))``. When ``is_right`` is False
    (``action2``), checks the left-action law
    ``lambda(g * h)(x) == lambda(g)(lambda(h)(x))``.
    Returns a list of ``|G|`` permutations indexed by ``0..|G|-1``.
    """
    ell = len(group_info["elements"])
    e_idx = group_info["identity"]
    table = group_info["table"]
    if isinstance(perms, dict):
        if set(perms) != set(range(ell)):
            raise Malformed("%s dict must map every group element 0..%d to a permutation"
                            % (name, ell - 1))
        full_perms = [_permutation(perms[g], size, name) for g in range(ell)]
    elif isinstance(perms, (list, tuple)):
        if len(perms) == ell:
            full_perms = [_permutation(p, size, name) for p in perms]
        elif (group_info["kind"] == "generators"
              and len(perms) == len(group_info["generator_indices"])):
            gen_perms = [_permutation(p, size, name) for p in perms]
            words = group_info["words"]
            full_perms = []
            for g in range(ell):
                cur = tuple(range(size))
                for gen_pos in words[g]:
                    gp = gen_perms[gen_pos]
                    if is_right:
                        cur = tuple(gp[cur[x]] for x in range(size))
                    else:
                        cur = tuple(cur[gp[x]] for x in range(size))
                full_perms.append(cur)
        else:
            raise Malformed(
                "%s must provide one permutation per group element (%d) or generator"
                % (name, ell))
    else:
        raise Malformed("%s must be a list of permutations" % name)

    id_perm = tuple(range(size))
    if full_perms[e_idx] != id_perm:
        raise Malformed("%s: identity group element must act as the identity permutation"
                        % name)
    for g in range(ell):
        pg = full_perms[g]
        for h in range(ell):
            ph = full_perms[h]
            p_gh = full_perms[table[g][h]]
            if is_right:
                # Right action: rho(g * h)(x) = rho(h)(rho(g)(x))
                if any(p_gh[x] != ph[pg[x]] for x in range(size)):
                    raise Malformed("%s does not satisfy the right-action homomorphism law"
                                    % name)
            else:
                # Left action: lambda(g * h)(x) = lambda(g)(lambda(h)(x))
                if any(p_gh[x] != pg[ph[x]] for x in range(size)):
                    raise Malformed("%s does not satisfy the left-action homomorphism law"
                                    % name)
    return full_perms


def balanced_product(group, H1, action1, H2, action2):
    """`L-BALANCED`: the balanced product of two binary matrices over a
    finite group G (abelian by cyclic orders, or nonabelian by multiplication
    table or permutation generators; spec/OPERATIONAL_SEMANTICS.md sections
    4.35 and 4.44).

    ``action1`` (right action on ``H1``) and ``action2`` (left action on ``H2``)
    are dicts with keys ``rows`` and ``cols``; ``H1`` and ``H2`` must be
    equivariant (``H[rows_g(a)][cols_g(i)] == H[a][i]``). The output is the
    hypergraph-product complex of ``H1`` and ``H2`` modulo the diagonal right
    action ``(x, y) -> (alpha_1(g)(x), alpha_2(g)^{-1}(y))``. The trivial
    group gives `L-HGP` row for row. Returns (state, dropped_rows).
    """
    info = _group_spec(group)
    H1 = _binary_matrix(H1, "H1")
    H2 = _binary_matrix(H2, "H2")
    m1, n1 = len(H1), len(H1[0])
    m2, n2 = len(H2), len(H2[0])
    actions = []
    for name, action, m, n, H, is_right in (
        ("action1", action1, m1, n1, H1, True),
        ("action2", action2, m2, n2, H2, False),
    ):
        if not isinstance(action, dict) or set(action) != {"rows", "cols"}:
            raise Malformed("%s must give row and column permutations" % name)
        if info["kind"] == "abelian":
            orders = info["orders"]
            rows = _group_action(orders, action["rows"], m, "%s rows" % name)
            cols = _group_action(orders, action["cols"], n, "%s cols" % name)
        else:
            rows = _nonabelian_group_action(info, action["rows"], m, is_right, "%s rows" % name)
            cols = _nonabelian_group_action(info, action["cols"], n, is_right, "%s cols" % name)
        for rho, kappa in zip(rows, cols):
            if any(H[rho[a]][kappa[i]] != H[a][i] for a in range(m) for i in range(n)):
                raise Malformed("%s: the matrix is not equivariant" % name)
        actions.append((rows, cols))
    (rows1, cols1), (rows2, cols2) = actions
    left_of, left = _orbits(n1, n2, cols1, cols2)
    right_of, right = _orbits(m1, m2, rows1, rows2)
    _x_of, x_checks = _orbits(m1, n2, rows1, cols2)
    _z_of, z_checks = _orbits(n1, m2, cols1, rows2)
    n = len(left) + len(right)

    def toggle(mask, bit):
        return mask ^ (1 << bit)

    rows = []
    # X-row of an X-check orbit c: the qubit orbits [q] for which an odd
    # number of members of c contain a representative q in their
    # hypergraph-product X-row.
    for orbit in x_checks:
        mask = 0
        for label, members in enumerate(left):
            i, j = members[0]
            if sum(1 for a, jj in orbit if jj == j and H1[a][i]) % 2:
                mask = toggle(mask, label)
        for label, members in enumerate(right):
            a, b = members[0]
            if sum(1 for aa, j in orbit if aa == a and H2[b][j]) % 2:
                mask = toggle(mask, len(left) + label)
        rows.append(("X", mask))
    # Z-row of a Z-check orbit: the image of a representative's
    # hypergraph-product Z-row in the qubit orbits, with cancellation.
    for orbit in z_checks:
        i, b = orbit[0]
        mask = 0
        for j in range(n2):
            if H2[b][j]:
                mask = toggle(mask, left_of[(i, j)])
        for a in range(m1):
            if H1[a][i]:
                mask = toggle(mask, len(left) + right_of[(a, b)])
        rows.append(("Z", mask))
    return _constructed_state(n, rows)

def tanner_code(n, local_x, local_z, views_x, views_z):
    """`L-TANNER`: local codes placed on the vertices of a bipartite
    incidence structure.

    ``local_x`` and ``local_z`` are binary matrices whose rows are the local
    X-checks and local Z-checks; ``views_x`` and ``views_z`` list, for each
    vertex of the X class and of the Z class, its embedding: an ordered
    list of distinct qubit labels in 0..n-1, as long as the local code. The
    natural rows are every local row at every vertex, read through the
    vertex's embedding, X class first. Applicability: the natural rows of
    the two sectors have pairwise even overlap (cross-partition
    commutation); otherwise there is no derivation. Returns
    (state, dropped_rows).
    """
    if isinstance(n, bool) or not isinstance(n, int) or n < 1:
        raise Malformed("L-TANNER takes a positive qubit count")
    local = {"X": _binary_matrix(local_x, "local_x"),
             "Z": _binary_matrix(local_z, "local_z")}
    rows = []
    for sector, views in (("X", views_x), ("Z", views_z)):
        if not isinstance(views, (list, tuple)):
            raise Malformed("L-TANNER views must be lists of embeddings")
        width = len(local[sector][0])
        for view in views:
            view = _label_list(view, "L-TANNER embedding")
            if (len(view) != width or len(set(view)) != width
                    or any(q >= n for q in view)):
                raise Malformed("an L-TANNER embedding lists %d distinct labels "
                                "below n" % width)
            for local_row in local[sector]:
                mask = 0
                for position, bit in enumerate(local_row):
                    if bit:
                        mask |= 1 << view[position]
                rows.append((sector, mask))
    if not _natural_rows_orthogonal(rows):
        raise NoDerivation("L-TANNER: the local checks of the two classes do not commute")
    return _constructed_state(n, rows)

def nested_css(check_x, check_z):
    """`L-NESTED-CSS`: the CSS code of two classical parity-check matrices.

    ``check_x`` and ``check_z`` are binary matrices with the same number n
    of columns: parity-check matrices of two classical codes of length n.
    The natural rows are the rows of ``check_x`` as X-rows, then the rows
    of ``check_z`` as Z-rows. Applicability: every row of ``check_x`` has
    even overlap with every row of ``check_z``, which is the nesting of
    the dual of the one code in the other; otherwise there is no
    derivation. A sector with no check is given as one zero row, which the
    retained display drops. Returns (state, dropped_rows).
    """
    check_x = _binary_matrix(check_x, "check_x")
    check_z = _binary_matrix(check_z, "check_z")
    n = len(check_x[0])
    if len(check_z[0]) != n:
        raise Malformed("L-NESTED-CSS takes two matrices with equally many columns")
    rows = []
    for sector, matrix in (("X", check_x), ("Z", check_z)):
        for row in matrix:
            mask = 0
            for position, bit in enumerate(row):
                if bit:
                    mask |= 1 << position
            rows.append((sector, mask))
    if not _natural_rows_orthogonal(rows):
        raise NoDerivation("L-NESTED-CSS: the two classical codes are not nested "
                           "(a row of check_x and a row of check_z overlap oddly)")
    return _constructed_state(n, rows)

def _apply_matrix(matrix, v):
    out = 0
    for j in range(len(matrix)):
        if (v >> j) & 1:
            out ^= matrix[j]
    return out


def mapping_cone(d_a, d_b, f1, f0):
    d_a = _binary_matrix(d_a, "d_a")
    d_b = _binary_matrix(d_b, "d_b")
    f1 = _binary_matrix(f1, "f1")
    f0 = _binary_matrix(f0, "f0")
    a1, a0 = len(d_a), len(d_a[0])
    b1, b0 = len(d_b), len(d_b[0])
    if len(f1) != a1 or any(len(row) != b1 for row in f1):
        raise Malformed("L-MAPPING-CONE takes f1 of shape a_1 x b_1")
    if len(f0) != a0 or any(len(row) != b0 for row in f0):
        raise Malformed("L-MAPPING-CONE takes f0 of shape a_0 x b_0")
    d_a_i = [sum(int(bit) << i for i, bit in enumerate(row)) for row in d_a]
    d_b_i = [sum(int(bit) << i for i, bit in enumerate(row)) for row in d_b]
    f1_i = [sum(int(bit) << i for i, bit in enumerate(row)) for row in f1]
    f0_i = [sum(int(bit) << i for i, bit in enumerate(row)) for row in f0]
    for j in range(a1):
        if _apply_matrix(d_b_i, f1_i[j]) != _apply_matrix(f0_i, d_a_i[j]):
            raise NoDerivation("L-MAPPING-CONE: the chain-map premise does not hold")
    n = a0 + b1
    rows = []
    for r in range(b0):
        mask = 0
        for i in range(a0):
            if (f0_i[i] >> r) & 1:
                mask |= 1 << i
        for j in range(b1):
            if (d_b_i[j] >> r) & 1:
                mask |= 1 << (a0 + j)
        rows.append(("X", mask))
    for j in range(a1):
        mask = d_a_i[j] | (f1_i[j] << a0)
        rows.append(("Z", mask))
    return _constructed_state(n, rows)


def tile_assembly(tiles, placements, identifications=(), removed=()):
    """`L-TILE`: local tiles placed on sites, with sites identified.

    A tile is a dict with ``qubits`` (its local qubit count t) and ``X`` and
    ``Z`` (lists of local row supports over 0..t-1). A placement is a pair
    (tile index, sites) with ``sites`` a list of t distinct site labels; two
    placements that name one site share that qubit. ``identifications`` is
    a list of site pairs to identify (the boundary rules), and ``removed``
    a list of (placement index, sector, local row index) naming tile rows
    that are not imposed. The qubits are the site classes in the order of
    their least site; the natural rows are the retained tile rows,
    placement by placement, X rows then Z rows, read through the placement
    and the identifications with cancellation. Applicability: the natural
    rows of the two sectors have pairwise even overlap (interface
    orthogonality); otherwise there is no derivation. Returns
    (state, dropped_rows).
    """
    if not isinstance(tiles, (list, tuple)) or not tiles:
        raise Malformed("L-TILE takes a non-empty tile set")
    parsed = []
    for tile in tiles:
        if not isinstance(tile, dict) or set(tile) != {"qubits", "X", "Z"}:
            raise Malformed("an L-TILE tile gives qubits, X, and Z")
        t = tile["qubits"]
        if isinstance(t, bool) or not isinstance(t, int) or t < 1:
            raise Malformed("an L-TILE tile has a positive local qubit count")
        local = {}
        for sector in ("X", "Z"):
            if not isinstance(tile[sector], (list, tuple)):
                raise Malformed("L-TILE tile rows must be lists of supports")
            supports = []
            for support in tile[sector]:
                support = _label_list(support, "L-TILE tile row")
                if len(set(support)) != len(support) or any(q >= t for q in support):
                    raise Malformed("an L-TILE tile row is a repeat-free "
                                    "support over the tile's qubits")
                supports.append(support)
            local[sector] = supports
        parsed.append((t, local))
    if not isinstance(placements, (list, tuple)) or not placements:
        raise Malformed("L-TILE takes a non-empty list of placements")
    placed = []
    parent = {}
    for placement in placements:
        if not isinstance(placement, (list, tuple)) or len(placement) != 2:
            raise Malformed("an L-TILE placement is a (tile index, sites) pair")
        tile_index, sites = placement
        if (isinstance(tile_index, bool) or not isinstance(tile_index, int)
                or not 0 <= tile_index < len(parsed)):
            raise Malformed("an L-TILE placement names a tile of the tile set")
        sites = _label_list(sites, "L-TILE sites")
        if len(sites) != parsed[tile_index][0] or len(set(sites)) != len(sites):
            raise Malformed("an L-TILE placement lists one distinct site per "
                            "local qubit")
        for site in sites:
            parent.setdefault(site, site)
        placed.append((tile_index, sites))

    def find(site):
        while parent[site] != site:
            parent[site] = parent[parent[site]]
            site = parent[site]
        return site

    if not isinstance(identifications, (list, tuple)):
        raise Malformed("L-TILE identifications must be a list of site pairs")
    for pair in identifications:
        pair = _label_list(pair, "L-TILE identification")
        if len(pair) != 2 or any(site not in parent for site in pair):
            raise Malformed("an L-TILE identification pairs two placed sites")
        low, high = sorted(find(site) for site in pair)
        parent[high] = low
    classes = sorted({find(site) for site in parent})
    label = {root: position for position, root in enumerate(classes)}
    dropped = set()
    if not isinstance(removed, (list, tuple)):
        raise Malformed("L-TILE removed must be a list of row references")
    for reference in removed:
        if not isinstance(reference, (list, tuple)) or len(reference) != 3:
            raise Malformed("an L-TILE removal is (placement, sector, row index)")
        position, sector, row_index = reference
        if (isinstance(position, bool) or not isinstance(position, int)
                or not 0 <= position < len(placed) or sector not in ("X", "Z")
                or isinstance(row_index, bool) or not isinstance(row_index, int)
                or not 0 <= row_index < len(parsed[placed[position][0]][1][sector])):
            raise Malformed("an L-TILE removal names a tile row of a placement")
        dropped.add((position, sector, row_index))
    rows = []
    for position, (tile_index, sites) in enumerate(placed):
        for sector in ("X", "Z"):
            for row_index, support in enumerate(parsed[tile_index][1][sector]):
                if (position, sector, row_index) in dropped:
                    continue
                mask = 0
                for q in support:
                    mask ^= 1 << label[find(sites[q])]
                rows.append((sector, mask))
    if not _natural_rows_orthogonal(rows):
        raise NoDerivation("L-TILE: the placed tile rows of the two sectors do not commute")
    return _constructed_state(len(classes), rows)

def empty_code():
    """`empty` (nullary base constructor): the CSS code on no
    qubits: $Q = \\varnothing$, empty display ($X = Z = \\{0\\}$), empty
    ``used``. Trivially well-formed (I1-I5 hold vacuously). Returns a
    ``CodeState`` with $n = 0$, $k = 0$.
    """
    state = CodeState((), (), frozenset())
    state.validate()
    return state


def free_code(qubits):
    """`free` (qubit-set base constructor): the CSS code with
    the given finite qubit set and an empty display ($X = Z = \\{0\\}$),
    so $k = n = |Q|$ and (for $Q \\neq \\varnothing$) semantic
    $d_X = d_Z = d = 1$. ``qubits`` is an iterable of distinct nonnegative
    integer labels; it is sorted and validated. Returns a ``CodeState``.
    """
    if not isinstance(qubits, (list, tuple, set, frozenset)):
        raise Malformed("free_code takes a collection of qubit labels")
    if isinstance(qubits, str):
        raise Malformed("free_code takes a collection of qubit labels")
    try:
        qubit_list = list(qubits)
    except TypeError:
        raise Malformed("free_code takes a collection of qubit labels")
    labels = sorted(set(qubit_list))
    if any(isinstance(q, bool) or not isinstance(q, int) or q < 0 for q in qubit_list):
        raise Malformed("free_code qubit labels must be nonnegative integers")
    if len(qubit_list) != len(set(qubit_list)):
        raise Malformed("free_code qubit labels must be distinct")
    state = CodeState(tuple(labels), (), frozenset())
    state.validate()
    return state


def _parse_qubit_map(mapping, domain, codomain, name):
    """Parse a total qubit map ``domain -> codomain`` from a dict or pair list."""
    if isinstance(mapping, dict):
        items = list(mapping.items())
    elif isinstance(mapping, (list, tuple)):
        items = []
        for entry in mapping:
            if not isinstance(entry, (list, tuple)) or len(entry) != 2:
                raise Malformed("%s entries must be (source, target) pairs" % name)
            items.append((entry[0], entry[1]))
    else:
        raise Malformed("%s must be a dict or list of (source, target) pairs" % name)
    dom_set = set(domain)
    cod_set = set(codomain)
    parsed = {}
    for src, dst in items:
        if (isinstance(src, bool) or not isinstance(src, int)
                or isinstance(dst, bool) or not isinstance(dst, int)):
            raise Malformed("%s labels must be integers" % name)
        if src in parsed:
            raise Malformed("%s has duplicate source label %d" % (name, src))
        if src not in dom_set:
            raise Malformed("%s source label %d is not in domain" % (name, src))
        if dst not in cod_set:
            raise Malformed("%s target label %d is not in codomain" % (name, dst))
        parsed[src] = dst
    if set(parsed) != dom_set:
        raise Malformed("%s must be total on the source qubit set" % name)
    return parsed


def _check_css_morphism(src, dst, mapping, name):
    """Check that the F_2-pushforward of every displayed row of ``src`` lies
    in the same-sector row space of ``dst``."""
    dst_bases = {
        "X": [row.mask for row in dst.sector_rows("X")],
        "Z": [row.mask for row in dst.sector_rows("Z")],
    }
    for row in src.rows:
        pushed_mask = 0
        for q in row.support:
            pushed_mask ^= 1 << mapping[q]
        if not in_span(pushed_mask, dst_bases[row.sector]):
            raise NoDerivation("%s: qubit map does not preserve %s-row %s"
                               % (name, row.sector, row.id))


def pullback_code(c1, c2, iface, phi1, phi2):
    """`A-PULLBACK`: fiber product of ``c1`` and ``c2`` over ``iface`` along
    CSS code morphisms ``phi1 : c1 -> iface`` and ``phi2 : c2 -> iface``.
    Returns (state, dropped_rows).
    """
    for arg, label in ((c1, "left"), (c2, "right"), (iface, "interface")):
        if not isinstance(arg, CodeState):
            raise Malformed("A-PULLBACK %s must be a CodeState" % label)
        arg.validate()
    m1 = _parse_qubit_map(phi1, c1.Q, iface.Q, "A-PULLBACK phi1")
    m2 = _parse_qubit_map(phi2, c2.Q, iface.Q, "A-PULLBACK phi2")
    _check_css_morphism(c1, iface, m1, "A-PULLBACK phi1")
    _check_css_morphism(c2, iface, m2, "A-PULLBACK phi2")
    pairs = [(q1, q2) for q1 in c1.Q for q2 in c2.Q if m1[q1] == m2[q2]]
    n = len(pairs)
    rows = []
    for row in c1.rows:
        sup = set(row.support)
        mask = 0
        for idx, (q1, _q2) in enumerate(pairs):
            if q1 in sup:
                mask |= 1 << idx
        rows.append((row.sector, mask))
    for row in c2.rows:
        sup = set(row.support)
        mask = 0
        for idx, (_q1, q2) in enumerate(pairs):
            if q2 in sup:
                mask |= 1 << idx
        rows.append((row.sector, mask))
    if not _natural_rows_orthogonal(rows):
        raise NoDerivation("A-PULLBACK: pulled-back rows of the two sectors do not commute")
    return _constructed_state(n, rows)


def pushout_code(c1, c2, sub, psi1, psi2):
    """`A-PUSHOUT`: amalgamated sum of ``c1`` and ``c2`` along ``sub`` via
    CSS code morphisms ``psi1 : sub -> c1`` and ``psi2 : sub -> c2``.
    Returns (state, dropped_rows).
    """
    for arg, label in ((c1, "left"), (c2, "right"), (sub, "subcode")):
        if not isinstance(arg, CodeState):
            raise Malformed("A-PUSHOUT %s must be a CodeState" % label)
        arg.validate()
    m1 = _parse_qubit_map(psi1, sub.Q, c1.Q, "A-PUSHOUT psi1")
    m2 = _parse_qubit_map(psi2, sub.Q, c2.Q, "A-PUSHOUT psi2")
    _check_css_morphism(sub, c1, m1, "A-PUSHOUT psi1")
    _check_css_morphism(sub, c2, m2, "A-PUSHOUT psi2")
    nodes = [(0, q1) for q1 in c1.Q] + [(1, q2) for q2 in c2.Q]
    index_of = {node: idx for idx, node in enumerate(nodes)}
    parent = list(range(len(nodes)))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for s in sub.Q:
        u = find(index_of[(0, m1[s])])
        v = find(index_of[(1, m2[s])])
        if u != v:
            low, high = (u, v) if u < v else (v, u)
            parent[high] = low
    classes = sorted({find(i) for i in range(len(nodes))})
    label = {root: pos for pos, root in enumerate(classes)}
    n = len(classes)
    rows = []
    for side, code in ((0, c1), (1, c2)):
        for row in code.rows:
            mask = 0
            for q in row.support:
                mask ^= 1 << label[find(index_of[(side, q)])]
            rows.append((row.sector, mask))
    if not _natural_rows_orthogonal(rows):
        raise NoDerivation("A-PUSHOUT: pushed-forward rows of the two sectors do not commute")
    return _constructed_state(n, rows)


def _gf2_nullspace_basis(row_masks, ncols):
    """Deterministic RREF basis of the GF(2) kernel of ``row_masks`` over
    columns ``0..ncols-1``."""
    rref = []
    for m in row_masks:
        v = m
        for pcol, pmask in rref:
            if (v >> pcol) & 1:
                v ^= pmask
        if v:
            pcol = (v & -v).bit_length() - 1
            rref = [(c, rm ^ v if (rm >> pcol) & 1 else rm) for c, rm in rref]
            rref.append((pcol, v))
    pivot_cols = {c for c, _ in rref}
    free_cols = [c for c in range(ncols) if c not in pivot_cols]
    basis = []
    for f in free_cols:
        vec = 1 << f
        for pcol, pmask in rref:
            if (pmask >> f) & 1:
                vec |= 1 << pcol
        basis.append(vec)
    return basis


def _mask_to_support(mask, ncols):
    return tuple(c for c in range(ncols) if (mask >> c) & 1)


def _best_kernel_supports(row_masks, ncols, max_enum_dim=8):
    """Deterministic list of non-zero kernel supports: all RREF basis vectors,
    plus (when ker dim <= max_enum_dim) the minimum-weight non-zero codeword."""
    basis = _gf2_nullspace_basis(row_masks, ncols)
    if not basis:
        return []
    seen = {}
    for vec in basis:
        sup = _mask_to_support(vec, ncols)
        seen[sup] = len(sup)
    if len(basis) <= max_enum_dim:
        best_weight = None
        best_sup = None
        for bits in range(1, 1 << len(basis)):
            vec = 0
            for idx, bvec in enumerate(basis):
                if (bits >> idx) & 1:
                    vec ^= bvec
            w = vec.bit_count()
            if best_weight is None or w <= best_weight:
                sup = _mask_to_support(vec, ncols)
                if best_weight is None or w < best_weight or sup < best_sup:
                    best_weight = w
                    best_sup = sup
        if best_sup is not None:
            seen[best_sup] = best_weight
    return sorted(seen, key=lambda s: (len(s), s))


def _extract_supplied_supports(supplied, side):
    if supplied is None:
        return None
    if isinstance(supplied, DistanceLedger):
        return [tuple(sorted(w["support"])) for w in supplied.witnesses.get(side, ())]
    if isinstance(supplied, dict) and side in supplied:
        out = []
        for entry in supplied[side]:
            raw = entry["support"] if isinstance(entry, dict) else entry
            out.append(tuple(sorted(int(q) for q in raw)))
        return out
    return None


def _state_logical_supports(state, side, supplied=None, max_enum_dim=8):
    """Deterministic validated logical supports of ``state`` in sector ``side``."""
    from_supplied = _extract_supplied_supports(supplied, side)
    if from_supplied is not None:
        valid = []
        for sup in from_supplied:
            validate_witness(state, side, sup, len(sup))
            valid.append(sup)
        return valid
    labels = list(state.Q)
    n = len(labels)
    if n == 0:
        return []
    index_of = {q: i for i, q in enumerate(labels)}
    opp = opposite_sector_name(side)

    def compact_mask(row):
        m = 0
        for q in row.support:
            m |= 1 << index_of[q]
        return m

    opp_masks = [compact_mask(r) for r in state.sector_rows(opp)]
    same_masks = [compact_mask(r) for r in state.sector_rows(side)]
    basis = _gf2_nullspace_basis(opp_masks, n)
    seen = set()
    candidates = []
    for vec in basis:
        if not in_span(vec, same_masks):
            sup = tuple(labels[c] for c in range(n) if (vec >> c) & 1)
            if sup not in seen:
                seen.add(sup)
                candidates.append(sup)
    if basis and len(basis) <= max_enum_dim:
        best_weight = None
        best_sup = None
        for bits in range(1, 1 << len(basis)):
            vec = 0
            for idx, bvec in enumerate(basis):
                if (bits >> idx) & 1:
                    vec ^= bvec
            if in_span(vec, same_masks):
                continue
            w = vec.bit_count()
            if best_weight is None or w <= best_weight:
                sup = tuple(labels[c] for c in range(n) if (vec >> c) & 1)
                if best_weight is None or w < best_weight or sup < best_sup:
                    best_weight = w
                    best_sup = sup
        if best_sup is not None and best_sup not in seen:
            seen.add(best_sup)
            candidates.append(best_sup)
    candidates.sort(key=lambda s: (len(s), s))
    return candidates


def _collect_valid_witnesses(state, candidates, source):
    """Validate candidate supports on ``state`` and format as witness entries."""
    out = {"X": [], "Z": []}
    for side in ("X", "Z"):
        seen = set()
        valid = []
        for raw in candidates.get(side, ()):
            sup = tuple(sorted(int(q) for q in raw))
            if not sup or sup in seen:
                continue
            try:
                validate_witness(state, side, sup, len(sup))
            except (NoDerivation, Malformed):
                continue
            seen.add(sup)
            valid.append({
                "support": list(sup),
                "value": len(sup),
                "source": source,
            })
        valid.sort(key=lambda w: (w["value"], w["support"]))
        out[side] = valid
    return out


def lift_hgp_witnesses(H1, H2, state=None):
    """Deterministic factor-to-child witness lifting for `L-HGP`
    (spec/OPERATIONAL_SEMANTICS.md section 4.45)."""
    H1 = _binary_matrix(H1, "H1")
    H2 = _binary_matrix(H2, "H2")
    if state is None:
        state, _ = hypergraph_product(H1, H2)
    m1, n1 = len(H1), len(H1[0])
    m2, n2 = len(H2), len(H2[0])
    h1_masks = [sum(bit << c for c, bit in enumerate(row)) for row in H1]
    h2_masks = [sum(bit << c for c, bit in enumerate(row)) for row in H2]
    h1t_masks = [sum(H1[r][c] << r for r in range(m1)) for c in range(n1)]
    h2t_masks = [sum(H2[r][c] << r for r in range(m2)) for c in range(n2)]

    ker1 = _best_kernel_supports(h1_masks, n1)
    ker2 = _best_kernel_supports(h2_masks, n2)
    ker1t = _best_kernel_supports(h1t_masks, m1)
    ker2t = _best_kernel_supports(h2t_masks, m2)

    j_anchors = sorted({sup[0] for sup in ker2}) if ker2 else list(range(n2))
    i_anchors = sorted({sup[0] for sup in ker1}) if ker1 else list(range(n1))
    a_anchors = sorted({sup[0] for sup in ker1t}) if ker1t else list(range(m1))
    b_anchors = sorted({sup[0] for sup in ker2t}) if ker2t else list(range(m2))

    left = n1 * n2
    candidates = {"X": [], "Z": []}
    for v in ker2:
        for i0 in i_anchors:
            candidates["X"].append(tuple(i0 * n2 + j for j in v))
    for ut in ker1t:
        for b0 in b_anchors:
            candidates["X"].append(tuple(left + a * m2 + b0 for a in ut))
    for u in ker1:
        for j0 in j_anchors:
            candidates["Z"].append(tuple(i * n2 + j0 for i in u))
    for vt in ker2t:
        for a0 in a_anchors:
            candidates["Z"].append(tuple(left + a0 * m2 + b for b in vt))
    return _collect_valid_witnesses(state, candidates, "L-HGP lifted witness")


def lift_nested_witnesses(HX, HZ, state=None, factor_witnesses=None):
    """Deterministic factor-to-child witness lifting for `L-NESTED-CSS`
    (spec/OPERATIONAL_SEMANTICS.md section 4.45)."""
    HX = _binary_matrix(HX, "HX")
    HZ = _binary_matrix(HZ, "HZ")
    if state is None:
        state, _ = nested_css(HX, HZ)
    n = len(HX[0])
    hx_masks = [sum(bit << c for c, bit in enumerate(row)) for row in HX]
    hz_masks = [sum(bit << c for c, bit in enumerate(row)) for row in HZ]
    candidates = {"X": [], "Z": []}
    for side, ker_masks in (("X", hz_masks), ("Z", hx_masks)):
        supplied = _extract_supplied_supports(factor_witnesses, side)
        if supplied:
            candidates[side].extend(supplied)
        candidates[side].extend(_best_kernel_supports(ker_masks, n))
    return _collect_valid_witnesses(state, candidates, "L-NESTED-CSS lifted witness")


def lift_concat_witnesses(outer, inner, groups, state=None,
                          outer_witnesses=None, representatives=None):
    """Deterministic factor-to-child witness lifting for `A-CONCAT`
    (spec/OPERATIONAL_SEMANTICS.md section 4.45)."""
    outer = _factor_state(outer)
    inner = _factor_state(inner)
    if state is None:
        state, _ = concatenate(outer, inner, groups, representatives=representatives)
    level = tower_level_data(inner)
    if level.get("status") != "computed":
        raise Malformed("A-CONCAT inner code: %s" % level.get("reason"))
    k_in = level["k_in"]
    _tower_groups(outer, groups, k_in)
    groups = [tuple(group) for group in groups]
    reps = representatives if representatives is not None else level["logical_basis"]
    inner_labels = list(inner.Q)
    n_in = len(inner_labels)
    index_of = {label: i for i, label in enumerate(inner_labels)}

    def shift(mask, block):
        out = 0
        for label in inner_labels:
            if (mask >> label) & 1:
                out |= 1 << (block * n_in + index_of[label])
        return out

    n_total = n_in * len(groups)
    candidates = {"X": [], "Z": []}
    for side in ("X", "Z"):
        outer_sups = _state_logical_supports(outer, side, outer_witnesses)
        for sup in outer_sups:
            sup_set = set(sup)
            mask = 0
            for block, group in enumerate(groups):
                rep = 0
                for position, label in enumerate(group):
                    if label in sup_set:
                        rep ^= reps[side][position]
                mask |= shift(rep, block)
            candidates[side].append(_mask_to_support(mask, n_total))
    return _collect_valid_witnesses(state, candidates, "A-CONCAT lifted witness")


def lift_product_witnesses(left, right, state=None,
                           left_witnesses=None, right_witnesses=None):
    """Deterministic middle-block factor-to-child witness lifting for `A-PRODUCT`
    (spec/OPERATIONAL_SEMANTICS.md section 4.45)."""
    left = _factor_state(left)
    right = _factor_state(right)
    if state is None:
        state, _ = css_tensor_product(left, right)
    first = len(left.sector_rows("Z")) * len(right.sector_rows("X"))
    nb = len(right.Q)
    index_a = {q: i for i, q in enumerate(left.Q)}
    index_b = {q: j for j, q in enumerate(right.Q)}
    candidates = {"X": [], "Z": []}
    for side in ("X", "Z"):
        left_sups = _state_logical_supports(left, side, left_witnesses)
        right_sups = _state_logical_supports(right, side, right_witnesses)
        for sa in left_sups:
            for sb in right_sups:
                sup = tuple(sorted(
                    first + index_a[qa] * nb + index_b[qb]
                    for qa in sa for qb in sb
                ))
                candidates[side].append(sup)
    return _collect_valid_witnesses(state, candidates, "A-PRODUCT lifted witness")


def lift_double_witnesses(parent, wiring=None, conjugate=False,
                          state=None, parent_witnesses=None):
    """Deterministic factor-to-child witness lifting for `A-DOUBLE`
    (spec/OPERATIONAL_SEMANTICS.md section 4.45)."""
    parent = _factor_state(parent)
    wiring = wiring or {}
    if state is None:
        state, _ = double_cover(parent, wiring, conjugate=conjugate)
    n = len(parent.Q)
    index = {q: i for i, q in enumerate(parent.Q)}
    candidates = {"X": [], "Z": []}
    for side in ("X", "Z"):
        p_sups = _state_logical_supports(parent, side, parent_witnesses)
        sheet1_side = opposite_sector_name(side) if conjugate else side
        for sup in p_sups:
            s0 = tuple(sorted(index[q] for q in sup))
            s1 = tuple(sorted(n + index[q] for q in sup))
            candidates[side].append(s0)
            candidates[sheet1_side].append(s1)
            if not conjugate:
                candidates[side].append(tuple(sorted(s0 + s1)))
    return _collect_valid_witnesses(state, candidates, "A-DOUBLE lifted witness")


def _parse_affine_blocks(p, blocks, name):
    """Parse a J x L block matrix of affine descriptors (a, b) over Z_p.

    An integer entry b is accepted as shorthand for the circulant (CPM) block
    (1, b % p); a 2-tuple (a, b) specifies the affine permutation block
    v = (a * u + b) % p with unit slope gcd(a, p) = 1.
    """
    if isinstance(p, bool) or not isinstance(p, int) or p < 1:
        raise Malformed("%s: lift size p must be a positive integer" % name)
    if not isinstance(blocks, (list, tuple)) or not blocks:
        raise Malformed("%s must be a non-empty list of block rows" % name)
    width = None
    out = []
    for r, row in enumerate(blocks):
        if not isinstance(row, (list, tuple)) or not row:
            raise Malformed("%s rows must be non-empty lists" % name)
        if width is None:
            width = len(row)
        if len(row) != width:
            raise Malformed("%s rows must have equal length" % name)
        parsed_row = []
        for c, entry in enumerate(row):
            if isinstance(entry, int) and not isinstance(entry, bool):
                a, b = 1, entry
            elif isinstance(entry, (list, tuple)) and len(entry) == 2:
                a, b = entry
                if (isinstance(a, bool) or not isinstance(a, int)
                        or isinstance(b, bool) or not isinstance(b, int)):
                    raise Malformed("%s[%d][%d] slope and shift must be integers"
                                    % (name, r, c))
            else:
                raise Malformed("%s[%d][%d] must be a shift int or (slope, shift) pair"
                                % (name, r, c))
            if math.gcd(a, p) != 1:
                raise NoDerivation("%s[%d][%d] slope %d is not a unit modulo %d"
                                   % (name, r, c, a, p))
            parsed_row.append((a % p if p > 1 else 1, b % p))
        out.append(tuple(parsed_row))
    if width < 2 or width % 2 != 0:
        raise NoDerivation("%s block column count L=%d must be an even integer >= 2"
                           % (name, width))
    return tuple(out)


def _check_pair_partition_orthogonality(p, bx, bz, pair_partition=None, name="L-PAIR-PARTITION"):
    """Verify the paired relative-affine orthogonality premise (Okada-Kasai v4
    Thm 4): for each block-row pair (r, s), the L columns partition into L/2
    pairs with matching relative affine maps A(a_X, b_X) A(a_Z, b_Z)^T.
    """
    L = len(bx[0])
    for r, row_x in enumerate(bx):
        for s, row_z in enumerate(bz):
            rel = []
            for c in range(L):
                ax, shift_x = row_x[c]
                az, shift_z = row_z[c]
                az_inv = pow(az, -1, p) if p > 1 else 1
                alpha = (ax * az_inv) % p if p > 1 else 1
                beta = (az_inv * (shift_x - shift_z)) % p
                rel.append((alpha, beta))
            if pair_partition is not None:
                if not isinstance(pair_partition, (list, tuple)):
                    raise Malformed("%s pair_partition must be a list of column pairs" % name)
                pairs = pair_partition[r][s] if (
                    len(pair_partition) == len(bx)
                    and isinstance(pair_partition[r], (list, tuple))
                    and len(pair_partition[r]) == len(bz)
                    and isinstance(pair_partition[r][s], (list, tuple))
                    and pair_partition[r][s]
                    and isinstance(pair_partition[r][s][0], (list, tuple))
                ) else pair_partition
                if not isinstance(pairs, (list, tuple)):
                    raise Malformed("%s pair_partition entries must be column pairs" % name)
                seen_cols = []
                for pair in pairs:
                    if not isinstance(pair, (list, tuple)) or len(pair) != 2:
                        raise Malformed("%s pair_partition entries must be column pairs" % name)
                    c1, c2 = pair
                    if (isinstance(c1, bool) or not isinstance(c1, int)
                            or isinstance(c2, bool) or not isinstance(c2, int)
                            or not (0 <= c1 < L and 0 <= c2 < L) or c1 == c2):
                        raise Malformed("%s pair_partition names invalid columns" % name)
                    seen_cols.extend([c1, c2])
                    if rel[c1] != rel[c2]:
                        raise NoDerivation(
                            "%s: paired columns (%d, %d) have unequal relative affine maps "
                            "at block rows (%d, %d)" % (name, c1, c2, r, s))
                if sorted(seen_cols) != list(range(L)):
                    raise Malformed("%s pair_partition must partition 0..L-1" % name)
            else:
                counts = {}
                for item in rel:
                    counts[item] = counts.get(item, 0) + 1
                if any(cnt % 2 != 0 for cnt in counts.values()):
                    raise NoDerivation(
                        "%s: block rows (%d, %d) do not admit a relative-affine pair partition"
                        % (name, r, s))


def _affine_block_rows(p, bx, bz):
    """Assemble the natural X and Z row bitmasks over n = L * p qubits."""
    L = len(bx[0])
    rows = []
    for sector, blocks in (("X", bx), ("Z", bz)):
        for row in blocks:
            for u in range(p):
                mask = 0
                for c, (a, b) in enumerate(row):
                    v = (a * u + b) % p
                    mask |= 1 << (c * p + v)
                rows.append((sector, mask))
    return L * p, rows


def pair_partition_code(p, blocks_x, blocks_z, pair_partition=None):
    """`L-PAIR-PARTITION`: pair-partition relative-permutation CSS constructor
    (CPM-PP / APM-PP; `spec/OPERATIONAL_SEMANTICS.md` section 2 card, section 4.46).


    Builds a CSS code on n = L * p qubits from J_X x L and J_Z x L block
    matrices of affine permutation descriptors (a, b) over Z_p (with integer b
    accepted as CPM shorthand for (1, b)). Applicability requires unit slopes
    gcd(a, p) = 1 and a relative-affine pair partition on every block-row pair
    so that the natural rows commute. Returns (state, dropped_rows).
    """
    bx = _parse_affine_blocks(p, blocks_x, "L-PAIR-PARTITION blocks_x")
    bz = _parse_affine_blocks(p, blocks_z, "L-PAIR-PARTITION blocks_z")
    if len(bx[0]) != len(bz[0]):
        raise Malformed("L-PAIR-PARTITION blocks_x and blocks_z must have equal column count L")
    _check_pair_partition_orthogonality(p, bx, bz, pair_partition, "L-PAIR-PARTITION")
    n, rows = _affine_block_rows(p, bx, bz)
    if not _natural_rows_orthogonal(rows):
        raise NoDerivation("L-PAIR-PARTITION: natural X and Z rows do not commute")
    return _constructed_state(n, rows)


def _evaluate_snf_bundle_at_size(bundle, target_p, roots_key="roots_r"):
    """Evaluate a Kasai §2.1 SNF parameter bundle at lift size ``target_p``:
    slopes a_q(P) = prod_j r_j(P)^{Q_{qj}} (mod P) with r_j(P)^{e_j} = 1 (mod P),
    and shifts b(P) = G(P) theta (mod P). Returns (blocks_x, blocks_z).
    """
    orders_e = bundle.get("orders_e", ())
    roots = bundle.get(roots_key, ())
    if not isinstance(orders_e, (list, tuple)) or not isinstance(roots, (list, tuple)):
        raise Malformed("PP-SCALE bundle orders_e and roots must be lists")
    if len(orders_e) != len(roots):
        raise Malformed("PP-SCALE bundle orders_e and roots must have equal length")
    for j, (e_j, r_j) in enumerate(zip(orders_e, roots)):
        if (isinstance(e_j, bool) or not isinstance(e_j, int) or e_j < 1
                or isinstance(r_j, bool) or not isinstance(r_j, int)):
            raise Malformed("PP-SCALE bundle orders_e and roots must be integers")
        if math.gcd(r_j, target_p) != 1 or pow(r_j, e_j, target_p) != 1 % target_p:
            raise NoDerivation(
                "PP-SCALE: root r_%d=%d does not satisfy r^{e_j} = 1 (mod %d)"
                % (j, r_j, target_p))
    out = {}
    for sector in ("x", "z"):
        q_mat = bundle.get("Q_" + sector)
        g_mat = bundle.get("G_" + sector)
        theta = bundle.get("theta_" + sector)
        shape = bundle.get("shape_" + sector)
        if q_mat is None or g_mat is None or theta is None or shape is None:
            raise Malformed("PP-SCALE SNF bundle requires Q_%s, G_%s, theta_%s, shape_%s"
                            % (sector, sector, sector, sector))
        if (not isinstance(shape, (list, tuple)) or len(shape) != 2
                or any(isinstance(d, bool) or not isinstance(d, int) or d < 1 for d in shape)):
            raise Malformed("PP-SCALE shape_%s must be (J, L)" % sector)
        J, L = shape
        total = J * L
        if len(q_mat) != total or len(g_mat) != total:
            raise Malformed("PP-SCALE Q_%s and G_%s must have J*L=%d rows"
                            % (sector, sector, total))
        slopes = []
        for row_q in q_mat:
            if not isinstance(row_q, (list, tuple)) or len(row_q) != len(roots):
                raise Malformed("PP-SCALE Q_%s row length must match roots" % sector)
            val = 1 % target_p
            for r_j, exp_q in zip(roots, row_q):
                if isinstance(exp_q, bool) or not isinstance(exp_q, int):
                    raise Malformed("PP-SCALE Q_%s exponents must be integers" % sector)
                val = (val * pow(r_j % target_p, exp_q, target_p)) % target_p
            slopes.append(val)
        shifts = []
        for row_g in g_mat:
            if not isinstance(row_g, (list, tuple)) or len(row_g) != len(theta):
                raise Malformed("PP-SCALE G_%s row length must match theta_%s"
                                % (sector, sector))
            val = 0
            for g_entry, th_entry in zip(row_g, theta):
                if (isinstance(g_entry, bool) or not isinstance(g_entry, int)
                        or isinstance(th_entry, bool) or not isinstance(th_entry, int)):
                    raise Malformed("PP-SCALE G_%s and theta_%s entries must be integers"
                                    % (sector, sector))
                val = (val + g_entry * th_entry) % target_p
            shifts.append(val)
        blocks = []
        for r in range(J):
            blocks.append([
                (slopes[r * L + c], shifts[r * L + c])
                for c in range(L)
            ])
        out[sector] = blocks
    return out["x"], out["z"]


def pp_scale_code(state0, P, bundle=None, blocks_x=None, blocks_z=None):
    """`PP-SCALE`: explicit extension (size scaling) of a PP-presented CSS code
    to target lift size P >= 2 (Kasai 2026; `spec/OPERATIONAL_SEMANTICS.md`
    section 2 card, section 4.45, `OBL-PP-SCALE`).

    Evaluates the PP parameter bundle (either an SNF parametrization bundle
    checked for reproduction at P0 against ``state0``, or evaluated target
    affine block matrices ``blocks_x``, ``blocks_z``) at target lift size
    ``P >= 2``. Row identifiers are canonically minted starting from
    ``state0.used`` (disjoint from ``state0.used``), and applicability requires
    positive logical dimension k' > 0. Returns (state, dropped_rows).
    """
    if not isinstance(state0, CodeState):
        raise Malformed("PP-SCALE state0 must be a CodeState")
    state0.validate()
    if isinstance(P, bool) or not isinstance(P, int):
        raise Malformed("PP-SCALE target size P must be an integer")
    if P < 2:
        raise NoDerivation("PP-SCALE requires target lift size P >= 2")
    pair_partition = None
    if bundle is not None:
        if not isinstance(bundle, dict):
            raise Malformed("PP-SCALE bundle must be a dict")
        pair_partition = bundle.get("pair_partition")
        if "P0" in bundle:
            p0 = bundle["P0"]
            if isinstance(p0, bool) or not isinstance(p0, int) or p0 < 2:
                raise Malformed("PP-SCALE bundle P0 must be an integer >= 2")
            if "Q_x" in bundle:
                repro_bx, repro_bz = _evaluate_snf_bundle_at_size(
                    bundle, p0, roots_key="roots_r0" if "roots_r0" in bundle else "roots_r")
            else:
                repro_bx = bundle.get("blocks_x0")
                repro_bz = bundle.get("blocks_z0")
                if repro_bx is None or repro_bz is None:
                    raise Malformed("PP-SCALE bundle with P0 requires SNF matrices or blocks_x0/blocks_z0")
            bx0 = _parse_affine_blocks(p0, repro_bx, "PP-SCALE blocks_x0")
            bz0 = _parse_affine_blocks(p0, repro_bz, "PP-SCALE blocks_z0")
            if "blocks_x0" in bundle and "Q_x" in bundle:
                exp_bx0 = _parse_affine_blocks(p0, bundle["blocks_x0"], "PP-SCALE expected blocks_x0")
                exp_bz0 = _parse_affine_blocks(p0, bundle["blocks_z0"], "PP-SCALE expected blocks_z0")
                if bx0 != exp_bx0 or bz0 != exp_bz0:
                    raise NoDerivation("PP-SCALE: SNF reproduction check failed at P0=%d" % p0)
            _check_pair_partition_orthogonality(p0, bx0, bz0, pair_partition, "PP-SCALE(P0)")
            n0, rows0 = _affine_block_rows(p0, bx0, bz0)
            repro_state, _ = _constructed_state(n0, rows0)
            repro_supports = {(r.sector, r.support) for r in repro_state.rows}
            actual_supports = {(r.sector, r.support) for r in state0.rows}
            if len(state0.Q) != n0 or repro_supports != actual_supports:
                raise NoDerivation("PP-SCALE: SNF reproduction check does not reproduce state0 at P0=%d" % p0)
        if blocks_x is None and blocks_z is None:
            if "Q_x" in bundle:
                blocks_x, blocks_z = _evaluate_snf_bundle_at_size(bundle, P, roots_key="roots_r")
            else:
                blocks_x = bundle.get("blocks_x")
                blocks_z = bundle.get("blocks_z")
    if blocks_x is None or blocks_z is None:
        raise Malformed("PP-SCALE requires target blocks_x and blocks_z or an SNF bundle")
    bx = _parse_affine_blocks(P, blocks_x, "PP-SCALE blocks_x")
    bz = _parse_affine_blocks(P, blocks_z, "PP-SCALE blocks_z")
    if len(bx[0]) != len(bz[0]):
        raise Malformed("PP-SCALE blocks_x and blocks_z must have equal column count L")
    _check_pair_partition_orthogonality(P, bx, bz, pair_partition, "PP-SCALE")
    n, rows = _affine_block_rows(P, bx, bz)
    if not _natural_rows_orthogonal(rows):
        raise NoDerivation("PP-SCALE: generated natural X and Z rows do not commute")
    state, dropped = _constructed_state(n, rows, initial_used=state0.used)
    k_out = n - rank([r.mask for r in state.sector_rows("X")]) \
        - rank([r.mask for r in state.sector_rows("Z")])
    if k_out <= 0:
        raise NoDerivation("PP-SCALE: positive dimension premise k' > 0 failed (k' = %d)" % k_out)
    return state, dropped



def _factor_state(value):
    if isinstance(value, dict):
        return CodeState.from_challenge(value)
    return value

def construct(spec):
    """Evaluate an admitted expression constructor from a specification dict.

    ``spec["constructor"]`` names the taxonomy ID; the remaining keys are its
    typed inputs: ``H1``, ``H2`` for `L-HGP`; ``group``, ``A``, ``B`` for
    `L-LIFTED`; ``group``, ``a``, ``b`` for `L-GROUP-ALGEBRA`; ``outer``,
    ``inner`` (CodeState objects or challenge documents), ``groups``, and
    optional ``representatives`` for `A-CONCAT`; ``group``, ``H1``,
    ``action1``, ``H2``, ``action2`` for `L-BALANCED`; ``n``, ``local_x``,
    ``local_z``, ``views_x``, ``views_z`` for `L-TANNER`; ``tiles``,
    ``placements``, and optional ``identifications`` and ``removed`` for
    `L-TILE`; ``left`` and ``right`` (CodeState objects or challenge
    documents) for `A-PRODUCT`; ``state``, ``wiring``, and optional
    ``conjugate`` for `A-DOUBLE`; ``HX`` and ``HZ`` for `L-NESTED-CSS`.
    Optional distance-ledger inputs (``lower_bounds``, ``constructor_cell``,
    ``witnesses``, ``lift_witnesses``) attach a ``ledger`` built through
    ``DistanceLedger.for_constructed``.
    Returns a dict with the state, the constructor, n, k, and the number of
    natural rows the retained display dropped (plus ``ledger`` when requested).
    A failed applicability premise raises ``NoDerivation``.
    """
    if not isinstance(spec, dict) or "constructor" not in spec:
        raise Malformed("a constructor specification names its constructor")
    name = spec["constructor"]
    if name in UNADMITTED_CONSTRUCTORS:
        raise Malformed("constructor %s is not admitted: %s"
                        % (name, UNADMITTED_CONSTRUCTORS[name]))
    if name == "L-HGP":
        state, dropped = hypergraph_product(spec.get("H1"), spec.get("H2"))
    elif name == "L-LIFTED":
        state, dropped = lifted_product(spec.get("group", ()), spec.get("A"), spec.get("B"))
    elif name == "L-GROUP-ALGEBRA":
        state, dropped = two_block_code(spec.get("group", ()), spec.get("a"), spec.get("b"))
    elif name == "A-CONCAT":
        state, dropped = concatenate(_factor_state(spec.get("outer")),
                                     _factor_state(spec.get("inner")),
                                     spec.get("groups"), spec.get("representatives"))
    elif name == "L-BALANCED":
        state, dropped = balanced_product(spec.get("group", ()), spec.get("H1"),
                                          spec.get("action1"), spec.get("H2"),
                                          spec.get("action2"))
    elif name == "L-TANNER":
        state, dropped = tanner_code(spec.get("n"), spec.get("local_x"),
                                     spec.get("local_z"), spec.get("views_x"),
                                     spec.get("views_z"))
    elif name == "L-TILE":
        state, dropped = tile_assembly(spec.get("tiles"), spec.get("placements"),
                                       spec.get("identifications", ()),
                                       spec.get("removed", ()))
    elif name == "A-PRODUCT":
        state, dropped = css_tensor_product(_factor_state(spec.get("left")),
                                            _factor_state(spec.get("right")))
    elif name == "A-DOUBLE":
        state, dropped = double_cover(spec.get("state"), spec.get("wiring", {}),
                                      spec.get("conjugate", False))
    elif name == "L-NESTED-CSS":
        state, dropped = nested_css(spec.get("HX"), spec.get("HZ"))
    elif name == "L-MAPPING-CONE":
        state, dropped = mapping_cone(spec.get("d_a"), spec.get("d_b"),
                                     spec.get("f1"), spec.get("f0"))
    elif name == "L-EMPTY":
        state, dropped = empty_code(), 0
    elif name == "L-FREE":
        state, dropped = free_code(spec.get("qubits")), 0
    elif name == "A-PULLBACK":
        state, dropped = pullback_code(_factor_state(spec.get("left")),
                                       _factor_state(spec.get("right")),
                                       _factor_state(spec.get("interface")),
                                       spec.get("phi1"), spec.get("phi2"))
    elif name == "A-PUSHOUT":
        state, dropped = pushout_code(_factor_state(spec.get("left")),
                                      _factor_state(spec.get("right")),
                                      _factor_state(spec.get("subcode")),
                                      spec.get("psi1"), spec.get("psi2"))
    elif name == "L-PAIR-PARTITION":
        state, dropped = pair_partition_code(spec.get("p"),
                                             spec.get("blocks_x"),
                                             spec.get("blocks_z"),
                                             spec.get("pair_partition"))
    elif name == "PP-SCALE":
        state, dropped = pp_scale_code(_factor_state(spec.get("state")),
                                       spec.get("P"),
                                       spec.get("bundle"),
                                       spec.get("blocks_x"),
                                       spec.get("blocks_z"))

    else:
        raise Malformed("unknown constructor %r" % (name,))
    n = len(state.Q)
    k = n - rank([r.mask for r in state.sector_rows("X")]) \
        - rank([r.mask for r in state.sector_rows("Z")])
    result = {"constructor": name, "state": state, "n": n, "k": k, "dropped_rows": dropped}
    if any(key in spec for key in ("lower_bounds", "witnesses", "constructor_cell", "lift_witnesses")):
        merged_witnesses = None
        if spec.get("lift_witnesses"):
            if name == "L-HGP":
                lifted = lift_hgp_witnesses(spec.get("H1"), spec.get("H2"), state=state)
            elif name == "L-NESTED-CSS":
                lifted = lift_nested_witnesses(spec.get("HX"), spec.get("HZ"), state=state)
            elif name == "A-CONCAT":
                lifted = lift_concat_witnesses(
                    spec.get("outer"), spec.get("inner"), spec.get("groups"),
                    state=state, representatives=spec.get("representatives"))
            elif name == "A-PRODUCT":
                lifted = lift_product_witnesses(
                    spec.get("left"), spec.get("right"), state=state)
            elif name == "A-DOUBLE":
                lifted = lift_double_witnesses(
                    spec.get("state"), spec.get("wiring", {}),
                    conjugate=spec.get("conjugate", False), state=state)
            else:
                lifted = {"X": [], "Z": []}
            result["lifted_witnesses"] = lifted
            merged_witnesses = {"X": list(lifted["X"]), "Z": list(lifted["Z"])}
        if spec.get("witnesses") is not None:
            extra = spec["witnesses"]
            if not isinstance(extra, dict):
                raise Malformed("witnesses must be a dict keyed by 'X' and/or 'Z'")
            if merged_witnesses is None:
                merged_witnesses = {"X": [], "Z": []}
            for side in ("X", "Z"):
                merged_witnesses[side].extend(extra.get(side, ()))
        result["ledger"] = DistanceLedger.for_constructed(
            state,
            lower_bounds=spec.get("lower_bounds"),
            witnesses=merged_witnesses,
            constructor_cell=spec.get("constructor_cell"),
        )
    return result


def _reduced_row_bases(masks, n):
    """Canonical GF(2) row-echelon basis of ``masks`` over ``n`` qubits.

    The returned masks are reduced against each other, so a row space that is
    a direct sum over disjoint qubit sets yields basis rows each supported on
    a single block (the column ordering cannot be mixed by row operations).
    This is the consumer's copy of the verifier's RREF step; it decides no
    calculus claim, it only describes the display's block structure.
    """
    basis = []  # (pivot bit index, row mask)
    limit = (1 << n) - 1 if n else 0
    for raw in masks:
        row = raw & limit
        for pivot, existing in basis:
            if (row >> pivot) & 1:
                row ^= existing
        if not row:
            continue
        pivot = row.bit_length() - 1
        for i, (old_pivot, old_row) in enumerate(basis):
            if (old_row >> pivot) & 1:
                basis[i] = (old_pivot, old_row ^ row)
        basis.append((pivot, row))
    return [row for _, row in sorted(basis)]


def structural_profile(state):
    """Report whether ``state``'s stabilizer group splits into direct-sum blocks.

    Returns ``{"connected", "blocks", "block_sizes"}``.  ``blocks`` is the
    number of independent qubit blocks of the stabilizer GROUP, computed from
    the reduced row echelon form of each sector separately (both rows and
    qubits in the union-find, isolated qubits included).  This mirrors the
    challenge gate's ``prescreen.block_structure`` test that refuses a direct
    sum before the distance search; a constructed child that reports
    ``connected: false`` cannot be staged as a single submission.

    This is structural metadata about the display, not a distance, price, or
    soundness claim: it licenses nothing in the calculus (``spec/CLAIMS.md``).
    """
    if not isinstance(state, CodeState):
        raise Malformed("structural_profile needs a CodeState")
    qubits = sorted(state.Q)
    n = len(qubits)
    index = {q: i for i, q in enumerate(qubits)}
    parent = list(range(n))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for sector in ("X", "Z"):
        masks = []
        for row in state.sector_rows(sector):
            mask = 0
            for q in row.support:
                mask |= 1 << index[q]
            masks.append(mask)
        for mask in _reduced_row_bases(masks, n):
            support = [i for i in range(n) if (mask >> i) & 1]
            for q in support[1:]:
                parent[find(q)] = find(support[0])

    sizes = {}
    for i in range(n):
        root = find(i)
        sizes[root] = sizes.get(root, 0) + 1
    block_sizes = sorted(sizes.values(), reverse=True)
    return {"connected": len(block_sizes) == 1,
            "blocks": len(block_sizes),
            "block_sizes": block_sizes}


__all__ = [
    'ADMITTED_CONSTRUCTORS',
    'UNADMITTED_CONSTRUCTORS',
    '_binary_matrix',
    '_group',
    '_validate_cayley_table',
    '_group_spec',
    '_algebra_element',
    '_algebra_matrix',
    '_involution',
    '_lift_rows',
    '_left_lift_rows',
    '_right_lift_rows',
    '_retained_display',
    '_constructed_state',
    'lifted_product',
    'hypergraph_product',
    'hypergraph_parameters',
    'two_block_code',
    'concatenate',
    '_natural_rows_orthogonal',
    '_label_list',
    'css_tensor_product',
    'double_cover',
    '_permutation',
    '_group_action',
    '_nonabelian_group_action',
    '_orbits',
    'balanced_product',
    'tanner_code',
    'nested_css',
    'mapping_cone',
    'empty_code',
    'free_code',
    'pullback_code',
    'pushout_code',
    'pair_partition_code',
    'pp_scale_code',

    'tile_assembly',
    'lift_hgp_witnesses',
    'lift_nested_witnesses',
    'lift_concat_witnesses',
    'lift_product_witnesses',
    'lift_double_witnesses',
    '_factor_state',
    'construct',
    '_reduced_row_bases',
    'structural_profile',
]
