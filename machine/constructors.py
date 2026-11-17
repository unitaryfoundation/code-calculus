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
from machine.layout import *
from machine.tower_prices import *
from machine.intervals import *

ADMITTED_CONSTRUCTORS = ("L-HGP", "L-LIFTED", "L-GROUP-ALGEBRA", "A-CONCAT",
                         "L-BALANCED", "L-TANNER", "L-TILE", "A-PRODUCT",
                         "A-DOUBLE", "L-NESTED-CSS")

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

def _algebra_element(value, orders, name):
    """An element of F_2[G] as a frozenset of exponent tuples (terms cancel)."""
    if not isinstance(value, (list, tuple, set, frozenset)):
        raise Malformed("%s must be a list of group elements (exponent tuples)" % name)
    terms = set()
    for term in value:
        if isinstance(term, int) and not isinstance(term, bool) and len(orders) == 1:
            term = (term,)
        if not isinstance(term, (list, tuple)) or len(term) != len(orders):
            raise Malformed("%s terms must be exponent tuples of length %d" % (name, len(orders)))
        if any(isinstance(t, bool) or not isinstance(t, int) for t in term):
            raise Malformed("%s exponents must be integers" % name)
        key = tuple(t % o for t, o in zip(term, orders))
        if key in terms:
            terms.remove(key)
        else:
            terms.add(key)
    return frozenset(terms)

def _algebra_matrix(matrix, orders, name):
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
        out.append([_algebra_element(v, orders, "%s[%d][%d]" % (name, r, c))
                    for c, v in enumerate(row)])
    return out

def _involution(element, orders):
    """The algebra involution g -> -g, applied termwise."""
    return frozenset(tuple((-t) % o for t, o in zip(term, orders)) for term in element)

def _lift_rows(element, orders, elements, index):
    """The regular representation of an algebra element: row h of L(x) has a
    one at h' exactly when h - h' is a term of x. Returned as bit masks over
    the group index."""
    rows = []
    for h in elements:
        mask = 0
        for g in element:
            shifted = tuple((hi - gi) % o for hi, gi, o in zip(h, g, orders))
            mask |= 1 << index[shifted]
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

def _constructed_state(n, rows):
    """A presented state on labels 0..n-1 from (sector, mask) rows: the
    retained display with canonically minted identifiers, validated."""
    kept, dropped = _retained_display(rows)
    used = set()
    display = []
    for sector, mask in kept:
        identifier = CodeState._mint_identifier(used)
        used.add(identifier)
        support = tuple(q for q in range(n) if (mask >> q) & 1)
        display.append(Row(identifier, sector, support))
    state = CodeState(tuple(range(n)), tuple(display), frozenset(used))
    _validate_output(state)
    return state, dropped

def lifted_product(orders, A, B):
    """`L-LIFTED`: the lifted product of base matrices over F_2[G], G abelian.

    With ``A`` of shape m_A x n_A and ``B`` of shape m_B x n_B over the group
    algebra of the abelian group of the given cyclic ``orders``, the qubits
    are the left block (i, j, g) and the right block (a, b, g); the X-checks,
    indexed by (a, j, h), carry ``A[a][i]`` lifted on the left qubits (i, j)
    and ``B[b][j]^*`` lifted on the right qubits (a, b); the Z-checks, indexed
    by (i, b, h), carry ``B[b][j]`` on the left and ``A[a][i]^*`` on the
    right, where ``*`` is the involution g -> -g. Orthogonality is the
    commutativity of the group algebra (section 4.34). The trivial group
    gives the hypergraph product. Returns (state, dropped_rows).
    """
    orders, elements, index = _group(orders)
    A = _algebra_matrix(A, orders, "A")
    B = _algebra_matrix(B, orders, "B")
    ell = len(elements)
    m_a, n_a = len(A), len(A[0])
    m_b, n_b = len(B), len(B[0])
    left = n_a * n_b * ell
    n = left + m_a * m_b * ell

    def left_offset(i, j):
        return (i * n_b + j) * ell

    def right_offset(a, b):
        return left + (a * m_b + b) * ell

    lifts = {}

    def lift(element):
        if element not in lifts:
            lifts[element] = _lift_rows(element, orders, elements, index)
        return lifts[element]

    rows = []
    for a in range(m_a):
        for j in range(n_b):
            for h in range(ell):
                mask = 0
                for i in range(n_a):
                    mask |= lift(A[a][i])[h] << left_offset(i, j)
                for b in range(m_b):
                    mask |= lift(_involution(B[b][j], orders))[h] << right_offset(a, b)
                rows.append(("X", mask))
    for i in range(n_a):
        for b in range(m_b):
            for h in range(ell):
                mask = 0
                for j in range(n_b):
                    mask |= lift(B[b][j])[h] << left_offset(i, j)
                for a in range(m_a):
                    mask |= lift(_involution(A[a][i], orders))[h] << right_offset(a, b)
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

def two_block_code(orders, a, b):
    """`L-GROUP-ALGEBRA`: the two-block code of a, b in F_2[G], G abelian.

    H_X = [L(a) | L(b)] and H_Z = [L(b)^T | L(a)^T] over 2|G| qubits, with
    L the regular representation; the rows commute because the group algebra
    is commutative, and k = 2 (|G| - rank[L(a) | L(b)]) because the
    involution matches the two kernels (section 4.34). Equal, row for row,
    to the lifted product of the 1 x 1 base matrices (a) and (b^*).
    Returns (state, dropped_rows).
    """
    orders, elements, index = _group(orders)
    a = _algebra_element(a, orders, "a")
    b = _algebra_element(b, orders, "b")
    ell = len(elements)
    la = _lift_rows(a, orders, elements, index)
    lb = _lift_rows(b, orders, elements, index)
    lat = _lift_rows(_involution(a, orders), orders, elements, index)   # L(a)^T
    lbt = _lift_rows(_involution(b, orders), orders, elements, index)   # L(b)^T
    rows = [("X", la[h] | (lb[h] << ell)) for h in range(ell)]
    rows += [("Z", lbt[h] | (lat[h] << ell)) for h in range(ell)]
    return _constructed_state(2 * ell, rows)

def concatenate(outer, inner, groups, representatives=None):
    """`A-CONCAT`: the inner CSS code on every block of the outer CSS code.

    ``groups`` partitions the outer qubits into blocks of k_in labels, the
    position of a label in its block naming the inner logical it encodes.
    Block j carries a copy of the inner code on labels j n_in + (index of the
    inner label); each outer row is lifted block by block through the
    representatives (by default the dual logical bases of the inner level
    data, `tower_level_data`). Well-formedness, n = n_in n_out, and k = k_out
    are derived in `design/DERIVED_RELATIONS.md` section 2a and
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

def balanced_product(orders, H1, action1, H2, action2):
    """`L-BALANCED`: the balanced product of two binary matrices over a
    finite abelian group acting on their index sets.

    ``action1`` and ``action2`` are dicts with keys ``rows`` and ``cols``,
    each a list of one permutation per cyclic generator; ``H1`` and ``H2``
    must be equivariant (``H[rows_g(a)][cols_g(i)] == H[a][i]``). The output
    is the hypergraph-product complex of ``H1`` and ``H2`` modulo the
    relation (g x, y) ~ (x, g y): qubits, X-checks, and Z-checks are the
    orbits of (x, y) -> (g x, g^{-1} y) on the corresponding index pairs,
    and the check maps are the hypergraph-product maps descended to orbits
    (`spec/OPERATIONAL_SEMANTICS.md` section 4.35). The trivial group gives
    `L-HGP` row for row. Returns (state, dropped_rows).
    """
    orders, _elements, _index = _group(orders)
    H1 = _binary_matrix(H1, "H1")
    H2 = _binary_matrix(H2, "H2")
    m1, n1 = len(H1), len(H1[0])
    m2, n2 = len(H2), len(H2[0])
    actions = []
    for name, action, m, n, H in (("action1", action1, m1, n1, H1),
                                  ("action2", action2, m2, n2, H2)):
        if not isinstance(action, dict) or set(action) != {"rows", "cols"}:
            raise Malformed("%s must give row and column permutations" % name)
        rows = _group_action(orders, action["rows"], m, "%s rows" % name)
        cols = _group_action(orders, action["cols"], n, "%s cols" % name)
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
    Returns a dict with the state, the
    constructor, n, k, and the number of natural rows the retained display
    dropped. A failed applicability premise raises ``NoDerivation``.
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
    else:
        raise Malformed("unknown constructor %r" % (name,))
    n = len(state.Q)
    k = n - rank([r.mask for r in state.sector_rows("X")]) \
        - rank([r.mask for r in state.sector_rows("Z")])
    return {"constructor": name, "state": state, "n": n, "k": k, "dropped_rows": dropped}


__all__ = [
    'ADMITTED_CONSTRUCTORS',
    'UNADMITTED_CONSTRUCTORS',
    '_binary_matrix',
    '_group',
    '_algebra_element',
    '_algebra_matrix',
    '_involution',
    '_lift_rows',
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
    '_orbits',
    'balanced_product',
    'tanner_code',
    'nested_css',
    'tile_assembly',
    '_factor_state',
    'construct',
]
