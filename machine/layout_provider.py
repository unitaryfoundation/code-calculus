"""Consumer-side layout provider: synthesize an honest 2D layout (issue #666).

The constructor cells of ``spec/JUDGMENT_LAYER.md`` §2d.5 (``L-HGP``,
``L-LIFTED``, ``L-BALANCED``, ``L-TANNER``, ``L-PAIR-PARTITION``, ...) carry the
interaction radius only under a *supplied* honest layout, and the binary cells
(``C-DIRECT-SUM``, ``E-GLUE``) need a supplied merged layout. This module
supplies one. It is **ledger-side tooling**: it reads a state's displayed rows
and returns a layout beside the state. It never builds, alters, or compares
states -- ``C = (Q, X, Z, pres, used)`` and ``≡`` are untouched -- and a
synthesized layout enters every cell exactly as a hand-supplied one would,
through the same exact honesty check (``machine.layout.layout_is_honest``).

The pipeline follows the three stages that He & Brun, *Constructively
Embedding Quantum Error-Correcting Codes* (arXiv:2611.33389v1, as cited in
issue #666), describe for Tanner-graph embedding:

1. **Continuous embedding** of the displayed Tanner graph's qubits in the
   plane: spectral embedding (the two lowest non-trivial eigenvectors of the
   qubit graph's Laplacian) or classical multidimensional scaling of the
   Tanner-graph shortest-path distances.
2. **Grid assignment** onto integer sites of a rectilinear grid, at most
   ``layers`` qubits per site, by a rank-preserving column/row packing.
3. **Refinement** by deterministic first-improvement moves and swaps that
   lower ``(r^2, sum of squared row diameters)``.

Path routing (the paper's third stage) is not implemented. The provider
reports a rectilinear **total grid distance** ``W`` as auxiliary metadata,
defined here as the sum over displayed rows of the L1 distance from each
support qubit to the row's coordinate-wise lower median (the L1-optimal star
centre for that row's ancilla, with ancilla site occupancy ignored). It is
this repository's definition and is not claimed to coincide with the paper's.

What is and is not claimed. The returned layout is a *witness*: its honesty,
planarity, radius and ``W`` are recomputed exactly from integer coordinates.
Nothing is claimed about optimality -- a smaller radius may exist for the same
code -- and the radius is a property of the pair (state, layout), never of the
state alone (``spec/VOCABULARY.md``, *interaction radius*). The procedure is
deterministic: the same display and parameters give the same layout.
"""

import argparse
import copy
import json
import math
import random
from collections import Counter, deque
from fractions import Fraction

from machine.layout import (
    interaction_radius_squared,
    layout_is_honest,
    locality_class,
    radius_nearest_decimal,
)
from machine.state import CodeState

PROVIDER_NAME = "machine.layout_provider"
PROVIDER_SOURCE = (
    "issue #666; three-stage embedding after He & Brun, arXiv:2611.33389v1 "
    "(as cited in the issue): continuous embedding, grid assignment, "
    "refinement; path routing not implemented")
METHODS = ("spectral", "mds")

# Lanczos steps used for an embedding; the Ritz pairs of the smallest (or
# largest) eigenvalues converge first, so far fewer steps than ``n`` suffice
# for a layout seed. The value only affects the seed, never a verdict.
LANCZOS_STEPS = 80


# ---------------------------------------------------------------------------
# The displayed Tanner graph
# ---------------------------------------------------------------------------

def _supports(state):
    return [tuple(row.support) for row in state.rows]


def qubit_graph(state):
    """The qubit adjacency of the displayed Tanner graph, with multiplicities.

    Two qubits are adjacent when some displayed row contains both; the weight
    counts those rows. Returns ``{q: {p: weight}}`` over ``state.Q``.
    """
    graph = {q: {} for q in state.Q}
    for support in _supports(state):
        for index, left in enumerate(support):
            for right in support[index + 1:]:
                graph[left][right] = graph[left].get(right, 0) + 1
                graph[right][left] = graph[right].get(left, 0) + 1
    return graph


def tanner_distances(state):
    """Shortest-path distances between qubits in the displayed Tanner graph.

    The Tanner graph is bipartite (qubits and displayed rows), so the distance
    between two qubits is twice the number of rows on a shortest path. Pairs
    in different components get one more than the largest finite distance,
    so that classical MDS sees a finite, separated metric.
    """
    qubits = list(state.Q)
    graph = qubit_graph(state)
    finite = {}
    largest = 0
    for source in qubits:
        seen = {source: 0}
        queue = deque([source])
        while queue:
            node = queue.popleft()
            for neighbour in graph[node]:
                if neighbour not in seen:
                    seen[neighbour] = seen[node] + 2
                    queue.append(neighbour)
        finite[source] = seen
        largest = max([largest] + list(seen.values()))
    gap = largest + 2
    return [[finite[a].get(b, gap) for b in qubits] for a in qubits]


# ---------------------------------------------------------------------------
# Stage 1: continuous embedding (pure Python, deterministic)
# ---------------------------------------------------------------------------

def _dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def _jacobi_eigen(matrix):
    """Eigenpairs of a small symmetric matrix by cyclic Jacobi rotations."""
    size = len(matrix)
    a = [list(row) for row in matrix]
    v = [[1.0 if i == j else 0.0 for j in range(size)] for i in range(size)]
    for _ in range(100):
        off = sum(a[i][j] ** 2 for i in range(size) for j in range(size) if i != j)
        if off < 1e-22:
            break
        for p in range(size):
            for q in range(p + 1, size):
                if abs(a[p][q]) < 1e-300:
                    continue
                theta = (a[q][q] - a[p][p]) / (2 * a[p][q])
                t = math.copysign(1.0, theta) / (abs(theta) + math.sqrt(theta * theta + 1))
                c = 1 / math.sqrt(t * t + 1)
                s = t * c
                for k in range(size):
                    akp, akq = a[k][p], a[k][q]
                    a[k][p] = c * akp - s * akq
                    a[k][q] = s * akp + c * akq
                for k in range(size):
                    apk, aqk = a[p][k], a[q][k]
                    a[p][k] = c * apk - s * aqk
                    a[q][k] = s * apk + c * aqk
                for k in range(size):
                    vkp, vkq = v[k][p], v[k][q]
                    v[k][p] = c * vkp - s * vkq
                    v[k][q] = s * vkp + c * vkq
    values = [a[i][i] for i in range(size)]
    vectors = [[v[k][i] for k in range(size)] for i in range(size)]
    return values, vectors


def _lanczos_extreme(matvec, size, count, *, largest, deflate_constant):
    """``count`` extreme eigenvectors of a symmetric operator, by Lanczos.

    Full reorthogonalization keeps the basis orthonormal. With
    ``deflate_constant`` the all-ones direction is projected out throughout
    (the Laplacian's trivial eigenvector, or MDS's double-centring kernel).
    Fewer than ``count`` vectors are returned when the reachable subspace is
    smaller. The start vector comes from a fixed seed, so the result is
    deterministic.
    """
    if size == 0:
        return []
    constant = [1 / math.sqrt(size)] * size if deflate_constant else None

    def orthogonalize(vector, basis):
        for _ in range(2):
            if constant is not None:
                shift = _dot(vector, constant)
                vector = [x - shift * c for x, c in zip(vector, constant)]
            for b in basis:
                shift = _dot(vector, b)
                vector = [x - shift * y for x, y in zip(vector, b)]
        return vector

    generator = random.Random(666)
    start = orthogonalize([generator.uniform(-1, 1) for _ in range(size)], [])
    norm = math.sqrt(_dot(start, start))
    if norm < 1e-12:
        return []
    basis = [[x / norm for x in start]]
    alphas, betas = [], []
    steps = min(LANCZOS_STEPS, size)
    while True:
        current = basis[-1]
        image = matvec(current)
        alphas.append(_dot(image, current))
        image = orthogonalize(image, basis)
        beta = math.sqrt(_dot(image, image))
        if len(basis) >= steps or beta < 1e-10:
            break
        betas.append(beta)
        basis.append([x / beta for x in image])
    m = len(basis)
    tridiagonal = [[0.0] * m for _ in range(m)]
    for i in range(m):
        tridiagonal[i][i] = alphas[i]
        if i + 1 < m:
            tridiagonal[i][i + 1] = tridiagonal[i + 1][i] = betas[i]
    values, vectors = _jacobi_eigen(tridiagonal)
    order = sorted(range(m), key=lambda i: (-values[i] if largest else values[i], i))
    result = []
    for index in order[:count]:
        coefficients = vectors[index]
        ritz = [sum(coefficients[j] * basis[j][i] for j in range(m)) for i in range(size)]
        result.append((values[index], ritz))
    return result


def spectral_embedding(state):
    """Planar seed from the qubit graph's two lowest non-trivial Laplacian modes.

    Returns ``{q: (x, y)}`` floats. A missing mode (tiny or edgeless graphs)
    is read as a zero coordinate; the grid assignment breaks every tie by
    label, so the seed only orders qubits.
    """
    qubits = list(state.Q)
    index = {q: i for i, q in enumerate(qubits)}
    graph = qubit_graph(state)
    neighbours = [[(index[p], w) for p, w in sorted(graph[q].items())] for q in qubits]
    degree = [sum(w for _, w in row) for row in neighbours]

    def laplacian(vector):
        return [degree[i] * vector[i] - sum(w * vector[j] for j, w in neighbours[i])
                for i in range(len(qubits))]

    modes = _lanczos_extreme(laplacian, len(qubits), 2, largest=False,
                             deflate_constant=True)
    return _seed_from_modes(qubits, modes)


def mds_embedding(state):
    """Planar seed by classical MDS of the Tanner-graph qubit distances.

    Classical (Torgerson) scaling: the two leading eigenvectors of
    ``B = -1/2 J D^2 J``, each scaled by the square root of its eigenvalue.
    Dense, so ``O(n^2)`` per Lanczos step; prefer ``spectral`` for large codes.
    """
    qubits = list(state.Q)
    size = len(qubits)
    distances = tanner_distances(state)
    squared = [[float(d * d) for d in row] for row in distances]
    row_mean = [sum(row) / size for row in squared] if size else []
    total_mean = sum(row_mean) / size if size else 0.0
    gram = [[-0.5 * (squared[i][j] - row_mean[i] - row_mean[j] + total_mean)
             for j in range(size)] for i in range(size)]

    def apply(vector):
        return [_dot(row, vector) for row in gram]

    modes = _lanczos_extreme(apply, size, 2, largest=True, deflate_constant=True)
    scaled = [(value, [x * math.sqrt(max(value, 0.0)) for x in vector])
              for value, vector in modes]
    return _seed_from_modes(qubits, scaled)


def _seed_from_modes(qubits, modes):
    columns = [vector for _, vector in modes]
    while len(columns) < 2:
        columns.append([0.0] * len(qubits))
    # Fix each mode's sign so that the result does not depend on the sign the
    # eigensolver happened to return: the first non-negligible entry is positive.
    fixed = []
    for column in columns:
        lead = next((x for x in column if abs(x) > 1e-9), 1.0)
        fixed.append([x if lead > 0 else -x for x in column])
    return {q: (fixed[0][i], fixed[1][i]) for i, q in enumerate(qubits)}


# ---------------------------------------------------------------------------
# Stage 2: grid assignment
# ---------------------------------------------------------------------------

def grid_side(n, layers, slack=1):
    """Side of the square grid: the least side whose capacity holds ``n``, plus slack."""
    if n == 0:
        return 0
    sites = -(-n // layers)
    return math.isqrt(sites - 1) + 1 + slack


def grid_assignment(seed, layers, side):
    """Pack a continuous seed onto a ``side x side`` grid, at most ``layers`` per site.

    Rank-preserving: qubits are sorted by ``x`` (ties by ``y``, then label)
    into ``side`` columns of near-equal size, and each column is sorted by
    ``y`` and spread over the ``side`` rows. A column holds at most
    ``ceil(n / side) <= side * layers`` qubits, and a row of a column at most
    ``ceil(k / side) <= layers``, so the packing respects the occupancy cap
    by construction. Returns ``{q: (column, row)}`` integer sites.
    """
    qubits = sorted(seed, key=lambda q: (seed[q][0], seed[q][1], q))
    n = len(qubits)
    if n == 0:
        return {}
    if n > side * side * layers:
        raise ValueError("grid of side %d cannot hold %d qubits at %d per site"
                         % (side, n, layers))
    sites = {}
    for column in range(side):
        chunk = qubits[column * n // side:(column + 1) * n // side]
        chunk.sort(key=lambda q: (seed[q][1], seed[q][0], q))
        k = len(chunk)
        for t, q in enumerate(chunk):
            sites[q] = (column, t * side // k)
    return sites


# ---------------------------------------------------------------------------
# Stage 3: refinement
# ---------------------------------------------------------------------------

def _diameter_squared_int(sites, support):
    widest = 0
    points = [sites[q] for q in support]
    for i, (x1, y1) in enumerate(points):
        for x2, y2 in points[i + 1:]:
            span = (x1 - x2) ** 2 + (y1 - y2) ** 2
            if span > widest:
                widest = span
    return widest


def refine(state, sites, layers, side, *, passes=4, window=2):
    """Deterministic first-improvement refinement of a grid assignment.

    The objective is the pair ``(r^2, sum of squared row diameters)``,
    compared lexicographically and computed exactly on integer sites. A
    qubit is offered every site within Chebyshev distance ``window`` of the
    rounded centroid of its row-neighbours; it moves there when the site has
    room, or swaps with an occupant otherwise, whenever the objective strictly
    drops. Occupancy never exceeds ``layers``. Stops after ``passes`` passes
    or at the first pass with no improvement. Returns the new sites.
    """
    sites = dict(sites)
    supports = _supports(state)
    rows_of = {q: [] for q in state.Q}
    for index, support in enumerate(supports):
        for q in support:
            rows_of[q].append(index)
    graph = qubit_graph(state)
    diameters = [_diameter_squared_int(sites, s) for s in supports]
    histogram = Counter(diameters)
    total = sum(diameters)
    occupants = {}
    for q, site in sites.items():
        occupants.setdefault(site, []).append(q)

    def objective(hist, tot):
        return (max(hist) if hist else 0, tot)

    def trial(moved):
        """Objective after applying ``moved`` ({q: new site}), and the changes."""
        affected = sorted({r for q in moved for r in rows_of[q]})
        old = {q: sites[q] for q in moved}
        sites.update(moved)
        fresh = {r: _diameter_squared_int(sites, supports[r]) for r in affected}
        sites.update(old)
        hist = histogram.copy()
        tot = total
        for r, value in fresh.items():
            hist[diameters[r]] -= 1
            if hist[diameters[r]] == 0:
                del hist[diameters[r]]
            hist[value] += 1
            tot += value - diameters[r]
        return objective(hist, tot), fresh, hist, tot

    for _ in range(passes):
        improved = False
        for q in sorted(state.Q):
            if not graph[q]:
                continue
            here = objective(histogram, total)
            cx = round(sum(sites[p][0] for p in graph[q]) / len(graph[q]))
            cy = round(sum(sites[p][1] for p in graph[q]) / len(graph[q]))
            candidates = sorted(
                (x, y)
                for x in range(max(0, cx - window), min(side, cx + window + 1))
                for y in range(max(0, cy - window), min(side, cy + window + 1))
                if (x, y) != sites[q])
            for target in candidates:
                residents = occupants.get(target, [])
                options = []
                if len(residents) < layers:
                    options.append({q: target})
                options.extend({q: target, other: sites[q]} for other in sorted(residents))
                accepted = None
                for moved in options:
                    score, fresh, hist, tot = trial(moved)
                    if score < here:
                        accepted = (moved, fresh, hist, tot)
                        break
                if accepted is None:
                    continue
                moved, fresh, hist, tot = accepted
                for p, site in moved.items():
                    occupants[sites[p]].remove(p)
                    if not occupants[sites[p]]:
                        del occupants[sites[p]]
                for p, site in moved.items():
                    sites[p] = site
                    occupants.setdefault(site, []).append(p)
                for r, value in fresh.items():
                    diameters[r] = value
                histogram, total = hist, tot
                improved = True
                break
        if not improved:
            break
    return sites


# ---------------------------------------------------------------------------
# Metrics and the provider entry point
# ---------------------------------------------------------------------------

def total_grid_distance(state, sites):
    """Rectilinear total grid distance ``W`` of a layout (this module's definition).

    For each displayed row, the L1 distance from every support qubit to the
    row's coordinate-wise lower median, summed over rows. The lower median of
    integers is an integer site and minimizes the L1 star length, so ``W`` is
    the least total rectilinear wire length with one ancilla per row placed on
    the grid, ignoring ancilla site occupancy. Exact for integer sites.
    """
    total = 0
    for support in _supports(state):
        if not support:
            continue
        xs = sorted(sites[q][0] for q in support)
        ys = sorted(sites[q][1] for q in support)
        mx, my = xs[(len(xs) - 1) // 2], ys[(len(ys) - 1) // 2]
        total += sum(abs(sites[q][0] - mx) + abs(sites[q][1] - my) for q in support)
    return total


def provide_layout(state, *, layers=1, method="spectral", slack=1, passes=4, window=2):
    """Synthesize an honest planar layout for ``state``.

    Returns a dict with ``qubits`` (``state.Q``), ``coordinates`` (integer
    ``[x, y]`` per qubit, in ``state.Q`` order), ``layers``, ``provenance``
    and exact ``metrics``. The layout is checked with
    ``machine.layout.layout_is_honest`` before it is returned; a failure is
    an internal error, never a silently dishonest layout.
    """
    if isinstance(layers, bool) or not isinstance(layers, int) or layers < 1:
        raise ValueError("layers must be a positive integer")
    if method not in METHODS:
        raise ValueError("method must be one of %s" % ", ".join(METHODS))
    if isinstance(slack, bool) or not isinstance(slack, int) or slack < 0:
        raise ValueError("slack must be a nonnegative integer")
    state.validate()
    n = state.n()
    seed = spectral_embedding(state) if method == "spectral" else mds_embedding(state)
    side = grid_side(n, layers, slack)
    sites = grid_assignment(seed, layers, side)
    if passes:
        sites = refine(state, sites, layers, side, passes=passes, window=window)
    coordinates = [list(sites[q]) for q in state.Q]
    if not layout_is_honest(coordinates, layers):
        raise AssertionError("layout provider produced a dishonest layout")
    index = {q: i for i, q in enumerate(state.Q)}
    radius_squared = interaction_radius_squared(
        coordinates, [[index[q] for q in s] for s in _supports(state)])
    occupancy = Counter(map(tuple, coordinates))
    return {
        "qubits": list(state.Q),
        "coordinates": coordinates,
        "layers": layers,
        "provenance": {
            "provider": PROVIDER_NAME,
            "source": PROVIDER_SOURCE,
            "method": method,
            "grid": [side, side],
            "slack": slack,
            "passes": passes,
            "window": window,
            "claim": ("witness layout: honesty, planarity, radius and W are "
                      "exact for these coordinates; no optimality is claimed"),
        },
        "metrics": {
            "interaction_radius_squared": str(radius_squared),
            "interaction_radius": radius_nearest_decimal(Fraction(radius_squared), 6),
            "locality_class": locality_class(radius_squared, layers),
            "total_grid_distance": total_grid_distance(state, sites),
            "max_site_occupancy": max(occupancy.values()) if occupancy else 0,
            "honest": True,
            "planar": True,
        },
    }


def locality_block(provided, contributed_by=None):
    """The ``locality`` block of a challenge document for a provided layout.

    The challenge format indexes coordinates by qubit label ``0..n-1``, so
    this needs ``qubits == list(range(n))``; any other namespace is refused
    rather than padded, since padding would add sites the code does not have.

    The challenge's ``contributed_by`` credits people (``@handles`` and a
    date), so the provider never writes one on its own: pass
    ``contributed_by`` to credit whoever ran it. The provider's provenance
    stays in ``provided["provenance"]``, beside the ledger.
    """
    qubits = provided["qubits"]
    if qubits != list(range(len(qubits))):
        raise ValueError("a locality block needs the qubit namespace 0..n-1")
    block = {
        "coordinates": copy.deepcopy(provided["coordinates"]),
        "layers": provided["layers"],
    }
    if contributed_by is not None:
        block["contributed_by"] = copy.deepcopy(contributed_by)
    return block


def attach_layout(document, *, replace=False, contributed_by=None, **options):
    """A copy of a challenge document with a synthesized ``locality`` block.

    A document that already carries a layout keeps it unless ``replace`` is
    set: a supplied layout (for instance a hardware placement) is the
    consumer's input, and a synthesized one never silently overrides it.
    Returns ``(document, provided)``.
    """
    if isinstance(document.get("locality"), dict) and not replace:
        raise ValueError("document already carries a layout; pass replace=True")
    state = CodeState.from_challenge(document)
    provided = provide_layout(state, **options)
    result = copy.deepcopy(document)
    result["locality"] = locality_block(provided, contributed_by)
    return result, provided


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("document", help="qLDPC challenge JSON file")
    parser.add_argument("output", help="path for the document with a synthesized layout")
    parser.add_argument("--layers", type=int, default=1)
    parser.add_argument("--method", choices=METHODS, default="spectral")
    parser.add_argument("--slack", type=int, default=1)
    parser.add_argument("--passes", type=int, default=4)
    parser.add_argument("--replace", action="store_true",
                        help="replace an existing locality block")
    args = parser.parse_args(argv)
    with open(args.document) as source:
        document = json.load(source)
    result, provided = attach_layout(
        document, replace=args.replace, layers=args.layers, method=args.method,
        slack=args.slack, passes=args.passes)
    with open(args.output, "w") as target:
        json.dump(result, target, indent=2)
        target.write("\n")
    print(json.dumps({"provenance": provided["provenance"],
                      "metrics": provided["metrics"]}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
