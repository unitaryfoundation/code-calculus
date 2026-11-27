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

from machine.state import *

def _exact_coordinate(value):
    """The exact rational value of one layout coordinate.

    A ``Fraction`` passes through, an ``int`` is exact, a ``float`` is read
    at its exact binary value, and a string or ``Decimal`` is read at its
    exact decimal value.
    """
    if isinstance(value, Fraction):
        return value
    if isinstance(value, str):
        return Fraction(Decimal(value))
    return Fraction(value)

def _squared_distance(a, b):
    """Exact squared Euclidean distance between two layout points."""
    return sum((x - y) ** 2 for x, y in zip(a, b))

def _diameter_squared(coordinates, support):
    """Largest squared distance between two points of a check's support."""
    points = [tuple(_exact_coordinate(value) for value in coordinates[q])
              for q in support]
    widest = Fraction(0)
    for index, left in enumerate(points):
        for right in points[index + 1:]:
            span = _squared_distance(left, right)
            if span > widest:
                widest = span
    return widest

def interaction_radius_squared(coordinates, supports):
    """The exact maximum squared Euclidean diameter over a set of supports.

    The interaction radius is the square root of this quantity, and every
    comparison against a cap is made on the squared values
    (``r <= c`` iff ``r*r <= c*c`` for ``c >= 0``), so no square root is
    ever taken for a verdict. ``coordinates`` is a list indexed the same way
    as the qubit indices in ``supports``. Exactly computable: no search is
    involved, and nothing is trusted.
    """
    widest = Fraction(0)
    for support in supports:
        span = _diameter_squared(coordinates, support)
        if span > widest:
            widest = span
    return widest

def radius_decimal(squared, decimals):
    """The decimal round-up of the radius, computed exactly.

    ``squared`` is the exact maximum squared diameter. The result is the
    float nearest to the least decimal ``k / 10**decimals`` that is at
    least the exact radius ``sqrt(squared)``, where ``k`` is computed by
    integer arithmetic on the rational squared value. The *decimal* is an
    upper bound on the real radius -- not on a floating-point measurement
    of it -- and the verifier parses the same decimal, so the claim and the
    entry cannot drift apart. The float nearest that decimal can sit one
    ulp below it; no comparison in this module reads the float.
    """
    if squared <= 0:
        return 0.0
    numerator = squared.numerator * 10 ** (2 * decimals)
    denominator = squared.denominator
    # The least integer k with k*k >= numerator/denominator is
    # isqrt((numerator - 1) // denominator) + 1.
    k = math.isqrt((numerator - 1) // denominator) + 1
    return k / 10 ** decimals

def radius_nearest_decimal(squared, decimals):
    """A decimal nearest-rounding of the radius, computed exactly.

    ``squared`` is the exact maximum squared diameter. The result is the
    nearest decimal ``k / 10**decimals`` to the exact radius
    ``sqrt(squared)`` (ties round up), computed by integer arithmetic on the
    rational squared value. This is a display convention only: no comparison
    reads it. The exported claim uses ``radius_decimal``, which rounds up
    so that it bounds the real value.
    """
    if squared <= 0:
        return 0.0
    numerator = squared.numerator * 10 ** (2 * decimals)
    denominator = squared.denominator
    # floor(sqrt(numerator/denominator)) == isqrt(numerator // denominator).
    k = math.isqrt(numerator // denominator)
    # Nearest rounding, ties round up: round up when the squared radius is
    # at least (k + 1/2)^2 in units of 1/10**decimals, i.e.
    # 4 * numerator >= (4*k*k + 4*k + 1) * denominator.
    if 4 * numerator >= (4 * k * k + 4 * k + 1) * denominator:
        k += 1
    return k / 10 ** decimals

def _radius_claim(squared):
    """Round the exact radius *up* to four decimals, for the qLDPC claim.

    The claim is an upper bound on the exact radius, and the qLDPC verifier
    compares the claim against the radius at full precision, so rounding
    down could reject an honest entry. Because the round-up is computed on
    the exact squared diameter (see ``radius_decimal``), it bounds the real
    value and not merely a floating-point measurement of it.
    """
    return radius_decimal(squared, 4)

def child_layout(parent, state):
    """The child's layout: the parent's layout restricted to the surviving qubits.

    Every transition either preserves the qubit namespace (`C-SKIP`,
    `C-DELETE-CHECK`, `C-ADD-CHECK`) or removes one qubit from it
    (`E-GRAFT`), and the state keeps the parent's qubit labels, so the
    child's coordinates are the parent's coordinates read at the child's
    qubits. Returns ``None`` when the parent carries no usable layout.
    """
    locality = parent.get("locality")
    if not isinstance(locality, dict):
        return None
    coordinates = locality.get("coordinates")
    if not isinstance(coordinates, list) or len(coordinates) != parent["n"]:
        return None
    for qubit in state.Q:
        if qubit >= len(coordinates):
            return None
    child = {"coordinates": [[_coordinate_to_number(value) for value in coordinates[qubit]]
                            for qubit in state.Q]}
    layers = locality.get("layers")
    if isinstance(layers, int):
        child["layers"] = layers
    modules = locality.get("modules")
    if isinstance(modules, list) and len(modules) == parent["n"]:
        child["modules"] = [modules[qubit] for qubit in state.Q]
    if "contributed_by" in locality:
        child["contributed_by"] = copy.deepcopy(locality["contributed_by"])
    return child

def radius_squared_in_layout(parent, state):
    """The squared interaction radius of a state in the parent's layout, or None.

    The state's rows carry the parent's qubit labels and the parent's
    coordinates are indexed the same way, so the two can be read against
    each other directly -- before and after a transition alike. As in
    `child_layout`, a state whose qubits fall outside the parent's layout has
    no radius here, rather than an out-of-range read. The exact squared
    value is returned so callers can compare against caps without a square
    root.
    """
    locality = parent.get("locality")
    if not isinstance(locality, dict):
        return None
    coordinates = locality.get("coordinates")
    if not isinstance(coordinates, list) or len(coordinates) != parent["n"]:
        return None
    for qubit in state.Q:
        if qubit >= len(coordinates):
            return None
    return interaction_radius_squared(coordinates, [row.support for row in state.rows])

LOCALITY_CLASS_CAPS = (
    (1, 4.0, "local-2d-single"),
    (2, 7.0, "local-2d-bilayer"),
)

def _coordinate_to_number(value):
    """Convert a layout coordinate to an int or float when it is textual."""
    if isinstance(value, bool):
        return value
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        return value
    if isinstance(value, str):
        text = value.strip()
        try:
            if "." in text or "e" in text.lower():
                return float(text)
            return int(text)
        except ValueError:
            return value
    return value

def layout_is_honest(coordinates, layers):
    """Whether a coordinate list is honest (spec/JUDGMENT_LAYER.md section 2d.3).

    A layout is honest when at most ``layers`` qubits share a site and
    distinct sites are at least 1 apart. Both conditions are decided
    exactly: the coordinates are read as exact rationals
    (`_exact_coordinate`) and the spacing condition is the squared-distance
    comparison ``|p - q|^2 >= 1``, so no verdict depends on a square root or
    a tolerance. A point that is not a coordinate list, or a layer count that
    is not a positive integer, makes the layout dishonest rather than raising.
    """
    if isinstance(layers, bool) or not isinstance(layers, int) or layers < 1:
        return False
    occupancy = {}
    for point in coordinates:
        if not isinstance(point, (list, tuple)):
            return False
        try:
            site = tuple(_exact_coordinate(value) for value in point)
        except (TypeError, ValueError, ArithmeticError):
            return False
        occupancy[site] = occupancy.get(site, 0) + 1
    if any(count > layers for count in occupancy.values()):
        return False
    sites = list(occupancy)
    for index, left in enumerate(sites):
        for right in sites[index + 1:]:
            if len(left) != len(right) or _squared_distance(left, right) < 1:
                return False
    return True

def layout_honest(parent):
    """Whether the parent's layout satisfies the honesty requirements (2d.3).

    A document without a layout is vacuously honest: there is nothing to be
    dishonest about, and no class is assigned without a radius. Otherwise the
    verdict is `layout_is_honest` at the document's layer count, read as
    `layout_layers` reads it; an invalid layer count gives no class, and the
    layout is reported dishonest.

    Until 2026-11-10 this function only required the sites to be distinct,
    which read a two-layer layout with two qubits on one site as dishonest
    and a pair of sites closer than 1 as honest; both disagreed with section
    2d.3, and the transcription was fixed to the prose.
    """
    locality = parent.get("locality") if isinstance(parent, dict) else None
    if not isinstance(locality, dict):
        return True
    coordinates = locality.get("coordinates")
    if not isinstance(coordinates, list):
        return True
    layers = layout_layers(parent)
    if layers is None:
        return False
    return layout_is_honest(coordinates, layers)

def layout_planar(parent):
    """Whether the parent's layout is two-dimensional (2d.4)."""
    locality = parent.get("locality") if isinstance(parent, dict) else None
    if not isinstance(locality, dict):
        return True
    coordinates = locality.get("coordinates")
    if not isinstance(coordinates, list):
        return True
    for point in coordinates:
        if not isinstance(point, (list, tuple)) or len(point) > 2:
            return False
    return True

def locality_class(radius_squared, layers, *, planar=True, honest=True):
    """The consumer's locality class for a squared radius and a layer count.

    The tightest class the caps admit; `unrestricted` otherwise, and also
    for a state with no layout at all. The classes nest by radius, not by
    layer count: a code qualifies for every class whose layer cap and radius
    cap it satisfies, and the caps are checked tightest first.

    The comparison is exact: the squared radius is compared against the
    squared cap (``r <= c`` iff ``r*r <= c*c`` for ``c >= 0``), so neither a
    square root nor a tolerance is involved
    (spec/JUDGMENT_LAYER.md section 2d.1, 2026-10-25).

    The class is assigned only when the layout is planar and honest
    (section 2d.3-2d.4); otherwise the verdict is `unrestricted`.
    """
    if radius_squared is None or layers is None or not planar or not honest:
        return "unrestricted"
    for max_layers, cap, name in LOCALITY_CLASS_CAPS:
        if layers <= max_layers and radius_squared <= cap * cap:
            return name
    return "unrestricted"

def layout_layers(parent):
    """The parent's layer count, or 1 when it states none.

    A boolean or non-positive layer count is not a valid layer count, so it
    yields ``None`` and the layout receives no locality class.
    """
    locality = parent.get("locality")
    if not isinstance(locality, dict):
        return 1
    layers = locality.get("layers")
    if isinstance(layers, bool) or not isinstance(layers, int) or layers <= 0:
        return None
    return layers

def export_challenge_entry(parent, state, ledger, name, construction, date,
                          trials=None, witness_trials=None, certified=False,
                          exact=False, oracle=False, seeds=None, depths=None,
                          staged=False, layout_aware=False, **kwargs):
    """Export only witness-backed upper bounds; interval lower bounds stay local."""
    relabel = {q: index for index, q in enumerate(state.Q)}
    # Issue #455: support search is mandatory before export. If the ledger
    # carries no valid witness for a side, run a bounded search first; only
    # raise if the search still finds nothing.
    missing_sides = [side for side in ("X", "Z")
                     if not ledger._valid_witnesses(state, side)]
    search_error = None
    if missing_sides:
        try:
            from machine.planner import (tighten_ledger_with_search,
                                          MINIMUM_SUPPORT_SEARCH_BUDGET)
            ledger, _ = tighten_ledger_with_search(
                state, ledger, sectors=tuple(missing_sides),
                max_weight=None,
                budget=max(MINIMUM_SUPPORT_SEARCH_BUDGET, 4096))
        except Exception as exc:  # noqa: BLE001 - export must not crash on a
            # contradicted/failed search; the missing witness is reported below.
            search_error = repr(exc)
    side_witnesses = {}
    for side in ("X", "Z"):
        valid = ledger._valid_witnesses(state, side)
        if not valid:
            raise ValueError("qLDPC export needs a current %s logical witness" % side)
        best = min(valid, key=lambda witness: witness["value"])
        _trials = trials if trials is not None else witness_trials
        _confidence = "upper_bound"
        if _trials is not None:
            from machine.entrypoints import witness_confidence as _witness_confidence
            _confidence = "%s (%s)" % (_confidence, _witness_confidence(_trials))
        side_witnesses[side] = {
            "value": best["value"],
            "confidence": _confidence,
            "witness": [relabel[q] for q in best["support"]],
        }
        if _trials is not None:
            side_witnesses[side]["trials"] = _trials
            side_witnesses[side]["witness_confidence"] = _witness_confidence(_trials)
    _exported_d = min(side_witnesses["X"]["value"], side_witnesses["Z"]["value"])
    _child_params = "[[%d,%d,%d]]" % (state.n(), state.k(), _exported_d)
    if isinstance(name, str):
        _stripped = re.sub(r"^\s*\[\[\s*\d+\s*,\s*\d+\s*,\s*\d+\s*\]\]\s*", "", name)
        name = ("%s %s" % (_child_params, _stripped)).strip() if _stripped else _child_params
    else:
        name = _child_params
    exported = {
        "schema_version": "0.5",
        "name": name,
        "code_type": "CSS",
        "n": state.n(),
        "k": state.k(),
        "checks": state.to_challenge_checks(relabel),
        "distance": {
            "d": min(side_witnesses["X"]["value"], side_witnesses["Z"]["value"]),
            "X": side_witnesses["X"],
            "Z": side_witnesses["Z"],
        },
        "provenance": copy.deepcopy(parent["provenance"]),
    }
    exported["provenance"]["construction"] = construction
    exported["provenance"]["date"] = date
    exported["provenance"]["notes"] = (
        "Generated by the priced construction calculus. Distance is reported "
        "only with witness-backed upper bounds; lower interval bounds are kept "
        "in the separate local ledger."
    )
    exported["provenance"]["origin"] = "submission"
    # The layout is inherited from the parent and restricted to the qubits the
    # child kept, and the interaction radius is recomputed against the child's
    # own check set -- it is a function of that check set, so a parent's claim
    # cannot be carried into a child whose checks differ. The radius is
    # measured on the exported entry, in the same index space the verifier
    # reads, so the claim and the entry cannot drift apart.
    layout = child_layout(parent, state)
    if layout is not None:
        from collections import Counter
        coords = layout.get("coordinates") or []
        if coords:
            max_mult = max(Counter(tuple(c) for c in coords).values())
            layers = layout.get("layers")
            if (not isinstance(layers, int) or isinstance(layers, bool)
                    or layers < max_mult):
                layout["layers"] = max(max_mult, 1)
        supports = exported["checks"]["X"] + exported["checks"]["Z"]
        layout["interaction_radius"] = _radius_claim(
            interaction_radius_squared(layout["coordinates"], supports)
        )
        exported["locality"] = layout
        if layout["coordinates"] != parent["locality"]["coordinates"]:
            exported["provenance"]["notes"] += (
                " The layout is inherited from the parent and restricted to the "
                "qubits the child kept."
            )
        else:
            exported["provenance"]["notes"] += (
                " The layout is inherited from the parent; its interaction "
                "radius was recomputed against this entry's own checks."
            )
    if certified or exact or oracle:
        try:
            from machine.priced_calculus import certified_distance as _cd
        except Exception:
            _cd = None
        try:
            _dists = _cd(state) if _cd is not None else None
        except Exception:
            _dists = None
        if _dists is not None:
            exported["distance"]["certified"] = _dists
            exported["distance"]["certified_distance"] = _dists.get("d")
            for side in ("X", "Z"):
                if side in exported["distance"] and isinstance(exported["distance"][side], dict):
                    exported["distance"][side]["confidence"] = "certified (exact)"
    if search_error is not None:
        exported["support_search_error"] = search_error
    if staged:
        try:
            from machine import planner as _planner
            _claimed = None
            try:
                _claimed = min(side_witnesses["X"]["value"], side_witnesses["Z"]["value"])
            except Exception:
                _claimed = None
            exported["staged_distance_check"] = _planner.staged_distance_check(
                state, claimed=_claimed, depths=depths, seeds=seeds, layout=parent,
                layout_aware=layout_aware)
        except Exception as exc:
            exported["staged_distance_check_error"] = repr(exc)
    return exported


__all__ = [
    '_exact_coordinate',
    '_squared_distance',
    '_diameter_squared',
    'interaction_radius_squared',
    'radius_decimal',
    'radius_nearest_decimal',
    '_radius_claim',
    'child_layout',
    'radius_squared_in_layout',
    'LOCALITY_CLASS_CAPS',
    '_coordinate_to_number',
    'layout_is_honest',
    'layout_honest',
    'layout_planar',
    'locality_class',
    'layout_layers',
    'export_challenge_entry',
]
