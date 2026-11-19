"""Monomial-quotient specialization validator, router, and conditional cell (issue #547).

Consumer-side enforcement for the CSS-preserving monomial-quotient specialization
recorded under ``A-QUOTIENT`` (``spec/TAXONOMY.md`` §2.15) and its conditional
transfer-theorem cell (``spec/JUDGMENT_LAYER.md`` §2i; Hsin, arXiv 2611.09538v1
§3.3).

Boundary:
    ``A-QUOTIENT`` remains ``taxonomy-only`` at rung 1. This module is **not**
    an admitted ``EvalExpr`` constructor (it does not register ``A-QUOTIENT`` in
    ``machine/constructors.py`` ``ADMITTED_CONSTRUCTORS``) and it never computes
    exact distances, Tate-cohomology counts, or uncertified lower bounds. It
    enforces the freeness and CSS-preserving applicability constraints, records
    duality-quotient routing, and records supplied transfer-theorem inputs under
    the priced-hypothesis boundary.
"""

from __future__ import annotations

from machine.intervals import Interval, _min_upper, _transport_interval, validate_witness
from machine.state import (
    CodeState,
    Malformed,
    NoDerivation,
    in_span,
    orthogonal,
    support_mask,
)

# Single-qubit / single-qudit Clifford sector classifications.
# On qubits (p = 2), sector-preserving Cliffords modulo phase are {I, X, Y, Z}
# (each maps X -> +/-X and Z -> +/-Z, preserving both sectors individually).
SECTOR_PRESERVING_CLIFFORDS = frozenset({"I", "X", "Y", "Z"})
SECTOR_SWAPPING_CLIFFORDS = frozenset({"H", "HX", "HZ", "HY"})
SECTOR_MIXING_CLIFFORDS = frozenset({
    "S", "S_DAG", "SDG", "SX", "SX_DAG", "SXDG", "SY", "SY_DAG", "SYDG",
    "SH", "HS", "V", "W",
})

DUALITY_ROUTING = {
    "css_preserving": False,
    "accepted": False,
    "route": "extended-state-layer",
    "css_sector_swap_counterpart": "E-LOCAL-HADAMARD (TAXONOMY.md §2.12, T=Q)",
    "extended_state_targets": ("X-LOCAL-CLIFFORD (§4.4)", "X-SYMPLECTIC-HALVE (§4.3)"),
    "v0_3_0_status": "extended-state layer refused for v0.3.0 (issue #545)",
}

MIXING_ROUTING = {
    "css_preserving": False,
    "accepted": False,
    "route": "extended-state-layer",
    "css_sector_swap_counterpart": None,
    "extended_state_targets": ("X-LOCAL-CLIFFORD (§4.4)",),
    "v0_3_0_status": "extended-state layer refused for v0.3.0 (issue #545)",
}


def _require_nonneg_int(value, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        raise Malformed(f"{name} must be a nonnegative integer")
    return value


def classify_single_qudit_clifford(clifford) -> str:
    """Classify a single-qudit Clifford by its action on the X and Z sectors.

    Accepts a canonical single-qubit Clifford label (``"I"``, ``"X"``, ``"Y"``,
    ``"Z"``, ``"H"``, ``"S"``, etc.) or a two-sector image ``(x_img, z_img)``
    / ``{"X": x_img, "Z": z_img}`` with sector tags in ``{"X", "Z", "Y", "XZ"}``.
    Returns ``"sector_preserving"``, ``"sector_swapping"``, or
    ``"sector_mixing"``.
    """
    if isinstance(clifford, str):
        token = clifford.strip().upper()
        if token in SECTOR_PRESERVING_CLIFFORDS:
            return "sector_preserving"
        if token in SECTOR_SWAPPING_CLIFFORDS:
            return "sector_swapping"
        if token in SECTOR_MIXING_CLIFFORDS:
            return "sector_mixing"
        raise Malformed(f"unknown single-qudit Clifford specifier: {clifford!r}")

    if isinstance(clifford, dict):
        if set(clifford.keys()) != {"X", "Z"}:
            raise Malformed("Clifford sector map dict must have exact keys {'X', 'Z'}")
        pair = (clifford["X"], clifford["Z"])
    elif isinstance(clifford, (list, tuple)) and len(clifford) == 2:
        pair = (clifford[0], clifford[1])
    else:
        raise Malformed(f"invalid single-qudit Clifford specifier: {clifford!r}")

    if not all(isinstance(s, str) for s in pair):
        raise Malformed("Clifford sector images must be strings")
    x_img, z_img = pair[0].strip().upper(), pair[1].strip().upper()
    valid_targets = {"X", "Z", "Y", "XZ", "ZX"}
    if x_img not in valid_targets or z_img not in valid_targets:
        raise Malformed(f"invalid Clifford sector images: {(x_img, z_img)!r}")
    if (x_img, z_img) == ("X", "Z"):
        return "sector_preserving"
    if (x_img, z_img) == ("Z", "X"):
        return "sector_swapping"
    return "sector_mixing"


def _is_identity_clifford(clifford) -> bool:
    if isinstance(clifford, str):
        return clifford.strip().upper() == "I"
    return classify_single_qudit_clifford(clifford) == "sector_preserving"


def _normalize_qubits(qubits) -> tuple[int, ...]:
    if not isinstance(qubits, (list, tuple, set, frozenset)) or not qubits:
        raise Malformed("qubits must be a nonempty collection of nonnegative integers")
    ordered = tuple(sorted(_require_nonneg_int(q, "qubit") for q in qubits))
    if len(set(ordered)) != len(ordered):
        raise Malformed("qubits must not contain duplicates")
    return ordered


def _lookup_clifford(cliffords, g, q):
    if cliffords is None:
        return "I"
    if not isinstance(cliffords, dict):
        raise Malformed("cliffords must be a mapping keyed by group element")
    if g not in cliffords:
        raise Malformed(f"missing Clifford entry for group element {g!r}")
    entry = cliffords[g]
    if isinstance(entry, dict) and set(entry.keys()) != {"X", "Z"}:
        if q not in entry:
            raise Malformed(f"missing Clifford entry for group element {g!r}, qubit {q!r}")
        return entry[q]
    return entry


def validate_free_group_action(
    qubits,
    group_action: dict,
    cliffords=None,
    identity=None,
) -> dict:
    """Validate that ``group_action`` is a free finite-group action on ``qubits``.

    Raises ``Malformed`` for ill-typed inputs, non-bijections, missing
    identity, or non-closed permutation sets, and ``NoDerivation`` for any
    non-free action (or nontrivial Clifford at a fixed point).
    """
    qtuple = _normalize_qubits(qubits)
    qset = set(qtuple)
    if not isinstance(group_action, dict) or not group_action:
        raise Malformed("group_action must be a nonempty mapping of group elements to permutations")

    perms = {}
    for g, mapping in group_action.items():
        if not isinstance(mapping, dict) or set(mapping.keys()) != qset:
            raise Malformed(f"permutation for {g!r} must map every qubit in Q")
        targets = list(mapping.values())
        if any(isinstance(v, bool) or not isinstance(v, int) or v not in qset for v in targets):
            raise Malformed(f"permutation for {g!r} maps outside Q")
        if len(set(targets)) != len(qset):
            raise Malformed(f"permutation for {g!r} is not bijective on Q")
        perms[g] = dict(mapping)

    id_perm = {q: q for q in qtuple}
    if identity is not None:
        if identity not in perms:
            raise Malformed(f"declared identity {identity!r} not in group_action")
        if perms[identity] != id_perm:
            raise Malformed(f"declared identity {identity!r} does not act as the identity on Q")
        id_key = identity
    else:
        id_keys = [g for g, p in perms.items() if p == id_perm]
        if not id_keys:
            raise Malformed("group_action must contain the identity element")
        if len(id_keys) > 1:
            if cliffords is not None:
                trivial_c = [
                    g for g in id_keys
                    if all(_is_identity_clifford(_lookup_clifford(cliffords, g, q)) for q in qtuple)
                ]
                if len(trivial_c) == 1:
                    id_key = trivial_c[0]
                else:
                    raise NoDerivation(
                        "action is not free: multiple group elements act trivially on Q"
                    )
            else:
                raise NoDerivation(
                    "action is not free: multiple group elements act trivially on Q"
                )
        else:
            id_key = id_keys[0]

    # Check closure under permutation composition (finite group check).
    perm_tuples = {tuple(p[q] for q in qtuple) for p in perms.values()}
    for g1, p1 in perms.items():
        for g2, p2 in perms.items():
            comp = tuple(p1[p2[q]] for q in qtuple)
            if comp not in perm_tuples:
                raise Malformed(
                    f"group_action is not closed under composition ({g1!r} o {g2!r})"
                )

    # Check freeness and fixed-point Clifford consistency.
    for g, p in perms.items():
        if g == id_key:
            continue
        for q in qtuple:
            if p[q] == q:
                c = _lookup_clifford(cliffords, g, q) if cliffords is not None else "I"
                if not _is_identity_clifford(c):
                    raise NoDerivation(
                        f"inconsistent monomial action: nontrivial Clifford {c!r} "
                        f"on fixed point qubit {q!r} under element {g!r}"
                    )
                raise NoDerivation(
                    f"action is not free: non-identity element {g!r} fixes qubit {q!r}"
                )

    # Partition Q into orbits.
    visited = set()
    orbits = []
    for q in qtuple:
        if q in visited:
            continue
        orb = tuple(sorted({perms[g][q] for g in perms}))
        visited.update(orb)
        orbits.append(orb)

    return {
        "qubits": qtuple,
        "identity": id_key,
        "group_order": len(perms),
        "orbits": tuple(orbits),
    }


def route_monomial_quotient(
    qubits,
    group_action: dict,
    cliffords=None,
    representatives=None,
    identity=None,
) -> dict:
    """Validate a monomial-Clifford action and determine CSS admission or routing.

    Enforces freeness (raising ``NoDerivation`` on fixed points) and classifies
    every single-qudit Clifford ``c_g``:
    - If all ``c_g`` are sector-preserving, accepts the instance under the
      ``A-QUOTIENT`` CSS-preserving specialization.
    - If any ``c_g`` is sector-swapping or sector-mixing, refuses the
      CSS-preserving specialization and returns the explicit duality-quotient /
      extended-state routing record (``css_preserving=False``, ``accepted=False``).
    """
    action_info = validate_free_group_action(
        qubits, group_action, cliffords=cliffords, identity=identity
    )
    qtuple = action_info["qubits"]
    orbits = action_info["orbits"]
    id_key = action_info["identity"]

    if representatives is None:
        chosen_reps = tuple(orb[0] for orb in orbits)
    else:
        if not isinstance(representatives, (list, tuple, set, frozenset)):
            raise Malformed("representatives must be a sequence or set of qubits")
        reps_list = [_require_nonneg_int(r, "representative") for r in representatives]
        if len(reps_list) != len(orbits):
            raise Malformed("representatives must choose exactly one qubit per orbit")
        rep_set = set(reps_list)
        if len(rep_set) != len(orbits):
            raise Malformed("representatives must be distinct")
        for orb in orbits:
            if len(rep_set & set(orb)) != 1:
                raise Malformed(f"orbit {orb!r} must have exactly one chosen representative")
        chosen_reps = tuple(next(r for r in orb if r in rep_set) for orb in orbits)

    # Validate identity element carries the identity sector action.
    if cliffords is not None:
        for q in qtuple:
            c_id = _lookup_clifford(cliffords, id_key, q)
            if not _is_identity_clifford(c_id):
                raise Malformed(
                    f"identity element {id_key!r} cannot carry nontrivial Clifford {c_id!r}"
                )

    classes = set()
    for g in group_action:
        for q in qtuple:
            c = _lookup_clifford(cliffords, g, q)
            classes.add(classify_single_qudit_clifford(c))

    base_fields = {
        "taxonomy_id": "A-QUOTIENT",
        "specialization": "monomial-quotient",
        "taxonomy_status": "taxonomy-only",
        "qubits": qtuple,
        "orbits": orbits,
        "representatives": chosen_reps,
        "group_order": action_info["group_order"],
        "clifford_classes": tuple(sorted(classes)),
    }

    if "sector_mixing" in classes:
        return {**base_fields, **MIXING_ROUTING}
    if "sector_swapping" in classes:
        return {**base_fields, **DUALITY_ROUTING}

    return {
        **base_fields,
        "css_preserving": True,
        "accepted": True,
        "route": "A-QUOTIENT:monomial-quotient-css",
    }


def _project_support_mod2(support, rep_of: dict[int, int]) -> int:
    """Push a parent row support forward to orbit representatives modulo 2."""
    mask = 0
    for q in support:
        mask ^= 1 << rep_of[q]
    return mask


def _verify_parent_css_compatibility(
    parent_state: CodeState,
    group_action: dict,
    record: dict,
) -> dict:
    """Verify parent I1-I5, G-equivariance of checks, and quotient CSS orthogonality."""
    if not isinstance(parent_state, CodeState):
        raise Malformed("parent_state must be a CodeState")
    parent_state.validate()
    if set(parent_state.Q) != set(record["qubits"]):
        raise Malformed(
            "parent_state.Q must match specialization qubits "
            f"({parent_state.Q!r} != {record['qubits']!r})"
        )

    rep_of = {}
    for orb, rep in zip(record["orbits"], record["representatives"]):
        for q in orb:
            rep_of[q] = rep

    projected = {}
    for sector in ("X", "Z"):
        rows = parent_state.sector_rows(sector)
        sector_masks = [row.mask for row in rows]
        for row in rows:
            for g, mapping in group_action.items():
                image_mask = support_mask(tuple(mapping[q] for q in row.support))
                if not in_span(image_mask, sector_masks):
                    raise NoDerivation(
                        f"parent {sector}-row {row.id!r} is not G-equivariant under "
                        f"group element {g!r}"
                    )
        proj_masks = []
        for row in rows:
            mask = _project_support_mod2(row.support, rep_of)
            if mask and not in_span(mask, proj_masks):
                proj_masks.append(mask)
        projected[sector] = tuple(proj_masks)

    if not orthogonal(projected["X"], projected["Z"]):
        raise NoDerivation("projected quotient X and Z checks fail CSS orthogonality")

    return {
        "parent_css_compatible": True,
        "quotient_css_orthogonal": True,
        "quotient_x_masks": projected["X"],
        "quotient_z_masks": projected["Z"],
    }


def enforce_css_monomial_quotient(
    qubits,
    group_action: dict,
    cliffords=None,
    representatives=None,
    identity=None,
    parent_state: CodeState | None = None,
) -> dict:
    """Check CSS-preserving applicability (and optional parent CSS compatibility); raise ``NoDerivation`` on refusal."""
    record = route_monomial_quotient(
        qubits,
        group_action,
        cliffords=cliffords,
        representatives=representatives,
        identity=identity,
    )
    if not record["accepted"]:
        raise NoDerivation(
            "A-QUOTIENT monomial-quotient specialization rejects non-CSS instance "
            f"(clifford_classes={record['clifford_classes']}); routes to "
            f"{record['route']} ({record['v0_3_0_status']})"
        )
    if parent_state is not None:
        compat = _verify_parent_css_compatibility(parent_state, group_action, record)
        return {**record, **compat}
    return record


def check_parent_css_compatibility(
    parent_state: CodeState,
    group_action: dict,
    cliffords=None,
    representatives=None,
    identity=None,
) -> dict:
    """Check CSS-preserving G-equivariance and quotient orthogonality on a parent ``CodeState``."""
    if not isinstance(parent_state, CodeState):
        raise Malformed("parent_state must be a CodeState")
    parent_state.validate()
    return enforce_css_monomial_quotient(
        parent_state.Q,
        group_action,
        cliffords=cliffords,
        representatives=representatives,
        identity=identity,
        parent_state=parent_state,
    )


def transfer_theorem_cell(
    specialization_record: dict,
    *,
    k_parent: int | None = None,
    k_quotient: int | None = None,
    tate_new_logicals: int | None = None,
    d_x_lower: int | None = None,
    d_z_lower: int | None = None,
    d_lower: int | None = None,
    quotient_state: CodeState | None = None,
    witnesses: dict | None = None,
    source: str | None = None,
) -> dict:
    """Build the conditional transfer-theorem judgment record (`JUDGMENT_LAYER.md` §2i).

    Enforces that ``specialization_record`` is an accepted CSS-preserving
    monomial-quotient instance and enforces the priced-hypothesis boundary:
    ``§2i`` records no usable automatic distance bound or ``k`` formula beyond
    ``§2c``/``§2g`` defaults, and supplied dimension/Tate-cohomology/distance
    bounds require a nonempty ``source`` string.
    """
    if not isinstance(specialization_record, dict):
        raise Malformed("specialization_record must be a dict")
    if not (
        specialization_record.get("accepted") is True
        and specialization_record.get("css_preserving") is True
    ):
        raise NoDerivation(
            "transfer theorem conditional cell applies only to accepted CSS-preserving instances"
        )

    supplied_fields = (k_quotient, tate_new_logicals, d_x_lower, d_z_lower, d_lower)
    if any(v is not None for v in supplied_fields):
        if not isinstance(source, str) or not source.strip():
            raise Malformed(
                "supplied transfer-theorem counts and lower bounds require a nonempty source"
            )

    if k_parent is not None:
        k_parent = _require_nonneg_int(k_parent, "k_parent")
    if k_quotient is not None:
        k_quotient = _require_nonneg_int(k_quotient, "k_quotient")
    if tate_new_logicals is not None:
        tate_new_logicals = _require_nonneg_int(tate_new_logicals, "tate_new_logicals")

    lowers = {
        "X": _require_nonneg_int(d_x_lower, "d_x_lower") if d_x_lower is not None else 0,
        "Z": _require_nonneg_int(d_z_lower, "d_z_lower") if d_z_lower is not None else 0,
        "d": _require_nonneg_int(d_lower, "d_lower") if d_lower is not None else 0,
    }
    lowers["d"] = max(lowers["d"], min(lowers["X"], lowers["Z"]))

    uppers = {"X": None, "Z": None}
    if witnesses is not None:
        if quotient_state is None or not isinstance(quotient_state, CodeState):
            raise Malformed("validating witnesses requires a quotient CodeState")
        if not isinstance(witnesses, dict):
            raise Malformed("witnesses must be a dict keyed by 'X' and/or 'Z'")
        for side in ("X", "Z"):
            for support in witnesses.get(side, []):
                sup = tuple(sorted(_require_nonneg_int(q, "witness qubit") for q in support))
                validate_witness(quotient_state, side, sup, len(sup))
                uppers[side] = _min_upper(uppers[side], len(sup))

    full_upper = _min_upper(uppers["X"], uppers["Z"])
    intervals = {
        "X": _transport_interval(lowers["X"], uppers["X"]),
        "Z": _transport_interval(lowers["Z"], uppers["Z"]),
        "d": _transport_interval(lowers["d"], full_upper),
    }

    return {
        "taxonomy_id": "A-QUOTIENT",
        "specialization": "monomial-quotient",
        "taxonomy_status": "taxonomy-only",
        "cell_status": "conditional",
        "computed_distance": False,
        "usable_automatic_bound": False,
        "source": source,
        "k_parent": k_parent,
        "k_quotient": k_quotient,
        "tate_new_logicals": tate_new_logicals,
        "intervals": intervals,
        "orbits": specialization_record["orbits"],
        "representatives": specialization_record["representatives"],
    }


__all__ = [
    "SECTOR_PRESERVING_CLIFFORDS",
    "SECTOR_SWAPPING_CLIFFORDS",
    "SECTOR_MIXING_CLIFFORDS",
    "classify_single_qudit_clifford",
    "validate_free_group_action",
    "route_monomial_quotient",
    "enforce_css_monomial_quotient",
    "check_parent_css_compatibility",
    "transfer_theorem_cell",
]
