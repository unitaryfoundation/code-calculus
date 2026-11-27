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
from machine.constructors import *

def apply_operation(state, operation):
    if not isinstance(operation, dict):
        raise Malformed("operation must be an object")
    op = operation.get("op")
    if op == "C-SKIP":
        return state.skip()
    if op == "C-DELETE-CHECK":
        return state.delete_check(operation.get("row_id"))
    if op == "C-ADD-CHECK":
        return state.add_check(operation.get("sector"), operation.get("support", []))
    if op == "E-GRAFT":
        return state.graft(operation.get("qubit"), operation.get("sector"),
                           operation.get("ordered_row_ids", []))
    if op == "P-REBASE":
        return state.rebase(operation.get("sector"), operation.get("matrix"))
    if op == "E-LOCAL-HADAMARD":
        qubits = operation.get("qubits")
        if qubits is None or not isinstance(qubits, (list, tuple)):
            raise Malformed("E-LOCAL-HADAMARD names a qubit subset T")
        qset = set(qubits)
        if len(qset) != len(qubits):
            # A list that repeats a label does not name a subset: the term is
            # ill-typed rather than inapplicable (spec/TERM_LANGUAGE.md §2,
            raise Malformed(
                "E-LOCAL-HADAMARD lists a qubit label twice; a list with "
                "repeats does not name a subset")
        if any(isinstance(q, bool) or not isinstance(q, int) or q < 0 for q in qubits):
            raise Malformed("E-LOCAL-HADAMARD qubit labels must be nonnegative integers")
        if not qset:
            return state.skip()
        if qset == set(state.Q):
            return state.hadamard_sector_swap()
        # 0 < |T| < |Q|: the split-subset instance, under the row-space
        # splitting guard (spec/OPERATIONAL_SEMANTICS.md §2, §4.27); a T
        # outside Q or a failed guard has no derivation.
        return state.local_hadamard(qset)
    if op == "E-PEEL":
        return state.peel(operation.get("qubit"), operation.get("sector"),
                          operation.get("row_id"))
    if op == "E-PUNCTURE":
        return state.puncture(operation.get("qubit"))
    if op == "E-EXTEND":
        return state.extend_code(operation.get("new_qubits", ()),
                                 operation.get("additions", ()))
    if op == "E-SPLIT":
        allowed_keys = {"op", "block", "cut_ids", "hypothesis", "witnesses"}
        extra_keys = sorted(set(operation) - allowed_keys)
        if extra_keys:
            raise Malformed(
                "E-SPLIT received unexpected key(s) %s; canonical keys are 'block' and 'cut_ids'"
                % ", ".join(repr(key) for key in extra_keys)
            )
        if "block" not in operation or "cut_ids" not in operation:
            raise Malformed("E-SPLIT requires both 'block' and 'cut_ids'")
        return state.split(operation["block"], operation["cut_ids"])
    if op == "E-GLUE":
        right_state = (operation.get("right_state")
                      or operation.get("other_state")
                      or operation.get("right")
                      or operation.get("other")
                      or operation.get("factor"))
        hypothesis = operation.get("hypothesis")
        if right_state is None and isinstance(hypothesis, dict):
            right_state = (hypothesis.get("right_state")
                          or hypothesis.get("other_state")
                          or hypothesis.get("right")
                          or hypothesis.get("other")
                          or hypothesis.get("factor"))
        if not isinstance(right_state, CodeState):
            raise Malformed("E-GLUE requires a right_state CodeState")
        seam_checks = (operation.get("seam_checks")
                      or operation.get("seams")
                      or operation.get("checks"))
        seam_certificate = (operation.get("seam_certificate")
                           or operation.get("certificate")
                           or operation.get("seam"))
        if seam_certificate is None and isinstance(hypothesis, dict):
            seam_certificate = (hypothesis.get("seam_certificate")
                               or hypothesis.get("certificate")
                               or hypothesis.get("seam"))
        if seam_checks is None and isinstance(hypothesis, dict):
            seam_checks = (hypothesis.get("seam_checks")
                          or hypothesis.get("seams")
                          or hypothesis.get("checks"))
        return state.glue(right_state, seam_checks=seam_checks,
                          seam_certificate=seam_certificate)
    raise Malformed("operation is outside the admitted evaluator subset: %s" % op)

def run_sequence(document, operations, lower_bounds=None, target=None):
    state = CodeState.from_challenge(document)
    ledger = DistanceLedger.from_challenge(state, document, lower_bounds)
    # The layer count is read once, from the parent. Restriction (E-GRAFT) and
    # the check transitions never change it, so it holds for every step; a
    # transition that did would have to re-read it here.
    layers = layout_layers(document)
    planar = layout_planar(document)
    honest = layout_honest(document)
    trace = []
    for index, operation in enumerate(operations):
        before = state
        state = apply_operation(state, operation)
        ledger = ledger.propagate(
            operation,
            state,
            hypothesis=operation.get("hypothesis"),
            observations=operation.get("witnesses"),
            parent_state=before,
        )
        radius_squared = radius_squared_in_layout(document, state)
        trace.append({
            "step": index + 1,
            "operation": operation["op"],
            "n": state.n(),
            "k": state.k(),
            "intervals": ledger.as_json(),
            "verdict": ledger.decide(target) if target is not None else None,
            "state_changed": before != state,
            # The interaction radius is recomputed against the child's own
            # check set; the locality class is the consumer's verdict on it.
            "interaction_radius": None if radius_squared is None
            else radius_nearest_decimal(radius_squared, 6),
            "locality_class": locality_class(radius_squared, layers,
                                                  planar=planar, honest=honest),
        })
    return state, ledger, trace

def _is_ledger_like(obj):
    if obj is None:
        return False
    if isinstance(obj, dict) and ("X" in obj or "Z" in obj or "witnesses" in obj):
        # ambiguous: a witnesses dict looks like this too; treat dict as not ledger
        # unless it carries ledger-only attributes.
        if hasattr(obj, "sector") or hasattr(obj, "_valid_witnesses"):
            return True
        return False
    return (hasattr(obj, "_valid_witnesses")
            or (hasattr(obj, "witnesses") and hasattr(obj, "sector")))


__all__ = [
    'apply_operation',
    'run_sequence',
    '_is_ledger_like',
]
