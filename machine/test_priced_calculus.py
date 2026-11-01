import copy
import math
import unittest
from decimal import Decimal
from fractions import Fraction

from machine.experiments.challenge_replay import exact_distances
from machine.priced_calculus import (
    CodeState,
    DistanceLedger,
    Interval,
    Malformed,
    NoDerivation,
    Row,
    apply_operation,
    child_layout,
    export_challenge_entry,
    graphlike_status,
    interaction_radius_squared,
    is_graphlike,
    is_stabilizer_group_connected,
    is_tanner_connected,
    locality_class,
    radius_decimal,
    radius_nearest_decimal,
    radius_squared_in_layout,
    stabilizer_group_components,
    tanner_components,
    w_exp_graphlike,
    run_sequence,
)


def small_challenge_code():
    return {
        "schema_version": "0.5",
        "name": "small CSS fixture",
        "code_type": "CSS",
        "n": 4,
        "k": 2,
        "checks": {"X": [[0, 1]], "Z": [[0, 1]]},
        "distance": {
            "d": 1,
            "X": {"value": 1, "confidence": "upper_bound", "witness": [2]},
            "Z": {"value": 1, "confidence": "upper_bound", "witness": [2]},
        },
        "provenance": {"authors": ["human"], "construction": "fixture",
                        "date": "2026-10-19", "origin": "submission"},
    }


def graftable_code():
    """A state where `E-GRAFT` at qubit 0 in the X sector is applicable.

    Q = {0,1,2,3,4}; X rows (0,1) and (0,2,3,4); Z rows (0,1,2) and (3,4).
    Grafting qubit 0 leaves X row {1,2,3,4} and Z rows {1,2}, {3,4}: the
    residual qubits are covered by both sectors, the code stays CSS, and
    k = 1 is preserved.
    """
    return {
        "schema_version": "0.5",
        "name": "graftable CSS fixture",
        "code_type": "CSS",
        "n": 5,
        "k": 1,
        "checks": {"X": [[0, 1], [0, 2, 3, 4]], "Z": [[0, 1, 2], [3, 4]]},
        "distance": {
            "d": 2,
            "X": {"value": 2, "confidence": "upper_bound", "witness": [1, 2]},
            "Z": {"value": 2, "confidence": "upper_bound", "witness": [2, 3]},
        },
        "provenance": {"authors": ["human"], "construction": "fixture",
                        "date": "2026-10-20", "origin": "submission"},
    }


class ExactDistanceOracleTests(unittest.TestCase):
    """The experiment's exhaustive oracle must return the *minimum* weight.

    The scan is exhaustive, so the first logical met in integer order is not
    necessarily the lightest: integer order is not weight order. The
    2026-10-19 review found the first-integer-order reading return 5 where
    the true distance is 3.

    It must also enumerate over the state's own qubit *labels*. Bit
    positions are not labels, and a grafted state's namespace is the
    parent's minus the grafted qubit. The 2026-10-20 pass found the label
    error, which reported a grafted child's distance as 1 where it is 2.
    """

    def test_oracle_returns_minimum_weight_not_first_in_integer_order(self):
        # Q = {0,1,2}; one Z check {0,1}; no X checks; k = 2.
        # The X-logicals are {0,1} (weight 2) and {2} (weight 1). Integer
        # order meets {0,1} = 3 before {2} = 4, so a first-integer-order
        # oracle reports 2 where the minimum weight is 1.
        document = {
            "schema_version": "0.5",
            "name": "min-weight oracle fixture",
            "code_type": "CSS",
            "n": 3,
            "k": 2,
            "checks": {"X": [], "Z": [[0, 1]]},
            "provenance": {"authors": ["human"], "construction": "fixture",
                            "date": "2026-10-20", "origin": "submission"},
        }
        state = CodeState.from_challenge(document)
        measured = exact_distances(state)
        self.assertEqual(measured["X"], 1)
        self.assertEqual(measured["Z"], 1)
        self.assertEqual(measured["d"], 1)
        self.assertEqual(measured["vectors_examined"], 7)

    def test_oracle_enumerates_over_qubit_labels_not_bit_positions(self):
        # A graft removes a qubit, so the child's labels are the parent's
        # minus that qubit: {1,2,3,4}, not {0,1,2,3}. An oracle enumerating
        # bit positions 0..n-1 would never examine label 4 and would invent
        # label 0, measuring a different object.
        parent = CodeState.from_challenge(graftable_code())
        child = apply_operation(parent, {
            "op": "E-GRAFT",
            "qubit": 0,
            "sector": "X",
            "ordered_row_ids": ["a1", "a2"],
        })
        self.assertEqual(child.Q, (1, 2, 3, 4))
        measured = exact_distances(child)
        # The child's rows are X {1,2,3,4} and Z {1,2}, {3,4}. Its X-logicals
        # are {1,2} and {3,4} (weight 2, even overlap with both Z rows), its
        # Z-logicals include {1,3} (weight 2), and no qubit is bare, because
        # every one is touched by a check of the other sector.
        self.assertEqual(measured["X"], 2)
        self.assertEqual(measured["Z"], 2)
        self.assertEqual(measured["d"], 2)
        self.assertEqual(measured["vectors_examined"], 15)


class PricedCalculusTests(unittest.TestCase):
    def test_add_check_carries_lower_bound_and_revalidates_witnesses(self):
        parent = small_challenge_code()
        bounds = {
            side: {"value": 1, "source": "small exact fixture enumeration"}
            for side in ("d", "X", "Z")
        }
        state, ledger, trace = run_sequence(
            parent,
            [{"op": "C-ADD-CHECK", "sector": "X", "support": [2],
              "witnesses": {"X": [3], "Z": [3]}}],
            bounds,
            target=1,
        )
        self.assertEqual((state.n(), state.k()), (4, 1))
        self.assertEqual(ledger.full, Interval(1, 1))
        self.assertEqual(trace[0]["verdict"], "certify")

    def test_zero_logical_qubits_certifies_every_finite_target(self):
        parent = small_challenge_code()
        state, ledger, trace = run_sequence(
            parent,
            [
                {"op": "C-ADD-CHECK", "sector": "X", "support": [2, 3]},
                {"op": "C-ADD-CHECK", "sector": "X", "support": [2]},
            ],
            target=1,
        )
        self.assertEqual(state.k(), 0)
        self.assertIsNone(ledger.full.lower)
        self.assertEqual(trace[-1]["verdict"], "certify")

    def test_unpriced_delete_drops_lower_but_keeps_sound_upper(self):
        parent = small_challenge_code()
        state, ledger, trace = run_sequence(
            parent,
            [{"op": "C-DELETE-CHECK", "row_id": "a1"}],
            target=2,
        )
        self.assertEqual((state.n(), state.k()), (4, 3))
        self.assertEqual(ledger.full, Interval(0, 1))
        self.assertEqual(trace[0]["verdict"], "prune")

    def test_priced_delete_requires_explicit_evidence_and_tightens(self):
        parent = small_challenge_code()
        state = CodeState.from_challenge(parent)
        operation = {
            "op": "C-DELETE-CHECK",
            "row_id": "a1",
            "hypothesis": {"deletion_price": {
                "w_del": 2,
                "w_exp": 1,
                "evidence": "fixture exact minima",
            }},
        }
        # Exercise endpoint mapping independently from a distance search. The
        # interval is hypothetical input evidence; this test does not assert it
        # is a bound for the tiny fixture code.
        initial = DistanceLedger(
            Interval(3, 5),
            {"X": Interval(3, 5), "Z": Interval(3, 5)},
        )
        child = apply_operation(state, operation)
        result = initial.propagate(
            operation, child, hypothesis=operation["hypothesis"]
        )
        self.assertEqual(result.full, Interval(1, 1))
        self.assertEqual(result.conditions[-1]["status"], "conditional")

    def test_strict_improvement_requires_exact_old_distance_and_enumeration(self):
        # One logical qubit with logical X_1 and Z_1 as its unique minimum
        # classes. Adding X_1 absorbs the former and anticommutes with the
        # latter, so this concrete instance satisfies the supplied hypothesis.
        state = CodeState(
            (0, 1),
            (Row("a9001", "X", (0,)),),
            frozenset(("a9001",)),
        )
        operation = {"op": "C-ADD-CHECK", "sector": "X", "support": [1]}
        exact_input = DistanceLedger(
            Interval(1, 1),
            {"X": Interval(1, 1), "Z": Interval(1, 1)},
        )
        child = state.add_check("X", [1])
        self.assertEqual(state.k(), 1)
        self.assertEqual(child.k(), 0)
        result = exact_input.propagate(
            operation,
            child,
            hypothesis={"strict_improvement": {
                "base_distance": 1,
                "all_minimum_classes_killed": True,
                "enumeration_id": "enumeration-001",
            }},
        )
        self.assertIsNone(result.full.lower)  # exact +infinity when k=0
        self.assertEqual(result.decide(2), "certify")
        with self.assertRaises(NoDerivation):
            exact_input.propagate(
                operation,
                child,
                hypothesis={"strict_improvement": {
                    "base_distance": 1,
                    "all_minimum_classes_killed": False,
                    "enumeration_id": "incomplete",
                }},
            )

    def test_missing_price_does_not_invent_exact_deletion_value(self):
        parent = small_challenge_code()
        state = CodeState.from_challenge(parent)
        initial = DistanceLedger.from_challenge(state, parent)
        operation = {"op": "C-DELETE-CHECK", "row_id": "a1"}
        result = initial.propagate(operation, state.delete_check("a1"))
        self.assertNotEqual(result.full.lower, result.full.upper)
        self.assertEqual(result.full.lower, 0)

    def test_graft_checks_coverage_css_and_k_preservation(self):
        state = CodeState(
            (0, 1, 2),
            (Row("a1", "X", (0, 1)), Row("a2", "X", (0, 2)),
             Row("b1", "Z", (0, 1, 2))),
            frozenset(("a1", "a2", "b1")),
        )
        child = state.graft(0, "X", ["a1", "a2"])
        self.assertEqual(child.Q, (1, 2))
        self.assertEqual(child.k(), state.k())
        self.assertEqual(child.sector_rows("X")[0].support, (1, 2))
        self.assertEqual(child.sector_rows("Z")[0].support, (1, 2))

    def test_challenge_import_selects_an_independent_presentation(self):
        document = small_challenge_code()
        document["checks"]["X"].append([0, 1])
        state = CodeState.from_challenge(document)
        self.assertEqual(len(state.sector_rows("X")), 1)
        self.assertEqual(state.k(), 2)

    def test_noncommuting_added_check_has_no_derivation(self):
        state = CodeState.from_challenge(small_challenge_code())
        with self.assertRaises(NoDerivation):
            state.add_check("X", [0])

    def test_add_check_rejects_support_outside_q(self):
        state = CodeState.from_challenge(small_challenge_code())
        with self.assertRaises(NoDerivation):
            state.add_check("X", [4])


class SectorPriceFirewallTests(unittest.TestCase):
    """A full-distance price is not a sector price -- but a *sector-indexed*
    price is.

    The two prices in the consumer are indexed differently, and the firewall
    follows the indexing, not the word "price".

    * The **deletion** price is a full-distance price. The source states the
      deletion relation on the full distance, with no sector-wise
      counterpart, so it moves the full-distance endpoints and no sector
      endpoint (`spec/JUDGMENT_LAYER.md` 2b).
    * The **graft exposure** price is indexed to the **non-spliced** sector,
      and the source's graft relation is stated sector-wise, so it moves that
      sector's endpoints as well as the full distance.
    """

    def test_full_distance_deletion_price_does_not_move_sector_endpoints(self):
        parent = small_challenge_code()
        state = CodeState.from_challenge(parent)
        operation = {
            "op": "C-DELETE-CHECK",
            "row_id": "a1",
            "hypothesis": {"deletion_price": {
                "w_del": 2,
                "w_exp": 1,
                "evidence": "fixture exact minima",
            }},
        }
        initial = DistanceLedger(
            Interval(3, 5),
            {"X": Interval(3, 5), "Z": Interval(3, 5)},
        )
        child = apply_operation(state, operation)
        result = initial.propagate(
            operation, child, hypothesis=operation["hypothesis"]
        )
        # The price licenses the full distance ...
        self.assertEqual(result.full, Interval(1, 1))
        # ... and nothing about the sectors, whose lower endpoints stay at the
        # unpriced rule's reset value of zero.
        self.assertEqual(result.sector["X"], Interval(0, 5))
        self.assertEqual(result.sector["Z"], Interval(0, 5))

    def test_graft_price_moves_the_non_spliced_sector_it_is_indexed_to(self):
        state = CodeState.from_challenge(graftable_code())
        operation = {
            "op": "E-GRAFT",
            "qubit": 0,
            "sector": "X",
            "ordered_row_ids": ["a1", "a2"],
            "hypothesis": {"graft_price": {
                "w_expose": 1,
                "evidence": "fixture exposure minimum",
            }},
        }
        initial = DistanceLedger(
            Interval(2, 2),
            {"X": Interval(2, 2), "Z": Interval(2, 2)},
        )
        child = apply_operation(state, operation)
        result = initial.propagate(
            operation, child, hypothesis=operation["hypothesis"]
        )
        # The exposure price is the non-spliced sector's, so it licenses that
        # sector's exact interval ...
        self.assertEqual(result.full, Interval(1, 1))
        self.assertEqual(result.sector["Z"], Interval(1, 1))
        # ... and the spliced sector needs no price and gets none.
        self.assertEqual(result.sector["X"], Interval(2, None))


class GraftSectorCarryTests(unittest.TestCase):
    """The graft relation is stated sector-wise under the corrected rules.

    The spliced sector carries its lower endpoint only and drops its upper
    endpoint to +inf unless a child-valid witness supplies one; the
    non-spliced sector resets its lower endpoint and carries its non-increase
    upper endpoint. The scalar form d' = min(d, w_expose,tau_bar)
    (d' <= d) is refuted for this transition; see OPERATIONAL_SEMANTICS.md
    §4.13.
    """

    def _graft(self, hypothesis=None):
        state = CodeState.from_challenge(graftable_code())
        operation = {
            "op": "E-GRAFT",
            "qubit": 0,
            "sector": "X",
            "ordered_row_ids": ["a1", "a2"],
        }
        if hypothesis is not None:
            operation["hypothesis"] = hypothesis
        child = apply_operation(state, operation)
        initial = DistanceLedger(
            Interval(2, 2),
            {"X": Interval(2, 2), "Z": Interval(2, 2)},
        )
        return initial.propagate(operation, child, hypothesis=hypothesis)

    def test_spliced_sector_carries_lower_only(self):
        result = self._graft()
        # The full distance carries nothing unpriced: lower reset to zero,
        # upper carried from the non-spliced sector (tightened by child-valid
        # witnesses).
        self.assertEqual(result.full, Interval(0, 2))
        # The spliced sector carries its lower endpoint only; its upper
        # endpoint is dropped unless a child-valid witness supplies one.
        self.assertEqual(result.sector["X"], Interval(2, None))
        # The non-spliced sector is where exposure happens: lower reset,
        # upper carried.
        self.assertEqual(result.sector["Z"], Interval(0, 2))

    def test_graft_tightens_sector_upper_endpoints_from_valid_witnesses(self):
        state = CodeState.from_challenge(graftable_code())
        operation = {
            "op": "E-GRAFT",
            "qubit": 0,
            "sector": "X",
            "ordered_row_ids": ["a1", "a2"],
        }
        child = apply_operation(state, operation)
        # The non-spliced sector's carried upper endpoint is 3; the witness
        # below weighs 2 and must tighten it.
        initial = DistanceLedger(
            Interval(2, 2),
            {"X": Interval(2, 2), "Z": Interval(2, 3)},
        )
        # Supply logical witnesses that are valid in the child. The child's
        # rows are X {1,2,3,4} and Z {1,2}, {3,4}: {1,2} commutes with both Z
        # rows and lies outside the X span, and {1,3} commutes with the X row
        # and lies outside the Z span.
        operation["witnesses"] = {"X": [1, 2], "Z": [1, 3]}
        result = initial.propagate(
            operation, child, observations=operation["witnesses"]
        )
        self.assertEqual(result.sector["X"], Interval(2, 2))
        self.assertEqual(result.sector["Z"], Interval(0, 2))
        self.assertEqual(result.full, Interval(0, 2))


class EndpointTransportTests(unittest.TestCase):
    """Observations tighten endpoints; they never widen or discard one.

    The transport rules carry what the licensed relation proves and tighten
    with witnesses valid in the child. A witness is only ever an upper bound,
    so a heavy witness must not lift a carried upper endpoint, and a witness
    lighter than a carried exact endpoint contradicts the licensed relation:
    that is `NoDerivation`, not a crash and not a silently widened interval.
    Strict improvement raises lower endpoints and never lowers one.
    """

    def test_observation_supplies_upper_for_spliced_sector(self):
        # Child state: X row {1..6}, Z rows {1,2},{3,4},{5,6}. The spliced
        # sector's upper endpoint is not carried (it drops to +inf), so a
        # weight-4 witness supplies an upper bound of 4.
        child = CodeState(
            (1, 2, 3, 4, 5, 6),
            (Row("a3", "X", (1, 2, 3, 4, 5, 6)),
             Row("b1", "Z", (1, 2)), Row("b2", "Z", (3, 4)),
             Row("b3", "Z", (5, 6))),
            frozenset(("a3", "b1", "b2", "b3")),
        )
        child.validate()
        initial = DistanceLedger(
            Interval(2, 2), {"X": Interval(2, 2), "Z": Interval(2, 2)}
        )
        result = initial.propagate(
            {"op": "E-GRAFT", "sector": "X"}, child,
            observations={"X": [1, 2, 3, 4]},
        )
        self.assertEqual(result.sector["X"], Interval(2, 4))
        self.assertEqual(result.full, Interval(0, 2))

    def test_observation_does_not_drop_the_carried_deletion_bound(self):
        # Deletion carries the proved d' <= d bound. A supplied witness is an
        # upper bound on top of it; a heavy one may not discard it.
        state = CodeState.from_challenge(small_challenge_code())
        child = state.delete_check("a1")
        initial = DistanceLedger(
            Interval(1, 1), {"X": Interval(1, 1), "Z": Interval(1, 1)}
        )
        result = initial.propagate(
            {"op": "C-DELETE-CHECK", "row_id": "a1"}, child,
            observations={"X": [2, 3], "Z": [2, 3]},
        )
        self.assertEqual(result.sector["X"], Interval(0, 1))
        self.assertEqual(result.sector["Z"], Interval(0, 1))
        self.assertEqual(result.full, Interval(0, 1))

    def test_contradicting_witness_is_no_derivation(self):
        # A witness lighter than a carried exact endpoint contradicts the
        # licensed relation. The three outcomes of spec/TERM_LANGUAGE.md 5
        # stay distinct: this is `no_derivation`, not malformation, and not a
        # raw ValueError escaping the consumer.
        child = CodeState((1, 2), (Row("a3", "X", (1, 2)),), frozenset(("a3",)))
        child.validate()
        initial = DistanceLedger(
            Interval(2, 2), {"X": Interval(2, 2), "Z": Interval(2, 2)}
        )
        with self.assertRaises(NoDerivation):
            initial.propagate(
                {"op": "E-GRAFT", "sector": "X"}, child, observations={"X": [1]}
            )

    def test_strict_improvement_never_lowers_a_carried_sector_bound(self):
        # Strict improvement raises lower endpoints; it never lowers one. A
        # sector may carry a lower bound above base+1 coherently, because
        # d = min(d_X, d_Z) constrains the sectors only through their minimum.
        state = CodeState(
            (0, 1, 2, 3), (Row("a9001", "X", (0,)),), frozenset(("a9001",))
        )
        child = state.add_check("X", [1])
        initial = DistanceLedger(
            Interval(1, 1), {"X": Interval(5, 5), "Z": Interval(1, 1)}
        )
        result = initial.propagate(
            {"op": "C-ADD-CHECK"}, child,
            hypothesis={"strict_improvement": {
                "base_distance": 1,
                "all_minimum_classes_killed": True,
                "enumeration_id": "enumeration-002",
            }},
        )
        self.assertEqual(result.full, Interval(2, None))
        self.assertEqual(result.sector["X"], Interval(5, None))
        self.assertEqual(result.sector["Z"], Interval(2, None))

    def test_malformed_or_contradictory_lower_bound_input_is_malformed(self):
        # Input shape is the consumer's business (trust boundary, consumer.json):
        # a non-integer or negative lower bound, or one that contradicts a
        # validated witness, is Malformed -- not a ValueError from Interval.
        document = small_challenge_code()
        state = CodeState.from_challenge(document)
        with self.assertRaises(Malformed):
            DistanceLedger.from_challenge(
                state, document, {"X": {"value": -1, "source": "bad"}}
            )
        with self.assertRaises(Malformed):
            DistanceLedger.from_challenge(
                state, document, {"X": {"value": 9, "source": "contradicted"}}
            )


class GraftOppositeSectorGuardTests(unittest.TestCase):
    def test_graft_requires_qubit_in_opposite_sector(self):
        state = CodeState(
            (0, 1, 2),
            (Row("a1", "X", (0, 1)), Row("b1", "Z", (0, 2))),
            frozenset(("a1", "b1")),
        )
        with self.assertRaises(NoDerivation):
            state.graft(1, "X", ["a1"])


class StabilizerWeightTests(unittest.TestCase):
    def test_w_is_max_row_weight(self):
        state = CodeState(
            (0, 1, 2, 3),
            (Row("a1", "X", (0, 1)), Row("a2", "X", (0, 2, 3)),
             Row("b1", "Z", (0, 1, 2, 3))),
            frozenset(("a1", "a2", "b1")),
        )
        self.assertEqual(state.w(), 4)

    def test_deletion_does_not_increase_w(self):
        state = CodeState(
            (0, 1, 2, 3),
            (Row("a1", "X", (0, 1)), Row("a2", "X", (0, 2, 3)),
             Row("b1", "Z", (0, 1, 2, 3))),
            frozenset(("a1", "a2", "b1")),
        )
        child = state.delete_check("b1")
        self.assertLessEqual(child.w(), state.w())

    def test_addition_w_is_max(self):
        state = CodeState.from_challenge(small_challenge_code())
        child = state.add_check("X", [0, 1, 2])
        self.assertEqual(child.w(), max(state.w(), 3))


def laid_out_code():
    """A CSS fixture carrying a two-dimensional layout.

    Q = {0,1,2,3,4} on the points (0,0), (1,0), (0,1), (2,1), (3,0). The X row
    {0,1} spans one unit and the Z row {2,3} spans two, so the display's
    interaction radius is 2.0. Qubit 4 is a logical of both sectors and is
    disjoint from every check, so it survives a check addition.
    """
    return {
        "schema_version": "0.5",
        "name": "laid-out CSS fixture",
        "code_type": "CSS",
        "n": 5,
        "k": 3,
        "checks": {"X": [[0, 1]], "Z": [[2, 3]]},
        "distance": {
            "d": 1,
            "X": {"value": 1, "confidence": "upper_bound", "witness": [4]},
            "Z": {"value": 1, "confidence": "upper_bound", "witness": [4]},
        },
        "provenance": {"authors": ["human"], "construction": "fixture",
                        "date": "2026-10-22", "origin": "submission"},
        "locality": {
            "coordinates": [[0.0, 0.0], [1.0, 0.0], [0.0, 1.0],
                            [2.0, 1.0], [3.0, 0.0]],
            "layers": 1,
            "interaction_radius": 2.0,
        },
    }


class LayoutTransportTests(unittest.TestCase):
    """The layout is recomputed in the child, never copied from the parent.

    The interaction radius is a function of the check set, so a parent's
    claim cannot be carried into a child whose checks differ. See
    `the archived notes` and .
    """

    def test_radius_is_the_largest_check_diameter(self):
        parent = laid_out_code()
        supports = parent["checks"]["X"] + parent["checks"]["Z"]
        self.assertEqual(
            interaction_radius_squared(parent["locality"]["coordinates"], supports),
            Fraction(4),
        )

    def test_the_squared_diameter_is_exact_over_the_supplied_coordinates(self):
        # Decimal strings are read at their exact decimal value, so the
        # squared diameter is the rational 1/100 -- a float path would
        # produce (0.2 - 0.1)**2 = 0.010000000000000002.
        coordinates = [["0.1", "0.0"], ["0.2", "0.0"]]
        self.assertEqual(
            interaction_radius_squared(coordinates, [[0, 1]]), Fraction(1, 100)
        )
        # A JSON float is read at its exact binary value, which is not the
        # decimal the supplier wrote; the convention is stated at
        # spec/JUDGMENT_LAYER.md section 2d.1.
        float_coordinates = [[0.1, 0.0], [0.2, 0.0]]
        self.assertNotEqual(
            interaction_radius_squared(float_coordinates, [[0, 1]]),
            Fraction(1, 100),
        )

    def test_addition_recomputes_the_radius_in_the_child(self):
        parent = laid_out_code()
        state = CodeState.from_challenge(parent)
        ledger = DistanceLedger.from_challenge(state, parent, None)
        # A Z row on {0,1,3} spans the diagonal from (0,0) to (2,1), so the
        # child's radius is larger than the parent's. It commutes with the X
        # row {0,1} (even overlap) and leaves the logical qubit 4 alone.
        child = state.add_check("Z", [0, 1, 3])
        child_ledger = ledger.copy().propagate(
            {"op": "C-ADD-CHECK"}, child, hypothesis=None, observations=None
        )
        exported = export_challenge_entry(
            parent, child, child_ledger, "layout probe", "probe", "2026-10-22"
        )
        claim = exported["locality"]["interaction_radius"]
        self.assertGreater(claim, parent["locality"]["interaction_radius"])
        self.assertGreaterEqual(claim, math.sqrt(5.0))
        # The claim is the four-decimal round-up of the exact radius, an
        # upper bound on the real value rather than on a float measurement.
        measured_sq = interaction_radius_squared(
            exported["locality"]["coordinates"],
            exported["checks"]["X"] + exported["checks"]["Z"],
        )
        self.assertEqual(claim, radius_decimal(measured_sq, 4))
        self.assertGreaterEqual(Fraction(Decimal(repr(claim))) ** 2, measured_sq)

    def test_deletion_cannot_increase_the_radius(self):
        parent = laid_out_code()
        state = CodeState.from_challenge(parent)
        ledger = DistanceLedger.from_challenge(state, parent, None)
        child = state.delete_check("b1")
        child_ledger = ledger.copy().propagate(
            {"op": "C-DELETE-CHECK"}, child, hypothesis=None, observations=None
        )
        exported = export_challenge_entry(
            parent, child, child_ledger, "layout probe", "probe", "2026-10-22"
        )
        self.assertLessEqual(
            exported["locality"]["interaction_radius"],
            parent["locality"]["interaction_radius"],
        )

    def test_exported_claim_is_never_below_the_measured_radius(self):
        # The claim is rounded up from the exact squared diameter, so the
        # verifier's full-precision comparison cannot reject an honest entry.
        parent = laid_out_code()
        state = CodeState.from_challenge(parent)
        ledger = DistanceLedger.from_challenge(state, parent, None)
        child = state.add_check("Z", [0, 1, 3])
        child_ledger = ledger.copy().propagate(
            {"op": "C-ADD-CHECK"}, child, hypothesis=None, observations=None
        )
        exported = export_challenge_entry(
            parent, child, child_ledger, "layout probe", "probe", "2026-10-22"
        )
        supports = exported["checks"]["X"] + exported["checks"]["Z"]
        measured_sq = interaction_radius_squared(
            exported["locality"]["coordinates"], supports
        )
        self.assertGreaterEqual(
            Fraction(Decimal(repr(exported["locality"]["interaction_radius"]))) ** 2, measured_sq
        )

    def test_the_export_claim_rounds_up_and_display_rounds_nearest(self):
        # Two decimal conventions over the exact squared diameter, neither
        # of which is the quantity the cap comparison uses:
        # - the exported qLDPC claim is the four-decimal round-up (1.4143
        #   for sqrt(2)), an upper bound on the real value;
        # - trace and report displays round to nearest (1.4142).
        squared = Fraction(2)
        self.assertEqual(radius_decimal(squared, 4), 1.4143)
        self.assertEqual(radius_nearest_decimal(squared, 4), 1.4142)
        self.assertGreaterEqual(
            Fraction(radius_decimal(squared, 4)) ** 2, squared
        )

    def test_nearest_rounding_rounds_ties_up(self):
        # An exact radius of 1.00005 is equidistant from 1.0000 and 1.0001
        # at four decimals; nearest rounding with ties up gives 1.0001.
        squared = Fraction(20001, 20000) ** 2
        self.assertEqual(radius_nearest_decimal(squared, 4), 1.0001)

    def test_a_radius_that_is_exactly_a_claim_decimal_rounds_up_to_itself(self):
        # The exact radius 2.0001 is already a four-decimal value, so the
        # round-up is the same decimal; the claim and the entry the verifier
        # reads carry that decimal, so they cannot drift apart.
        exact_radius = Fraction(20001, 10 ** 4)
        self.assertEqual(radius_decimal(exact_radius ** 2, 4), 2.0001)

    def test_graft_restricts_the_layout_to_the_surviving_qubits(self):
        parent = graftable_code()
        parent["locality"] = {
            "coordinates": [[0.0, 0.0], [1.0, 0.0], [2.0, 0.0],
                            [3.0, 0.0], [4.0, 0.0]],
            "layers": 1,
        }
        state = CodeState.from_challenge(parent)
        child = state.graft(0, "X", ["a1", "a2"])
        layout = child_layout(parent, child)
        self.assertEqual(len(layout["coordinates"]), 4)
        self.assertEqual(layout["coordinates"][0], [1.0, 0.0])
        self.assertEqual(layout["coordinates"][3], [4.0, 0.0])
        self.assertEqual(layout["layers"], 1)

    def test_a_parent_without_a_layout_yields_no_layout(self):
        parent = laid_out_code()
        del parent["locality"]
        state = CodeState.from_challenge(parent)
        self.assertIsNone(child_layout(parent, state))


class RadiusCarryTests(unittest.TestCase):
    """The radius is recomputed in the child, and the class is a verdict on it.

    The carry rules are in `spec/JUDGMENT_LAYER.md` §2d and the derivation is
    at `spec/OPERATIONAL_SEMANTICS.md` §4.21.
    """

    def test_skip_carries_the_radius(self):
        parent = laid_out_code()
        state, ledger, trace = run_sequence(parent, [{"op": "C-SKIP"}])
        self.assertEqual(trace[0]["interaction_radius"], 2.0)
        self.assertEqual(trace[0]["locality_class"], "local-2d-single")

    def test_deletion_cannot_increase_the_radius(self):
        parent = laid_out_code()
        state = CodeState.from_challenge(parent)
        child = state.delete_check("b1")
        self.assertLessEqual(
            radius_squared_in_layout(parent, child),
            radius_squared_in_layout(parent, state),
        )

    def test_addition_gives_the_maximum(self):
        parent = laid_out_code()
        state = CodeState.from_challenge(parent)
        child = state.add_check("Z", [0, 1, 3])
        self.assertEqual(
            radius_squared_in_layout(parent, child),
            max(radius_squared_in_layout(parent, state),
                interaction_radius_squared(parent["locality"]["coordinates"],
                                           [[0, 1, 3]])),
        )

    def test_graft_doubles_at_most(self):
        # The factor-of-two bound, checked exactly on the squared values:
        # r'^2 <= 4 r^2. The naive non-increase is false, and the survey
        # behind that refutation is
        # `the conformance harness`.
        parent = graftable_code()
        parent["locality"] = {
            "coordinates": [[0.0, 0.0], [1.0, 0.0], [2.0, 0.0],
                            [3.0, 0.0], [4.0, 0.0]],
            "layers": 1,
        }
        state = CodeState.from_challenge(parent)
        parent_sq = radius_squared_in_layout(parent, state)
        child = state.graft(0, "X", ["a1", "a2"])
        child_sq = radius_squared_in_layout(parent, child)
        self.assertLessEqual(child_sq, 4 * parent_sq)

    def test_a_state_outside_the_layout_has_no_radius(self):
        # The parent's layout covers qubits 0-3 only, so qubit 4 is outside it.
        # The guard degrades to None, as child_layout does, instead of raising.
        parent = laid_out_code()
        state = CodeState.from_challenge(parent)
        narrowed = copy.deepcopy(parent)
        narrowed["n"] = 4
        narrowed["locality"]["coordinates"] = narrowed["locality"]["coordinates"][:4]
        self.assertIsNone(radius_squared_in_layout(narrowed, state))
        self.assertIsNone(child_layout(narrowed, state))

    def test_locality_class_is_a_verdict_not_a_property(self):
        # A code with no layout has no radius and lands in `unrestricted`.
        parent = laid_out_code()
        del parent["locality"]
        state, ledger, trace = run_sequence(parent, [{"op": "C-SKIP"}])
        self.assertIsNone(trace[0]["interaction_radius"])
        self.assertEqual(trace[0]["locality_class"], "unrestricted")

    def test_class_degrades_when_the_radius_crosses_a_cap(self):
        # The classes nest, so a single-layer code whose radius passes the
        # single-layer cap still qualifies for the bilayer class. The
        # comparison is exact on the squared values: a radius of exactly 4.0
        # is inside the cap, and 4.1 is outside it, with no tolerance.
        self.assertEqual(locality_class(Fraction(39, 10) ** 2, 1),
                         "local-2d-single")
        self.assertEqual(locality_class(Fraction(4) ** 2, 1), "local-2d-single")
        self.assertEqual(locality_class(Fraction(41, 10) ** 2, 1),
                         "local-2d-bilayer")
        self.assertEqual(locality_class(Fraction(6) ** 2, 2), "local-2d-bilayer")
        self.assertEqual(locality_class(Fraction(6) ** 2, 1), "local-2d-bilayer")
        self.assertEqual(locality_class(Fraction(71, 10) ** 2, 2), "unrestricted")
        self.assertEqual(locality_class(Fraction(71, 10) ** 2, 1), "unrestricted")


class GraftScalarRefutationTests(unittest.TestCase):
    """The two worked examples of OPERATIONAL_SEMANTICS.md §4.20.

    They refute the scalar graft form d' = min(d, w_expose) and the
    monotonicity d' <= d for the transition as specified, and they pin the
    corrected carry rules: the spliced sector carries its lower endpoint only,
    and the full distance carries nothing in either direction unpriced.

    The exact distances come from the external exhaustive oracle in
    `the conformance harness`. That oracle is
    evidence, not a proof; the consumer never calls it.
    """

    def _state(self, n, x_supports, z_supports):
        rows = []
        for index, support in enumerate(x_supports):
            rows.append(Row("a%d" % (index + 1), "X", tuple(support)))
        for index, support in enumerate(z_supports):
            rows.append(Row("b%d" % (index + 1), "Z", tuple(support)))
        rows = tuple(rows)
        return CodeState(
            tuple(range(n)), rows, frozenset(row.id for row in rows)
        )

    def _graft(self, state, qubit, sector, chain):
        operation = {
            "op": "E-GRAFT",
            "qubit": qubit,
            "sector": sector,
            "ordered_row_ids": chain,
        }
        child = apply_operation(state, operation)
        return operation, child

    def test_spliced_sector_rises_and_its_upper_endpoint_is_dropped(self):
        state = self._state(
            7,
            [(0, 4, 6), (2, 4), (0, 1, 4, 5, 6), (0, 2, 3, 5, 6)],
            [(1, 2, 3, 4, 5, 6), (0, 2, 4)],
        )
        operation, child = self._graft(state, 0, "Z", ["b2"])
        parent = exact_distances(state)
        exact = exact_distances(child)
        self.assertEqual((parent["X"], parent["Z"], parent["d"]), (2, 2, 2))
        self.assertEqual((exact["X"], exact["Z"], exact["d"]), (2, 3, 2))
        initial = DistanceLedger(
            Interval(2, 2),
            {"X": Interval(2, 2), "Z": Interval(2, 2)},
        )
        result = initial.propagate(operation, child)
        # The spliced sector carries its lower endpoint and drops its upper
        # endpoint, because the parent's weight-2 Z-logical touches q.
        self.assertEqual(result.sector["Z"], Interval(2, None))
        # The full distance carries nothing in either direction unpriced.
        self.assertEqual(result.full, Interval(0, 2))
        self.assertEqual(result.sector["X"], Interval(0, 2))

    def test_full_distance_rises_so_the_parent_upper_endpoint_must_not_carry(self):
        state = self._state(
            8,
            [(2, 5, 6, 7), (0, 4, 6, 7), (0, 2, 3, 6), (0, 1, 2, 5, 6)],
            [(0, 4, 6, 7), (0, 1, 2, 3, 6), (3, 4, 5, 6)],
        )
        operation, child = self._graft(state, 1, "X", ["a4"])
        parent = exact_distances(state)
        exact = exact_distances(child)
        self.assertEqual((parent["X"], parent["Z"], parent["d"]), (2, 3, 2))
        self.assertEqual((exact["X"], exact["Z"], exact["d"]), (3, 3, 3))
        initial = DistanceLedger(
            Interval(2, 2),
            {"X": Interval(2, 2), "Z": Interval(3, 3)},
        )
        result = initial.propagate(operation, child)
        # The spliced X sector carries its lower endpoint only.
        self.assertEqual(result.sector["X"], Interval(2, None))
        # The full upper endpoint must not be the parent's 2: the child's
        # exact distance is 3, and a carried upper endpoint of 2 would make
        # decide(3) return "prune" on a code whose exact distance is 3.
        self.assertEqual(result.full, Interval(0, 3))
        self.assertEqual(result.sector["Z"], Interval(0, 3))
        self.assertNotEqual(result.decide(3), "prune")

    def test_exposure_price_does_not_cap_the_full_distance_at_the_parent_value(self):
        state = self._state(
            8,
            [(2, 5, 6, 7), (0, 4, 6, 7), (0, 2, 3, 6), (0, 1, 2, 5, 6)],
            [(0, 4, 6, 7), (0, 1, 2, 3, 6), (3, 4, 5, 6)],
        )
        operation, child = self._graft(state, 1, "X", ["a4"])
        hypothesis = {"graft_price": {"w_expose": 3, "evidence": "graft exposure"}}
        initial = DistanceLedger(
            Interval(2, 2),
            {"X": Interval(2, 2), "Z": Interval(3, 3)},
        )
        result = initial.propagate(operation, child, hypothesis=hypothesis)
        exact = exact_distances(child)
        self.assertEqual(result.full, Interval(2, 3))
        self.assertEqual(result.sector["X"], Interval(2, None))
        self.assertEqual(result.sector["Z"], Interval(3, 3))
        # Every emitted interval still contains the child's exact distance.
        self.assertLessEqual(result.full.lower, exact["d"])
        self.assertGreaterEqual(result.full.upper, exact["d"])
        self.assertLessEqual(result.sector["X"].lower, exact["X"])
        self.assertLessEqual(result.sector["Z"].lower, exact["Z"])



class DirectSumExtinctionTests(unittest.TestCase):
    def test_direct_sum_extinction_raises_lower_endpoint(self):
        state = CodeState(
            (0, 1, 2, 3, 4, 5),
            (Row("a9001", "X", (0, 1)),
             Row("a9002", "X", (2, 3, 4, 5)),
             Row("b9002", "Z", (2, 3, 4, 5))),
            frozenset(("a9001", "a9002", "b9002")),
        )
        # Add a Z check inside block A, extinguishing its single logical.
        child = state.add_check("Z", (0, 1))
        operation = {"op": "C-ADD-CHECK", "sector": "Z", "support": [0, 1]}
        ledger = DistanceLedger(
            Interval(1, 1),
            {"X": Interval(1, 1), "Z": Interval(1, 1)},
        )
        result = ledger.propagate(
            operation,
            child,
            hypothesis={"direct_sum_extinction": {
                "base_distance": 1,
                "factor_distance": 2,
                "evidence": "direct-sum extinction",
            }},
            parent_state=state,
        )
        self.assertEqual(result.full, Interval(2, 2))
        self.assertTrue(any(c.get("cell") == "C-ADD-CHECK direct-sum extinction"
                            for c in result.conditions))
        with self.assertRaises(NoDerivation):
            ledger.propagate(
                operation,
                child,
                hypothesis={"direct_sum_extinction": {
                    "base_distance": 1,
                    "factor_distance": 1,
                    "evidence": "not an improvement",
                }},
                parent_state=state,
            )

    def test_direct_sum_extinction_requires_exact_old_distance(self):
        state = CodeState(
            (0, 1, 2, 3),
            (Row("a9001", "X", (0, 1)), Row("b9001", "Z", (0, 1))),
            frozenset(("a9001", "b9001")),
        )
        child = state.add_check("X", (2, 3))
        operation = {"op": "C-ADD-CHECK", "sector": "X", "support": [2, 3]}
        ledger = DistanceLedger(
            Interval(0, 1),
            {"X": Interval(0, 1), "Z": Interval(0, 1)},
        )
        with self.assertRaises(NoDerivation):
            ledger.propagate(
                operation,
                child,
                hypothesis={"direct_sum_extinction": {
                    "base_distance": 1,
                    "factor_distance": 2,
                    "rank_check": "rank-completion",
                    "evidence": "mismatched base",
                }},
            )


class GraphlikeExposureTests(unittest.TestCase):
    def test_graphlike_detection_predicate(self):
        graphlike_state = CodeState(
            (0, 1, 2, 3),
            (Row("b9001", "Z", (0, 1)), Row("b9002", "Z", (2, 3))),
            frozenset(("b9001", "b9002")),
        )
        self.assertTrue(is_graphlike(graphlike_state))
        self.assertEqual(graphlike_status(graphlike_state)["max_z_column_weight"], 1)

        nongraphlike_state = CodeState(
            (0, 1, 2),
            (Row("b9001", "Z", (0, 1)), Row("b9002", "Z", (0, 2)), Row("b9003", "Z", (0, 1, 2))),
            frozenset(("b9001", "b9002", "b9003")),
        )
        self.assertFalse(is_graphlike(nongraphlike_state))
        self.assertGreater(graphlike_status(nongraphlike_state)["max_z_column_weight"], 2)

    def test_w_exp_graphlike_never_guesses(self):
        state = CodeState(
            (0, 1, 2, 3),
            (Row("b9001", "Z", (0, 1)), Row("b9002", "Z", (2, 3))),
            frozenset(("b9001", "b9002")),
        )
        verdict = w_exp_graphlike(state)
        self.assertIsInstance(verdict, dict)
        self.assertEqual(verdict["status"], "unavailable")

    def test_graphlike_provider_computes_exposure_price(self):
        state = CodeState(
            (0, 1, 2, 3),
            (Row("b9001", "Z", (0, 1)), Row("b9002", "Z", (1, 2))),
            frozenset(("b9001", "b9002")),
        )
        verdict = w_exp_graphlike(state, deleted="b9001")
        self.assertEqual(verdict["status"], "computed")
        self.assertEqual(verdict["w_exp"], 1)
        self.assertEqual(verdict["value"], 1)
        self.assertTrue(verdict["graphlike"])
        self.assertEqual(verdict["deleted_checks"], ["b9001"])

    def test_graphlike_provider_refuses_non_graphlike_input(self):
        state = CodeState(
            (0, 1, 2),
            (Row("b9001", "Z", (0, 1)),
             Row("b9002", "Z", (0, 2)),
             Row("b9003", "Z", (0, 1, 2))),
            frozenset(("b9001", "b9002", "b9003")),
        )
        verdict = w_exp_graphlike(state, deleted="b9001")
        self.assertEqual(verdict["status"], "unavailable")
        self.assertFalse(verdict["graphlike"])
        self.assertIsNone(verdict["w_exp"])
        self.assertIn("not graphlike", verdict["reason"])

    def test_graphlike_provider_refuses_unknown_deleted_check(self):
        state = CodeState(
            (0, 1, 2, 3),
            (Row("b9001", "Z", (0, 1)), Row("b9002", "Z", (1, 2))),
            frozenset(("b9001", "b9002")),
        )
        verdict = w_exp_graphlike(state, deleted="missing")
        self.assertEqual(verdict["status"], "unavailable")
        self.assertIsNone(verdict["w_exp"])
        self.assertIn("not found", verdict["reason"])

    def test_graphlike_provider_refuses_without_a_deleted_check(self):
        state = CodeState(
            (0, 1, 2, 3),
            (Row("b9001", "Z", (0, 1)), Row("b9002", "Z", (1, 2))),
            frozenset(("b9001", "b9002")),
        )
        verdict = w_exp_graphlike(state)
        self.assertEqual(verdict["status"], "unavailable")
        self.assertIsNone(verdict["w_exp"])
        self.assertIn("no deleted check", verdict["reason"])


class SectorAwareGaugingTests(unittest.TestCase):
    def test_sector_gauging_tightens_one_sector_only(self):
        ledger = DistanceLedger(
            Interval(1, 2),
            {"X": Interval(1, 2), "Z": Interval(1, 2)},
        )
        state = CodeState(
            (0, 1, 2),
            (Row("b9001", "Z", (0, 1)),),
            frozenset(("b9001",)),
        )
        child = state.add_check("X", (2,))
        operation = {"op": "C-ADD-CHECK", "sector": "X", "support": [2]}
        result = ledger.propagate(
            operation,
            child,
            hypothesis={"sector_gauging": {"w_X": 2, "evidence": "sector minimum"}},
        )
        self.assertEqual(result.sector["X"].lower, 2)
        self.assertEqual(result.sector["Z"].lower, 1)
        self.assertTrue(any(c.get("cell") == "C-ADD-CHECK sector-aware gauging"
                            for c in result.conditions))
        with self.assertRaises(NoDerivation):
            ledger.propagate(
                operation,
                child,
                hypothesis={"sector_gauging": {"evidence": "missing price"}},
            )


class TannerConnectivityTests(unittest.TestCase):
    def test_connected_code(self):
        state = CodeState(
            (0, 1, 2),
            (Row("a9001", "X", (0, 1)), Row("b9001", "Z", (1, 2))),
            frozenset(("a9001", "b9001")),
        )
        self.assertTrue(is_tanner_connected(state))

    def test_direct_sum_is_disconnected(self):
        left = CodeState((0, 1), (Row("a9001", "X", (0, 1)),), frozenset(("a9001",)))
        right = CodeState((2, 3), (Row("b9001", "Z", (2, 3)),), frozenset(("b9001",)))
        merged = CodeState.direct_sum(left, right)
        self.assertFalse(is_tanner_connected(merged))

    def test_components_count(self):
        state = CodeState(
            (0, 1, 2, 3),
            (Row("a9001", "X", (0, 1)), Row("b9001", "Z", (2, 3))),
            frozenset(("a9001", "b9001")),
        )
        self.assertEqual(tanner_components(state), 2)


class WorkedDeletionExampleTests(unittest.TestCase):
    def test_small_challenge_deletion_transport(self):
        parent = small_challenge_code()
        state = CodeState.from_challenge(parent)
        initial = DistanceLedger.from_challenge(state, parent)
        child = state.delete_check("a1")
        operation = {"op": "C-DELETE-CHECK", "row_id": "a1"}
        result = initial.propagate(operation, child)
        # Unpriced deletion resets the lower endpoint to zero and carries
        # the proved non-increase upper bound.
        self.assertEqual(result.full.lower, 0)
        self.assertLessEqual(result.full.upper, initial.full.upper)
        self.assertEqual(child.n(), state.n())
        self.assertEqual(child.k(), state.k() + 1)


class StabilizerGroupConnectivityTests(unittest.TestCase):
    def test_connected_code(self):
        state = CodeState(
            (0, 1, 2),
            (Row("a9001", "X", (0, 1)), Row("b9001", "Z", (1, 2))),
            frozenset(("a9001", "b9001")),
        )
        self.assertTrue(is_stabilizer_group_connected(state))

    def test_padded_direct_sum_fails_group_connectivity(self):
        # Two disjoint checks plus a redundant cross-block check: Tanner
        # connected, but the group (RREF) still splits into two blocks.
        state = CodeState(
            (0, 1, 2, 3),
            (Row("a9001", "X", (0, 1)), Row("b9001", "Z", (2, 3)),
             Row("a9002", "X", (0, 1, 2, 3))),
            frozenset(("a9001", "b9001", "a9002")),
        )
        self.assertTrue(is_tanner_connected(state))
        self.assertFalse(is_stabilizer_group_connected(state))


class ConnectivityCarryTests(unittest.TestCase):
    def test_skip_preserves_connectivity(self):
        state = CodeState(
            (0, 1, 2),
            (Row("a9001", "X", (0, 1)), Row("b9001", "Z", (1, 2))),
            frozenset(("a9001", "b9001")),
        )
        self.assertTrue(is_tanner_connected(state.skip()))

    def test_addition_cannot_disconnect(self):
        state = CodeState(
            (0, 1, 2),
            (Row("a9001", "X", (0, 1)), Row("b9001", "Z", (0, 1, 2))),
            frozenset(("a9001", "b9001")),
        )
        child = state.add_check("X", (0, 2))
        self.assertTrue(is_tanner_connected(state))
        self.assertTrue(is_tanner_connected(child))

    def test_deletion_can_disconnect(self):
        state = CodeState(
            (0, 1, 2, 3),
            (Row("c9001", "X", (0,)), Row("c9002", "X", (1,)),
             Row("c9003", "X", (2,)), Row("c9004", "X", (0, 1, 2, 3))),
            frozenset(("c9001", "c9002", "c9003", "c9004")),
        )
        self.assertTrue(is_tanner_connected(state))
        child = state.delete_check("c9004")
        self.assertFalse(is_tanner_connected(child))

    def test_deletion_can_preserve_connectivity(self):
        state = CodeState(
            (0, 1, 2, 3),
            (Row("a9003", "X", (0, 1)), Row("a9004", "X", (1, 2)),
             Row("a9005", "X", (2, 3)), Row("b9004", "Z", (0, 1, 2, 3))),
            frozenset(("a9003", "a9004", "a9005", "b9004")),
        )
        self.assertTrue(is_tanner_connected(state))
        child = state.delete_check("a9004")
        self.assertTrue(is_tanner_connected(child))

    def test_direct_sum_is_disconnected(self):
        left = CodeState((0, 1), (Row("a9001", "X", (0, 1)),), frozenset(("a9001",)))
        right = CodeState((2, 3), (Row("b9001", "Z", (2, 3)),), frozenset(("b9001",)))
        self.assertFalse(is_tanner_connected(CodeState.direct_sum(left, right)))

    def test_graft_preserves_connectivity(self):
        state = CodeState.from_challenge(graftable_code())
        child = state.graft(0, "X", ["a1", "a2"])
        self.assertTrue(is_tanner_connected(state))
        self.assertTrue(is_tanner_connected(child))


class Gate6ConditionalCellTests(unittest.TestCase):
    """The five stated Gate 6 CSS conditional-cell transitions.

    Spec sources: spec/OPERATIONAL_SEMANTICS.md §2 (typed transitions) and
    §4.26–§4.30 (dated hand derivations); judgment cells at
    spec/JUDGMENT_LAYER.md §2f, interval rules §2b. These tests exercise the
    *mechanics* and the interval transport the consumer licenses; they are
    evidence, never a discharge of `OBL-GATE6-CSS-EXTENSIONS`.
    """

    # -- fixtures -----------------------------------------------------------

    def peelable(self):
        """Q={0,1,2,3}; Z rows {0,1} and {2,3}; X row {0,1,2,3}.

        Peeling qubit 0 with the unique touching Z row b1={0,1}: the child
        has Q={1,2,3}, keeps Z row {2,3}, and the opposite (X) sector drops
        the qubit: X row {1,2,3}. k is carried exactly (§4.28).
        """
        return CodeState(
            (0, 1, 2, 3),
            (Row("b1", "Z", (0, 1)), Row("b2", "Z", (2, 3)),
             Row("a1", "X", (0, 1, 2, 3))),
            frozenset(("a1", "b1", "b2")),
        )

    def qfree_peelable(self):
        """Q={0,1,2}; Z row {0,1}; X row {2}: the X sector is q-free at q=0.

        Peeling q=0 with b1: the opposite (X) sector's display is untouched,
        so its distance carries exactly (§4.28's q-free regime).
        """
        return CodeState(
            (0, 1, 2),
            (Row("b1", "Z", (0, 1)), Row("a1", "X", (2,))),
            frozenset(("a1", "b1")),
        )

    def disjoint_pair(self):
        """Two independent CSS blocks for extend/rebase inputs."""
        return CodeState(
            (0, 1, 2, 3),
            (Row("a1", "X", (0, 1)), Row("b1", "Z", (2, 3))),
            frozenset(("a1", "b1")),
        )

    # -- P-REBASE (§4.26) ---------------------------------------------------

    def test_rebase_identity_mix_preserves_the_state_semantics(self):
        state = CodeState.from_challenge(graftable_code())
        child = state.rebase("X", [[1, 0], [0, 1]])
        self.assertEqual(child.Q, state.Q)
        self.assertEqual(child.k(), state.k())
        self.assertEqual(exact_distances(child)["d"], exact_distances(state)["d"])
        self.assertEqual(exact_distances(child)["X"], exact_distances(state)["X"])
        self.assertEqual(exact_distances(child)["Z"], exact_distances(state)["Z"])
        # The display changed: the minted rows replace the sector's display.
        self.assertNotEqual(
            {row.id for row in child.sector_rows("X")},
            {row.id for row in state.sector_rows("X")},
        )

    def test_rebase_mix_preserves_row_spaces_and_distances(self):
        state = CodeState.from_challenge(graftable_code())
        child = state.rebase("X", [[1, 1], [0, 1]])
        # Row space unchanged: the mixed display spans the same X-space.
        for mask in [row.mask for row in state.sector_rows("X")]:
            from machine.priced_calculus import in_span, support_mask
            restricted = [row.mask for row in child.sector_rows("X")]
            self.assertTrue(
                all(in_span(mask, restricted) for mask in
                    [row.mask for row in state.sector_rows("X")]))
        self.assertEqual(exact_distances(child)["X"], exact_distances(state)["X"])
        self.assertEqual(exact_distances(child)["Z"], exact_distances(state)["Z"])
        self.assertEqual(child.k(), state.k())

    def test_rebase_refuses_a_singular_matrix(self):
        state = CodeState.from_challenge(graftable_code())
        with self.assertRaises(NoDerivation):
            state.rebase("X", [[1, 1], [1, 1]])

    def test_rebase_refuses_an_empty_display(self):
        state = CodeState((0,), (), frozenset())
        with self.assertRaises(NoDerivation):
            state.rebase("X", [])

    def test_rebase_refuses_a_malformed_matrix(self):
        state = CodeState.from_challenge(graftable_code())
        with self.assertRaises(Malformed):
            state.rebase("X", [[1, 0]])  # wrong width
        with self.assertRaises(Malformed):
            state.rebase("X", [[1, 2], [0, 1]])  # entries outside F_2

    def test_rebase_ledger_carries_every_span_endpoint(self):
        state = CodeState.from_challenge(graftable_code())
        ledger = DistanceLedger(
            Interval(1, 2), {"X": Interval(1, 2), "Z": Interval(1, 2)},
            witnesses={"X": [{"support": [1, 2], "value": 2,
                              "source": "test"}], "Z": []})
        child = state.rebase("X", [[1, 0], [0, 1]])
        out = ledger.propagate({"op": "P-REBASE", "sector": "X"}, child,
                               parent_state=state)
        self.assertEqual(out.full, Interval(1, 2))
        self.assertEqual(out.sector["X"], ledger.sector["X"])
        self.assertEqual(out.sector["Z"], ledger.sector["Z"])
        self.assertEqual(out.witnesses["X"], ledger.witnesses["X"])
        self.assertTrue(any(c["cell"] == "P-REBASE" for c in out.conditions))

    # -- E-LOCAL-HADAMARD, T=Q (§4.27) --------------------------------------

    def test_hadamard_sector_swap_exchanges_sectors_and_carries_full(self):
        state = CodeState.from_challenge(small_challenge_code())
        child = state.hadamard_sector_swap()
        self.assertEqual(child.Q, state.Q)
        self.assertEqual(child.k(), state.k())
        self.assertEqual(child.w(), state.w())
        # Sector rows exchanged, supports unchanged.
        self.assertEqual(
            [(row.id, row.support) for row in child.sector_rows("X")],
            [(row.id, row.support) for row in state.sector_rows("Z")],
        )
        self.assertEqual(
            [(row.id, row.support) for row in child.sector_rows("Z")],
            [(row.id, row.support) for row in state.sector_rows("X")],
        )
        ex_parent = exact_distances(state)
        ex_child = exact_distances(child)
        self.assertEqual(ex_child["X"], ex_parent["Z"])
        self.assertEqual(ex_child["Z"], ex_parent["X"])
        self.assertEqual(ex_child["d"], ex_parent["d"])

    def test_hadamard_ledger_swaps_sector_intervals_and_revalidates(self):
        state = CodeState.from_challenge(small_challenge_code())
        ledger = DistanceLedger(
            Interval(0, 1),
            {"X": Interval(0, 1), "Z": Interval(0, 1)},
            witnesses={},
        )
        child = state.hadamard_sector_swap()
        out = ledger.propagate({"op": "E-LOCAL-HADAMARD", "qubits": list(state.Q)},
                               child, parent_state=state)
        self.assertEqual(out.full, Interval(0, 1))
        self.assertEqual(out.sector["X"], ledger.sector["Z"])
        self.assertEqual(out.sector["Z"], ledger.sector["X"])
        self.assertTrue(any(c["cell"] == "E-LOCAL-HADAMARD sector swap"
                            for c in out.conditions))

    def test_hadamard_refuses_the_general_split_subset(self):
        state = CodeState.from_challenge(graftable_code())
        with self.assertRaises(NoDerivation):
            apply_operation(state, {"op": "E-LOCAL-HADAMARD", "qubits": [0]})

    def test_hadamard_empty_conjugation_is_the_identity(self):
        state = CodeState.from_challenge(graftable_code())
        child = apply_operation(state, {"op": "E-LOCAL-HADAMARD", "qubits": []})
        self.assertEqual(child, state)
        ledger = DistanceLedger(
            Interval(0, 1),
            {"X": Interval(0, 1), "Z": Interval(0, 2)},
            witnesses={},
        )
        out = ledger.propagate({"op": "E-LOCAL-HADAMARD", "qubits": []},
                               child, parent_state=state)
        self.assertEqual(out.full, ledger.full)
        self.assertEqual(out.sector, ledger.sector)

    def test_hadamard_refuses_an_ill_typed_argument(self):
        state = CodeState.from_challenge(graftable_code())
        with self.assertRaises(Malformed):
            apply_operation(state, {"op": "E-LOCAL-HADAMARD"})

    # -- E-PEEL (§4.28) ------------------------------------------------------

    def test_peel_unique_touch_removes_qubit_and_selected_row(self):
        state = self.peelable()
        child = state.peel(0, "Z", "b1")
        self.assertEqual(child.Q, (1, 2, 3))
        self.assertNotIn("b1", [row.id for row in child.rows])
        # The opposite sector dropped the qubit from its support.
        xrow = [row for row in child.rows if row.sector == "X"][0]
        self.assertEqual(xrow.support, (1, 2, 3))
        # k is carried exactly (§4.28's injectivity argument).
        self.assertEqual(child.k(), state.k())

    def test_peel_refuses_a_non_unique_touch(self):
        state = CodeState(
            (0, 1, 2),
            (Row("b1", "Z", (0, 1)), Row("b2", "Z", (0,)),
             Row("a1", "X", (0, 1, 2))),
            frozenset(("a1", "b1", "b2")),
        )
        with self.assertRaises(NoDerivation):
            state.peel(0, "Z", "b1")

    def test_peel_cannot_leave_an_empty_opposite_row(self):
        # The zero-check guard is carried as a redundancy check: a parent
        # whose opposite sector contains the row {q} would be invalid (odd
        # overlap with r), so the guard's refusal is defensive, not a
        # transition premise (§4.28). This state violates the parent side,
        # which is why the refusal documents the checker, not the rule.
        state = CodeState(
            (0, 1),
            (Row("b1", "Z", (0, 1)), Row("a1", "X", (0,))),
            frozenset(("a1", "b1")),
        )
        with self.assertRaises(NoDerivation):
            state.peel(0, "Z", "b1")

    def test_puncture_unnamed_free_qubit_refutes_the_carry(self):
        # §4.29's refuted-carry fixture: Q={0,1,2} with the single Z row
        # {0,1}; the parent's lightest X logical is the deleted qubit's own
        # free direction {2}; puncturing the unnamed qubit 2 *raises* the
        # X distance from 1 to 2. Every interval resets.
        state = CodeState(
            (0, 1, 2),
            (Row("b1", "Z", (0, 1)),),
            frozenset(("b1",)),
        )
        # The parent is well formed and its X distance is 1.
        ex = exact_distances(state)
        self.assertEqual(ex["X"], 1)
        self.assertEqual(ex["d"], 1)
        ledger = DistanceLedger(
            Interval(0, ex["d"]),
            {"X": Interval(0, ex["X"]), "Z": Interval(0, ex["Z"])},
            witnesses={},
        )
        child = state.puncture(2)
        ex_child = exact_distances(child)
        # The X distance *rose* from 1 to 2: the deleted qubit's own free
        # direction was the parent's lightest X logical. (The child's d is
        # min(d_X', d_Z') = min(2, 1) = 1, driven by the Z side.)
        self.assertEqual(ex_child["X"], 2)
        self.assertEqual(ex_child["d"], 1)
        out = ledger.propagate({"op": "E-PUNCTURE", "qubit": 2}, child,
                               parent_state=state)
        # A carried X upper would exclude the child's exact distance; the
        # reset does not.
        self.assertEqual(out.sector["X"], Interval(0, None))
        self.assertEqual(out.full, Interval(0, None))

    def test_peel_ledger_resets_every_interval(self):
        state = self.peelable()
        ex = exact_distances(state)
        ledger = DistanceLedger(
            Interval(0, ex["d"]),
            {"X": Interval(0, ex["X"]), "Z": Interval(0, ex["Z"])},
            witnesses={},
        )
        child = state.peel(0, "Z", "b1")
        out = ledger.propagate({"op": "E-PEEL", "qubit": 0, "sector": "Z"},
                               child, parent_state=state)
        # §4.28: neither polarity is derivable; everything resets and only
        # child-valid witnesses supply upper endpoints.
        self.assertEqual(out.full, Interval(0, None))
        self.assertEqual(out.sector["X"], Interval(0, None))
        self.assertEqual(out.sector["Z"], Interval(0, None))
        self.assertTrue(any(c["cell"] == "E-PEEL" for c in out.conditions))

    def test_peel_refuses_when_the_named_row_is_not_in_the_named_sector(self):
        state = self.peelable()
        with self.assertRaises(NoDerivation):
            state.peel(0, "X", "b1")

    # -- E-PUNCTURE (§4.29) ---------------------------------------------------

    def test_puncture_removes_the_qubit_and_every_touching_row(self):
        state = CodeState(
            (0, 1, 2),
            (Row("a1", "X", (0, 1)), Row("b1", "Z", (0, 2))),
            frozenset(("a1", "b1")),
        )
        child = state.puncture(0)
        self.assertEqual(child.Q, (1, 2))
        self.assertEqual(child.rows, ())
        child.validate()

    def test_puncture_a_qubit_named_by_no_row_keeps_the_display(self):
        # Q=(0,1,2,3); a1=X(1,2); b1=Z(1,2); qubit 3 is named by no row: the
        # display is unchanged and only the namespace shrinks (n'=n-1,
        # k'=k-1); the distance intervals still reset (§4.29).
        state = CodeState(
            (0, 1, 2, 3),
            (Row("a1", "X", (1, 2)), Row("b1", "Z", (1, 2))),
            frozenset(("a1", "b1")),
        )
        ex = exact_distances(state)
        ledger = DistanceLedger(
            Interval(0, ex["d"]),
            {"X": Interval(0, ex["X"]), "Z": Interval(0, ex["Z"])},
            witnesses={},
        )
        child = state.puncture(0)
        self.assertEqual(child.n(), state.n() - 1)
        self.assertEqual(child.k(), state.k() - 1)
        out = ledger.propagate({"op": "E-PUNCTURE", "qubit": 0}, child,
                               parent_state=state)
        self.assertEqual(out.full, Interval(0, None))
        self.assertEqual(out.sector["X"], Interval(0, None))
        self.assertEqual(out.sector["Z"], Interval(0, None))

    def test_puncture_refuses_an_unknown_qubit(self):
        state = self.disjoint_pair()
        with self.assertRaises(NoDerivation):
            state.puncture(9)

    def test_puncture_ledger_resets_every_interval(self):
        state = CodeState.from_challenge(graftable_code())
        ex = exact_distances(state)
        ledger = DistanceLedger(
            Interval(0, ex["d"]),
            {"X": Interval(0, ex["X"]), "Z": Interval(0, ex["Z"])},
            witnesses={},
        )
        for q in state.Q:
            child = state.puncture(q)
            out = ledger.propagate({"op": "E-PUNCTURE", "qubit": q}, child,
                                   parent_state=state)
            self.assertEqual(out.full, Interval(0, None))
            self.assertEqual(out.sector["X"], Interval(0, None))
            self.assertEqual(out.sector["Z"], Interval(0, None))

    # -- E-EXTEND (§4.30) -----------------------------------------------------

    def test_extend_adds_qubits_and_minted_rows(self):
        state = self.disjoint_pair()
        child = state.extend_code((4,), [("X", (0, 4))])
        self.assertEqual(child.Q, (0, 1, 2, 3, 4))
        self.assertEqual(child.k(), state.k() + 1 - 1)  # |Δ|=1, s_X=1
        minted = [row.id for row in child.rows if row.id not in state.used]
        self.assertEqual(len(minted), 1)
        child.validate()

    def test_extend_k_formula(self):
        state = self.disjoint_pair()
        child = state.extend_code((4, 5), [("X", (0, 4)), ("Z", (5,))])
        self.assertEqual(child.n(), state.n() + 2)
        self.assertEqual(child.k(), state.k() + 2 - 1 - 1)
        child.validate()

    def test_extend_refuses_ill_typed_and_inapplicable_additions(self):
        state = self.disjoint_pair()
        with self.assertRaises(NoDerivation):
            state.extend_code((0,), [("X", (0, 4))])  # Δ overlaps Q
        with self.assertRaises(NoDerivation):
            state.extend_code((4,), [("Z", (0, 4))])  # anti-commutes with a1
        with self.assertRaises(NoDerivation):
            state.extend_code((4,), [("Z", (2, 3))])  # dependent on b1

    def test_extend_refuses_an_empty_support(self):
        state = self.disjoint_pair()
        with self.assertRaises(NoDerivation):
            state.extend_code((4,), [("X", ())])

    def test_extend_ledger_resets_when_the_namespace_grows(self):
        state = self.disjoint_pair()
        child = state.extend_code((4,), [("X", (0, 4))])
        out = DistanceLedger(Interval(1, 2), {"X": Interval(1, 2), "Z": Interval(1, 2)}) \
            .propagate({"op": "E-EXTEND", "new_qubits": [4],
                        "additions": [["X", [0, 4]]]}, child, parent_state=state)
        self.assertEqual(out.full, Interval(0, None))
        self.assertEqual(out.sector["X"], Interval(0, None))
        self.assertEqual(out.sector["Z"], Interval(0, None))

    def test_extend_ledger_with_empty_delta_matches_the_add_monotonicity(self):
        state = self.disjoint_pair()
        child = state.extend_code((), [("Z", (0, 1))])
        out = DistanceLedger(Interval(1, None), {"X": Interval(1, None), "Z": Interval(1, None)}) \
            .propagate({"op": "E-EXTEND", "new_qubits": [],
                        "additions": [["Z", [0, 1]]]}, child, parent_state=state)
        # Monotone: the lower endpoints carry; the added sector's upper is
        # rebuilt; the untouched sector carries both endpoints.
        self.assertEqual(out.full.lower, 1)
        self.assertEqual(out.sector["Z"].lower, 1)
        self.assertEqual(out.sector["X"], Interval(1, None))

    # -- E-GLUE ---------------------------------------------------------------

    def test_glue_transition_combines_disjoint_factors(self):
        left = self.disjoint_pair()
        right = CodeState(
            (4, 5),
            (Row("a2", "X", (4, 5)),),
            frozenset(("a2",)),
        )
        child = apply_operation(left, {
            "op": "E-GLUE",
            "right_state": right,
            "seam_certificate": {"move_words": ["UDLR", "UDLR"],
                                 "evidence": "seam source"},
        })
        self.assertEqual(set(child.Q), {0, 1, 2, 3, 4, 5})
        self.assertEqual(len(child.rows), 3)
        self.assertEqual(child.used, frozenset(("a1", "b1", "a2")))



class AmbientContainmentTests(unittest.TestCase):
    """: every row-introducing transition keeps its rows inside
    the ambient space of its (possibly new) qubit namespace."""

    def test_extend_rejects_support_outside_union(self):
        state = CodeState.from_challenge(small_challenge_code())
        with self.assertRaises(NoDerivation):
            state.extend_code((4,), [("X", (1, 9))])

    def test_glue_rejects_seam_support_outside_union(self):
        left = CodeState((0, 1), (Row("a1", "X", (0, 1)),),
                          frozenset(("a1",)))
        right = CodeState((2, 3), (), frozenset())
        with self.assertRaises(NoDerivation):
            left.glue(right, seam_checks=[("X", (0, 9))])

    def test_add_check_rejects_support_outside_q(self):
        state = CodeState.from_challenge(small_challenge_code())
        with self.assertRaises(NoDerivation):
            state.add_check("X", [9])

    def test_rebase_output_stays_in_q(self):
        state = CodeState.from_challenge(small_challenge_code())
        child = state.rebase("X", [[1]])
        for row in child.rows:
            self.assertTrue(set(row.support) <= set(child.Q))

    def test_hadamard_output_stays_in_q(self):
        state = CodeState.from_challenge(small_challenge_code())
        child = state.hadamard_sector_swap()
        for row in child.rows:
            self.assertTrue(set(row.support) <= set(child.Q))

    def test_peel_output_stays_in_q_prime(self):
        state = CodeState(
            (0, 1, 2),
            (Row("b1", "Z", (0, 1)), Row("a1", "X", (0, 1, 2))),
            frozenset(("a1", "b1")),
        )
        child = state.peel(0, "Z", "b1")
        for row in child.rows:
            self.assertTrue(set(row.support) <= set(child.Q))

    def test_puncture_output_stays_in_q_prime(self):
        state = CodeState(
            (0, 1, 2),
            (Row("a1", "X", (0, 1)), Row("b1", "Z", (0, 2))),
            frozenset(("a1", "b1")),
        )
        child = state.puncture(0)
        for row in child.rows:
            self.assertTrue(set(row.support) <= set(child.Q))

    def test_graft_output_stays_in_q_prime(self):
        state = CodeState.from_challenge(graftable_code())
        child = state.graft(0, "X", ["a1", "a2"])
        for row in child.rows:
            self.assertTrue(set(row.support) <= set(child.Q))



if __name__ == "__main__":
    unittest.main()
