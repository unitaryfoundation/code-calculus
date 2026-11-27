"""Lean productions of the typed constructors.

`lake build` is the authority for the Lean side; these tests do not run
Lean. They pin that the committed
`lean/CodeCalculus/ConstructorInstances.lean` is what the generator emits
from the consumer's own `construct`, and that every admitted constructor
has a Lean production, an `EvalExpr` rule, a denotation case, and at least
one kernel-checked instance, so a constructor admitted on the Python side
cannot land without its Lean counterpart.
"""

import os
import re
import unittest

from machine.experiments.constructor_lean_instances import OUTPUT, generate
from machine.priced_calculus import ADMITTED_CONSTRUCTORS

LEAN_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                        "lean", "CodeCalculus")

# Taxonomy ID -> (Lean constructor name, Lean state update).
LEAN_NAMES = {
    "L-HGP": ("hgp", "hgpState"),
    "L-LIFTED": ("lift", "liftState"),
    "L-GROUP-ALGEBRA": ("twoblock", "twoblockState"),
    "A-CONCAT": ("concat", "concatState"),
    "A-PRODUCT": ("product", "productState"),
    "A-DOUBLE": ("double", "doubleState"),
    "L-BALANCED": ("balanced", "balancedState"),
    "L-TANNER": ("tanner", "tannerState"),
    "L-TILE": ("tile", "tileState"),
    "L-NESTED-CSS": ("nested", "nestedState"),
    "L-MAPPING-CONE": ("cone", "coneState"),
    "L-EMPTY": ("empty", "emptyCodeState"),
    "L-FREE": ("free", "freeState"),
    "A-PULLBACK": ("pullback", "pullbackState"),
    "A-PUSHOUT": ("pushout", "pushoutState"),
    "L-PAIR-PARTITION": ("pairPartition", "pairPartitionState"),
    "PP-SCALE": ("ppScale", "ppScaleState"),

}

# Taxonomy ID -> (Lean production, Lean state update) of the three group
# constructors with the group given by its multiplication table.
TABLE_PRODUCTIONS = {
    "L-LIFTED": ("liftTable", "tableLiftState"),
    "L-GROUP-ALGEBRA": ("twoblockTable", "tableTwoblockState"),
    "L-BALANCED": ("balancedTable", "tableBalancedState"),
}


def lean_source(name):
    with open(os.path.join(LEAN_DIR, name)) as source:
        return source.read()


class ConstructorLeanTests(unittest.TestCase):
    def test_committed_instances_match_the_generator(self):
        self.assertEqual(OUTPUT.read_text(), generate())

    def test_every_admitted_constructor_is_named(self):
        self.assertEqual(set(LEAN_NAMES), set(ADMITTED_CONSTRUCTORS))

    def test_every_admitted_constructor_has_a_production_and_a_rule(self):
        term = lean_source("Term.lean")
        evaluation = lean_source("Eval.lean")
        updates = lean_source("Constructors.lean")
        for taxonomy_id, (name, update) in LEAN_NAMES.items():
            with self.subTest(constructor=taxonomy_id):
                self.assertRegex(term, r"\|\s+%s\s+:" % name)
                self.assertIn("`%s`" % taxonomy_id, term)
                if name == "empty":
                    self.assertIn("EvalExpr StateExpr.empty", evaluation)
                    self.assertIn("| StateExpr.empty ", evaluation)
                else:
                    self.assertRegex(evaluation, r"\|\s+%s\s+\{" % name)
                    self.assertIn("EvalExpr (StateExpr.%s " % name, evaluation)
                    self.assertIn("| StateExpr.%s " % name, evaluation)
                self.assertRegex(updates, r"def %s\b" % update)

    def test_every_admitted_constructor_has_a_checked_instance(self):
        instances = OUTPUT.read_text()
        for taxonomy_id, (name, update) in LEAN_NAMES.items():
            with self.subTest(constructor=taxonomy_id):
                if name == "empty":
                    self.assertIn("theorem empty_base_state : emptyCodeState =", instances)
                    self.assertIn("EvalExpr (StateExpr.empty)", instances)
                else:
                    self.assertRegex(
                        instances,
                        r"theorem \w+_state : %s (.|\n)*?:= by decide" % re.escape(update))
                    self.assertIn("EvalExpr (StateExpr.%s " % name, instances)

    def test_group_constructors_have_a_table_production(self):
        term = lean_source("Term.lean")
        evaluation = lean_source("Eval.lean")
        updates = lean_source("CayleyTables.lean")
        instances = OUTPUT.read_text()
        for taxonomy_id, (name, update) in TABLE_PRODUCTIONS.items():
            with self.subTest(constructor=taxonomy_id):
                self.assertIn(taxonomy_id, ADMITTED_CONSTRUCTORS)
                self.assertRegex(term, r"\|\s+%s\s+:" % name)
                self.assertRegex(evaluation, r"\|\s+%s\s+\{" % name)
                self.assertIn("EvalExpr (StateExpr.%s " % name, evaluation)
                self.assertIn("| StateExpr.%s " % name, evaluation)
                self.assertRegex(updates, r"def %s\b" % update)
                self.assertRegex(
                    instances,
                    r"theorem \w+_state : %s (.|\n)*?:= by decide" % re.escape(update))
                self.assertIn("EvalExpr (StateExpr.%s " % name, instances)
        self.assertIn("theorem s3_gens_table", instances)
        self.assertIn("theorem nonassociative_table_refused", instances)
        self.assertIn("theorem balanced_s3_left_action_refused", instances)

    def test_well_formedness_theorems_are_present(self):
        text = lean_source("ConstructorOrthogonality.lean")
        for theorem in ("evalExpr_hgp_wf", "hgp_naturalOrthogonal",
                        "stateK_of_wf"):
            self.assertIn("theorem %s" % theorem, text)
        overlap = lean_source("ConstructorOverlap.lean")
        for theorem in ("evalExpr_lift_wf", "evalExpr_twoblock_wf",
                        "evalExpr_concat_wf", "lift_naturalOrthogonal",
                        "twoblock_naturalOrthogonal",
                        "concat_naturalOrthogonal",
                        "evalExpr_liftTable_wf", "evalExpr_twoblockTable_wf"):
            self.assertIn("theorem %s" % theorem, overlap)
        assembly = lean_source("ConstructorAssembly.lean")
        for theorem in ("evalExpr_product_wf", "evalExpr_double_wf",
                        "evalExpr_balanced_wf", "evalExpr_tanner_wf",
                        "evalExpr_tile_wf", "evalExpr_nested_wf",
                        "evalExpr_cone_wf",
                        "evalExpr_empty_wf", "evalExpr_free_wf",
                        "evalExpr_pullback_wf", "evalExpr_pushout_wf",
                        "evalExpr_pairPartition_wf", "evalExpr_ppScale_wf",
                        "evalExpr_pairPartition_paired",
                        "sixMaps_no_derivation",

                        "product_naturalOrthogonal"):
            self.assertIn("theorem %s" % theorem, assembly)
        balanced = lean_source("BalancedOverlap.lean")
        for theorem in ("balanced_overlap", "balanced_naturalOrthogonal",
                        "evalExpr_balanced_wellFormed",
                        "cayleyBalanced_naturalOrthogonal",
                        "evalExpr_balancedTable_wf"):
            self.assertIn("theorem %s" % theorem, balanced)
        self.assertIn("theorem wf_constructedState",
                      lean_source("ConstructorWellFormedness.lean"))
        natural = lean_source("ConstructorRankNatural.lean")
        for theorem in ("tannerState_k_ge", "tannerState_k_of_indep",
                        "evalExpr_tanner_k_ge", "evalExpr_tanner_k_of_indep",
                        "tileState_k_ge", "tileState_k_of_indep",
                        "evalExpr_tile_k_ge", "evalExpr_tile_k_of_indep",
                        "rankBitmasks_eq_length_iff_indep",
                        "tannerState_k_eq_counting_iff",
                        "tileState_k_eq_counting_iff",
                        "tannerState_k_ge_localRank",
                        "evalExpr_tanner_k_ge_localRank",
                        "tannerState_k_of_disjoint_views",
                        "evalExpr_tanner_k_of_disjoint_views",
                        "tanner_k_not_determined_by_params",
                        "tile_k_not_determined_by_params"):
            self.assertIn("theorem %s" % theorem, natural)
        concat = lean_source("ConcatRetention.lean")
        for theorem in ("combineRows_take_drop", "vecIndep_concatInner",
                        "vecIndep_concat", "concatState_rows_length",
                        "concatState_k_closed", "evalExpr_concat_k"):
            self.assertIn("theorem %s" % theorem, concat)

    def test_future_pi_field_sketch_theorems_are_present(self):
        future_pi = lean_source("FuturePiFields.lean")
        for theorem in (
            "constructionRecord_ofExpr_valid",
            "constructionRecord_transportCmd_valid",
            "constructionRecord_transportCmdPure_valid",
            "constructionRecord_directSum_valid",
            "constructionRecord_glue_valid",
            "constructionRecord_concat_valid",
            "constructionRecord_product_valid",
            "constructionRecord_double_valid",
            "constructionRecord_ppScale_valid",
            "frame_toLogField_sound",
            "frame_toLogField_onePerClass",
            "transportFrame_wellFormed_of_dual",
            "frame_wellFormed_deleteState",
            "frame_wellFormed_addState",
            "frame_wellFormed_rebaseState",
            "frame_wellFormed_swapState",
            "frame_wellFormed_directSumState",
            "frame_wellFormed_glueState",
            "frame422_wellFormed",
        ):
            self.assertIn("theorem %s" % theorem, future_pi)


if __name__ == "__main__":
    unittest.main()
