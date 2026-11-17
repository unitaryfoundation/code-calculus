"""Lean productions of the typed constructors (issues #370, #407, and #445).

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
                self.assertRegex(evaluation, r"\|\s+%s\s+\{" % name)
                self.assertIn("EvalExpr (StateExpr.%s " % name, evaluation)
                self.assertIn("| StateExpr.%s " % name, evaluation)
                self.assertRegex(updates, r"def %s\b" % update)

    def test_every_admitted_constructor_has_a_checked_instance(self):
        instances = OUTPUT.read_text()
        for taxonomy_id, (name, update) in LEAN_NAMES.items():
            with self.subTest(constructor=taxonomy_id):
                self.assertRegex(
                    instances,
                    r"theorem \w+_state : %s (.|\n)*?:= by decide" % re.escape(update))
                self.assertIn("EvalExpr (StateExpr.%s " % name, instances)

    def test_well_formedness_theorems_are_present(self):
        text = lean_source("ConstructorOrthogonality.lean")
        for theorem in ("evalExpr_hgp_wf", "hgp_naturalOrthogonal",
                        "stateK_of_wf"):
            self.assertIn("theorem %s" % theorem, text)
        overlap = lean_source("ConstructorOverlap.lean")
        for theorem in ("evalExpr_lift_wf", "evalExpr_twoblock_wf",
                        "evalExpr_concat_wf", "lift_naturalOrthogonal",
                        "twoblock_naturalOrthogonal",
                        "concat_naturalOrthogonal"):
            self.assertIn("theorem %s" % theorem, overlap)
        assembly = lean_source("ConstructorAssembly.lean")
        for theorem in ("evalExpr_product_wf", "evalExpr_double_wf",
                        "evalExpr_balanced_wf", "evalExpr_tanner_wf",
                        "evalExpr_tile_wf", "evalExpr_nested_wf",
                        "product_naturalOrthogonal"):
            self.assertIn("theorem %s" % theorem, assembly)
        self.assertIn("theorem wf_constructedState",
                      lean_source("ConstructorWellFormedness.lean"))


if __name__ == "__main__":
    unittest.main()
