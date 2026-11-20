"""Tower price provider and sweep (issue #327; cost-table helper from #324).

The provider `tower_deletion_prices` prices the deletion of lifted outer
checks of a concatenation tower from level data alone: the inner class
dictionary (`tower_level_data`) and the outer presentation. The derivation
is `DERIVED_RELATIONS.md` section 2a; the sweep against exhaustive
enumeration on built towers is `machine/experiments/tower_sweep.py`. The
tests here pin hand instances and a seeded sweep. Agreement is evidence,
not proof.
"""

import os
import random
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.join(HERE, "experiments")
for path in (EXP, HERE):
    if path not in sys.path:
        sys.path.insert(0, path)

import tower_sweep  # noqa: E402
from weight3_split_reduction import exposure_price_exhaustive  # noqa: E402
from machine.priced_calculus import (  # noqa: E402
    CodeState,
    DistanceLedger,
    Interval,
    Malformed,
    Row,
    tower_cost_table_size,
    tower_deletion_prices,
    tower_level_data,
)


def state(n, rows):
    result = CodeState(tuple(range(n)), tuple(rows), frozenset(row.id for row in rows))
    result.validate()
    return result


def code_422():
    """The [[4, 2, 2]] code: one X-check and one Z-check on all four qubits."""
    return state(4, [Row("a1", "X", (0, 1, 2, 3)), Row("b1", "Z", (0, 1, 2, 3))])


def nonuniform_inner():
    """X-check on {0, 1}, Z-check on {2, 3}: k_in = 2 with class minimum
    weights 1, 2, and 3, so the inner distance alone misprices two classes."""
    return state(4, [Row("a1", "X", (0, 1)), Row("b1", "Z", (2, 3))])


class TestTowerCostTable(unittest.TestCase):
    def test_cost_table_size(self):
        self.assertEqual(tower_cost_table_size(1), 4)
        self.assertEqual(tower_cost_table_size(2), 16)
        self.assertEqual(tower_cost_table_size(3), 64)

    def test_malformed(self):
        with self.assertRaises(Malformed):
            tower_cost_table_size(0)


class TestTowerLevelData(unittest.TestCase):
    def test_the_422_dictionary_is_uniform(self):
        level = tower_level_data(code_422())
        self.assertEqual(level["status"], "computed")
        self.assertEqual(level["k_in"], 2)
        self.assertEqual(level["X"], [0, 2, 2, 2])
        self.assertEqual(level["Z"], [0, 2, 2, 2])
        self.assertEqual(level["distance"], {"X": 2, "Z": 2})
        # Two sector dictionaries of 2^k_in entries; the source's cost-table
        # figure 2^(2 k_in) is recorded alongside, not used.
        self.assertEqual(level["dictionary_entries"], 8)
        self.assertEqual(level["cost_table_size"], 16)

    def test_dual_logical_bases_pair_to_the_identity(self):
        level = tower_level_data(nonuniform_inner())
        xs, zs = level["logical_basis"]["X"], level["logical_basis"]["Z"]
        for a in range(2):
            for b in range(2):
                self.assertEqual((xs[a] & zs[b]).bit_count() % 2, int(a == b))

    def test_a_nonuniform_inner_code_has_a_refined_dictionary(self):
        level = tower_level_data(nonuniform_inner())
        self.assertEqual(sorted(level["X"][1:]), [1, 2, 3])
        self.assertEqual(sorted(level["Z"][1:]), [1, 2, 3])
        self.assertEqual(level["distance"], {"X": 1, "Z": 1})

    def test_an_inner_code_without_logicals_is_refused(self):
        bare = state(2, [Row("a1", "X", (0, 1)), Row("b1", "Z", (0, 1))])
        self.assertEqual(tower_level_data(bare)["status"], "unavailable")


class TestTowerDeletionPrices(unittest.TestCase):
    def setUp(self):
        self.inner = code_422()
        # Two blocks; one outer X-check and one outer Z-check on all four
        # outer qubits (they commute).
        self.outer = state(4, [Row("p1", "X", (0, 1, 2, 3)), Row("q1", "Z", (0, 1, 2, 3))])
        self.groups = [(0, 1), (2, 3)]

    def test_hand_tower_prices_match_exhaustive_enumeration(self):
        verdict = tower_deletion_prices(self.inner, self.outer, self.groups, "q1")
        self.assertEqual(verdict["status"], "computed")
        self.assertEqual(verdict["sector"], "Z")
        # Exposed: any outer X-vector odd on {0,1,2,3}; the lightest has one
        # nonzero block, dictionary weight 2. Promoted: the deleted outer row
        # itself, class (1, 1) on both blocks, dictionary weight 2 + 2.
        self.assertEqual(verdict["w_exp"], 2)
        self.assertEqual(verdict["w_del"], 4)
        self.assertEqual(verdict["tower_n"], 8)
        tower, lifted = tower_sweep.concatenate(self.inner, self.outer, self.groups)
        self.assertEqual(len(tower.Q), 8)
        self.assertEqual(exposure_price_exhaustive(tower, [lifted["q1"]]), 2)
        self.assertEqual(tower_sweep.deletion_price_exhaustive(tower, [lifted["q1"]]), 4)

    def test_the_verdict_carries_a_ledger_ready_price(self):
        verdict = tower_deletion_prices(self.inner, self.outer, self.groups, "q1")
        price = verdict["deletion_price"]
        self.assertEqual((price["w_del"], price["w_exp"]), (4, 2))
        self.assertIn("section 2a", price["evidence"])
        self.assertIn("issue #327", verdict["citation_status"])

    def test_the_ledger_consumes_the_provider_price_as_a_full_distance_cell(self):
        verdict = tower_deletion_prices(self.inner, self.outer, self.groups, "q1")
        tower, lifted = tower_sweep.concatenate(self.inner, self.outer, self.groups)
        child = tower.delete_check(lifted["q1"])
        ledger = DistanceLedger(Interval(3, 4), {"X": Interval(3, 4), "Z": Interval(3, 4)})
        out = ledger.propagate({"op": "C-DELETE-CHECK", "row_id": lifted["q1"]}, child,
                               hypothesis={"deletion_price": verdict["deletion_price"]},
                               parent_state=tower)
        # d' = min(d, w_del, w_exp) with w_exp = 2 pins the full interval at 2;
        # sector-split : the deleted (Z) sector carries w_del = 4
        # and the opposite (X) sector carries w_exp = 2.
        self.assertEqual(out.full, Interval(2, 2))
        self.assertEqual(out.sector["X"].lower, 2)
        self.assertEqual(out.sector["Z"].lower, 3)
        self.assertEqual(out.conditions[-1]["cell"], "C-DELETE-CHECK priced")
        self.assertEqual(out.conditions[-1]["evidence"], verdict["deletion_price"]["evidence"])

    def test_representatives_do_not_change_the_tower_prices(self):
        class Always:
            """A stand-in random source that adds every inner stabilizer."""

            def random(self):
                return 0.0

        plain, lifted = tower_sweep.concatenate(self.inner, self.outer, self.groups)
        noisy, lifted_noisy = tower_sweep.concatenate(
            self.inner, self.outer, self.groups, rng=Always())
        self.assertNotEqual(set(row.support for row in plain.rows),
                            set(row.support for row in noisy.rows))
        for tower, ids in ((plain, lifted), (noisy, lifted_noisy)):
            self.assertEqual(exposure_price_exhaustive(tower, [ids["q1"]]), 2)
            self.assertEqual(tower_sweep.deletion_price_exhaustive(tower, [ids["q1"]]), 4)

    def test_k_in_one_factorizes_as_inner_distance_times_outer_price(self):
        inner = state(4, [Row("a1", "X", (0, 1)), Row("a2", "X", (2, 3)),
                          Row("b1", "Z", (0, 1, 2, 3))])
        level = tower_level_data(inner)
        self.assertEqual(level["k_in"], 1)
        self.assertEqual(level["distance"], {"X": 2, "Z": 2})
        outer = state(3, [Row("p1", "X", (0, 1, 2)), Row("q1", "Z", (0, 1))])
        groups = [(0,), (1,), (2,)]
        verdict = tower_deletion_prices(inner, outer, groups, ["q1"])
        # Outer exposure price 1 (the vector {2}) and outer deletion price 2
        # (the row {0, 1}), each times the inner distance 2.
        self.assertEqual((verdict["w_exp"], verdict["w_del"]), (2, 4))
        self.assertEqual(verdict["w_exp"], 2 * exposure_price_exhaustive(outer, ["q1"]))
        self.assertEqual(verdict["w_del"],
                         2 * tower_sweep.deletion_price_exhaustive(outer, ["q1"]))
        tower, lifted = tower_sweep.concatenate(inner, outer, groups, rng=random.Random(1))
        self.assertEqual(exposure_price_exhaustive(tower, [lifted["q1"]]), 2)
        self.assertEqual(tower_sweep.deletion_price_exhaustive(tower, [lifted["q1"]]), 4)

    def test_the_unrefined_dictionary_misprices_a_nonuniform_tower(self):
        inner = nonuniform_inner()
        outer = state(4, [Row("q1", "Z", (0, 1, 2, 3)), Row("q2", "Z", (1, 3))])
        groups = [(0, 1), (2, 3)]
        verdict = tower_deletion_prices(inner, outer, groups, ["q1"])
        tower, lifted = tower_sweep.concatenate(inner, outer, groups, rng=random.Random(2))
        exhaustive = {"w_exp": exposure_price_exhaustive(tower, [lifted["q1"]]),
                      "w_del": tower_sweep.deletion_price_exhaustive(tower, [lifted["q1"]])}
        self.assertEqual({"w_exp": verdict["w_exp"], "w_del": verdict["w_del"]}, exhaustive)
        unrefined = tower_sweep.unrefined_prices(tower_level_data(inner), outer, ["q1"])
        self.assertNotEqual(unrefined, exhaustive)

    def test_refusals_and_malformed_groups(self):
        self.assertEqual(tower_deletion_prices(self.inner, self.outer, self.groups, "zz")["status"],
                         "unavailable")
        self.assertEqual(tower_deletion_prices(self.inner, self.outer, self.groups,
                                               ["p1", "q1"])["status"], "unavailable")
        with self.assertRaises(Malformed):
            tower_deletion_prices(self.inner, self.outer, [(0, 1), (2,)], "q1")
        with self.assertRaises(Malformed):
            tower_deletion_prices(self.inner, self.outer, [(0, 1), (1, 2)], "q1")


class TestTowerSweep(unittest.TestCase):
    def test_seeded_sweep_agrees_with_exhaustive_enumeration(self):
        report = tower_sweep.run(seed=327, trials=32)
        self.assertEqual(report["mismatches"], [])
        self.assertEqual(report["cell_mismatches"], [])
        self.assertEqual(set(report["k_in_histogram"]), {"1", "2", "3"})
        self.assertGreater(report["cell_checks"], 0)
        self.assertGreater(report["refinement_needed"], 0)


if __name__ == "__main__":
    unittest.main()
