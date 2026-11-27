"""External code ingestion (`spec/REPRESENTATION.md` §9; issue #620).

`lake build` is the authority for the theorems of
`lean/CodeCalculus/IngestedInstances.lean` and runs in its own CI job.
These tests pin the committed module to the generator, pin the binding
hash to the value qldpc-challenge computes, and exercise the build-side
binding check on modules that should fail it. One test compiles a freshly
generated module and is skipped where no built Lean tree is present.
"""

import copy
import json
import os
import shutil
import subprocess
import tempfile
import unittest

from machine.experiments.code_state_lean_instances import (
    INSTANCES,
    OUTPUT,
    ROOT,
    generate,
    load,
    one_off,
    verify,
)
from machine.ingestion import (
    binding_failures,
    canonical_checks,
    checks_sha256,
    ingest,
    lean_ingestion_block,
    lean_presentations,
    span_coefficients,
)
from machine.priced_calculus import CodeState, Malformed

# `checks_sha256` of `verify/check_certs.py` in qldpc-challenge, applied to
# `codes/10-2-3-b.json`. The two repositories must agree on this number.
QLDPC_10_2_3_B_SHA256 = (
    "7596f93bb30edec0d88fe1276bbdf157db404d620252e5f42a71b6e50dc082b7")

LEAN_DIR = ROOT / "lean"


def parent():
    return load("qldpc_10_2_3_b.json")


def toric():
    return load("toric_2x2.json")


class BindingHashTests(unittest.TestCase):
    def test_hash_is_the_one_qldpc_challenge_computes(self):
        self.assertEqual(checks_sha256(parent()), QLDPC_10_2_3_B_SHA256)

    def test_hash_ignores_row_order_and_support_order(self):
        document = parent()
        shuffled = copy.deepcopy(document)
        for side in ("X", "Z"):
            shuffled["checks"][side] = [
                list(reversed(row))
                for row in reversed(shuffled["checks"][side])]
        self.assertNotEqual(shuffled["checks"], document["checks"])
        self.assertEqual(checks_sha256(shuffled), checks_sha256(document))
        self.assertEqual(ingest(shuffled), ingest(document))

    def test_hash_separates_the_sectors_and_sees_one_qubit(self):
        document = parent()
        swapped = copy.deepcopy(document)
        swapped["checks"] = {"X": document["checks"]["Z"],
                             "Z": document["checks"]["X"]}
        self.assertNotEqual(checks_sha256(swapped), checks_sha256(document))
        moved = copy.deepcopy(document)
        moved["checks"]["X"][0][0] = 6
        self.assertNotEqual(checks_sha256(moved), checks_sha256(document))

    def test_hash_does_not_cover_n(self):
        # The contract compares `n` separately for this reason.
        document = parent()
        wider = dict(document, n=11, k=3)
        self.assertEqual(checks_sha256(wider), checks_sha256(document))
        text = lean_ingestion_block("p", document)[0]
        text += ("\n\ntheorem p_binds :\n    presentationBinds p "
                 "p_presentation p_span = true := by decide")
        self.assertEqual(
            binding_failures(text, "p", wider),
            ["literal n = 10 is not the source n = 11"])


class IngestionTests(unittest.TestCase):
    def test_independent_presentation_keeps_every_row(self):
        document = parent()
        state = ingest(document)
        canon = canonical_checks(document)
        for side in ("X", "Z"):
            self.assertEqual(
                [list(row.support) for row in state.sector_rows(side)],
                canon[side])
        self.assertEqual(state.Q, tuple(range(10)))
        self.assertEqual(state.used, frozenset(row.id for row in state.rows))

    def test_ingested_state_has_the_row_spaces_of_the_replay_parent(self):
        # `CodeState.from_challenge` keeps the presented order; ingestion
        # sorts first. Same rows, other identifiers.
        ingested, replay = ingest(parent()), CodeState.from_challenge(parent())
        self.assertNotEqual(ingested, replay)
        for side in ("X", "Z"):
            self.assertEqual(
                sorted(row.support for row in ingested.sector_rows(side)),
                sorted(row.support for row in replay.sector_rows(side)))

    def test_redundant_presentation_drops_dependent_rows(self):
        document = toric()
        state = ingest(document)
        canon = canonical_checks(document)
        coefficients = span_coefficients(document, state)
        for side in ("X", "Z"):
            retained = state.sector_rows(side)
            self.assertEqual(len(canon[side]), 4)
            self.assertEqual(len(retained), 3)
            for support, coeffs in zip(canon[side], coefficients[side]):
                mask = 0
                for row, used in zip(retained, coeffs):
                    if used:
                        mask ^= row.mask
                self.assertEqual(mask, sum(1 << q for q in support))
            self.assertEqual(sum(coefficients[side][3]), 3)

    def test_malformed_presentations_are_refused(self):
        document = parent()
        stabilizer = dict(document, checks={"S": [{"X": [0], "Z": [1]}]})
        repeated = copy.deepcopy(document)
        repeated["checks"]["X"][0] = [0, 0, 3, 4]
        anticommuting = copy.deepcopy(document)
        anticommuting["checks"]["X"][0] = [0, 1, 3]
        outside = copy.deepcopy(document)
        outside["checks"]["X"][0] = [0, 1, 3, 40]
        wrong_k = dict(document, k=3)
        for bad in (stabilizer, repeated, anticommuting, outside, wrong_k):
            with self.assertRaises(Malformed):
                ingest(bad)

    def test_unusable_lean_names_are_refused(self):
        for name in ("10_2_3", "Parent", "a b", "x'"):
            with self.assertRaises(ValueError):
                lean_ingestion_block(name, parent())


class GeneratedModuleTests(unittest.TestCase):
    def test_committed_instances_match_the_generator(self):
        self.assertEqual(OUTPUT.read_text(), generate())

    def test_committed_module_binds_every_fixture(self):
        self.assertEqual(verify(OUTPUT.read_text()), [])

    def test_literals_read_back_are_the_canonical_rows(self):
        found = lean_presentations(OUTPUT.read_text())
        self.assertEqual(sorted(found), sorted(name for name, _, _ in INSTANCES))
        for name, filename, _ in INSTANCES:
            document = load(filename)
            self.assertEqual(found[name]["checks"], canonical_checks(document))
            self.assertEqual(found[name]["n"], document["n"])
            self.assertEqual(found[name]["recorded"], checks_sha256(document))

    def test_module_is_registered_with_the_build_and_the_audit(self):
        for path in ("CodeCalculus.lean", "CodeCalculus/AxiomAudit.lean"):
            text = (LEAN_DIR / path).read_text()
            self.assertIn("import CodeCalculus.Ingestion\n", text)
            self.assertIn("import CodeCalculus.IngestedInstances\n", text)

    def test_a_tampered_module_fails_the_binding_check(self):
        text = OUTPUT.read_text()
        name, document = "qldpc_10_2_3_b_ingested", parent()
        self.assertEqual(binding_failures(text, name, document), [])

        literal = "  X := [[0, 1, 3, 4], [0, 2, 5, 9],"
        self.assertIn(literal, text)
        moved = text.replace(literal, "  X := [[0, 1, 3, 6], [0, 2, 5, 9],", 1)
        failures = binding_failures(moved, name, document)
        self.assertEqual(len(failures), 2)
        self.assertIn("recorded hash", failures[0])
        self.assertIn("is not the source hash", failures[1])

        forged = text.replace(QLDPC_10_2_3_B_SHA256, "0" * 64)
        self.assertEqual(len(binding_failures(forged, name, document)), 1)

        self.assertIn("is not the source hash",
                      binding_failures(text, name, toric())[0])
        self.assertEqual(binding_failures(text, "absent", document),
                         ["no presentation literal for absent"])
        unstated = text.replace("theorem %s_binds" % name, "theorem other")
        self.assertEqual(binding_failures(unstated, name, document),
                         ["the module does not state %s_binds" % name])


class RoundTripTests(unittest.TestCase):
    @unittest.skipUnless(
        shutil.which("lake")
        and (LEAN_DIR / ".lake" / "build" / "lib" / "lean" / "CodeCalculus"
             / "Ingestion.olean").is_file(),
        "needs lake and a built lean/ tree")
    def test_a_fresh_presentation_builds_and_binds(self):
        # A presentation that is not committed as a Lean module: the toric
        # fixture with its rows reversed.
        document = toric()
        for side in ("X", "Z"):
            document["checks"][side] = list(reversed(document["checks"][side]))
        with tempfile.TemporaryDirectory() as scratch:
            source = os.path.join(scratch, "presentation.json")
            with open(source, "w") as handle:
                json.dump(document, handle)
            text = one_off(source, "fresh")
            module = os.path.join(scratch, "Fresh.lean")
            with open(module, "w") as handle:
                handle.write(text)
            result = subprocess.run(
                ["lake", "env", "lean", module], cwd=LEAN_DIR,
                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(binding_failures(text, "fresh", document), [])
        self.assertEqual(checks_sha256(document), checks_sha256(toric()))


if __name__ == "__main__":
    unittest.main()
