"""Tests for the qldpc-challenge certificate payload and its generator (#645, #647, #653).

`export_challenge_certificate` maps sector certificates to the board's
``certs/<slug>.json`` shape; these tests check the payload against the
rules of qldpc-challenge's ``cert.schema.json`` and ``verify/check_certs.py``
as restated here, and its refusals. When ``QLDPC_CHALLENGE_DIR`` names a
qldpc-challenge checkout, the payloads are also run through that
checkout's ``verify/check_certs.py`` in a temporary tree.

The generator tests stop before ``lake build``. Nothing here checks a
Lean theorem, and a payload's ``replay`` names whatever the caller gives it.
"""

import contextlib
import copy
import io
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from machine.certificates import (
    build_sector_lower_bound_certificate,
    build_sector_lower_bound_tree_certificate,
    export_challenge_certificate,
)
from machine.experiments import formal_cert_from_challenge as generator
from machine.ingestion import (
    LEAN_GENERATION_QUBIT_LIMIT,
    LEAN_WELL_FORMEDNESS_ROW_LIMIT,
    binding_failures,
    checks_sha256,
    ingest,
    lean_certified_block,
    lean_ingestion_block,
)

FIXTURES = Path(__file__).resolve().parent / "fixtures"
REPLAY = {"repo": "github.com/example/formal", "commit": "0" * 40,
          "theorem": "CodeCalculus.FormalCert_x.x_certified"}
CHECKER = "Lean 4.35.0 (core library, no Mathlib)"
SOLVER = "code-calculus pruning-tree certificate"


def _entry():
    return json.loads((FIXTURES / "qldpc_10_2_3_b.json").read_text())


def _toric_entry():
    """The redundant toric presentation, with weight-2 witnesses."""
    document = json.loads((FIXTURES / "toric_2x2.json").read_text())
    document["distance"] = {"d": 2, "X": {"value": 2, "witness": [0, 2]},
                            "Z": {"value": 2, "witness": [0, 1]}}
    return document


def _asymmetric_entry():
    """Three qubits, Z-checks only: d_Z = 1 and d_X = 3."""
    return {"n": 3, "k": 1, "checks": {"X": [], "Z": [[0, 1], [1, 2]]},
            "distance": {"d": 1, "X": {"value": 3, "witness": [0, 1, 2]},
                         "Z": {"value": 1, "witness": [0]}}}


def _certificates(state, bounds, tree=True):
    build = (build_sector_lower_bound_tree_certificate if tree
             else build_sector_lower_bound_certificate)
    return {side: build(state, side, bound) for side, bound in bounds.items()}


def _witnesses(document):
    return {side: document["distance"][side]["witness"] for side in ("X", "Z")}


def _export(document, bounds, d_exact, **overrides):
    state = ingest(document)
    arguments = {
        "d": document["distance"]["d"], "d_exact": d_exact, "solver": SOLVER,
        "checker": CHECKER, "replay": dict(REPLAY),
        "witnesses": _witnesses(document),
    }
    arguments.update(overrides)
    certificates = arguments.pop("certificates", None)
    if certificates is None:
        certificates = _certificates(state, bounds)
    return export_challenge_certificate(document, state, certificates,
                                        **arguments)


def schema_problems(payload, document):
    """The rules of the board's schema and checker a payload can break."""
    out = []
    d, sides = payload["d"], payload["sides"]
    if set(sides) != {"X", "Z"}:
        out.append("sides are not X and Z")
    minima = [side["proved_min"] for side in sides.values()]
    if payload["d_lower"] != min(minima):
        out.append("d_lower is not the least proved_min")
    if payload["d_exact"]:
        if payload["d_lower"] != d or any(m != d for m in minima):
            out.append("an exact payload has a bound other than d")
    elif not 2 <= payload["d_lower"] < d:
        out.append("a partial payload's d_lower is not in 2 .. d - 1")
    for side in sides.values():
        if side.get("exact") and side["proved_min"] != d:
            out.append("an exact side's proved_min is not d")
        if "value" in side and side["value"] < side["proved_min"]:
            out.append("a side's value is below its proved_min")
    verification = payload["verification"]
    if verification["level"] != "formal" or not verification.get("checker"):
        out.append("not a formal payload with a checker")
    replay = verification.get("replay") or {}
    if not {"repo", "commit", "theorem"} <= set(replay):
        out.append("replay lacks repo, commit or theorem")
    if not set(replay) <= {"repo", "commit", "theorem", "build",
                           "toolchain", "mathlib"}:
        out.append("replay has a key the formal schema forbids")
    if verification.get("checks_sha256") != checks_sha256(document):
        out.append("checks_sha256 is not the entry's")
    return out


class ExportPayloadTests(unittest.TestCase):
    def test_exact_payload(self):
        document = _entry()
        payload = _export(document, {"X": 3, "Z": 3}, True)
        self.assertEqual(schema_problems(payload, document), [])
        self.assertTrue(payload["d_exact"])
        self.assertEqual(payload["d_lower"], 3)
        for side in ("X", "Z"):
            self.assertEqual(payload["sides"][side]["proved_min"], 3)
            self.assertTrue(payload["sides"][side]["exact"])
            self.assertEqual(payload["sides"][side]["value"], 3)
        self.assertEqual(payload["verification"]["replay"], REPLAY)

    def test_partial_payload(self):
        document = _entry()
        payload = _export(document, {"X": 2, "Z": 2}, False)
        self.assertEqual(schema_problems(payload, document), [])
        self.assertFalse(payload["d_exact"])
        self.assertEqual(payload["d_lower"], 2)
        for side in ("X", "Z"):
            self.assertEqual(payload["sides"][side]["proved_min"], 2)
            self.assertFalse(payload["sides"][side]["exact"])
            self.assertEqual(payload["sides"][side]["value"], 3)

    def test_partial_payload_without_witnesses_states_no_value(self):
        document = _entry()
        payload = _export(document, {"X": 2, "Z": 2}, False, witnesses=None)
        self.assertEqual(schema_problems(payload, document), [])
        for side in payload["sides"].values():
            self.assertNotIn("value", side)
            self.assertNotIn("witness", side)

    def test_kill_certificates_are_accepted_too(self):
        document = _entry()
        state = ingest(document)
        payload = _export(document, None, True, certificates=_certificates(
            state, {"X": 3, "Z": 3}, tree=False))
        self.assertEqual(schema_problems(payload, document), [])

    def test_redundant_presentation_binds_the_entry_hash(self):
        document = _toric_entry()
        state = ingest(document)
        retained = {"n": state.n(), "checks": {
            side: [sorted(row.support) for row in state.sector_rows(side)]
            for side in ("X", "Z")}}
        self.assertNotEqual(checks_sha256(retained), checks_sha256(document))
        payload = _export(document, {"X": 2, "Z": 2}, True)
        self.assertEqual(payload["verification"]["checks_sha256"],
                         checks_sha256(document))
        self.assertEqual(schema_problems(payload, document), [])

    def test_asymmetric_exact_payload(self):
        document = _asymmetric_entry()
        payload = _export(document, {"X": 3, "Z": 1}, True)
        self.assertEqual(schema_problems(payload, document), [])
        self.assertEqual(payload["d"], 1)
        self.assertEqual(payload["sides"]["X"]["proved_min"], 1)
        self.assertIn("d_X >= 3 is proved", payload["sides"]["X"]["note"])
        self.assertFalse(payload["sides"]["X"]["exact"])
        self.assertTrue(payload["sides"]["Z"]["exact"])

    def test_optional_fields_pass_through(self):
        document = _entry()
        replay = dict(REPLAY, build="cd lean && lake build X",
                      toolchain="leanprover/lean4:v4.35.0")
        payload = _export(document, {"X": 3, "Z": 3}, True, replay=replay,
                          name="[[10,2,3]]", note="n", reference="r")
        self.assertEqual(payload["name"], "[[10,2,3]]")
        self.assertEqual(payload["verification"]["replay"], replay)
        self.assertEqual(payload["verification"]["note"], "n")
        self.assertEqual(payload["verification"]["reference"], "r")


class ExportRefusalTests(unittest.TestCase):
    def assertRefused(self, document, bounds, d_exact, **overrides):
        with self.assertRaises(ValueError):
            _export(document, bounds, d_exact, **overrides)

    def test_one_sector_is_refused(self):
        document = _entry()
        state = ingest(document)
        self.assertRefused(document, None, True, certificates=_certificates(
            state, {"X": 3}))

    def test_state_of_another_entry_is_refused(self):
        document = _entry()
        other = _toric_entry()
        with self.assertRaises(ValueError):
            export_challenge_certificate(
                document, ingest(other), _certificates(
                    ingest(other), {"X": 2, "Z": 2}),
                d=3, d_exact=False, solver=SOLVER, checker=CHECKER,
                replay=REPLAY)

    def test_certificate_of_another_state_is_refused(self):
        document = _entry()
        other = ingest(_toric_entry())
        certificates = _certificates(ingest(document), {"X": 3, "Z": 3})
        certificates["Z"] = build_sector_lower_bound_tree_certificate(
            other, "Z", 2)
        self.assertRefused(document, None, True, certificates=certificates)

    def test_rejected_certificate_is_refused(self):
        document = _entry()
        certificates = _certificates(ingest(document), {"X": 3, "Z": 3})
        forged = copy.deepcopy(certificates)
        forged["X"]["bound"] = 4
        self.assertRefused(document, None, True, certificates=forged)

    def test_bad_witnesses_are_refused(self):
        document = _entry()
        bounds = {"X": 3, "Z": 3}
        for witnesses in ({"X": []}, {"X": [0, 1, 2]}, {"X": [0, 8, 9, 9]},
                          {"Y": [0, 8, 9]}, {"X": [True, 8, 9]}):
            with self.subTest(witnesses=witnesses):
                self.assertRefused(document, bounds, True,
                                   witnesses=witnesses)

    def test_witness_lighter_than_d_is_refused(self):
        self.assertRefused(_entry(), {"X": 3, "Z": 3}, False, d=4)

    def test_partial_bounds_out_of_range_are_refused(self):
        document = _entry()
        self.assertRefused(document, {"X": 3, "Z": 3}, False)
        self.assertRefused(document, {"X": 1, "Z": 3}, False)

    def test_exact_needs_its_bound_and_a_witness(self):
        document = _entry()
        self.assertRefused(document, {"X": 2, "Z": 3}, True)
        self.assertRefused(document, {"X": 3, "Z": 3}, True, witnesses=None)

    def test_replay_and_checker_have_no_defaults(self):
        document = _entry()
        bounds = {"X": 3, "Z": 3}
        for replay in ({"repo": "r", "commit": "c"},
                       dict(REPLAY, emit="python3 emit.py"),
                       dict(REPLAY, theorem=""), "not a mapping"):
            with self.subTest(replay=replay):
                self.assertRefused(document, bounds, True, replay=replay)
        self.assertRefused(document, bounds, True, checker="")
        self.assertRefused(document, bounds, True, solver=None)
        self.assertRefused(document, bounds, "yes")


@unittest.skipUnless(os.environ.get("QLDPC_CHALLENGE_DIR"),
                     "QLDPC_CHALLENGE_DIR names no qldpc-challenge checkout")
class CheckCertsAcceptanceTests(unittest.TestCase):
    """The payloads pass the board's own checker in a temporary tree."""

    def test_check_certs_accepts_the_payloads(self):
        source = Path(os.environ["QLDPC_CHALLENGE_DIR"])
        exact = _entry()
        partial = _entry()
        toric = _toric_entry()
        payloads = {
            "exact": (exact, _export(exact, {"X": 3, "Z": 3}, True)),
            "partial": (partial, _export(partial, {"X": 2, "Z": 2}, False)),
            "toric": (toric, _export(toric, {"X": 2, "Z": 2}, True)),
        }
        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch)
            for part in ("verify", "schema"):
                shutil.copytree(source / part, root / part)
            (root / "codes").mkdir()
            (root / "certs").mkdir()
            for slug, (document, payload) in payloads.items():
                (root / "codes" / ("%s.json" % slug)).write_text(
                    json.dumps(document))
                (root / "certs" / ("%s.json" % slug)).write_text(
                    json.dumps(payload))
            proc = subprocess.run(
                [sys.executable, str(root / "verify" / "check_certs.py")],
                cwd=str(root), capture_output=True, text=True)
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn("3 certificates valid", proc.stdout)
        self.assertNotIn("jsonschema unavailable", proc.stdout)


class LeanBlockTests(unittest.TestCase):
    def test_well_formedness_theorem_is_optional(self):
        document = _entry()
        with_block, _ = lean_ingestion_block("e", document)
        without, _ = lean_ingestion_block("e", document,
                                          include_well_formedness=False)
        self.assertIn("theorem e_wellFormed", with_block)
        self.assertNotIn("e_wellFormed", without)
        self.assertEqual(with_block.replace(
            "theorem e_wellFormed : EncodingWellFormed e :=\n"
            "  encodingWellFormed_of_bool (by decide)\n\n", ""), without)

    def test_certified_block_conjoins_the_stated_theorems(self):
        text = lean_certified_block("e", {"X": 3, "Z": 2}, {"X"})
        self.assertIn("theorem e_certified :", text)
        self.assertIn("exactDistance? Sector.X e = some 3 ∧", text)
        self.assertIn("(∀ d : Nat, exactDistance? Sector.Z e = some d → "
                      "2 ≤ d) :=", text)
        self.assertIn("⟨e_binds, e_X_exact, e_Z_lower_bound⟩", text)


class GeneratorTests(unittest.TestCase):
    """`formal_cert_from_challenge` up to, not including, `lake build`."""

    def test_module_states_one_certified_theorem_and_binds(self):
        document = _entry()
        generated = generator.generate(document, "e", {"X": 3, "Z": 3})
        module = generated["module"]
        self.assertEqual(generated["exact"], {"X", "Z"})
        self.assertIn("namespace CodeCalculus.FormalCert_e", module)
        self.assertIn("theorem e_certified :", module)
        self.assertIn("theorem e_wellFormed", module)
        self.assertEqual(binding_failures(module, "e", document), [])
        self.assertEqual(generator.theorem_name("e"),
                         "CodeCalculus.FormalCert_e.e_certified")
        self.assertEqual(generator.build_command("e"),
                         "cd lean && lake build CodeCalculus.FormalCerts.e")

    def test_bound_below_the_witness_gives_lower_bounds_only(self):
        generated = generator.generate(_entry(), "e", {"X": 2, "Z": 2})
        self.assertEqual(generated["exact"], set())
        self.assertNotIn("e_X_exact", generated["module"])

    def test_one_sector_still_generates(self):
        generated = generator.generate(_entry(), "e", {"X": 3})
        self.assertEqual(set(generated["certificates"]), {"X"})
        self.assertNotIn("Sector.Z e = some", generated["module"])

    def test_default_bounds_are_the_witnessed_values(self):
        self.assertEqual(generator._sector_bounds(_entry(), [], []),
                         {"X": 3, "Z": 3})
        self.assertEqual(generator._sector_bounds(_entry(), ["z"], [2]),
                         {"Z": 2})
        for sectors, bounds in ((["X", "X"], []), (["Y"], []),
                                (["X", "Z"], [2])):
            with self.assertRaises(generator.Refused):
                generator._sector_bounds(_entry(), sectors, bounds)
        with self.assertRaises(generator.Refused):
            generator._sector_bounds(_toric_entry() | {"distance": {}}, [], [])

    def test_well_formedness_is_left_out_above_the_row_limit(self):
        n = 2 * (LEAN_WELL_FORMEDNESS_ROW_LIMIT + 2)
        rows = [[q, q + 1] for q in range(0, n - 1, 2)]
        document = {"n": n, "k": n - len(rows), "checks": {"X": [],
                                                           "Z": rows}}
        notes = io.StringIO()
        with contextlib.redirect_stderr(notes):
            generated = generator.generate(document, "e", {"Z": 1})
        self.assertIn("leaving out e_wellFormed", notes.getvalue())
        self.assertFalse(generated["well_formedness"])
        self.assertNotIn("e_wellFormed", generated["module"])
        forced = generator.generate(document, "e", {"Z": 1},
                                    well_formedness="always")
        self.assertIn("e_wellFormed", forced["module"])

    def test_large_entries_are_refused_unless_allowed(self):
        n = LEAN_GENERATION_QUBIT_LIMIT + 1
        document = {"n": n, "k": n, "checks": {"X": [], "Z": []}}
        with self.assertRaises(generator.Refused):
            generator.generate(document, "e", {"Z": 1})
        generated = generator.generate(document, "e", {"Z": 1},
                                       allow_large=True)
        self.assertIn("theorem e_certified", generated["module"])

    def test_bad_names_and_entries_are_refused(self):
        with self.assertRaises(generator.Refused):
            generator.generate(_entry(), "Bad-Name", {"X": 3})
        broken = _entry()
        broken["checks"]["X"][0] = [0, 0, 1]
        with self.assertRaises(generator.Refused):
            generator.generate(broken, "e", {"X": 3})
        with self.assertRaises(generator.Refused):
            generator.generate(_entry(), "e", {"X": 4})

    def test_a_hand_written_module_is_not_overwritten(self):
        with tempfile.TemporaryDirectory() as scratch:
            saved = generator.MODULE_DIR, generator.ROOT
            generator.MODULE_DIR = Path(scratch) / "FormalCerts"
            generator.ROOT = Path(scratch)
            try:
                generator.MODULE_DIR.mkdir()
                (generator.MODULE_DIR / "e.lean").write_text("-- by hand\n")
                with self.assertRaises(generator.Refused):
                    generator.write_module("e", "new\n")
                (generator.MODULE_DIR / "e.lean").write_text(
                    generator.GENERATED_MARK + "\n")
                generator.write_module("e", "new\n")
                self.assertEqual(
                    (generator.MODULE_DIR / "e.lean").read_text(), "new\n")
            finally:
                generator.MODULE_DIR, generator.ROOT = saved

    def test_checker_string_names_version_and_axioms(self):
        self.assertEqual(
            generator.checker_string("leanprover/lean4:v4.35.0",
                                     ["Quot.sound", "propext"]),
            "Lean 4.35.0 (core library, no Mathlib); kernel-checked by lake "
            "build; axioms: Quot.sound, propext")


if __name__ == "__main__":
    unittest.main()
