"""Alignment checks between the Python consumer and the Lean mechanization.

These tests are cheap, deterministic guards that the two sides of the
repository still describe the same object: the pinned identifier enumeration,
the canonical mint, and the proof-discipline invariants (no `sorry`,
`admit`, `axiom`, or `unsafe` in the Lean source).  They do not run Lean;
`lake build` is the authority for that and runs in its own CI job.

The point is to make a silent drift between `machine/priced_calculus.py` and
`lean/CodeCalculus/` fail a fast test instead of being noticed during a
review.
"""

import os
import random
import re
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
LEAN_DIR = os.path.join(ROOT, "lean", "CodeCalculus")
if HERE not in sys.path:
    sys.path.insert(0, HERE)

from priced_calculus import CodeState, IDENTIFIERS


class LeanProofDisciplineTests(unittest.TestCase):
    def test_no_forbidden_proof_tokens_in_lean_source(self):
        forbidden = ("sorry", "admit", "axiom", "unsafe")
        offenders = []
        for name in os.listdir(LEAN_DIR):
            if not name.endswith(".lean"):
                continue
            path = os.path.join(LEAN_DIR, name)
            with open(path) as f:
                text = f.read()
            # Strip block comments (/- ... -/, possibly nested one level) and
            # line comments before scanning, so documentation that names these
            # tokens does not trip the guard.
            text = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
            for lineno, line in enumerate(text.splitlines(), 1):
                code = line.split("--", 1)[0]
                for token in forbidden:
                    if re.search(r"\b" + token + r"\b", code):
                        offenders.append("%s:%d: %s" % (name, lineno, token))
        self.assertEqual(offenders, [],
                         "forbidden proof token in Lean source:\n" + "\n".join(offenders))

    def test_lean_toolchain_and_lakefile_present(self):
        self.assertTrue(os.path.isfile(os.path.join(ROOT, "lean", "lean-toolchain")))
        self.assertTrue(os.path.isfile(os.path.join(ROOT, "lean", "lakefile.toml")))


class IdentifierEnumerationAlignmentTests(unittest.TestCase):
    def _lean_consts(self):
        path = os.path.join(LEAN_DIR, "State.lean")
        with open(path) as f:
            text = f.read()
        prefixes = re.search(r"def identifierPrefixChars : List Char := \[([^\]]*)\]",
                             text).group(1)
        prefixes = [p.strip().strip("'") for p in prefixes.split(",") if p.strip()]
        block = int(re.search(r"def identifiersPerBlock : Nat := (\d+)", text).group(1))
        total = int(re.search(r"def totalIdentifiers : Nat := .*", text).group(0).split(":=")[1].strip()
                    .replace("identifierPrefixChars.length * identifiersPerBlock", str(len(prefixes) * block)))
        # total is computed; recompute to be safe
        total = len(prefixes) * block
        return prefixes, block, total

    def test_prefixes_match_python(self):
        prefixes, block, total = self._lean_consts()
        # Python's block boundaries are the runs of identical leading letter.
        py_prefixes = []
        current = None
        for ident in IDENTIFIERS:
            prefix = "".join(ch for ch in ident if ch.isalpha())
            if prefix != current:
                py_prefixes.append(prefix)
                current = prefix
        self.assertEqual(prefixes, py_prefixes)
        self.assertEqual(block, 10000)
        self.assertEqual(total, len(IDENTIFIERS))

    def test_identifier_at_formula_matches_python(self):
        prefixes, block, total = self._lean_consts()
        # Spot-check every block boundary plus a sample of interior ranks.
        ranks = [0, 1, block - 1, block, block + 1, 2 * block - 1,
                 total - 2, total - 1]
        rng = random.Random(20261110)
        ranks += [rng.randrange(0, total) for _ in range(1000)]
        for rank in ranks:
            block_index = rank // block
            pos = rank % block + 1
            lean_name = prefixes[block_index] + str(pos)
            self.assertEqual(lean_name, IDENTIFIERS[rank],
                             "rank %d" % rank)

    def test_rank_of_string_round_trips_for_sample(self):
        prefixes, block, total = self._lean_consts()
        # Replicate Lean's rankOfChars? for a sample of names.
        rng = random.Random(7)
        for _ in range(500):
            rank = rng.randrange(0, total)
            name = IDENTIFIERS[rank]
            # find block
            block_index = None
            for i, p in enumerate(prefixes):
                if name.startswith(p):
                    block_index = i
                    break
            self.assertIsNotNone(block_index)
            rest = name[len(prefixes[block_index]):]
            idx = int(rest)
            self.assertTrue(1 <= idx <= block)
            self.assertEqual(block_index * block + (idx - 1), rank)


class CanonicalMintAlignmentTests(unittest.TestCase):
    def test_python_mint_is_least_unused_rank(self):
        # Empty state: used empty -> first identifier.
        state = CodeState((), (), frozenset())
        self.assertEqual(state._mint(frozenset()), IDENTIFIERS[0])

    def test_mint_matches_least_unused_for_random_subsets(self):
        rng = random.Random(20261111)
        n = len(IDENTIFIERS)
        for _ in range(200):
            used_size = rng.randrange(0, 40)
            used = set(rng.sample(range(n), used_size))
            used_ids = {IDENTIFIERS[r] for r in used}
            state = CodeState((), (), frozenset(used_ids))
            minted = state._mint(frozenset(used_ids))
            # least rank not in used
            expected_rank = 0
            while expected_rank in used and expected_rank < n:
                expected_rank += 1
            self.assertEqual(minted, IDENTIFIERS[expected_rank])
            self.assertEqual(IDENTIFIERS.index(minted), expected_rank)

    def test_mint_raises_when_exhausted(self):
        # Use a tiny stand-in: monkeypatch by sampling all identifiers is too
        # slow; instead check the method raises on the full set directly.
        all_ids = frozenset(IDENTIFIERS)
        state = CodeState((), (), all_ids)
        with self.assertRaises(Exception):
            state._mint(all_ids)


class FixtureCoverageAlignmentTests(unittest.TestCase):
    def test_coverage_report_has_no_missing_theorems(self):
        import lean_fixture_coverage as lfc
        r = lfc.coverage_report()
        self.assertEqual(r["missing_theorems"], [])
        self.assertEqual(r["lean_uncovered_fixtures"],
                         ["W24", "W25", "W26", "W27", "W28", "W29"])

    def test_eval_replay_module_present(self):
        path = os.path.join(ROOT, "lean", "CodeCalculus", "FixtureEvalReplay.lean")
        self.assertTrue(os.path.isfile(path))
        with open(path) as f:
            text = f.read()
        self.assertIn("theorem fixture_W3_eval", text)
        self.assertIn("theorem fixture_W4_no_eval", text)


if __name__ == "__main__":
    unittest.main()
