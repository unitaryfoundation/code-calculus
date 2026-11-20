"""Regression tests for the CI changed-path classifier."""

import unittest

from ci_path_filter import classify_changed_paths


class ChangedPathFilterTests(unittest.TestCase):
    def test_empty_or_documentation_only_changes_skip_code_checks(self):
        expected = {"code": False, "lean": False, "pinned": False}
        self.assertEqual(classify_changed_paths([]), expected)
        self.assertEqual(classify_changed_paths(["README.md", "docs/note.md"]), expected)

    def test_code_paths_enable_python_checks(self):
        for path in (
            "machine/test_priced_calculus.py",
            "scripts/lint_docs.sh",
            "docs/ablation/result.md",
        ):
            with self.subTest(path=path):
                self.assertEqual(
                    classify_changed_paths([path]),
                    {"code": True, "lean": False, "pinned": False},
                )

    def test_lean_inputs_enable_lean_build(self):
        for path in (
            "lean/CodeCalculus.lean",
            "spec/OPERATIONAL_SEMANTICS.md",
            "machine/fixtures/mvp_fixtures.json",
        ):
            with self.subTest(path=path):
                result = classify_changed_paths([path])
                self.assertTrue(result["code"])
                self.assertTrue(result["lean"])

    def test_pinned_replay_inputs_enable_integration_replay(self):
        for path in (
            "machine/experiments/issue21_challenge_replay.py",
            "machine/experiments/issue21_challenge_replay.json",
        ):
            with self.subTest(path=path):
                self.assertEqual(
                    classify_changed_paths([path]),
                    {"code": True, "lean": False, "pinned": True},
                )

    def test_consumer_modules_trigger_replay_but_tests_and_other_experiments_do_not(self):
        for path in ("machine/priced_calculus.py", "machine/state.py", "machine/oracle.py"):
            with self.subTest(path=path):
                self.assertTrue(classify_changed_paths([path])["pinned"])
        for path in (
            "machine/test_priced_calculus.py",
            "machine/experiments/layout_conformance_harness.py",
        ):
            with self.subTest(path=path):
                self.assertFalse(classify_changed_paths([path])["pinned"])

    def test_renames_out_of_watched_directory_still_trigger_via_old_path(self):
        # With --no-renames both the old and new paths are listed, so the
        # consumer module's old path keeps the filters true.
        result = classify_changed_paths(["machine/oracle.py", "docs/oracle.py"])
        self.assertTrue(result["code"])
        self.assertTrue(result["pinned"])

    def test_workflow_and_requirements_changes_trigger_pinned_replay(self):
        for path in (
            ".github/workflows/ci.yml",
            ".github/workflows/weekly.yml",
            ".github/workflows/release.yml",
            "machine/requirements.txt",
        ):
            with self.subTest(path=path):
                self.assertTrue(classify_changed_paths([path])["pinned"])


if __name__ == "__main__":
    unittest.main()
