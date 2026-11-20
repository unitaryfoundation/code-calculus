"""Classify changed paths for the selective GitHub Actions jobs."""

from collections.abc import Iterable
import sys


CODE_PREFIXES = (
    "machine/",
    "spec/",
    "lean/",
    "scripts/",
    "docs/ablation/",
    ".github/workflows/",
)
LEAN_PREFIXES = ("lean/", "spec/")
PINNED_REPLAY_PATHS = {
    "machine/experiments/issue21_challenge_replay.py",
    "machine/experiments/issue21_challenge_replay.json",
}
# Workflows that carry the pinned qLDPC challenge commit and the numpy pin.
PINNED_WORKFLOW_PATHS = {
    ".github/workflows/ci.yml",
    ".github/workflows/weekly.yml",
    ".github/workflows/release.yml",
}
FIXTURE_PATH = "machine/fixtures/mvp_fixtures.json"
REQUIREMENTS_PATH = "machine/requirements.txt"


def _is_pinned_replay_path(path: str) -> bool:
    # The replay imports the top-level runtime modules through priced_calculus
    # and oracle; unit tests and unrelated experiment scripts do not need it.
    if path in PINNED_REPLAY_PATHS:
        return True
    if path in PINNED_WORKFLOW_PATHS:
        return True
    if path == REQUIREMENTS_PATH:
        return True
    if not path.startswith("machine/") or not path.endswith(".py"):
        return False
    module_path = path.removeprefix("machine/")
    return "/" not in module_path and not module_path.startswith("test_")


def classify_changed_paths(paths: Iterable[str]) -> dict[str, bool]:
    """Return the CI path-filter outputs for a set of repository paths."""
    changed = tuple(path.strip() for path in paths if path.strip())
    return {
        "code": any(path.startswith(CODE_PREFIXES) for path in changed),
        "lean": any(
            path.startswith(LEAN_PREFIXES) or path == FIXTURE_PATH
            for path in changed
        ),
        "pinned": any(_is_pinned_replay_path(path) for path in changed),
    }


def main() -> None:
    for name, enabled in classify_changed_paths(sys.stdin.read().splitlines()).items():
        print(f"{name}={'true' if enabled else 'false'}")


if __name__ == "__main__":
    main()
