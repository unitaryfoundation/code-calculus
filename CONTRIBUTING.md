# Contributing

This repository is a formal-design research artifact with an executable
consumer prototype. Contributions are welcome, but please read these notes
first.

## Before you start

- Read `README.md`, `SCOPE.md`, and `spec/VERSIONING.md`. The stopping
  point in `SCOPE.md` is the canonical statement of scope; work outside it
  should be proposed as a design note first.
- `spec/` is normative and wins every disagreement. `machine/` is a derived
  transcription; where it disagrees with `spec/`, `spec/` wins and the
  transcription is fixed.
- Decisions are recorded in the pull request or release notes, not in the artifact they concern.

## How to contribute

1. Open an issue describing the change before large work.
2. Branch from `main`; keep changes focused (one concern per branch/PR).
3. Run `sh scripts/lint_docs.sh` and `python -m pytest -q machine/` before
   submitting.
4. Open a pull request; maintainers review and merge. Do not merge your own PR.

## Normative changes

Changes to `spec/`, claim statuses, gates, or scope require a
pull request with one approving review and a dated decision record (pull request description or release note).

## License

By contributing, you agree your contributions are licensed under the Apache
License, Version 2.0 (see `LICENSE`).
