# AGENTS.md — public contributor notes

This is the public, sanitized version of the repository's agent/contributor
notes. Internal red-team records, issue numbers, and branch names are omitted.

## Read first

1. [`README.md`](README.md)
2. [`CONTRIBUTING.md`](CONTRIBUTING.md)
3. [`SCOPE.md`](SCOPE.md)
4. [`../spec/VOCABULARY.md`](spec/VOCABULARY.md)

## Hard rules

- Never claim a proof. Agreement between an example and a rule is evidence,
  never confirmation.
- Do not merge pull requests, create tags, or publish without maintainer
  approval.
- `spec/` wins every disagreement with `machine/`.
- Decisions are recorded in pull requests or release notes.

## Validation

Run from the repository root:

```sh
sh scripts/lint_docs.sh
PYTHONPYCACHEPREFIX=/tmp/code-calculus-pycache python3 -m unittest machine.test_priced_calculus -v
```