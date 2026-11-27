# AGENTS.md — public contributor notes

This is the public, sanitized version of the repository's agent/contributor
notes. Internal red-team records, issue numbers, and branch names are omitted.

## Read first

1. [`README.md`](README.md)
2. [`CONTRIBUTING.md`](CONTRIBUTING.md)
3. [`spec/GATES.md`](spec/GATES.md) and [`spec/VERSIONING.md`](spec/VERSIONING.md)
4. [`spec/VOCABULARY.md`](spec/VOCABULARY.md)
5. [`AXIOMS.md`](AXIOMS.md)

## Hard rules

- Never claim a proof. Agreement between an example and a rule is evidence,
 never confirmation.
- Do not discharge a proof obligation with an axiom or `sorry`. The audited
 `CodeCalculus` library must build with `0 sorry` and no new axioms;
 `AXIOMS.md` records the accepted assumptions, and none remain.
- Do not merge pull requests, create tags, or publish without maintainer
 approval.
- `spec/` wins every disagreement with `machine/` and `lean/`.
- Decisions are recorded in pull requests or release notes (`CHANGELOG.md`).

## Validation

Run from the repository root:

```sh
sh scripts/lint_docs.sh
PYTHONPYCACHEPREFIX=/private/tmp/code-calculus-pycache python3 -m unittest discover -s machine
python3 machine/fixture_conformance.py
cd lean && lake build
```