# Machine (derived transcription and executable consumer)

This directory holds the **derived** side of the repository: a transcription of
the normative specification into machine-readable form, plus the executable
interval consumer, fixtures, and pinned replay. It is **not** normative — where
it disagrees with [`../spec/`](../spec/), the prose wins and this directory is
fixed (`AGENTS.md` *Precedence*).

No soundness claim is established here. `priced_calculus.py` evaluates the
implemented transition subset and propagates distance intervals without
searching for exact distance; its traces are evidence about the interface, not
proofs.

## Layout

- `state.json`, `semantics.json` — transcription of `spec/STATE_MODEL.md`,
  `spec/REPRESENTATION.md`, `spec/TERM_LANGUAGE.md`, and
  `spec/OPERATIONAL_SEMANTICS.md`.
- `consumer.json` — transcription of the interval consumer contract
  (`spec/JUDGMENT_LAYER.md` §§2a–2f, 5).
- `operation_registry.json` — derived index of `spec/TAXONOMY.md` and
  `spec/CLAIMS.md`.
- `priced_calculus.py` — the executable interval consumer.
- `planner.py`, `certificates.py` — consumer-side planning and certificate
  helpers.
- `fixture_conformance.py` — full fixture-conformance evaluator.
- `lean_fixture_coverage.py` — record-by-record conformance against the Lean
  transcription.
- `fixtures/` — `mvp_fixtures.json` (the state-level fixture surface) and
  `qldpc_10_2_3_b.json`.
  (`an archived note`), layout/graft surveys, and recorded reports.
- `test_*.py` — the test suite run by CI (`python -m pytest -q machine/`).
- `requirements.txt` — Python dependencies.

## Run and validate

Python 3.12.

```sh
python -m pip install -r machine/requirements.txt
python -m pytest -q machine/
python3 machine/fixture_conformance.py
```

From the repository root, the documentation lint also checks that every rule
transcribed in `consumer.json` and `semantics.json` carries a `source` resolving
to a `spec/` section naming its operation:

```sh
sh scripts/lint_docs.sh
```

The pinned qLDPC replay additionally needs the challenge repository at a
pinned commit (see [`../README.md`](../README.md)).

## Authority

- [`../spec/`](../spec/) is the source of truth; this directory is derived.
- [`../AGENTS.md`](../AGENTS.md) states the hard rules, including that priced
  hypotheses are inputs rather than computed facts, and that the consumer
  checks input shape, not truth.
- [`../SCOPE.md`](../SCOPE.md) is the stopping point for what the
  calculus and this consumer set out to do.