# code-calculus

A formal calculus of CSS-code transformations and priced construction moves: a
typed term language, a partial operational semantics, and a consumer-side
interval ledger that carries distance bounds through construction steps and
requests re-measurement only when the current bounds cannot decide a target.

**Status: research artifact, Apache 2.0.** The formal calculus and its soundness
theorem are the research objective; no soundness claim is machine-proved in
full. The repository contains the normative specification (`spec/`), an
executable consumer for the admitted transition subset (`machine/`), and partial
Lean mechanization (`lean/`). The consumer is evidence about whether the
interface is useful; it does not establish the calculus soundness theorem. See
`SCOPE.md` for the stopping point and `spec/GATES.md` for what is and is not
claimed.

## Run and reproduce

Python 3.12.

```sh
python -m pip install -r machine/requirements.txt
sh scripts/lint_docs.sh
python -m pytest -q machine/
python3 machine/fixture_conformance.py
```

Lean (toolchain pinned in `lean/lean-toolchain`):

```sh
cd lean && lake build
```

## Layout

Four layers. One authority per topic: the same fact is not stated twice.

| Layer | Holds | Authority |
| --- | --- | --- |
| [`spec/`](spec/) | Normative calculus: representation, state model, term language, operational semantics, judgment layer, claims, obligations | Wins every disagreement |
| [`machine/`](machine/) | `state.json`, `semantics.json`, `consumer.json`, executable interval consumer, fixtures, pinned replay | Derived; where it disagrees with prose, prose wins and the transcription is fixed |

`CHANGELOG.md` is the dated record of what was decided, when, and why. Root
holds framing and process: `AGENTS.md`, `AUTHORITY.md`, `spec/VOCABULARY.md`,
`spec/CLAIMS.md`, `spec/VERSIONING.md`, and `spec/TAXONOMY.md`.

## Status

- The five-operation kernel is specified, with conditional construction cells
  for priced `C-DELETE-CHECK`, `E-GRAFT`, and strict improvement under
  `C-ADD-CHECK`. The Gate 6 CSS-level extensions `E-GLUE`, `E-PUNCTURE`,
  `E-PEEL`, `E-EXTEND`, `E-LOCAL-HADAMARD`, and `P-REBASE` are in scope as
  conditional cells; their transitions and soundness obligations are tracked by
  `OBL-GATE6-CSS-EXTENSIONS`. The tower factorization in `A-CONCAT` is a price
  provider, not a calculus constructor.
- `machine/priced_calculus.py` evaluates the implemented transition subset and
  propagates distance intervals without searching for exact distance. The
  adapter exports witness-backed `upper_bound` claims only.
- Every obligation named as in scope by `SCOPE.md` has a dated hand derivation
  in `spec/OPERATIONAL_SEMANTICS.md` §4; the ledger is
  `spec/OBLIGATIONS.md`. A hand derivation is evidence in the repository, not a
  machine-checked result.
- Machine-checked soundness is not claimed. `OBL-JUDGMENT-SOUNDNESS` is `proved`
  by hand derivation; its Lean form is stated for a well-formed evaluation chain
  with the evaluation assumed, and the `k` and distance cells enter it as
  hypotheses. What is proved, what is mechanized under which hypotheses, and what
  is not established is summarized in `spec/VERSIONING.md`.

The project's stopping point is `SCOPE.md`. The calculus is intended to be
sound and deliberately incomplete: `unavailable` is withheld by design
commitment, and no artifact describes it as aiming at completeness in the MVP.
Soundness remains an open proof obligation.

## Start here

- Agents: `AGENTS.md` — read order, hard rules, and what to grep when you
  change something. Decisions belong in `CHANGELOG.md`, not amended into the
  artifact they concern.
- Humans: `spec/REPRESENTATION.md` for the construction and interval-ledger
  proposal, then `spec/OPERATIONAL_SEMANTICS.md` for transitions and
  `spec/JUDGMENT_LAYER.md` for conditional price cells and target decisions.
- Consistency check: `sh scripts/lint_docs.sh` checks link resolution,
  taxonomy-ID definitions, obligation-name definitions, and the normative
  `source` of every rule transcribed in `machine/consumer.json` and
  `machine/semantics.json`.

## Provenance

Seeded from an earlier proposal draft; this copy is the living document. The
formal-design packages FD0–FD7 are closed, and their artifacts are superseded by
`spec/`.

## Gates

Gate 0 and Gate 1 are ratified; Gates 2–7 are unchecked. See
`spec/GATES.md` for the authoritative gate statements and non-goals.

## Non-goals

No complete move set, no target family, no completeness theorem, no inferability
claim, no unconditional exact deletion distance, no circuit realizations, no
DEM-level distance equality, no software code generator, and no load-bearing
category theory.

The Lean development under `lean/` is partial and certifies nothing beyond the
theorems it states (`lean/README.md`). The executable consumer is a discovery
aid whose hypotheses remain explicit and whose traces do not prove soundness.
See `spec/VERSIONING.md`.

## Research program

The project develops a formal language for composing and deforming CSS codes:
syntax for which transformations can be written, an operational semantics for
which transformations are valid and what states they produce, and a judgment
layer for what can be proved about those transformations. Realization questions
remain outside the initial calculus.

The planning MVP specifies four code-level operations: direct sum of disjoint
codes (`C-DIRECT-SUM`), single-stabilizer deletion (`C-DELETE-CHECK`),
single-stabilizer addition (`C-ADD-CHECK`), and sequential composition
(`C-SEQUENCE`). The companion taxonomy in `spec/TAXONOMY.md` records the
broader operation space. The calculus distinguishes valid construction from
property claims; deletion-distance lower bounds and equalities are unavailable
in the MVP, while the non-increase upper bound is an included claim.

The stopping point, in-scope cells, and obligation set are stated in
`SCOPE.md`.
