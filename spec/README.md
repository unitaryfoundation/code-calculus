# Specification (normative)

> **New here?** Read `REPRESENTATION.md` → `STATE_MODEL.md` → `TERM_LANGUAGE.md`
> → `OPERATIONAL_SEMANTICS.md` → `JUDGMENT_LAYER.md` first; the rest are
> reference material. Every section is authoritative on its own topic, so you
> do not need to read the whole directory. Internal citation keys
> (`proposal §N`, `code-deformation`, etc.) are resolved in
> [`../REFERENCES.md`](../REFERENCES.md).


This directory holds the normative calculus: **one authority per topic**. Where
`machine/` or `lean/` disagree with a file here, this
directory wins and the other artifact is fixed (`AGENTS.md` *Precedence*).

Nothing here is executable or derived. The executable transcription lives in
[`../machine/`](../machine/) (`state.json`, `semantics.json`,
`consumer.json`, `operation_registry.json`); where it disagrees with prose here,
the prose wins and the transcription is fixed.

## Read order

1. [`REPRESENTATION.md`](REPRESENTATION.md) — how a code is written down; the
   assume-spanning contract.
2. [`STATE_MODEL.md`](STATE_MODEL.md) — `C=(Q,X,Z,pres,used)`, invariants
   I1–I5, equality, update ownership.
3. [`TERM_LANGUAGE.md`](TERM_LANGUAGE.md) — grammar, the kernel and in-scope
   `E-GRAFT` transition, the three distinct failure outcomes.
4. [`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) — the partial
   big-step relation, transitions, and the dated hand derivations (§4).
5. [`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) — carry table, conditional prices,
   interval consumer, `unavailable`, the `W13` half.
6. [`CLAIMS.md`](CLAIMS.md) — admission schema, claim/evidence model, outcome
   vocabulary, admission ladder.
7. [`OBLIGATIONS.md`](OBLIGATIONS.md) — every open obligation and its status.
8. [`GATES.md`](GATES.md) — proof gates and non-goals (Gate 0 passed
   2026-10-27; Gate 1 ratified 2026-10-29; Gates 2–7 unchecked).
9. [`VOCABULARY.md`](VOCABULARY.md) — controlled vocabulary; use these terms
   exactly.
10. [`TAXONOMY.md`](TAXONOMY.md) — operation inventory, stable IDs, extension
    boundary.
11. [`VERSIONING.md`](VERSIONING.md) — releases, compatibility policy, tracked
    obligation set.

## Authority and editing

- Decisions and their reasons live in [`../CHANGELOG.md`](../CHANGELOG.md), not amended
  into the artifact they concern. A qualification that changes how a claim must
  be read stays where the claim is; history moves to the diary.
- Claim-status discipline: `established` only when its derivation or citation
  is in the repository; classical facts awaiting evidence read `proposed
  (classical)`. The evidence vocabulary (`proved`, `conditional`, `empirical`,
  `conjectural`, `open`, `not-applicable`) is defined in
  [`CLAIMS.md`](CLAIMS.md) and is not redefined here.
- The four-outcome vocabulary is exact: **false** / **not derivable** /
  **unavailable** / **not yet defined**.
- Markdown is linted from the repository root: `sh scripts/lint_docs.sh`
  (link resolution, taxonomy-ID definitions, obligation-name definitions, and
  transcription `source` resolution).
- Cross-reference by relative link and section name, not by line number.

## References and citation keys

Shorthand citations used throughout this directory (`proposal §N`, `code-deformation`,
`manuscript`, `an archived internal note`) are resolved in
[`../REFERENCES.md`](../REFERENCES.md). None of those sources is shipped here;
the calculus is stated so that its normative content does not depend on them.

## What is *not* here

- Mechanization: [`../lean/`](../lean/) (partial; certifies only the theorems
  it states).
- Executable consumer and fixtures: [`../machine/`](../machine/).
- Root framing, process, and authority: [`../README.md`](../README.md),
  [`../AGENTS.md`](../AGENTS.md), [`../AUTHORITY.md`](../AUTHORITY.md).