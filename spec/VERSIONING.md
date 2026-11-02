# Versioning the CSS-Code Calculus

**Status:** versioning scheme and compatibility policy. This note owns
*release-level* version facts: the version model, release identity, the
compatibility policy, and the release table. *Item-level* version facts
(`introduced-in`, `discharged-through`) are owned by the file that owns the item
— the proposal grammar, [`CLAIMS.md`](CLAIMS.md), and
[`OBLIGATIONS.md`](OBLIGATIONS.md) — and this note
references them by pointer only, never by restatement. It records version axes;
neither a release row nor an executable artifact establishes soundness.

## 1. Purpose

The calculus is developed in **releases**, like a software tool: the term language
is expanded, the assertion language grows, and more properties are formalized,
each without a wholesale rewrite. This note defines what a release is, how
releases are named, and what a new release must preserve. It records design
commitments only.

## 2. Version model — four axes

A release pins one value on each of four **independent axes**:

1. **State model** — the mathematical object being transformed.
2. **Operation set / term language** — the admitted productions and commands.
3. **Assertion and judgment language** — what the calculus may state and derive.
4. **Obligation and proof set** — which proof obligations are discharged.

Syntax and semantics are *not* separate axes: an operation's syntax and semantics
are specified together by its semantic contract.

The axes change at different rates. Expanding the term language changes axis 2;
formalizing a further property changes axis 3, and usually axis 4, **without**
touching axis 2. A release records all four, so an axis-3-only change is visible
as such.

## 3. Release identity

A release is named `<line>-<ordinal>`.

- **Line** — the state model. `stdCSS` is the phase-insensitive standard-CSS line
 ([`STATE_MODEL.md`](STATE_MODEL.md)).
- **Ordinal** — within a line: increment for a conservative language or assertion
 addition; a patch level for an obligation- or proof-only change; a markedly
 rarer in-line erratum otherwise (§4).

The current development release is `stdCSS-2`; `MVP` remains an alias for the
historical `stdCSS-1` baseline. The release table records both axis sets.

`stdCSS-1` axes:

| Axis | `stdCSS-1` value |
| --- | --- |
| State model | phase-insensitive standard CSS |
| Operation set | `C-SKIP`, `C-DIRECT-SUM`, `C-DELETE-CHECK`, `C-ADD-CHECK`, `C-SEQUENCE` |
| Assertion language | the research proposal (see REFERENCES.md): $n$, $k$, $d_X$, $d_Z$; $=$, $\leq$, $\geq$; structural predicates; finite conjunction |
| Obligation set | the Gate 0–5 targets tracked in [`OBLIGATIONS.md`](OBLIGATIONS.md) |

**Item-level convention:** absence of an `introduced-in` field means `stdCSS-1`
(§6). Existing artifacts are not retro-tagged.

## 4. Compatibility policy

**Within a line, development is conservative:** a release adds syntax, assertions,
or proofs and does not change any existing derivation.

**Across lines there is no supersession:** a new state model (for example a future
subsystem line) is a *separate* line, not an upgrade of an existing one.
Interaction between lines requires an explicit **embedding/migration relation**,
itself a versioned artifact. This matches
[`spec/TAXONOMY.md`](TAXONOMY.md) §4, where extended-state operations require
a state model beyond ordinary CSS stabilizer codes and are deferred, not
abandoned.

**Metatheorems are scoped to a release's operation set, and a bump is never free.**

- A metatheorem — a statement about the calculus's own transition system — is
 written for a specific release's operation set (for example soundness over the
 `C-*` operations for `stdCSS-1`).
- Adding an operation is conservative for **existing derivations** (nothing in the
 old release mentions it) but can falsify or restrict a metatheorem that
 quantified over all operations.
- Every release bump therefore creates a **re-discharge obligation**: re-establish
 each affected metatheorem against the expanded operation set, by extending it or
 by restricting its statement explicitly.
- Only **derivation-level** compatibility is guaranteed across a bump.
 Metatheorems are *not* guaranteed to survive a bump unchanged.

A metatheorem entry records its discharge with `discharged-through`; the field
does not advance until the re-proof lands, so the entry's status reverts toward
`open` on each bump. The per-release discharge history is the release table (§5).

The evidence-status vocabulary is part of the assertion-language axis. A future
release may extend it with the reserved status `certificate-checked` (a
machine-checked certificate from an external search whose translation is
verified in the proof assistant; see `spec/CLAIMS.md`, *Reserved future
status*). Extending the vocabulary is an assertion-language change and
therefore requires a new release row, never a silent edit.

The claim-shape vocabulary gained the `probabilistic` (delta-bounded) shape on
2026-10-27: a claim about a search, not a lower-bound certificate.
It is an assertion-language-axis change and ships as a release note only; no
release row is re-numbered by it, and it never upgrades `unavailable` to
`proved`.

## 5. Release table

Per release: its four-axis pin, operation set, and the obligations and gates it
discharged.

| Release | State model | Operation set | Discharged | Notes |
| --- | --- | --- | --- | --- |
| `stdCSS-1` (`MVP`) | phase-insensitive standard CSS | `C-SKIP`, `C-DIRECT-SUM`, `C-DELETE-CHECK`, `C-ADD-CHECK`, `C-SEQUENCE` | planning targets: Gates 0–5 ([`OBLIGATIONS.md`](OBLIGATIONS.md)); parameter derivations in [`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4 | historical five-primitive baseline |
| `stdCSS-2` | same state model | `stdCSS-1` operations plus the in-scope `E-GRAFT` production, at `transition-defined` | `OBL-GRAFT-TRANSITION-SOUNDNESS` (§4.12), `OBL-PRICED-INTERVAL-SOUNDNESS` (§4.13, under the corrected E-GRAFT rules) and `OBL-PRICED-INPUT-SEMANTICS` (§4.14) are discharged by hand derivation; the source derivations for the conditional cells are reproduced at §4.19 | adds the conditional judgment-input schema for full-distance deletion price, graft exposure price, and strict improvement. `E-GRAFT` is not state-sound and is not claimed as a proved rule. Current development release; the interval-transport metatheorem is `proved` under the corrected E-GRAFT rules (§4.13, 2026-10-21), while the judgment soundness metatheorem `OBL-JUDGMENT-SOUNDNESS` remains open. |

A future release appends a row. Rows are not edited after the fact; a changed
release is a new row.

**Dated note.** `OBL-PRICED-INTERVAL-SOUNDNESS` flips to
`proved` under the corrected E-GRAFT rules (§4.13); `OBL-GRAFT-TRANSITION-
SOUNDNESS` (§4.12) and `OBL-PRICED-INPUT-SEMANTICS` (§4.14) were already
proved on `main`. The conditional-cell source derivations are reproduced at
§4.19. The `stdCSS-2` row above records the release as it stood; the
discharge is recorded here and in `spec/OBLIGATIONS.md` rather than by
rewriting the row, because `stdCSS-2` is the current development release and
has not shipped.

**Dated note.** The interaction radius $r$ is an
axis-3 (property) addition with no axis-2 (term-language) change. On the
`w` precedent it is recorded here rather than as a new row: `stdCSS-2`
remains the current development release and axis 4 (ordinal) is unchanged.
Axis 3 additions that do not change the term language are thus visible in
these dated notes rather than in the table, consistent with the `w`
addition.

**Dated note.** The `stdCSS-2` row above is not
edited. Its closing clause says `OBL-JUDGMENT-SOUNDNESS` "remains open"; that
wording records the release as it stood, and the current ledger status is
superseded here: the metatheorem is `proved` by hand derivation (§4.11,
2026-10-20), and its Lean mechanization is partial. The first slice
(`lean/CodeCalculus/Soundness.lean`) proves the `⊨` half for a well-formed
evaluation chain, with the `Eval` conjunct assumed rather than proved, for
skip's identity and the `n` cells of deletion, addition, and the graft; the
distance monotonicity/bounds and `k`/well-formedness cells are later slices.
Scope and evidence status are recorded at
[`OBLIGATIONS.md`](OBLIGATIONS.md), `OBL-JUDGMENT-SOUNDNESS`.



**Dated note.** A `v0.1` release is
prepared but **not tagged**: the maintainer decides when to tag. Its four-axis
pin, as the tree stands at `f030b61`, is:

- **Line / state model:** `stdCSS-2` (phase-insensitive standard CSS; finite
 70,000-name identifier namespace per WP3).
- **Operation set:** `stdCSS-1` operations plus `E-GRAFT` (conditional) and
 the six Gate 6 CSS-level conditional cells (`E-GLUE`, `E-PEEL`,
 `E-PUNCTURE`, `E-EXTEND`, `E-LOCAL-HADAMARD`, `P-REBASE`), at their recorded
 rungs; `E-GLUE` remains without a unary grammar production.
- **Assertion language:** the research proposal (see REFERENCES.md): $n$, $k$, $d_X$, $d_Z$, $d$, $w$,
 $r$; $=$, $\leq$, $\geq$; structural predicates; finite conjunction; plus
 the Gate 6 structural effects of §4.26–§4.30.
- **Obligation set:** Gates 0 and 1 (ratified
 2026-10-29); `OBL-GATE6-CSS-EXTENSIONS` discharged (§4.32, 2026-10-28);
 `OBL-JUDGMENT-SOUNDNESS` proved by hand derivation (§4.11) with partial
 Lean mechanization; the measure-monotonicity hypothesis discharged for the exact sector
 distance. Gates 2–7 remain unchecked by design.

**Re-discharge obligations created by this release** (per §3): every
metatheorem scoped to the `stdCSS-1` operation set must be re-established
against the expanded operation set before its `discharged-through` advances;
in particular the Gate 6 metatheorems remain conditional cells, not admitted
rules, and the refined §4.31 soundness statement is not mechanized. When the maintainer tags, this note
is replaced by an appended release row (rows are not edited after the fact)
and the `discharged-through` values are updated in the same change.

**Not included in v0.1 (by decision, not omission):** exact-distance
computation as a calculus move; heuristic search results presented as lower
bounds; the Lean mechanization of the §4.31 transformers and of `E-GLUE`;
Gates 2–7 ratification; the v0.2 candidate items (tracked in the  tracker).

## 6. Item-level conventions and owners

Declared here; applied where each item is owned.

- **`introduced-in`** — the release that first admitted the item. Absent means
 `stdCSS-1`.
- **`discharged-through`** — the latest release for which the item's proof has
 been (re-)established.

| Fact | Owner |
| --- | --- |
| grammar production introduction | an archived internal note §3.2 |
| contract admission | [`CLAIMS.md`](CLAIMS.md) |
| obligation introduction and discharge | [`OBLIGATIONS.md`](OBLIGATIONS.md) |

This note references those files; it does not restate their contents.

## 7. Non-goals

- no retrofit of `stdCSS-1` tags onto existing entries;
- no mechanization in the current phase;
- no single global version counter and no per-layer counters beyond the
 line/ordinal scheme.

**Dated note.** The six Gate 6 CSS-level productions
(`P-REBASE`, `E-LOCAL-HADAMARD`, `E-PEEL`, `E-PUNCTURE`, `E-EXTEND`,
`E-GLUE`) are in scope as conditional cells under `stdCSS-2` (admitted
2026-10-23). Their addition creates re-discharge obligations for the
metatheorems scoped to the `stdCSS-2` operation set: each affected
metatheorem's `discharged-through` does not advance until it is re-established
against the expanded operation set. The six rows are recorded in the
update-ownership table of `spec/STATE_MODEL.md` §4 and `machine/state.json`.
