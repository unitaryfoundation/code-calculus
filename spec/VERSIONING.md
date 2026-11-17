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

The current development release is `stdCSS-3` (software `v0.2.0`, prepared
2026-11-14 and not yet tagged; `v0.1` shipped at commit `078cab2` on
2026-11-02); `MVP` remains an alias for the historical `stdCSS-1` baseline. The
release table records all axis sets.

`stdCSS-1` axes:

| Axis | `stdCSS-1` value |
| --- | --- |
| State model | phase-insensitive standard CSS |
| Operation set | `C-SKIP`, `C-DIRECT-SUM`, `C-DELETE-CHECK`, `C-ADD-CHECK`, `C-SEQUENCE` |
| Assertion language | proposal §5–§6: $n$, $k$, $d_X$, $d_Z$; $=$, $\leq$, $\geq$; structural predicates; finite conjunction |
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
therefore requires a new release row, never a silent edit. On 2026-11-11
(issue #329) the status was admitted to the `stdCSS-3` candidate (§5.1) for
per-state atomic judgments, conditional on a mechanized certificate checker.
The checker landed 2026-11-11 (issue #371,
`lean/CodeCalculus/CertificateChecker.lean`). The status ships with that
row: until then it is carried only by the candidate's per-state Lean
theorems, and by no claim of `stdCSS-2` (`spec/CLAIMS.md`, *Admission* and
*Mechanized checker*).

The claim-shape vocabulary gained the `probabilistic` (delta-bounded) shape on
2026-10-27: a claim about a search, not a lower-bound certificate.
It is an assertion-language-axis change and ships as a release note only; no
release row is re-numbered by it, and it never upgrades `unavailable` to
`proved`. On 2026-11-11 (issue #329) the shape was admitted as the recorded
form of heuristic search outcomes (`spec/CLAIMS.md`, *Admission*): a dated
note on the current ordinal, since the shape already exists; the record
licenses no endpoint.

### 4.1 Bump criteria (calculus line)

A change's **bump** is determined by which axes it touches, not by its size.
The table is exhaustive; if a change does not fit a row, it is not yet a
release and needs a `DIARY.md` disposition first.

| Change | Axis touched | Bump | Notes |
| --- | --- | --- | --- |
| New state model (e.g. phase-sensitive or extended-state CSS) | 1 | new **line** | No supersession; requires an embedding/migration relation (§4). |
| New admitted operation or grammar production; new conditional cell admitted as `transition-defined` | 2 | new **ordinal** within the line | Creates re-discharge obligations for every metatheorem scoped to the old operation set (§4). |
| New assertion or judgment vocabulary; new evidence-status or claim-shape label (e.g. `certificate-checked`, `probabilistic`) | 3 | new **ordinal** within the line | Visible as an axis-3 change even with no axis-2 change. |
| New property added to the inventory ($w$, $r$, …) with no term-language change | 3 | **dated note** only, no new row | On the `w`/`r` precedent; the ordinal is unchanged. |
| Obligation discharged; proof landed; `discharged-through` advances | 4 | **patch level** within the ordinal | Proof-only; no new derivation is invalidated. |
| Hand derivation corrected in a way that changes what it asserts | 4 (erratum) | rare **in-line erratum** | Recorded in the dated notes, not as a new row, unless it alters an admitted rule. |
| Transcription fix in `machine/` or `lean/` that changes no admitted semantics | none | **no bump** | Transcription is derived; prose wins (AGENTS.md). |
| Machine-only provider work (new enumerator, benchmark, planner mode) | none | **no bump** | Explicit non-goal (§7). |

A bump is never free: every new ordinal re-opens the re-discharge obligations
of §4, and `discharged-through` does not advance until the re-proof lands.

## 5. Release table

Per release: its four-axis pin, operation set, and the obligations and gates it
discharged.

| Release | State model | Operation set | Discharged | Notes |
| --- | --- | --- | --- | --- |
| `stdCSS-1` (`MVP`) | phase-insensitive standard CSS | `C-SKIP`, `C-DIRECT-SUM`, `C-DELETE-CHECK`, `C-ADD-CHECK`, `C-SEQUENCE` | planning targets: Gates 0–5 ([`OBLIGATIONS.md`](OBLIGATIONS.md)); parameter derivations in [`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4 | historical five-primitive baseline |
| `stdCSS-2` | same state model | `stdCSS-1` operations plus the in-scope `E-GRAFT` production, at `transition-defined` | `OBL-GRAFT-TRANSITION-SOUNDNESS` (§4.12), `OBL-PRICED-INTERVAL-SOUNDNESS` (§4.13, under the corrected E-GRAFT rules) and `OBL-PRICED-INPUT-SEMANTICS` (§4.14) are discharged by hand derivation; the source derivations for the conditional cells are reproduced at §4.19 | adds the conditional judgment-input schema for full-distance deletion price, graft exposure price, and strict improvement. `E-GRAFT` is not state-sound and is not claimed as a proved rule. Current development release; the interval-transport metatheorem is `proved` under the corrected E-GRAFT rules (§4.13, 2026-10-21), while the judgment soundness metatheorem `OBL-JUDGMENT-SOUNDNESS` remains open. |
| `v0.1.0` (software release of `stdCSS-2`) | phase-insensitive standard CSS (`stdCSS-2`) | `stdCSS-1` operations plus `E-GRAFT` (conditional) and the six Gate 6 CSS-level conditional cells (`E-GLUE`, `E-PEEL`, `E-PUNCTURE`, `E-EXTEND`, `E-LOCAL-HADAMARD`, `P-REBASE`), at their recorded rungs; `E-GLUE` has no unary grammar production | Gates 0 and 1 ratified (2026-10-29); `OBL-GATE6-CSS-EXTENSIONS` discharged (§4.32, 2026-10-28); `OBL-JUDGMENT-SOUNDNESS` proved by hand derivation (§4.11) with partial Lean mechanization; measure-monotonicity hypothesis discharged for the exact sector distance | Prepared 2026-11-10 at commit `1afc766`; not yet tagged. Gates 2–7 unchecked by design. Re-discharge obligations of §3/§4 remain open until the re-proofs land; `discharged-through` values are not advanced by this preparation. |
| `stdCSS-3` / `v0.2.0` | phase-insensitive standard CSS (`stdCSS-2` state model) | `stdCSS-2` operations plus the `stdCSS-3` candidate scope of §5.1: the distance-increasing constructors (`L-HGP`, `L-LIFTED`, `L-GROUP-ALGEBRA`, `A-CONCAT`, `L-BALANCED`, `L-TANNER`, `L-TILE`, `A-PRODUCT`, `A-DOUBLE`), `L-NESTED-CSS`, layout-transfer cells, puncturing/peeling price cells, `E-GLUE` promotion with seam-certificate equality, `E-LOCAL-HADAMARD` sector-swap support, W13 half, and the admitted heuristic statuses; `E-GLUE` retains no unary grammar production | Gates 0 and 1 ratified; `OBL-GATE6-CSS-EXTENSIONS` discharged (§4.32); `OBL-JUDGMENT-SOUNDNESS` proved by hand (§4.11) with partial Lean mechanization; `discharged-through` values **not advanced** — re-discharge obligations of §4 remain open until the re-proofs land | **Prepared 2026-11-14 (issue #441, "prepare but do not tag"):** candidate scope of §5.1 staged as a release row; not tagged. Gates 2–7 unchecked by design. Rows are not edited after the fact; a changed release is a new row. |

**Dated note (2026-11-14, issue #441).** The `stdCSS-3` / `v0.2.0` release
row above is **prepared but not tagged** ("prepare but do not tag"): it stages
the §5.1 candidate scope as a release row and records that
`discharged-through` values are not advanced. Tagging and appending the final
tag record remain maintainer-only actions (AGENTS.md *Hard rules*); the row is
not edited after the fact, and a changed release is a new row.

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
pin, as the tree stands at `1afc766`, is:

- **Line / state model:** `stdCSS-2` (phase-insensitive standard CSS; finite
 70,000-name identifier namespace per WP3).
- **Operation set:** `stdCSS-1` operations plus `E-GRAFT` (conditional) and
 the six Gate 6 CSS-level conditional cells (`E-GLUE`, `E-PEEL`,
 `E-PUNCTURE`, `E-EXTEND`, `E-LOCAL-HADAMARD`, `P-REBASE`), at their recorded
 rungs; `E-GLUE` remains without a unary grammar production.
- **Assertion language:** proposal §5–§6: $n$, $k$, $d_X$, $d_Z$, $d$, $w$,
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
rules, and the §4.32 soundness statement is mechanized only conditional on
the §4.26 to §4.30 distance relations (`lean/CodeCalculus/Gate6Soundness.lean`,
issue #311). **Preparation (2026-11-10).** The release row for `v0.1.0` has been appended to
the table in §5 (prepared at commit `1afc766`); it is not yet a tagged release.
The `discharged-through` values are not advanced by this preparation and remain
to be updated at tag time, together with the final tag push. When the maintainer
tags, this note is replaced by the tagged-release record (rows are not edited
after the fact).

**Not included in v0.1 (by decision, not omission):** exact-distance
computation as a calculus move; heuristic search results presented as lower
bounds; the Lean mechanization of the §4.31 transformers (the `E-GLUE`
constructor now exists, but its refined transformer remains open); the Lean
discharge of the §4.28 peel relations and of the `k = 0` reading for the
exact distance; Gates 2–7 ratification; the v0.2 candidate items (tracked
in the issue tracker).

**Dated note (2026-11-12).** The `v0.1` release recorded above as "prepared
but not tagged" has shipped: public tag `v0.1` at commit `078cab2`
(2026-11-02). The prepared-pin note is superseded by this release record; the
row itself is not rewritten, per §5. The four-axis pin above is the released
pin. `discharged-through` values remain as recorded until the `v0.2` release.

## 5.1 Candidate next release (`stdCSS-3` / software `v0.2.0`)

**Status: prepared in §5 (2026-11-14, issue #441), not yet tagged.** Nothing
below was owed by the stopping point (`design/SCOPE.md` §3). Each item required
a `DIARY.md` disposition before implementation; that disposition landed
2026-11-10 (issues #312–#316), accepting the items listed below (weight-3
exposure accepted as an investigation; heuristic status accepted as both
`probabilistic` and `certificate-checked`). The `stdCSS-3` / `v0.2.0` row is
staged in the release table (§5) under the "prepare but do not tag" decision
(issue #441), and `discharged-through` values are not advanced until the
re-proofs land (§4).

**Intended calculus-side scope (axes 3/4, and axis 2 where noted):**

- Mechanization of the refined Gate 6 soundness statement (§4.31
  transformers) and the `+∞` handling: landed 2026-11-11 (issue #339,
  `lean/CodeCalculus/Gate6Exact.lean`) as the instance of the §4.32 theorem
  at the exact distance and the `glueLedger` transformer on the `E-GLUE`
  constructor; the graft relations, the direct-sum law on disjoint
  well-formed factors, and the $\Delta = \varnothing$ extension law it left
  as hypotheses are proved for the exact distance since 2026-11-11 (issue
  #367; `ExactGraft.lean`, `ExactDirectSum.lean`, `ExactPermute.lean`), the
  seam certificate's equality and the glued state's well-formedness staying
  premises by decision; the §4.28 peel relations
  and the `k = 0` reading of the exact distance (`hk0`) landed 2026-11-11
  (issue #338, `lean/CodeCalculus/ExactPeel.lean`); the derivation-level
  `W13` half landed 2026-11-11 (issue #340) with a generator-referencing
  claim, an assertion-language extension (axis 3) defined at
  `spec/JUDGMENT_LAYER.md` §4 and derived at
  `spec/OPERATIONAL_SEMANTICS.md` §4.11; it ships with this candidate's row
  and is not part of `stdCSS-2` (TODO.md item 8/10). Its input-display
  source rule and its graft rows landed 2026-11-11 (issue #368), in the same
  two sections; they add rules for the claim and no new vocabulary. The Gate 6
  rows for the claim landed 2026-11-14 (issue #424) in the same
  two sections: `Derives.genExtend`, `genExtendMint`, `genPeel`,
  `genPuncture`, `genHadamard`, `genRebase`, and `genRebaseMint`, with
  refusals `not_derivable_gen_of_peeled`,
  `not_derivable_gen_of_punctured`, and `not_derivable_gen_of_rebased`.
- Layout-transfer judgment cells: landed 2026-11-10 (issue #333) as
  `spec/JUDGMENT_LAYER.md` §2d.5, `machine/semantics.json` `layout_cells`,
  and `machine/experiments/layout_conformance_harness.py`. A property cell
  with no term-language change, so a dated note (`DIARY.md`, 2026-11-10) and
  no new release row (§4, the `w`/`r` precedent).
- Distance-increasing constructor admission: `L-HGP`, `L-LIFTED`,
  `L-BALANCED`, `L-GROUP-ALGEBRA`, `L-TANNER`, `L-TILE`, `A-CONCAT`,
  `A-PRODUCT`, `A-DOUBLE` as typed constructors with explicit distance
  hypotheses, axes 2/3/4 (TODO.md §13). Partially landed 2026-11-11 (issue
  #330): `L-HGP`, `L-LIFTED`, `L-GROUP-ALGEBRA`, and `A-CONCAT` are
  `transition-defined` expression constructors (`TERM_LANGUAGE.md` §1, §2;
  `OPERATIONAL_SEMANTICS.md` §2 cards, §4.34), an axis-2 change staged on
  this candidate's row; they carry no distance rule, so no judgment cell is
  added, and their well-formedness instances of
  `OBL-WELL-FORMEDNESS-PRESERVATION` are proved by hand (§4.34). Their Lean
  productions and rules landed 2026-11-11 (issue #370), with the
  retained-display theorem, $n$, and the `L-HGP` overlap proved. The
  other three overlaps are proved in Lean since issue #482. Of the $k$
  closed forms, that of `L-GROUP-ALGEBRA` is proved in Lean since issue
  #483 and that of `A-CONCAT`, with the retention of every natural row,
  since issue #505. Since 2026-11-16 (issue #519), the closed forms of
  `L-HGP` and `A-PRODUCT` are proved modulo the four rank axioms
  `hgp_rankX`, `hgp_rankZ`, `product_rankX`, and `product_rankZ` recorded
  in `lean/extra/ClosedK.lean` and `AXIOMS.md`; those axioms are accepted
  as `proposed (classical)` assumptions, not discharged obligations, and
  `L-HGP` otherwise stays a hand derivation (§4.34). The
  re-discharge obligations of §4 apply to the metatheorems scoped to the
  `stdCSS-2` operation set once the row ships. The other five
  (`L-BALANCED`, `L-TANNER`, `L-TILE`, `A-PRODUCT`, `A-DOUBLE`) landed the
  same day (issue #369) as `transition-defined` expression constructors
  with typed inputs realized as finite objects (`OPERATIONAL_SEMANTICS.md`
  §2 cards, §4.35), also an axis-2 change staged on this row and also
  without a distance rule.
- Puncturing/peeling distance prices: landed 2026-11-10 (issue #331) as two
  `E-PEEL` price cells with a new typed input, the avoidance minimum
  (`spec/JUDGMENT_LAYER.md` §2a, §2c), over sharpened unpriced carries, and
  as the recorded `E-PUNCTURE` reduction with the refusal kept
  (`spec/OPERATIONAL_SEMANTICS.md` §4.28, §4.29). Judgment-vocabulary content
  of this candidate (axis 3); it ships with the candidate's row and adds none
  of its own.
- Gluing promotion: `E-GLUE` from conditional lower-bound connector to a
  licensed connected-code composition with seam-certificate equality. The
  §4.31 repair's lower-endpoint half is mechanized as
  `glue_exactDistance_ge_min` (`lean/CodeCalculus/ExactGlue.lean`); the
  instance-wise equality as `glue_exactDistance_eq_min_of_survivesA/B`
  (`lean/CodeCalculus/ExactGlueSurvival.lean`); the class-pair distance
  formula as `glue_exactDistance?_eq_some_iff`
  (`lean/CodeCalculus/ExactGlueDistance.lean`); and the Theorem 4 / claim 7.4
  extraction of 2026-11-11 (issue #332) discharges the family-level guarantee
  for admissible seams at the spec level, contingent on survival of the factor
  representative, which the logical-witness field of `STATE_MODEL.md` §1
  carries. The logical-witness field and its `E-GLUE` transport are mechanized
  as definitions outside `CodeState`, and the family-level statement in its
  conditional form as `family_glueExact_iff`
  (`lean/CodeCalculus/LogicalWitness.lean`, issue #439). That admissible
  seams guarantee survival is not mechanized; the equality stays conditional on seam
  admissibility and on that survival.
- Re-exposure hardness in constrained splits: landed 2026-11-11 (issue #328)
  as `OBL-GLUE-RE-EXPOSURE` ([`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md)
  §4.33): no re-exposed class under the admitted `E-GLUE`, so the quantity is
  $+\infty$ there; the hardness boundary stays recorded against
  shared-interface splits, which the calculus does not admit.
- Heuristic result statuses, admitted 2026-11-11 (issue #329):
  `probabilistic` as the recorded shape of heuristic search outcomes, a
  dated note with no new row; `certificate-checked` as an evidence status of
  this candidate for per-state atomic judgments. The mechanized certificate
  checker landed 2026-11-11 (issue #371): `checkCertificate` in
  `lean/CodeCalculus/CertificateChecker.lean`, with acceptance proved to
  imply the sector lower bound for the exact distance, and the first
  per-state theorems in `lean/CodeCalculus/CertificateInstances.lean`
  (`spec/CLAIMS.md`, *Mechanized checker*, records the trust basis). The
  status is carried by those theorems and by no consumer field.
- Sector-swap exploitation via `E-LOCAL-HADAMARD` (`T=Q`): landed
  2026-11-11 (issue #346) as consumer support only; no derived cell was
  needed, so no axis-3 content ships with it (the conjugation identity is
  recorded in `design/DERIVED_RELATIONS.md` §2b).

**Intended machine-side scope (no calculus change; may also ship as patches):**

- Sector-targeted deletion/peel search, multi-objective candidate ranking,
  heuristic-result status (TODO.md §13, distance-increasing subsection); the
  heuristic-result status landed 2026-11-11 as the `heuristic_outcome`
  record (issue #329).

**Re-discharge obligations created by this release** (per §4): every
metatheorem scoped to the `stdCSS-2` operation set must be re-established
against the expanded operation set before its `discharged-through` advances;
in particular the Gate 6 metatheorems remain conditional cells, not admitted
rules, and the §4.32 soundness statement is mechanized only conditional on
the §4.26 to §4.30 distance relations until the remaining relations land
here.

**Admitted after the 2026-11-10 disposition and staged on the `stdCSS-3` /
`v0.2.0` row.** `L-NESTED-CSS` is a `transition-defined` expression constructor
since 2026-11-13 (issue #445; `TERM_LANGUAGE.md` §1, §2;
`OPERATIONAL_SEMANTICS.md` §2 card, §4.36). It is an axis-2 change with no
distance rule and no judgment cell, and its well-formedness instance of
`OBL-WELL-FORMEDNESS-PRESERVATION` is proved by hand (§4.36) and mechanized in
Lean (`evalExpr_nested_wf`, `ConstructorAssembly.lean`). Staged on the
`stdCSS-3` / `v0.2.0` release row (§5, issue #441).

**Dated note (2026-11-14, issues #446–#453).** By dated maintainer decision
(`diary/2026-11-14-admit-v030-candidate-constructors-judgments-issues-446-453.md`),
the following are admitted into this candidate's scope: positive composition
criteria (#446), CNOT-disguised direct sums + depth-one equality (#447),
multi-band patch count as construction metadata (#448), mapping cone /
chain-map construction (#449), one-shot level-map transport (#450),
decoupling of translation-invariant CSS codes (#451), gate-realization
candidate rows (#452), and future Π fields as sketch refinement (#453).
Their conditions and hypotheses are preserved; none upgrades an exactness,
lower-bound, or universal claim. Implementation (taxonomy IDs, grammar
productions, spec cards, machine and Lean counterparts) follows in separate
PRs; re-discharge obligations apply where an entry touches axis 2 or 3.

**Not in this candidate (guardrails, TODO.md §13):** exact-distance
computation as a calculus move; heuristic search results presented as lower
bounds; release-ordinal bumps for machine-only provider work.

## 6. Item-level conventions and owners

Declared here; applied where each item is owned.

- **`introduced-in`** — the release that first admitted the item. Absent means
 `stdCSS-1`.
- **`discharged-through`** — the latest release for which the item's proof has
 been (re-)established.

| Fact | Owner |
| --- | --- |
| grammar production introduction | CSS_CODE_CALCULUS_PROPOSAL_DRAFT.md §3.2 |
| contract admission | [`CLAIMS.md`](CLAIMS.md) |
| obligation introduction and discharge | [`OBLIGATIONS.md`](OBLIGATIONS.md) |

This note references those files; it does not restate their contents.

## 7. Non-goals

- no retrofit of `stdCSS-1` tags onto existing entries;
- no mechanization in the current phase;
- no single global version counter and no per-layer counters beyond the
 line/ordinal scheme.
- no release-ordinal or software-MINOR bump for machine-only or
 documentation work; such changes are PATCH only (§4.1, §8).

**Dated note.** The six Gate 6 CSS-level productions
(`P-REBASE`, `E-LOCAL-HADAMARD`, `E-PEEL`, `E-PUNCTURE`, `E-EXTEND`,
`E-GLUE`) are in scope as conditional cells under `stdCSS-2` (admitted
2026-10-23). Their addition creates re-discharge obligations for the
metatheorems scoped to the `stdCSS-2` operation set: each affected
metatheorem's `discharged-through` does not advance until it is re-established
against the expanded operation set. The six rows are recorded in the
update-ownership table of `spec/STATE_MODEL.md` §4 and `machine/state.json`.


## 8. Software release track (`vMAJOR.MINOR.PATCH`)

The repository is also released as a software artifact, independently of the
calculus line (§3, §5). The two tracks are cross-referenced but never merged:
a calculus line names a mathematical object; a software release names a build.

- **Track A — calculus line** (`stdCSS-n`): normative content. Bump rules in
  §4 and §4.1.
- **Track B — software release** (`vMAJOR.MINOR.PATCH`): the repository as
  distributed (`machine/`, `lean/`, `spec/`, docs, CI). Tag form is
  `vMAJOR.MINOR.PATCH` (e.g. `v0.1.0`); the bare `v0.1` form is legacy.

**Bump criteria (Track B):**

| Bump | When |
| --- | --- |
| **PATCH** (`v0.1.x`) | No change to any calculus axis, admitted rung, or obligation status. Documentation fixes, transcription fixes, CI/pinned-replay re-pinning, consumer bug fixes that do not alter admitted semantics, accepted machine-side candidates (§5.1), Lean hygiene. All validation gates (lint, pytest, fixture conformance, priced harness, `lake build`) green. |
| **MINOR** (`v0.2.0`) | A new calculus ordinal/row (conservative addition), or admission of new conditional cells as `transition-defined`, or an advanced `discharged-through`, or a new advertised consumer capability. Normally accompanied by a `stdCSS-(n+1)` row (§5). |
| **MAJOR** (`v1.0.0`) | A new calculus line (new state model), a non-conservative change breaking existing derivations, removal of an admitted operation, or — by convention — all in-scope obligations discharged and the soundness metatheorem mechanized. |

**Invariant.** A software MINOR never lands without a corresponding calculus-row
change, or an explicit note that the change is machine-only (in which case it
is a PATCH). This keeps the line number meaningful ("which calculus").

**Tagging and publishing are maintainer-only** (AGENTS.md *Hard rules*). A
release is prepared (four-axis pin recorded, changelog drafted, `discharged-
through` values staged) but not tagged by an agent; the maintainer appends the
release row and tags in the same change.


**Dated note (2026-11-16, issue #519).** The four rank axioms of
`lean/extra/ClosedK.lean` (`hgp_rankX`, `hgp_rankZ`, `product_rankX`,
`product_rankZ`) are accepted as `proposed (classical)` assumptions and
recorded in `AXIOMS.md`; issues #497, #498, and the #424 umbrella are
closed on that condition. The arithmetic that combines the ranks
(`hgp_arith`, `product_arith`) remains proved. This is a mechanization
status change only: it advances no `discharged-through` value, creates no
new calculus row, and does not make the rank identities `established`.

**Dated note (2026-11-16, CI).** The validation workflow's scaled
conformance case count was reduced to `SCALED_CASES=500` (issues #520,
#521); this is a machine-only change with no calculus-axis effect and no
release-row change.
