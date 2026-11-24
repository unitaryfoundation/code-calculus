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

The current development release is `stdCSS-3` (software `v0.3.0`, prepared
2026-11-19 and not yet tagged; `v0.2.0` shipped at commit `e94fa83` on
2026-11-17; `v0.1` shipped at commit `078cab2` on 2026-11-02); `MVP`
remains an alias for the historical `stdCSS-1` baseline. The release table
records all axis sets.

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
therefore requires a new release row, never a silent edit. On 2026-11-11 the status was admitted to the `stdCSS-3` candidate (§5.1) for
per-state atomic judgments, conditional on a mechanized certificate checker.
The checker landed 2026-11-11 (`lean/CodeCalculus/CertificateChecker.lean`). The status ships with that
row: until then it is carried only by the candidate's per-state Lean
theorems, and by no claim of `stdCSS-2` (`spec/CLAIMS.md`, *Admission* and
*Mechanized checker*).

The claim-shape vocabulary gained the `probabilistic` (delta-bounded) shape on
2026-10-27: a claim about a search, not a lower-bound certificate.
It is an assertion-language-axis change and ships as a release note only; no
release row is re-numbered by it, and it never upgrades `unavailable` to
`proved`. On 2026-11-11 the shape was admitted as the recorded
form of heuristic search outcomes (`spec/CLAIMS.md`, *Admission*): a dated
note on the current ordinal, since the shape already exists; the record
licenses no endpoint.

### 4.1 Bump criteria (calculus line)

A change's **bump** is determined by which axes it touches, not by its size.
The table is exhaustive; if a change does not fit a row, it is not yet a
release and needs a decision-log disposition first.

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
| `stdCSS-3` / `v0.2.0` | phase-insensitive standard CSS (`stdCSS-2` state model) | `stdCSS-2` operations plus the `stdCSS-3` candidate scope of §5.1: the distance-increasing constructors (`L-HGP`, `L-LIFTED`, `L-GROUP-ALGEBRA`, `A-CONCAT`, `L-BALANCED`, `L-TANNER`, `L-TILE`, `A-PRODUCT`, `A-DOUBLE`), `L-NESTED-CSS`, layout-transfer cells, puncturing/peeling price cells, `E-GLUE` promotion with seam-certificate equality, `E-LOCAL-HADAMARD` sector-swap support, W13 half, and the admitted heuristic statuses; `E-GLUE` retains no unary grammar production | Gates 0 and 1 ratified; `OBL-GATE6-CSS-EXTENSIONS` discharged (§4.32); `OBL-JUDGMENT-SOUNDNESS` proved by hand (§4.11) with partial Lean mechanization; `discharged-through` values **not advanced** — re-discharge obligations of §4 remain open until the re-proofs land | **Prepared 2026-11-14 ( "prepare but do not tag"):** candidate scope of §5.1 staged as a release row; not tagged. Gates 2–7 unchecked by design. Rows are not edited after the fact; a changed release is a new row. |
| `stdCSS-3` / `v0.3.0` | phase-insensitive standard CSS (`stdCSS-3` state model) | `stdCSS-2` operations plus the `stdCSS-3` candidate scope of §5.1, now completed: gate-realization judgment rows (`preserves_U`, `ω` floor, §2h/§7.1–§7.4), W13 Gate 6 rows and Trace/StepChain seam discharge (§4.11/§4.37), one-shot level-map transport (§2j), `A-QUOTIENT` monomial-quotient specialization (§2i), kernel five promoted to rung 6 (§4.40), `E-GLUE` mechanization with binary-only production (§1–§2, §4.31/§4.33) | Gates 0–6 ratified (2026-11-19); `OBL-GATE6-CSS-EXTENSIONS` discharged (§4.32); `OBL-JUDGMENT-SOUNDNESS` proved by hand (§4.11) with partial Lean mechanization; `discharged-through` advanced to `stdCSS-3` for all metatheorems (§4.40) | **Prepared 2026-11-19 (maintainer decision):** completes the `stdCSS-3` candidate scope; `discharged-through` values advanced; Gate 7 unchecked by design. Re-discharge obligations of §4 remain scoped to the named fragments (§4.40). Tagging and appending the final tag record remain maintainer-only (AGENTS.md *Hard rules*). |

**Dated note (2026-11-14).** The `stdCSS-3` / `v0.2.0` release
row above is **prepared but not tagged** ("prepare but do not tag"): it stages
the §5.1 candidate scope as a release row and records that
`discharged-through` values are not advanced. Tagging and appending the final
tag record remain maintainer-only actions (AGENTS.md *Hard rules*); the row is
not edited after the fact, and a changed release is a new row.

**Dated note (2026-11-19, v0.3.0 preparation).** The `stdCSS-3` / `v0.3.0`
release row above is **prepared but not tagged** ("prepare but do not tag"):
it completes the `stdCSS-3` candidate scope (gate-realization judgment rows,
W13 Gate 6 rows, one-shot level-map transport, `A-QUOTIENT` specialization,
kernel five at rung 6, `E-GLUE` mechanization) and records that
`discharged-through` values are advanced to `stdCSS-3` (§4.40). By maintainer
decision the calculus line is recorded as `stdCSS-3` (the candidate scope's
own name) rather than a new ordinal; the §4.1 tension is noted and resolved
by that decision. Tagging and appending the final tag record remain
maintainer-only (AGENTS.md *Hard rules*).

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
the §4.26 to §4.30 distance relations (`lean/CodeCalculus/Gate6Soundness.lean`). **Preparation (2026-11-10).** The release row for `v0.1.0` has been appended to
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

**Status: prepared in §5 (2026-11-14), not yet tagged.** Nothing
below was owed by the stopping point (`SCOPE.md` §3). Each item required
a `the decision log` disposition before implementation; that disposition landed
2026-11-10, accepting the items listed below (weight-3
exposure accepted as an investigation; heuristic status accepted as both
`probabilistic` and `certificate-checked`). The `stdCSS-3` / `v0.2.0` row is
staged in the release table (§5) under the "prepare but do not tag" decision, and `discharged-through` values are not advanced until the
re-proofs land (§4).

**Intended calculus-side scope (axes 3/4, and axis 2 where noted):**

- Mechanization of the refined Gate 6 soundness statement (§4.31
 transformers) and the `+∞` handling: landed 2026-11-11 (
 `lean/CodeCalculus/Gate6Exact.lean`) as the instance of the §4.32 theorem
 at the exact distance and the `glueLedger` transformer on the `E-GLUE`
 constructor; the graft relations, the direct-sum law on disjoint
 well-formed factors, and the $\Delta = \varnothing$ extension law it left
 as hypotheses are proved for the exact distance since 2026-11-11 ( `ExactGraft.lean`, `ExactDirectSum.lean`, `ExactPermute.lean`), the
 seam certificate's equality and the glued state's well-formedness staying
 premises by decision; the §4.28 peel relations
 and the `k = 0` reading of the exact distance (`hk0`) landed 2026-11-11
 ( `lean/CodeCalculus/ExactPeel.lean`); the derivation-level
 `W13` half landed 2026-11-11 with a generator-referencing
 claim, an assertion-language extension (axis 3) defined at
 `spec/JUDGMENT_LAYER.md` §4 and derived at
 `spec/OPERATIONAL_SEMANTICS.md` §4.11; it ships with this candidate's row
 and is not part of `stdCSS-2` (the issue tracker item 8/10). Its input-display
 source rule and its graft rows landed 2026-11-11, in the same
 two sections; they add rules for the claim and no new vocabulary. The Gate 6
 rows for the claim landed 2026-11-14 in the same
 two sections: `Derives.genExtend`, `genExtendMint`, `genPeel` (with
 `peelSupport_eq_graftSupport_of_eval`), `genPuncture`, `genHadamard`,
 `genRebase`, and `genRebaseMint`, with refusals `not_derivable_gen_of_peeled`,
 `not_derivable_gen_of_punctured`, `not_derivable_gen_of_punctured_id`, and
 `not_derivable_gen_of_rebased`, completed together with the `Trace`/`StepChain`
 seam-condition discharge and Gate 6 worked instances on 2026-11-18.
- Layout-transfer judgment cells: landed 2026-11-10 as
 `spec/JUDGMENT_LAYER.md` §2d.5, `machine/semantics.json` `layout_cells`,
 and `machine/experiments/layout_conformance_harness.py`. A property cell
 with no term-language change, so a dated note (`the decision log`, 2026-11-10) and
 no new release row (§4, the `w`/`r` precedent).
- Distance-increasing constructor admission: `L-HGP`, `L-LIFTED`,
 `L-BALANCED`, `L-GROUP-ALGEBRA`, `L-TANNER`, `L-TILE`, `A-CONCAT`,
 `A-PRODUCT`, `A-DOUBLE` as typed constructors with explicit distance
 hypotheses, axes 2/3/4 (the issue tracker §13). Partially landed 2026-11-11: `L-HGP`, `L-LIFTED`, `L-GROUP-ALGEBRA`, and `A-CONCAT` are
 `transition-defined` expression constructors (`TERM_LANGUAGE.md` §1, §2;
 `OPERATIONAL_SEMANTICS.md` §2 cards, §4.34), an axis-2 change staged on
 this candidate's row; they carry no distance rule, so no judgment cell is
 added, and their well-formedness instances of
 `OBL-WELL-FORMEDNESS-PRESERVATION` are proved by hand (§4.34). Their Lean
 productions and rules landed 2026-11-11, with the
 retained-display theorem, $n$, and the `L-HGP` overlap proved. The
 other three overlaps are proved in Lean since. Of the $k$
 closed forms, that of `L-GROUP-ALGEBRA` is proved in Lean since and that of `A-CONCAT`, with the retention of every natural row,
 since. Since 2026-11-16, the closed forms of
 `L-HGP` and `A-PRODUCT` are proved modulo the four rank axioms
 `hgp_rankX`, `hgp_rankZ`, `product_rankX`, and `product_rankZ` recorded
 in `lean/extra/ClosedK.lean` and `AXIOMS.md`; those axioms are accepted
 as `proposed (classical)` assumptions, not discharged obligations, and
 `L-HGP` otherwise stays a hand derivation (§4.34). The
 re-discharge obligations of §4 apply to the metatheorems scoped to the
 `stdCSS-2` operation set once the row ships. The other five
 (`L-BALANCED`, `L-TANNER`, `L-TILE`, `A-PRODUCT`, `A-DOUBLE`) landed the
 same day as `transition-defined` expression constructors
 with typed inputs realized as finite objects (`OPERATIONAL_SEMANTICS.md`
 §2 cards, §4.35), also an axis-2 change staged on this row and also
 without a distance rule.
- Puncturing/peeling distance prices: landed 2026-11-10 as two
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
 extraction of 2026-11-11 discharges the family-level guarantee
 for admissible seams at the spec level, contingent on survival of the factor
 representative, which the logical-witness field of `STATE_MODEL.md` §1
 carries. The logical-witness field and its `E-GLUE` transport are mechanized
 as definitions outside `CodeState`, and the family-level statement in its
 conditional form as `family_glueExact_iff`
 (`lean/CodeCalculus/LogicalWitness.lean`). That admissible
 seams guarantee survival is not mechanized; the equality stays conditional on seam
 admissibility and on that survival.
- Re-exposure hardness in constrained splits: landed 2026-11-11
 as `OBL-GLUE-RE-EXPOSURE` ([`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md)
 §4.33): no re-exposed class under the admitted `E-GLUE`, so the quantity is
 $+\infty$ there; the hardness boundary stays recorded against
 shared-interface splits, which the calculus does not admit.
- Heuristic result statuses, admitted 2026-11-11:
 `probabilistic` as the recorded shape of heuristic search outcomes, a
 dated note with no new row; `certificate-checked` as an evidence status of
 this candidate for per-state atomic judgments. The mechanized certificate
 checker landed 2026-11-11: `checkCertificate` in
 `lean/CodeCalculus/CertificateChecker.lean`, with acceptance proved to
 imply the sector lower bound for the exact distance, and the first
 per-state theorems in `lean/CodeCalculus/CertificateInstances.lean`
 (`spec/CLAIMS.md`, *Mechanized checker*, records the trust basis). The
 status is carried by those theorems and by no consumer field.
- Sector-swap exploitation via `E-LOCAL-HADAMARD` (`T=Q`): landed
 2026-11-11 as consumer support only; no derived cell was
 needed, so no axis-3 content ships with it (the conjugation identity is
 recorded in `DERIVED_RELATIONS.md` §2b).

**Intended machine-side scope (no calculus change; may also ship as patches):**

- Sector-targeted deletion/peel search landed 2026-11-18 as `bounded_sector_search`; multi-objective candidate ranking, heuristic-result status
 (the issue tracker §13, distance-increasing subsection); the heuristic-result status
 landed 2026-11-11 as the `heuristic_outcome` record.

**Re-discharge obligations created by this release** (per §4): every
metatheorem scoped to the `stdCSS-2` operation set must be re-established
against the expanded operation set before its `discharged-through` advances;
in particular the Gate 6 metatheorems remain conditional cells, not admitted
rules, and the §4.32 soundness statement is mechanized only conditional on
the §4.26 to §4.30 distance relations until the remaining relations land
here.

**Admitted after the 2026-11-10 disposition and staged on the `stdCSS-3` /
`v0.2.0` row.** `L-NESTED-CSS` is a `transition-defined` expression constructor
since 2026-11-13 ( `TERM_LANGUAGE.md` §1, §2;
`OPERATIONAL_SEMANTICS.md` §2 card, §4.36). It is an axis-2 change with no
distance rule and no judgment cell, and its well-formedness instance of
`OBL-WELL-FORMEDNESS-PRESERVATION` is proved by hand (§4.36) and mechanized in
Lean (`evalExpr_nested_wf`, `ConstructorAssembly.lean`). Staged on the
`stdCSS-3` / `v0.2.0` release row (§5).

**Dated note (2026-11-14).** A dated maintainer decision recorded in the
development repository admits the following into this candidate's scope:
positive composition criteria, CNOT-disguised direct sums and depth-one
equality, multi-band patch count as construction metadata, mapping-cone /
chain-map construction, one-shot level-map transport, decoupling of
translation-invariant CSS codes, gate-realization candidate rows, and future
Π fields as sketch refinement.
Their conditions and hypotheses are preserved; none upgrades an exactness,
lower-bound, or universal claim. Implementation (taxonomy IDs, grammar
productions, spec cards, machine and Lean counterparts) follows as separate
work; re-discharge obligations apply where an entry touches axis 2 or 3.

**Dated note (2026-11-18).** The two gate-realization judgment rows
are decided and recorded on axis 3 (`stdCSS-3` / `v0.3.0` candidate
scope): (1) the operator-indexed codespace-preservation predicate
$\mathsf{preserves}_U(C)$ on CSS displays, with its `C-ADD-CHECK` carry cell
(carries at every angle when all generators commute with the added row $s$,
carries at $\theta_j = \pi/4$ iff $V_s \in \mathcal{S}(C')$, and stays
`not yet defined` when a generator anticommutes with $s$ at an angle
$\neq \pi/4$, alongside addressability and logical action) and kernel rows
(`C-SKIP`, `C-DIRECT-SUM` on one summand, `C-SEQUENCE`, and the
`C-DELETE-CHECK` refutation); and (2) the equal-syndrome generator weight floor
$\omega(C) \ge \lceil d(C)/2 \rceil$, carried by weakening as the monotone
image $\lceil L_d/2 \rceil$ of the full-distance lower endpoint $L_d$ re-read
at each state (`spec/JUDGMENT_LAYER.md` §2, §2h, §7.1–§7.4;
`spec/CLAIMS.md`; hand derivations at `spec/OPERATIONAL_SEMANTICS.md` §4.37).
No operation identifier is minted for a logical gate (`spec/TAXONOMY.md` §3.8).
`discharged-through` values are not advanced until the re-discharge obligations
of §4 are met.

**Dated note (2026-11-18).** The monomial-quotient specialization
of `A-QUOTIENT` (`spec/TAXONOMY.md` §2.15) and its conditional transfer-theorem
record (`spec/JUDGMENT_LAYER.md` §2i) are recorded for `v0.3.0`. `A-QUOTIENT`
remains `taxonomy-only` at rung 1 (no grammar production or axis-2 change), §2i
records the existence of Hsin's transfer theorem without introducing a new
assertion-language operator or usable automatic distance/dimension bound, and
`discharged-through` values do not advance.

**Dated note (2026-11-18).** By dated maintainer decision
extending `SCOPE.md` §3–§4, the conditional family-level transport rule for
Yuan's one-shot hollowed-tensor level map (`arXiv:2610.02137v1`, Definitions
104/106/111/113/116 and Eq. (249), Lemmas 117–118, Theorem 81 Eq. (1), Remark
39) is admitted to the `stdCSS-3` / `v0.3.0` candidate scope on axis 3
(`spec/JUDGMENT_LAYER.md` §2j; `spec/CLAIMS.md`). No new property is added to
the §7.1 signature (failure probability is a decoder/noise quantity, not a
carried property) and no new assertion-language operator is minted; the
`upper-bound` cell is recorded as judgment vocabulary only. No taxonomy operation
identifier is minted (`spec/TAXONOMY.md` §3.8), no distance lower bound is
claimed (`unavailable`), imported framework lemmas stay `conditional`, empirical
finite-seed $\bar\Gamma$ checks stay `empirical` and separate, and
`discharged-through` values do not advance.

**Dated note (2026-11-18).** Axis: 2 (operation set / term
language). By dated maintainer decision
(`the decision log`),
the `glue(e_1, e_2; \vec u)` production is recorded in
[`TERM_LANGUAGE.md`](TERM_LANGUAGE.md) §1, matching the constructor already
present in Lean (`StateExpr.glue` / `EvalExpr.glue`) and
`machine/semantics.json`; the binary-only decision (no unary command
production) is an axis-2 record on the `stdCSS-3` candidate, not an edit to
an existing release row. `E-GLUE` remains **binary-only** (no unary command
production) and is recorded
explicitly in [`TERM_LANGUAGE.md`](TERM_LANGUAGE.md) §1–§2 as the binary
state-expression constructor $e ::= \mathrm{glue}(e_1, e_2; \vec u)$ beside
$\oplus$ (matching `StateExpr.glue` / `EvalExpr.glue` in Lean and
`machine/semantics.json`); the remaining CSS-level algebraic pieces of the
extracted §4.31/§4.33 Theorem 4 / claim 7.4 derivation and `E-GLUE` state
soundness are mechanized in `lean/CodeCalculus/GlueExtraction.lean` with the
irreducible geometric move-word $\to$ `AdmissibleSeam` gap explicitly recorded
as a substrate boundary; and `E-GLUE` advances to **rung 5 (`contract-stated`)**
in [`CLAIMS.md`](CLAIMS.md) (and derived `machine/operation_registry.json`),
while remaining a Gate 6 conditional cell with Gate 6 unchecked. Existing §5
release rows are not edited, and `discharged-through` values do not advance.

**Dated note (2026-11-18).** By dated maintainer decision
(`the decision log`), the
five kernel operations (`C-SKIP`, `C-DIRECT-SUM`, `C-DELETE-CHECK`,
`C-ADD-CHECK`, `C-SEQUENCE`) are promoted from rung 5 (`contract-stated`) to
**rung 6 (`contract-proved`)** in [`CLAIMS.md`](CLAIMS.md) (and derived index
`machine/operation_registry.json`), backed by the dated hand derivations in
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4 including the
quotient-level logical-sector exact sequences (§4.39) and the `stdCSS-3`
metatheorem re-discharge ledger (§4.40). Every metatheorem in
[`OBLIGATIONS.md`](OBLIGATIONS.md) — together with
`OBL-WELL-FORMEDNESS-PRESERVATION` — now records its `discharged-through`
field at **`stdCSS-3`** (either discharged across the full `stdCSS-3`
operation and 2026-11-18 axis-3 judgment set, or explicitly restricted to its
named fragment and discharged on that fragment through `stdCSS-3`; §4.40).
This is an axis-4 / contract-status change (no new state model, operation ID,
or grammar production). Existing §5 release rows are not edited; appending the
`v0.3.0` release row and tagging remain maintainer-only actions (§8), rung 7
(`mechanized`) remains owed, and Gates 2–7 remain unchecked.

**Dated note (2026-11-19).** The sector-split deletion price
cells for `C-DELETE-CHECK` (deleted sector
$d'_\tau=\min(d_\tau,w_{\mathrm{del}})$, opposite sector
$d'_{\bar\tau}=\min(d_{\bar\tau},w_{\mathrm{exp}})$, full distance
$d'=\min(d,w_{\mathrm{del}},w_{\mathrm{exp}})$) are admitted as new-admission
scope under the 2026-11-18 re-schedule and ship in `v0.4.0`; they do not form
part of the `v0.3.x` patches. `discharged-through` values are not advanced.
See `the decision log`.


**Not in this candidate (guardrails, the issue tracker §13):** exact-distance
computation as a calculus move; heuristic search results presented as lower
bounds; release-ordinal bumps for machine-only provider work.

**Dated note (2026-11-19, `v0.4.0` target).** Axis: 2 (operation
set / term language). By dated maintainer decision
(`the decision log`),
`L-EMPTY` (`empty`), `L-FREE` (`free(Q)`), `A-PULLBACK`
(`pullback(e₁, e₂, e_I; φ₁, φ₂)`), and `A-PUSHOUT`
(`pushout(e₁, e₂, e_S; ψ₁, ψ₂)`) are admitted as `transition-defined`
expression constructors (`TERM_LANGUAGE.md` §1–§2; `OPERATIONAL_SEMANTICS.md`
§2 cards, §4.43; `JUDGMENT_LAYER.md` §2g, §2d.5; `CLAIMS.md`), and the
Kan-extension candidate remains refused. They carry no automatic distance
Rule beyond §2g (`DistanceLedger.for_constructed`). Existing §5 release rows
are not edited, and `discharged-through` values do not advance (re-discharge
obligations of §4 apply).

**Dated note (2026-11-22, `v0.4.0` target).** Axis: 2 (operation set / term
language) and 3 (conditional interval cell and family-level ceiling). The
dated maintainer decision is recorded in the decision log (2026-11-22):
`L-PAIR-PARTITION`
(`pair_partition(p; B_X, B_Z)`) is admitted and `PP-SCALE` (`pp_scale(e; P)`)
is promoted, both as `transition-defined` expression constructors
(`TERM_LANGUAGE.md` §1–§2; `OPERATIONAL_SEMANTICS.md` §2 cards, §4.46–§4.47;
`JUDGMENT_LAYER.md` §2d.5, §2g, §2l; `CLAIMS.md`; `OBLIGATIONS.md`
`OBL-PP-SCALE` and `OBL-WELL-FORMEDNESS-PRESERVATION`). Existing §5 release
rows are not edited, and `discharged-through` values do not advance
(re-discharge obligations of §4 apply).

**Dated note (2026-11-23, `stdCSS-4` / `v0.4.0` candidate scope; machine-side).**
The consumer capabilities of software `v0.3.1` are staged on the `stdCSS-4`
row under the §8 staged-admission rule: (1) objective-aware search, in which
`bounded_sector_search` and `plan` select the ranking objective (distance,
check weight, n, k, an axis/targets dict, or a callable); (2) applicability
diagnostics, in which `bounded_sector_search` reports per-move-family
`enabled`, `enumerated` and first-drop-reason counts; (3) constructor
screening and separation, in which typed constructor specifications enter the
objective-filtered pool with a `structural_profile`, and sector swaps are
reported as presentation-only candidates and never as improvements; and (4)
stop and budget reporting, in which `bounded_sector_search` names its stop
reason and the budget it declined, and `run_campaign` records a `stop_reason`.
None of these changes an axis, an admitted rung, or an obligation status, and
none advances a `discharged-through` value. Each is a new advertised consumer
capability. Under §8 it may ship in the `v0.3.1` PATCH only as a staged
admission on the `stdCSS-4` row, as this note stages it; without this note it
would be a MINOR criterion.

**Dated note (2026-11-22, `v0.4.0` target).** Axes: 2 (operation set / term
language) and 3 (judgment set / distance ledger).
1. **Nonabelian finite group inputs (Axis 2, `OBL-NONABELIAN-GROUP-INPUTS`):**
   `L-LIFTED`, `L-GROUP-ALGEBRA`, and `L-BALANCED` are generalized from finite
   abelian groups given by cyclic orders to arbitrary finite groups $G$
   (presented by cyclic orders, an explicit multiplication table, or
   permutation generators; `TAXONOMY.md` §1 and §3.3–§3.5; `TERM_LANGUAGE.md`
   §1, §2, §7; `OPERATIONAL_SEMANTICS.md` §2 cards and §4.44;
   `lean/CodeCalculus/ConstructorOverlap.lean`). Left and right regular
   representations $L(x)$ and $R(y)$ commute over $\mathbb{F}_2$, and for
   abelian groups $R(y) = L(y)$ entry for entry, so the extension is strictly
   conservative on the abelian fragment.
2. **Conditional constructor distance cells and witness lifting (Axis 3,
   `OBL-CONDITIONAL-CONSTRUCTOR-CELLS`):** `JUDGMENT_LAYER.md` §2g and §2g.1
   and `OPERATIONAL_SEMANTICS.md` §4.45 define conditional lower-bound cells
   and deterministic factor-to-child witness lifting for `L-HGP`,
   `L-NESTED-CSS`, `A-CONCAT`, `A-PRODUCT`, and `A-DOUBLE`
   (`lean/CodeCalculus/PricedInterval.lean`; `machine/intervals.py`;
   `machine/constructors.py`).
3. **Admission of `L-PAIR-PARTITION` (Axis 2):** `L-PAIR-PARTITION`
   (`pair_partition(p; B_X, B_Z)`) is admitted as a `transition-defined`
   expression constructor (`TERM_LANGUAGE.md` §1–§2;
   `OPERATIONAL_SEMANTICS.md` §2 card, §4.46; `JUDGMENT_LAYER.md` §2d.5, §2g;
   `CLAIMS.md`; `OBLIGATIONS.md` `OBL-WELL-FORMEDNESS-PRESERVATION`). It carries
   no automatic distance rule beyond §2g (`DistanceLedger.for_constructed`).
4. **Re-discharge obligations (§4):** Per §4, this axis-2/axis-3 change does not
   edit existing §5 release rows and does not automatically advance
   `discharged-through` values on pre-existing obligations; re-discharge of
   `OBL-WELL-FORMEDNESS-PRESERVATION` on the widened nonabelian domain is
   supplied by §4.44 and `cayleyTwoblock_naturalOrthogonal`,
   `cayleyLift_naturalOrthogonal`, and `cayleyBalanced_naturalOrthogonal`,
   while all other tracked obligations retain
   their existing `discharged-through` markers until the `v0.4.0` release audit.


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
| **PATCH** (`v0.1.x`) | No change to any calculus axis, admitted rung, or obligation status, except a staged admission under the rule below. Documentation fixes, transcription fixes, CI/pinned-replay re-pinning, consumer bug fixes that do not alter admitted semantics, accepted machine-side candidates (§5.1), Lean hygiene. All validation gates (lint, pytest, fixture conformance, priced harness, `lake build`) green. |
| **MINOR** (`v0.2.0`) | A new calculus ordinal/row (conservative addition), or admission of new conditional cells as `transition-defined`, or an advanced `discharged-through`, or a new advertised consumer capability. Normally accompanied by a `stdCSS-(n+1)` row (§5). |
| **MAJOR** (`v1.0.0`) | A new calculus line (new state model), a non-conservative change breaking existing derivations, removal of an admitted operation, or — by convention — all in-scope obligations discharged and the soundness metatheorem mechanized. |

**Staged admissions may ride a PATCH.** A PATCH may carry axis-2 or axis-3
content (new productions, new conditional cells, and the rungs and obligations
minted with them), together with the consumer capabilities that realize it,
when all of the following hold:

1. a dated note in this file already stages that content on the next §5
   release row, with its operation or judgment set stated;
2. each consumer capability the PATCH ships is named in a dated §5.1 note as
   staged on that same row; a capability not so named is a MINOR under the
   table above;
3. the PATCH appends no §5 row and advances no `discharged-through` value;
4. the §4 re-discharge obligations are deferred to the audit of that next
   MINOR;
5. the changelog records the staging and the label decision.

The PATCH records no calculus-row fact of its own. The ordinal bump and the
row append fall due together at the next MINOR, which is the release that
records the staged content.

**Invariant.** A software MINOR lands together with the calculus-row change it
records: a new §5 row, a new ordinal, or an advanced `discharged-through`. A
release with no such change is a PATCH, and a PATCH never appends a §5 row.
This keeps the line number meaningful ("which calculus").

**Tagging and publishing are maintainer-only** (AGENTS.md *Hard rules*). A
release is prepared (four-axis pin recorded, changelog drafted, `discharged-
through` values staged) but not tagged by an agent; the maintainer appends the
release row and tags in the same change.


**Dated note (2026-11-16).** The four rank axioms of
`lean/extra/ClosedK.lean` (`hgp_rankX`, `hgp_rankZ`, `product_rankX`,
`product_rankZ`) are accepted as `proposed (classical)` assumptions and
recorded in `AXIOMS.md`; the associated work item was closed on that
condition. The arithmetic that combines the ranks
(`hgp_arith`, `product_arith`) remains proved. This is a mechanization
status change only: it advances no `discharged-through` value, creates no
new calculus row, and does not make the rank identities `established`.

**Dated note (2026-11-16, CI).** The validation workflow's scaled
conformance case count was reduced to `SCALED_CASES=500`; this is a machine-only change with no calculus-axis effect and no
release-row change.
