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
- **Ordinal** — within a line: increment for a change to the calculus's
 **shape**, the interfaces its metatheorems and judgments quantify over (§4.1),
 unless the change is additive and folded into the current ordinal by dated
 maintainer decision (§4.1, *Fold*).
 A new **instance** of an existing interface (an operation, constructor, or
 cell that meets the instance contract of §4.2), a proof, or tooling does not
 change the ordinal; a markedly rarer in-line erratum otherwise (§4).

An ordinal names a shape, not an inventory, and names it only up to the folds
its §5 rows record. From `v0.3.2` on, the ordinal alone does not determine the
assertion language: `stdCSS-3` / `v0.3.1` and `stdCSS-3` / `v0.3.2` have
different ones (§5.3). The exact interfaces and the exact operation,
constructor, and cell inventory of a release are pinned by its software tag
(§8) and its row in the release table (§5), so a citation names the tag, for
example `stdCSS-3` / `v0.3.2`.

The current release is `stdCSS-3`: software `v0.3.0` (tagged 2026-11-20),
`v0.3.1` (tagged 2026-11-23), and `v0.3.2` (prepared 2026-11-26) publish it.
`v0.2.0` was tagged 2026-11-17
and `v0.1` shipped at commit `078cab2` on 2026-11-02. `MVP` remains an alias
for the historical `stdCSS-1` baseline. The release table records all axis
sets.

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

### 4.1 Bump criteria (calculus line): shape and inventory

A change's **bump** is determined by whether it changes an interface, not by
its size or by how many derivations it adds. An **interface** is anything a
metatheorem or a judgment quantifies over. The interfaces of a line are the
closed list in the first rows below. A change that adds or changes one of
them is a **shape** change and takes a new ordinal, unless it is additive and
folded (*Fold*, below). A change that adds an
**instance** of an existing interface is an **inventory** change and keeps
the ordinal, provided the instance meets the contract of §4.2.

The test for a borderline change: does any metatheorem's proof have to
change, rather than gain a case that a local lemma of the new instance
discharges? If it does, the change is a shape change.

The table is exhaustive. A change that fits no row needs a decision-log
disposition before it is released.

| Change | Axis touched | Kind | Bump |
| --- | --- | --- | --- |
| New state model (e.g. phase-sensitive or extended-state CSS) | 1 | line | new **line**; requires an embedding/migration relation (§4) |
| Change to state equality $\equiv$, to the invariants I1–I5, or to the canonical-mint rule | 1 | shape | new **ordinal**; never folded |
| New grammar sort, or a production of a new form (for example a command returning more than one state, or one that reads `steps`) | 2 | shape | new **ordinal**; never folded |
| New judgment form, assertion predicate, or assertion-language operator (for example $\mathsf{preserves}_U$, family-level transport) | 3 | shape | new **ordinal**, or a **fold** if additive |
| New evidence status or claim shape (for example `certificate-checked`, `probabilistic`) | 3 | shape | new **ordinal**, or a **fold** if additive |
| New metatheorem | 4 | shape | new **ordinal**, or a **fold** if additive |
| Change to the statement of an existing metatheorem | 4 | shape | new **ordinal**; never folded |
| New command or expression constructor of an existing form, or a widened input domain of an existing one, meeting §4.2 | 2 | inventory | **patch level** |
| New conditional cell in an existing cell format with an existing status, meeting §4.2 | 3 | inventory | **patch level** |
| New property added to the inventory ($w$, $r$, …) with no term-language change | 3 | inventory | **patch level**, on the `w`/`r` precedent |
| Obligation discharged; proof landed; `discharged-through` advances | 4 | proof | **patch level** |
| Hand derivation corrected in a way that changes what it asserts | 4 (erratum) | erratum | rare **in-line erratum**, recorded in the dated notes unless it alters an admitted rule |
| New certificate format or checker for an existing evidence status, with a mechanized proof that acceptance implies the certified bound | 3 | inventory | **patch level** |
| Addition to the representation contract ([`REPRESENTATION.md`](REPRESENTATION.md)) that changes no state, production, or judgment, for example an ingestion contract | none | inventory | **patch level** |
| Rung promotion of an admitted operation ([`CLAIMS.md`](CLAIMS.md)) | 4 | proof | **patch level** |
| Gate ratification, admission refusal, or other dated decision that admits nothing | none | decision | **patch level** |
| Transcription fix in `machine/` or `lean/` that changes no admitted semantics | none | tooling | **patch level**; transcription is derived and prose wins (AGENTS.md) |
| Consumer or machine-only provider work (new enumerator, benchmark, planner mode, search reporting) | none | tooling | **patch level**; explicit non-goal (§7) |
| Documentation, CI, or Lean hygiene that changes no admitted semantics | none | tooling | **patch level** |

A shape change is never free: every new ordinal re-opens the re-discharge
obligations of §4, and `discharged-through` does not advance until the
re-proof lands. An inventory change admitted under §4.2 re-opens nothing,
because the contract requires the instance to bring its own cases. Items
admitted before the contract existed are the exception recorded in §5.2.

**Fold.** A shape change may be published under the current ordinal, instead
of opening a new one, when it is **additive** and a dated maintainer decision
folds it. A shape change is additive when it adds an interface and changes
none:

1. every existing derivation, judgment form, predicate, evidence status, claim
   shape, and grammar form reads as before;
2. every existing metatheorem keeps its statement on the interfaces and
   instances its disposition names
   ([`OBLIGATIONS.md`](OBLIGATIONS.md), *Re-discharge status of
   metatheorems*), and no `discharged-through` value is read as covering the
   new interface until a disposition names it.

A change to the state model, a new grammar sort or production form, and a
change to the statement of an existing metatheorem are never additive, since
they change what every metatheorem quantifies over; the table marks them
"never folded". A fold is not free either: it opens no ordinal, but the
folded interface stands only on the evidence recorded for it until the §4
re-discharge audit names it in a disposition.

The release preparation records each folded item in §5, as §4.2 items are
recorded for instances: the §4.1 row it falls under; why it is additive; the
evidence its new cells or obligations stand on; the metatheorems whose
dispositions do not yet cover it; and the re-discharge audit still owed. The
decision to fold is the maintainer's
([`AUTHORITY.md`](../AUTHORITY.md)); whether a change is eligible is
computed from this section.

### 4.2 Instance contract

An operation, constructor, or cell is admitted as an instance of an existing
interface only when it supplies, at admission, every local obligation that the
line's metatheorems need from an instance of that kind:

1. a taxonomy ID ([`TAXONOMY.md`](TAXONOMY.md)), a production of an existing
   form ([`TERM_LANGUAGE.md`](TERM_LANGUAGE.md)), and an update-ownership row
   ([`STATE_MODEL.md`](STATE_MODEL.md) §4);
2. a card and a dated hand derivation of output well-formedness
   ([`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §2, §4), as an
   instance of `OBL-WELL-FORMEDNESS-PRESERVATION`;
3. single-valuedness on fixed presentations, as an instance of
   `OBL-PRIMITIVE-DETERMINISM`, and, for a command, that it reads no `steps`
   (`OBL-SKIP-IDENTITY`);
4. its structural carry cells and their rows of `OBL-JUDGMENT-SOUNDNESS`
   ([`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md)); a property it does not carry is
   recorded as such, never left blank;
5. for a cell: an existing cell format and an existing evidence status, with
   its hypotheses named as priced inputs (`OBL-PRICED-INPUT-SEMANTICS`);
6. for each metatheorem that is restricted to a named fragment, either a proof
   of the instance's case or an explicit statement that the instance lies
   outside the fragment.

An instance that lacks an item is not admitted at patch level. Either the
item lands first, or the instance waits for the next ordinal and its
re-discharge audit. The contract binds admissions from 2026-11-24; the items
admitted earlier, and what each still lacks, are recorded in §5.2. A
metatheorem whose `discharged-through` reads the current ordinal covers
exactly the instances named in its disposition
([`OBLIGATIONS.md`](OBLIGATIONS.md), *Re-discharge status of metatheorems*).

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
| `stdCSS-3` / `v0.3.1` | phase-insensitive standard CSS (`stdCSS-3` state model) | the `stdCSS-3` / `v0.3.0` row's set plus the inventory of §5.2: published in `v0.3.0` but missing from that row, `C-COLUMN-CNOT`, `L-MAPPING-CONE`, `L-EMPTY`, `L-FREE`, `A-PULLBACK`, `A-PUSHOUT`, and the sector-split `C-DELETE-CHECK` price cells; published in `v0.3.1`, `L-PAIR-PARTITION`, `PP-SCALE`, nonabelian group inputs for `L-LIFTED`, `L-GROUP-ALGEBRA`, and `L-BALANCED`, and the conditional constructor distance cells with witness lifting | Gates 0–6 ratified (2026-11-19); `discharged-through` at `stdCSS-3` for every metatheorem, covering the inventory each disposition names; for the §5.2 inventory, what each item has and lacks under §4.2 is recorded item by item in §5.2, under a transitional clause ([`OBLIGATIONS.md`](OBLIGATIONS.md), *Re-discharge status of metatheorems*) | Recorded 2026-11-24 by maintainer decision: everything published in a `v0.3.x` tag is `stdCSS-3`. The `v0.3.0` row is not edited; this row completes its inventory. Gate 7 unchecked by design. |
| `stdCSS-3` / `v0.3.2` | phase-insensitive standard CSS (`stdCSS-3` state model) | the `stdCSS-3` / `v0.3.1` row's set plus the §5.3 inventory: `E-SPLIT` separating deletion (`split(Q_A; R)`), split-subset `E-LOCAL-HADAMARD` ($\varnothing \subsetneq T \subsetneq Q$), coset inputs for `L-LIFTED` ($\mathrm{lift}_{G;H}(A, B)$), the `E-EXTEND` distance-loss conditional cell, and the frame-reading gate-realization predicates (`preserves_U(C \| F)`, `phase_U(C \| F) = z`, `image_U(C; e) ≡ P`, `addresses_U(C; F, A)`) and any-angle `C-ADD-CHECK` cell (`JUDGMENT_LAYER.md` §2h Rows C–F), together with the `open` completeness obligation `OBL-ELEMENTARY-COMPLETENESS` | Gates 0–7 ratified (Gate 7 for `stdCSS-3`, 2026-11-26); §5.2 transitional clause retired (all `v0.3.x` inventory items meet §4.2, including `Command.cnotSwap`); four rank axioms of `L-HGP`/`A-PRODUCT` proved in `ClosedK.lean` (no Lean axioms remain, `AXIOMS.md`); `discharged-through` remains at `stdCSS-3` on the §4.40 / §5.2–§5.3 inventory; Rows C–F stand on dated hand derivations (§4.37 Lemmas 5–11, not mechanized, not yet covered by §4.40 metatheorem dispositions); `OBL-ELEMENTARY-COMPLETENESS` remains `open` | Prepared 2026-11-26 by maintainer decision: ships as `v0.3.2` (`stdCSS-3`), folding the items formerly staged for `stdCSS-4` (#572, #606) into `stdCSS-3` as additive shape changes under §4.1 (*Fold*), with the fold records of §5.3. Also ships external code ingestion (`REPRESENTATION.md` §9), pruning-tree distance certificates, formal challenge-certificate generation, `L-TANNER`/`L-TILE` `k` bounds and no-go theorems, `W25`–`W29` Lean replays, planner applicability/canonical-key/layout-provider tooling, and the asserted stress battery. Tagging and publishing remain maintainer-only. |

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
 since. From 2026-11-16 the closed forms of
 `L-HGP` and `A-PRODUCT` were proved modulo the four rank axioms
 `hgp_rankX`, `hgp_rankZ`, `product_rankX`, and `product_rankZ` of
 `lean/extra/ClosedK.lean`. Since 2026-11-24 the four are theorems of
 `lean/CodeCalculus/ClosedK.lean` and the two closed forms rest on no
 assumption (`AXIOMS.md`). The
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

**Not in this candidate (guardrails, the issue tracker §13):** exact-distance
computation as a calculus move; heuristic search results presented as lower
bounds; release-ordinal bumps for machine-only provider work.

## 5.2 `stdCSS-3` inventory published in `v0.3.x`

Everything published in a `v0.3.x` tag belongs to `stdCSS-3` (maintainer
decision, 2026-11-24). Each item below is an instance of an interface that
`stdCSS-3` already has: a command of an existing form, an expression
constructor, a widened input domain, or a conditional cell in the §2g
format with the existing `conditional` status. None adds a grammar sort,
judgment form, evidence status, claim shape, or metatheorem, so none is a
shape change under §4.1. The `stdCSS-3` / `v0.3.1` row of §5 records them;
no item is staged on a later row.

**Published in `v0.3.0`, missing from its row:**

- `C-COLUMN-CNOT` (`cnotSwap(U)`, $U \in \mathrm{GL}(Q, 2)$), a command
  admitted 2026-11-18 (`TERM_LANGUAGE.md` §2; `OPERATIONAL_SEMANTICS.md`
  §4.42).
- `L-MAPPING-CONE` (`cone(∂_A, ∂_B, f_1, f_0)`), admitted 2026-11-18 under
  the chain-map premise (`OPERATIONAL_SEMANTICS.md` §2 card, §4.41).
- `L-EMPTY` (`empty`), `L-FREE` (`free(Q)`), `A-PULLBACK`
  (`pullback(e₁, e₂, e_I; φ₁, φ₂)`), and `A-PUSHOUT`
  (`pushout(e₁, e₂, e_S; ψ₁, ψ₂)`), admitted 2026-11-19 as
  `transition-defined` expression constructors (`TERM_LANGUAGE.md` §1–§2;
  `OPERATIONAL_SEMANTICS.md` §2 cards, §4.43; `JUDGMENT_LAYER.md` §2g,
  §2d.5; `CLAIMS.md`). They carry no automatic distance rule beyond §2g
  (`DistanceLedger.for_constructed`). The Kan-extension candidate remains
  refused.
- The sector-split deletion price cells for `C-DELETE-CHECK`, admitted
  2026-11-19: deleted sector $d'_\tau=\min(d_\tau,w_{\mathrm{del}})$,
  opposite sector $d'_{\bar\tau}=\min(d_{\bar\tau},w_{\mathrm{exp}})$, and
  full distance $d'=\min(d,w_{\mathrm{del}},w_{\mathrm{exp}})$. They are
  conditional on the supplied $w_{\mathrm{del}}$ and $w_{\mathrm{exp}}$,
  which the consumer checks for shape, not truth.

**Published in `v0.3.1`:**

- `L-PAIR-PARTITION` (`pair_partition(p; B_X, B_Z)`), admitted 2026-11-22,
  and `PP-SCALE` (`pp_scale(e; P)`), promoted 2026-11-22, both as
  `transition-defined` expression constructors (`TERM_LANGUAGE.md` §1–§2;
  `OPERATIONAL_SEMANTICS.md` §2 cards, §4.46–§4.47; `JUDGMENT_LAYER.md`
  §2d.5, §2g, §2l; `CLAIMS.md`; `OBLIGATIONS.md` `OBL-PP-SCALE`). Neither
  carries an automatic distance rule beyond §2g; the `PP-SCALE`
  family-level ceiling is `conjectural`.
- Nonabelian finite group inputs for `L-LIFTED`, `L-GROUP-ALGEBRA`, and
  `L-BALANCED` (`OBL-NONABELIAN-GROUP-INPUTS`): groups presented by cyclic
  orders, an explicit multiplication table, or permutation generators
  (`TAXONOMY.md` §1, §3.3–§3.5; `TERM_LANGUAGE.md` §1, §2, §7;
  `OPERATIONAL_SEMANTICS.md` §4.44). Left and right regular representations
  commute over $\mathbb{F}_2$ and agree for abelian groups, so the widening
  is conservative on the abelian fragment. The abelian $k$ closed form does
  not extend: an explicit $D_4$ instance refutes it (§4.44).
- Conditional constructor distance cells and factor-to-child witness
  lifting for `L-HGP`, `L-NESTED-CSS`, `A-CONCAT`, `A-PRODUCT`, and
  `A-DOUBLE` (`OBL-CONDITIONAL-CONSTRUCTOR-CELLS`; `JUDGMENT_LAYER.md` §2g,
  §2g.1; `OPERATIONAL_SEMANTICS.md` §4.45). The lower-bound cells are priced
  hypotheses, not proved bounds.

The consumer capabilities that also shipped in `v0.3.1` (objective-aware
search, applicability diagnostics, constructor screening and separation,
stop and budget reporting) are tooling under §4.1. They change no axis,
rung, or obligation status.

**Instance-contract record (completed 2026-11-25, issue #657).** The 2026-11-24
transitional clause is retired: every item above now meets all six items of the
§4.2 instance contract, recorded item by item below, and no `discharged-through`
value moves. §4.2 continues to bind every admission from 2026-11-24 on.

**Expression constructors (`L-MAPPING-CONE`, `L-EMPTY`, `L-FREE`, `A-PULLBACK`,
`A-PUSHOUT`, `L-PAIR-PARTITION`, `PP-SCALE`, and the multiplication-table
productions of the nonabelian inputs for `L-LIFTED`, `L-GROUP-ALGEBRA`, and
`L-BALANCED`).** Every item has:
- a taxonomy ID, grammar production, §2 card, contract row in `CLAIMS.md`,
  update-ownership row in `STATE_MODEL.md` §4, and matching entries in
  `machine/state.json`, `machine/semantics.json`, and
  `machine/operation_registry.json` (including `L-MAPPING-CONE`);
- a hand derivation of output well-formedness (§4.41, §4.43, §4.44, §4.46,
  §4.47), mechanized for every `StateExpr` constructor by `wf_of_evalExpr`
  (`lean/CodeCalculus/ExpandedSoundness.lean`);
- single-valuedness on fixed presentations, recorded in §4.40 item 2 and
  `OBL-PRIMITIVE-DETERMINISM` and mechanized for every `StateExpr` constructor
  by `evalExpr_unique` (`ExpandedSoundness.lean`);
- structural carry rows recorded in §4.40 item 12 and `OBL-JUDGMENT-SOUNDNESS`
  and mechanized under `ext_judgment_soundness_of_term` (`ExpandedSoundness.lean`:
  `instExprWF` for all constructors, `instConeN`/`instConeK`,
  `instEmptyN`/`instEmptyK`, `instFreeN`/`instFreeK`, `instPullbackN`,
  `instPushoutN`, `instPairPartitionN`, `instPpScaleN`, `instLiftTableN`,
  `instTwoblockTableN`, and `instBalancedTableN`; no automatic distance rule
  beyond §2g, and no nonabelian `k` closed form).

**Command (`C-COLUMN-CNOT`).** Has:
- a taxonomy ID, grammar production (`TERM_LANGUAGE.md` §2), carry rows in
  `JUDGMENT_LAYER.md` §2k, a §2 card in `OPERATIONAL_SEMANTICS.md`, an
  update-ownership row in `STATE_MODEL.md` §4, a contract row in `CLAIMS.md`,
  and entries in `machine/state.json`, `machine/semantics.json`, and
  `machine/operation_registry.json`, with executable counterpart
  `machine/css_preserving_cnot_swap.py`;
- a dated hand derivation of well-formedness, $n' = n$, $k' = k$,
  inapplicability/malformation behavior (meeting `transition-defined`),
  single-valuedness, `steps` inertness, and sequence associativity (§4.42);
- a constructor `Command.cnotSwap` and rule `Eval.cnotSwap` in Lean
  (`Term.lean`, `Eval.lean`, `ColumnCnot.lean`), so `eval_unique`,
  `eval_deterministic`, `denote_eval`, `denote_seq_assoc`,
  `seq_assoc_fwd`/`bwd`, `eval_cnotSwap_skip_left`/`right`, `StepChain`,
  `Derives.genCnotSwap`, and `ext_judgment_soundness_of_term`
  (`instCnotSwapN`, `instCnotSwapK`, `instCnotSwapWF`, `genCnotSwap`) cover
  it, with an explicit well-formedness qualification: `Eval.cnotSwap` takes
  `EncodingWellFormed s'` as a premise, so `wf_of_eval_all` and
  `instCnotSwapWF` cover `Command.cnotSwap` through the well-formedness
  premise its transition carries (a premise restatement rather than a
  mechanized proof of I1–I5 preservation), and `eval_cnotSwap_k` relies on
  that premise as well; the theorem that an invertible column map $U$
  preserves I1–I5 is hand-derived in `OPERATIONAL_SEMANTICS.md` §4.42 and
  not mechanized in Lean.

**Conditional cells.** The sector-split `C-DELETE-CHECK` price cells are
covered by the `C-DELETE-CHECK` case of `OBL-PRICED-INTERVAL-SOUNDNESS`
(§4.13, priced sector-split bullet). The conditional constructor cells are
covered by `OBL-CONDITIONAL-CONSTRUCTOR-CELLS` (§4.45; `LedgerSound` in
`lean/CodeCalculus/PricedInterval.lean`), under their hypotheses (`OBL-PRICED-INPUT-SEMANTICS`).

**Restricted metatheorems (§4.2 item 6).** Every item above lies outside
the named fragments of `OBL-ORDER-INDEPENDENT-DELETION`,
`OBL-CROSS-SECTOR-PERMUTATION`, `OBL-FIXED-NAMESPACE-REACHABILITY`,
`OBL-PRESENTATION-CONJUGATION`, and `OBL-DERIVED-TERM-FACTORIZATION`, since
none is a kernel command or `E-GRAFT` (and `C-COLUMN-CNOT` is a primitive
extension command). `OBL-JUDGMENT-TRANSPORT` covers `C-COLUMN-CNOT` in command
sequences (`SeamChains.lean`, `ExpandedSoundness.lean`) and excludes expression
constructors from command-sequence position (they enter at chain position 0).
`OBL-PRICED-INTERVAL-SOUNDNESS` is restricted to the core §8.3 transformers:
the sector-split cells lie inside it as above, `C-COLUMN-CNOT` widens to reset
in `propagateCmd` (governed by §2k/§4.42), and the constructors and their
conditional cells lie outside it.

**Scope of the dispositions.** The metatheorem dispositions in
[`OBLIGATIONS.md`](OBLIGATIONS.md) (*Re-discharge status of metatheorems*,
*Scope of `stdCSS-3`*) and [`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md)
§4.40 now name every item above. No `discharged-through` value moves.

**Dated note (2026-11-25, updated 2026-11-26; Gate 7 completeness obligation,
issue #606).** By dated maintainer decision (MathysRennela, Option (a)), the
scoped non-circular completeness obligation `OBL-ELEMENTARY-COMPLETENESS` is
opened in [`OBLIGATIONS.md`](OBLIGATIONS.md) at status `open`, backed by the
feasibility argument in [`TAXONOMY.md`](TAXONOMY.md) (*Completeness
feasibility decision*). Originally staged for `stdCSS-4` (`v0.4.0`) under §4.1,
it was folded into `stdCSS-3` / `v0.3.2` by maintainer decision on 2026-11-26
(alongside issue #572; §5.3). No existing §5 release row is edited, the
obligation remains `open`, and no `stdCSS-3` `discharged-through` value moves.

## 5.3 `stdCSS-3` inventory published in `v0.3.2`

Each item in the first group below was admitted after 2026-11-24 under the
instance contract of §4.2, item by item, as patch-level `stdCSS-3` inventory.
The second group records the two items originally staged for `stdCSS-4` that
were folded into `stdCSS-3` / `v0.3.2` by maintainer decision on 2026-11-26.
The `stdCSS-3` / `v0.3.2` row of §5 records them.

- **`E-EXTEND` distance-loss cell** (2026-11-26, issue #677). This is a new
  conditional cell of an existing format on an existing command, for
  $\Delta\neq\varnothing$. The §4.2 items are met as follows:
  1. The taxonomy ID, the production and the update-ownership row exist
     unchanged.
  2. The card is unchanged, and so is the well-formedness derivation
     (`OPERATIONAL_SEMANTICS.md` §4.30): the cell moves no state.
  3. Single-valuedness is unchanged. The cell reads its hypothesis and no
     `steps`.
  4. The structural rows are unchanged. The distance rows of
     `JUDGMENT_LAYER.md` §2a, §2b and the cell table record the cell.
  5. The format is the existing conditional-price format (cf. `peel_price`),
     with evidence status `conditional`, and the hypothesis is named as a
     priced input (`extend_distance_loss`, `OBL-PRICED-INPUT-SEMANTICS`).
  6. The dispositions are in `OBLIGATIONS.md`, *Re-discharge status of
     metatheorems*. The cell is covered by hand derivation only
     (`OBL-EXTEND-DISTANCE-LOSS`). It lies outside the core §8.3 slice of
     `OBL-PRICED-INTERVAL-SOUNDNESS` and outside the Lean
     `gate6_interval_soundness`, which covers the unpriced `E-EXTEND`
     transformer.

- **Coset inputs for `L-LIFTED`** (2026-11-26, issue #675). This is a widened
  input domain of the existing constructor: the production
  $\mathrm{lift}_{G;H}(A, B)$ takes a subgroup $H \le G$, with $B$ over
  $\mathbb{F}_2[N_G(H)]$. The §4.2 items are met as follows:
  1. The taxonomy ID exists, the production is in `TERM_LANGUAGE.md` §1, and
     the update-ownership row is in `STATE_MODEL.md` §4.
  2. The card is at `OPERATIONAL_SEMANTICS.md` §2, and the dated
     well-formedness derivation at §4.49.
  3. Single-valuedness is in §4.49 (not a command, so no `steps` item).
  4. The $n$ and $k$ rows are in `JUDGMENT_LAYER.md`; the other structural rows
     are those of the regular lift.
  5. Not applicable: this is not a cell.
  6. The dispositions are in `OBLIGATIONS.md`, *Re-discharge status of
     metatheorems*. The instance is covered by hand derivation only and lies
     outside every Lean `StateExpr` theorem.

  No Lean counterpart exists (`OBL-COSET-LIFT-INPUTS`, *Owed*).

- **Split-subset `E-LOCAL-HADAMARD`** (2026-11-26, issue #571). This is a
  widened input domain of the existing command `hadamard(T)`: it admits
  $\varnothing\subsetneq T\subsetneq Q$ under the decidable row-space
  splitting guard, and the canonical-mint rule is unchanged. The §4.2 items
  are met as follows:
  1. The taxonomy ID and production already exist, and the update-ownership
     row is in `STATE_MODEL.md` §4.
  2. The card is at `OPERATIONAL_SEMANTICS.md` §2, and the dated
     well-formedness derivation at §4.27(b).
  3. The update is a deterministic function of the state: it reads displayed
     rows in identifier order (the order of the fixed identifier enumeration)
     both for the seed and for the mixed-row pass, so it is single-valued
     (`eval_deterministic`) and $\equiv$-input invariant
     (`splitHadamardState_equiv`), and reads no `steps`.
  4. The carry rows are in `JUDGMENT_LAYER.md` §2b, §2d.2, §2d.5, §2f and
     §9.4, and the $\mathsf{gen}_i$ row in §4.
  5. Not applicable: this is not a cell.
  6. The per-metatheorem dispositions are in `OBLIGATIONS.md`, *Re-discharge
     status of metatheorems*.

  Lean mechanizes the transition, determinism, well-formedness (as a
  checked premise), and the structural and generator rows. For the exact
  distance it also mechanizes the ledger's relations $d'=d$ and
  $d_\sigma'\ge d$ (`lean/CodeCalculus/SplitHadamard.lean`). The
  factor-code closed forms of §4.27(b) are hand-derived.

- **`E-SPLIT` separating deletion** (2026-11-25, issue #546): admitted by
  dated maintainer decision (MathysRennela) at rung 3 (`transition-defined`,
  `introduced-in: stdCSS-3 / v0.3.2`) as the command production
  $\mathrm{split}_{Q_A; R}$ over an explicit cut $(Q_A, R)$
  (`TERM_LANGUAGE.md` §1–§2; `OPERATIONAL_SEMANTICS.md` §2, §4.48), derived
  over `C-DELETE-CHECK` and `C-SEQUENCE`, while the two-state projection
  reading is refused (returning two states would be a production of a new
  form, a §4.1 shape change that is never folded because it changes the
  evaluation relation every metatheorem quantifies over).
  Satisfies all six items of §4.2 at admission (§4.48 item 10): (1) taxonomy
  ID, command production, and update-ownership row (`STATE_MODEL.md` §4,
  `machine/state.json`); (2) §2 card and §4.48 well-formedness derivation
  (`wf_of_eval_all`); (3) single-valuedness and `steps` inertness
  (`eval_unique`, `KernelObligations.lean`); (4) structural, layout, and `W13`
  carry cells (`JUDGMENT_LAYER.md`, `ExpandedSoundness.lean`); (5) conditional
  `split_block_intervals` cell (`OBL-PRICED-INPUT-SEMANTICS`,
  `OBL-GATE6-CSS-EXTENSIONS`, consumer and Lean support); and (6) explicit
  dispositions for every fragment-restricted metatheorem. Existing §5 release
  rows are not edited; no re-discharge obligation is re-opened.

**Folded into `stdCSS-3` / `v0.3.2` (§4.1, *Fold*; maintainer decision
2026-11-26).** The two items below are shape changes under §4.1. Both are
additive, and by dated maintainer decision (MathysRennela, 2026-11-26) both
are folded into `stdCSS-3` / `v0.3.2` rather than opening `stdCSS-4`. The
fold record of §4.1 is given for each.

- **Frame-reading gate predicates (issue #572, admitted 2026-11-26).** Four
  operator- and frame-indexed assertion predicates on CSS displays,
  $\mathsf{preserves}_U(C \mid F)$, $\mathsf{phase}_U(C \mid F) = z$,
  $\mathsf{image}_U(C; e) \equiv P$, and $\mathsf{addresses}_U(C; F, A)$,
  reading the logical-witness field as a frame supplied with the state
  ([`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2h, Rows C–F;
  [`STATE_MODEL.md`](STATE_MODEL.md) §1a, *Eigenvalue reading*; hand
  derivations at [`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md)
  §4.37, Lemmas 5–11). The same derivations decide the `C-ADD-CHECK` cell of
  $\mathsf{preserves}_U$ for every rational angle $\theta_j \in \pi\mathbb{Q}$
  (Corollary 7.1; other angles have no admitted decision procedure and stay
  `not yet defined`), replacing its `not yet defined` non-$\pi/4$ branch by a
  proved cell. No state field, equality clause, invariant, grammar production,
  or taxonomy operation identifier changes, so
  $C = (Q, X, Z, \mathsf{pres}, \mathsf{used})$ is unchanged.
  The fold record:
  1. *Row:* new assertion predicate (§4.1, axis 3).
  2. *Why additive:* the four predicates are new rows beside the existing
     ones. No existing judgment form, predicate, evidence status, claim
     shape, or grammar form changes, and no existing derivation changes. The
     any-angle `C-ADD-CHECK` cell replaces a `not yet defined` branch, from
     which nothing was derivable. No metatheorem's statement changes on the
     interfaces its disposition names.
  3. *Evidence:* the cells of `JUDGMENT_LAYER.md` §2h Rows C–F stand on the
     dated hand derivations of `OPERATIONAL_SEMANTICS.md` §4.37 (Lemmas
     5–11), and are not mechanized.
  4. *Not yet covered:* no §4.40 metatheorem disposition names Rows C–F. In
     particular `OBL-JUDGMENT-SOUNDNESS`, `discharged-through` `stdCSS-3`,
     covers the judgment rows its disposition names and not these
     ([`OBLIGATIONS.md`](OBLIGATIONS.md), *Re-discharge status of
     metatheorems*).
  5. *Owed:* the §4 re-discharge audit of `OBL-JUDGMENT-SOUNDNESS` and the
     other metatheorems against Rows C–F. No `discharged-through` value
     advances until it lands.
- **Scoped elementary completeness obligation (`OBL-ELEMENTARY-COMPLETENESS`,
  issue #606, opened 2026-11-25).** Recorded in
  [`OBLIGATIONS.md`](OBLIGATIONS.md) as `Introduced in: stdCSS-3 / v0.3.2`
  at status `open`, backed by the feasibility sketch in
  [`TAXONOMY.md`](TAXONOMY.md) (*Completeness feasibility decision*). No
  completeness theorem is claimed for `stdCSS-3` / `v0.3.2`, and deliberate
  judgment incompleteness is unchanged. The fold record:
  1. *Row:* new metatheorem (§4.1, axis 4).
  2. *Why additive:* the obligation is new and `open`. It changes the
     statement of no existing metatheorem and asserts nothing.
  3. *Evidence:* the feasibility sketch only; it claims no theorem.
  4. *Not yet covered:* the obligation has no `discharged-through` value.
  5. *Owed:* its own discharge, or a dated restriction of its statement.

Neither fold extends a `discharged-through` value. A reader of
"`discharged-through` `stdCSS-3`" reads it on the interfaces and instances
named in the metatheorem's disposition (§6), which from `v0.3.2` on is
narrower than everything `stdCSS-3` contains.

## 5.4 Candidate next ordinal (`stdCSS-4` / `v0.4.0`)

No items are currently staged for `stdCSS-4` / `v0.4.0`: by maintainer
decision on 2026-11-26, issues #572 and #606 were folded into `stdCSS-3` /
`v0.3.2` (§5.3). The next shape change under §4.1 that is not folded opens
`stdCSS-4` / `v0.4.0`.

## 6. Item-level conventions and owners

Declared here; applied where each item is owned.

- **`introduced-in`** — the release that first published the item, written
 `<ordinal> / <tag>` (for example `stdCSS-3` / `v0.3.1`). Absent means
 `stdCSS-1`. An item admitted on `main` and not yet tagged reads
 `<ordinal>` followed by `(unreleased)`; the tag is filled in when the release
 is prepared.
- **`discharged-through`** — the latest ordinal for which the item's proof has
 been (re-)established, covering the interfaces and instances its disposition
 names (§4.2). An interface folded into that ordinal (§4.1, *Fold*) is not
 covered until a disposition names it.

| Fact | Owner |
| --- | --- |
| grammar production introduction | CSS_CODE_CALCULUS_PROPOSAL_DRAFT.md §3.2 |
| contract admission | [`CLAIMS.md`](CLAIMS.md) |
| obligation introduction and discharge | [`OBLIGATIONS.md`](OBLIGATIONS.md) |

This note references those files; it does not restate their contents.

## 7. Non-goals

- no retrofit of `stdCSS-1` tags onto existing entries;
- no mechanization in the current phase;
- no version counter beyond the line/ordinal and the software tag, and no
 per-layer counters;
- no release-ordinal or software-MINOR bump for inventory, proof,
 machine-only, or documentation work; such changes are PATCH only (§4.1, §8).

**Dated note.** The six Gate 6 CSS-level productions
(`P-REBASE`, `E-LOCAL-HADAMARD`, `E-PEEL`, `E-PUNCTURE`, `E-EXTEND`,
`E-GLUE`) are in scope as conditional cells under `stdCSS-2` (admitted
2026-10-23). Their addition creates re-discharge obligations for the
metatheorems scoped to the `stdCSS-2` operation set: each affected
metatheorem's `discharged-through` does not advance until it is re-established
against the expanded operation set. The six rows are recorded in the
update-ownership table of `spec/STATE_MODEL.md` §4 and `machine/state.json`.


## 8. Software release track (`vMAJOR.MINOR.PATCH`)

The repository is released as a software artifact, tagged
`vMAJOR.MINOR.PATCH` (e.g. `v0.1.0`; the bare `v0.1` form is legacy). A tag
pins the whole repository (`spec/`, `machine/`, `lean/`, docs, CI), and with
it the exact inventory of the calculus. The tag and the calculus ordinal are
one track: each version component answers one question.

| Component | Question it answers | Bumps when |
| --- | --- | --- |
| **MAJOR** | Is the research objective met? | `v1.0.0`: the `stdCSS` stopping point is reached ([`../design/SCOPE.md`](../design/SCOPE.md) §3: its in-scope transformations, properties, and cells are admitted and the soundness metatheorem is mechanized for the current ordinal, with every admitted instance named in its dispositions and none `open`). After `v1.0.0`: a new calculus line (new state model), a non-conservative change breaking existing derivations, or removal of an admitted operation. |
| **MINOR** | Which calculus is this, up to folds? | A shape change under §4.1 that is not folded, together with the new ordinal and its §5 row. From `v0.4.0` on, software `v0.N.x` publishes `stdCSS-N`. A folded shape change (§4.1, *Fold*) ships at PATCH; the tag, not the ordinal, then fixes the exact interfaces (§3). |
| **PATCH** | How much of it is admitted, proved, and usable? | Anything else: inventory instances meeting §4.2, proofs and advanced `discharged-through` values, gate ratifications and refusal decisions, consumer and machine features and fixes, transcription fixes, documentation, CI, Lean hygiene. |

**The bump is computed; a fold is a recorded decision.** When a release is
prepared, each change merged since the previous tag is classified by the §4.1
table, and each instance among them is checked against §4.2: the release
preparation records, per instance, where each contract item is met. The
release is a MINOR if it contains a shape change that is not folded (§4.1,
*Fold*: additive, folded by dated maintainer decision, with its fold record);
otherwise it is a PATCH. Whether a shape change is
eligible for a fold is computed from §4.1; whether to fold it is the
maintainer's decision, never an agent's. An instance
that fails §4.2 is completed before the tag or reverted; it never ships as
inventory. Milestones and issue titles state intent and do not fix the
label.

**Every tag has a §5 row.** A PATCH row names the same ordinal as the row
before it and records the inventory and discharge status at that tag. A
MINOR row names the new ordinal and records the re-discharge status the §4
audit reached; a metatheorem not yet re-established keeps its previous
`discharged-through` value.

**Alignment.** The earlier tags do not follow the equation above: `v0.1.0`
published `stdCSS-2`, and `v0.2.0`, `v0.3.0`, `v0.3.1`, and `v0.3.2` publish
`stdCSS-3`. They are not renumbered. The first MINOR under this section is
`v0.4.0`, which publishes `stdCSS-4`, so the two numbers agree from there.

**Validation.** Every release, of either kind, requires the validation gates
green on the release commit: lint, pytest, fixture conformance, the priced
harness, and `lake build`.

**Tagging and publishing are maintainer-only** (AGENTS.md *Hard rules*). A
release is prepared (four-axis pin recorded, changelog drafted, row drafted)
but not tagged by an agent; the maintainer appends the release row and tags
in the same change.

**Dated note (2026-11-16).** The four rank axioms of
`lean/extra/ClosedK.lean` (`hgp_rankX`, `hgp_rankZ`, `product_rankX`,
`product_rankZ`) are accepted as `proposed (classical)` assumptions and
recorded in `AXIOMS.md`; the associated work item was closed on that
condition. The arithmetic that combines the ranks
(`hgp_arith`, `product_arith`) remains proved. This is a mechanization
status change only: it advances no `discharged-through` value, creates no
new calculus row, and does not make the rank identities `established`.

**Dated note (2026-11-24).** The four rank statements of the note above
are theorems of `lean/CodeCalculus/ClosedK.lean`, an audited module, and
`lean/` declares no axiom (`AXIOMS.md`). This is a mechanization status
change only: it advances no `discharged-through` value and creates no new
calculus row. Whether the closed forms for $k$ of `L-HGP` and `A-PRODUCT`
now read `established` is a maintainer decision and is not made by this
note.

**Dated note (2026-11-16, CI).** The validation workflow's scaled
conformance case count was reduced to `SCALED_CASES=500`; this is a machine-only change with no calculus-axis effect and no
release-row change.
