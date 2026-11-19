# Roadmap

**Role:** public design note. This is the index of everything
**planned but not yet normative**, so that a tentative feature can be found,
promoted, or dropped deliberately rather than by forgetting.

It is not a specification and it decides nothing. The calculus's mechanics live in
`spec/`, which wins on any shared ground. Where an entry here
describes a rule, `spec/` states it.

**Why this file exists.** The admission ladder in
`spec/CLAIMS.md` §1 is a real promotion mechanism, but it had
no index: "what is coming" was scattered across the taxonomy, the Gate 6/7
sections of the proposal, the `not yet defined` rows of the claim inventory, and
four archived survey notes. A ladder nobody consults is not a mechanism.

## The ladder

Restated from `spec/CLAIMS.md` §1, which is authoritative:

```
taxonomy-only → syntax-candidate → transition-defined → state-sound
              → contract-stated  → contract-proved    → mechanized
```

`contract-draft` is a document label for an incomplete record, **not** a stage. A
draft or planned transition is not an admitted calculus rule.

## §1 The kernel, staged

**Promoted to rung 6 (`contract-proved`) on 2026-11-18 (issue #535).** All five
kernel operations (`C-SKIP`, `C-DIRECT-SUM`, `C-DELETE-CHECK`, `C-ADD-CHECK`,
`C-SEQUENCE`) reached rung 5 (`contract-stated`) on 2026-10-27 (Gate 0;
rung-4 well-formedness derivations at `spec/OPERATIONAL_SEMANTICS.md` §4.7,
2026-10-20) and are promoted to **rung 6 (`contract-proved`)** by dated
maintainer decision on 2026-11-18 (issue #535;
`an internal note`).
Every kernel operation carries its typed transition, complete applicability
conditions, exact state/context update, unconditional theorem-level derivations
(including quotient-level logical-sector exact sequences at §4.39), conditional
carry cells (with stated hypotheses), and `stdCSS-3` metatheorem re-discharge
records (§4.40, `../spec/OBLIGATIONS.md`).

| Operation | Rung | Transition & applicability | State/context update & carry cells | Derivations & re-discharge |
| --- | --- | --- | --- | --- |
| `C-SKIP` | 6 — `contract-proved` | `m ::= skip`; no premises (`OPERATIONAL_SEMANTICS.md` §1, §2) | identity on $Q$, display, `used` (inert `steps`); all carry cells unconditional identity (`JUDGMENT_LAYER.md` §2, §2b, §2d.5, §2h) | §4.6–§4.8, §4.11, §4.13, §4.21–§4.22, §4.37, §4.40 |
| `C-DIRECT-SUM` | 6 — `contract-proved` | `e ::= e₁ ⊕ e₂`; $Q_A \cap Q_B = \varnothing$, $\mathsf{used}_A \cap \mathsf{used}_B = \varnothing$ (§2) | disjoint union of $Q$, display, `used` (no mint); exact `min` distance & structural cells; conditional honest merged layout for $r$ (§2d.3, §2d.5) and allocation-compatible addition clause of `OBL-FRAME-LAW` (§4.9) | §4.4, §4.7–§4.9, §4.11, §4.13, §4.21–§4.22, §4.37, §4.39, §4.40 |
| `C-DELETE-CHECK` | 6 — `contract-proved` | `m ::= delete_r`; `DisplayedGenerator` + `Independent` (§2) | removes $r$, retires id in `used` (no mint); non-increase upper bound `[proved]`, unpriced exact `unavailable`; conditional full-distance price $d' = \min(d, w_{\mathrm{del}}, w_{\mathrm{exp}})$ (`JUDGMENT_LAYER.md` §2a–§2c) | §4.1, §4.5, §4.7–§4.11, §4.13, §4.15–§4.19, §4.21–§4.22, §4.37, §4.39, §4.40 |
| `C-ADD-CHECK` | 6 — `contract-proved` | `m ::= addStab_r`; $\mathrm{supp}(r) \subseteq Q$ (`W22`), opposite-sector commutation, same-sector independence, H-4 capacity (§2) | appends $r$ with canonical mint in `used`; nondecrease lower bound `[proved]`, exact `open`; three conditional cells (`JUDGMENT_LAYER.md` §2a–§2c): strict improvement (Prop. 18.3), sector-aware gauging (Lemma 18.5), direct-sum extinction (Prop. 18.6 + Cor. 18.7) | §4.2–§4.3, §4.7–§4.11, §4.13, §4.16–§4.19, §4.21–§4.22, §4.37, §4.39, §4.40 |
| `C-SEQUENCE` | 6 — `contract-proved` | `m ::= m₁ ; m₂`; left-to-right composition of sub-command premises (`W10`, §1, §2) | intermediate state feeds $m_2$; structural persistence & single-polarity distance composition `[proved]` (§4.11; mixed opposite-polarity exact-quantity chains `open`, `W13` `unavailable`); conditional step-wise interval composition (`OBL-PRICED-INTERVAL-SOUNDNESS`, §4.13, §8.5) | §4.6–§4.8, §4.10–§4.11, §4.13, §4.15, §4.17, §4.21–§4.23, §4.37, §4.40 |

Rung 6 records hand-derivation evidence (`proved`), not rung 7 (`mechanized`)
and not Gate 2–5 ratification: rung 7 remains open (tracked across issues #533
and #534), and Gates 2–7 remain unchecked (`../spec/GATES.md`).

## §2 The queue

Everything not yet normative. **Rung** is the ladder position; **promotion
criterion** is what would have to become true.

### Admitted to the kernel — out of scope for the MVP

The stopping point ([`SCOPE.md`](SCOPE.md)) excludes these. They are not
abandoned, and they are not open questions; they are deferred with a reason.

| Entry | Rung | Blocked by | Promotion criterion |
| --- | --- | --- | --- |
| `P-RELABEL` | 1 — `taxonomy-only` (contract-index row staged 2026-10-25; previously listed here as *unrecorded*) | no grammar production | A decision to admit relabeling as ordinary syntax, plus `OBL-PRESENTATION-CONJUGATION` discharged |
| `OBL-PRESENTATION-CONJUGATION` | — obligation, not an operation | out of scope | D-6's canonicalization step is admitted to the calculus |

`P-REBASE` and `OBL-REBASE-GENERATION` were removed from this deferred table
on 2026-10-23, when the Gate 6 decision admitted `P-REBASE` as a conditional
cell and `OPERATIONAL_SEMANTICS.md` §4.26 discharged the generation obligation.
They are recorded in the Gate 6 section below.

**Issue #21 update (2026-10-19).** `E-GRAFT` is now
`transition-defined` as a conditional construction extension and appears in
`spec/TERM_LANGUAGE.md` and
`spec/OPERATIONAL_SEMANTICS.md`. The
full-distance deletion price and strict-improvement cell are judgment inputs,
not new operations. `A-CONCAT` tower factorization is a price provider, not an
admitted constructor.

### Gate 6 CSS extensions and `P-REBASE`

**Scope decision 2026-10-23 (maintainer decision, `DIARY.md`).** Five CSS-level
extensions (`E-GLUE`, `E-PEEL`, `E-PUNCTURE`, `E-EXTEND`,
`E-LOCAL-HADAMARD`) plus presentation rebasing (`P-REBASE`) are **admitted as
conditional cells** and are now in scope under the stopping point. The
admission is recorded as conditional rows at
`spec/JUDGMENT_LAYER.md` §2f and as the soundness
obligation `OBL-GATE6-CSS-EXTENSIONS`
(`spec/OBLIGATIONS.md`). **Restricted transitions are defined** for all six (`E-GLUE` remains
binary-only as the expression constructor `glue(e₁, e₂; seams)` with no unary
command production, decided 2026-11-18, issue #536; evaluator transition
admitted 2026-10-27, `OPERATIONAL_SEMANTICS.md` §4.31):
each admitted move still sits at its recorded ladder rung. Sound admission
is discharged under the stated hypotheses (`OBL-GATE6-CSS-EXTENSIONS`,
§4.32), but the moves remain conditional cells and are not admitted
calculus rules. The §4.32 transformers are mechanized in
`lean/CodeCalculus/Gate6Soundness.lean` (issue #311), conditional on the
§4.26 to §4.30 distance relations. The
non-CSS extended-state layer (`X-SYMPLECTIC-DOUBLE`/`X-SYMPLECTIC-HALVE`) is
**not** admitted by this decision, and is refused for `v0.3.0` (issue #545,
2026-11-18).

| Entry | Rung | Status |
| --- | --- | --- |
| `E-GLUE` | 5 — `contract-stated` (2026-11-18, issue #536) | admitted 2026-10-23 as a conditional cell; **binary-only expression constructor `glue(e₁, e₂; seams)` with no unary command production** (`TERM_LANGUAGE.md` §1–§2, decided 2026-11-18, issue #536). Both future-$\Pi$ fields are defined in full (`STATE_MODEL.md` §1a, issues #332, #366, #440; `WitnessFields.lean`), the §2e equality is discharged by extraction of Theorem 4 / claim 7.4 (`OPERATIONAL_SEMANTICS.md` §4.31), and interval-transformer soundness is discharged under the stated hypotheses (`OBL-GATE6-CSS-EXTENSIONS`, §4.32). All CSS-level algebra of §4.31/§4.33 — state soundness (`wf_glueState_of_eval_glueCommand`, `evalExpr_glue_iff_evalTerm_glueCommand`), $w_{\mathrm{re},\sigma} = +\infty$, Theorem 4 lower bound, Claim 2 Steps 1 & 3–5, Consequence (iii), issue #398 refutation, and `AdmissibleSeam` $\to$ `glueField` / `glueLedger` soundness — is mechanized across `ExactGlue*.lean`, `LogicalWitness.lean`, `AdmissibleSeamFamily.lean`, `Gate6Exact.lean`, and `GlueExtraction.lean` (issue #536), with the irreducible geometric move-word $\to$ `AdmissibleSeam` gap explicitly recorded (`ADMISSIBLE_SEAM_FAMILY.md` §4, §7). Full §1–§12 contract stated in `CLAIMS.md`; remains a Gate 6 conditional cell (not `contract-proved`, Gate 6 unchecked) |
| `E-PEEL`, `E-PUNCTURE` | 3 — `transition-defined` (contract-index rows staged 2026-10-25; previously listed here as rung 1) | admitted 2026-10-23 as conditional cells; typed transitions landed 2026-10-25 (`TERM_LANGUAGE.md` §2; `OPERATIONAL_SEMANTICS.md` §4.28, §4.29, issue #119); interval-transformer soundness discharged under the stated hypotheses (`OBL-GATE6-CSS-EXTENSIONS`, §4.32); the move stays a conditional cell, not an admitted calculus rule |
| `E-EXTEND` (patch growth / breeding) | 3 — `transition-defined` (contract-index row staged 2026-10-25; previously listed here as *unrecorded*) | admitted 2026-10-23 as a conditional cell; typed transition landed 2026-10-25 (`OPERATIONAL_SEMANTICS.md` §4.30, issue #119); interval-transformer soundness discharged under the stated hypotheses (`OBL-GATE6-CSS-EXTENSIONS`, §4.32); the move stays a conditional cell, not an admitted calculus rule |
| `E-LOCAL-HADAMARD` | 3 — `transition-defined` (contract-index row staged 2026-10-25; previously listed here as rung 1) | admitted 2026-10-23 as a conditional cell; typed transition landed 2026-10-25 ($T=Q$ only, `OPERATIONAL_SEMANTICS.md` §4.27, issue #119); interval-transformer soundness discharged under the stated hypotheses (`OBL-GATE6-CSS-EXTENSIONS`, §4.32); the move stays a conditional cell, not an admitted calculus rule |
| `P-REBASE` | 3 — `transition-defined` (contract-index row present) | admitted 2026-10-23 as a conditional cell; transition defined (`TERM_LANGUAGE.md` §2, `rebase(τ; M)`; `OPERATIONAL_SEMANTICS.md` §4.26); `OBL-REBASE-GENERATION` discharged by §4.26; rank-preservation mechanization landed (machine-checked: `sectorRank_rebaseState`, `stateK_rebaseState` in `lean/CodeCalculus/RebaseRankSector.lean`, issue #128); interval-transformer soundness discharged under the stated hypotheses (`OBL-GATE6-CSS-EXTENSIONS`, §4.32); the move stays a conditional cell, not an admitted calculus rule |

**`OBL-REBASE-GENERATION` (discharged 2026-10-23).** The obligation minted on
2026-10-11 was discharged by the §4.26 hand derivation once the Gate 6 decision
gave `P-REBASE` a transition. The result is an equality of transformation sets
modulo mint conventions, not an equivalence of labeled states; the Lean
rank-preservation slice landed as issue #128 (machine-checked under `rebaseMatrix_ok`; pointers at `lean/CodeCalculus/RebaseRankSector.lean`).

**Still unadmitted** — not covered by the 2026-10-23 decision:

| Entry | Rung | Needs |
| --- | --- | --- |
| `E-SPLIT` | 1 — `taxonomy-only` (contract-index row staged 2026-10-25; previously listed here as *unrecorded*) | merge/split routing; Gate 6 admission decision still owed. A candidate transition and its judgments are stated as a proposal in `E_SPLIT_PROPOSAL.md` (issue #546), which decides nothing |

**Promotion criterion, common to the admitted moves:** state the typed
transition, the applicability conditions, the exact state/context update, and
the conditional carry cell (`spec/JUDGMENT_LAYER.md` §2f), so the ladder
reaches `transition-defined`. Discharging `OBL-GATE6-CSS-EXTENSIONS` (§4.32)
records a sound, monotone interval transformer under the stated hypotheses;
it does **not** by itself advance the ladder rung, promote the move to
`state-sound` or `contract-proved`, or make it an admitted calculus rule.
The move remains a conditional cell subject to its hypotheses, and its
property claims keep the evidence status of those hypotheses. `E-SPLIT`
remains unadmitted Gate 6 work: it is out of scope under the stopping point
until a maintainer decision admits it.

### Gate 6 candidates — extended-state (non-CSS) layer

**Refused for `v0.3.0` (issue #545, 2026-11-18).** The maintainer has refused
admission of the extended-state layer for `v0.3.0`: the state model stays
`C=(Q,X,Z,pres,used)`, the four records stay at `taxonomy-only`, and
`machine/symplectic_calculus.py` stays a consumer-side model that admits
nothing. Reopening requires a reviewed design note for the two-sorted state
model (including the sign decision and the embedding of the CSS line), a
re-evidencing plan, and a per-move decision starting with the two symplectic
moves (diary entry
`2026-11-18-refuse-admission-of-the-extended-state-layer-issue-545.md`).

**Rung: 1 — `taxonomy-only`.** A two-sorted state model (ordinary CSS as
special case plus a general stabilizer state presented by a symplectic check
matrix), with cross-layer moves between them. Scoped in
`an internal note`
(2026-09-29); Gate 6 decides whether the extension enters. Leading moves:

| Entry | Needs |
| --- | --- |
| `X-SYMPLECTIC-DOUBLE` | general stabilizer → CSS, $n'=2n$, $k'=2k$, $d \le d' \le 2d$; inverse always applicable to doubled outputs |
| `X-SYMPLECTIC-HALVE` | CSS → general stabilizer, requiring typed halving data (fixed-point-free involution $\pi$ with $\pi(S_X)=S_Z$); $n'=n/2$, $k'=k/2$, $\lceil d/2\rceil \le d' \le d$; existence of $\pi$ is a decidable linear-algebra property of a presented CSS state (a `not yet defined` judgment slot) |
| `X-LOCAL-CLIFFORD` | typed Clifford data (per `provenance.clifford_relabel_of`-style provenance) and a purity condition; the CSS-preserving single-qubit instance is `E-LOCAL-HADAMARD`; deferred with the rest of the extended-state layer (`spec/TAXONOMY.md` §4.4, 2026-10-23) |
| `X-DRESSED-QUOTIENT` (candidate, no taxonomy ID yet) | new constructor: parent Pauli code + higher-form / cup-polynomial background class + trivializing cover → commuting-projector (dressed) code; the twist is an entangling diagonal circuit (CZ-type for quadratic defects, CCZ-type for cubic and higher); dressed Gauss laws give the orthogonality; Clifford level at most one less than the twist degree; for cubic twists the dimension is a count of solutions of quadratic equations in cup products (certifies non-Pauli when not a power of two); linear distance on tori and slabs | Needs Gate 6 admission of the extended-state layer; input type, orthogonality proof, distance cell. Source: Hsin, arXiv 2611.09538v1 (prior art, `PRIOR_ART.md`, 2026-11-09). Satisfies §3.8's criteria for its own record, but at the extended-state layer, not the CSS one |
| Two-sorted state model | invariants I1–I5 re-scoped to the CSS special case; sector distances ($d_X,d_Z$) become Pauli distance $d$ across the layer boundary |

**Recorded at rung 1 (`taxonomy-only`)** — `X-LOCAL-CLIFFORD` has carried a
contract-index row since the 2026-10-25 staging (previously listed here as
*unrecorded*). It is not constructor-shaped (a conjugation that preserves the
code up to equivalence, not a typed-input constructor), so it is not listed
under Gate 7.

**Promotion criterion:** Gate 6 admission of the extended-state layer, plus
re-evidencing of the CSS core under the two-sorted model. Out of scope under the
stopping point; recorded here so the deferred work is findable. Consumer-side
helpers exist for the two moves and for a symplectic kernel (skip, delete,
add, direct sum) with a Pauli-distance ledger and a conformance harness
(`machine/symplectic_calculus.py`, issue #305, the way `CodeState.glue`
preceded `E-GLUE`'s transition); they admit nothing, and the interval rules
they implement are derived in
`an internal note`,
not in `spec/`.

**Disposition (2026-11-10, issue #316 C2).** `X-DRESSED-QUOTIENT` was admitted
to the roadmap as an extended-state-layer (Gate 6) candidate, with placement and
admission criteria per this section; it is not admitted to the CSS core and
remains subject to Gate 6 admission of the extended-state layer.

The two
symplectic moves are also listed under Gate 7 constructors below, since they
are also constructor-shaped moves; the Gate 6 question (state model) precedes
the Gate 7 question (typed inputs).

### Gate 7 candidates — constructors

**Recorded at rung 1 (`taxonomy-only`)** — all fifteen Gate 7 candidates
carry a contract-index row since the 2026-10-25 staging (TODO item 5,
`an internal note`):
`A-PRODUCT`, `A-CONCAT`, `A-DOUBLE`, `A-QUOTIENT`, `L-HGP`, `L-LIFTED`,
`L-NESTED-CSS`, `L-TILE`, `L-TANNER`, `L-BALANCED`, `L-GROUP-ALGEBRA`,
`X-SYMPLECTIC-DOUBLE`, `X-SYMPLECTIC-HALVE`, `X-SUBSYSTEM`, `X-GAUGE-FIX`.
Rungs are recorded here in `ROADMAP.md`, not in `TAXONOMY.md`.
`spec/TAXONOMY.md` §2.13 still states the general
consequence — with no contract-index row an operation "sits below the ladder's
first rung (`taxonomy-only`) rather than on it" — which now applies to no
listed operation; the rule stands for future ones.

**Promotion criterion, common to all:** define the constructor's typed input
signature. `A-*` and `L-*` in particular are **not encodable as commands over an
existing CSS state** and must not be. Promotion above rung 1 is maintainer work.

**Typed input signatures recorded (2026-10-28, issue #193).** The fifteen
candidates below now carry typed input signatures at
`CONSTRUCTOR_SIGNATURES.md`: the typed objects
each consumes, the obligations it incurs, and whether each input is
constructive or axiomatic. This is a signature record only — no constructor is
admitted, no claim status is flipped, no grammar production is added, and the
common promotion criterion above is unchanged.

| ID | Typed input signature (abbreviated) |
| --- | --- |
| `A-PRODUCT` | `(A,B : ChainComplex \| CSSCode; μ : ProductStructure; ρ : RetainedDisplay) -> CSSCode` |
| `A-CONCAT` | `(O : CSSCode; I : CSSCode \| StabilizerCode; E : EncodingMap; L : LogicalReps) -> CSSCode` |
| `A-DOUBLE` | `(C : CSSCode; w : WiringMap; s : SectorDualityChoice?) -> CSSCode` |
| `A-QUOTIENT` | `(V : StabilizerSpace \| Subspace; q : QuotientMap; e : EmbeddingData) -> CSSCode` |
| `L-NESTED-CSS` | `(X,Z : ClassicalCode) -> CSSCode` |
| `L-HGP` | `(C1,C2 : ClassicalCode) -> CSSCode` |
| `L-LIFTED` | `(B : BaseMatrix \| ChainMap; A : Algebra; ℓ : LiftAction) -> CSSCode` |
| `L-BALANCED` | `(F1,F2 : LiftedFactor; G : GroupAction; q : QuotientRelation) -> CSSCode` |
| `L-GROUP-ALGEBRA` | `(a,b : AlgebraElement; R : Representation) -> CSSCode` |
| `L-TANNER` | `(λ : LocalCode; Γ : TypedGraph; ι : EmbeddingData) -> CSSCode` |
| `L-TILE` | `(τ : LocalTileSet; β : BoundaryRules; α : Cellulation) -> CSSCode` |
| `X-SYMPLECTIC-DOUBLE` | `(S : StabilizerCode) -> CSSCode` |
| `X-SYMPLECTIC-HALVE` | `(C : CSSCode; π : Involution) -> StabilizerCode` |
| `X-SUBSYSTEM` | `(G : GaugeData; S : CenterData; L : LogicalData) -> SubsystemCode` |
| `X-GAUGE-FIX` | `(E : ExtendedState; g : GaugeGeneratorChoice) -> ExtendedState \| CSSCode` |

One instance is already live and unproved: `A-PRODUCT`'s retained-presentation
payload creates a well-formedness instance under `OBL-WELL-FORMEDNESS-PRESERVATION`
that Gate 7 may never reach.

**Disposition (2026-11-10, issue #315 C1).** The fifteen Gate 7 constructors
above (and, in particular, `L-HGP`, `L-LIFTED`, `L-BALANCED`,
`L-GROUP-ALGEBRA`, `L-TANNER`, `L-TILE`, `A-CONCAT`, `A-PRODUCT`,
`A-DOUBLE`) were accepted for admission as typed constructors with explicit
distance hypotheses. Acceptance is a disposition, not an admission: each remains
at rung 1 (`taxonomy-only`) until its typed transition, obligation rows, and
dated derivation/citation land; promotion above rung 1 remains maintainer work.
See `DIARY.md` (2026-11-10) and `spec/OBLIGATIONS.md` (v0.2 candidates).

**Landed in part (2026-11-11, issue #330).** `L-HGP`, `L-LIFTED` (finite
abelian groups), `L-GROUP-ALGEBRA` (two-block over a finite abelian group),
and `A-CONCAT` (CSS factors) are `transition-defined` expression constructors
(rung 3): productions at `../spec/TERM_LANGUAGE.md`
§1 and §2, cards at `../spec/OPERATIONAL_SEMANTICS.md`
§2, well-formedness and parameters at §4.34, cells at
`../spec/JUDGMENT_LAYER.md` §2g (no distance
rule).

**Landed in full (2026-11-11, issue #369).** `L-BALANCED`, `L-TANNER`,
`L-TILE`, `A-PRODUCT`, and `A-DOUBLE` are `transition-defined` expression
constructors (rung 3) with typed inputs realized as finite objects: cards
at `OPERATIONAL_SEMANTICS.md` §2, derivations at §4.35, cells at
`JUDGMENT_LAYER.md` §2g (no distance rule). The realizations are narrower
than the signatures in the table above: the CSS tensor product only,
finite abelian groups only, one local code per vertex class, and the
two-sheet cover of the displayed incidences only.

**`L-NESTED-CSS` (2026-11-13, issue #445).** `L-NESTED-CSS` is a
`transition-defined` expression constructor (rung 3) for two classical
codes given by parity-check matrices: card at `OPERATIONAL_SEMANTICS.md`
§2, derivation at §4.36, cells at `JUDGMENT_LAYER.md` §2g (no distance
rule). It is an instance of the `L-TANNER` production (§4.36).

### Candidate specialization recorded from prior art (2026-11-09)

**Not a new ID, not a new state update.** Hsin, arXiv 2611.09538v1 (prior
art, `PRIOR_ART.md`) unifies balanced-product, bivariate-bicycle,
genon and five-qubit codes as **quotient codes**: a parent folded onto itself
by identifying each check with its image under a deck transformation composed
with a symmetry. The flat case is a balanced product; the general lattice form
is a free monomial-Clifford action (qudit permutation + single-qudit
Clifford) with orbit representatives. This is a **specialization of the
existing `A-QUOTIENT` record** (`spec/TAXONOMY.md`
§2.15), not a new primitive: same state update (restrict/identify stabilizer
data under a specified map). It earns a record of its own under
`spec/TAXONOMY.md` §3.8 via a distinct *parameter
theorem* — the transfer theorem, with a Tate cohomology group counting the
logical operators that are new — and a precisely typed quotient mechanism
(free action, consistency condition that a nontrivial Clifford on a fixed point
is inconsistent, representatives up to local Clifford equivalence). CSS-preserving
instance only (permutation actions, or sector-preserving single-qudit
Cliffords); the duality-quotient instance (letters change; five-qubit code) is
the sector-swap case of `E-LOCAL-HADAMARD` (§2.12), and when it leaves CSS it
belongs to the extended-state layer. Placement if ever admitted: specialization
row under `A-QUOTIENT` in `spec/TAXONOMY.md` §2.15, with the transfer theorem
as its conditional price/property cell. The dressed-quotient variant is the
`X-DRESSED-QUOTIENT` candidate above. "Compactification" as such is not a
separate operation — it is the physical reading of the quotient (theory on
$X\times F$ with a symmetry background along $F$); the geometry enters as the
symmetry action and cover data that `A-QUOTIENT`/balanced product already
require. Neither is an MVP transformation.

**Disposition (2026-11-10, issue #316).** The monomial-quotient specialization
was admitted as a specialization record under `A-QUOTIENT` (§2.15), CSS-preserving
instance only, with the transfer theorem as its conditional price/property cell;
the dressed-quotient constructor (`X-DRESSED-QUOTIENT`) was admitted to the
roadmap as an extended-state-layer (Gate 6) candidate, with placement and
admission criteria per this section. Neither is admitted to the CSS core; both
remain subject to their stated prerequisites.

**Specialization row and conditional cell landed (2026-11-18, issue #547).**
The monomial-quotient specialization row is recorded under `A-QUOTIENT` in
`../spec/TAXONOMY.md` §2.15 (with single-code set-level
coequalizers also folded here per issue #518), the transfer theorem is recorded
as a conditional slot in `../spec/JUDGMENT_LAYER.md`
§2i (recording existence only, with no usable automatic bound or $k$ formula),
CSS-preserving applicability constraints are checked consumer-side in
`machine/quotient_specialization.py` and transcribed in `machine/consumer.json`,
and duality-quotient instances route to `E-LOCAL-HADAMARD` (`TAXONOMY.md` §2.12,
$T = Q$) or to the deferred general-stabilizer extended-state layer (§4, refused
for `v0.3.0` under issue #545). `A-QUOTIENT` remains at rung 1 (`taxonomy-only`).

**A gap this exposed — closed 2026-10-25.** Thirteen operations had no
contract-index row, so the ladder could not promote them: there was nothing to
promote *from*. The 2026-10-25 staging (TODO item 5, maintainer) added the
missing twelve rows at rung 1 (`taxonomy-only`), every operation above now has
a row, and promotion above rung 1 remains maintainer work rather than
something an agent should infer.

### Decoupling of translation-invariant CSS codes (candidate, v0.2+)

**Recorded 2026-11-10 from the 2026-11-10 arXiv watch triage** (He, Wang,
Song, Gu, arXiv 2610.40592v2, *Toric codes all the way down: decoupling
translation-invariant topological CSS codes in higher dimensions*). Prior art;
not yet a taxonomy ID and not a contract-index row.

**What the paper does.** For a translation-invariant `p`-ary CSS code (`p`
prime, `p = 2` for qubits), it gives an explicit algorithm that constructs a
decoupling as a circuit of SUM (qudit CNOT) and SWAP gates: a finite-depth
local CSS-preserving Clifford circuit that maps the code to a stack of
higher-form toric codes, possibly after adding ancillas and coarse-graining on
a superlattice. The obstruction is fully characterized: a code decouples
exactly when, after coarse-graining, translations act trivially on every
superselection layer and the gluing between layers vanishes; once translations
act trivially on every layer, further coarse-graining by `p^{m-1}` in every
direction removes any remaining gluing (for `m` nonzero layers). The same
criterion determines when the code encodes the maximal number of logical qudits
on a finite torus.

**Why it is not a new primitive in this scope.** It is a code-to-code
transformation, but (a) it applies only to translation-invariant codes, (b)
its target is a stack of higher-form toric codes (a constructor family, not a
deformation of an arbitrary CSS state), and (c) it is a finite-depth Clifford
circuit over an existing code, i.e. a constructor in the `L-*`/extended-state
sense rather than a kernel primitive over an existing CSS state. Per
[`SCOPE.md`](SCOPE.md) §4, Gate 7 constructors (`L-`, `A-PRODUCT`,
etc.) and the extended-state layer are out of scope for v0.1. The move also
requires translation-invariance data that is not part of the state model
(`spec/STATE_MODEL.md`), so it cannot be stated as a premise-free transition
today.

**Placement if ever admitted.** A v0.2+ candidate under the `L-*` constructor
family (or a new decoupling constructor if the input signature is distinct from the
existing fifteen), with a typed input signature of the form
`(C : TranslationInvariantCSSCode; L : Superlattice) -> StackOfHigherFormToricCodes`
and the translation-triviality + gluing-vanishing criterion as its
admission hypothesis. The circuit construction (SUM/SWAP) is the *evidence*
for the move, not a calculus rule. No distance claim is made by the paper
beyond the toric-stack parameters; any distance statement remains a hypothesis
to be supplied.

**What it does not change.** No in-scope cell, no obligation, no release axis.
It is recorded here so the transformation is not rediscovered, and so the
translation-invariance prerequisite is visible if a future scope decision
admits constructor families.

**Candidate formulation (2026-11-13, issue #451).**
`DECOUPLING_CONSTRUCTOR.md` defines the
translation-invariant input as a finite typed object on a torus, and
recommends stating the move as a certificate-checked relation (a supplied
SUM and SWAP circuit, checked on the display) in place of a constructor
that trusts the criterion. It derives exact $n$ and $k$ cells and a distance
window, with a harness at
`machine/experiments/translation_invariant_decoupling.py`. That note admits
nothing, and the placement above is unchanged until a decision is recorded.

### Nullary and interface constructors (candidates, unassigned)

**Added 2026-11-04; dispositioned 2026-11-18 (issue #518).** Recorded from the
categorical-construction sweep of the state model. These are **not** assigned
taxonomy IDs, carry no contract-index row, and sit below the ladder's first
rung. They are candidates only; promotion requires a dated maintainer decision
and the stated proof/evidence obligations (tracked at issue #549). The former
*Kan extension (meta-level)* row had no state update (1) and no promotion
criterion (6), and was deleted on 2026-11-18 under §3's promotion rule (issue
#518; `DIARY.md`). Set-level equalizer (subcode/intersection) and coequalizer
(amalgamation/identification) candidates fold into the pullback/fiber-product
and pushout/amalgamated-sum rows below (and into `A-QUOTIENT`,
`../spec/TAXONOMY.md` §2.15, for the single-code
self-zipping case, issue #547) rather than forming separate rows.

| Entry | Form | Conditions to preserve | Promotion criterion |
| --- | --- | --- | --- |
| empty code (nullary constructor) | state with $Q=\varnothing$, $X=Z=\{0\}$, empty display, empty `used`; $k=0$, $d=+\infty$ | I1–I5 hold vacuously; canonical mint is vacuous; equality and `used` are trivial | A dated maintainer decision to add a constant state expression, plus grammar and fixture updates |
| free code (qubit-set base constructor; 0-ary in input `CSSCode`s only) | state with empty $X,Z$ on a given $Q$; for $Q\neq\varnothing$, $k=n$, $d=1$ (for $Q=\varnothing$, coincides with empty code, $d=+\infty$) | CSS orthogonality and displayed independence hold vacuously; canonical mint is vacuous | A dated maintainer decision to add a constant/base-set state expression, plus grammar and fixture updates |
| pullback / fiber product constructor (includes set-level equalizer / common subcode) | constructor taking two codes plus maps to a common interface; output qubits are a fiber product | definition of code maps and output rows, interface compatibility, CSS orthogonality | Typed signature (including $I$), defined code maps and output rows, well-formedness proof, distance/judgment cell, and maintainer admission |
| pushout / amalgamated sum (generalized gluing; includes two-code coequalizer / identification) | constructor generalizing direct sum along a shared subcode (single-code self-zipping is the coequalizer specialization of `A-QUOTIENT`, `spec/TAXONOMY.md` §2.15) | definition of subcode embeddings and output rows, seam compatibility, CSS orthogonality | Admission beyond `E-GLUE`'s planar seam case, with defined code maps/output rows, hypotheses, and proof obligations stated |

**Disposition (2026-11-18, issue #549; read after issue #518).** Of the four
remaining candidates above (the former *Kan extension* row having been deleted
under §3 on 2026-11-18, issue #518, and set-level equalizers / two-code
coequalizers folded into `pullback` / `pushout`), `empty`, `free`, `pullback`,
and `pushout` are accepted into `v0.3.0` **candidate scope** with typed
signatures, well-formedness conditions, and candidate property/judgment cells
in `NULLARY_AND_INTERFACE_CONSTRUCTORS.md`,
while the refusal of `kan` as a state constructor is reconfirmed. Candidate
admission authorizes follow-up `v0.3.0` PRs to draft promotion artifacts
(definitions of code maps and output rows for `pullback`/`pushout`, grammar
productions, §2 cards, §4 well-formedness derivations, §2g/§4 cells, and
fixtures), whereas a refused candidate is closed out of `v0.3.0` work unless a
new state-level proposal is submitted. None is promoted to `transition-defined`
or admitted to `spec/` by this disposition, and issue #549 remains open until
those follow-up PRs land. See
`an internal note`.

**Promotion criterion, common to all.** A dated maintainer decision in
`../DIARY.md` admitting the result, plus the stated hypotheses
and proof/evidence obligations being met. None is owed by the stopping point.

**Landed as `transition-defined` (2026-11-19, issue #549).** `L-EMPTY`
(`empty`), `L-FREE` (`free(Q)`), `A-PULLBACK` (`pullback(e₁, e₂, e_I; φ₁, φ₂)`),
and `A-PUSHOUT` (`pushout(e₁, e₂, e_S; ψ₁, ψ₂)`) are admitted at rung 3
(`transition-defined`) for the `v0.4.0` target: productions in
`../spec/TERM_LANGUAGE.md` §1–§2, cards in
`../spec/OPERATIONAL_SEMANTICS.md` §2,
derivations in §4.43, cells in
`../spec/JUDGMENT_LAYER.md` §2g and §2d.5 (no
automatic distance rule beyond §2g), contract-index rows in
`../spec/CLAIMS.md`, consumer support in
`machine/constructors.py`, and Lean productions/well-formedness theorems in
`lean/CodeCalculus/` (`ConstructorInstances.lean`). The Kan-extension candidate
remains refused. See
`an internal note`.

### Obligations formerly deferred here

All three obligations this file used to list as out of scope or deferred have
since been discharged by dated hand derivations (the third, `OBL-CERTIFICATE-PATH-KEYING`,
ratified 2026-10-27; its three Gate 5 questions remain open). See the
"Completed and recorded (v0.2)" appendix below.

The obligations now open under the stopping point are the mechanization slices
of item 8 in `../TODO.md`; `OBL-GATE6-CSS-EXTENSIONS`, above, is
discharged (§4.32, 2026-10-28) and its cells remain conditional.

### Not operations, and still tracked

| Entry | State | Promotion criterion |
| --- | --- | --- |
| **The evaluator** | **full fixture conformance landed (M1, 2026-10-21).** `machine/priced_calculus.py` executes the admitted transition subset; `machine/fixture_conformance.py` reports 0 mismatches over the pinned state fixtures. The judgment-level conformance harness (issue #27) also runs in CI | A scope change that adds new admitted transitions: each must be wired through the evaluator with fixtures |
| **The formalization** | **WP0–WP1 landed; first derivation-layer soundness slice landed (2026-10-25, issue #118); deeper slices open.** The Lean development under `lean/` carries the presented state, the pinned identifier enumeration with its round trip (`rankOf_identifierAt`), presentation equality ≡, the term language, I1–I5, the `EvalExpr`/`Eval` skeleton (`base` and `directSum` at the expression level; `skip`, `seq`, `delete`, `addStab`, `graft`, and the five Gate 6 transitions `rebase`, `hadamard`, `peel`, `puncture`, `extend`), the interval/ledger judgment skeleton, generated fixture-state definitions with their well-formedness replay (issue #83, closed 2026-10-25; the remaining coverage gaps are reported by `machine/lean_fixture_coverage.py`), and — `lean/CodeCalculus/Soundness.lean` — the annotated-judgment models predicate of §4.11 with the soundness metatheorem `judgment_soundness` over the L3 inventory (skip's identity on every field, the `n` cells of deletion, addition, and the graft, the `k` cells with the dimension bound `RanksFit` derived from I1 (`ranksFit_of_wf`, issue #216), and the well-formedness cells of skip, deletion, addition, and the graft (issue #217); the distance cells are taken as hypotheses at the row) | Hand derivations in `spec/OPERATIONAL_SEMANTICS.md` §4 re-derived as Lean theorems, plus the soundness metatheorem **in full** — judgment transport is mechanized (issue #158, merged 2026-10-28), except that the derivation-level `W13` half has no instance, since the sentence language has no claim that refers to a generator; the distance rows take the measure's monotonicity; the `W13` half of transport and any Gate 6 soundness statement are not mechanized — that is item 8/M3 in `../TODO.md` |
| **Future $\Pi$ fields** | not MVP data | A use that requires them, and a decision to admit them |
| **The layout parameter** | **admitted as ledger data 2026-10-22** (issue #62). The interaction radius `r` is a derived, carried property; the locality class is a consumer-side verdict, not a property. The layout itself is **not** a $\Pi$ field, so the state model and the equality relation are unchanged | A second metric judgment that needs the layout to be *state* data -- for example a claim about quotients of the layout, or about a merge that must preserve geometry as well as the code |
| **`not yet defined` claims** | circuits, DEM, realization, ZX duality, and **logical-gate addressability, logical action, and non-$\pi/4$ anticommuting check addition** (named by arXiv 2610.17612 and specified in §2 "Gate-realization verification" below; codespace preservation $\mathsf{preserves}_U$ for commuting and $\pi/4$ CSS additions and the equal-syndrome weight floor $\omega \ge \lceil d/2 \rceil$ are admitted in `../spec/JUDGMENT_LAYER.md` §2 and §2h, issue #543) | An assertion-language extension reading the logical-witness frame |

### Future extensions from the taxonomy remainder audit (2026-10-24)

Recorded from an internal note §1. These are
**not** admitted and carry no rung; they are future destinations for the calculus
program, to be promoted by dated maintainer decisions only. Ledger numbers in
parentheses and "Lemma 14.4" are section/theorem/lemma numbers in the companion
paper *code-deformation* (its proof ledger); see
`DERIVED_RELATIONS.md` for the citation style.
"Done when" criteria are carried in the final column; they are no longer
mirrored in `../TODO.md`, which keeps only a one-line pointer
under *Deliberately not on this list*. Baselines already recorded in `spec/` are
cited where an entry's remainder is smaller than the original audit framing.

| Entry | Form | Conditions to preserve | Done when |
| --- | --- | --- | --- |
| Mapping-cone / chain-map construction | Future constructor roadmap entry; distance formula as a conditional price/property provider | Exactness is a source theorem; separately audit the claimed identification with a strict pushout and the induced metric/norm semantics; a rule must take the chain map and compatible weights as explicit inputs | A dated maintainer decision admits the constructor, with the strict-pushout identification audited and the chain-map/weights inputs recorded; no exactness claim beyond the source theorem |
| Multi-band patch count (12.3) | Future dense-packing family rule or construction metadata provider for $k$ | Complete the proof of Lemma 14.4; counts fused patches / logical dimension, not a distance certificate; reconstruct the physical check structure from the constructor, not the mask count | Lemma 14.4 proved; counts recorded as construction metadata, not a distance certificate; physical check structure reconstructed from the constructor |
| One-shot level-map transport (30.1–30.7) | Candidate family/amplification rule for a future calculus with family-level moves | Imported framework lemmas need independent review; transport direction is an upper ceiling, not a lower guarantee; keep empirical probes separate from the conditional theorem | **Conditional rule admitted in `v0.3.0` candidate scope (2026-11-18, issue #541):** `SCOPE.md` §3–§4 extended, conditional family-level rule recorded in `spec/JUDGMENT_LAYER.md` §2j (`CLAIMS.md`, `VERSIONING.md` §5.1, `machine/consumer.json`); Definitions 104/106/111/113/116 and Eq. (249) transcribed with finite `bar Gamma` probe in `machine/experiments/one_shot_level_map_transport.py`; amplified distance stays `unavailable` and imported lemmas stay `conditional` |
| Positive composition criteria (typed seam tests, interface classification, union-layout immunity, boundary-signature certificates) | Grow `E-GLUE` into a family of typed, conditional judgments and certificate providers (extends issue #57, closed) | Keep sector, layout, defect, and orientation hypotheses attached; boundary tables remain trusted inputs until checked; odd-cycle table omission and incomplete certificate producer stay visible; circuit preservation is empirical where the source says so | Baseline already admitted in `spec/JUDGMENT_LAYER.md` §2e (seam certificate conditional on the planar scope with the move-word hypothesis). Remaining delta: interface classification, union-layout immunity, and boundary-signature certificates admitted as conditional rows with hypotheses attached; odd-cycle omission and incomplete producer remain visible; circuit preservation stays empirical where the source says so |
| Composition insufficiency / arbitrary-gap family | Completeness boundary: with only factor summaries and coarse connectivity the consumer returns `inconclusive` | Graph-homology / selected-sector scope; does not prove every composition loses distance or that no richer certificate can work | Baseline already recorded in `spec/JUDGMENT_LAYER.md` §2e (no-go obstruction row: factor data plus connectivity must return `inconclusive`). Remaining delta: the graph-homology / selected-sector scope qualifier recorded on the row; the no-go not overstated as "every composition loses distance" or "no richer certificate can work" |
| CNOT-disguised direct sums (12.2) + depth-one equality (13.8) | Future presentation-transform judgments and regression examples | Hamming weight is not invariant under general Clifford conjugation; preserve depth and sector hypotheses; unproved universal equality tail stays open; do not model a generic CNOT layer as zero-price | Spec notes and regression fixtures exist; Hamming-weight non-invariance under general Clifford conjugation preserved; unproved universal equality tail stays open; no generic CNOT layer modelled as zero-price |
| Hole punch (15.7, 28.6, 29.10–29.15) | Future operation with proved partial facts and an explicit `unavailable` full-price result (issue #59, open; D2 lower bound established in-repository under the strict-interior model, tracked at #94; reduction `d_Z = min(h, d_hole)` proved in general, issue #157; boundary-touching case resolved as no undercut) | Full price conjectural on the companion-paper side for interior holes; the lower bound (strict-interior) and the `d_Z = min(h, d_hole)` reduction (general) are in-repository (`an internal note`, `an internal note`, `an internal note`, issues #94 and #157); boundary-touching holes give `d_Z = h`; still no cell or fixture; never insert a withdrawn/proposed closed form as a sound price | Baseline already recorded in `spec/TAXONOMY.md` (`E-PUNCTURE` row: pricing blocked on D2, tracked at #59, no cell and no fixture admitted). The property records and the explicit `unavailable` full price are in `spec/JUDGMENT_LAYER.md` §2f (issue #548). Remaining delta: a conditional hole-price cell, which waits on maintainer acceptance of the D2 lower bound; never a withdrawn/proposed closed form inserted as a sound price |
| Multi-punch deletion family (15.11), defect punch (15.6), safe single deletion (15.14) | Worked example + conformance-fixture family for priced deletion and sequence evaluation (extends issue #58, closed; overlaps open #86 for the second fixture family) | Keep square-lattice and defect assumptions; examples are evidence for the evaluator; general formula remains the paper's theorem; do not promote into a universal deletion rule | Fixtures pass the conformance evaluator; no universal deletion rule claimed |
| Graphlike exposure (15.15) | Complete a graphlike exposure-price provider (issue #54, closed 2026-10-24 as a source-data gap; see `an internal note`) | Column-weight-at-most-two scope; X-exposure of deleted Z-checks; exact deletion set; the column-weight-three hardness is derived in-repository (`DERIVED_RELATIONS.md` §3a, issue #326) and stays out of the provider's proof | Procedure matches the worked instances; non-graphlike inputs refused with a recorded reason; citation status stated |
| Tower pricing, arbitrary $k_{\mathrm{in}}$ (27.5 / 27.8) | Extend the admitted concatenation-tower price provider from $k_{\mathrm{in}}=1$ to arbitrary $k_{\mathrm{in}}$ (issue #56, closed 2026-10-25; provider landed under issue #327) | Refined lift-subtorus class dictionary (unrefined is false); cost table grows as $2^{2k_{\mathrm{in}}}$; stays a price provider until a separate constructor is admitted; executable provider derived in-repository (`DERIVED_RELATIONS.md` §2a, 2026-11-11) for deletions of lifted outer checks, inner-check deletions not covered | Provider documented for general $k_{\mathrm{in}}$; sweep for at least one $k_{\mathrm{in}}=2$ instance passes (both in tree 2026-11-11: `machine/experiments/tower_sweep.py` sweeps $k_{\mathrm{in}}\in\{1,2,3\}$ at $n_{\mathrm{in}}=4$; promotion remains a maintainer decision) |

**Implementation (issue #539, 2026-11-18).** The multi-band patch-count
construction metadata is now implemented on the machine side:
`machine/experiments/multi_band_patch_count.py` records the count as a
metadata field and provides a toy reconstruction of a check structure
(qubits, X-rows, Z-rows with supports) whose independent check count is
chosen so the logical dimension agrees with the formula;
`machine/test_multi_band_patch_count.py` checks that agreement. This is not
a reconstruction from the dense-packing constructor's geometry (unavailable
in this repository); Lemma 14.4 stays an explicit-instance insufficiency
witness (not a general theorem); no spec, taxonomy, or constructor is
admitted. The roadmap row above retains its done-when as the record of what
is still owed for promotion.

**Promotion criterion, common to all:** a dated maintainer decision in
`../DIARY.md` admitting the result (or its provider/operation)
to the calculus, plus the stated hypotheses and proof/evidence obligations
being met. None is owed by the stopping point.

**Mapping-cone entry (2026-11-13, issue #449).**
`MAPPING_CONE_CONSTRUCTOR.md` states the cone
of a chain map between two-term complexes as a typed input with candidate
cells, and carries out the audit the entry asks for against the statement
this repository records: the recorded formula is one term of one sector's
distance, and the strict-pushout identification holds for the complexes and
fails for the quotient norm. The paper itself was not available, and the
note admits nothing.

**Implementation (issue #540, 2026-11-18).** The mapping-cone / chain-map
constructor is now implemented on the machine side as conditional judgment
records that make the chain map and compatible weights explicit inputs, record
the strict-pushout identification audit, state the induced metric/norm
semantics (Hamming weight in the cone basis, not the quotient norm), and make
no exactness claim beyond the source theorem:
`machine/experiments/mapping_cone.py` (re-exported by
`machine/mapping_cone.py`) gains `chain_map_input`, `compatible_weights`,
`pushout_audit`, `induced_metric`, `no_exactness_beyond_source`,
`conditional_price`, and `mapping_cone_constructor`, with aliases;
`machine/entrypoints.py` re-exports them. No `spec/`, taxonomy, or constructor
is admitted.

**Admission decision (2026-11-14, issues #446–#453).** The eight candidate
entries of this section — mapping cone (#449), multi-band patch count (#448),
one-shot level-map transport (#450), positive composition criteria (#446),
CNOT-disguised direct sums + depth-one equality (#447), decoupling (#451),
gate-realization rows (#452), and future Π fields (#453) — are admitted into
the `stdCSS-3` / `v0.2.0` candidate scope by dated maintainer decision
(`an internal note`).
Their conditions, hypotheses, and proof obligations are preserved; none of
their exactness/lower-bound/universal claims is upgraded by the decision.
Implementation (taxonomy IDs, grammar productions, spec cards, machine and
Lean counterparts) follows in separate PRs. Issues stay open until those
land.

### Organizational uses of category theory (dispositioned 2026-11-18, issue #518)

**Added 2026-10-25; closed out 2026-11-18 (`DIARY.md`, issue #518).** The
former *Double-category / operadic organization of the obligation ledger* entry
carried the done-when condition *"A concrete coherence-law-shaped gap in the
ledger is identified that per-cell proofs cannot express; otherwise the entry
is deleted."* No such gap arose, `TODO.md` item 11 (structured constructor
signatures, `CONSTRUCTOR_SIGNATURES.md`)
is complete, and the non-goal stands: no load-bearing category theory
(`../spec/GATES.md` §11). By the 2026-11-18 maintainer
decision on issue #518:

- **Accepted as a proof-architecture slice (Candidate A):** the classical
  `puncture ⊣ shorten` Galois connections, the dual-code identity
  $P_i(C)^\perp = S_i(C^\perp)$, and the sector-swap involution and transition
  conjugation laws $H(m_\sigma(C)) = m_{\bar\sigma}(H(C))$ are mechanized in
  `lean/CodeCalculus/DualityAdjunction.lean` without a category-theory library
  (`DUALITY_AND_METATHEORY.md` §2,
  `DERIVED_RELATIONS.md` §2b).
- **Folded into existing candidate rows (Candidates B and C nullary):**
  equalizers fold into the pullback/fiber-product row above (issue #549);
  coequalizers fold into `A-QUOTIENT` (`../spec/TAXONOMY.md`
  §2.15, issue #547) and the pushout/amalgamated-sum row above (issue #549);
  initial/terminal objects stay the empty/free nullary constructors above
  (issue #549).
- **Kept as non-normative design-note readings only (Candidates F and G):**
  the descent reading of `E-GLUE` (`DUALITY_AND_METATHEORY.md`
  §5.4, cashed out in linear algebra at
  `../spec/OPERATIONAL_SEMANTICS.md` §4.33
  as $L_\sigma(C)\cong K_\sigma/W_\sigma$) and the probabilistic monad boundary
  for randomized moves (`DUALITY_AND_METATHEORY.md`
  §4.2, outside the `stdCSS` line).
- **Deleted under §3 (failing (1) state update and (6) promotion criterion):**
  the double-category/operadic ledger row, the meta-level Kan-extension row,
  filtered colimits / directed unions (Candidate C), `(epi, mono)`
  factorization systems (Candidate D), operadic substitution-associativity
  laws (Candidate E; operadic signature notation remains the reading convention
  of `CONSTRUCTOR_SIGNATURES.md`
  §1), and higher-categorical 2-cells/3-cells/homotopy equality (Candidate H).

### Gate-realization verification — decidable, with two named gaps

**Added 2026-10-15, from arXiv 2610.17612.** Recorded here because the two
prerequisites are exactly the shape of thing this file exists to make findable,
and because one of them is *not* a gap in FD1.

**Why it is on the roadmap at all.** Nelson–Danageozian–Cao–Economou–Barnes
derive a codespace-preservation condition for commuting multiqubit Pauli
rotations that is **decidable**: GF(2) linear algebra over the displayed rows
for the syndromes, plus sign arithmetic for the angle condition
([`PRIOR_ART.md`](PRIOR_ART.md) §2). That is the profile of a Gate 5
artifact, and it is the first candidate of its kind that has appeared against
this state model. Two things stand between it and being hosted. **Neither is
FD1, and neither is a new prerequisite** — see the lemma below, and both gaps
attach to fields already flagged elsewhere in the record.

| Gap | What it blocks | Promotion criterion |
| --- | --- | --- |
| **Logical witness / Pauli frame.** The non-Clifford branch evaluates $\sum_j\epsilon_j\theta_j\,\ell_j^{(\lambda)}\in\pi\mathbb{Z}$ over eigenvalues of the zero-syndrome logicals $L_j$, which needs a chosen frame. Today `not yet defined` (`spec/JUDGMENT_LAYER.md` §2). | Every $\theta<\pi/4$ case, and the logical action of any accepted gate | A decision to admit the logical-witness field, which is **already** the §2.10 Gate 6 prerequisite (`spec/TAXONOMY.md`); this entry adds no new prerequisite, only a second claimant |
| **Per-row sign, for non-CSS only.** The $\pi/4$ condition is sign-sensitive (Cor 3). For a CSS display the sign of any product of displayed rows is **determined** and recoverable — see the lemma below — so FD1 costs nothing there. A mixed Pauli row is different: one bit per row is independent data, and the source carries "signed stabilizer generators" in its output | Sign conditions on non-CSS codes; the paper's non-CSS demonstrations are exactly this case | A decision to extend the state model with a sign field, which is the `X-SYMPLECTIC-DOUBLE`/`X-SYMPLECTIC-HALVE` question at `spec/TAXONOMY.md` §4.3, not a new one |

**FD1 is safe here, and it is worth saying why rather than assuming.** For a CSS
display, products of displayed rows carry a determined phase: X-rows multiply to
pure-X with coefficient $+1$, Z-rows to pure-Z with coefficient $+1$, and
mixing the two parts on $m$ shared qubits contributes $(-i)^m$ because
$X_iZ_i=-iY_i$. So `(sector, support)` determines the sign of every product in
the display, and `spec/REPRESENTATION.md` §4's
phase-insensitivity discards nothing that a CSS transformation or a CSS
gate-realization protocol needs. Checked against the source's own worked
example: its Eq. (2) computes $S_A S_B$ for $S_A=X^{\otimes4}$,
$S_B=Z^{\otimes4}$ and gets $+Y^{\otimes4}$, which is $(-i)^4=+1$ on an
overlap of $m=4$ — the lemma reproduces it. The phase-insensitivity bites on
**mixed** rows, where the bit is genuinely independent. This is a boundary
statement, not a new obligation.

**Two judgment rows (issue #452, implemented in `spec/` under issue #543):**

| Row | Source | Status |
| --- | --- | --- |
| **Gate survival and addressability through `C-ADD-CHECK`.** Whether a constructed gate survives a check addition and stays addressable — its §IV.4 imposes one check per encoding level while carrying gates along, §IV.4.3 *promoting lower-level gates*, §IV.4.5 *additional addressability* | its §IV.4 and §§IV.4.3, IV.4.5 | **Gate survival ($\mathsf{preserves}_U$) admitted on CSS displays** (`spec/JUDGMENT_LAYER.md` §2, §2h; `spec/CLAIMS.md`; `spec/OPERATIONAL_SEMANTICS.md` §4.37, issue #543): carries across `C-ADD-CHECK` at every angle when all generators commute with the added row $s$, and at $\theta_j = \pi/4$ iff $V_s \in \mathcal{S}(C')$. Addressability, logical action, and the non-$\pi/4$ anticommuting `C-ADD-CHECK` branch remain `not yet defined` pending a logical-frame reading of the logical-witness field |
| **Bound transport by weakening rather than substitution.** Its Cor 2 gives $w_{\max}\ge\lceil d/2\rceil$; the contrapositive plus "`C-DELETE-CHECK` only lowers $d$" means a child inherits a *weaker* bound, not the parent's value | Cor 2 | **Admitted** (`spec/JUDGMENT_LAYER.md` §2, §2h, §7.2 schema 6; `spec/CLAIMS.md`; `spec/OPERATIONAL_SEMANTICS.md` §4.37, issue #543): equal-syndrome generator weight floor $\omega(C) \ge \lceil d(C)/2 \rceil$ in the property inventory, carried by weakening as $\lceil L_d/2 \rceil$ from the full-distance lower endpoint $L_d$ at each state and never substituted from the parent |

Neither mints an operation identifier: a logical gate leaves
`C = (Q, X, Z, pres, used)` unchanged, so `spec/TAXONOMY.md` §3.8's bar for a
distinct state update is never reached.

Both rows are derived for a CSS display in
`../spec/OPERATIONAL_SEMANTICS.md` §4.37
and [`GATE_REALIZATION_ROWS.md`](GATE_REALIZATION_ROWS.md) (issues #452 and
#543), with consumer support on `DistanceLedger.equal_syndrome_weight_floor`
(`machine/intervals.py`) and the falsification harness at
`machine/experiments/gate_realization_rows.py`.

## §3 The promotion rule

**An entry that cannot state a promotion criterion is deleted, not parked.**

That is the whole anti-junk mechanism, and it is the same discipline the repo
already applies to `not_derivable` — one claim, in a stated scope, naming what
would change it. A roadmap without it becomes a graveyard within two versions.

Promoting an entry from rung $k$ to $k{+}1$ requires the rung's own definition to
be met, and **the dated decision is recorded in `DIARY.md`** —
not amended into this file.

## §4 The pull rule

**A release walks this file and promotes what is now satisfied.**

`spec/VERSIONING.md` records releases; this records what is waiting
to be considered. At each release boundary, every entry at a rung below the one
it now satisfies is re-examined, and either promoted by a dated decision or left
with its criterion unmet. Entries are not promoted implicitly by the passage of
time.

## §5 What this file does not do

It does not admit anything. Admission is the schema rule in
`spec/CLAIMS.md`, and it is a Gate 6/7 decision for anything
outside the kernel; the `E-GRAFT` exception is recorded above.

It does not claim the kernel or `E-GRAFT` is sound. The kernel's soundness is
`OBL-JUDGMENT-SOUNDNESS`, which is `proved` (§4.11, 2026-10-20); `E-GRAFT`'s
transition obligation is `proved` (§4.12, 2026-10-20) and its interval and
priced-input obligations are `proved` (§4.13, §4.14) — yet `E-GRAFT`'s ladder position is still `transition-defined`, because no dated
decision has promoted it, and promotion is not implicit (§4). The five kernel
operations reached rung 6 (`contract-proved`) on 2026-11-18 by dated decision
(issue #535; §1); rung 7 (`mechanized`) remains open and Gates 2–7 remain
unchecked.

## Completed and recorded (v0.2)

Moved out of the active queue on 2026-11-16; full rationale lives in the
cited normative artifacts and diary entries.

- **Kernel rung 5 (`contract-stated`) and rung 6 (`contract-proved`)** —
  `C-SKIP`, `C-DIRECT-SUM`, `C-DELETE-CHECK`, `C-ADD-CHECK`, `C-SEQUENCE`
  reached rung 5 on 2026-10-27 (Gate 0; rung-4 well-formedness derivations at
  `spec/OPERATIONAL_SEMANTICS.md` §4.7) and were promoted to rung 6
  (`contract-proved`) on 2026-11-18 (issue #535; §4.39 logical-sector quotients,
  §4.40 metatheorem re-discharge, updated `spec/CLAIMS.md` and `spec/OBLIGATIONS.md`).
  Rung 7 (`mechanized`) remains open.
- **Discharged obligations** — `OBL-DERIVED-TERM-FACTORIZATION` (§4.23),
  `OBL-CERTIFICATE-PATH-KEYING` (§4.24, ratified 2026-10-27),
  `OBL-FIXED-NAMESPACE-REACHABILITY` (§4.17, scoped).
- **`D-9` citation rows** — decided 2026-11-14 (issue #442): not owed;
  citations stay inline; `PRIOR_ART.md` §12 is a review aid.
- **Milestones** — evaluator full fixture conformance (M1, 2026-10-21);
  formalization WP0–WP1 + first soundness slice (issue #118, 2026-10-25);
  judgment transport mechanized (issue #158, 2026-10-28). Issue #424
  (item 8 / M3) closed 2026-11-16 on the four rank axioms accepted as
  `proposed (classical)` assumptions (see `AXIOMS.md`); the remaining
  axiom discharge (extend `MaskRank.lean`) is tracked there, not as an
  open issue.
