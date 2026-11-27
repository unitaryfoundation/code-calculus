# Gates and Non-Goals

**Status:** normative. **One authority per topic.**

Gates 0–7 are ratified (Gate 7 for `stdCSS-3`, 2026-11-26). A gate-status
audit records evidence and open items and does not ratify any gate.

**Consequence, stated plainly:** no artifact may describe an unchecked gate as
met, or any claim as sound, on the strength of a gate being *listed* here.
Listing is not passing, and Gate 0's passage claims **record completeness
only — no soundness**: the proof gates are 1–7, and every claim still stands on
its derivation in `spec/OPERATIONAL_SEMANTICS.md` §4 or on its obligation row in
`spec/OBLIGATIONS.md`.

---

## 10. Proof gates

### Gate 0: taxonomy-to-syntax boundary

For every operation admitted into the formal calculus, record its stable taxonomy
identifier and the semantic contract required by
[`CLAIMS.md`](CLAIMS.md): syntax category, input and output
types, applicability conditions, exact state/context update, structural effects,
logical and distance effects, evidence status, complexity, inverse, provenance,
well-formedness obligation, property judgments, and primitive/derived status. No
operation enters the core grammar merely because it has a familiar name in the
literature or on a leaderboard.

**Ratified.** Scope: every operation with a grammar production — the five
kernel operations, `E-GRAFT`, `P-REBASE`, `E-PEEL`, `E-PUNCTURE`, `E-EXTEND`,
`E-LOCAL-HADAMARD` — plus `E-GLUE`, whose evaluator transition has no unary
production. The record required above is complete for that set. What this
ratification does **not** claim: any soundness result. `E-GRAFT`'s ladder
position remains `transition-defined` (no dated promotion decision), the cells'
sound admission remained open at ratification, `contract-proved` and
mechanization remain owed for the kernel, and Gates 1–7 were unchecked at
ratification (Gate 1 later ratified).

**Supersession note.** The ratification record above is not edited by the later
discharge of `OBL-GATE6-CSS-EXTENSIONS` (discharged by the dated hand
derivation at `OPERATIONAL_SEMANTICS.md` §4.32 and recorded in
`OBLIGATIONS.md`) or by the promotion of the five kernel operations
(`C-SKIP`, `C-DIRECT-SUM`, `C-DELETE-CHECK`, `C-ADD-CHECK`, `C-SEQUENCE`) to
rung 6 (`contract-proved`) on 2026-11-18 ( [`CLAIMS.md`](CLAIMS.md),
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4.39–§4.40). Those
updates supersede only the "remained open" and "`contract-proved` ... remain
owed for the kernel" readings at ratification, not the ratification itself.
Mechanization (rung 7) remains owed for the kernel, and Gates 2–7 remain
unchecked (neither discharge nor rung-6 promotion ratifies a proof gate).

### Gate 1: formal syntax

Produce the grammar of states, contexts, elementary moves, and sequential terms.

**Ratified.** Scope: the MVP grammar of
[`TERM_LANGUAGE.md`](TERM_LANGUAGE.md) — states ($e ::= S \mid e_1\oplus e_2$),
elementary moves ($m$, §2), sequential terms ($m_1;m_2$, $m\triangleright e$),
and contexts (the presentation carried by $S$, §8 of `TERM_LANGUAGE.md`).
Contexts are not a separate syntactic category: a state is always presented, and
its presentation is the context; evaluation contexts (holes) are absent because
the partial big-step relation evaluates closed terms directly. What this
ratification does **not** claim: any soundness result; admission of the
extended-state moves (`X-*`, `E-GLUE`'s merge/split layer) or contract-level
proofs, which remain later-layer work; and Gates 2–7 remain unchecked. The
artifact does not admit any new operation or change any claim status.

**Supersession note.** The `glue(e_1, e_2; \vec u)` production added to
[`TERM_LANGUAGE.md`](TERM_LANGUAGE.md) §1 (`E-GLUE`, dated maintainer decision
2026-11-18) does not alter this ratification: it is an extension
constructor admitted under Gate 6 as a conditional cell, not part of the MVP
grammar ratified here. Gate 1's ratified scope — states
$S \mid e_1 \oplus e_2$, elementary moves, sequential terms, and
presentation-as-context — is unchanged; the glue production is recorded as an
axis-2 (operation set / term language) addition on the `stdCSS-3` candidate,
staged outside this ratification.

### Gate 2: deletion derivation

Give a complete formal rule for single-stabilizer deletion and prove output
validity, the exact logical-dimension consequence, and the quotient-level
logical-sector results. Mark deletion-distance lower bounds and equalities
explicitly unavailable; no deletion-distance formula is an MVP gate. The
non-increase upper bound is an included claim with its hand derivation recorded
at `spec/OPERATIONAL_SEMANTICS.md` §4.

**Ratified (2026-11-19).** Scope: the single-stabilizer deletion rule
`C-DELETE-CHECK` (§4.1), output well-formedness, the exact logical-dimension
consequence (§4.7), the quotient-level logical-sector characterization
(§4.39), and the deletion-distance non-increase upper bound (§4.5).
Deletion-distance lower bounds and equalities remain explicitly `unavailable`;
no deletion-distance formula is an MVP gate. What this ratification does
**not** claim: any soundness result for the calculus as a whole; mechanization
(rung 7) remains owed; Gate 7 is unchecked.

### Gate 3: direct sum and sequencing

Prove that direct sum and sequential composition produce valid terms and derive
their structural judgments. Prove the sequencing obligations of Section 4: skip
identity, associativity, conditional permutation of independent moves, and
judgment transport for the partial big-step relation.

**Ratified (2026-11-19).** Scope: `C-DIRECT-SUM` and `C-SEQUENCE` produce valid
terms and derive their structural judgments (§4.4, §4.8); skip identity (§4.6),
associativity (§4.8), conditional permutation of independent moves restricted to
opposite-sector kernel single-check pairs (§4.10), and judgment transport for
the partial big-step relation (§4.11). What this ratification does **not**
claim: unrestricted permutation of independent moves (restricted by
`OBL-CROSS-SECTOR-PERMUTATION`); mechanization (rung 7) remains owed; Gate 7
is unchecked.

### Gate 4: stabilizer-addition derivation

Add the dual unary rule for an independent commuting CSS stabilizer and prove
its exact logical-dimension and distance-monotonicity judgments. Do not include
subsystem-code gauging in this gate.

**Ratified (2026-11-19).** Scope: the dual unary rule `C-ADD-CHECK` for an
independent commuting CSS stabilizer with its exact logical-dimension and
distance-monotonicity judgments (§4.2, §4.3, §4.7). Subsystem-code gauging is
excluded from this gate. What this ratification does **not** claim: any
soundness result for the calculus as a whole; mechanization (rung 7) remains
owed; Gate 7 is unchecked.

### Gate 5: annotated-term soundness

Define the semantics of the satisfaction relation $\models$ on states and on
command evaluations. Then prove that every property annotation derivable by the
initial rules is true of the denoted state or evaluation.

**Ratified (2026-11-19).** Scope: the satisfaction relation $\models$ on states
and command evaluations and annotated-term soundness for the kernel five,
`E-GRAFT`, the Gate 6 structural/`Ann.gen` rows, and the `stdCSS-3`
constructors' structural/well-formedness rows (§4.11;
`lean/CodeCalculus/ExpandedSoundness.lean`). What this ratification does **not**
claim: conditional priced/certificate/layout-honesty cells, §2j family-level
transport, or `A-QUOTIENT` (§2i), which remain restricted; mechanization
(rung 7) remains owed for the kernel slice; Gate 7 is unchecked.

### Gate 6: transformation extension decision

Use the first calculus and the taxonomy-to-syntax contract to determine whether
presentation rebasing, peeling, puncture, extension (patch growth and breeding),
graft, merge, split, or another transformation can be added without changing the
core state model. Every admitted extension must identify its additional support,
column-update, or interface predicates.

**Scope decision (priced construction calculus).** `E-GRAFT`, the exact deletion
price for `C-DELETE-CHECK`, and strict improvement for `C-ADD-CHECK` are
included as **conditional** extensions: their cells carry only when the consumer
supplies the stated hypothesis, and otherwise remain `unavailable` or `not yet
defined`. This does not pass Gate 0 or establish `E-GRAFT` as a sound
formal-calculus rule, and its ladder position remains `transition-defined`:
`OBL-GRAFT-TRANSITION-SOUNDNESS` is discharged at §4.12 and
`OBL-JUDGMENT-SOUNDNESS` at §4.11, but discharge is not promotion and no dated
decision promotes the rung. Glue, puncture, patch growth/breeding, and Hadamard
remain extension decisions under this gate, except the CSS-level subset
(`E-GLUE`, `E-PUNCTURE`, `E-PEEL`, `E-EXTEND`, `E-LOCAL-HADAMARD`,
`P-REBASE`) admitted as conditional cells on 2026-10-23.

**Extended-state layer (refused for `v0.3.0`, 2026-11-18).** Whether the ordinary-CSS state model
$C=(Q,X,Z,\mathsf{pres},\mathsf{used})$ is extended to a two-sorted model
(CSS as a special case plus a general stabilizer state presented by a
symplectic check matrix), with cross-layer moves between them, is also a Gate 6
decision. Leading candidate moves are `X-SYMPLECTIC-DOUBLE` (general
stabilizer → CSS) and `X-SYMPLECTIC-HALVE` (CSS → general stabilizer,
requiring typed halving data: a fixed-point-free involution $\pi$ with
$\pi(S_X)=S_Z$). Scoping: taxonomy records in `TAXONOMY.md` §4.3. Both sit at
the admission ladder's `taxonomy-only` rung — a contract-index row, but no
grammar production, no typed transition, and no obligation — and no obligation
attaches until Gate 6 admits them. The maintainer has refused admission for
`v0.3.0`: the state model stays $C=(Q,X,Z,\\mathsf{pres},\\mathsf{used})$, the
four records stay at `taxonomy-only`, and `machine/symplectic_calculus.py`
stays a consumer-side model that admits nothing. Reopening requires a reviewed
design note for the two-sorted state model (including the sign decision and the
embedding of the CSS line), a re-evidencing plan, and a per-move decision
starting with the two symplectic moves (diary entry
`2026-11-18-refuse-admission-of-the-extended-state-layer-issue-545.md`). Out
of scope under the stopping point.

**Ratified (2026-11-19).** Scope: the CSS-level transformation
extension decisions — `E-GLUE`, `E-PUNCTURE`, `E-PEEL`, `E-EXTEND`,
`E-LOCAL-HADAMARD`, and `P-REBASE` admitted as conditional cells with their
additional support, column-update, and interface predicates identified
(§4.26–§4.32); `E-GRAFT` remains `transition-defined` with transition
soundness discharged (§4.12) but not promoted. The extended-state
(two-sorted symplectic) layer is refused for `v0.3.0`. What this
ratification does **not** claim: promotion of `E-GRAFT` past
`transition-defined`; admission of the extended-state layer; any soundness result
for the calculus as a whole; mechanization (rung 7) remains owed; Gate 7 is
unchecked.

### Gate 7: constructor, family, and completeness decision

Only after the preceding gates should the collaborators decide which lower-level
constructors require typed input objects, which named families are closed under
which transformations, and whether a non-circular generation or transition
completeness theorem is justified.

**Decision inputs recorded (2026-11-24 / 2026-11-25).** All three questions
have dated records in [`TAXONOMY.md`](TAXONOMY.md), *Gate 7 decision matrices*
and *Completeness feasibility decision (Gate 7, issue #606)*. The *typed-input
decision matrix* records, for every admitted constructor and command, whether
its typed inputs are required, optional, or derived. The *family-closure
matrix* records closure or non-closure for each named family under each
admitted transformation; a closure there is a code-level membership fact and
enters no judgment cell. On 2026-11-25 (maintainer decision, MathysRennela;
issue #606, Option (a)), the completeness question was settled by recording a
scoped, non-circular feasibility argument for elementary generation and
variable-namespace transition completeness and opening
`OBL-ELEMENTARY-COMPLETENESS` in [`OBLIGATIONS.md`](OBLIGATIONS.md) (status
`open`; folded into `stdCSS-3` / `v0.3.2` by maintainer decision 2026-11-26),
leaving deliberate
judgment incompleteness (`design/SCOPE.md` §2, §11 below) untouched.
Recording these inputs does not by itself check Gate 7.

**Ratified (2026-11-26, maintainer decision, MathysRennela; issue #603).**
Scope: the three Gate 7 questions are settled for `stdCSS-3`
([`VERSIONING.md`](VERSIONING.md) §4.1, §8) on the decision inputs above and
on the Tier 2 dispositions listed below, each of which is recorded once, in
its own dated diary fragment and in the `spec/` sections it names. This record
cites them and does not restate them.

1. **Typed inputs.** Typed inputs stay arguments of their production or
   command; none becomes a field of $C=(Q,X,Z,\mathsf{pres},\mathsf{used})$
   (`STATE_MODEL.md` §1). The matrix's required / optional / derived verdicts
   stand as recorded. Priced hypotheses remain judgment inputs, never
   production arguments. No production, transition, or judgment cell is added
   by this decision.
2. **Family closure.** The matrix's closure and non-closure verdicts stand as
   recorded: code-level membership facts that enter no judgment cell and no
   claim rung. They are not soundness results.
3. **Completeness.** Settled by the 2026-11-25 decision above: no completeness
   theorem is claimed for `stdCSS-3`. `OBL-ELEMENTARY-COMPLETENESS` stays
   `open` (recorded in `stdCSS-3` / `v0.3.2` by maintainer decision 2026-11-26)
   and moves no `discharged-through` value. Judgment incompleteness is unchanged.

**Tier 2 dispositions this ratification relies on** (all issues closed on
`main`):

- `#544` (future-$\Pi$ fields): specified as sketch refinement (PR #660); none
  admitted as state data (`STATE_MODEL.md` §1a; diary
  `2026-11-25-future-pi-field-sketches-issue-544.md`).
- `#546` (`E-SPLIT`): separating deletion admitted 2026-11-25 as the command
  production $\mathrm{split}_{Q_A; R}$ at `transition-defined`; two-state
  projection refused (PR #662; `VERSIONING.md` §5.3; diary
  `2026-11-25-admit-e-split-separating-deletion-issue-546.md`).
- `#565`, `#567` (nonabelian group inputs; conditional constructor cells with
  witness lifting): implemented (PR #622).
- `#568` (pair-partition constructor): implemented (PR #621).
- `#571` (split-subset `E-LOCAL-HADAMARD`): implemented (PR #661;
  `VERSIONING.md` §5.3).
- `#572` (gate-realization extensions): admitted 2026-11-26 (PR #665) and
  folded into `stdCSS-3` / `v0.3.2` by maintainer decision 2026-11-26
  (`VERSIONING.md` §5.3; diary `2026-11-26-gate-realization-log-frame-issue-572.md`,
  `2026-11-26-ship-v032-fold-stdcss-4-into-stdcss-3.md`).
- `#573` (symplectic inner inputs for `A-CONCAT`): refused 2026-11-25
  (PR #663; `TAXONOMY.md` §2.14; diary
  `2026-11-25-refuse-symplectic-inner-inputs-for-a-concat-issue-573.md`).
- `#606` (completeness): obligation opened 2026-11-25, as above (PR #663;
  diary `2026-11-25-gate7-completeness-feasibility-obligation-issue-606.md`).
- `#657` (instance-contract obligations for the `v0.3.x` inventory): recorded
  2026-11-25, including the `C-COLUMN-CNOT` Lean `Command` constructor
  (PR #663; `VERSIONING.md` §5.2; diary
  `2026-11-25-record-stdcss-3-instance-contract-obligations-issue-657.md`).

**Ledger pass (issue #609).** [`OBLIGATIONS.md`](OBLIGATIONS.md) and
[`CLAIMS.md`](CLAIMS.md) match this record: the ratification admits nothing,
so no `discharged-through` value and no `stdCSS-3` claim rung moves.

**Extended-state layer.** The 2026-11-18 refusal (Gate 6 above) was worded for
`v0.3.0`. Everything published in a `v0.3.x` tag is `stdCSS-3`
(`VERSIONING.md` §5.2), so this record reads the refusal as attaching to
`stdCSS-3`: the extended-state (two-sorted symplectic) layer is not part of
the `stdCSS-3` this gate ratifies. Admitting it would be a new line, not a
`stdCSS-3` patch.

What this ratification does **not** claim: any soundness result for the
calculus; promotion of `E-GRAFT` past `transition-defined`; admission of the
extended-state layer; any completeness theorem; any mechanized metatheorem
beyond those already recorded (rung 7 remains owed for the kernel slice); or
any new production, judgment cell, or consumer path. Mechanization (issue
#607) is complete on the scoped modules, with `lake build` green and no
`sorry` (`lean/CodeCalculus/AxiomAudit.lean`). Gates 0–6 remain ratified as
recorded; Gate 7 is ratified for `stdCSS-3`.

---

## 11. Non-goals for the first project phase

The first phase does not attempt to:

- provide a complete move set for all CSS codes;
- define a final family of all target codes;
- prove that every property is inferable;
- prove distance preservation for every move;
- derive circuit realizations;
- establish DEM-level distance equality;
- implement a software code generator beyond the admitted consumer (evaluator,
 certify/prune/re-measure loop, qLDPC adapter);
- make category theory load-bearing.

The first phase is entirely formal. Computational work may help discover examples
or counterexamples, but no claim enters the proposal without a mathematical
derivation.

### Future empirical dataset protocol

Only after the design phase and an explicitly authorized implementation, the
[Unitary Foundation QEC Challenge](https://unitaryfoundation.github.io/qldpc-challenge/)
dataset may serve as a non-normative empirical testbed. It is not an MVP
deliverable. The future sequence would be:

1. **Regression of proven judgments.** Load the dataset and verify the already-proven rules (direct-sum min-distance, $k\pm 1$ bookkeeping, `addStab` monotonicity) on all codes. A plumbing check, not a proof.
2. **Two-sector deletion sweep.** Apply single-generator deletion over a stratified sample; compute sector distances before and after; test candidate closed forms for the newly admitted logical classes. Every mismatch is a counterexample to a candidate formula.
3. **Move-ladder mining.** Construction-family ladders in the dataset (lifted, balanced, generalized-bicycle series) are candidate derived move sequences; check whether observed parameter transitions obey candidate judgment rules.

Discipline for all three steps:

- A dataset run can falsify a candidate rule but never confirm soundness; mined conjectures enter the calculus only with a derivation.
- Upper-bound distance witnesses suffice for counterexamples but not for confirming inequalities; exact distances are computed only where the positive direction is needed.
- Experiments fix a canonical presentation (e.g., row-reduced); any surviving formula must be presentation-invariant.
- The dataset is context-free: it informs code-level judgments only, not context-composition obligations.
