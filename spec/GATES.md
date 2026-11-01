# Gates and Non-Goals

**Status:** normative. **One authority per topic.**

Gate 0 and Gate 1 are passed. Gates 2–7 are **unchecked**. A gate-status audit
records evidence and open items and does not ratify any gate.

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
`OBLIGATIONS.md`); the discharge supersedes only the "remained open" reading,
not the ratification itself. Gate 6 remains unchecked (discharge is not
promotion).

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

### Gate 2: deletion derivation

Give a complete formal rule for single-stabilizer deletion and prove output
validity, the exact logical-dimension consequence, and the quotient-level
logical-sector results. Mark deletion-distance lower bounds and equalities
explicitly unavailable; no deletion-distance formula is an MVP gate. The
non-increase upper bound is an included claim with its hand derivation recorded
at `spec/OPERATIONAL_SEMANTICS.md` §4.

### Gate 3: direct sum and sequencing

Prove that direct sum and sequential composition produce valid terms and derive
their structural judgments. Prove the sequencing obligations of Section 4: skip
identity, associativity, conditional permutation of independent moves, and
judgment transport for the partial big-step relation.

### Gate 4: stabilizer-addition derivation

Add the dual unary rule for an independent commuting CSS stabilizer and prove
its exact logical-dimension and distance-monotonicity judgments. Do not include
subsystem-code gauging in this gate.

### Gate 5: annotated-term soundness

Define the semantics of the satisfaction relation $\models$ on states and on
command evaluations. Then prove that every property annotation derivable by the
initial rules is true of the denoted state or evaluation.

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

**Extended-state layer (deferred).** Whether the ordinary-CSS state model
$C=(Q,X,Z,\mathsf{pres},\mathsf{used})$ is extended to a two-sorted model
(CSS as a special case plus a general stabilizer state presented by a
symplectic check matrix), with cross-layer moves between them, is also a Gate 6
decision. Leading candidate moves are `X-SYMPLECTIC-DOUBLE` (general
stabilizer → CSS) and `X-SYMPLECTIC-HALVE` (CSS → general stabilizer,
requiring typed halving data: a fixed-point-free involution $\pi$ with
$\pi(S_X)=S_Z$). Scoping: taxonomy records in `TAXONOMY.md` §4.3. Both sit at
the admission ladder's `taxonomy-only` rung — a contract-index row, but no
grammar production, no typed transition, and no obligation — and no obligation
attaches until Gate 6 admits them. Out of scope under the stopping point.

### Gate 7: constructor, family, and completeness decision

Only after the preceding gates should the collaborators decide which lower-level
constructors require typed input objects, which named families are closed under
which transformations, and whether a non-circular generation or transition
completeness theorem is justified.

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
