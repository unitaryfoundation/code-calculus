# CSS-Code Operation Taxonomy

## Purpose

This note inventories operations and constructors in the CSS-code calculus. It distinguishes four origins; some origins have more detailed sublayers:

1. **Supporting presentation operations** act on how a code is displayed. They are often prerequisites for a deformation, but do not necessarily produce a new code up to equivalence.
2. **CSS-code transformations** take one or more already-formed CSS-code states as input and produce another CSS-code state.
3. **Lower-level constructors** form a CSS code from ingredients below the CSS-code level, such as classical codes, matrices, group algebras, graphs, or cellulations. These are part of the long-term taxonomy but are not assumed to belong to the first calculus slice.
4. **Extended-state operations** require a state model beyond ordinary CSS stabilizer codes, such as gauge generators, stabilizer centers, or subsystem logical sectors.

The taxonomy is normative about vocabulary and distinctions, but not every listed operation is currently a formal calculus rule. A named operation becomes a calculus rule only after its state type, applicability conditions, state update, CSS-preservation proof, property judgments, and semantic contract have been specified. The contract schema and evidence-status rules are maintained in [`CLAIMS.md`](CLAIMS.md).

`A-*` is a sublayer label rather than a fifth origin: an algebraic operation is code-level when its inputs are already CSS states, and lower-level when its inputs are matrices, complexes, algebras, graphs, or other ingredients below the CSS-code level.

The taxonomy deliberately does not classify circuits, measurement procedures, decoding procedures, or layout-only changes.

## Stable operation identifiers

The following identifiers are stable cross-references for the proposal, work plan, proof ledger, and future mechanization. An identifier classifies an operation; it does not by itself admit that operation into the calculus.

| ID | Operation | Layer |
| --- | --- | --- |
| `P-RELABEL` | Qubit relabeling | Supporting presentation |
| `P-REBASE` | Generator rebasing and row replacement | Supporting presentation |
| `C-SKIP` | Identity / `skip` | Core CSS calculus |
| `C-DIRECT-SUM` | Direct sum | Core CSS calculus |
| `C-DELETE-CHECK` | Stabilizer/check deletion | Core CSS calculus |
| `C-ADD-CHECK` | Stabilizer/check addition | Core CSS calculus |
| `C-SEQUENCE` | Sequential composition | Core CSS calculus |
| `E-PEEL` | Qubit/check peeling | Conditional CSS extension admitted 2026-10-23; transition defined 2026-10-23; soundness discharged (§4.32), conditional on hypotheses |
| `E-GRAFT` | Row-space grafting | In-scope conditional CSS extension; transition soundness proved under the coverage guard (§4.12); interval soundness proved (§4.13) |
| `E-PUNCTURE` | Puncturing | Conditional CSS extension admitted 2026-10-23; transition defined 2026-10-23; soundness discharged (§4.32), conditional on hypotheses; distance prices blocked |
| `E-EXTEND` | Qubit/check extension | Conditional CSS extension admitted 2026-10-23; transition defined 2026-10-23 (row-added form); soundness discharged (§4.32), conditional on hypotheses |
| `E-GLUE` | Interface gluing / merge | Conditional CSS extension admitted 2026-10-23; binary-only expression constructor `glue(e₁, e₂; seams)` (`TERM_LANGUAGE.md` §1–§2, decided 2026-11-18; no unary command production); evaluator transition (§4.31) and interval soundness (§4.32) discharged; future-$\Pi$ fields defined (`STATE_MODEL.md` §1a); CSS-level algebra of §4.31/§4.33 mechanized (`GlueExtraction.lean`) with geometric move-word gap recorded; `contract-stated` (rung 5, 2026-11-18; Gate 6 unchecked) |
| `E-SPLIT` | Split | Candidate CSS extension (unadmitted) |
| `E-LOCAL-HADAMARD` | Local Hadamard (per-qubit sector swap) | Conditional CSS extension admitted 2026-10-23; transition defined 2026-10-23 for the $T=Q$ instance (§4.27); soundness discharged (§4.32), conditional on hypotheses |
| `C-COLUMN-CNOT` | CSS-preserving column CNOT/SWAP transformation | Conditional CSS extension admitted 2026-11-18: state transformer by `U in GL(Q, 2)` with `H_X -> H_X U^{-1}`, `H_Z -> H_Z U^T`; `n' = n`, `k' = k`; `w`, `r` recomputed; distance window `[ceil(d_sigma / rho_sigma^-), rho_sigma d_sigma]` with four sector norms (§4.42); Hamming weight non-invariant; no zero-price generic CNOT layer |
| `A-PRODUCT` | Algebraic product of code-level objects | Later algebraic constructor; the CSS tensor product admitted 2026-11-11 as a typed expression constructor, `transition-defined` (`OPERATIONAL_SEMANTICS.md` §2 card, §4.35) |
| `A-CONCAT` | Concatenation | Later algebraic constructor; admitted 2026-11-11 as a typed expression constructor, `transition-defined` (`OPERATIONAL_SEMANTICS.md` §2 card, §4.34); the tower price provider is separate |
| `A-QUOTIENT` | Quotient and subspace transformation | Later algebraic constructor |
| `A-DOUBLE` | Duplication ("double it") construction | Later algebraic constructor; the two-sheet cover under a wiring map admitted 2026-11-11 as a typed expression constructor, `transition-defined` (`OPERATIONAL_SEMANTICS.md` §2 card, §4.35) |
| `A-PULLBACK` | Pullback / fiber product along interface maps | Later algebraic constructor; admitted 2026-11-19 as a typed expression constructor (`pullback(e₁, e₂, e_I; φ₁, φ₂)`), `transition-defined` (`OPERATIONAL_SEMANTICS.md` §2 card, §4.43) |
| `A-PUSHOUT` | Pushout / amalgamated sum along a shared subcode | Later algebraic constructor; admitted 2026-11-19 as a typed expression constructor (`pushout(e₁, e₂, e_S; ψ₁, ψ₂)`), `transition-defined` (`OPERATIONAL_SEMANTICS.md` §2 card, §4.43) |
| `L-EMPTY` | Empty code (nullary base constructor) | Lower-level base constructor; admitted 2026-11-19 as a nullary expression constructor (`empty`), `transition-defined` (`OPERATIONAL_SEMANTICS.md` §2 card, §4.43) |
| `L-FREE` | Free code (qubit-set base constructor) | Lower-level base constructor; admitted 2026-11-19 as a typed expression constructor (`free(Q)`), `transition-defined` (`OPERATIONAL_SEMANTICS.md` §2 card, §4.43) |
| `L-NESTED-CSS` | CSS code from nested classical codes | Lower-level constructor; admitted 2026-11-13 for codes given by parity-check matrices as a typed expression constructor, `transition-defined` (`OPERATIONAL_SEMANTICS.md` §2 card, §4.36) |
| `L-MAPPING-CONE` | Mapping cone of a chain map between two-term complexes | Lower-level constructor; admitted 2026-11-18 for codes given by four binary matrices satisfying the chain-map premise as a typed expression constructor, `transition-defined` (`OPERATIONAL_SEMANTICS.md` §2 card, §4.41) |
| `L-HGP` | Hypergraph product | Lower-level constructor; admitted 2026-11-11 as a typed expression constructor, `transition-defined` (`OPERATIONAL_SEMANTICS.md` §2 card, §4.34) |
| `L-LIFTED` | Lifted product | Lower-level constructor; admitted 2026-11-11 as a typed expression constructor, `transition-defined` (`OPERATIONAL_SEMANTICS.md` §2 card, §4.34; generalized to finite abelian and nonabelian groups 2026-11-22, §4.44) |
| `L-BALANCED` | Balanced product | Lower-level constructor; admitted 2026-11-11 as a typed expression constructor, `transition-defined` (`OPERATIONAL_SEMANTICS.md` §2 card, §4.35; generalized to finite abelian and nonabelian groups 2026-11-22, §4.44) |
| `L-GROUP-ALGEBRA` | Group-algebra and two-block constructions | Lower-level constructor; the two-block code over a finite group (abelian or nonabelian, with explicit left/right regular representations) admitted 2026-11-11 as a typed expression constructor, `transition-defined` (`OPERATIONAL_SEMANTICS.md` §2 card, §4.34; generalized 2026-11-22, §4.44) |
| `L-TANNER` | Local code on a graph / quantum Tanner construction | Lower-level constructor; admitted 2026-11-11 as a typed expression constructor, `transition-defined` (`OPERATIONAL_SEMANTICS.md` §2 card, §4.35) |
| `L-TILE` | Tile or cellulation construction | Lower-level constructor; admitted 2026-11-11 as a typed expression constructor, `transition-defined` (`OPERATIONAL_SEMANTICS.md` §2 card, §4.35) |
| `L-PAIR-PARTITION` | Pair-partition relative-permutation construction (CPM-PP / APM-PP) | Lower-level constructor; admitted 2026-11-22 as a typed expression constructor (`pair_partition(p; B_X, B_Z)`), `transition-defined` (`OPERATIONAL_SEMANTICS.md` §2 card, §4.46) |
| `PP-SCALE` | Explicit extension (size scaling) of a pair-partition code (Kasai 2026) | Lower-level specialization constructor; promoted 2026-11-22 to a typed expression constructor (`pp_scale(e; P)`), `transition-defined` (`OPERATIONAL_SEMANTICS.md` §2 card, §4.47) |
| `X-GAUGE-FIX` | Gauge fixing | Extended state model |
| `X-GAUGING` | Gauging / logical measurement by gauging | Extended state model (deferred) |
| `X-LOCAL-CLIFFORD` | Local/block-Clifford conjugation | Extended state model (deferred) |
| `X-SUBSYSTEM` | Subsystem-code deformation | Extended state model |
| `X-SYMPLECTIC-DOUBLE` | Symplectic doubling (general stabilizer → CSS) | Extended state model (deferred) |
| `X-SYMPLECTIC-HALVE` | Symplectic halving (CSS → general stabilizer) | Extended state model (deferred) |
| `X-DRESSED-QUOTIENT` | Dressed quotient (parent Pauli code + higher-form/cup-polynomial background + trivializing cover → commuting-projector code) | Extended state model (candidate; prior art Hsin, arXiv 2611.09538v1) |

---

## Operation records

Each operation should eventually be documented using the following fields.

| Field | Meaning |
| --- | --- |
| **Status** | MVP candidate, admitted conditional extension, candidate extension, later constructor, or deferred state model |
| **Input** | The typed objects consumed by the operation |
| **Output** | The typed CSS-code state produced |
| **Operation** | The mathematical state transformation |
| **Conditions** | Well-formedness, independence, support, interface, or orthogonality requirements |
| **Parameter effects** | Sound consequences for $n$, $k$, distances, row spaces, supports, or interfaces |
| **Primitive / derived** | Whether the operation is a primitive command or a composition of other operations |
| **Formalization status** | Specified in planning documents, candidate, or not yet specified |
| **Semantic contract** | Status and link to the operation's semantic contract in [`CLAIMS.md`](CLAIMS.md) |
| **Partial inverse** | An inverse-direction operation, when one exists under additional data |

A parameter effect is not a theorem merely because it is observed in an example. It enters the calculus only with stated hypotheses and a derivation.

## Semantic contract reference

[`CLAIMS.md`](CLAIMS.md) defines the proof-oriented contract required for operations admitted to the calculus. It records, per claim:

- exact effects on $n$, $k$, and stabilizer ranks;
- sector-specific and full-distance effects;
- newly admitted, removed, and transported logical classes;
- required support, interface, and context data;
- claim shape and evidence status, using the controlled vocabularies in [`CLAIMS.md`](CLAIMS.md);
- complexity of applicability checks, construction, validation, and exact-distance computation;
- metric-preservation status by sector and for the full distance;
- partial inverses and information loss;
- provenance required for sequencing, audit, and inversion.

The taxonomy can list an operation as `taxonomy-only` or `contract-draft` without claiming that its effects are proved. An operation is not an admitted transition until its transition is defined and output well-formedness is proved. A contract may still mark individual property effects as `open` or `unavailable`; unknown effects must never be omitted.

---

# 1. Supporting presentation operations

These operations change the displayed presentation or the names of objects. They are included because support-sensitive deformations may depend on the chosen presentation.

## 1.1 Qubit relabeling

| Field | Description |
| --- | --- |
| **Status** | Core infrastructure |
| **Input** | A presented CSS code and a finite bijection on its qubit set |
| **Output** | An isomorphic presented CSS code |
| **Operation** | Transport every stabilizer support along the bijection; logical witnesses, interfaces, and certificates are not carried (not-yet-defined future-$\Pi$ data) |
| **Conditions** | The transport must be applied consistently to all presentation and context data |
| **Parameter effects** | $n$, $k$, sector distances, and stabilizer dimensions are preserved |
| **Primitive / derived** | Supporting primitive |
| **Formalization status** | Required by presentation equivalence; not in the kernel grammar |
| **Partial inverse** | The inverse relabeling |

Qubit relabeling should be an explicit congruence of the calculus, not an accidental property of matrix layout.

**Flagged dependency.** The transport claim above now carries stabilizer supports only; logical witnesses, interfaces, and certificates are not-yet-defined future-$\Pi$ data and are not transported. The dependency is thereby narrowed rather than resolved, and remains a prerequisite for `OBL-PRESENTATION-CONJUGATION`. The design-level type sketch for the logical-witness field lives in the superseded
CONTEXT_FIELD_INVENTORY.md
§4.1, retained as provenance; no clean successor exists in `spec/` (future-$\Pi$
data is not MVP state data per [`STATE_MODEL.md`](STATE_MODEL.md) §1).

*(Intentional provenance: `CONTEXT_FIELD_INVENTORY.md` is superseded; the type sketch above is a design proposal, not a normative
definition. Citation retained for the historical record; not a normative
dependency.)*

## 1.2 Generator rebasing

| Field | Description |
| --- | --- |
| **Status** | Core infrastructure |
| **Input** | A CSS code and a new independent basis for one or both stabilizer row spaces |
| **Output** | The same semantic CSS code with a new presentation |
| **Operation** | Replace the displayed generators by another basis spanning the same $X$- or $Z$-row space |
| **Conditions** | The new rows must have the same type, be independent, and span the original row space |
| **Parameter effects** | The semantic code, $n$, $k$, and distances are unchanged; support-sensitive predicates may change truth value |
| **Primitive / derived** | Supporting primitive |
| **Formalization status** | Transition defined 2026-10-23: the command $\mathrm{rebase}_{\tau;M}$ is in the grammar ([`TERM_LANGUAGE.md`](TERM_LANGUAGE.md) §2) and its typed transition, applicability ($M \in \mathrm{GL}$), update, and derivations are in [`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §2 and §4.26, under the 2026-10-23 Gate 6 admission (`JUDGMENT_LAYER.md` §2f); `OBL-REBASE-GENERATION` discharged at §4.26. Its sound admission is discharged (`OBL-GATE6-CSS-EXTENSIONS`, §4.32) |
| **Partial inverse** | Any other basis change |

Rebasing is not the same as deleting a stabilizer. It changes the displayed presentation but not the stabilizer subgroup.

## 1.3 Generator replacement by a row-space element

A generator replacement is a useful special case of rebasing. For example, a displayed generator $r$ may be replaced by $r+s$ when $s$ is a suitable sum of generators of the same type.

The replacement must preserve independence and the generated row space. It is the supporting operation that can expose a low-weight stabilizer for a later qubit/check deformation.

## 1.4 Presentation equivalence

For the MVP, presentation equivalence identifies states related by permitted qubit relabelings, with generator identifiers and displayed rows transported along the bijection. Generator rebasing is not an MVP command or quotient: it is deferred until support-sensitive applicability and transport are formalized. The calculus retains a concrete presentation whenever a rule refers to a specific displayed generator or support pattern.

---

# 2. Core CSS-code transformations

These operations take already-formed CSS-code states as input. The kernel
contains `C-SKIP`, `C-DIRECT-SUM`, `C-DELETE-CHECK`, `C-ADD-CHECK`, and
`C-SEQUENCE`; `E-GRAFT` is admitted as a conditional construction transition.
The remaining entries are candidate extensions or later constructors.

## 2.1–2.5 The five MVP primitives — **specified elsewhere**

**Moved 2026-10-11.** These five operations are in the kernel, and their
identity, input, conditions and effects are stated **once**, in
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §2, with the syntax in
[`TERM_LANGUAGE.md`](TERM_LANGUAGE.md) §2.

| § | Operation | Taxonomy ID | Specified in |
| --- | --- | --- | --- |
| 2.1 | Identity / skip | `C-SKIP` | [`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §2 |
| 2.2 | Direct sum | `C-DIRECT-SUM` | [`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §2 |
| 2.3 | Stabilizer/check deletion | `C-DELETE-CHECK` | [`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §2 |
| 2.4 | Stabilizer/check addition | `C-ADD-CHECK` | [`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §2 |
| 2.5 | Sequential composition | `C-SEQUENCE` | [`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §2 |

Their admission rung is recorded in
 §1, not here: the ladder is about
*when a thing enters the calculus*, and this file is about *what operations
exist*.

**What this file keeps for them:** the stable operation identifiers (§ above), the
taxonomy-to-calculus contract, and the extension boundary. What it no longer keeps
is a second copy of their rules — which existed, and which is what the lint
cannot catch.

---


## 2.6 Qubit/check peeling

Also called restricted $r=1$ grafting in some deformation contexts.

| Field | Description |
| --- | --- |
| **Status** | Admitted conditional extension |
| **Input** | A CSS code, a qubit $q$, and one displayed stabilizer $r$ of a selected type |
| **Output** | A code with $q$ and $r$ removed, with the remaining stabilizer supports restricted to the remaining qubits |
| **Operation** | Remove one physical qubit together with a unique touching check |
| **Conditions** | $q$ must occur in exactly one displayed generator of the selected type; the resulting restricted checks must remain CSS-orthogonal; required context about interfaces and support ownership must be updated |
| **Parameter effects** | Usually $n'=n-1$ and $k'=k$ when exactly one independent check is removed; distances have no general monotonicity rule |
| **Primitive / derived** | Candidate primitive or derived operation, depending on the chosen state model |
| **Formalization status** | Transition defined 2026-10-23 (`TERM_LANGUAGE.md` §2; `OPERATIONAL_SEMANTICS.md` §2, §4.28), under the 2026-10-23 Gate 6 admission (`JUDGMENT_LAYER.md` §2f). Applicability is the unique-touch premise (the consumer carries a redundant zero-check guard; §4.28 shows it never binds on a well-formed parent); $n'=n-1$ and $k'=k$ are proved exactly (§4.28). Sound admission discharged (`OBL-GATE6-CSS-EXTENSIONS`, §4.32) |
| **Partial inverse** | Qubit/check extension, with the removed qubit, check, and support data supplied |

The unique-touch condition is what prevents the deleted column from changing commutation relations among surviving checks of the relevant type. “Grafting” should not be used without specifying the direction: this operation is the reduction/peeling direction, while its inverse adds structure.

## 2.7 Row-space grafting

| Field | Description |
| --- | --- |
| **Status** | Admitted conditional transition |
| **Input** | A presented CSS state, qubit $q$, sector $\tau$, and an ordering of every displayed $\tau$-row touching $q$ |
| **Output** | A CSS state on $Q\setminus\{q\}$; adjacent products in the selected chain replace its touching rows, and opposite-sector checks are shortened at $q$ |
| **Applicability** | The selected list is exact and nonempty; resulting checks commute and remain independent; $k'=k$; every remaining qubit is touched by both check types |
| **Distance effect** | Conditional, sector-wise: $d'_\sigma=\min(d_\sigma,w_{\mathrm{expose},\sigma})$ for the non-spliced sector $\bar\tau$; the spliced sector carries its lower endpoint and drops its upper endpoint to $+\infty$ unless a witness valid in the child supplies one. The scalar form $d'=\min(d,w_{\mathrm{expose},\bar\tau})$ is **not** valid for this transition, so no relation $d'\le d$ follows. Without a supplied exposure minimum there is no positive lower bound. See [`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4.13, 2026-10-21. |
| **Primitive / derived** | Primitive transition over a presented state; no implicit rebasing operation |
| **Formalization status** | Syntax and transition defined in [`TERM_LANGUAGE.md`](TERM_LANGUAGE.md) §2 and [`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §2. Transition soundness proved under the coverage guard (§4.12), interval soundness proved (§4.13), judgment soundness proved (§4.11); the ladder rung stays `transition-defined`, because discharge is not promotion. |
| **Partial inverse** | Requires the removed qubit, touching rows, and inverse presentation information; generally non-unique |

The coverage condition is an empirical modeling guard, not a theorem for all
CSS families. The exposure minimum is external judgment input and is not
computed by the transition. The source's graft result is retained at
; the repository does not promote that draft source
to `established` evidence.

Cross-check: the qLDPC challenge's shortening entries are instances of this
transition, not an unnamed move the calculus is missing. `../qldpc-challenge`
`a worked example` constructs a code by "remove parent qubit 0, shorten the
X-check row space, and puncture the Z checks" — the §2.7 transition exactly,
and `a worked example` performs a two-row pivot on qubit 548 using the XOR of
two Z rows, a graft with a chain of length two (read at challenge commit
`d5a2a7406f92841ae1129c7db228c4d6eac35892`).

## 2.8 Puncturing

| Field | Description |
| --- | --- |
| **Status** | Admitted conditional extension |
| **Input** | A CSS code, a qubit $q$, and an induced stabilizer-update rule |
| **Output** | A CSS code on $Q \setminus \{q\}$ |
| **Operation** | Remove a physical coordinate and update the stabilizer description accordingly |
| **Conditions** | Raw column restriction is valid only under an explicit compatibility condition, or the operation must include the additional check modifications/measurement semantics that restore CSS orthogonality |
| **Parameter effects** | $n'=n-1$; the change in $k$ and both distances is not fixed by $n$ alone |
| **Primitive / derived** | Candidate primitive |
| **Formalization status** | Transition defined 2026-10-23 (`TERM_LANGUAGE.md` §2; `OPERATIONAL_SEMANTICS.md` §2, §4.29), under the 2026-10-23 Gate 6 admission (`JUDGMENT_LAYER.md` §2f): the admitted induced stabilizer update is the **check-puncturing form** (the qubit and every displayed row touching it are removed). Distance *prices* for this move are deliberately not admitted in this scope — hole-punch pricing is blocked on the D2 lower-bound question; no cell and no fixture for it enters until that lower bound lands. The full price reads `unavailable`, and the partial facts about rectangular holes are recorded as records, not cells (`JUDGMENT_LAYER.md` §2f, hole-punch records). Sound admission discharged (`OBL-GATE6-CSS-EXTENSIONS`, §4.32) |
| **Partial inverse** | Extension by a qubit and compatible stabilizer data; generally many-to-one in the reverse direction |

Raw column deletion is not automatically a valid CSS transformation. If an $X$ row and a $Z$ row both touch $q$, deleting the coordinate can change their overlap parity. A puncturing rule therefore needs either a support predicate or an induced stabilizer update.

## 2.9 Qubit/check extension

| Field | Description |
| --- | --- |
| **Status** | Admitted conditional extension |
| **Input** | A CSS code, a new qubit, and new or modified stabilizer data |
| **Output** | A larger CSS code |
| **Operation** | Add a qubit together with checks or support modifications satisfying CSS orthogonality |
| **Conditions** | The new rows must be independent as claimed, commute with existing opposite-type rows, and preserve all state invariants |
| **Parameter effects** | Depends on whether checks are added, removed, or recombined; no generic $k$ or distance formula |
| **Primitive / derived** | Candidate primitive |
| **Formalization status** | Transition defined 2026-10-23 as the **row-added extension** (`TERM_LANGUAGE.md` §2; `OPERATIONAL_SEMANTICS.md` §2, §4.30), under the 2026-10-23 Gate 6 admission (`JUDGMENT_LAYER.md` §2f): the move adds a qubit set $\Delta$ disjoint from $Q$ and an ordered list of well-typed, canonically-minted check rows over $Q\cup\Delta$. Sound admission discharged (`OBL-GATE6-CSS-EXTENSIONS`, §4.32) |
| **Partial inverse** | Peeling, only with retained support and provenance data |

This is an extension family, not a single universally valid operation. The exact qubit placement and check update must be part of its type.

## 2.10 Interface gluing / merge

| Field | Description |
| --- | --- |
| **Status** | Admitted conditional extension |
| **Input** | Two or more CSS codes plus typed boundary/interface data |
| **Output** | A CSS code on an identified or connected qubit set |
| **Operation** | Identify boundary qubits, add seam checks, remove redundant checks, or otherwise combine stabilizer data across an interface |
| **Conditions** | The interface maps, qubit identifications, retained checks, and cross-interface commutation conditions must be explicit; the interface must also state its logical-dimension bookkeeping — for a parity-measurement seam, $k' = k_1 + k_2 - t$ where $t$ is the number of independent cross-interface constraints (the "logical space is preserved" condition of unequal-distance merges, arXiv:2609.26784 §II.4), with $t$ read from the stabilizer data as the drop in logical dimension attributable to the new seam checks (qubit identification and added seam qubits are accounted for in $n'$ and the check spaces, not in $t$); the merged value is always $k' = n' - \dim X' - \dim Z'$. An interface that does not state its $t$ is inapplicable |
| **Parameter effects** | $n$, $k$, and distances depend on the interface; direct-sum formulas do not apply in general. Seam distance: the scalar relation $d=\min(d_A,d_B)$ is not admitted; settled as `false` as a universal (§4.33 counterexample), holding only instance-wise when a minimum-weight factor class survives the seam. The lower bound $d_\sigma(C)\ge\min(d_\sigma(C_A),d_\sigma(C_B))$ is proved (§4.31, §4.33 Claim 1). Evidence status `false` for the universal candidate claim |
| **Primitive / derived** | Candidate derived operation |
| **Formalization status** | Listed as a later geometric construction |
| **Partial inverse** | Split, only when a cut and its boundary data are retained |

**Review finding (second red-team pass, 2026-09-26) — dispositioned
2026-09-26.** The **Conditions**
row requires every interface to state $t$ and imposes $k' = k_1 + k_2 - t$,
but the operation also identifies qubits and adds seam qubits, and both change
$k'$ without any constraint being measured: two unchecked single qubits have
$k_1 = k_2 = 1$, identifying them gives $k' = 1$ with no measured constraint,
and adding one unchecked seam qubit instead gives $k' = 3$. Read as an
admissibility hypothesis the equation rejects both merges, which is acceptable —
but $t$ must then be defined from the stabilizer data (for example as the drop
in logical dimension attributable to the new seam checks) or the condition
cannot be checked.

**Disposition.** $t$ is read from the
stabilizer data as the drop in logical dimension attributable to the new seam
checks; qubit identification and added seam qubits are accounted for in $n'$
and the check spaces, not in $t$. The **Conditions** row now says so and also
records that $k'$ is always $k' = n' - \dim X' - \dim Z'$. See that review.

Gluing is not the same as placing two codes near each other. It is a code composition only when the resulting stabilizer structure contains an explicitly defined interface operation.

**Gate 6 prerequisite (met, 2026-11-12; defined in full
2026-11-13, [`STATE_MODEL.md`](STATE_MODEL.md) §1a).** Both
future-$\Pi$ prerequisites were first defined as type sketches in
[`STATE_MODEL.md`](STATE_MODEL.md) §1: the logical-witness field
is a set of logical representatives $(S,\sigma,\varepsilon)$ with survival
transport under `E-GLUE`, and the boundary/edge-label field is a
set of boundary supports $(S,\sigma,i)$ indexed by logical operator, with
transport under `E-GLUE` the restriction of logical-witness survival to
boundary supports. Both remain future-$\Pi$ data, not MVP state data, and
neither is minted or read by equality. Merge and split correctness is stated
about logical operators (which representatives survive the seam, which are
created or destroyed) and about boundary segments (which labels are carried,
refined, or exchanged), and the survival transport is the content Theorem 4 /
claim 7.4 of *composition-distance* records. Both prerequisites are thereby
met, subject to the equality cell being discharged and to the
Lean mechanization of the extracted derivation. The scalar
relation $d=\min(d_A,d_B)$ is still not admitted, and the candidate
seam-distance claim is settled as `false` (refuted by the §4.33 counterexample).

**2026-10-27 update.** `E-GLUE` gains an admitted evaluator transition (§4.31): two disjoint factor states are combined and seam checks are minted canonically, consuming the §2e seam certificate. The logical-witness prerequisite (`not-yet-defined`) remains unmet, so no distance relation beyond the §2e conditional cell is admitted and the §2f obstruction row stands.

**2026-11-11 update.** The logical-witness field is defined as a
future-$\Pi$ type sketch in [`STATE_MODEL.md`](STATE_MODEL.md) §1, with
survival transport under `E-GLUE`. The §2e equality cell is discharged by
extraction of Theorem 4 / claim 7.4 of *composition-distance* (recorded in
`OPERATIONAL_SEMANTICS.md` §4.31, 2026-11-11). The first Gate 6 prerequisite
is thereby met; the second (boundary/edge labels) remains `not-yet-defined`,
so the move's distance relation stays the §2e/§2f conditional cell and the
scalar relation $d=\min(d_A,d_B)$ is still not admitted.

**2026-11-12 update.** The boundary/edge-label field is defined
as a future-$\Pi$ type sketch in [`STATE_MODEL.md`](STATE_MODEL.md) §1, with
transport under `E-GLUE` the restriction of logical-witness survival to
boundary supports. Both Gate 6 prerequisites are thereby met. The scalar
relation $d=\min(d_A,d_B)$ remains unadmitted and the candidate seam-distance
claim is settled as `false` (refuted by the §4.33 counterexample).

**2026-11-18 update.** By dated maintainer decision
(MathysRennela): (1) `E-GLUE` remains **binary-only**, recorded in
`TERM_LANGUAGE.md` §1–§2 as the expression constructor
$e ::= \mathrm{glue}(e_1, e_2; \vec u)$ with no unary command production;
(2) the CSS-level algebra of the extracted §4.31/§4.33 derivation is
mechanized in `lean/CodeCalculus/GlueExtraction.lean` (building on
`ExactGlue*.lean`, `LogicalWitness.lean`, `WitnessFields.lean`,
`AdmissibleSeamFamily.lean`, and `Gate6Exact.lean`), with the irreducible
geometric move-word $\to$ `AdmissibleSeam` gap recorded as a substrate
boundary; and (3) `E-GLUE` advances to `contract-stated` (rung 5 in
`CLAIMS.md`), remaining a Gate 6 conditional cell with Gate 6 unchecked.

## 2.11 Split

| Field | Description |
| --- | --- |
| **Status** | Candidate extension |
| **Input** | A CSS code plus a cut/interface decomposition |
| **Output** | One or more CSS codes, or a code with exposed interfaces |
| **Operation** | Separate a code along a specified interface and update checks and qubits |
| **Conditions** | The cut, boundary ownership, and induced stabilizer updates must be specified |
| **Parameter effects** | No generic parameter formula; logical sectors may split, merge, or acquire interface modes |
| **Primitive / derived** | Candidate derived operation |
| **Formalization status** | Listed as a later geometric construction |
| **Partial inverse** | Gluing with the retained interface data |

**Prior art (2026-11-09).** Wang et al., *Decoupling 2D translation-invariant
topological CSS codes*, arXiv 2608.09915 (2026), proves that every 2D
translation-invariant topological CSS code admits a local-unitary decoupling
into toric codes and product states after passing to the maximal
anyon-preserving superlattice, and gives an efficient algorithm for the
decoupling map. This is the inverse direction of gluing/merge (§2.10) and a
sibling of `C-DIRECT-SUM`: it decomposes a code rather than combining two
disjoint ones, and its precondition (anyon-preserving superlattice) is a
typed condition that an `E-SPLIT`-style operation would have to carry. It is
evidence that decomposition is algorithmically available for the topological
subclass; it does not discharge any obligation or promote this candidate
record.

## 2.12 Local Hadamard (per-qubit sector swap)

| Field | Description |
| --- | --- |
| **Status** | Admitted conditional extension |
| **Input** | A presented CSS code and a qubit $q$ (or a subset of qubits) |
| **Output** | A CSS code on the same qubit namespace with the two sector row spaces conjugated at $q$ |
| **Operation** | Apply the Hadamard at $q$: swap column $q$ of the $X$- and $Z$-type support data, exchanging the two sectors' contributions at that qubit |
| **Conditions** | Both sector row spaces split along $q$ — for every row $v$ of $X$, $v|q \in X$, and for every row $w$ of $Z$, $w|q \in Z$. Then the column swap is applied row-wise (each row's entry at $q$ moves to the other sector) and the image is again a well-formed CSS presentation with unchanged ranks. Without the split the image need not be CSS; the former "none beyond a valid input" condition is withdrawn — see the qualification below |
| **Parameter effects** | $n' = n$, $k' = k$, sector ranks unchanged (dimension counts). Distances: no generic rule for a single-qubit application; the full-qubit instance (global $X \leftrightarrow Z$ sector duality) exchanges them exactly, $d_X' = d_Z$ and $d_Z' = d_X$ (candidate effects pending derivation at contract stage) |
| **Primitive / derived** | Candidate primitive |
| **Formalization status** | The **$T=Q$ instance — the global sector duality** — has a typed transition (`TERM_LANGUAGE.md` §2; `OPERATIONAL_SEMANTICS.md` §2, §4.27), admitted 2026-10-23 as a conditional cell under the Gate 6 decision (`JUDGMENT_LAYER.md` §2f). The general split-subset instance is **without a transition**: `hadamard(T)` terms with $\varnothing\subsetneq T\subsetneq Q$ are inapplicable in the admitted transition, whose row-wise image for a mixed row needs a rebasing argument not specified here. Sound admission discharged (`OBL-GATE6-CSS-EXTENSIONS`, §4.32) |
| **Partial inverse** | Itself at $q$ (the Hadamard is an involution; the $T=Q$ instance is involutive) |

**Review finding (second red-team pass, 2026-09-26) — dispositioned
2026-09-26.** The **Conditions**
row's "none beyond a valid input" claim did not survive either reading of the
operation.
*Physical reading:* Hadamarding a subset of qubits can leave the standard-CSS
presentation — witness $Q=\{1,2\}$ with X-row `12` and Z-row `12`, whose image
generates no pure-X or pure-Z element. *Matrix reading:* pairing the $i$-th X
row with the $i$-th Z row depends on row order, which the makes
semantically absent, and breaks orthogonality when the two row lists are not
aligned. The report derives the splitting criterion — the image is standard CSS
exactly when both row spaces split along the conjugated subset — and
cross-checks it by exhaustive enumeration on 3 and 4 qubits (evidence, never
confirmation). The **Parameter effects** row's global instance is correct.

**Disposition.** The first repair is
adopted: the **Conditions** row now requires both row spaces to split along the
conjugated qubits, and the column swap is read row-wise — each row's entry at
$q$ moves to the other sector — not by pairing X rows with Z rows. The
per-qubit move stays in the taxonomy as a conditional CSS-model move, the
global sector swap being the $T=Q$ case. The former unconditional preservation
claim is withdrawn; nothing may cite it. See that review.

Per-qubit conjugation is the only nontrivial single-qubit Clifford effect the phase-insensitive check structure can represent: Paulis act by quotiented phases, and $S$ is not CSS-representable (it maps $\langle X \rangle$ toward $\langle Y \rangle$, which has no pure-sector generator) — hence the name *Hadamard* rather than *local Clifford*. Applying it to every qubit realizes the global $X \leftrightarrow Z$ sector duality. Motivations include rough–smooth boundary changes, twist moves, and the conjugate-copy variants of `A-DOUBLE`. Boundary labels (once defined as proposed in [`STATE_MODEL.md`](STATE_MODEL.md) §1) are where this move's geometric uses would be typed: conjugating along a boundary edge exchanges the sector of the logical representative that edge supports.

## 2.13 Algebraic product of code-level objects

| Field | Description |
| --- | --- |
| **Status** | Later extension |
| **Input** | Typed chain-complex, matrix, or CSS-code objects with a specified product structure |
| **Output** | A CSS code obtained from the product |
| **Operation** | Form a product such as a tensor, homological product, or mapping cone and extract the CSS checks |
| **Conditions** | The input maps, grading, boundary operators, and orthogonality proof must be part of the constructor type |
| **Parameter effects** | Constructor-specific; generic tensor notation is insufficient. **Dispositioned 2026-10-05 (repair (a)):** for the CSS-tensor-product instance these effects are functions of the *retained display's row counts* rather than of ranks, so they are not code invariants; the constructor carries retained-presentation data of `P-REBASE` shape to discharge that dependence. See the disposition below |
| **Primitive / derived** | Usually a lower-level or derived constructor |
| **Formalization status** | Expression production `product(e_A, e_B)` admitted 2026-11-11 for the CSS tensor product of two presented states (`TERM_LANGUAGE.md` §2; `OPERATIONAL_SEMANTICS.md` §2 card, §4.35), `transition-defined`; $k = k_A k_B$ derived; other product structures have no production |
| **Partial inverse** | Generally none; factorization data may provide a restricted decomposition |

A naive tensor product of Hilbert spaces is not by itself a CSS-code operation. The calculus needs the relevant chain-complex or matrix construction.

**Qualification (prior-art sweep, 2026-09-30; **`proposed`, dispositioned
2026-10-05** — repair (a) adopted).** Source: PRIOR_ART.md §1/§6 (arXiv
2609.37231v1, read 2026-09-30), probed as `W20` in
WORKED_EXAMPLES.md. This refines a placeholder. It
withdraws no prior claim, mints no operation identifier, and adds no operation:
the record's status stays *Later extension*.

*(Intentional provenance: `WORKED_EXAMPLES.md` is superseded; no
clean successor in `spec/` for this worked-example record. The instance is
retained as later-layer probe `W20` in (per the superseded
file's successor note). Citation retained for the historical record; not a
normative dependency.)*

- **What the instance shows.** The construction is the Audoux–Couvreur CSS tensor
 product — two length-two chain complexes, the total complex truncated to its
 central three terms — so it instantiates this record rather than adjoining to it,
 and it is emphatically not `C-DIRECT-SUM` (the output qubit set overlaps both
 inputs, so the namespace-disjointness premise of proposal §7.1 and the
 used-set premise of I3 are both unavailable, and $k$ multiplies where
 `C-DIRECT-SUM` adds).
- **Why "Constructor-specific" is now too weak.** It hides that the parameter
 effects are functions not of the code alone but of a **retained display** the
 constructor returns — data of `P-REBASE` shape that is not part of the input
 state. Any future judgment transport over this constructor inherits that
 dependence (`OBL-JUDGMENT-TRANSPORT`).
 The
 earlier form of this bullet argued the effects are *"presentation-count"-
 dependent*, on the ground that *"two presentations of one code therefore give
 two different output sizes under the same constructor."* **That is false under
 reading (A).** $m_X$ is pinned to $\dim X$ and $m_Z$ to $\dim Z$ for every
 well-formed state — I1's span clause is definitional (see
 [`STATE_MODEL.md`](STATE_MODEL.md) §3, corrected
 2026-10-10) — so two well-formed presentations of one code have **identical**
 row counts and therefore identical output size. There is no such choice for the
 effects to depend on. What does vary is the constructor's **retention
 decision** — which rows it carries forward — and that is extra data, not a
 presentation of the input. The dependence survives, restated as a dependence on
 retained-presentation data, which is precisely why the disposition below has
 the constructor carry it. The earlier argument is superseded, not deleted, per
 `AGENTS.md`.
- **The well-formedness clash.** The instance deliberately retains *dependent*
 displayed rows. Its own count formulas give, for one flagged-amplifier step,
 $n' = 90$, $k' = 8$, and $m_X' + m_Z' = 108$ retained check rows, whence
 $\mathrm{rank} H_X + \mathrm{rank} H_Z = 90 - 8 = 82$ and 26 dependent
 displayed rows. Since I1 requires displayed rows to span $X$ and $Z$, and I2
 requires displayed independence (citation corrected 2026-10-10 — it read
 "I2/I5", citing two invariants that do not state spanning), the constructor's
 raw output is not a member of the MVP
 well-formedness class (`OBL-WELL-FORMEDNESS-PRESERVATION`).
 **Qualification (red-team a review finding, 2026-10-10 — DISPOSITIONED as *live repair
 work*, D-3 closed, : reading (A)).** The
 citation "I2/I5 require ... to span the row spaces" repeats the T-2 defect:
 **I2 states displayed independence, I5 is a provenance invariant, and neither
 states spanning** — spanning sits in I1's clause. Under reading (A), where
 I1's span clause is definitional, **the argument below is now false, not merely
 mis-cited**: "Two presentations of one code therefore give two different output
 sizes under the same constructor" cannot hold, because $m_X$ is pinned to
 $\dim X$ for every well-formed state, so two well-formed presentations of one
 code have identical row counts and identical output size. **The conclusion
 survives** — 26 dependent displayed rows violate I2 on its own terms, and the
 constructor's raw output is still outside the well-formedness class — but the
 *rationale* must be rewritten to rest on that rather than on presentation
 counts. **This is the recorded-disposition-was-at-risk case materialising: D-2
 needs rework.** Action owed, ranked below D-1; see
 REDTEAM_D3_SPANNING_2026-10-10.md.
 **Actioned 2026-10-10 — this finding is now worked, not pending.** The
 rationale above has been rewritten and the citation corrected, both in this
 record. **Scope of what changed, stated so it is not read as a re-disposition:**
 the **disposition** (repair (a),
 re-decision; what was defective was its *argument*, now resting on the I2
 violation and on retained-presentation data rather than on presentation counts.
 D-2's queue row stands; no claim status, obligation, or fixture moves.
- **Disposition).** Adopt **repair (a)**: the
 constructor must return an **independent display**, and therefore carries
 retained-presentation data of `P-REBASE` shape. **Repair (b)** — extending
 well-formedness to admit redundant displays — was considered and **rejected**,
 because it would redefine I2/I5 and change the meaning of `pres` for every
 state, and `spec/VOCABULARY.md` treats a new state model as a new line.

 Consequences, recorded so they are not rediscovered:

 - **I2/I5 and the `C-ADD-CHECK` independence premise are unchanged.** Every existing
 fixture and every `OBL-*` statement stays valid.
 - **The `P-REBASE` data shape is admitted as constructor input**, not as an
 `P-REBASE` remains neither command nor quotient in the MVP
 ([`TERM_LANGUAGE.md`](TERM_LANGUAGE.md) §2, qualified 2026-10-05).
 - **The presentation-count dependence is not repaired — it is made explicit and
 carried.** The counts $m_X,m_Z$ were always functions of the chosen display,
 because the constructor counts displayed rows; (a) does not change that, it
 makes the constructor's dependence on its input presentation part of its
 signature. Any judgment transport over this constructor inherits it
 (`OBL-JUDGMENT-TRANSPORT`).
 - **Admission remains a Gate 7 question and is not decided here.** This
 disposition fixes the well-formedness *strategy* only. If Gate 7 declines
 admission, the `P-REBASE`-data boundary revision stands but no constructor
 needs it.
 - **Choosing a repair discharges no obligation.** In particular
 output is **live and unproved**, not discharged:
 it now asks whether the repaired output satisfies I1–I5, which is an open proof
 obligation. This disposition does not establish that the constructor is
 well-formed.

 **Scope limit, recorded against the recommendation.** Deferring to Gate 6 (the
 scoping note's position) was recommended on 2026-10-05 and declined: admission is
 a Gate 7 decision that may never occur, so a repair decided today may
 accommodate a constructor that is never admitted. That reasoning is retained here
 so the trade-off is auditable.
 lower-level constructors require typed input objects is Gate 7 (proposal §10,
 *constructor, family, and completeness decision*). Both remain open; neither is
 dispositioned here.
- **Claim status.** The distance-gain statement for this constructor is
 `proposed`, not `established`: no derivation for it exists in this repository,
 and agreement between prior art and a candidate rule is evidence that may
 falsify the rule, never confirmation (README, *Status*). The row-count
 arithmetic above is an arithmetic consequence of the source's two published
 count formulas, so it is checkable evidence about well-formedness — not a
 derivation of either repair.
- **Circuit layer.** Extraction schedules, gate orders, flag placement,
 fault-response certificates, and circuit distance have no field in
 $C = (Q, X, Z, \mathsf{pres}, \mathsf{used})$; those judgments are `not yet
 defined` here, not `unavailable`.
- **Admission status.** §2.13 has no grammar production — `A-*`/`L-*` constructors
 need typed inputs (proposal §8; crosswalk in `spec/TERM_LANGUAGE.md §2`) — and it
 carries taxonomy-only rows for the L-* constructors; see [`CLAIMS.md`](CLAIMS.md)
 *Initial contract index* and no stable identifier, so it sits below the ladder's
 first rung (`taxonomy-only`) rather than on it. The families it would serve are
 indexed separately: `L-HGP` (canonical HGP amplifiers) and `A-DOUBLE` (duplication).
 Admission of the constructor itself was a Gate 7 matter when this bullet was
 written. **Superseded in part 2026-11-11:** `L-HGP`
 and `A-DOUBLE` are `transition-defined`, and the CSS tensor product instance
 of this record has the production `product(e_A, e_B)` under the stable
 identifier `A-PRODUCT`, also `transition-defined`
 (`OPERATIONAL_SEMANTICS.md` §2 card, §4.35). Product structures other than
 the CSS tensor product still have no production. The bullet's closing
 clause is kept as it stood: the full scoping input is, which decides neither
 gate.
- **Exit-row effect.** None. Because no syntax production is affected, the syntax
 admitted by and its exit are unchanged.

## 2.14 Concatenation

| Field | Description |
| --- | --- |
| **Status** | Later extension |
| **Input** | An outer code and an inner code, or typed classical components for each CSS sector |
| **Output** | A CSS code with encoded blocks replacing outer coordinates |
| **Operation** | Substitute an inner encoded block for each outer coordinate and define the induced stabilizers |
| **Conditions** | Encoding maps, block interfaces, CSS compatibility, and independence claims must be explicit |
| **Parameter effects** | Constructor-specific; block lengths and logical dimensions usually multiply, while distance bounds require hypotheses |
| **Primitive / derived** | Lower-level constructor or derived composition |
| **Formalization status** | Expression production `concat(e_O, e_I; blocks)` admitted 2026-11-11 for CSS factors (`TERM_LANGUAGE.md` §2; `OPERATIONAL_SEMANTICS.md` §2 card, §4.34), `transition-defined`; non-CSS inner inputs excluded |
| **Partial inverse** | Generally none |

**Flagged gap — non-CSS inner inputs.** The **Input** row reads
"an outer code and an inner code" without stating whether "code" there means a
CSS state. Three qLDPC board entries concatenate a CSS outer with a non-CSS
stabilizer inner (`codes/512-54-24.json`, `codes/576-42-24.json`,
`codes/672-28-30.json`, added 2026-10-14; read at challenge commit
`6e1e41be3`): the composite is CSS, but the inner input is not representable in
$C = (Q, X, Z, \mathsf{pres}, \mathsf{used})$. Whether `A-CONCAT` admits such
inputs under a typed interface, or whether those instances sit below the CSS
layer, is an open question; until it is answered the **Input** row does not
read onto them. This qualification changes how the record must be read and
stays inline until the question is answered.

**Check-weight effect.** The **Parameter effects** row names block
lengths, logical dimensions, and distance hypotheses but not check weight.
Under the standard block lift — the inner checks on every block plus each outer
check lifted through chosen inner logical representatives — the lifted pieces
of one outer check occupy disjoint inner blocks, so the child's maximum check
weight is the larger of the inner check weight and (heaviest outer check
weight) × (heaviest chosen representative's weight). This is a description of
that lift, not a derived bound and not a price: the check-weight effect is
priced nowhere — the only `A-CONCAT` row in the carry table is the
tower-factorization **price provider**
([`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2a), which supplies
deletion/exposure prices from tower level data and says nothing about check
weight — and the constructor itself is admitted at `transition-defined` without
a check-weight rule ([`CLAIMS.md`](CLAIMS.md),
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4.34). The
effect is not academic on the qLDPC board, whose cell index is locality class ×
check weight:
the three 2026-10-25 board entries (`codes/196-100-4.json`,
`codes/324-196-4.json`, `codes/400-256-4.json`) choose a sparse outer code for
exactly this product — `196-100-4` lifts weight-8 outer checks through
weight-3 representatives to max check weight 24, under the verifier's 32 cap.

## 2.15 Quotient and subspace transformation

| Field | Description |
| --- | --- |
| **Status** | Later extension |
| **Input** | Typed stabilizer spaces, subspaces, quotient maps, or chain-complex data |
| **Output** | A CSS code represented by the resulting quotient or subspace structure |
| **Operation** | Restrict, quotient, identify, or extend stabilizer data under a specified linear map |
| **Conditions** | The map must preserve or explicitly account for CSS orthogonality, qubit support, and independence |
| **Parameter effects** | Depends on ranks and kernels; no generic distance rule (general case). Candidate 1-complex bound for the self-zipping (co-equalizer) instance: $d(Q)\ge \min(d(A),\Delta(f,g))$, where $\Delta$ is the homological separation metric (min weight of a chain with nonzero zipped boundary). Proven in `the coequalizer-bound proof attempt` (2026-11-09). Applies to twist-defect / folding constructions (Bombin 2010; planar-to-toric folding) at the 1-complex level. 2-complex case abandoned (same 2-cell re-exposure obstruction as other identifying compositions). |
| **Primitive / derived** | Algebraic constructor |
| **Formalization status** | Algebraic branch; no grammar production |
| **Partial inverse** | Only with retained kernel, quotient, and embedding data |

“Take a subspace” is not a sufficient operation description. The map and the induced CSS structure must be typed.

**Candidate specialization (recorded 2026-11-09, prior art Hsin arXiv 2611.09538v1).**
The *monomial quotient* — a parent Pauli stabilizer code folded by a free
monomial-Clifford action (qudit permutation + single-qudit Clifford) with orbit
representatives — is a specialization of this record, not a new primitive: same
state update (restrict/identify stabilizer data under a specified map). It earns
a record of its own under §3.8 via a distinct parameter theorem (transfer
theorem: logical qudits, logical operators and distance bounds from the parent,
with a Tate cohomology group counting the new logicals) and a precisely typed
quotient mechanism (free action; consistency condition that a nontrivial
Clifford on a fixed point is inconsistent; representatives up to local Clifford
equivalence). CSS-preserving instance only (permutation actions, or
sector-preserving single-qudit Cliffords); the duality-quotient instance, in
which letters change (the paper's five-qubit example), is the sector-swap case
of `E-LOCAL-HADAMARD` (§2.12) and, when it leaves the CSS model, the
extended-state layer. The dressed-quotient variant (higher-form / cup-polynomial
backgrounds producing commuting-projector codes) is the separate candidate
`X-DRESSED-QUOTIENT` (§4.5), not a specialization of this record. Placement
and admission criteria: `ROADMAP.md` (*Candidate specialization recorded
from prior art*, 2026-11-09) and `PRIOR_ART.md`. Neither is an MVP
transformation.

**Disposition (2026-11-10).** The monomial-quotient
specialization above was admitted as a specialization record under this
operation (§2.15), CSS-preserving instance only, with the transfer theorem as
its conditional price/property cell. Admission of the specialization record
still requires `A-QUOTIENT` itself to be admitted (it remains at rung 1,
`taxonomy-only`); the disposition does not by itself add a grammar production
or advance a ladder rung.

**Specialization row (v0.3.0).** Under §3.8 the monomial quotient
is a specialization of this record, not a new primitive and not a new state
update: it shares `A-QUOTIENT`'s restrict/identify update (and single-code
set-level coequalizers / self-zipping also fold here per the 2026-11-18
disposition). Its row:

| Field | Monomial-quotient specialization |
| --- | --- |
| Input | A CSS parent code $C$ (general Pauli stabilizer parents belong to the deferred extended-state layer §4) plus a free monomial-Clifford action $(G, \{c_g\})$: a finite group $G$ acting freely on the qubits/qudits by permutations composed with single-qudit Cliffords, with chosen orbit representatives |
| State update | $\pi(S)$: identify stabilizer data under the group-equivariant quotient map $\pi$ sending each qudit $q = h r$ to representative $r$ conjugated by $c_h^{-1}$ (quotient, not the deck-invariant subspace) — the same restrict/identify update as `A-QUOTIENT` and the balanced product |
| CSS-preserving instance | Pure qudit-permutation actions ($c_g = I$), or monomial-Clifford actions whose single-qudit Cliffords $c_g$ are **sector-preserving** (each $c_g$ maps pure-$X$ operators to pure-$X$ operators and pure-$Z$ operators to pure-$Z$ operators; on qubits, modulo phase this requires trivial sector exchange, i.e. $\{I, X, Y, Z\}$). **Applicability constraint:** any instance in which some $c_g$ swaps $X \leftrightarrow Z$ (Hadamard-type) or mixes $X$ and $Z$ (e.g. phase-type $X \mapsto Y$) is **not** CSS-preserving and is outside this specialization (checked consumer-side by `machine/quotient_specialization.py` and transcribed in `machine/consumer.json`; `A-QUOTIENT` remains `taxonomy-only` with no admitted calculus transition) |
| Duality-quotient instance routing | Sector-swapping Cliffords (Hadamard-type, e.g. the paper's five-qubit example) and sector-mixing Cliffords are **not** instances of this CSS-preserving row: a global CSS sector swap routes to `E-LOCAL-HADAMARD` (§2.12, $T = Q$), and any quotient leaving the ordinary-CSS model routes to the deferred general-stabilizer extended-state layer (§4, cf. `X-LOCAL-CLIFFORD` §4.4 / `X-SYMPLECTIC-HALVE` §4.3; refused for `v0.3.0` under) |
| Consistency condition | The action must be free: a nontrivial Clifford on a fixed point is inconsistent, and non-free actions violate quotient consistency |
| Local Clifford equivalence | A different choice of orbit representatives changes $\pi$ by single-qudit Cliffords; the quotient is defined up to local Clifford equivalence (sector-preserving local equivalence within this specialization) |
| Parameter theorem (conditional cell) | Transfer theorem (arXiv 2611.09538v1 §3.3): logical qudits, logical operators descending from the parent with new logicals counted by Tate cohomology, and conditional distance bounds from the parent's bounds. Recorded as a conditional cell in `JUDGMENT_LAYER.md` §2i |
| Distance | No generic distance rule; supplied bounds and validated witnesses only, subject to the priced-hypothesis boundary (`JUDGMENT_LAYER.md` §2b, §2c, §2i) |

## 2.16 Duplication ("double it") construction

| Field | Description |
| --- | --- |
| **Status** | Later extension |
| **Input** | A CSS code plus typed duplication data: a wiring/identification map on two copies of the qubit namespace, and for conjugate-copy variants a sector-duality choice |
| **Output** | A CSS code on $2n$ qubits |
| **Operation** | Form two copies of the namespace and impose the specified wiring on their stabilizer row spaces, yielding a code whose qubit count is twice the input's |
| **Conditions** | The wiring data must be explicit and typed; the resulting rows must be independent and $X \perp Z$. The duplication data is part of the constructor type, not implicit layout |
| **Parameter effects** | $n' = 2n$; $k$ and both distances are constructor-specific — no generic distance rule |
| **Primitive / derived** | Candidate primitive; whether it factors through `A-CONCAT` (with a fixed two-qubit inner code), through a cover/lift constructor, or requires `E-LOCAL-HADAMARD` for conjugate-copy variants is an open question, to be settled by the §3.8 criteria |
| **Formalization status** | Expression production `double(e; wiring[, conjugate])` admitted 2026-11-11 (`TERM_LANGUAGE.md` §2; `OPERATIONAL_SEMANTICS.md` §2 card, §4.35), `transition-defined`: the two-sheet cover of the displayed incidences, with a commutation premise; the factorization question in the row above stays open |
| **Partial inverse** | Generally none; a projection recovering one copy requires retained wiring data |

A family name alone is not an operation (§3.8), so this record deliberately states the *shape* — a unary code-to-code constructor with $n' = 2n$ — and leaves the mechanism open. Parametric family-level doubling frameworks exist in the prior art (QECLean's BB doubling framework, cover-transfer and deck-homotopy; PRIOR_ART.md §5) and must be represented as parameterizations or factorizations of this record rather than as unrelated primitives.

Toward the open factorization question: the qLDPC challenge kit's
`research/kit/doubling.py` implements the **free-$\mathbb{Z}_2$ BB cover** —
a base BB code on $\mathbb{Z}_l \times \mathbb{Z}_m$ lifted to
$\mathbb{Z}_{2l} \times \mathbb{Z}_m$ at the same polynomial supports — which
changes the group-algebra input of the bivariate-bicycle constructor, i.e.
`L-GROUP-ALGEBRA` / `L-LIFTED` territory, and touches this record through the
odd-cover ladder (odd covers grow $n$ at fixed $k$). The cover ring surjects
onto the base ring, so $k$ of the cover can only grow or stay; whether it
stays is a decidable condition that the kit screens for (qec-lab's A12
equivalence: $k(\text{cover}) = k(\text{base})$ holds exactly when
$1 + x^l$ lies in the ideal $(A,B)$ of
$\mathbb{F}_2[x,y]/(x^{2l}-1, y^m-1)$), with the Gross base and one other
as the instances where it holds. Under that condition, together with the base
floor conditions, $d(\text{cover}) = 2\,d(\text{base})$ — the "double it"
shape with $n' = 2n$ and $k' = k$. The free $\mathbb{Z}_2$ cover is therefore
not an even, $k$-preserving counterpart of the odd-cover ladder by default;
$k$-preservation is a screened-for condition, not a property of the cover.
This is evidence that the degree-2 case of the `n' = 2n` shape factors through
a cover constructor rather than arguing for a dedicated `A-DOUBLE` primitive
(read at challenge commit `d5a2a7406f92841ae1129c7db228c4d6eac35892`).

## 2.17 Pullback / fiber product

| Field | Description |
| --- | --- |
| **Status** | Admitted typed expression constructor (`transition-defined`, 2026-11-19) |
| **Input** | Three well-formed CSS codes $C_1, C_2, I$ and two CSS code morphisms $\phi_1 : Q_1 \to Q_I$, $\phi_2 : Q_2 \to Q_I$ |
| **Output** | A CSS code on the fiber product $Q_1 \times_{Q_I} Q_2$ |
| **Operation** | Form the fiber-product qubit set $Q_1 \times_{Q_I} Q_2$, pull back the displayed rows of $C_1$ and $C_2$ along the projections $\pi_1, \pi_2$, and retain an independent display with canonically minted identifiers |
| **Conditions** | $\phi_1$ and $\phi_2$ are CSS code morphisms into $I$ (pushforwards of displayed rows lie in the corresponding sector span of $I$), and the pulled-back $X$ and $Z$ natural rows have pairwise even overlap |
| **Parameter effects** | $n = |Q_1 \times_{Q_I} Q_2|$, $k$ by rank bookkeeping over the retained display; no automatic distance cell (the naive bound $d(A \times_C B) \ge \min(d_A, d_B)$ is `false`) |
| **Primitive / derived** | Algebraic code-level constructor (includes set-level equalizers) |
| **Formalization status** | Expression production `pullback(e₁, e₂, e_I; φ₁, φ₂)` admitted 2026-11-19 (`TERM_LANGUAGE.md` §1–§2; `OPERATIONAL_SEMANTICS.md` §2 card, §4.43), `transition-defined` |
| **Partial inverse** | Generally none |

## 2.18 Pushout / amalgamated sum

| Field | Description |
| --- | --- |
| **Status** | Admitted typed expression constructor (`transition-defined`, 2026-11-19) |
| **Input** | Three well-formed CSS codes $C_1, C_2, S$ and two CSS code morphisms $\psi_1 : Q_S \to Q_1$, $\psi_2 : Q_S \to Q_2$ |
| **Output** | A CSS code on the amalgamated qubit set $Q_1 \sqcup_{Q_S} Q_2$ |
| **Operation** | Quotient $Q_1 \sqcup Q_2$ by $\psi_1(s) \sim \psi_2(s)$ for $s \in Q_S$, push forward the displayed rows of $C_1$ and $C_2$ modulo 2, and retain an independent display with canonically minted identifiers |
| **Conditions** | $\psi_1$ and $\psi_2$ are CSS code morphisms from $S$, and the pushed-forward $X$ and $Z$ natural rows have pairwise even overlap |
| **Parameter effects** | $n = |Q_1 \sqcup_{Q_S} Q_2|$, $k$ by rank bookkeeping over the retained display; no automatic distance cell (general pushouts with $S \neq 0$ can drop distance) |
| **Primitive / derived** | Algebraic code-level constructor (includes two-code set-level coequalizers) |
| **Formalization status** | Expression production `pushout(e₁, e₂, e_S; ψ₁, ψ₂)` admitted 2026-11-19 (`TERM_LANGUAGE.md` §1–§2; `OPERATIONAL_SEMANTICS.md` §2 card, §4.43), `transition-defined` |
| **Partial inverse** | Generally none |

---

# 3. Lower-level CSS constructors

These operations do not primarily transform an existing CSS code. They form one from lower-level ingredients. They are therefore a later layer of the calculus, even when they are called products or compositions in the literature.

## 3.1 CSS code from nested classical codes

| Field | Description |
| --- | --- |
| **Status** | Later constructor |
| **Input** | Classical linear spaces or parity-check matrices satisfying the relevant nesting/orthogonality relation |
| **Output** | A CSS code $(X,Z)$ |
| **Operation** | Set one stabilizer space from one classical component and the other from a compatible orthogonal component |
| **Conditions** | The resulting $X$ and $Z$ spaces must be orthogonal and the chosen presentation must be defined |
| **Parameter effects** | $n$ and $k$ follow from the classical dimensions; distances require separate classical-code hypotheses |
| **Primitive / derived** | Lower-level constructor |
| **Formalization status** | Expression production `nested(H_X, H_Z)` admitted 2026-11-13 (`TERM_LANGUAGE.md` §2; `OPERATIONAL_SEMANTICS.md` §2 card, §4.36), `transition-defined`, for two parity-check matrices with the nesting as an applicability premise; an instance of the `L-TANNER` production (§4.36) |
| **Partial inverse** | Recovering the classical ingredients is non-unique |

Self-orthogonal Steane-, Hamming-, or Reed–Muller-derived CSS codes belong here. They are not necessarily compositions of two independently supplied quantum codes.

## 3.2 Hypergraph product

| Field | Description |
| --- | --- |
| **Status** | Later constructor |
| **Input** | Two typed classical codes or parity-check complexes |
| **Output** | A CSS code from their homological product |
| **Operation** | Combine the two input complexes into product X- and Z-check maps |
| **Conditions** | Matrix dimensions, tensor-factor ordering, and the product differential must be explicit |
| **Parameter effects** | For $H_i \in \mathbb{F}_2^{m_i \times n_i}$ in the standard parity-check convention, the usual qubit count is $n_1n_2+m_1m_2$; other conventions must state their object ordering |
| **Primitive / derived** | Lower-level constructor |
| **Formalization status** | Expression production `hgp(H₁, H₂)` admitted 2026-11-11 (`TERM_LANGUAGE.md` §2; `OPERATIONAL_SEMANTICS.md` §2 card, §4.34), `transition-defined`; $n = n_1 n_2 + m_1 m_2$ and $k = k_1 k_2 + k_1^{T} k_2^{T}$ derived |
| **Partial inverse** | Generally none |

HGP is a genuine construction, but it should not be conflated with an operation that combines two already-formed CSS states unless the calculus defines that typed interface.

## 3.3 Lifted product

| Field | Description |
| --- | --- |
| **Status** | Later constructor |
| **Input** | Base matrices or chain maps over a specified group algebra or lift algebra |
| **Output** | A CSS code whose block maps are lifted from the base data |
| **Operation** | Replace scalar entries by algebra elements or permutation-like blocks and apply a typed product construction |
| **Conditions** | The coefficient algebra, involution/transpose convention, lift action, and orthogonality proof must be specified |
| **Parameter effects** | Depend on base dimensions and lift size; degree and rank bounds require constructor-specific hypotheses |
| **Primitive / derived** | Lower-level constructor |
| **Formalization status** | Expression production `lift_G(A, B)` admitted 2026-11-11 for finite abelian groups (`TERM_LANGUAGE.md` §2; `OPERATIONAL_SEMANTICS.md` §2 card, §4.34) and generalized 2026-11-22 to finite nonabelian groups via explicit multiplication-table or permutation-generator presentations with commuting left/right regular representations $L(x), R(y)$ and antipode involution $g \mapsto g^{-1}$ (§4.44), `transition-defined` |
| **Partial inverse** | Generally none |

Normal-subgroup lifts are specializations of this layer, not automatically a new primitive.

## 3.4 Balanced product

| Field | Description |
| --- | --- |
| **Status** | Later constructor |
| **Input** | Typed complexes or lifted factors with a shared group action |
| **Output** | A quotient/product CSS code |
| **Operation** | Form a product and quotient redundant copies using the specified shared action |
| **Conditions** | The group action, quotient relation, and induced check maps must be explicit |
| **Parameter effects** | Typically differs from an unconstrained lifted product because the quotient changes qubit and check counts |
| **Primitive / derived** | Lower-level constructor |
| **Formalization status** | Expression production `balanced_G(H₁, α₁; H₂, α₂)` admitted 2026-11-11 for finite abelian groups acting by permutations (`TERM_LANGUAGE.md` §2; `OPERATIONAL_SEMANTICS.md` §2 card, §4.35) and generalized 2026-11-22 to finite nonabelian groups with explicit right action $\alpha_1$ on $H_1$ and left action $\alpha_2$ on $H_2$ (§4.44), `transition-defined` |
| **Partial inverse** | Generally none |

## 3.5 Group-algebra and two-block constructions

| Field | Description |
| --- | --- |
| **Status** | Later constructor |
| **Input** | Algebra elements and a specified regular or coset representation |
| **Output** | A two-block CSS code |
| **Operation** | Build paired X/Z block matrices from left/right multiplication, with the required algebra involution |
| **Conditions** | The exact representation convention must prove $H_XH_Z^T=0$; nonabelian transpose/inversion conventions cannot remain implicit |
| **Parameter effects** | Block length, check degree, and rank depend on the algebra and representation |
| **Primitive / derived** | Lower-level constructor |
| **Formalization status** | Expression production `twoblock_G(a, b)` admitted 2026-11-11 for finite abelian groups (`TERM_LANGUAGE.md` §2; `OPERATIONAL_SEMANTICS.md` §2 card, §4.34) and generalized 2026-11-22 to finite nonabelian groups with $H_X = [L(a) \mid R(b)]$, $H_Z = [R(b^*) \mid L(a^*)]$, and $k = 2|G| - \mathrm{rank}[L(a) \mid R(b)] - \mathrm{rank}[L(b) \mid R(a)]$ (reducing to $2(|G| - \mathrm{rank}[L(a) \mid L(b)])$ when $G$ is abelian; §4.44), `transition-defined` |
| **Partial inverse** | Generally none |

Generalized bicycle, bivariate bicycle, multivariate bicycle, quadricycle, and related group-action families should normally be recorded as specializations or parameterizations of this constructor rather than unrelated primitives.

## 3.6 Local code on a graph / quantum Tanner construction

| Field | Description |
| --- | --- |
| **Status** | Later constructor |
| **Input** | Local classical or CSS codes and a typed graph or group action |
| **Output** | A global CSS code assembled from local constraints |
| **Operation** | Place local code data on graph vertices, edges, or bipartition classes and combine the induced checks |
| **Conditions** | Incidence maps, local-to-global embeddings, and cross-partition commutation must be explicit |
| **Parameter effects** | Depend on graph size, local dimensions, expansion, and boundary conventions |
| **Primitive / derived** | Lower-level constructor |
| **Formalization status** | Expression production `tanner(n; Λ_X, Λ_Z; ι_X, ι_Z)` admitted 2026-11-11 (`TERM_LANGUAGE.md` §2; `OPERATIONAL_SEMANTICS.md` §2 card, §4.35), `transition-defined`, with cross-partition commutation as an applicability premise; one local code per vertex class |
| **Partial inverse** | Generally none |

A Tanner construction is a code constructor even when it is described informally as composing local codes.

## 3.7 Tile or cellulation construction

| Field | Description |
| --- | --- |
| **Status** | Later constructor |
| **Input** | A set of typed local tiles, boundary rules, and a cellulation or assembly pattern |
| **Output** | A global CSS code on the assembled qubits and checks |
| **Operation** | Identify tile boundaries and combine local stabilizer patterns into global checks |
| **Conditions** | Boundary identifications, retained/removed checks, and interface orthogonality must be specified |
| **Parameter effects** | Depend on tile count, boundary type, identifications, and local rank relations |
| **Primitive / derived** | Lower-level geometric constructor |
| **Formalization status** | Expression production `tile(tiles; placements; boundary rules)` admitted 2026-11-11 (`TERM_LANGUAGE.md` §2; `OPERATIONAL_SEMANTICS.md` §2 card, §4.35), `transition-defined`, with interface orthogonality as an applicability premise |
| **Partial inverse** | Splitting the assembly, only with tile and boundary provenance |

“Packing” is not enough to make this a code construction. The tile assembly must change or define the global stabilizer code.

## 3.7a Empty code (nullary base constructor)

| Field | Description |
| --- | --- |
| **Status** | Admitted nullary base constructor (`transition-defined`, 2026-11-19) |
| **Input** | None (`()`) |
| **Output** | The empty CSS code ($Q = \varnothing$, empty display, empty `used`) |
| **Operation** | Construct the trivial 0-qubit CSS state |
| **Conditions** | None (vacuously well-formed) |
| **Parameter effects** | $n = 0$, $k = 0$, $w = 0$, $\kappa = 0$, $r = 0$; semantic $d_X = d_Z = d = +\infty$ (ledger starts at $[0, +\infty)$ per `JUDGMENT_LAYER.md` §2g) |
| **Primitive / derived** | Nullary base expression constructor |
| **Formalization status** | Expression production `empty` admitted 2026-11-19 (`TERM_LANGUAGE.md` §1–§2; `OPERATIONAL_SEMANTICS.md` §2 card, §4.43), `transition-defined` |
| **Partial inverse** | Not applicable |

## 3.7b Free code (qubit-set base constructor)

| Field | Description |
| --- | --- |
| **Status** | Admitted base constructor (`transition-defined`, 2026-11-19) |
| **Input** | A finite set $Q \subset \mathbb{N}$ of distinct nonnegative qubit labels |
| **Output** | The CSS code on $Q$ with an empty display and empty `used` |
| **Operation** | Construct the check-free CSS state on $Q$ (`free(∅) ≡ empty`) |
| **Conditions** | $Q$ is a finite set of distinct nonnegative integers |
| **Parameter effects** | $n = |Q|$, $k = |Q|$, $w = 0$, $\kappa = |Q|$, $r = 0$; semantic $d_X = d_Z = d = 1$ for $Q \neq \varnothing$ and $+\infty$ for $Q = \varnothing$ (ledger starts at $[0, +\infty)$ per `JUDGMENT_LAYER.md` §2g) |
| **Primitive / derived** | Base expression constructor (unary in `QubitSet`, 0-ary in input `CSSCode`s) |
| **Formalization status** | Expression production `free(Q)` admitted 2026-11-19 (`TERM_LANGUAGE.md` §1–§2; `OPERATIONAL_SEMANTICS.md` §2 card, §4.43), `transition-defined` |
| **Partial inverse** | Not applicable |

## 3.7c Pair-partition relative-permutation constructor (`L-PAIR-PARTITION`)

| Field | Description |
| --- | --- |
| **Status** | Admitted lower-level constructor (`transition-defined`, 2026-11-22) |
| **Input** | Lift size $p \ge 1$ and paired block matrices $B_X \in (\mathbb{Z}_p^\times \times \mathbb{Z}_p)^{J_X \times L}$ and $B_Z \in (\mathbb{Z}_p^\times \times \mathbb{Z}_p)^{J_Z \times L}$ ($L \ge 2$ even) of relative permutation / affine maps over $\mathbb{Z}_p$ (CPM-PP with unit slope $a = 1$, or APM-PP with general unit slopes $\gcd(a, p) = 1$) |
| **Output** | A CSS code state on $n = L \cdot p$ qubits ($p$ lift qubits per block column) |
| **Operation** | Assemble the $X$ and $Z$ block parity-check matrices from the $p \times p$ affine permutation blocks $A(a, b)$ ($v \equiv a u + b \pmod p$) and retain an independent display with canonically minted identifiers |
| **Conditions** | Even block-column count $L \ge 2$, unit slopes $\gcd(a, p) = 1$, and for each block-row pair $(r, s)$ a pair partition of $\{0, \dots, L - 1\}$ into $L/2$ column pairs with matching relative affine maps $A(a^X_{r, c}, b^X_{r, c})\, A(a^Z_{s, c}, b^Z_{s, c})^T$ so that $H_X H_Z^T = 0$ over $\mathbb{F}_2$ (Okada–Kasai, arXiv:2607.14091v4 Thm 4) |
| **Parameter effects** | $n = L \cdot p$ exact, $k = L \cdot p - \mathrm{rank}(H_X) - \mathrm{rank}(H_Z)$ by rank bookkeeping over the retained display; distance hypotheses remain conditional (for CPM-PP, the structural factorial ceiling $d \le (J+1)!$ of Thm 3 is an external bound a consumer may cite, while APM-PP escapes that ceiling; ledger starts at $[0, +\infty)$ per `JUDGMENT_LAYER.md` §2g) |
| **Primitive / derived** | Lower-level expression constructor |
| **Formalization status** | Expression production `pair_partition(p; B_X, B_Z)` admitted 2026-11-22 (`TERM_LANGUAGE.md` §1–§2; `OPERATIONAL_SEMANTICS.md` §2 card, §4.46), `transition-defined`, mechanized in `machine/constructors.py` and `lean/CodeCalculus/` (`Term.lean`, `Constructors.lean`, `Eval.lean`, `ConstructorAssembly.lean`, `ConstructorInstances.lean`) |
| **Partial inverse** | None in general |

---

## 3.8 Named specializations and new families

Pair-partition CPM, GALA, Cornucopia, and related named constructions should initially be represented as specializations of more general typed constructors when possible.

**Note.** arXiv 2607.14091v4 §VII supports this reading from within
the family itself: its APM-PP extension (Thm 4) pairs equal *relative affine
maps* where the CPM construction pairs equal differences, so the general
typed constructor is `L-PAIR-PARTITION` ("pair-partition over relative
permutation maps," §3.7c, admitted 2026-11-22), with CPM-PP and APM-PP as
specializations sharing one CSS-orthogonality proof shape. See PRIOR_ART.md §1
(Okada–Kasai v4 specifics).

A named family deserves its own operation only when it has at least one of the following:

- a distinct input type;
- a distinct state update;
- a distinct CSS-orthogonality proof;
- a distinct parameter theorem;
- a genuinely different quotient, action, or boundary mechanism.

A family name, repository tag, or paper citation alone is not an operation. In
particular, a logical gate on a code (such as a commuting Pauli-rotation family
checked for codespace preservation, [`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md)
§2h) leaves $C = (Q, X, Z, \mathsf{pres}, \mathsf{used})$ unchanged
and has no state update, so **no operation identifier is minted for a logical
gate**; its codespace-preservation and weight-floor judgments belong to the
judgment layer. Likewise, the *family-level* transport statement under the
one-shot hollowed-tensor level map ([`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2j) — the tower-level threshold and amplification claim — is a
conditional rule over QLDPC code families rather than a single-state operation on
$C = (Q, X, Z, \mathsf{pres}, \mathsf{used})$, so **no taxonomy operation
identifier is minted** for that family-level rule. (The single-code map
$\bar\Gamma(C)$ itself is constructor-candidate material and is not evaluated
by any calculus term in this release; identifier allocation for it is left for
another PR.)

---

**Specialization record (rung 3, transition-defined) — `PP-SCALE` (explicit extension of a pair-partition code).** Source: Kasai, *Increasing Quantum LDPC Code Distance through Explicit Extensions*, arXiv submit/8406448 (2026-11-21), read 2026-11-22. This is a specialization of the general *pair equal relative permutation maps* constructor (PRIOR_ART.md §1, Okada–Kasai v4 Thm 4), not a new primitive; it earns a record under §3.8 on four of the five criteria:

- **Distinct input type.** A PP-presented CSS code `C₀` (equivalently a typed PP-parameter bundle `B = (M, Q, (e_j), λ, θ, conventions)` output by the extraction meta-procedure) plus a target size `P ≥ 2`. The bundle is constructor-side data, not part of `C = (Q, X, Z, pres, used)`.
- **Distinct state update.** Construction of a *new* CSS state on `L·P` qubits: `Q'` a fresh namespace (canonically minted, disjoint from `used₀`), `X'/Z'` the rows assembled from `A(a,b)` blocks per (1) with slopes `a_q(P) = ∏_j r_j(P)^{Q_{qj}} (mod P)` (`r_j^{e_j}=1`) and shifts `b(P) = G(P) θ (mod P)` (`G = V C` from the SNF of the shift congruence matrix), `pres'` the generated display, `used'` all minted ids. No mutation of `C₀`.
- **Distinct CSS-orthogonality proof.** The PP conditions (2) at `P`, together with SNF invertibility over the integers, imply `H_X H_Z^T = 0` for every `P ≥ 2` (paper §2.1). This is a different proof shape from the direct-sum or graft orthogonality arguments.
- **Distinct parameter theorem.** The Smith-normal-form parametrization of slopes and shifts with fixed coordinates `θ`, `λ`, `e_j`, and the reproduction check at `P₀` (paper §2.1, (3)–(5), Algorithms 1–2). The construction is total given a valid bundle: no candidate screening by distance.

**Conditions (applicability premises).** (i) `C₀` is PP-presented and all original slopes are units; (ii) the PP conditions (2) hold at `P₀`; (iii) the SNF reproduction check passes ((3) and (5) reproduce the original arrays); (iv) `P ≥ 2`; (v) positive dimension `k = L·P − rank H_X − rank H_Z > 0`, checked separately (the paper states this is not automatic); (vi) generated rows independent as claimed. Absence of a derivation for (v) is part of the semantics (partial big-step), not a failure.

**Parameter effects.** `n' = L·P`; `k' = L·P − rank_X' − rank_Z'` (rank bookkeeping over the retained display); `w' = L` (carries — each natural row has one 1 in each of the $L$ block columns, so row weight is the block-column count $L$); `d_X'`, `d_Z'`, `d'` have no generic formula and are `not yet defined` unless supplied as priced hypotheses; `r'` and Tanner connectivity are recomputed from the generated presentation. No automatic distance cell.

**Judgment cells (per evaluation, scoped).** `w` carries; `n`, `k`, `r`, Tanner connectivity do not carry (recomputed); `d_X`/`d_Z`/`d` are `not yet defined` by default and become `conditional` when a verified interval `[d_lo, d_hi]` is supplied (recorded as a trusted upper/lower bound; the consumer checks input shape, not truth, per the priced-hypothesis boundary). The paper's verified intervals (e.g. `34 ≤ d ≤ 70`) enter as `upper_bound` claims only.

**Family-level structural bound (separate, no operation ID).** The paper's conjecture of a finite, size-independent structural upper bound `B` with improvement toward it as `P` grows is a *conditional family-level rule* over PP-scale families with fixed parameters, analogous to `JUDGMENT_LAYER.md` §2j. Under §3.8, **no taxonomy operation identifier is minted** for it. If admitted, it is recorded as a conditional rule with `B` as a trusted (conjectural) input, scoped as an upper ceiling, with monotonicity explicitly not assumed. Family closure and amplified lower bounds remain `unavailable` (`design/SCOPE.md` §4, issue #541).

**Formalization status.** Transition-defined (rung 3, 2026-11-22): grammar production `pp_scale(e; P)` added to `TERM_LANGUAGE.md` §1–§2; transition card at `OPERATIONAL_SEMANTICS.md` §2; dated hand derivation at `OPERATIONAL_SEMANTICS.md` §4.47 (Kasai §2.1 orthogonality argument in calculus notation, with the `k > 0` premise, canonical minting, and fresh-namespace update explicit); obligation entry `OBL-PP-SCALE` recorded in `OBLIGATIONS.md`; mechanized in `machine/constructors.py` and `lean/CodeCalculus/` (`Term.lean`, `Constructors.lean`, `Eval.lean`, `ConstructorAssembly.lean`, `ConstructorInstances.lean`).

**Partial inverse.** None in general. Recovering `P₀` or the original code from a generated code is not unique (permutation equivalence; the paper notes normalization choices define different families).

**Price-provider boundary.** The extraction meta-procedure (Algorithm 1) is admitted only as a source of constructor parameters, analogous to `A-CONCAT` tower factorization admitted only as a price provider (`design/SCOPE.md`). It is not a term production and not a state transformation; exposing it as a term would require an extended state carrying pair partitions and SNF data, which is not in `C`.

---

# 4. Deferred operations requiring an extended state model

These operations may form new codes, but they cannot be faithfully represented by the initial ordinary-CSS state model.

## 4.1 Gauge fixing

Requires a state containing gauge generators, stabilizer centers, gauge qubits, and a distinction between bare and dressed logical operators. It should not be represented as ordinary `addStab` until those objects are part of the state.

**External support.** Huang et al., *Graphical CSS
Code Transformation Using ZX Calculus*, arXiv 2307.02437v2, reduces gauge fixing
(Prop. 5.2) to *"equivalent to adding $L_g^X$ to $\mathcal{S}_{sub}$"* — and can do
so only **after** its Def. 3.1 has already admitted gauge operators into the
state, as Z-spiders carrying a joint density operator $\rho$ (step (e)) with no
input wire. The reduction follows from having built the extended state, not from
the stabilizer-group bookkeeping, so the sentence above is not only a restriction
this repository chose. Evidence; it changes no status here.

## 4.2 Subsystem-code deformation

Requires subsystem-code states and update rules for gauge groups and stabilizer centers. Distance judgments must distinguish bare and dressed logical distance.

**External support.** Def. 3.1 and
Prop. 5.2 of that paper leave the bare/dressed distinction above load-bearing for a
published transformation, not a refinement: its ⟦15,4,3⟧ intermediate and the
extended Steane code carry **the same stabilizer group**
$\langle F^X, F^Z, H^X, H^Z\rangle$ and differ only in the logical/gauge partition
(its Eq. 7, $\mathcal{L}' = \mathcal{L}_g \cup \mathcal{L}$) and in the physical
gauge state — neither of which has a field in $C = (Q, X, Z, \mathsf{pres}, \mathsf{used})$.
So the Steane ↔ Reed-Muller switch reduces, in this model, to one of two distinct
three-step `C-ADD-CHECK` sequences, after which the switching step has no
expression. This is evidence for the extended-state layer and for the §2.10 Gate 6
prerequisite — the missing field is the same `not yet defined` logical-witness field
— and it discharges nothing.

## 4.3 Symplectic halving and doubling (CSS ↔ general stabilizer)

A matched pair of code-to-code transformations between ordinary CSS codes and
general stabilizer codes, related through the symplectic form. Doubling maps a
general stabilizer code with symplectic check matrix $H = (A \mid B)$ to the CSS
code with $H_X' = (A \mid B)$, $H_Z' = (B \mid A)$ on $2n$ qubits; halving is its
inverse on a CSS parent that admits a fixed-point-free qubit involution $\pi$
exchanging the two sector row spaces ($\pi(S_X) = S_Z$).

Both the doubling input and the halving output live outside the ordinary-CSS
state model, so neither transition can be a CSS-model rule. This is the global,
structured version of the failure mode the disposition identified for
`E-LOCAL-HADAMARD` (§2.12): sector-conjugating moves without a splitting
condition leave the CSS model. The records are therefore deferred to the
extended-state layer, not conditioned into it. The doubling here is distinct
from `A-DOUBLE` (§2.16), which maps a CSS code to a CSS code on $2n$ qubits;
whether the two doubling records factor through one another is an explicit open
question under the §3.8 criteria.

Cross-check: the qLDPC challenge's `[[144,10,16]]` entry in
`a worked example` does not perform a cover — its parent is a published
cover, and the operation applied to it is the abelian mirror construction, an
inversion-based instance of symplectic halving (read at challenge commit
`d5a2a7406f92841ae1129c7db228c4d6eac35892`).

Source: Lee–Okada–Maskara–Kasai–Zhou, arXiv 2609.30069 (§IV, Def. 3; parameter
effects Eq. 20), named 2026-09-29 in the non-CSS extension scoping note.


### Record: `X-SYMPLECTIC-DOUBLE` (symplectic doubling)

| Field | Description |
| --- | --- |
| **Status** | Deferred extended-state operation |
| **Input** | A general stabilizer code on $n$ qubits presented by a symplectic check matrix $H = (A \mid B)$ with $AB^{\mathsf T} + BA^{\mathsf T} = 0$ |
| **Output** | A CSS code on $2n$ qubits with $H_X' = (A \mid B)$ and $H_Z' = (B \mid A)$ |
| **Operation** | Duplicate each qubit; split each mixed check into its $X$-half (on one copy) and $Z$-half (on the other) |
| **Conditions** | The input is a commuting stabilizer code ($AB^{\mathsf T} + BA^{\mathsf T} = 0$); the output is CSS by construction |
| **Parameter effects** | $n' = 2n$, $k' = 2k$, $d \le d' \le 2d$ (candidate effects pending derivation at contract stage) |
| **Primitive / derived** | Candidate primitive of the extended-state layer |
| **Formalization status** | Named 2026-09-29 in the non-CSS extension scoping note; transition not specified |
| **Partial inverse** | `X-SYMPLECTIC-HALVE`; total on doubled outputs, which always admit the copy-swap involution |

### Record: `X-SYMPLECTIC-HALVE` (symplectic halving)

| Field | Description |
| --- | --- |
| **Status** | Deferred extended-state operation |
| **Input** | A CSS code on $2n$ qubits plus typed halving data: a fixed-point-free qubit involution $\pi$ with $\pi(S_X) = S_Z$ (a ZX duality of the parent) |
| **Output** | A general stabilizer code on $n$ qubits with symplectic check matrix $H_{\mathrm{halved}} = (A \mid B)$, where $H_X = (A \mid B)$ and $H_Z = (B \mid A)$ under the pairing induced by $\pi$ |
| **Operation** | Fold each $\pi$-pair of qubits to one qubit; a parent $X$-check's entries on the two members of a pair become the $X$- and $Z$-components of the corresponding folded check |
| **Conditions** | $\pi$ is fixed-point-free and exchanges the sector row spaces; the folded checks commute because parent CSS orthogonality gives $AB^{\mathsf T} + BA^{\mathsf T} = 0$. Existence of such a $\pi$ is a decidable linear-algebra property of the presented CSS state (a candidate future judgment, `not yet defined`), but the output is not representable in the ordinary-CSS model |
| **Parameter effects** | $n' = n_{\mathrm{in}}/2$, $k' = k_{\mathrm{in}}/2$, $\lceil d_{\mathrm{in}}/2 \rceil \le d' \le d_{\mathrm{in}}$; encoding rate preserved; supplied check weights never increase (candidate effects pending derivation at contract stage) |
| **Primitive / derived** | Candidate primitive of the extended-state layer |
| **Formalization status** | Named 2026-09-29 in the non-CSS extension scoping note; transition not specified |
| **Partial inverse** | `X-SYMPLECTIC-DOUBLE` (applicable to every halved output) |

## 4.4 Local/block-Clifford conjugation and normalization

### Record: `X-LOCAL-CLIFFORD`

| Field | Description |
| --- | --- |
| **Status** | Deferred extended-state operation |
| **Input** | A general stabilizer (or CSS) code plus a Clifford conjugation: a qubit permutation optionally composed with single-qubit or block Cliffords |
| **Output** | A code in the same state model as the input, or, for a CSS input, a general stabilizer code when the conjugation does not preserve the pure-sector form |
| **Operation** | Conjugate every stabilizer generator and logical representative by the supplied Clifford; transport the state's presentation along the resulting Pauli map |
| **Conditions** | The supplied Clifford must be typed (support, sector action, and any block structure). For a CSS input to remain CSS, each displayed generator must map to a pure $X$ or pure $Z$ operator; otherwise the result leaves the ordinary-CSS model. Whether this purity condition holds is checkable per presented state — the phase-insensitive model represents at most the per-qubit sector swap here, see §2.12's disposition |
| **Parameter effects** | $n$ and $k$ are preserved by any Clifford conjugation. The Pauli distance is preserved when the Clifford is a qubit permutation or single-qubit Clifford (block size $b=1$); for a block Clifford of block size $b>1$, $\lceil d/b \rceil \le d' \le b\,d$, with the maximum stabilizer weight moving within the same factor. Sector distances $d_X, d_Z$ are not defined for a non-CSS output. (Conditional on the Clifford type; no unconditional distance formula.) |
| **Primitive / derived** | A **presentation operation** of the extended-state / presentation layer (§7: a conjugation that preserves the code up to the chosen equivalence). The `X-` prefix marks this deferral type: the move leaves the ordinary-CSS state model in general, so it joins the extended-state layer rather than the CSS one. The CSS-preserving single-qubit instance (sector swap) is already `E-LOCAL-HADAMARD` |
| **Formalization status** | Named 2026-10-23 from the qLDPC challenge's Clifford-image provenance discipline: the `provenance.clifford_relabel_of` field (with the `clifford_block_size` companion) of the challenge's `schema/code.schema.json`, whose schema text records that such an image has the same $n$, $k$, and code space as its parent, that the verifier tests only the single-qubit case (`is_css_up_to_local_clifford`, in `verify/qldpc_verify.py`; the schema description names it), and that multi-qubit Clifford equivalence is not tested. Read at challenge commit `d5a2a7406f92841ae1129c7db228c4d6eac35892`; transition not specified |
| **Partial inverse** | The inverse Clifford conjugation, with the same typed data |

This record does not make arbitrary local Clifford conjugation a CSS-model
move. The challenge's own schema directs a code that is CSS up to local
Clifford to its CSS image, because the image carries the same information:
which sector-conjugating single-qubit deformations stay inside the model is
the disposition §2.12 already fixes, and this record does not re-derive it.
Block Cliffords and shears that do not preserve purity are deferred with the
rest of the extended-state layer. The record exists so the deferral is
explicit rather than implicit.

**Prior art (2026-11-09).** Wang & Krastanov, *Local Clifford equivalence to
CSS codes: Polynomial-time classification and conversion*, arXiv 2610.28737
(2026), gives a deterministic polynomial-time algorithm that decides whether
an arbitrary stabilizer code is locally Clifford-equivalent to a CSS code and
constructs the required single-qubit Clifford and CSS checks when it is,
preserving parameters and check sparsity for qLDPC codes; for graph states it
gives a bipartite-graph criterion in the local-complementation orbit. This is
the CSS-recovery instance of this record's single-qubit case: it supplies the
missing decision procedure and construction that the record previously left as
"transition not specified", without changing the extended-state-layer status of
general block-Clifford conjugation. It is evidence for the record, not a
discharge of any obligation.

## 4.5 Dressed quotient (extended-state constructor candidate)

### Record: `X-DRESSED-QUOTIENT`

| Field | Description |
| --- | --- |
| **Status** | Candidate extended-state constructor (not admitted; no taxonomy ID promotion, no grammar production) |
| **Input** | A parent Pauli stabilizer code together with a higher-form or cup-polynomial symmetry background (a class in $H^{q+1}(F;A)$ or a cup-polynomial defect) and, when applicable, a finite trivializing cover of the background |
| **Output** | A commuting-projector code (in general not a Pauli stabilizer code) on the quotient, possibly with non-abelian topological order such as $D(D_4)$ |
| **Operation** | The twist is an entangling diagonal circuit (CZ-type for quadratic defects, CCZ-type for cubic and higher); when a finite cover trivializes the background the code is a *dressed quotient* of the parent, with dressed Gauss laws replacing the parent's checks |
| **Conditions** | The parent must be a Pauli stabilizer code (or commuting-projector code for the non-trivializing-cover case); the background class / cup polynomial and the (optional) trivializing cover must be typed; the dressed Gauss laws must define a code (commutation of the dressed checks) |
| **Parameter effects** | Dressings have Clifford level at most one less than the degree of the twist; for cubic twists the code dimension is a count of solutions of quadratic equations in cup products (certifies the code is not a Pauli stabilizer code when the count is not a power of two); on tori and slabs the distance is linear in the size. General parameter formulas are constructor-specific and not yet stated |
| **Primitive / derived** | Constructor (extended-state layer) |
| **Formalization status** | Candidate record added 2026-11-09 from prior art (Hsin, arXiv 2611.09538v1; `PRIOR_ART.md`). No transition, no grammar production, no contract-index row beyond this record. Gate 6 admission of the extended-state layer precedes any promotion |
| **Partial inverse** | None stated; a cover/lift reconstruction would require retained background and cover data |

**Why it is a candidate rather than an alias.** Under [`spec/TAXONOMY.md`](TAXONOMY.md) §3.8 a named family earns its own record with a distinct input type, state update, CSS-orthogonality proof, parameter theorem, or quotient/action/boundary mechanism. The dressed quotient has all five: input type (parent + background class / cup polynomial + trivializing cover), state update (dressed Gauss laws in place of the parent's checks, producing a non-CSS commuting-projector code), orthogonality proof (the dressed Gauss laws), parameter theorem (point count of cup-product solutions; Clifford-level bound), and a quotient mechanism distinct from the monomial quotient (entangling-circuit dressing rather than a monomial-Clifford action). It is not representable in $C = (Q, X, Z, \mathsf{pres}, \mathsf{used})$ and therefore cannot be a CSS-level move; it joins the extended-state layer alongside `X-SYMPLECTIC-DOUBLE`/`HALVE` and `X-LOCAL-CLIFFORD`. Its flat/monomial counterpart is the specialization of `A-QUOTIENT` recorded in `ROADMAP.md` (*Candidate specialization recorded from prior art*, 2026-11-09).

## 4.6 Weight reduction to subsystem codes

### Record: `X-WEIGHT-REDUCTION`

| Field | Description |
| --- | --- |
| **Status** | Deferred extended-state operation (candidate; no taxonomy promotion beyond this record) |
| **Input** | A stabilizer code (CSS or general) plus an embedding of its Tanner graph into a target graph |
| **Output** | A subsystem code whose checks are 3-local (weight at most 3), with related parameters |
| **Operation** | Reduce check weights by introducing gauge qubits / gauge operators via layer codes, so that the resulting code is a subsystem code on the embedded graph |
| **Conditions** | The Tanner-graph embedding and the layer-code data must be typed; the result is a subsystem code, so gauge and stabilizer centers must be tracked (extended state) |
| **Parameter effects** | $n$ may grow by the embedding/layer overhead; check weight drops to at most 3; distance and rate are related to the input's but not preserved exactly — constructor-specific hypotheses required |
| **Primitive / derived** | Candidate transformation of the extended-state layer (produces a subsystem code from a stabilizer code) |
| **Formalization status** | Candidate record added 2026-11-09 from prior art (Yuan, Baspin & Williamson, *Quantum Weight Reduction with Layer Codes*, arXiv 2603.04883 (2026); Hastings, arXiv 2102.10030; arXiv 2410.10194). No transition, no grammar production. Requires the subsystem/gauge state model of §4.1/§4.2; Gate 6 admission of the extended-state layer precedes any promotion |
| **Partial inverse** | None stated; recovering the input stabilizer code would require un-gauging the introduced gauge operators |

**Why it is a candidate rather than an alias.** Under `spec/TAXONOMY.md` §3.8 a named operation earns its own record with a distinct input type, state update, orthogonality proof, parameter theorem, or quotient/action/boundary mechanism. Weight reduction has a distinct output type (subsystem code vs. stabilizer code), a distinct state update (gauge operators are introduced), and distinct parameter behaviour (weight drops to 3 at the cost of block-length overhead). It is not representable in $C = (Q, X, Z, \mathsf{pres}, \mathsf{used})$ because gauge groups and stabilizer centers have no field there, so it joins the extended-state layer alongside `X-GAUGE-FIX` and `X-SUBSYSTEM`. It is not a CSS-model move and is not an instance of `C-ADD-CHECK`.

## 4.7 Gauging and logical measurement by gauging

### Record: `X-GAUGING`

| Field | Description |
| --- | --- |
| **Status** | Deferred extended-state operation |
| **Input** | A CSS parent code, typed symmetry data (a Clifford or finite-order symmetry factoring into operations on disjoint matter blocks of bounded size), a connected gauging graph \(G=(V,E)\) on those blocks, and (for Clifford symmetries) completion data: central checks \(\mathsf K_a\), an order on noncommuting pairs, and one completion qubit per conflicting pair |
| **Output** | A gauged stabilizer code on matter, gauge, and completion qubits, whose checks are the completed Gauss operators, flux operators, modified parent stabilizers, central checks, and pinning checks; together with the data needed for ungauging (gauge qubit \(Z\)-basis readout and a vertex correction). The output is not, in general, an ordinary CSS code: modified parent stabilizers and completion factors are mixed/Clifford checks |
| **Operation** | Gauge a symmetry of the parent code: introduce gauge qubits on the edges of \(G\), modify the parent stabilizers along chosen paths, and (for Clifford symmetries) add completion qubits so the raw checks commute. Ungauging measures the gauge qubits and applies a vertex correction to return to the parent code space |
| **Conditions** | The symmetry must preserve the parent code space and factor into block operations of bounded size; the gauging graph must be connected and its paths chosen for the modified parent stabilizers; raw checks must satisfy the commutator relation \(C_i C_j = \mathsf K_{ij} C_j C_i\) with \(\mathsf K_{ij}\in\langle \mathsf K_a\rangle\); completion qubits are pinned in their \(+\) eigenspace on the code space; the resulting full family must be mutually commuting; the output code space and distance must be preserved as stated under the construction hypotheses. The construction also supplies bounded-depth extraction circuits and detection tests for repeated rounds |
| **Parameter effects** | \(n_{\text{gauged}} = n + |E(G)| + c\) with \(c\) completion qubits; \(n_{\text{meas}} = M_{\text{raw}} + c\) measurement ancillas. Each conflict adds one completion qubit and one pinning-check ancilla. Completion preserves the LDPC property with bounded weight and incidence when the raw family has them. The code-space projection satisfies \(d(\widehat P_g)=d(P_g)\) under the construction's hypotheses (conditional; not an automatic calculus judgment). Clifford raw checks can be measured at level three or below after completion; qudit variants give hierarchy bounds in prime dimensions. The construction is also used for logical measurement of the symmetry with circuit fault distance \(\Omega(d)\) in \(O(d)\) rounds under the stated graph and circuit conditions |
| **Primitive / derived** | Candidate extended-state constructor / transformation; not a CSS-model move. It is not a measurement procedure in the calculus's sense, but its code construction is recorded here so the deferral is explicit |
| **Formalization status** | Taxonomy-only. Source: Wang, *Commuting-check gauging for fault-tolerant logical measurements*, arXiv:2611.12236v1 (2026). No grammar production, no typed transition, no obligation, and no claim status beyond this record. Circuit realizations, extraction schedules, gate orders, and fault-response certificates have no field in \(C=(Q,X,Z,\mathsf{pres},\mathsf{used})\) and remain not yet defined here |
| **Partial inverse** | Ungauging returns to the parent code space under the construction's readout and correction data; generally requires retained graph, path, completion, and measurement data |

This record does not make gauging a calculus operation. The parent is CSS, but the gauged output leaves the ordinary-CSS model, so it joins the deferred extended-state layer alongside `X-GAUGE-FIX`. The paper's fault-tolerance and circuit-distance statements are evidence about the construction, not proofs of calculus claims, and they do not enter the judgment layer without a Gate 6 admission decision and supplied hypotheses. Circuit-level content is a non-goal of the first phase and is recorded here only as scope context.

---

# Gate 7 constructor signatures

The fifteen Gate 7 candidate constructors (`A-PRODUCT`, `A-CONCAT`,
`A-DOUBLE`, `A-QUOTIENT`, `L-HGP`, `L-LIFTED`, `L-NESTED-CSS`, `L-TILE`,
`L-TANNER`, `L-BALANCED`, `L-GROUP-ALGEBRA`, `X-SYMPLECTIC-DOUBLE`,
`X-SYMPLECTIC-HALVE`, `X-SUBSYSTEM`, `X-GAUGE-FIX`) are recorded in the taxonomy: each states the typed objects it consumes, the obligations it
incurs, and whether its inputs are constructive or axiomatic. `X-LOCAL-CLIFFORD`
is excluded because it is not constructor-shaped.

The signature record itself admitted no constructor; ten of the fifteen
(`L-HGP`, `L-LIFTED`, `L-GROUP-ALGEBRA`, `A-CONCAT`, `L-BALANCED`, `L-TANNER`,
`L-TILE`, `A-PRODUCT`, `A-DOUBLE`, `L-NESTED-CSS`) were subsequently admitted
at rung 3 (`transition-defined`) in 2026-11-11/13 (
[`CLAIMS.md`](CLAIMS.md)), while the remaining five stay at rung 1
(`taxonomy-only`). Promotion above rung 1 remains maintainer work.

# 5. Operation dependencies

The following dependency structure summarizes the intended calculus growth:

```text
qubit relabeling ───────────────┐
 ├── presentation equivalence
 generator rebasing ────────────┘
 │
 v
 delete_check ───────┐
 add_check ──────────┼── sequential composition ── deformation chains
 direct_sum ─────────┘
 │
 v
 peel / puncture / graft / merge / split
 │
 v
 typed algebraic and geometric constructors
 │
 v
 gauge and subsystem extensions
```

Lower-level constructors form a parallel input branch:

```text
classical codes ───────┐
matrices / algebras ───┼──> lower-level CSS constructors ──> CSS-code state
graphs / cellulations ─┘
```

The two branches should not be silently identified. A lower-level constructor may output a CSS code that is subsequently transformed by the code-level calculus, but its input type and proof obligations are different.

---

# 6. Current status relative to the proposal

| Operation family | Current proposal status |
| --- | --- |
| `skip` | Initial syntax |
| Direct sum | Initial state expression and judgments |
| Check deletion | Initial primitive and proof gate |
| Check addition | Initial primitive and proof gate |
| Sequential composition | Initial syntax and proof obligations |
| Qubit relabeling | Required infrastructure for equivalence |
| Generator rebasing | Admitted as a conditional extension 2026-10-23 (`P-REBASE`); `OBL-REBASE-GENERATION` discharged (§4.26) |
| Qubit/check peeling | Admitted conditional extension 2026-10-23; transition defined (§2.6), soundness discharged (§4.32) |
| Row-space grafting | In-scope conditional extension (`E-GRAFT`); transition soundness proved (§4.12) |
| Puncturing | Admitted conditional extension 2026-10-23; transition defined (§2.8), soundness discharged (§4.32) |
| Qubit/check extension | Admitted conditional extension 2026-10-23; transition defined (§2.9), soundness discharged (§4.32) |
| Merge/glue/split | `E-GLUE` admitted conditional extension 2026-10-23, evaluator transition 2026-10-27 (§4.31), logical-witness and boundary/edge-label fields defined (`STATE_MODEL.md` §1/§1a), `transition-defined` (2026-11-11); `E-SPLIT` remains an unadmitted candidate extension |
| Local Hadamard (per-qubit sector swap) | Conditional extension admitted 2026-10-23; the **$T=Q$ instance has a typed transition** (§2.12: the sector exchange of the whole display); the general split-subset instance's conditions require both row spaces to split along the conjugated qubits and its row-wise conjugation mechanics are **not** specified |
| Duplication ("double it") | Later algebraic branch; factorization question open (`A-CONCAT` vs. cover/lift vs. duality-assisted) |
| Tensor, homological product, concatenation | Algebraic branch |
| Mapping cone and quotient/subspace operations | Algebraic branch |
| HGP, lifted, balanced, group-algebra, Tanner, tile constructors | Later lower-level constructor layer |
| Gauge fixing and subsystem operations | Deferred state-model extension |
| Local/block-Clifford conjugation | Deferred extended-state presentation operation, named 2026-10-23 (§4.4); anchored on the challenge's `provenance.clifford_relabel_of` schema field; the CSS-preserving instance is the per-qubit sector swap, §2.12; transition not specified |
| Symplectic halving/doubling (CSS ↔ general stabilizer) | Deferred extended-state pair, named 2026-09-29 (§4.3); distinct from `A-DOUBLE`; factorization question open |

The initial calculus does not need to implement every taxonomy entry. Its first success condition is that the distinction between these layers is precise and that each future operation has a well-defined place, input type, and proof obligation.

---

# 7. Vocabulary rules

- Use **composition** for combining code states or structured ingredients into a code, but always state which input level is meant.
- Use **deformation** for a transformation whose primary input is an existing CSS-code state.
- Use **constructor** for an operation that forms a CSS code from lower-level objects.
- Use **presentation operation** for a change that preserves the underlying stabilizer code up to the chosen equivalence.
- Use **derived operation** when a named move factors into already-defined operations.
- Do not treat a family tag, database import, search method, or citation as an operation without a state transformation.
- Do not assert a parameter formula without its hypotheses.
- Do not treat raw qubit-column deletion as a valid CSS puncture without an orthogonality condition or an induced stabilizer update.
