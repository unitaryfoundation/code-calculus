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
| `E-GLUE` | Interface gluing / merge | Conditional CSS extension admitted 2026-10-23; binary-only expression constructor `glue(e₁, e₂; seams)` (`TERM_LANGUAGE.md` §1–§2, decided 2026-11-18; no unary command production); evaluator transition (§4.31) and interval soundness (§4.32) discharged; future-$\Pi$ fields defined (`STATE_MODEL.md` §1a); CSS-level algebra of §4.31/§4.33 mechanized (`GlueExtraction.lean`) with geometric move-word gap recorded; `contract-stated` (rung 5, 2026-11-18) |
| `E-SPLIT` | Split (separating deletion) | Conditional CSS extension admitted 2026-11-25 (maintainer decision, issue #546): separating deletion command `split(Q_A; R)` over a cut $(Q_A, R)$ (`TERM_LANGUAGE.md` §1–§2; `OPERATIONAL_SEMANTICS.md` §2, §4.48), derived over `C-DELETE-CHECK`, `transition-defined`, meeting `VERSIONING.md` §4.2; two-state projection refused |
| `E-LOCAL-HADAMARD` | Local Hadamard (per-qubit sector swap) | Conditional CSS extension admitted 2026-10-23; transition defined 2026-10-23 for the $T=Q$ instance and 2026-11-26 for the split-subset instance under the row-space splitting guard (§4.27); soundness discharged (§4.32), conditional on hypotheses |
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
| `L-BRUHAT` | CSS codes from the Bruhat order of a Coxeter group | Lower-level constructor candidate (taxonomy-only, rung 1); distinct input type (Coxeter group + Bruhat interval) and chain complex from the Bruhat face poset; prior art Brádler, arXiv 2603.16036 (2026); see §3.8 candidate record (2026-11-26) |
| `L-MONOMIAL` | Divisible decreasing monomial codes (monomial/Reed-Muller codes punctured at a downward-closed set on the Boolean hypercube) | Lower-level constructor candidate (taxonomy-only, rung 1); distinct input type and a closed-form distance parameter theorem; prior art Wills, arXiv 2608.24000 (2026); see §3.8 candidate record (2026-11-26) |
| `L-BOOTSTRAP` | Quantum bootstrap product (codes from the bootstrap equation / fork complexes) | Lower-level constructor candidate (taxonomy-only, rung 1); distinct consistency-condition input and fork-complex output; generalizes HGP and fracton codes; prior art Li, arXiv 2601.22363 (2026); see §3.8 candidate record (2026-11-26) |
| `X-EAQLRC` | Entanglement-assisted locally recoverable codes (CSS-like construction without the dual-containing condition) | Extended state model (candidate; prior art, arXiv 2607.27091 (2026)); uses pre-shared entanglement, so not representable in ordinary CSS state model; see §4 candidate record (2026-11-26) |
| `X-GAUGE-FIX` | Gauge fixing | Extended state model |
| `X-GAUGING` | Gauging / logical measurement by gauging | Extended state model (deferred) |
| `X-LOCAL-CLIFFORD` | Local/block-Clifford conjugation | Extended state model (deferred) |
| `X-SUBSYSTEM` | Subsystem-code deformation | Extended state model |
| `X-SYMPLECTIC-DOUBLE` | Symplectic doubling (general stabilizer → CSS) | Extended state model (deferred) |
| `X-SYMPLECTIC-HALVE` | Symplectic halving (CSS → general stabilizer) | Extended state model (deferred) |
| `X-DRESSED-QUOTIENT` | Dressed quotient (parent Pauli code + higher-form/cup-polynomial background + trivializing cover → commuting-projector code) | Extended state model (candidate; prior art Hsin, arXiv 2611.09538v1) |
| `X-WEIGHT-REDUCTION` | Weight reduction to subsystem codes | Extended state model (candidate; §4.6) |

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
| **Conditions** | $q$ must occur in exactly one displayed generator of the selected type; the resulting restricted checks must remain CSS-orthogonal (the admitted transition at `OPERATIONAL_SEMANTICS.md` §4.28 reads the displayed rows only and updates no interface or support-ownership context field) |
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

**Specialization note (2026-11-26, prior art Reddy & Kashyap, arXiv 2608.19094).**
The *appending construction* for logical diagonal gates — take an `[[n',k']]` CSS
code $Q'$ and a target logical $Z$-rotation, extend $Q'$ by appending $n''$
physical qubits to obtain an `[[n,k]]` CSS code with $n=n'+n''$, $k=k'$, realizing
the target gate by a transversal physical $Z$-rotation on the appended qubits, with
controllable distance loss — is a **specialization of `E-EXTEND`** (row-added
extension) with a specific choice of added rows and a gate-realization hypothesis.
The state update (add a qubit set $\Delta$ disjoint from $Q$ and an ordered list
of well-typed, canonically-minted check rows over $Q\cup\Delta$) is exactly
`E-EXTEND`; the logical-gate content is outside the object language (§1 circuit
exclusion, `design/SCOPE.md` §4) and stays a hypothesis. No new taxonomy ID is
minted. The distance-loss control enters as the `E-EXTEND` distance-loss conditional cell (`JUDGMENT_LAYER.md` §2a; `OPERATIONAL_SEMANTICS.md` §4.30, *Distance-loss cell*): a supplied, sourced loss $\ell_\tau$ gives the lower endpoint $\max(0, L_\tau-\ell_\tau)$, and the consumer checks its shape, not its truth.

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
| **Partial inverse** | `E-SPLIT` (separating deletion with cut $(Q_A, R_{\mathrm{seam}})$ where $R_{\mathrm{seam}}$ is the set of minted seam identifiers, §2.11, `OPERATIONAL_SEMANTICS.md` §4.48): restores the qubits and displayed rows of $C_A \oplus C_B$ in order, with $\mathsf{used}$ grown by $R_{\mathrm{seam}}$ (batch form of the add-then-delete law, §4.9) |

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
`CLAIMS.md`), remaining a Gate 6 conditional cell.

## 2.11 Split

| Field | Description |
| --- | --- |
| **Status** | Admitted conditional extension (2026-11-25, maintainer decision, issue #546; separating deletion admitted, two-state projection refused) |
| **Input** | A presented CSS state $C$ and a cut $(Q_A, R)$: a qubit block $Q_A \subseteq Q$ and an explicit finite set $R$ of displayed generator identifiers |
| **Output** | A single presented CSS state $C'$ on the same qubit namespace $Q' = Q$, separated at $Q_A$ (the "code with exposed interfaces" reading; the two-state projection reading is refused — see below) |
| **Operation** | Delete every displayed row whose identifier lies in $R$, retaining all other displayed rows in order; retire the identifiers in $R$ in $\mathsf{used}$ (nothing minted) |
| **Conditions** | (1) $Q_A \subseteq Q$; (2) every identifier in $R$ is displayed in $C$ (`DisplayedGenerator(r, pres)`); (3) every displayed row of $C$ that crosses $(Q_A, Q \setminus Q_A)$ (its support meets both $Q_A$ and $Q \setminus Q_A$) has its identifier in $R$. $R$ may include additional non-crossing displayed rows (e.g. intra-factor `E-GLUE` seam checks). Duplicate qubit labels in $Q_A$ or duplicate identifiers in $R$ are malformed; failure of (1)–(3) is inapplicable (`no_derivation`) |
| **Parameter effects** | $n' = n$; $k' = k + t = k(C'\vert_A) + k(C'\vert_B)$ with $t = |R|$; $w' \le w$; $r' \le r$ with layout unchanged and honesty preserved; $\kappa'$ recomputed ($\kappa' \ge 2$ whenever both $Q_A$ and $Q \setminus Q_A$ are nonempty); $C'$ separated at $Q_A$. Distances: non-increase $d_\sigma(C') \le d_\sigma(C)$ and $d(C') \le d(C)$ (`proved`); exact unpriced distances `unavailable`; exact block-minimum identity $d_\sigma(C') = \min(d_\sigma(C'\vert_A), d_\sigma(C'\vert_B))$ and price decomposition $d_\sigma(C') = \min(d_\sigma(C), w_{\mathrm{del},\sigma}, w_{\mathrm{exp},\sigma})$ (`proved`, §4.48), giving the conditional priced cell on supplied restriction-display intervals (`JUDGMENT_LAYER.md` §2a, §2f). Minimum deletions over all displays of sector $\sigma$ is the row-space cut rank $c_\sigma = \operatorname{rank}(S_\sigma\vert_A) + \operatorname{rank}(S_\sigma\vert_B) - \operatorname{rank}(S_\sigma)$, attained after `P-REBASE` |
| **Primitive / derived** | Derived command over `C-DELETE-CHECK` and `C-SEQUENCE` (`OBL-DERIVED-TERM-FACTORIZATION`), with admitted command production $\mathrm{split}_{Q_A; R}$ (`TERM_LANGUAGE.md` §1–§2) |
| **Formalization status** | Transition defined 2026-11-25 (`TERM_LANGUAGE.md` §1–§2; `OPERATIONAL_SEMANTICS.md` §2, §4.48; `JUDGMENT_LAYER.md` §2a–§2c, §2d.5, §2f, §4; `CLAIMS.md` `transition-defined`), meeting `VERSIONING.md` §4.2 at patch level on `stdCSS-3`; mechanized in `lean/CodeCalculus/SplitCommand.lean` (plus `Term.lean`, `Eval.lean`, `Soundness.lean`, `ExpandedSoundness.lean`, `Gate6Soundness.lean`, `Gate6Exact.lean`) |
| **Partial inverse** | `E-GLUE` on a glued state (deleting the minted seam identifiers $R_{\mathrm{seam}}$ restores the qubits and rows of $C_A \oplus C_B$ with $\mathsf{used}$ grown by $R_{\mathrm{seam}}$), and in the other direction re-adding the deleted supports by `C-ADD-CHECK` restores both row spaces with fresh canonical identifiers and grown `used` (§4.48, batch form of §4.9) |

**Projection refused (2026-11-25, maintainer decision, issue #546).** The
alternative reading of the output — returning the two restriction displays
$C'|_A$ and $C'|_B$ as separate states — is refused: `Eval` returns one state
(returning two states would be a production of a new form, a shape change
under `VERSIONING.md` §4.1 that is never folded), no
kernel rule removes qubits while preserving block distance, and `used` has no
canonical partition because retired identifiers have no row and therefore belong
to neither block. Restriction displays are used only as the mathematical
objects whose distances the conditional priced cell takes as hypotheses.

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
| **Parameter effects** | $n' = n$, $k' = k$, $d' = d$. The full-qubit instance (global $X \leftrightarrow Z$ sector duality) exchanges the sector distances exactly, $d_X' = d_Z$ and $d_Z' = d_X$. A split subset $T$ exchanges them only on the factor code $C_T$: $d_X' = \min(d_Z(C_T), d_X(C_{Q\setminus T}))$ and $d_Z' = \min(d_X(C_T), d_Z(C_{Q\setminus T}))$, so each sector distance is at least $d$ (`OPERATIONAL_SEMANTICS.md` §4.27) |
| **Primitive / derived** | Candidate primitive |
| **Formalization status** | The **$T=Q$ instance — the global sector duality** — has a typed transition (`TERM_LANGUAGE.md` §2; `OPERATIONAL_SEMANTICS.md` §2, §4.27), admitted 2026-10-23 as a conditional cell under the Gate 6 decision (`JUDGMENT_LAYER.md` §2f). The **split-subset instance** $\varnothing\subsetneq T\subsetneq Q$ has a typed transition under the decidable splitting guard above, read along $T$. A mixed row is re-presented by a deterministic canonical update that uses the canonical mint (`OPERATIONAL_SEMANTICS.md` §2 `E-LOCAL-HADAMARD` card, §4.27(b)). Sound admission discharged (`OBL-GATE6-CSS-EXTENSIONS`, §4.32) |
| **Partial inverse** | Itself, with the same $T$. The $T=Q$ instance is involutive on labeled states. A split subset restores both row spaces, and restores the labeled state when the display has no mixed row (§4.27(b)) |

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
 - **The repair is not an admission.** Choosing it discharges no obligation.
 The CSS tensor product instance is admitted as `A-PRODUCT`, with output
 well-formedness proved
 ([`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4.35). Gate 7
 ([`GATES.md`](GATES.md) §10, ratified 2026-11-26) keeps typed inputs as
 production arguments.
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
- **Admission status.** The CSS tensor product instance of this record has the
 production `product(e_A, e_B)` under the stable identifier `A-PRODUCT`
 (`OPERATIONAL_SEMANTICS.md` §2 card, §4.35), `transition-defined`; the
 related families `L-HGP` (canonical HGP amplifiers) and `A-DOUBLE`
 (duplication) are `transition-defined` too ([`CLAIMS.md`](CLAIMS.md),
 *Initial contract index*). Product structures other than the CSS tensor
 product have no production.
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

**Refused input extension — non-CSS / symplectic inner inputs (decided
2026-11-25, issue #573).** By dated maintainer decision (MathysRennela,
2026-11-25), finite symplectic inner-matrix inputs for `A-CONCAT` are
**refused**, and the **Input** row above reads onto `stdCSS` CSS states only.
Three qLDPC board entries concatenate a CSS outer with a non-CSS stabilizer
inner (`codes/512-54-24.json`, `codes/576-42-24.json`, `codes/672-28-30.json`,
added 2026-10-14; read at challenge commit `6e1e41be3`). Neither the inner
input nor the composite is representable in
$C = (Q, X, Z, \mathsf{pres}, \mathsf{used})$: each of the three composites is
a non-CSS stabilizer code (`code_type: "stabilizer"`) whose stabilizer group is
not generated by its X-type and Z-type elements (corrected 2026-11-24;
`design/A_CONCAT_SYMPLECTIC_INNER_PROPOSAL.md` §2 in the development
repository). Any CSS-composite guard refuses all three entries, and a CSS
composite forces a CSS group on every block, so without outer stabilizers
confined to a block the inner code is already CSS. Those instances sit below
the CSS layer and require a non-CSS stabilizer state sort, which the 2026-11-18
decision on issue #545 refused. This scope qualification stays inline so the
**Input** row is read onto CSS states only.

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
| **Formalization status** | Expression production `lift_G(A, B)` admitted 2026-11-11 for finite abelian groups (`TERM_LANGUAGE.md` §2; `OPERATIONAL_SEMANTICS.md` §2 card, §4.34) and generalized 2026-11-22 to finite nonabelian groups via explicit multiplication-table or permutation-generator presentations with commuting left/right regular representations $L(x), R(y)$ and antipode involution $g \mapsto g^{-1}$ (§4.44), `transition-defined`; optional subgroup argument for the coset lift (non-normal $H \le G$, $B$ over $\mathbb{F}_2[N_G(H)]$) admitted 2026-11-26 (§4.49) |
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
gate**; its codespace-preservation, frame-reading, and weight-floor judgments belong to the
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
- **Distinct state update.** Construction of a *new* CSS state on `L·P` qubits: `Q'` a fresh namespace `{0, ..., L·P - 1}`, `X'/Z'` the rows assembled from `A(a,b)` blocks per (1) with slopes `a_q(P) = ∏_j r_j(P)^{Q_{qj}} (mod P)` (`r_j^{e_j}=1`) and shifts `b(P) = G(P) θ (mod P)` (`G = V C` from the SNF of the shift congruence matrix), `pres'` the generated display with identifiers canonically minted starting from `used₀`, `used'` the union of `used₀` with the newly minted ids. No mutation of `C₀`.
- **Distinct CSS-orthogonality proof.** The PP conditions (2) at `P`, together with SNF invertibility over the integers, imply `H_X H_Z^T = 0` for every `P ≥ 2` (paper §2.1). This is a different proof shape from the direct-sum or graft orthogonality arguments.
- **Distinct parameter theorem.** The Smith-normal-form parametrization of slopes and shifts with fixed coordinates `θ`, `λ`, `e_j`, and the reproduction check at `P₀` (paper §2.1, (3)–(5), Algorithms 1–2). The construction is total given a valid bundle: no candidate screening by distance.

**Conditions (applicability premises).** (i) `C₀` is PP-presented and all original slopes are units; (ii) the PP conditions (2) hold at `P₀`; (iii) the SNF reproduction check passes ((3) and (5) reproduce the original arrays); (iv) `P ≥ 2`; (v) positive dimension `k = L·P − rank H_X − rank H_Z > 0`, checked separately (the paper states this is not automatic); (vi) generated rows independent as claimed. Absence of a derivation for (v) is part of the semantics (partial big-step), not a failure.

**Parameter effects.** `n' = L·P`; `k' = L·P − rank_X' − rank_Z'` (rank bookkeeping over the retained display); `w' = L` (carries — each natural row has one 1 in each of the $L$ block columns, so row weight is the block-column count $L$); `d_X'`, `d_Z'`, `d'` have no generic formula and are `unavailable` automatically unless supplied as priced hypotheses; `r'` and Tanner connectivity are recomputed from the generated presentation. No automatic distance cell.

**Judgment cells (per evaluation, scoped).** `w` carries; `n`, `k`, `r`, Tanner connectivity do not carry (recomputed); `d_X`/`d_Z`/`d` are `unavailable` automatically and become `conditional` when a supplied interval `[d_lo, d_hi]` is recorded as a priced hypothesis (consumer checks input shape, not truth, per the priced-hypothesis boundary; upper endpoints enter as `upper-bound` claims only).

**Family-level structural bound (separate, no operation ID).** The paper's conjecture of a finite, size-independent structural upper bound `B` with improvement toward it as `P` grows is a *conditional family-level rule* over PP-scale families with fixed parameters, analogous to `JUDGMENT_LAYER.md` §2j. Under §3.8, **no taxonomy operation identifier is minted** for it. If admitted, it is recorded as a conditional rule with `B` as a trusted (conjectural) input, scoped as an upper ceiling, with monotonicity explicitly not assumed. Family closure and amplified lower bounds remain `unavailable` (`design/SCOPE.md` §4).

**Formalization status.** Transition-defined (rung 3, 2026-11-22): grammar production `pp_scale(e; P)` added to `TERM_LANGUAGE.md` §1–§2; transition card at `OPERATIONAL_SEMANTICS.md` §2; dated hand derivation at `OPERATIONAL_SEMANTICS.md` §4.47 (Kasai §2.1 orthogonality argument in calculus notation, with the `k > 0` premise, canonical minting, and fresh-namespace update explicit); obligation entry `OBL-PP-SCALE` recorded in `OBLIGATIONS.md`; mechanized in `machine/constructors.py` and `lean/CodeCalculus/` (`Term.lean`, `Constructors.lean`, `Eval.lean`, `ConstructorAssembly.lean`, `ConstructorInstances.lean`).

**Partial inverse.** None in general. Recovering `P₀` or the original code from a generated code is not unique (permutation equivalence; the paper notes normalization choices define different families).

**Price-provider boundary.** The extraction meta-procedure (Algorithm 1) is admitted only as a source of constructor parameters, analogous to `A-CONCAT` tower factorization admitted only as a price provider (`design/SCOPE.md`). It is not a term production and not a state transformation; exposing it as a term would require an extended state carrying pair partitions and SNF data, which is not in `C`.

---

## 3.8a Candidate constructor records added 2026-11-26 (taxonomy-only, rung 1)

These records name families identified by the 2026-11-26 internet scan (`notes/missed_constructions_scan_2026-11-26.md`) that satisfy §3.8's distinct-input / distinct-state-update / distinct-parameter-theorem criteria at the level of a candidate record. They are **not** admitted transitions: no grammar production, no typed transition, no obligation, and no claim status beyond the record. Each stays at rung 1 until a dated maintainer decision admits it: under the instance contract of [`VERSIONING.md`](VERSIONING.md) §4.2 if it is an instance of an existing interface, and with a new ordinal, or an additive fold, if it changes an interface (§4.1). Gate 7 (ratified 2026-11-26) admits none of them. They are recorded so the deferral is explicit rather than implicit, per `design/SCOPE.md` §4 (Gate 7 constructors are out of the stopping point). Typed-signature sketches and recommended dispositions for these records, for the §2.9 appending note and for `X-EAQLRC` (§4.9) are in `design/GATE7_CANDIDATE_EVALUATIONS.md`; they are recommendations only and change no record's rung.

### Record: `L-BRUHAT` (CSS codes from the Bruhat order of a Coxeter group)

| Field | Description |
| --- | --- |
| **Status** | Lower-level constructor candidate (taxonomy-only, rung 1) |
| **Input** | A Coxeter group (finite or infinite, reducible or not) given by its presentation, plus a collection of Bruhat intervals whose union is closed under going down in the Bruhat order (so convex, which the orthogonality argument needs; an arbitrary union of intervals is not orthogonal in general) and has nonzero homology in the selected degree, a degree selection, and the chain-complex extraction data derived from the Bruhat face poset. A single interval does not suffice: in its middle degrees it encodes no logical qubits (`design/GATE7_CANDIDATE_EVALUATIONS.md` §1) |
| **Output** | A CSS code on the qubits and checks of the extracted chain complex |
| **Operation** | Interpret the Bruhat order as the face poset of a regular CW complex; take the chain complex of a Bruhat interval; extract two- or three-term (length-three) complexes readable as $X$/$Z$ check maps of a CSS code |
| **Conditions** | The Coxeter presentation, the Bruhat interval, and the chain-complex extraction (boundary maps) must be typed; the resulting $X$ and $Z$ spaces must be orthogonal |
| **Parameter effects** | Constructor-specific; examples include controlled stabilizer weights (e.g. $[[6006,924,\{\le 14,\le 7\}]]$, $[[22880,3432,\{\le 8,\le 16\}]]$) and irregular-weight codes (e.g. $[[571,199,\{5,5\}]]$). The source's weight-reduction method for rare heavy stabilizers acts on a finished code and is **not** part of this constructor. No generic distance formula |
| **Primitive / derived** | Lower-level constructor (not a transformation of an existing CSS state) |
| **Formalization status** | Candidate record added 2026-11-26 from prior art (Brádler, arXiv 2603.16036 (2026)). No grammar production, no typed transition, no obligation. Admission needs a dated maintainer decision (see the section introduction) |
| **Partial inverse** | None stated |

**Why it is a candidate rather than an alias.** Under §3.8 the family has a distinct input type (Coxeter group + Bruhat interval, not a classical code, matrix, graph, or cellulation), a distinct orthogonality proof (Bruhat face-poset incidence), and a distinct parameter theorem (weight control via interval structure). It is not a specialization of `L-NESTED-CSS`, `L-MAPPING-CONE`, `L-TILE`, or `L-HGP`: the incidence structure is poset-interval, not a user-supplied chain map or cellulation.

### Record: `L-MONOMIAL` (divisible decreasing monomial codes)

| Field | Description |
| --- | --- |
| **Status** | Lower-level constructor candidate (taxonomy-only, rung 1) |
| **Input** | A monomial/Reed-Muller-type code on the Boolean hypercube plus a downward-closed puncturing set (and, for the randomized instance, a protected set of points) |
| **Output** | A CSS code whose logical qubits are created by the puncturing |
| **Operation** | Form a divisible decreasing monomial code and puncture it at a downward-closed set on the Boolean hypercube, with a closed-form distance for the punctured code |
| **Conditions** | The monomial family, the divisibility conditions, and the downward-closed puncturing set must be typed; the resulting $X$/$Z$ spaces must be orthogonal |
| **Parameter effects** | Constructor-specific; includes a closed-form expression for the distance of the punctured code (a parameter theorem). Transversal (strong) $T$-gate property is a logical-gate property and stays outside the object language (§1 circuit exclusion) |
| **Primitive / derived** | Lower-level constructor |
| **Formalization status** | Candidate record added 2026-11-26 from prior art (Wills, arXiv 2608.24000 (2026)). No grammar production, no typed transition, no obligation. Admission needs a dated maintainer decision (see the section introduction) |
| **Partial inverse** | None stated |

**Why it is a candidate rather than an alias.** Under §3.8 the family has a distinct input type (monomial family + downward-closed puncturing set, not arbitrary parity-check matrices) and a distinct parameter theorem (the closed-form distance). It is not a specialization of `E-PUNCTURE`, which is a state transformation on an existing code, not a from-scratch constructor, nor of `L-NESTED-CSS`.

### Record: `L-BOOTSTRAP` (quantum bootstrap product)

| Field | Description |
| --- | --- |
| **Status** | Lower-level constructor candidate (taxonomy-only, rung 1) |
| **Input** | Input codes together with a solution of the "bootstrap equation" consistency condition on multiple components |
| **Output** | A CSS code whose chain complex is a "fork complex" (chain groups and boundary maps with multiple components) |
| **Operation** | Solve the bootstrap consistency condition to obtain a chain complex that is not a simple tensor product of the inputs' complexes |
| **Conditions** | The bootstrap equation must be satisfied; the resulting fork complex must define a valid CSS code ($X \perp Z$) |
| **Parameter effects** | Constructor-specific; can surpass HGP rate upper bounds and produce self-correcting codes from constant-energy-barrier inputs. No generic distance formula |
| **Primitive / derived** | Lower-level constructor |
| **Formalization status** | Candidate record added 2026-11-26 from prior art (Li, arXiv 2601.22363 (2026)). No grammar production, no typed transition, no obligation. Admission needs a dated maintainer decision (see the section introduction) |
| **Partial inverse** | None stated |

**Why it is a candidate rather than an alias.** Under §3.8 the family has a distinct input type (a consistency equation over multiple components, not two chain complexes with a tensor product) and a distinct output (fork complexes). It generalizes `L-HGP` and fracton (X-cube) codes. It does **not** factor through `A-PRODUCT`: the admitted `product(e_A, e_B)` is the CSS tensor product of two presented states, and a fork complex is in general not a tensor product of its components (`design/GATE7_CANDIDATE_EVALUATIONS.md` §3).

### Specialization note: coset lifted product (under `L-LIFTED`)

**Recorded 2026-11-26 (prior art Rajpurohit–Lalitha–Garani, arXiv 2610.12782).**
The coset lifted product (CLP) generalizes `L-LIFTED` from normal-subgroup lifts to
non-normal subgroup coset actions: given a finite group $G$, a (possibly non-normal)
subgroup $H \le G$, a protograph $A$ over $\mathbb F_2[G]$ and $B$ over
$\mathbb F_2[N_G(H)]$, it produces a CSS code via left/right coset actions on
$G/H$. For odd-order groups it gives a dimension formula as a sum over irreducible
representations of $G$ of HGP dimensions. Under §3.8 this is a **specialization of
`L-LIFTED`** (non-normal coset action + normalizer + representation-theoretic
dimension formula), not a new primitive and not a new state update: the underlying
lift action is the same typed product, with a generalized group action. The
non-normal case is a distinct input condition and a distinct dimension formula,
which may earn a named record of its own if admitted, but it does not change the
state model. The coset lift is admitted as the optional subgroup argument of
`lift_G(A, B)`, with the normalizer as a typing premise on $B$
(`OPERATIONAL_SEMANTICS.md` §2 `L-LIFTED` card, §4.49;
`OBL-COSET-LIFT-INPUTS`). No taxonomy ID is minted. The dimension formula is
not transcribed, because $k$ is computed exactly.

### Specialization note: fair-density parity-check codes (under `L-HGP`)

**Recorded 2026-11-26 (prior art, arXiv 2609.01181).**
Fair-density parity-check (FDPC) codes used as components in hypergraph products,
with structured sparsification replacing dense checks by lower-weight checks while
retaining a minimum-distance guarantee, are a **specialization of `L-HGP`** with a
new component family (FDPC) and a sparsification step. The sparsification is a
component-level check-weight reduction, not a state transformation on a finished
code, so no new taxonomy ID is minted. The analytical logical-multiplicity data
is a candidate priced-hypothesis source (lower bounds / enumerations) consistent
with the consumer's trusted-input boundary. It is not admitted; admission needs a dated maintainer decision.

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

## 4.9 Entanglement-assisted locally recoverable codes (candidate)

### Record: `X-EAQLRC`

| Field | Description |
| --- | --- |
| **Status** | Candidate extended-state constructor (taxonomy-only, rung 1); not admitted; no grammar production |
| **Input** | Two classical codes (without the ordinary dual-containing/self-orthogonality condition) plus pre-shared maximally entangled pairs, plus locality data |
| **Output** | An entanglement-assisted CSS-like code with locality $r$ (not an ordinary CSS code in $C=(Q,X,Z,\mathsf{pres},\mathsf{used})$) |
| **Operation** | Relax the dual-containing constraint by assuming noiseless halves of pre-shared entangled pairs; build extended stabilizers with controlled supports; derive a CSS-like construction from two classical codes without the ordinary dual-containing condition |
| **Conditions** | The sufficient support conditions on extended stabilizers must hold; the entanglement resource must be typed and accounted for (it is not part of the ordinary CSS state) |
| **Parameter effects** | Constructor-specific; includes locality upper bounds and a Singleton-like bound for CSS-like EAQLRCs, with optimal families from $\ell$-intersection pairs of MDS codes and block parity-check matrices. Distance and rate depend on the classical inputs and the entanglement resource |
| **Primitive / derived** | Candidate constructor of the extended-state layer |
| **Formalization status** | Candidate record added 2026-11-26 from prior art (arXiv 2607.27091 (2026)). No transition, no grammar production, no obligation. Gate 6 admission of the extended-state layer (currently refused for v0.3.0, `design/SCOPE.md` §4) precedes any promotion |
| **Partial inverse** | None stated |

**Why it is a candidate rather than an alias.** Under §3.8 the family has a distinct input type (classical codes + entanglement resource, with the dual-containing condition dropped), a distinct state update (extended stabilizers rather than ordinary CSS checks), and distinct parameter theorems (locality bounds, Singleton-like bound). It is not representable in $C=(Q,X,Z,\mathsf{pres},\mathsf{used})$ because the entanglement resource and extended stabilizers have no field there, so it joins the extended-state layer. It is not an instance of `L-NESTED-CSS` or `C-ADD-CHECK`.

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

# Gate 7 decision matrices

Recorded 2026-11-24 as inputs to the Gate 7 decision, which was ratified on
2026-11-26 for `stdCSS-3` on these inputs
([`GATES.md`](GATES.md) §10, *Gate 7*). Neither matrix adds a production, a
transition, a judgment cell, or a consumer path.

## Typed-input decision matrix

**Argument kinds.** Each argument of a production is one of three kinds.

- A *lower-level object* is a finite object from outside the state sort: a
  binary matrix, a finite group presentation, a group-algebra element or
  matrix, a group action, local codes with vertex embeddings, tiles with
  placements and boundary rules, a qubit-label set, a lift size with block
  descriptors, a new row support, or an invertible matrix.
- A *state expression* is evaluated to a presented state.
- *Selection data* refers into the value of a state expression: a displayed
  identifier, a qubit of $Q$, a sector, a subset or partition of $Q$, a map
  between two evaluated namespaces, or a wiring keyed by displayed
  identifiers. It is well-typed only relative to that state and is checked
  against it.

**Statuses.** A production is **required** when it takes at least one
lower-level object, which no presented state determines and the term must
therefore supply. It is **derived** when every argument is a state expression
or selection data, so it needs no lower-level object. An argument is
**optional** when the card states a default for it, computed from the other
arguments. The optional status is recorded beside the primary one.

**Decision recorded.** Typed inputs stay arguments of their production or
command. None becomes a field of $C=(Q,X,Z,\mathsf{pres},\mathsf{used})$
([`STATE_MODEL.md`](STATE_MODEL.md) §1). Constructor-side data that a state does
not carry, such as the PP-parameter bundle of `PP-SCALE`, is supplied with the
term and is never read from the state ([`TERM_LANGUAGE.md`](TERM_LANGUAGE.md) §1).
Priced hypotheses are judgment inputs, never production arguments; see
*Conditional cells* below the table.

| ID | Production | Lower-level objects | State expressions and selection data | Status | Why |
| --- | --- | --- | --- | --- | --- |
| `L-HGP` | `hgp(H₁, H₂)` | $H_1$, $H_2$ binary, all dimensions $\ge 1$ | — | required | The output is a function of two classical parity-check matrices. No CSS state is an input. |
| `L-LIFTED` | `lift_G(A, B)`, `lift_{G;H}(A, B)` | $G$ (cyclic orders, multiplication table, or permutation generators); $A$ over $\mathbb{F}_2[G]$; $B$ over $\mathbb{F}_2[G]$, or over $\mathbb{F}_2[N_G(H)]$ with $H$; $H \le G$ by generators | — | required; $H$ optional (default $\{e\}$, the regular lift) | The group and the algebra entries fix the lift. Over the trivial group the term reads as `hgp(A, B)`. |
| `L-GROUP-ALGEBRA` | `twoblock_G(a, b)` | $G$; $a, b \in \mathbb{F}_2[G]$ | — | required | The $1 \times 1$ restriction of the `L-LIFTED` input: `twoblock_G(a, b)` equals `lift_G((a), (b*))` row for row (`OPERATIONAL_SEMANTICS.md` §4.34, §4.44). |
| `L-BALANCED` | `balanced_G(H₁, α₁; H₂, α₂)` | $G$; $H_1$, $H_2$; a right action $\alpha_1$ and a left action $\alpha_2$ | — | required | Equivariance is a typing condition, so an input that fails it is malformed. The actions are part of the input type and are not checked against a state. |
| `L-TANNER` | `tanner(n; Λ_X, Λ_Z; ι_X, ι_Z)` | $n$; local codes $\Lambda_X$, $\Lambda_Z$; vertex embeddings $\iota_X$, $\iota_Z$ | — | required | The incidence structure is the input. Commutation is an applicability premise (no derivation when it fails), and no expansion hypothesis is an input. |
| `L-TILE` | `tile(τ; α; β)` | tiles; placements; identifications and removed checks | — | required | The cellulation is the input. Interface orthogonality is an applicability premise. |
| `L-NESTED-CSS` | `nested(H_X, H_Z)` | $H_X$, $H_Z$, each with at least one row, with equally many columns | — | required | The two classical codes are the input. Nesting is an applicability premise. |
| `L-MAPPING-CONE` | `cone(∂_A, ∂_B, f₁, f₀)` | four binary matrices | — | required | Two two-term complexes and a chain map. The chain-map identity is an applicability premise. |
| `L-PAIR-PARTITION` | `pair_partition(p; B_X, B_Z)` | $p$; block matrices of affine descriptors | — | required | The affine permutation blocks are the input. The pairing condition is an applicability premise. |
| `L-EMPTY` | `empty` | none | none | derived (nullary) | The output is fixed, so nothing is supplied. |
| `L-FREE` | `free(Q)` | a finite label set $Q \subset \mathbb{N}$ | — | required | The qubit namespace is the whole input, and no state precedes it. |
| `PP-SCALE` | `pp_scale(e; P)` | $P$; the PP-parameter bundle or the target block matrices | $e$, a PP-presented state | required | The PP presentation is constructor-side data that $C$ does not carry, so it cannot be read off the value of $e$. |
| `A-CONCAT` | `concat(e_O, e_I; B⃗)` | — | $e_O$, $e_I$; the block list $\vec B$, a partition of $Q_O$; the representatives | derived; representatives optional | Every argument is read from or checked against the two factors. The representatives default to the dual logical bases of the inner level data. Non-CSS inner codes are not inputs (§2.14). |
| `A-PRODUCT` | `product(e_A, e_B)` | — | $e_A$, $e_B$ | derived | The product structure is fixed as the CSS tensor product. The output depends on the two displays (`OPERATIONAL_SEMANTICS.md` §4.35). |
| `A-DOUBLE` | `double_{w,s}(e)` | — | $e$; the wiring $w$, keyed by displayed identifiers; the flag $s$ | derived; $s$ optional | The wiring names subsets of displayed supports. $s$ defaults to absent, and the empty wiring gives the plain two-sheet cover. |
| `A-PULLBACK` | `pullback(e₁, e₂, e_I; φ₁, φ₂)` | — | $e_1$, $e_2$, $e_I$; total qubit maps $\phi_1$, $\phi_2$ | derived | The maps run between the namespaces of the evaluated states. The morphism property is an applicability premise. |
| `A-PUSHOUT` | `pushout(e₁, e₂, e_S; ψ₁, ψ₂)` | — | $e_1$, $e_2$, $e_S$; total qubit maps $\psi_1$, $\psi_2$ | derived | As for `A-PULLBACK`. |
| `C-DIRECT-SUM` | `e₁ ⊕ e₂` | — | $e_1$, $e_2$ | derived | The disjointness of the namespaces and of `used` are premises. |
| `E-GLUE` | `glue(e₁, e₂; u⃗)` | the seam checks $(\tau_i, \mathrm{supp}_i)$ | $e_1$, $e_2$ | required | The seam supports are new rows that neither factor carries. The seam certificate is a judgment input (`JUDGMENT_LAYER.md` §2e), not an argument. |
| `C-SKIP` | `skip` | none | none | derived (nullary) | Nothing to supply. |
| `C-DELETE-CHECK` | `delete_r` | — | $r$, a displayed identifier | derived | The deleted row is selected from the display. |
| `C-ADD-CHECK` | `addStab_r` | the new row $r$ (sector and support in $Q$) | — | required | The added support is new data that the state does not carry. |
| `E-GRAFT` | `graft(q, τ; r⃗)` | — | $q$, $\tau$, the ordered list $\vec r$ | derived | The set of rows in $\vec r$ is fixed by $(q, \tau)$. Their order is selection data. |
| `E-PEEL` | `peel(q, τ; r)` | — | $q$, $\tau$, $r$ | derived | $r$ is the unique displayed $\tau$-row containing $q$. |
| `E-PUNCTURE` | `puncture(q)` | — | $q$ | derived | The punctured qubit is selected from $Q$. |
| `E-EXTEND` | `extend(Δ; u⃗)` | the fresh labels $\Delta$; the added rows $(\tau_i, \mathrm{supp}_i)$ | — | required | The new qubits and supports are not in the state. |
| `E-LOCAL-HADAMARD` | `hadamard(T)` | — | $T \subseteq Q$ | derived | $T$ is selected from $Q$. The row-space splitting guard is an applicability premise, not an argument. |
| `P-REBASE` | `rebase(τ; M)` | $M \in \mathrm{GL}(m, 2)$ | $\tau$ | required | The size $m$ is read off the display, but the entries of $M$ are not. |
| `C-COLUMN-CNOT` | `cnotSwap(U)` | $U \in \mathrm{GL}(Q, 2)$ | — | required | $U$ is the argument of the command and the source of its computed distance window (`JUDGMENT_LAYER.md` §2k). |
| `E-SPLIT` | `split(Q_A; R)` | — | $Q_A \subseteq Q$ (qubit block), $R$ (displayed cut-row identifiers) | derived | Both $Q_A$ and $R$ are selection data checked against the state ($Q_A \subseteq Q$, every $r \in R$ displayed, $R$ covering every crossing row); no lower-level object is supplied. The optional `split_block_intervals` pricing hypothesis is a judgment input (`JUDGMENT_LAYER.md` §2c), not a command argument. |
| `C-SEQUENCE` | `m₁ ; m₂` | — | — | that of its steps | The arguments are those of $m_1$ and $m_2$, so the term is required when either step is. |

**Not admitted.** `A-QUOTIENT`, `X-SYMPLECTIC-DOUBLE`, `X-SYMPLECTIC-HALVE`,
`X-SUBSYSTEM`, and `X-GAUGE-FIX`, the five remaining candidates of the signature
record, have no production. Their typed-input status is therefore not yet
defined. Their signatures are recorded in `CONSTRUCTOR_SIGNATURES.md`.
`P-RELABEL` has no row in this table because it has no grammar production: it
is a congruence, not a command ([`TERM_LANGUAGE.md`](TERM_LANGUAGE.md) §2). It
does have a row in the family-closure matrix below, which records that
membership is invariant under it.

**Conditional cells.** The conditional Gate 6 cells
([`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2f) and the conditional constructor
cells (§2g.1) take hypotheses that the consumer supplies: prices, avoidance
minima, seam certificates, factor witnesses, and sourced lower bounds. These are
judgment inputs, not typed inputs. No production takes one as an argument
([`TERM_LANGUAGE.md`](TERM_LANGUAGE.md) §2). A missing hypothesis leaves the cell
`unavailable` or `not yet defined` rather than making the term malformed, and the
consumer checks the shape of a hypothesis, not its truth.

**Dimension reading.** The `L-HGP` and `L-NESTED-CSS` cards state that their
matrices are nonempty. The `L-LIFTED`, `L-BALANCED`, and `L-MAPPING-CONE` cards
leave this implicit. The transcription rejects an empty matrix or an empty row
(`_binary_matrix` and `_algebra_matrix` in `machine/constructors.py`). The
family-closure matrix below uses that reading and marks each verdict that
depends on it.

## Family-closure matrix

**The question.** Let $F$ be a family and $m$ a transformation. Is $F$ closed
under $m$, that is, is every output of $m$ on a member of $F$ again a member?

**Membership is code-level.** No field of $C$ records a family, so membership
has to be read off the state. At the level of presented states (`≡`) closure
already fails for `C-DELETE-CHECK`. Every constructor in the matrix mints its
identifiers from an empty `used`, so in each output `used` is the set of
displayed identifiers. After $\mathrm{delete}_r$ the retired identifier $r$ stays in
`used` while it is no longer displayed (`OPERATIONAL_SEMANTICS.md` §2,
`C-DELETE-CHECK`). The matrix therefore reads membership on codes. A state $C$
is in $F_c$ when some well-typed input of constructor $c$ that has a derivation
evaluates to a state with as many qubits as $C$ and, under some bijection of
the qubits, the same $X$ and $Z$ row spaces. The display, the identifiers,
`used`, and the qubit labels are ignored. For a binary transformation
(`C-DIRECT-SUM`, `E-GLUE`), closure means that two members on disjoint
namespaces give a member. A relabeled copy of a member is a member.

**The families.**

- *HGP, lifted, balanced, Tanner, tile, nested CSS, and mapping cone* are
  $F_c$ for $c$ = `L-HGP`, `L-LIFTED`, `L-BALANCED`, `L-TANNER`, `L-TILE`,
  `L-NESTED-CSS`, and `L-MAPPING-CONE`.
- *Decoupling* is the class of translation-invariant CSS codes of
  [`DECOUPLING_CONSTRUCTOR.md`](../design/DECOUPLING_CONSTRUCTOR.md). No
  production, taxonomy identifier, or state field defines it: $C$ has no
  lattice and no translation action.
- *Gate realization* is, for a fixed gate $U$ on a fixed $Q$
  ([`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2h), the family
  $G_U = \{C \text{ on } Q : \mathsf{preserves}_U(C)\}$. It depends on the labels by
  definition, since $U$ acts on named qubits.

**Verdicts.**

- *closed*: `proved`, with the derivation in this section or the cited one.
- *closed when …*: `proved` under the stated side condition.
- *not closed*: the closure claim is `false`, and the counterexample is
  recorded.
- *open*: no derivation in either direction; evidence `open`.
- *not yet defined*: the family, or the action of $m$ on it, has no definition
  in this state model; `not-applicable`.

The rows are the thirteen admitted transformations other than `C-SEQUENCE`,
together with the `P-RELABEL` congruence, which is not a command. Closure under
`C-SEQUENCE` follows from closure under each step, so it has no row of its
own. Every counterexample below is a one-step term.

**What this matrix does not do.** It enters no judgment cell and no consumer
path. Family closure as a carried judgment, family-level completeness, and
amplified distance lower bounds remain `unavailable`, as stated in
[`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2j and §2l and in
[`SCOPE.md`](../design/SCOPE.md) §4. A *closed* verdict says only that the
output code is again a member. It transports no parameter, distance, or
witness.

| Transformation | HGP | lifted | balanced | Tanner | tile | nested CSS | mapping cone | decoupling | gate realization |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `C-SKIP` | closed (L1) | closed (L1) | closed (L1) | closed (L1) | closed (L1) | closed (L1) | closed (L1) | not yet defined | closed (GR1) |
| `P-RELABEL` | closed (L1) | closed (L1) | closed (L1) | closed (L1) | closed (L1) | closed (L1) | closed (L1) | not yet defined | not closed for a fixed $U$ (GR3); closed when $U$ is relabeled with the state |
| `P-REBASE` | closed (L1) | closed (L1) | closed (L1) | closed (L1) | closed (L1) | closed (L1) | closed (L1) | not yet defined | closed (GR1) |
| `C-DELETE-CHECK` | not closed (H2) | not closed (H2) | open (B) | closed (U) | closed (U) | closed (U) | closed (U) | not yet defined | not closed (GR4) |
| `C-ADD-CHECK` | not closed (H1) | not closed (H1) | open (B) | closed (U) | closed (U) | closed (U) | closed (U) | not yet defined | not closed (GR6); closed iff $\Phi_{J(s)}(l) \in \pi\mathbb{Z}$ for every $l \in \Lambda(\mathcal{S}(C'), J(s))$, decided for rational angles (§2h, Corollary 7.1; in particular when every generator commutes with the added row, or when all angles are $\pi/4$ and $V_s \in \mathcal{S}(C')$) |
| `C-DIRECT-SUM` | closed when the summands share a factor matrix (H6); otherwise open | open | open (B) | closed (U) | closed (U) | closed (U) | closed (U) | not yet defined | closed when $U$ is supported on one summand and read as the identity on the other, the one namespace change §2h transports |
| `E-GRAFT` | open | open | open (B) | closed (U) | closed (U) | closed (U) | closed (U) | not yet defined | not yet defined (GR5) |
| `E-PEEL` | not closed (H4) | not closed (H4) | not closed (H4) | not closed at $n = 1$; closed on $n \ge 2$ (U1) | not closed at $n = 1$; closed on $n \ge 2$ (U1) | not closed at $n = 1$; closed on $n \ge 2$ (U1) | not closed at $n = 2$; closed on $n \ge 3$ (U2) | not yet defined | not yet defined (GR5) |
| `E-PUNCTURE` | not closed (H3) | not closed (H3) | not closed (H3) | not closed at $n = 1$; closed on $n \ge 2$ (U1) | not closed at $n = 1$; closed on $n \ge 2$ (U1) | not closed at $n = 1$; closed on $n \ge 2$ (U1) | not closed at $n = 2$; closed on $n \ge 3$ (U2) | not yet defined | not yet defined (GR5) |
| `E-EXTEND` | not closed (H1) | not closed (H1) | open (B) | closed (U) | closed (U) | closed (U) | closed (U) | not yet defined | not yet defined (GR5) |
| `E-LOCAL-HADAMARD` ($T = Q$) | closed (H7) | closed (H8) | open (B) | closed (U) | closed (U) | closed (U) | closed (U) | not yet defined | not closed (GR2) |
| `C-COLUMN-CNOT` | open | open | open (B) | closed (U) | closed (U) | closed (U) | closed (U) | not yet defined | not closed (GR3) |
| `E-GLUE` | not closed (H5) | not closed (H5) | open (B) | closed (U) | closed (U) | closed (U) | closed (U) | not yet defined | not yet defined (GR5) |
| `E-SPLIT` | not closed (H2) | not closed (H2) | open (B) | closed (U) | closed (U) | closed (U) | closed (U) | not yet defined | not closed (GR4) |

`E-LOCAL-HADAMARD` at $T = \varnothing$ is the identity and falls under (L1). The
split-subset instance has no row here: its family-closure verdicts are
not yet defined. The
mapping-cone column, and the lifted and balanced verdicts that rest on (J1) or
(J2), use the nonempty-matrix reading of the typed-input matrix above. The
instance checks and the counterexamples are replayed in
[`test_family_closure.py`](../machine/test_family_closure.py). That agreement is
evidence that the derivations are transcribed as stated. It is not a proof.

**(L1) Transformations that keep the code.** `C-SKIP` leaves the state
unchanged. `P-REBASE` leaves both row spaces unchanged
(`OPERATIONAL_SEMANTICS.md` §4.26, *Row space*). `P-RELABEL` is a bijection of
the qubits, and membership is invariant under such bijections by definition.
Each therefore maps a member to a member. ∎

**(U) The universal families.** Write $\mathrm{CSS}_{\ge c}$ for the well-formed
CSS states on at least $c$ qubits.

- $F_{\mathrm{nested}} = \mathrm{CSS}_{\ge 1}$. The card requires $n \ge 1$, so
  $F_{\mathrm{nested}} \subseteq \mathrm{CSS}_{\ge 1}$. Conversely, relabel a state
  with $n \ge 1$ onto $\{0, \ldots, n-1\}$ in order. It then has the code of
  $\mathrm{nested}(H_X, H_Z)$, where the rows of $H_X$ and $H_Z$ are its displayed
  rows and a sector with no displayed row is given by one zero row. The premise
  is I1 (`OPERATIONAL_SEMANTICS.md` §4.36, *Relation to `L-TANNER`*, the
  genericity statement).
- $F_{\mathrm{Tanner}} = \mathrm{CSS}_{\ge 1}$. By §4.36,
  $\mathrm{nested}(H_X, H_Z) = \mathrm{tanner}(n; H_X, H_Z; \iota, \iota)$ with
  $\iota$ the identity embedding, so $F_{\mathrm{nested}} \subseteq F_{\mathrm{Tanner}}$.
  The card requires $n \ge 1$.
- $F_{\mathrm{tile}} = \mathrm{CSS}_{\ge 1}$. Take one tile with $t = n$ local
  qubits whose local $X$- and $Z$-row supports are the displayed supports of $C$
  relabeled onto $\{0, \ldots, n-1\}$, one placement on the sites
  $0, \ldots, n-1$, and no identifications or removed checks. The site classes
  are then the sites, the natural rows are the displayed rows, and interface
  orthogonality is I1 of $C$. In the other direction, the card requires $t \ge 1$
  and a nonempty list of placements, so every output has $n \ge 1$.
- $F_{\mathrm{cone}} = \mathrm{CSS}_{\ge 2}$, under the nonempty-matrix reading.
  Every output has $n = a_0 + b_1 \ge 2$. Conversely, take a state with $n \ge 2$
  and check matrices $H_X$ and $H_Z$ (one zero row for an empty sector). Put
  $a_0 = n - 1$ and $b_1 = 1$. Let $\partial_A$ be $H_Z$ without its last column,
  $f_1$ the last column of $H_Z$, $f_0$ the transpose of $H_X$ without its last
  column, and $\partial_B$ the transpose of the last column of $H_X$. By the card,
  the natural $Z$-rows are then the rows of $H_Z$ and the natural $X$-rows are
  the rows of $H_X$. At row $j$ of $H_Z$ and row $r$ of $H_X$, the chain-map
  premise reads
  $\sum_{i < n-1} H_Z[j, i] H_X[r, i] = H_Z[j, n-1] H_X[r, n-1]$. Over
  $\mathbb{F}_2$ this is $H_Z H_X^{T} = 0$, which is I1.

Every admitted transformation maps a well-formed state to a well-formed state
(`OBL-WELL-FORMEDNESS-PRESERVATION`: `OPERATIONAL_SEMANTICS.md` §4.7 for the
kernel, §4.12 for the graft, §4.26–§4.32 for the Gate 6 commands, §4.42 for
the column CNOT, and §4.48 for `E-SPLIT`). A family $\mathrm{CSS}_{\ge c}$ is therefore closed under $m$
exactly when $m$ never takes a member to fewer than $c$ qubits. The qubit count
is unchanged by delete, add, rebase, the sector exchange, the column CNOT, and `E-SPLIT`.
It grows by $|\Delta|$ under extend and is $n_A + n_B$ under the direct sum and
the glue. It drops by one under graft, peel, and puncture, so only those three
can leave the family.

- *(U1), $c = 1$.* $\mathrm{puncture}_0$ on $\mathrm{free}(\{0\})$, and
  $\mathrm{peel}_{0, X; r}$ on the one-qubit state whose only row is the $X$-row
  $\{0\}$, both reach the empty state, which has $n = 0$. So these two are not
  closed at $n = 1$ and are closed on members with $n \ge 2$.
- *(U2), $c = 2$.* Puncture any two-qubit member, for example
  $\mathrm{free}(\{0, 1\})$, or apply $\mathrm{peel}_{0, X; r}$ to the state with rows
  $X_0$ and $Z_1$. Both reach $n = 1$. So these two are not closed at $n = 2$ and
  are closed on members with $n \ge 3$.
- *Graft never leaves either family.* The card requires $q$ to lie in a
  $\tau$-row and in an opposite-sector row. On one qubit both rows would be
  $\{q\}$, and their overlap is odd, against I1, so graft has no derivation at
  $n = 1$. On two qubits an $X$-row and a $Z$-row through $q$ overlap evenly only
  if both are $\{0, 1\}$. Then $X = \langle X_0 X_1 \rangle$ and
  $Z = \langle Z_0 Z_1 \rangle$, because each sector lies in the orthogonal
  complement $\{00, 11\}$ of the other. Grafting either sector at $q$ removes its
  only row and leaves the other qubit in no $\tau$-row. The card requires every
  remaining qubit to lie in a check of each sector, so there is no derivation
  here either. ∎

**(H) HGP, lifted, and balanced.** Both invariants below read the input
matrices as nonempty. The `L-HGP` card says so, and for `L-LIFTED` and
`L-BALANCED` this is the transcription's reading.

- *(J1), all three: $n \ge 2$.* For `L-HGP`, $n = n_1 n_2 + m_1 m_2$. For
  `L-LIFTED`, $n = \ell(n_A n_B + m_A m_B)$. For `L-BALANCED`, $n$ counts the
  orbits of the pairs of column indices and the orbits of the pairs of row
  indices, and both sets of pairs are nonempty.
- *(J2), HGP and lifted: $X = 0$ if and only if $Z = 0$.* In `hgp(H₁, H₂)` the
  left parts of the $X$-rows $(a, j)$ meet every entry of $H_1$, because
  $n_2 \ge 1$, and their right parts meet every entry of $H_2$, because
  $m_1 \ge 1$. So every $X$-row is empty if and only if $H_1 = 0$ and $H_2 = 0$.
  The $Z$-rows $(i, b)$ meet the same entries, because $n_1, m_2 \ge 1$. Hence
  $X = 0 \iff H_1 = H_2 = 0 \iff Z = 0$. For `lift_G(A, B)` and
  `lift_{G;H}(A, B)` the argument runs on the block matrices, not on the
  algebra entries. The $X$-rows meet the left blocks through every
  $L_H(A[a,i])$ and the right blocks through every $R_H(B[b,j]^*)$. So
  $X = 0$ if and only if all of these matrices are zero. Likewise $Z = 0$ if
  and only if every $R_H(B[b,j])$ and every $L_H(A[a,i]^*)$ is zero. Since
  $L_H(x^*) = L_H(x)^T$ and $R_H(y^*) = R_H(y)^T$, and a matrix is zero
  exactly when its transpose is, $X = 0 \iff Z = 0$. Here $H = \{e\}$ is the
  regular lift. The entry-level reading $L(x) = 0 \iff x = 0$ holds only for
  the regular lift: with $H = G$, $L_H(g + g') = 0$. For `L-BALANCED`
  over a nontrivial group, (J2) is not derived: the card defines an orbit row by
  parities over the orbit, and these may cancel.

Two members of all three families serve as seeds.
$E_0 = \mathrm{hgp}([0], [0])$ is two qubits with no rows.
$E_1 = \mathrm{hgp}([1], [0])$ has $X = \langle X_0 \rangle$ and
$Z = \langle Z_1 \rangle$: the $X$-row $(0, 0)$ is the left qubit $0$, and the
$Z$-row $(0, 0)$ is the right qubit $1$. Over the trivial group the `L-LIFTED`
and `L-BALANCED` cards evaluate to `hgp` row for row, so the seeds are members
of those families too.

- *(H1)* $\mathrm{addStab}_{r:X} \triangleright E_0$ with $r = \{0\}$, and
  $\mathrm{extend}_{\Delta; (X, \{0\})} \triangleright E_0$ for any fresh $\Delta$,
  give $X \ne 0$ and $Z = 0$. This violates (J2).
- *(H2)* $\mathrm{delete}_r \triangleright E_1$ — and likewise
  $\mathrm{split}_{\{0\}; \{r\}} \triangleright E_1$, whose crossing set is
  empty so $R = \{r\}$ is valid (§4.48) — with $r$ the $Z$-row, gives
  $X \ne 0$ and $Z = 0$. This violates (J2).
- *(H3)* $\mathrm{puncture}_0 \triangleright E_0$ has $n = 1$. This violates (J1).
- *(H4)* $\mathrm{peel}_{0, X; r} \triangleright E_1$, with $r$ the unique $X$-row
  containing $0$, has $n = 1$. This violates (J1).
- *(H5)* Let $E_0'$ be a copy of $E_0$ on $\{2, 3\}$, with no rows and an empty
  `used`. Then $\mathrm{glue}(E_0, E_0'; [(X, \{0\})])$ has $X = \langle X_0 \rangle$
  and $Z = 0$ on four qubits. This violates (J2).
- *(H6) Distributivity of `hgp`.* Write $H \oplus H'$ for the block-diagonal
  matrix. Then $\mathrm{hgp}(H \oplus H', K)$ has the code of
  $\mathrm{hgp}(H, K) \oplus \mathrm{hgp}(H', K)$, and $\mathrm{hgp}(K, H \oplus H')$
  has the code of $\mathrm{hgp}(K, H) \oplus \mathrm{hgp}(K, H')$. *Derivation.*
  The row and column index sets of $H \oplus H'$ are disjoint unions of those of
  $H$ and $H'$, and the entries between the two blocks are $0$. In
  $\mathrm{hgp}(H \oplus H', K)$ every qubit, $(i, j)$ or $(a, b)$, has its first
  index in one block. The $X$-row $(a, j)$ has support
  $\{(i, j) : (H \oplus H')[a, i] = 1\} \cup \{(a, b) : K[b, j] = 1\}$, whose
  first indices all lie in the block of $a$. On that block it is the $X$-row
  $(a, j)$ of $\mathrm{hgp}(H, K)$ or of $\mathrm{hgp}(H', K)$. The $Z$-row
  $(i, b)$ behaves the same way. So the qubits split into two blocks that no row
  crosses, and each block carries one summand. For the second argument, exchange
  the roles of the two indices. ∎ Hence the direct sum of two HGP members that
  share their first or their second factor matrix is an HGP member.
- *(H7) The sector exchange of `hgp`.* Let $C = \mathrm{hgp}(H_1, H_2)$ and
  $C' = \mathrm{hgp}(H_1^{T}, H_2^{T})$. The left qubits of $C'$ are the pairs
  $(a, b)$ and its right qubits are the pairs $(i, j)$. The $X$-row $(i, b)$ of
  $C'$ has support $\{(a, b) : H_1[a, i] = 1\} \cup \{(i, j) : H_2[b, j] = 1\}$.
  This is the support of the $Z$-row $(i, b)$ of $C$ under the bijection that
  sends the left qubit $(i, j)$ of $C$ to the right qubit $(i, j)$ of $C'$, and
  the right qubit $(a, b)$ of $C$ to the left qubit $(a, b)$ of $C'$. In the same
  way the $Z$-row $(a, j)$ of $C'$ is the $X$-row $(a, j)$ of $C$. So
  $\mathrm{hadamard}_Q \triangleright C$ (§4.27) has the code of $C'$, and the
  transposes are nonempty. ∎
- *(H8) The sector exchange of `lift`.* Let $C = \mathrm{lift}_G(A, B)$ and
  $C' = \mathrm{lift}_G(A', B')$, where $A'[i, a] = A[a, i]^*$ and
  $B'[j, b] = B[b, j]^*$. The $X$-row $(i, b, h)$ of $C'$ carries row $h$ of
  $L(A'[i, a]) = L(A[a, i]^*)$ on the qubits $(a, b, \cdot)$ for every $a$, and
  row $h$ of $R(B'[j, b]^*) = R(B[b, j])$ on the qubits $(i, j, \cdot)$ for every
  $j$. Under the bijection of (H7), with the group coordinate fixed, this is the
  $Z$-row $(i, b, h)$ of $C$. Symmetrically, using $(x^*)^* = x$, the $Z$-row
  $(a, j, h)$ of $C'$ is the $X$-row $(a, j, h)$ of $C$. This holds for every
  finite group, abelian or not. ∎
- *Open cells.* The column CNOT keeps $n$ and keeps each sector zero or nonzero.
  A graft output has every remaining qubit in rows of both sectors. The direct
  sum preserves (J1) and (J2). So neither invariant decides the column CNOT, the
  graft, or the general direct sum, and those cells stay open. At $n = 2$ the
  column CNOT is closed for HGP and lifted. A two-qubit member of either family
  is `hgp` of $1 \times 1$ matrices, by (J1) and the nonempty reading. The two-qubit
  CSS codes with both sectors nonzero are, up to relabeling, those of
  $\mathrm{hgp}([1],[0])$ and $\mathrm{hgp}([1],[1])$, and a column operation
  keeps each sector zero or nonzero. This does not decide larger $n$.
- *(B) Balanced.* (H3) and (H4) use only (J1), so they hold. The trivial-group
  members do not decide the other cells, and (J2) is not derived for a
  nontrivial group, so those cells stay open.

**(GR) Gate realization.**

- *(GR1)* $\mathsf{preserves}_U(C)$ depends only on
  $\mathcal{S}(C) = \langle X, Z \rangle$: its carrier is `span` (§2h). `C-SKIP`
  and `P-REBASE` keep $\mathcal{S}(C)$ (§4.26). §2h records a cell for `C-SKIP`
  and none for `P-REBASE`. The `P-REBASE` verdict here is a family-level fact
  read off the carrier, not a judgment cell.
- *(GR2) The sector exchange.* Let $Q = \{0, 1\}$, let $C$ have the single
  $X$-row $\{0, 1\}$, and let $U = \exp(i \frac{\pi}{4} X_0)$. The row commutes
  with $X_0$, so $V = I$ and $\mathsf{preserves}_U(C)$ holds (Lemma 3,
  `OPERATIONAL_SEMANTICS.md` §4.37). $\mathrm{hadamard}_Q$ gives the single
  $Z$-row $\{0, 1\}$, which anticommutes with $X_0$. So $V = i X_0$, which is not
  in $\mathcal{S}(C')$ by Lemma 1 because its phase is $i$, and
  $\mathsf{preserves}_U(C')$ fails.
- *(GR3) The column SWAP.* Let $C$ have the single $X$-row $\{0\}$, and let
  $U = \exp(i \frac{\pi}{4} Z_1)$. Then $\mathsf{preserves}_U(C)$ holds. Let
  $P \in \mathrm{GL}(Q, 2)$ be the permutation matrix that exchanges the columns
  $0$ and $1$ (§2k). Then $\mathrm{cnotSwap}_P$, which is also the relabeling that
  exchanges $0$ and $1$, gives the single $X$-row $\{1\}$. This row anticommutes
  with $Z_1$, so $V = i Z_1 \notin \mathcal{S}$. If instead $U$ is relabeled with
  the state, $\mathsf{preserves}_{P_\pi U P_\pi^\dagger}(\pi \cdot C)$ holds if and
  only if $\mathsf{preserves}_U(C)$ does, because the codespace of $\pi \cdot C$ is
  $P_\pi \mathcal{V}(C)$.
- *(GR4)* The deletion counterexample of §4.37, and for `E-SPLIT` the same
  single-row deletion realized as $\mathrm{split}_{Q; \{r\}}$ (whose crossing
  set is empty, so $R = \{r\}$ is valid and produces the identical child state).
- *(GR5)* `E-GRAFT`, `E-PEEL`, `E-PUNCTURE`, `E-EXTEND`, and `E-GLUE` change the
  namespace while $U$ stays fixed on $Q$. Membership of the output in $G_U$ is
  therefore not defined without a rule that transports $U$, and §2h records no
  cell for `E-GRAFT` or for the Gate 6 transitions.
- *(GR6) The check addition.* Let $Q = \{0\}$, let $C$ have no rows, and let
  $U = \exp(i \theta X_0)$ with $\theta$ not a multiple of $\pi$. The codespace
  of $C$ is the whole space, so $\mathsf{preserves}_U(C)$ holds.
  $\mathrm{addStab}_{r:Z}$ with $r = \{0\}$ has a derivation, and the child's
  codespace is spanned by $|0\rangle$. Since
  $U|0\rangle = \cos\theta\,|0\rangle + i\sin\theta\,|1\rangle$ leaves it,
  $\mathsf{preserves}_U(C')$ fails. At $\theta = \pi/4$ this is Lemma 3 of §4.37:
  $Z_0$ anticommutes with $X_0$, and $V = iX_0 \notin \mathcal{S}(C')$. Membership
  in $G_U$ is defined at every angle, and Corollary 7.1 of §4.37 (issue #572,
  `stdCSS-3` / `v0.3.2`) decides the carry cell from the display alone for every rational
  angle $\theta \in \pi\mathbb{Q}$ (its
  reading in a logical frame is Row C of §2h).

**Decoupling.** Every cell is `not yet defined`. The candidate of
[`DECOUPLING_CONSTRUCTOR.md`](../design/DECOUPLING_CONSTRUCTOR.md) §1 is a
certificate-checked relation between two presented states, not a constructor.
Its translation-invariant input class has no representation in $C$.

## Completeness feasibility decision (Gate 7, issue #606)

**Decision recorded (2026-11-25, maintainer decision, MathysRennela; Option
(a)).** A scoped, non-circular **generation and transition completeness**
theorem over the elementary move fragment is feasible and is opened as the
proof obligation `OBL-ELEMENTARY-COMPLETENESS` in
[`OBLIGATIONS.md`](OBLIGATIONS.md) (evidence status `open`; folded into
`stdCSS-3` / `v0.3.2` by maintainer decision 2026-11-26, originally opened as an
axis-4 shape obligation per [`VERSIONING.md`](VERSIONING.md) §4.1).
This decision is strictly about **code-level reachability**; it leaves the
project's deliberate **judgment incompleteness**
([`SCOPE.md`](../design/SCOPE.md) §2, [`GATES.md`](GATES.md) §11 —
`unavailable` deletion-distance lower bounds and no inferability claim)
completely unchanged.

**Why naive completeness statements are circular or obstructed.**

1. *Circular one-shot constructors.* Derivation **(U)** above shows that
   `L-NESTED-CSS`, `L-TANNER`, `L-TILE`, and `L-MAPPING-CONE` each generate
   $\mathrm{CSS}_{\ge 1}$ or $\mathrm{CSS}_{\ge 2}$ in a single constructor
   call, only because they accept the entire target parity-check matrices
   $(H_X, H_Z)$ as raw lower-level input. That is circular and does not count
   as generation completeness.
2. *Presentation-exact (`≡`) obstruction.* Identifier history `used` is
   monotonically non-decreasing across every command and never reuses a retired
   identifier (`STATE_MODEL.md` I3; `OBL-FIXED-NAMESPACE-REACHABILITY`,
   `OPERATIONAL_SEMANTICS.md` §4.17). Completeness therefore holds only **up to
   code equivalence** (identical qubit set $Q$ and identical stabilizer row
   spaces $X, Z$, with canonical identifier allocation), never at literal `≡`.
3. *Structured-family non-closure (and scope).* In the family-closure matrix
   above, derivations **(H1)–(H5)** show that `L-HGP` and `L-LIFTED` are
   **not closed** under `C-ADD-CHECK` and `E-EXTEND` (H1), `C-DELETE-CHECK`
   (H2), `E-PUNCTURE` (H3), `E-PEEL` (H4), and `E-GLUE` (H5); for
   `L-BALANCED`, only `E-PUNCTURE` (H3) and `E-PEEL` (H4) are decided
   (`not closed`), while `C-DELETE-CHECK`, `C-ADD-CHECK`, `E-EXTEND`, and
   `E-GLUE` remain `open` (B). Non-closure under a move says only that some
   step leaves the family, not that two members have no path staying inside it;
   what follows from the matrix is that the elementary bridge of the sketch
   below leaves these families, so `OBL-ELEMENTARY-COMPLETENESS` makes no
   family-internal claim. Likewise, the family-closure matrix has no
   bounded-weight LDPC family, and `OBL-ELEMENTARY-COMPLETENESS` makes no
   bounded-weight preservation claim.
4. *Capacity boundary (H-4).* The 70,000-name finite identifier enumeration
   (`STATE_MODEL.md` I3) bounds the total identifiers minted along any finite
   derivation.

**Scoped non-circular feasibility argument.** Fix the elementary fragment
comprising the nullary seed `L-EMPTY` and the elementary commands
`C-DELETE-CHECK`, `C-ADD-CHECK`, `E-PUNCTURE`, `E-EXTEND` (restricted to
single bare-qubit additions $|\Delta| = 1, \vec u = \varnothing$), and
`C-SEQUENCE`. Every step adds or removes at most one qubit or one check vector;
no constructor consumes a whole target check matrix pair.

- *Generation completeness (from `L-EMPTY`):* for any well-formed CSS state
  $C = (Q, X, Z, \mathsf{pres}, \mathsf{used})$ with
  $\dim X + \dim Z \le 70{,}000$, apply $|Q|$ single-qubit empty-addition
  `E-EXTEND` steps to reach the check-free code on $Q$ (zero mints,
  $\mathsf{used} = \varnothing$), then insert a displayed basis of $X$ followed
  by a displayed basis of $Z$ via `C-ADD-CHECK` ($\dim X + \dim Z$ canonical
  mints; commutation holds by I1 and independence by I2 at every step).
- *Variable-namespace transition completeness:* extending
  `OBL-FIXED-NAMESPACE-REACHABILITY` (§4.17) across distinct finite namespaces,
  for any two well-formed CSS states $C_1$ on $Q_1$ and $C_2$ on $Q_2$
  satisfying the H-4 capacity bound
  $|\mathsf{used}(C_1)| + \dim X_2 + \dim Z_2 \le 70{,}000$: (i) delete every
  displayed check of $C_1$ via `C-DELETE-CHECK` (zero mints, reaching the
  check-free code on $Q_1$); (ii) remove each qubit $q \in Q_1 \setminus Q_2$
  via `E-PUNCTURE` (zero mints; on a check-free state I1–I5 hold vacuously down
  to $n = 0$, §4.29); (iii) add each qubit $q \in Q_2 \setminus Q_1$ via
  `E-EXTEND` with $\Delta = \{q\}, \vec u = \varnothing$ (zero mints, §4.30);
  and (iv) insert a displayed basis of $X_2$ and $Z_2$ via `C-ADD-CHECK`
  ($\dim X_2 + \dim Z_2$ mints, all within H-4 capacity).

This feasibility sketch demonstrates why `OBL-ELEMENTARY-COMPLETENESS` is
non-circular and achievable, and does **not** discharge it; the formal hand
derivation and Lean mechanization remain `open`. The check-free bridge
collapses distance to 1 along the intermediate path and implies no
distance-preserving path or judgment completeness.

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
| Merge/glue/split | `E-GLUE` admitted conditional extension 2026-10-23, binary-only expression constructor (`TERM_LANGUAGE.md` §1–§2, 2026-11-18), evaluator transition (§4.31), logical-witness and boundary/edge-label fields defined (`STATE_MODEL.md` §1a), `contract-stated` (rung 5, 2026-11-18); `E-SPLIT` separating deletion admitted 2026-11-25 as a derived command production `split(Q_A; R)` over `C-DELETE-CHECK` (`transition-defined`, §4.48; two-state projection refused) |
| Local Hadamard (per-qubit sector swap) | Conditional extension admitted 2026-10-23; the **$T=Q$ instance has a typed transition** (§2.12: the sector exchange of the whole display). The **split-subset instance has a typed transition** too (2026-11-26): it requires both row spaces to split along $T$, and its canonical update is specified in `OPERATIONAL_SEMANTICS.md` §2 and §4.27(b) |
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
