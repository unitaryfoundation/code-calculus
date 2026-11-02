# Proof-Obligation Ledger

## Evidence

**Evidence lives with its obligation, not in a separate worked-examples file.**
An obligation that records *what is claimed* but not *what was worked out* cannot
be assessed, and the worked cases were doing that work from 584 lines away.

**Evidence is never proof.** Agreement between an example and a rule is evidence,
never confirmation (`AGENTS.md`, *Hard rules*). Every entry below is an 
worked case: it *falsifies* the design or it does not.

**The instances are in [`machine/fixtures/mvp_fixtures.json`](../machine/fixtures/mvp_fixtures.json).**
That file defines two sets: the **acceptance surface is `W0`–`W16`**
(`acceptance_surface: true`) and the **supplementary probes are `W21`–`W28`**
(`acceptance_surface: false`, executed but not part of that surface). Every count
below and elsewhere in the repository cites those two sets rather than
restating a number. The JSON is what an evaluator reads.

Later-layer probes `W17`–`W20` are recorded in the fixture file. 

| Evidence | Establishes | For |
| --- | --- | --- |
| `W7` | delete-then-add on $r$ with $s$ in the surviving span restores the row space but is **not** a state identity: $A_3\not\equiv A$, and `used` grows | `OBL-ROW-REPLACEMENT-FACTOR` |
| `W7` | a row-referencing certificate is invalidated at the deletion step although the final code equals the original — **information-losing at the context level** | `OBL-ROW-REPLACEMENT-FACTOR` |
| `W8` | one order applies and the other does not: **the moves do not permute**. Conditional permutation cannot be claimed | `OBL-CROSS-SECTOR-PERMUTATION` |
| `W13` | a claim referring to a deleted generator does not transport; distance values are true of the state but **deliberately underivable** | `OBL-JUDGMENT-TRANSPORT` |
| `W14` | direct-sum distance law holds, with the equality level corrected to **literal** $\equiv$ — the defect that survived six days and two review dispositions | `OBL-DIRECT-SUM-LAWS` |
| `W21` | an implementation checking only **qubit** disjointness is insufficient; `used` sets must also be disjoint | `OBL-FRAME-LAW` |
| `W22` | an implementation reading the `C-ADD-CHECK` commutation premise as a bare dot product is insufficient; complements are taken inside $\mathbb{F}_2^Q$, so $\operatorname{supp}(r)\subseteq Q$ is required | `OBL-WELL-FORMEDNESS-PRESERVATION` |
| `W10` | a later command failing after an earlier one succeeds yields **no derivation**, not a stuck residual — the semantics exposes no partial state | `OBL-SEQUENCE-ASSOCIATIVITY` |

**What this is not.** Eight worked cases out of the 25 records in that file. The
remaining seventeen are applicability and well-formedness cases whose expected outcome is
recorded in the fixture itself; there is no claim riding on them that is not
already in the rule. Nothing here discharges an obligation.

---

## Entry format

Each entry records:

- stable name and taxonomy operation IDs;
- semantic-contract field and evidence status, when applicable;
- statement;
- hypotheses;
- conclusion;
- dependencies;
- classification as definition, lemma, theorem, or metatheorem;
- known edge cases and counterexamples;
- intended mechanization status;
- `introduced-in` release, when later than `stdCSS-1`;
- `discharged-through` release, for a tracked re-discharge status.

Entries are obligations; an entry is not a proved result. The ledger covers
every intended obligation of the work plan.

Every entry records, as requires:

- stable name and taxonomy operation IDs;
- semantic-contract field and evidence status, when applicable;
- statement;
- hypotheses;
- conclusion;
- dependencies;
- classification as definition, lemma, theorem, or metatheorem;
- known edge cases and counterexamples;
- intended mechanization status;
- `introduced-in` release, when later than `stdCSS-1`;
- `discharged-through` release, for a tracked re-discharge status.

Version conventions are defined in [`spec/VERSIONING.md`](VERSIONING.md): absence of
`introduced-in` means `stdCSS-1`, and `discharged-through` does not advance until
the obligation is re-established for the named release.

Classification convention: a **lemma** or **theorem** is a statement about CSS
codes and their transformations; a **metatheorem** is a statement about the
calculus's own transition system (derivability, order of evaluation,
reachability).

Evidence statuses follow [`CLAIMS.md`](CLAIMS.md):
`conjectural` marks a claim with a proof sketch that cannot be discharged before
 fixes the operational semantics; `open` marks a claim with no available
argument yet.

---

## `OBL-ORDER-INDEPENDENT-DELETION` — Order-independent deletion

**Taxonomy IDs:** `C-DELETE-CHECK`, `C-SEQUENCE`

**Semantic-contract field:** `C-DELETE-CHECK` fields 3 (state update) and 11
(provenance); `C-SEQUENCE` annotation transport.

**Claim shape:** `equality`

**Evidence status:** `proved` (state-level part); `proved` under the
fixed-reference-set hypothesis (annotation-transport part) — hand derivation
`spec/OPERATIONAL_SEMANTICS.md` §4.15, 2026-10-20.

**Classification:** metatheorem

**Ledger status:** proved (hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.15, 2026-10-20).

**Intended mechanization status:** Lean theorem in the and slices after
explicit authorization; feeds Gates 2–3 and the multi-row deletion note in
[`spec/TAXONOMY.md`](TAXONOMY.md) §2.3.

**Statement.** Let $S$ be a finite set of displayed generator identifiers of a
well-formed presented CSS state, over either stabilizer type or both. For any two
enumeration orders of $S$, the corresponding `C-DELETE-CHECK` sequences under
`C-SEQUENCE` are both applicable and produce the same final presented state and
the same transported context: identical qubit namespace, surviving displayed rows
with their identifiers, surviving row spaces, and annotation updates. A
simultaneous deletion of $S$ is therefore well-defined as an unordered batch
operation.

**Hypotheses.**

- The input is a well-formed phase-insensitive presented CSS state  whose
 displayed generators are independent per type.
- $S$ is a finite set of displayed generator identifiers; each deleted row is
 displayed and independent at its deletion step, which is automatic for subsets
 of an independent displayed set.
- No presentation operation intervenes between the deletions (interleaved
 `P-RELABEL` or `P-REBASE` is excluded and covered by the
 presentation-conjugation obligation).
- The context-update table specifies annotation invalidation, which
 follows the **fixed-reference-set model**: each
 certificate or witness $c$ carries a reference set $\operatorname{Ref}(c)$ of
 generator identifiers, and deleting identifier $r$ updates the valid set by
 $V\mapsto V\setminus\{c : r\in\operatorname{Ref}(c)\}$. This update family is
 pairwise commuting and idempotent, and its composition depends only on the
 deleted-identifier set $S$.

**Conclusion.**

- Both enumeration orders are applicable and yield equal final presented states
 and equal transported context, up to the ordering of provenance step records.
- Annotation invalidation is determined by $S$ as a set, not by the deletion
 order: certificates and witnesses mentioning one or more deleted rows are
 invalidated exactly once.
- Multi-row deletion factors as a derived batch operation equal to any
 sequential enumeration of $S$ (the `spec/TAXONOMY.md` §2.3 instance).

**Dependencies.** (presented-state identity, context inventory); 
(`C-DELETE-CHECK` update and inapplicability rules, context-update table,
intermediate-state behavior); the `C-DELETE-CHECK` and `C-SEQUENCE` semantic
contracts; presentation conjugation (for the excluded interleavings).

**Known edge cases and counterexamples.**

- Dependent-generator deletion ( required example) is inapplicable: the
 result is scoped to sets of displayed identifiers; a dependent target row is
 an applicability failure, not an order-dependence.
- A certificate referencing two rows of $S$ must be invalidated once, not
 twice; under the fixed-reference-set model this is automatic (the certificate
 is removed from $V$ once, and further deletions find it already absent), which
 is why this model — not bare idempotence — is the hypothesis on the
 context-update table.
- Provenance chains record individual steps in execution order; the final
 records agree only up to step ordering, or the batch form must record $S$ as a
 set.
- Mixed-type sets: state-level agreement is immediate per type, but cross-sector
 annotation transport is where an implementation would surface errors; 
 should include a mixed-type example.
- **Disposition.** The qualification below is confirmed: idempotence alone does
 not suffice. Adopt the **fixed-reference-set model** as the hypothesis
 replacing bare idempotence: each certificate carries
 $\operatorname{Ref}(c)$, with invalidation
 $V\mapsto V\setminus\{c : r\in\operatorname{Ref}(c)\}$. This family is
 pairwise commuting (the updates remove disjoint singletons for distinct $r$),
 idempotent, and its composition depends only on the deleted-identifier set —
 exactly what the annotation-transport conclusion needs. Bare-idempotence-only
 formulations are rejected; the abstract countermodel below is retained as the
 motivation. The hypothesis block above is restated accordingly. Scoping:
 annotation invalidation is a **future-$\Pi$** effect; the definition is to be
 recorded in
 [`STATE_MODEL.md`](STATE_MODEL.md) §1 (proposed
 field-type sketches) at the next revision — the §6 matrix itself is not
 extended in the MVP. The state-level (MVP projection) statement is untouched.
 The earlier "pending disposition" framing is superseded by this block.
- **Countermodel retained as motivation:** the
 extended-context / annotation-transport part of the conclusion is not
 supported by the idempotence hypothesis alone. Idempotence of annotation
 updates does not imply they commute. Abstract countermodel:
 $V\subseteq\{p,q\}$ valid certificates; $f(V)=V\setminus\{p\}$;
 $g(V)=V\setminus\{q\}$ if $p\in V$ else $V$; both $f$ and $g$ are idempotent
 and only invalidating, but from $\{p,q\}$: $(f\circ g)(\{p,q\})=\emptyset$
 while $(g\circ f)(\{p,q\})=\{q\}$.

---

## `OBL-ROW-REPLACEMENT-FACTOR` — Row-replacement factorization

**Taxonomy IDs:** `C-DELETE-CHECK`, `C-ADD-CHECK`. **`P-REBASE` removed
2026-10-11** by the split below; its residual obligation is
`OBL-REBASE-GENERATION`.

**Semantic-contract field:** `C-DELETE-CHECK` field 10 (partial inverse).

**Claim shape:** `equality`

**Evidence status:** `proved` for the loop (hand derivation
`spec/OPERATIONAL_SEMANTICS.md` §4.16, 2026-10-20) and for the generation
conjunct (hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.18, 2026-10-20,
with the classical citation recorded there), up to canonical identifier
allocation and `used`-set growth .

**Classification:** lemma

**Ledger status:** proved (loop in §4.16; generation conjunct in §4.18),
up to canonical identifier allocation and `used`-set growth . Worked
example `W7` ( §4.2) present and
re-evidenced 2026-09-26. **Split 2026-10-11.** The entry had three claims of two polarities: two computable over

the MVP primitives (the loop applies and restores the row space; it is *not* a
presentation identity), and one quantifying over `P-REBASE` ("the row-replacement
special case of `P-REBASE` factors through core moves… these generate all basis
changes"). The third is **not stateable**: `P-REBASE` has no grammar production
and is neither command nor quotient in the MVP
([`TERM_LANGUAGE.md`](TERM_LANGUAGE.md) §2), so it has no cases to
take cases of, and the contract row it would depend on is itself
`not-yet-defined` / `not-applicable`
([`CLAIMS.md`](CLAIMS.md), *Claim inventory*). It is
minted separately as `OBL-REBASE-GENERATION`. This entry keeps **the name and
the numbering**, so every existing citation remains correct: each of them cites
the delete/add loop or the generation result, both of which stay here. The cut
is between *"core moves generate the basis-change group"* (a statement about
`C-DELETE-CHECK` / `C-ADD-CHECK`, retained) and *"therefore `P-REBASE` does"*
(a statement about `P-REBASE`, deferred) — not between the loop and the
generation result.

**Intended mechanization status:** Lean lemma joining the and slices
after explicit authorization. **No longer an input to the Gate 6 `P-REBASE`
decision**: that dependency is now carried by `OBL-REBASE-GENERATION`.

**Statement.** Let $r$ be a displayed independent generator of one stabilizer
type in a well-formed presented CSS state, and let $s$ lie in the span of the
surviving displayed generators of the same type. Then `C-DELETE-CHECK` on $r$
followed by `C-ADD-CHECK` on $r+s$ (binary sum) is applicable, and the final row
space is the original row space with the displayed basis obtained by replacing
$r$ with $r+s$. The composite is a semantic loop: the code is unchanged and $k$
returns to its original value, while the presentation changes by the row
replacement $r \mapsto r+s$ with fresh row identifiers. The composite is **not** a
state identity: the final state carries a fresh row identifier and a strictly
larger `used` set.

**Hypotheses.**

- Well-formed phase-insensitive presented CSS state ; $r$ is displayed,
 independent, and of known type.
- $s$ is in the span of the displayed same-type rows other than $r$; $r+s$ is
 the characteristic-two sum.
- No intervening presentation operations; the deleted identifier is not reused
 for the added row.

**Conclusion.**

- The deletion is applicable by displayed independence; the addition is
 applicable because $r+s$ lies in the unchanged opposite-sector orthogonality
 complement and is independent of the surviving rows.
- The final row space spanned by the surviving rows and $r+s$ equals the
 original row space spanned by the surviving rows and $r$; the intermediate
 state has $k$ incremented by one and the final state has the original $k$.
- Row replacements generate elementary basis changes, and these generate all
 basis changes of a fixed row space over the binary field, up to row-identifier
 conventions. This conjunct is a statement about `C-DELETE-CHECK` /
 `C-ADD-CHECK` and is **retained here**; the identification of `P-REBASE`'s
 case set with it is `OBL-REBASE-GENERATION`, minted on the split above.

**Dependencies.** (applicability and inapplicability behavior of both
moves); the partial-inverse laws ( relational core); an worked example.

**Known edge cases and counterexamples.**

- Row-referencing certificates are invalidated at the deletion step even though
 the final code equals the original: the loop is information-losing at the
 context level, a counterexample to any claim that semantic identity preserves
 certificates.
- The loop is not a presentation identity: the new row receives a fresh
 identifier and provenance records a two-step history, a counterexample to
 deriving `P-REBASE` as a presentation operation rather than at the row-space
 level.
- $s = 0$ degenerates to delete-then-readd, the converse-order case of the partial-inverse law: it restores the row space and displayed supports, not the state (fresh identifier; `used` grows).
- If $s$ involves rows deleted elsewhere in a surrounding sequence, the
 hypotheses must be re-checked at the intermediate state; this links to
 `OBL-ORDER-INDEPENDENT-DELETION`.

---

## `OBL-REBASE-GENERATION` — Completeness of core-move generation of `P-REBASE`

**Taxonomy IDs:** `P-REBASE`.

**Semantic-contract field:** `P-REBASE` contract field 3 (the `P-REBASE` route
in [`CLAIMS.md`](CLAIMS.md), *Claim inventory*), now `transition-defined`
(§4.26).

**Claim shape:** `equality`

**Evidence status:** `proved` (hand derivation
`spec/OPERATIONAL_SEMANTICS.md` §4.26, 2026-10-23). The earlier reading, that
the second conjunct was not stateable, was superseded on 2026-10-23 when the
Gate 6 decision admitted `P-REBASE` as a conditional cell with the §2
transition. The result is evidence, not a machine-checked proof.

**Classification:** `lemma`.

**Ledger status:** discharged
`spec/OPERATIONAL_SEMANTICS.md` §4.26. **Minted 2026-10-11** (maintainer
decision) by splitting
[`OBL-ROW-REPLACEMENT-FACTOR`](#obl-row-replacement-factor--row-replacement-factor),
whose third claim mixed a statement about the core moves with a statement about
`P-REBASE`. The entry keeps the name and the number, so existing citations
remain correct. The "deferred, and out of scope" status recorded before the
Gate 6 decision is superseded; the obligation is in scope as the generative
claim about the admitted conditional cell.

**Intended mechanization status:** / rank-preservation slice, tracked by
. Machine-checked (Lean 4): rank preservation under
`rebaseMatrix_ok` — `sectorRank_rebaseState` and `stateK_rebaseState` in
`lean/CodeCalculus/RebaseRankSector.lean` (theorem depends on `propext`,
`Classical.choice`, `Quot.sound` only; no `sorry`/`native_decide`). The
mechanized result is rank preservation under `rebaseMatrix_ok`, not the
transformation-set equality stated by this obligation's conjunct 2; that
equality remains the hand derivation at `spec/OPERATIONAL_SEMANTICS.md`
§4.26.

**Statement.** Two conjuncts.

1. *(Stateable, classical; retained in `OBL-ROW-REPLACEMENT-FACTOR`.)* For a
 fixed row space $R$ of rank $m$ over the binary field, the group generated by
 row replacements $r \mapsto r+s$ — each realized as the
 `C-DELETE-CHECK` / `C-ADD-CHECK` loop — is the full basis-change group
 $\mathrm{GL}(m,2)$ acting on displays of $R$, up to row-identifier
 conventions.
2. *(Stateable since 2026-10-23.)* `P-REBASE`'s transformation set coincides
 with the basis-change group of a fixed row space, up to row-identifier
 conventions.

**Hypotheses.** Conjunct 1 needs $R$ fixed across the replacements and the
identifier conventions of I3; conjunct 2 needs the `P-REBASE` transition, which
§2 supplies for $M\in\mathrm{GL}(m,2)$ per sector.

**Conclusion.** Discharged by §4.26: conjunct 1 is proved at §4.18; conjunct 2
holds because the admitted transition's output rows are $V_\tau M$ for
$M\in\mathrm{GL}(m,2)$, so its transformation set is the basis-change group
per sector, modulo the canonical mint.

**Dependencies.** The `P-REBASE` contract (`transition-defined`, §4.26);
`OBL-ROW-REPLACEMENT-FACTOR` for conjunct 1; and .

**Known edge cases and counterexamples.**

- **The discharge is modulo minting.** It is a set identification, not an
 equivalence of labeled states: the loop and the rebase command emit different
 identifiers on distinct paths, and their outputs are not $\equiv$ (§4.26,
 *Not claimed*). Factorization of a semantically labeled derivation is
 `OBL-DERIVED-TERM-FACTORIZATION`, not this entry.
- **The pre-2026-10-23 reading is superseded.** Before the Gate 6 decision,
 `P-REBASE` had no grammar production and conjunct 2 could not be phrased;
 that reading is retained here only as history.
- **The MVP half is not evidence for this.** `W7` shows the loop is not a
 presentation identity ($A_3\not\equiv A$; `used` grows) — evidence against the
 presentation-level comparison, and nothing about the row-space-level
 identification.
- **'s `candidate` cap is unaffected.** This obligation is not the
 canonicalization transport that lifts the cap; that is
 `OBL-PRESENTATION-CONJUGATION` together with the judgment-transport condition
 in §4.

---

## `OBL-FIXED-NAMESPACE-REACHABILITY` — Fixed-namespace reachability and connectivity

**Taxonomy IDs:** `C-DELETE-CHECK`, `C-ADD-CHECK`, `C-SEQUENCE`

**Semantic-contract field:** not applicable as a per-operation contract claim;
metatheorem over the transition system. It grounds the fixed-namespace
reachability tier of §2.

**Claim shape:** metatheorem entry (explicit schema exception — see
[`CLAIMS.md`](CLAIMS.md) *Claim shape and evidence
status*.

**Evidence status:** `proved` (hand derivation `spec/OPERATIONAL_SEMANTICS.md`
§4.17, 2026-10-20).

**Classification:** metatheorem

**Ledger status:** proved (hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.17, 2026-10-20), scoped to the all-deletions-first route.

**Intended mechanization status:** Lean metatheorem after –; it is the
fixed-namespace reachability tier of §2 and a direct
input to Gate 7.

**Statement.** Let $C_0$ and $C_1$ be well-formed phase-insensitive CSS states
on the same finite qubit namespace. Then $C_1$ is reachable from $C_0$ by a
finite `C-SEQUENCE` of `C-DELETE-CHECK` and `C-ADD-CHECK` applications,
starting from any presentation of $C_0$ and reaching the **supports** of any
presentation of $C_1$ with canonically minted identifiers (disposition:
scoped to canonical identifier allocation; exact labeled reachability is out of
scope). At the level of row-space effects, the connecting path can be chosen
with all deletions first and all additions after.

**Hypotheses.**

- Both endpoints are well-formed (each sector's rows lie in the orthogonality
 complement of the other) over the same qubit namespace; the namespace is
 fixed, and `n`-changing moves of the `E-*` layer are out of scope.
- The phase-insensitive state model of ; the intersection of the $X$- and
 $Z$-row spaces need not be trivial (the glossary allows $Y$-type products).
- Basis adaptation along the path uses the row-replacement loop of
 `OBL-ROW-REPLACEMENT-FACTOR`.
- No metric requirement is imposed on the path.

**Conclusion.**

- Connectivity: the well-formed state space at fixed namespace is connected
 under the core row moves — a generation-completeness (reachability) result at
 fixed $n$.
- Explicit path: **superseded by the all-deletions-first route**
 (delete every displayed row to the zero state, then add all of $C_1$'s rows),
 which passes through the zero row space and needs neither basis adaptation
 nor cross-sector permutation. The earlier contraction-to-intersection path
 (contract to the intersection, then expand) is retained as a pointer only.
- Basis transitivity: any target presentation is reachable, since
 row-replacement loops generate all basis changes of a fixed row space over the
 binary field (as in `OBL-ROW-REPLACEMENT-FACTOR`), up to canonical identifier
 allocation (disposition, below).

**Dependencies.** `OBL-ROW-REPLACEMENT-FACTOR` (basis adaptation); cross-sector
conditional permutation (applicability of the contraction-first serialization);
; .

**Known edge cases and counterexamples.**

- The claim is structural only. Connecting paths may raise $k$ substantially —
 deletion phases raise $k$ — and may destroy distance entirely: a counterexample
 to reading this as distance-safe reachability. Distance-safe reachability is a
 strictly harder question, constrained by the hardness of exact distance
 ( §3.1).
 **Correction (review finding — adopted, disposition below):** $k$ is bounded at
 fixed $n$: since $X\subseteq Z^\perp$ implies $\dim X+\dim Z\le n$, every
 valid intermediate state has $0\le k\le n$. Path length and the number of
 oscillations may be unbounded; $k$ itself is not.
- When neither endpoint row space contains the other, no $k$-monotone path
 exists; any claim of monotone reachability is false.
 **Correction (review finding — adopted, disposition below):** the original
 parenthetical explanation ("the bridge forces a pass through the
 intersection") is false for arbitrary paths. Witness: on $Q=\{1,2\}$, $Z=0$,
 $X_0=\operatorname{span}\{1\}$, $X_1=\operatorname{span}\{2\}$: add an $X$-row
 on qubit 2, then delete the original row on qubit 1 — the path passes through
 $\operatorname{span}\{1,2\}$ and never through $X_0\cap X_1=0$, with $k$
 values $1,0,1$. What remains correct, and what the entry claims, is the
 nonexistence of a **monotone-$k$** path for incomparable endpoints: every
 non-skip command changes $k$ by exactly one, so monotonicity forces
 exclusively additions or exclusively deletions, which implies componentwise
 inclusion one way.
- The bridge may pass through extreme states, e.g. both row spaces trivial when
 the endpoint spaces intersect only at zero; well-formedness permits this.
- The hypotheses exclude `n`-changing moves (peeling, puncturing) and
 extended-state (subsystem) models entirely.
- **Disposition.** Both corrections above are adopted into the edge-case
 statements. The reachability claim is **scoped to canonical identifier
 allocation**, replacing the earlier "up to row-identifier conventions"
 phrase:

 - *Row-space-level reachability (adopted).* The all-deletions-first argument
 is valid: delete all displayed rows, add an independent target $X$ basis,
 then an independent target $Z$ basis; at most $2n$ commands. It requires an
 **infinite identifier enumeration** (recorded as an explicit assumption of
 this entry) with finite used history per path — guaranteed since each
 command mints exactly one identifier and paths are finite, so `used` stays
 finite (disposition).
 - *Endpoint comparison (made explicit).* The constructed path reaches the
 target basis **supports** with canonically minted identifiers — not an
 arbitrary assignment of target identifiers or retirement history. Claims
 about labeled endpoints must state which of the two they mean.
 - *Exact labeled reachability (out of scope).* It has a concrete obstruction:
 on $Q=\{1\}$, a source with an $X$-row on qubit 1 with identifier $a$ and a
 target with a $Z$-row on qubit 1 with identifier $a$ is unreachable even
 modulo $\approx$: no command changes a surviving identifier's sector and
 deletion retires permanently (I3). The conclusion's basis-transitivity
 clause is therefore read "up to canonical identifier allocation."
 - The weaker argument needs neither cross-sector permutation nor row
 replacement and makes no distance guarantee. The earlier "pending
 disposition" framing is superseded by this block.

---

## Inventory stubs

The entries below complete the inventory (work plan *Resolve* list and
relational-core table). They were **sharpened on 2026-09-23**, after the /
artifacts landed and the walkthrough rulings fixed the naming and comparison
conventions. Each statement is now precise and asserts no more than its `open`
evidence status licenses (no available argument yet).

**Sharpening conventions (fixed 2026-09-23).**

- $\equiv$ — observational equality of states: **identical `Q`, identical
 labeled rows, and identical `used`**, per [`STATE_MODEL.md`](STATE_MODEL.md)
 §2, which is the authority for equality; row order is not read, and `Q` is
 read as a set. The `steps` log may differ, being semantically inert
 ([`STATE_MODEL.md`](STATE_MODEL.md) §2, §5). Obligation statements quantify
 states modulo $\equiv$. The `Q` clause was added 2026-10-29;
 the three entries that conclude in $\equiv$ (`OBL-PRIMITIVE-DETERMINISM`,
 `OBL-FRAME-LAW`, `OBL-DIRECT-SUM-LAWS`) carry their re-evidence inline.
 **Corrected 2026-10-13.** This bullet previously read *"identical `Q`,
 `rows_*`, `id`, and `sector` fields"* and omitted `used`. That wording is
 fixed 2026-09-23 and **predates the disposition**, which made
 `used` semantic and put it inside $\equiv$. It is superseded and kept only for
 provenance; nothing may cite it. No obligation statement changes meaning — the
 rest of this file already read $\equiv$ in the corrected sense, citing `used`
 growth as what *breaks* equality in `OBL-ROW-REPLACEMENT-FACTOR`
 ($A_3\not\equiv A$) and `OBL-PARTIAL-INVERSE-LAWS` (add-then-delete endpoint
 not $\equiv$), and enumerating the `used` set among the unions in
 `OBL-DIRECT-SUM-LAWS`. This bullet was the sole outlier.
- $\approx$ — presentation equivalence: relabeling transport of qubits,
 displayed rows, identifiers, and sector labels (the research proposal (see REFERENCES.md)).
- Fresh identifiers are minted by the canonical rule (I3), so every MVP
 primitive is deterministic; displayed rows are finite unordered sets. The
 determinism claim made in this convention is discharged per primitive by
 `OBL-PRIMITIVE-DETERMINISM`.

The entries are ordered roughly by the plan's dependency order and preserve the
entry format above.

## `OBL-PRIMITIVE-DETERMINISM` — Functional update of every MVP primitive

**Taxonomy IDs:** `C-SKIP`, `C-DIRECT-SUM`, `C-DELETE-CHECK`, `C-ADD-CHECK`,
`C-SEQUENCE`.

**Semantic-contract field:** per-primitive fields 3 (state update) and 4
(presentation update) of the contract schema; admission rule item 2
(applicability domain).

**Claim shape:** `equality` — **Evidence status:** `proved` (hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.8, 2026-10-20).

**Classification:** metatheorem.

**Ledger status:** added 2026-09-30 (logical-framework panel, §5.3) — statement fixed; proof `open`. **** proved by hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.8; evidence status `proved`. The provenance of this entry differs from those
around it: it is **not** from the work plan's *Resolve* list or
relational-core table. It formalizes a commitment the cards and
[`STATE_MODEL.md`](STATE_MODEL.md) §3 already make, and
so does not depend on the pending logical-framework decision.

**Intended mechanization status:** one Lean lemma per primitive across the
– slices; input to Gates 2–4. The derivation system for the annotation
layer is `not-yet-defined` until Gate 5, so no judgment-level form is claimed
here.

**Re-evidenced 2026-10-29.** The equality now reads $Q$. Each
primitive's output is a function of the semantic input state and the term
(§4.8), so two outputs agree on $Q$ as on every other field, and the
conclusion $S_1'\equiv S_2'$ stands with the added clause; status unchanged.
Lean: `eval_deterministic` gives literal equality, which implies $\equiv$
(`codeStateEquiv_of_eq`).

**Statement.** For every MVP primitive $p$ — the commands `C-SKIP`,
`C-DELETE-CHECK`, `C-ADD-CHECK`, `C-SEQUENCE`, and the expression constructor
`C-DIRECT-SUM` (two-input, not a unary command) — and every well-formed input on
which $p$ is applicable, at most one output state is produced: if
$\operatorname{Eval}(p,S,S_1')$ and $\operatorname{Eval}(p,S,S_2')$ both hold
($\operatorname{EvalExpr}(e_1\oplus e_2,S_A\oplus S_B,S')$ for the constructor),
then $S_1'\equiv S_2'$. Equivalently, the transition relation of each MVP
primitive is functional on its applicability domain.

The obligation concerns **uniqueness of the output, not its existence**: an
inapplicable command has no output, which is not nondeterminism.

**Hypotheses.**

- $S$ satisfies I1–I5 ([`STATE_MODEL.md`](STATE_MODEL.md) §3).
- The applicability premises of the primitive's card
 ([`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §2) hold.
- Identifier allocation is canonical (I3): the mint is the first element of the
 fixed enumeration not in `used`, and no MVP primitive takes a mint parameter.
- Every MVP primitive is parameterised entirely by explicit term data, and its
 update is a function of that data together with the complete semantic input
 state. `used` is semantic and read by the mint; `steps` is semantically inert
 and read by no rule (inventory §3), so it cannot affect the output.

**Dependencies.** (inventory §2–§3, I3); per-primitive cards;
`OBL-CROSS-SECTOR-PERMUTATION` (its case 2 is order dependence, not
nondeterminism — canonical minting removes nondeterminism, not order dependence,
per the disposition); `OBL-DIRECT-SUM-LAWS` for the direct-sum laws, whose
value claim was corrected 2026-09-30 independently of this entry.

**Known edge cases and counterexamples.**

- `C-ADD-CHECK` takes no mint parameter: the fresh identifier is fixed by the
 canonical rule over `used`. Without I3 this obligation **fails** — that was
 review finding, and the disposition is what makes it
 hold. `Eval` is deterministic outright; there is no fresh-name choice.
- `C-DIRECT-SUM` is determined for an ordered pair once the qubit- and
 used-set-disjointness premises hold, since no renaming is performed. An
 identifier collision makes the constructor **inapplicable**, not
 nondeterministic (I3; `W15`). Corrected 2026-09-30: the card previously read
 "unique up to relabeling equivalence", which overstated the indeterminacy.
- `C-SEQUENCE` inherits determinism from its parts. When a middle command is
 inapplicable both bracketings are undefined together (`W10`) — a statement
 about the domain, not a counterexample.
- **What would falsify this.** An operation that must select among candidates
 with no canonical rule and no state field to select on. The admitted
 `E-GRAFT` transition declares its ordered row-chain in the term, so its
 operation-specific determinism is part of
 `OBL-GRAFT-TRANSITION-SOUNDNESS`. Remaining examples include `E-PUNCTURE`
 (repair choice) and `X-GAUGE-FIX` (gauge-set choice); neither may be admitted
 without declaring the choice in the term or fixing a canonical rule.

## `OBL-WELL-FORMEDNESS-PRESERVATION` — Output well-formedness of every primitive

**Taxonomy IDs:** `C-SKIP`, `C-DIRECT-SUM`, `C-DELETE-CHECK`, `C-ADD-CHECK`, `C-SEQUENCE`.

**Semantic-contract field:** admission rule item 4 (`state-sound`).

**Claim shape:** `preservation` — **Evidence status:** `proved` (MVP instances:
`C-SKIP`, `C-DELETE-CHECK`, `C-ADD-CHECK`, `C-DIRECT-SUM`, `C-SEQUENCE`);
`open` for the later-layer algebraic constructor instance admitted under
repair (a) (see above).

**Ledger status:** MVP instances proved by dated hand derivation
`spec/OPERATIONAL_SEMANTICS.md` §4.7; statement fixed against
the conventions above. The later-layer constructor instance remains `open`.

**Intended mechanization status:** one Lean lemma per – slice; input to
Gates 2–4. Machine-checked (Lean 4, `lean/CodeCalculus/WellFormedness.lean`,
, no `sorry`, no `native_decide`): the `C-SKIP`, `C-DELETE-CHECK`,
`C-ADD-CHECK`, and `C-SEQUENCE` instances, as `wf_deleteState` (any
deletion), `wf_addState` (under the `C-ADD-CHECK` premises), and `wf_of_eval`
(every evaluation of a graft-free command: sequencing by induction on the
evaluation, the Gate 6 cells through the well-formedness premise their
transitions carry). The `C-DIRECT-SUM` instance is mechanized as
`directSum_wellFormed`; the
graft's preservation (§4.12) is mechanized as `wf_graftState` and
`wf_graft_of_eval` (`lean/CodeCalculus/GraftWellFormedness.lean`, ,
no `sorry`, no `native_decide`) under the transition's premises, with I2
derived by rank counting from the `k`-preservation premise and the dimension
bound `ranksFit_of_wf` (`lean/CodeCalculus/RanksFit.lean`);
`wf_of_eval_all` there lifts preservation to every command. The rebase's
output well-formedness, which `Eval.rebase` carries as a premise, is derived
from the parent's well-formedness and the matrix's invertibility by
`wf_rebaseState` (`lean/CodeCalculus/RebaseWellFormedness.lean`, ,
no `sorry`, no `native_decide`), so that premise is redundant for the rebase
(`eval_rebase_of_wf`); the other four Gate 6 transitions keep theirs as
premises. The later-layer constructor instance is not mechanized. Evidence
status unchanged.

**Scope widened 2026-10-05).** This obligation was previously scoped to the five MVP primitives only. With
repair (a) adopted, a later-layer algebraic constructor returning an **independent
display** has a well-formedness obligation too, and that instance is now **live and
unproved**. Two things follow, and neither is a discharge:

- The MVP instances are **unchanged** by this disposition — I2/I5 and the
 `C-ADD-CHECK` independence premise were preserved precisely by choosing (a) over
 (b).
- **Choosing the repair is not proving it.** This entry's evidence status stays
 `open` for the MVP instances and gains a further `open` instance for the
 constructor. The question "does the repaired output satisfy I1–I5?" is a proof
 obligation, not a consequence of the signature decision recorded in
 `spec/TERM_LANGUAGE.md` §2.
 The MVP instances are now proved (§4.7, 2026-10-20); the constructor
 instance remains open. The earlier "stays open for the MVP instances" framing
 is superseded by this block.

The constructor's **admission** remains a Gate 7 question; this obligation records
what would have to be discharged if it is admitted, and is not itself an
admission.

**Statement (restated per the  disposition).** For each MVP *command*
(`C-SKIP`, `C-DELETE-CHECK`, `C-ADD-CHECK`, `C-SEQUENCE`) and every applicable
transition $\operatorname{Eval}(\mathit{op},S,S')$, and for the expression
constructor `C-DIRECT-SUM` every applicable two-input judgment
$\operatorname{EvalExpr}(e_1\oplus e_2,\ S_A\oplus S_B)$ (it is not a unary
command), the output satisfies `WellFormedCSS`: invariants I1–I5 hold of $S'$
after the field updates of
[`STATE_MODEL.md`](STATE_MODEL.md) §4.

**Disposition.** The original
one-$\operatorname{Eval}$ form quantified over a unary judgment that direct sum
does not have; the restated statement splits the two judgment forms, matching
the `C-DIRECT-SUM` card's worked derivation shape
([`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §2). The earlier
"well-formedness preservation scope" qualification at
 is superseded
by this block.

**Hypotheses.** $S$ satisfies I1–I5; the applicability premises of the
primitive's card ([`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §2) hold.

**Dependencies.** (`spec/STATE_MODEL.md §3`); cards.

**Known edge cases and counterexamples.**

- Deletion cannot violate $X\perp Z$ (removing rows shrinks a row space);
 addition relies on its opposite-sector commutation premise; direct sum on
 qubit- and identifier-disjointness (`W15`).

## `OBL-SKIP-IDENTITY` — Skip identity

**Taxonomy IDs:** `C-SKIP`, `C-SEQUENCE`.

**Claim shape:** `equality` — **Evidence status:** `proved`.

**Classification:** metatheorem.

**Ledger status:** sharpened 2026-09-23 — statement fixed against the
conventions above; **proof discharged
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4. The evidence status
moves `open` → `proved` because a derivation is now in this repository
(`AGENTS.md`, *Claim-status discipline*: `proved` is the evidence status,
`established` its proposal-side tag). **No promotion occurs here**: `promoted` is
a review disposition requiring an independent review and maintainer confirmation
(`AUTHORITY.md` §B1–§B2), and the claim is `proved` and not yet `promoted` — the
normal state. The derivation is re-derived mechanically in the slice
(*Intended mechanization status*).

**Intended mechanization status:** Lean theorem in the slice; Gate 3 input.

**Statement.** For every command $m$ and well-formed $S$:
$\operatorname{Eval}(m,S,S')$ holds if and only if
$\operatorname{Eval}(\operatorname{skip};m,S,S'')$ if and only if
$\operatorname{Eval}(m;\operatorname{skip},S,S''')$, where $S''$ and $S'''$
agree with $S'$ up to $\equiv$ (they add only a `skip` record to `steps`).

**Hypotheses.** $m$ well-typed; $S$ satisfies I1–I5.

**Dependencies.** (`C-SEQUENCE` card).

**Known edge cases and counterexamples.**

- $\operatorname{skip};\operatorname{skip}$ is the degenerate case; the `steps`
 records differ across the three forms, which is why the statement is modulo
 $\equiv$.

## `OBL-SEQUENCE-ASSOCIATIVITY` — Sequencing associativity and denotational adequacy

**Taxonomy IDs:** `C-SEQUENCE`.

**Claim shape:** `equality` — **Evidence status:** `proved` (hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.8, 2026-10-20).

**Classification:** metatheorem.

**Ledger status:** proved (hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.8, 2026-10-20).

**Intended mechanization status:** Lean theorem in the slice; Gate 3 input.

**Statement.** $(m_1;m_2);m_3\equiv m_1;(m_2;m_3)$ as partial state
transformers — literally equal, `steps` included, since step-log concatenation
is associative — and the big-step relation is adequate for the conventional
left-to-right reading (the research proposal (see REFERENCES.md): associativity and denotational adequacy are
proof obligations, not assumed equations).

**Note.** The denotation the adequacy half is stated
against is the derived denotation at
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §1a:
$\llbracket m\rrbracket(S) = \mathsf{some}\ S'$ iff
$\operatorname{Eval}(m,S,S')$. This note adds the pointer only; the
obligation's status is unchanged.

**Hypotheses.** Well-typed commands; $S$ satisfies I1–I5.

**Dependencies.** (`C-SEQUENCE` card).

**Known edge cases and counterexamples.**

- When a middle command is inapplicable, both bracketings must be undefined
 together (`W10`).

## `OBL-CROSS-SECTOR-PERMUTATION` — Cross-sector conditional permutation

**Taxonomy IDs:** `C-DELETE-CHECK`, `C-ADD-CHECK`, `C-SEQUENCE`.

**Claim shape:** `equality` — **Evidence status:** `proved` (hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.10, 2026-10-20).

**Classification:** metatheorem.

**Ledger status:** proved (hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.10, 2026-10-20).

**Disposition.** The three-case analysis is confirmed non-exhaustive. Adopt the
missing fourth case rather than strengthen the equivalence: the outputs of case
2 differ only in canonical identifier allocation, and no admitted equivalence
identifies them — $\equiv$ requires identical labeled rows, and $\approx$
transports sector labels with their rows (relabeling preserves sectors), so the
identifier-to-sector assignment is invariant under both. Making them equivalent
would require quotienting identifier allocation, contradicting the ratified
identifier-visibility ruling. Canonical minting removes
nondeterminism, not order dependence. The statement below is restated
accordingly; the earlier "pending disposition" correction is superseded by this
block.

**Intended mechanization status:** Lean theorem joining the / slices with
; input to Gate 5 judgment transport.

**Statement (restated per the disposition).** For commands $m_1, m_2$ whose
applicability on any state is order-independent, exactly one of the following
holds for $m_1;m_2$ and $m_2;m_1$:

1. both apply and the outputs are $\equiv$-equal;
2. both apply and the outputs are **not** $\equiv$- or $\approx$-related —
 under the canonical mint this arises exactly when both orders are applicable
 but the identifier-to-sector allocation differs;
3. exactly one order applies (identifying which);
4. neither applies.

The characterization must show every pair falls into exactly one case and
identify side conditions $\Pi(m_X,m_Z,S)$ that select case 1 over case 2.

**Hypotheses.** $m_X$ and $m_Z$ are single MVP commands of opposite sector type
over the same well-formed $S$; applicability as in the cards
([`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §2).

**Dependencies.** ; `OBL-SEQUENCE-ASSOCIATIVITY`.

**Known edge cases and counterexamples.**

- `W8` is case 3 (the earlier case (b)): one order applies and the other has
 no derivation. Any candidate $\Pi$ must classify this pair correctly.
- **Counterexample (review finding) — now the case-2 witness:** $Q=\{1,2\}$, no
 displayed rows, no used identifiers; $m_X$ adds an $X$-row on qubit 1 and
 $m_Z$ adds a $Z$-row on qubit 2. Both orders apply; $m_X;m_Z$ allocates
 $(X,1)\mapsto i_0,(Z,2)\mapsto i_1$ and $m_Z;m_X$ the swap. The outputs are
 neither $\equiv$ (the identifier-to-sector assignments differ) nor $\approx$
 (qubit relabeling preserves sector labels and identifiers). Retained as the
 motivating witness for case 2.
- The earlier "required correction" bullet (add the fourth case, or weaken the
 comparison) is superseded by the disposition above: the fourth case is
 adopted.

## `OBL-PARTIAL-INVERSE-LAWS` — Partial-inverse laws

**Taxonomy IDs:** `C-ADD-CHECK`, `C-DELETE-CHECK`.

**Claim shape:** `equality` — **Evidence status:** `proved` (hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.9, 2026-10-20).

**Classification:** lemma.

**Ledger status:** sharpened 2026-09-23 — statement fixed against the conventions above; proof `open`. **** proved by hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.9; evidence status `proved`.

**Intended mechanization status:** Lean lemmas joining the and slices;
input to the `C-DELETE-CHECK` partial-inverse contract field.

**Statement.** `C-ADD-CHECK` followed by `C-DELETE-CHECK` on the added row
restores the displayed rows and row space exactly (the endpoint differs from
the start only in `used` and `steps`; see the identifier-history edge case
below); the converse order restores the row space and displayed rows but mints
a fresh identifier (I3), so it fails
$\equiv$-identity exactly by the renaming the ratified identifier-visibility
reading forbids. Multiplicity is recorded.

**Correction (disposition, 2026-09-26).** Under the disposition the
add-then-delete clause is **not** a state identity: the endpoint's `used` set
strictly grows (the minted identifier is retired but retained), and $\equiv$
now requires identical `used`. The clause holds as an identity of displayed
rows and row spaces only; any state-level identity claim is dropped. This
correction is in force; the statement above has been aligned with it.

**Hypotheses.** Retained-row provenance data (`steps`,
[`STATE_MODEL.md`](STATE_MODEL.md)); identifier
non-reuse and the canonical mint (I3).

**Dependencies.** ; provenance rules; `OBL-ROW-REPLACEMENT-FACTOR`.

**Known edge cases and counterexamples.**

- The $s=0$ degenerate case of the row-replacement loop (`W7`) is the converse-order case: row space and displayed supports are restored, the state is not.
- Fresh identifiers make the inverse non-unique: the presentation is not
 recovered without retained data.
- Identifier history (review finding — RESOLVED, disposition 2026-09-26): the
 add-then-delete endpoint is **not** $\equiv$ to the start: retirement is
 recorded semantically in `used` (which strictly grows), and $\equiv$ requires
 identical `used`. The clause is therefore read as an identity of displayed
 rows and row space, not of states; the earlier "pending disposition"
 qualification is superseded by the correction above.

## `OBL-FRAME-LAW` — Frame law for direct-sum blocks

**Taxonomy IDs:** `C-DIRECT-SUM`, `C-DELETE-CHECK`, `C-ADD-CHECK`, `C-SEQUENCE`.

**Claim shape:** `equality` — **Evidence status:** `proved` (deletion clause); `conditional` (addition clause, subject to the allocation-compatibility premise) — hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.9, 2026-10-20.

**Classification:** lemma.

**Ledger status:** proved (hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.9, 2026-10-20).

**Disposition.** The addition clause is confirmed false as written (additions
take typed vectors, not live generator identifiers). Adopt the **split** into a
 deletion clause and a conditional addition clause with different hypothesis
shapes, rather than a weakened uniform statement. The disposition
supplies what the review observation said was missing: `used` is semantic and
`C-DIRECT-SUM` disjointness is over complete used-sets, so the historical
variant below is either rejected at the sum or handled by the
allocation-compatibility premise. The statement below is restated accordingly;
the earlier "pending disposition" correction is superseded by this block.

**Intended mechanization status:** Lean lemma joining with –; input to
 composition judgments. Machine-checked (Lean 4,
`lean/CodeCalculus/KernelObligations.lean`, no `sorry`, no `native_decide`):
the deletion clause at the state level, `frame_law_delete_left` and
`frame_law_delete_right`; the addition clause, `frame_law_add`: applicability splits per block (`frame_law_add_applicable_iff`)
and, under the premise `canonicalMint (A.used ++ B.used) = canonicalMint
A.used`, the result is `A' ⊕ B` up to `≡` (`frame_law_add_equiv`), with
`A' ⊕ B` a derivable direct sum (`frame_law_add_directSum_evalExpr`). The
premise is characterized by `canonicalMint_append_eq_iff` and shown necessary
by the two-state witness `frame_law_add_needs_mint_premise`. Hypotheses beyond
the `C-DIRECT-SUM` premises: the candidate support lies in $Q_A$, and the
displayed supports of each summand lie in that summand's namespace (a conjunct
of well-formedness, taken on its own). Evidence status unchanged: this is
mechanization progress, not a status upgrade.

**Re-evidenced 2026-10-29.** The equality now reads $Q$. The
deletion clause is a literal equality of states (`frame_law_delete_left`,
`frame_law_delete_right`); in the addition clause both sides have namespace
$Q_A\sqcup Q_B$, since `addStab` keeps the namespace and the sum unions it, so
`frame_law_add_equiv` carries the new clause by reflexivity and the status is
unchanged.

**Statement (restated per the disposition).**

- **Deletion clause (unconditional).** $\operatorname{delete}_r$ with $r$ a
 displayed row of $A\oplus B$ is applicable iff $r$ is displayed in exactly one
 summand, and then $\operatorname{Eval}(\operatorname{delete}_r,\ A\oplus B,\
 C_A'\oplus B)$ where $C_A'$ is the summand's deletion result. Proof shape:
 displayedness and independence are per-block; the used-set bookkeeping is
 per-block (the retired identifier stays in the owning summand's `used`).
- **Addition clause (conditional).** $\operatorname{addStab}_r$ with
 $\operatorname{supp}(r)\subseteq Q_A$ is applicable on $A\oplus B$ iff it is
 applicable on $A$ (orthogonality and membership split per block because $r$
 annihilates $Z_B$ and cannot meet $X_B$), and then the result is $A'\oplus B$
 **provided the allocation-compatibility premise holds**:
 $\operatorname{mint}(\mathsf{used}_A)\notin\mathsf{used}_B$, equivalently
 $\operatorname{mint}(\mathsf{used}_A\cup
 \mathsf{used}_B)=\operatorname{mint}(\mathsf{used}_A)$, so the sum's mint
 equals the summand's mint. Every identifier before
 $\operatorname{mint}(\mathsf{used}_A)$ in the fixed enumeration lies in
 $\mathsf{used}_A$, so under used-set disjointness the premise says that
 $\mathsf{used}_B$ starts strictly after $\operatorname{mint}(\mathsf{used}_A)$.
 Without the premise the sums are still applicable
 but mint differently: the clause fails, which is why it is a hypothesis, not
 a bug.

**Hypotheses.** `C-DIRECT-SUM` premises on both sides (qubit- and
identifier-disjointness, [`STATE_MODEL.md`](STATE_MODEL.md) §4).

**Dependencies.** `OBL-DIRECT-SUM-LAWS`; `OBL-WELL-FORMEDNESS-PRESERVATION`.

**Known edge cases and counterexamples.**

- A move naming a row of the other summand must be inapplicable blockwise.
- **Counterexample (review finding) — retained as the motivation for the
 addition clause's hypotheses:** additions accept typed vectors, not live
 generator identifiers. Witness: empty $A$ on $\{1\}$, empty $B$ on $\{2\}$;
 adding an $X$-row on qubit 12 to the sum is applicable but names no displayed
 row of either summand; even a local addition of an $X$-row on qubit 1 to empty
 $A$ applies while naming nothing.
- **Historical variant (review finding):** $B$ with no live rows but a retired
 $i_0$ makes the right-hand sum either rejected or differently-identified
 under either reading of collision. Under the disposition this variant is
 resolved: used-set disjointness rejects the colliding sum outright, and the
 non-colliding case is governed by the allocation-compatibility premise.
- The earlier "required correction" bullet (split into deletion and addition
 clauses with support-locality and allocation-compatibility hypotheses) is
 superseded by the disposition above: the split is adopted.
- **Historical variant (review finding):** $B$ with no live rows but a retired
 $i_0$ makes the right-hand sum either rejected or differently-identified
 under either reading of collision.

## `OBL-PRESENTATION-CONJUGATION` — Presentation conjugation and relabeling congruence

**Taxonomy IDs:** `P-RELABEL`, `P-REBASE`.

**Claim shape:** `equality` — **Evidence status:** `proved` (hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.25, 2026-10-23).
**Classification:** metatheorem.

**Ledger status:** proved (hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.25, 2026-10-23).

**Disposition.** The same-command congruence is confirmed false for additions.
Adopt the **transported-command congruence**: deletions are identifier-stable,
additions must transport the support ($\sigma m$), and expression congruence is
scoped to relabelings that preserve the summand decomposition. The statement
below is restated accordingly; the earlier "pending disposition" correction and
the separate expression-congruence qualification are superseded by this block
(the scoping is absorbed into the statement).

**Intended mechanization status:** Lean metatheorem after –; input to
Gate 6.

**Statement (restated per the disposition).** For a permitted qubit
relabeling $\sigma$ with $\tilde S=\sigma S\approx S$:

- **Deletions (identifier-stable).** $\operatorname{Eval}(\operatorname{delete}_r,
 S, S')$ iff $\operatorname{Eval}(\operatorname{delete}_r, \tilde S,
 \widetilde{S'})$, with the same identifier $r$ on both sides: identifiers
 transport with their rows, and displayedness/independence are
 relabeling-invariant.
- **Additions (support-transported).** $\operatorname{Eval}(\operatorname{addStab}_r,
 S, S')$ iff $\operatorname{Eval}(\operatorname{addStab}_{\sigma r}, \tilde S,
 \widetilde{S'})$, where $\sigma r$ is the transported support vector. The
 transported command **must** be used; minted identifiers agree because
 relabeling leaves `used` unchanged.
- **Sequences and skip** compose pointwise from the two clauses.
- **Expression congruence (scoped).** For $\oplus$, the congruence holds for
 relabelings applied uniformly to the whole sum: a global bijection preserves
 disjointness ($\sigma Q_A\cap\sigma Q_B=\sigma(Q_A\cap Q_B)$), and used-set
 disjointness is label-invariant. Per-summand relabelings are covered by
 composing with the sum's embedding. Relabelings that cut across a summand
 boundary are outside the congruence's scope; this scoping is part of the
 disposition.

`P-REBASE` remains deferred in the MVP: its clause cannot be exercised until
support-sensitive applicability is formalized.

**Hypotheses.** The presentation equivalence of the research proposal (see REFERENCES.md); the
identifier-visibility reading, ratified at the walkthrough.

**Dependencies.** `OBL-DIRECT-SUM-LAWS`; .

**Known edge cases and counterexamples.**

- `W11` records the ratified reading and its rejected alternative.
- **Counterexample (review finding) — retained as the motivation for the
 transported-command form:** the congruence with the same command $m$ on both
 sides fails for additions. Witness: $S$ on $\{1,2\}$ has only a $Z$-row on
 qubit 1 with identifier $b$; $\sigma$ swaps qubits 1 and 2;
 $S\approx\sigma S$; the command $m$ adding an $X$-row on qubit 2 applies to
 $S$ ($2\cdot 1=0$) but fails on $\sigma S$ ($2\cdot 2=1$).
- The earlier "required correction" (transport $\sigma m$) and "additional
 qualification" (expression-congruence scoping) bullets are superseded by the
 disposition above: the transported-command form is adopted and the scoping is
 absorbed into the statement.
- `P-REBASE` is deferred in the MVP: its clause of the obligation cannot be
 exercised until support-sensitive applicability is formalized.

## `OBL-DIRECT-SUM-LAWS` — Direct-sum laws

**Taxonomy IDs:** `C-DIRECT-SUM`.

**Claim shape:** `equality` — **Evidence status:** `proved` (hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.8, 2026-10-20).

**Classification:** metatheorem.

**Ledger status:** proved (hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.8, 2026-10-20).

**Intended mechanization status:** Lean theorem in the slice; Gate 3 input.

**Re-evidenced 2026-10-29.** The equality now reads $Q$;
$Q_A\sqcup Q_B$ is a set union, associative and commutative, so both laws
stand with the added clause and the status is unchanged. Lean now carries
commutativity up to $\equiv$ (`directSum_comm_equiv`) and associativity up to
$\equiv$ (`directSum_assoc_equiv`), where before it stated only the three list
permutations.

**Statement.** On unordered presentations with the disjointness premises, direct
sum is associative and commutative as **literal equality** of states
($\equiv$): $Q$, the displayed rows, the `id` assignment, the `sector` labels, and
the `used` set are each set unions of disjoint sets, so
$(C_A\oplus C_B)\oplus C_C\equiv C_A\oplus(C_B\oplus C_C)$ and
$C_A\oplus C_B\equiv C_B\oplus C_A$. No relabeling is involved — each summand's
rows keep their own identifiers, sectors, and supports, and a summand's embedding
into the disjoint union is the identity on that summand. Separately, the
structural judgments of §7.1 respect $\approx$ (relabeling congruence), which is a
statement about presentation equivalence and not about the direct-sum laws.

**Disposition.**
This statement previously opened "Direct sum is associative and commutative up to
$\approx$", citing the research proposal (see REFERENCES.md), which said the laws hold "not by literal equality
of labeled states". The two artifacts disagreed, and this entry also disagreed
with itself: its next sentence already said both bracketings and both orders
"literally agree". Resolved in favour of literal equality, on the ground that the
$\approx$ wording is a vestige of the pre- matrix presentation, where a row
permutation was the only difference a relabeling could absorb. 's collection
convention (inventory §2: displayed rows are unordered sets, so state identity does
not depend on row order or matrix layout) removed that need, and the second
sentence of this entry already reflects the corrected view — so this was stale
propagation from a design change rather than a mathematical disagreement. Proposal
§3.2 is corrected in the same change. The $\approx$ clause on the structural
judgments is **retained**. `W14`, which already checks the laws at $\equiv$, is
unaffected and no longer in tension with this entry; the equivalence level recorded
in the qualification below is superseded by this disposition.

**Equivalence level (logical-framework panel, 2026-09-30 — recorded, then
dispositioned the same day). Superseded by the disposition above; retained as the
record of the disagreement, per `AGENTS.md`.** Two normative artifacts stated
these laws at different equivalence levels, and the direct-sum determinism
correction initially declined to choose between them:

- this entry: on unordered presentations with the disjointness premises, "both
 bracketings and both orders **literally agree** up to the summand embeddings'
 relabeling";
- an archived internal note
 §3.2: "Direct sum is associative and commutative up to this explicit
 relabeling equivalence, **not by literal equality of labeled states**."

On disjoint namespaces the summand embeddings are the identity on each summand,
so no relabeling is available to absorb and the two statements do not agree.
Evidence pointing toward literal equality: displayed rows are unordered sets
whose order does not affect state identity
([`STATE_MODEL.md`](STATE_MODEL.md) §3, *Collection
convention*); the `used`-set union is order-independent (I3); and `W14` checks
associativity and commutativity at $\equiv$. Evidence the other way: no field is
named whose presentation could differ. The statement above is left verbatim
pending a dated . The separately-corrected claim that the
value of $C_A\oplus C_B$ for an ordered pair is determined does not depend on
this question; see [`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §2,
`C-DIRECT-SUM`. **Resolution:** the ledger and the research proposal (see REFERENCES.md) are brought into
agreement with each other and with 's collection convention by the disposition
above, which fixes the laws at $\equiv$.

**Hypotheses.** Qubit- and identifier-disjointness at each $\oplus$
([`STATE_MODEL.md`](STATE_MODEL.md) §4); 
presentation equivalence.

**Dependencies.** ; `OBL-WELL-FORMEDNESS-PRESERVATION`.

**Known edge cases and counterexamples.**

- `W14` agrees with the statement but is not proof.
- `W15` shows disjointness is a premise, not a consequence.

## `OBL-JUDGMENT-TRANSPORT` — Judgment transport through sequences

**Taxonomy IDs:** `C-SEQUENCE`.

**Semantic-contract field:** not applicable as a per-operation contract claim;
metatheorem over the transition system.

**Claim shape:** `preservation` — **Evidence status:** `proved` (hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.11, 2026-10-20).

**Classification:** metatheorem.

**Ledger status:** proved (hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.11, 2026-10-20).

The shape is `preservation` (established judgments survive sequencing), not the
reserved evidence status `not-applicable` — review finding, dispositioned
2026-09-26.

**Intended mechanization status:** Lean metatheorem in the slice; input to
Gate 5. First slice landed 2026-10-27, 
(`lean/CodeCalculus/Transport.lean`; no `sorry`, no `native_decide`;
`propext`, `Classical.choice`, and `Quot.sound` only). Positive half: two
valid chains sharing their seam state compose to a valid chain
(`chain_append`); a derivation over either segment is a derivation over the
composed chain, unchanged for the first segment and with every atom position
shifted past it for the second (`Derives.weaken`, `Derives.shift`); and the
seam compositions of §4.11 are theorems (`transport_eq_eq` for equalities by
substitution, `transport_le_le_down` and `transport_le_le_up` for one-sided
bounds of one polarity, `transport_le_eq` and `transport_eq_le` for the mixed
chains), closed by `judgment_soundness` on the composed chain
(`transport_models`). The schema-composition condition is, in that encoding,
position bookkeeping: a sentence derived over a segment mentions chain
positions of that segment. Fixed-reference-set model (§4.15): over an
arbitrary certificate type with reference sets, deletion-wise invalidation is
pairwise commuting and idempotent, and its composition depends only on the
deleted identifiers as a set (`invalidate_comm`, `invalidate_idem`,
`invalidateAll_set_determined`, `invalidateAll_perm`); a certificate that
refers to a deleted identifier is absent from the transported context
(`not_mem_invalidateAll_of_ref`), and one that refers to none survives
(`mem_invalidateAll_of_survives`). `W13` shape: a sentence false of a
well-formed chain has no derivation over it (`not_derivable_of_false`); on a
delete-then-add chain the two one-sided distance bounds are derivable and
neither composite bound is (`not_derivable_mixed_le`,
`not_derivable_mixed_ge`), and no equality between distance atoms at two
positions is derivable in a chain without an identity step, for any choice of
the measure (`not_derivable_distance_eq`). Not mechanized: the
derivation-level `W13` half proper, because the slice's sentence language has
no claim that refers to a generator, and adding one is an assertion-language
extension ( §4, Reading II); and the connection of
the fixed-reference-set model to `Eval`, since no normative artifact fixes
what a non-deletion command does to a context. Each refutation is relative to
the slice's `Derives` inventory: no derivation closes, not none can (F7
disposition, second cost).

**Statement.** Structural judgments compose through valid sequences; a claim
that refers to a deleted generator is not transported automatically (proposal
§4 judgment transport).

*Instance reading (2026-10-28).* The positive half is restated as the
composition schema (S1, `JUDGMENT_LAYER.md` §7.2.4) and the interval
composition theorem (S2, §8.5); verdict monotonicity is S3 §9.2. No status
change.

**Hypotheses.** Persistence conditions on annotations (the research proposal (see REFERENCES.md)); the
annotation-invalidation design of the future context inventory.

**Dependencies.** ; `OBL-SEQUENCE-ASSOCIATIVITY`;
`OBL-ORDER-INDEPENDENT-DELETION` (annotation-transport part; per the 
disposition there, proposed 2026-09-26, the transported-context conclusion
rests on the fixed-reference-set model — pairwise commuting, set-determined
invalidation — rather than on bare idempotence).

**Known edge cases and counterexamples.**

- `W13`: claims about deleted rows are unavailable as transported claims, which
 must not be confused with falsity.
- **Open question (F7, recorded 2026-10-05) — superseded 2026-10-11** by the
 F7 disposition recorded in ; expressibility settled
 there. Kept as a pointer, not deleted, per `AGENTS.md`.

## `OBL-DERIVED-TERM-FACTORIZATION` — Factorization of derived terms

**Taxonomy IDs:** future derived commands over `C-SKIP`, `C-DIRECT-SUM`,
`C-DELETE-CHECK`, `C-ADD-CHECK`, `C-SEQUENCE`.

**Semantic-contract field:** contract schema item on factorization for derived
operations.

**Claim shape:** `equality` — **Evidence status:** `proved` (hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.23, 2026-10-23).

**Classification:** metatheorem.

**Ledger status:** proved (hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.23, 2026-10-23).

**Intended mechanization status:** Lean metatheorem after –; Gate 6 input.

**Statement.** Every later derived command must be proved equivalent to its
sequence of elementary commands before admission (the research proposal (see REFERENCES.md) factorization),
where equivalence is $\equiv$ or $\approx$ as the derived signature indicates
and mints are canonical (I3). Instances already identified: multi-row deletion
as a batch operation (`spec/TAXONOMY.md` §2.3, via
`OBL-ORDER-INDEPENDENT-DELETION`) and the row-replacement loop
(`OBL-ROW-REPLACEMENT-FACTOR`).

**Hypotheses.** The derived command's signature and its equivalence notion are
fixed at admission time.

**Dependencies.** `OBL-ORDER-INDEPENDENT-DELETION`; `OBL-ROW-REPLACEMENT-FACTOR`;
`OBL-SEQUENCE-ASSOCIATIVITY`.

**Known edge cases and counterexamples.**

- Factorization is at the row-space level for row replacement; provenance
 behavior need not factor (`OBL-ROW-REPLACEMENT-FACTOR` edge cases).

## `OBL-CERTIFICATE-PATH-KEYING` — Certificate-path keying and checker route-scoping

**Taxonomy IDs:** not applicable — no MVP operation; a framework-level question.

**Semantic-contract field:** the reserved `certificate-checked` path of
[`CLAIMS.md`](CLAIMS.md) (*Reserved future status*).

**Claim shape:** `definition` — **Evidence status:** `proved`.

**Classification:** framework metatheorem (Gate 5 input).

**Ledger status:** minted 2026-10-05 by the framework ratification; statement
fixed, discharged at `spec/OPERATIONAL_SEMANTICS.md` §4.24; the three Gate 5 questions §4.24 lists stay open. Not
from the work plan's *Resolve* list or its relational-core table.

**Provenance.** Carried from the logical-framework panel's *Owed to the next
reader* item 3: the **certificate-path keying** (§8.2) and the **route-scoping a
checker would have to enforce** (§8.4) were deferred to Gate 5 rather than
answered. The 2026-10-05 ratification (
§9) adopts the framework while deferring these questions, so they are recorded
here as obligations rather than left as loose notes.

**Statement.** For the reserved `certificate-checked` path: (i) *keying* — what
identifies the instance a certificate speaks for, and what makes a certificate
evidencing one instance incapable of supporting an operation-contract claim;
(ii) *route-scoping* — the obligation a checker must discharge to establish that
a claim labelled `unavailable` on one route is not derivable on another.  fixed
that `certificate-checked` attaches to per-state atomic judgments and never to an
operation contract; that distinction is the typing discipline this obligation
must make checkable.

**Hypotheses.** The schema-versus-instance typing (the  route-scoping of `unavailable`; the ratified D2 discipline.

**Dependencies.** ; the ratified framework (D1, D2); the
`OBL-CERTIFICATE-PATH-KEYING` statement is a Gate 5 input and is **not** a
prerequisite for –.

**Known edge cases and counterexamples.** None yet recorded — the claim shape
is `definition`, and the three Gate 5 questions §4.24 defers are recorded
there as `open` rather than `conjectural`.

**What is settled, and what is still Gate 5 work (entry minted 2026-10-05).**
Two questions about the `certificate-checked` path were open before
this entry existed: the **certificate-path keying** and the **route-scoping a
checker must enforce**. Ratification settled neither; §4.24 discharges both halves and sets the evidence status above.
Concretely, still
owed at Gate 5:

- What identifies the instance a certificate speaks for, such that a certificate
 evidencing **one** instance can never support an **operation-contract** claim.
  fixed the schema-versus-instance distinction, and §4.24 writes the keying
 (the instance triple $(C, P, \sigma)$); whether that is the intended keying
 remains a Gate 5 decision.
- What a checker must discharge to establish that a claim labelled `unavailable`
 on one route is not derivable on another. Note that D2 (§6 distance opacity) and
 this route-scoping question interact: opacity forbids a rule from *computing* a
 distance, while route-scoping asks how the *absence* of such a derivation is
 verified. These are different obligations and neither discharges the other.
 §4.24 answers this half by re-running the derivability check on the other
 route; whether a checker must additionally discharge a non-derivability
 proof, and whether `certificate-checked` ever gains an operation-contract
 variant, remain Gate 5 decisions.

**Intended mechanization status:** none at MVP. It is not part of the W0–W16
acceptance surface, and no `C-*` card carries an `Underivability` entry for it,
because no MVP operation uses a certificate.

## `OBL-JUDGMENT-SOUNDNESS` — Annotated-judgment soundness

**Taxonomy IDs:** `C-SKIP`, `C-DIRECT-SUM`, `C-DELETE-CHECK`, `C-ADD-CHECK`,
`C-SEQUENCE`.

**Semantic-contract field:** every claimed theorem-level judgment (admission
rule).

**Claim shape:** metatheorem entry (explicit schema exception — see
[`CLAIMS.md`](CLAIMS.md) *Claim shape and evidence
status*; review finding, 
(hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.11, 2026-10-20).

**Classification:** metatheorem.

**Ledger status:** proved (hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.11, 2026-10-20).

**Intended mechanization status:** Lean metatheorem after Gate 4; this is the
Gate 5 obligation and the precondition of maintainer acceptance. First slice
landed 2026-10-25: the models predicate `Models` over the evaluation chain
the closed command unfolds through, the L3 rule inventory as the inductive
`Derives`, and the metatheorem `judgment_soundness` by induction on the
derivation, for a well-formed evaluation chain (`Chain cs` and
`WellFormedContext cs`). `Models` returns the chain hypothesis unchanged, so
the slice proves the `⊨` half under an assumed evaluation; the `Eval` conjunct
of the statement below is assumed rather than proved, and the chain hypothesis
cannot be dropped (`le_refl` and the pure order rows are derivable over any
list of states). Scope of the slice: the instantiation cells proved are skip's
identity (every field of the §4.11 list — input and output state coincide, so
the identity holds under any reading of the distance fields: `dX` and `dZ` are
read through a supplied measure parameter the derivation constrains nowhere
else, and `d` is their minimum by definition)
and the `n` cells of deletion, addition, and the graft (`n' = n - 1`, under
the qubit-namespace nonduplication). The slice of 2026-10-26
adds the `k` cells (deletion, addition, graft) and the distance monotonicity
and bounds cells (deletion and addition, `d_X`/`d_Z`/`d`) as instantiation
rows that take the corresponding cell's truth at that evaluation as a premise:
a derivable `k` or distance annotation then means the cell is assumed at the
row, not discharged by a per-primitive lemma. The slice of 2026-10-27 (`lean/CodeCalculus/WellFormedness.lean`) adds the output well-formedness
cells as the sentence `Ann.wf`, with rows for skip, deletion, addition, and the
graft: the first three are discharged by the §4.7 preservation lemmas
(`wf_deleteState`, `wf_addState`, lifted to every graft-free evaluation by
`wf_of_eval`), and the graft's is discharged by `wf_graft_of_eval`
(`lean/CodeCalculus/GraftWellFormedness.lean`, , 2026-10-28). The
same slice discharges the `k` cells of deletion and addition from the
transition's own independence premise through the rank-decrease lemmas
(`sectorRank_deleteState_same`, `sectorRank_addState_same`, bridged from the
vector-level premise to `rankBitmasks` by `inSpanRows_iff_inSpanMasks`), under
the dimension bound `RanksFit` (`rank X + rank Z ≤ |Q|`), which keeps the
truncated subtraction in `stateK` exact and which `ranksFit_of_wf`
(`lean/CodeCalculus/RanksFit.lean`, , 2026-10-28) derives from
well-formedness, so no row takes it as a premise. `judgment_soundness_of_head`
derives the chain's well-formedness context from the input state alone on any
chain. The slice of 2026-10-29 removes the per-row premise from
the six distance rows and gives `judgment_soundness` one hypothesis in its
place, `MeasureMonotone dMeasure`: deletion does not raise either sector
distance and addition does not lower either, over every evaluation of the two
commands; the full-distance rows follow by monotonicity of `min`. The
row-space inclusions the two transitions produce are proved
(`sectorRows_deleteState_sublist`, `sectorRows_addState_sublist`), and the
span form `SpanMonotone` is bridged to the hypothesis by
`measureMonotone_of_spanMonotone`, so a concrete measure enters through the
set-inclusion argument of §4.3 and §4.5 alone. That discharge landed
2026-10-29: `exactMeasure`
is the exact sector distance over `F₂` vectors, with `|Q| + 1` standing for
`+∞`, `spanMonotone_exactMeasure` proves it span-monotone through the same
set-inclusion argument, and `judgment_soundness_exact` instantiates the
metatheorem with no measure hypothesis left. The measure parameter of
`judgment_soundness` itself stays uninterpreted, and the `Nat` reading of
`+∞` is a stand-in recorded in the module note. The slice of 2026-10-29 states the `k` cells of deletion and addition in the spec's exact
additive form (`k' = k + 1` and `k = k' + 1`, rows `instDeleteK` and
`instAddK`, through a new `add` term constructor) and keeps the truncated
`Nat` reading as separate rows (`instDeleteKSub`, `instAddKSub`), since
`TRANSITIVITY` composes two-step `k` chains only through a shared middle
term; before that slice only the truncated forms were rows, which are weaker
than the cell at `k' = 0`. The module note records three encoding limits: the
absorbing `min` under chain extension, the `Nat`-valued measure with no `+∞`
at `k = 0`, and the inventory's lack of an arithmetic or congruence rule, so
a two-graft `n` chain is not derivable by `TRANSITIVITY`. Evidence status is
unchanged.
`OBL-JUDGMENT-TRANSPORT` is mechanized in
`lean/CodeCalculus/Transport.lean`. Evidence status is unchanged
by these landings: they are mechanization progress, not a status upgrade.


**Statement.** $\Gamma\vdash \operatorname{Eval}(m,S,S') : R$ implies
$\operatorname{Eval}(m,S,S')$ and $(S,m,S')\models R$ (the research proposal (see REFERENCES.md)): every
derivable annotation is true of the denoted command evaluation.

**Hypotheses.** $\Gamma$ contains only well-formedness assumptions of ; the
derivation system for $\vdash$ is the L3 rule inventory of
 §3.4 and §3.4.1
(instantiation, `TRANSITIVITY`, `MIN-ORDER`, ambient order theory on
$\mathbb{N}\cup\{+\infty\}$).

**Dependencies.** derivation-rule inventory; `OBL-JUDGMENT-TRANSPORT`;
`OBL-WELL-FORMEDNESS-PRESERVATION`.

**Known edge cases and counterexamples.**

- Soundness is vacuous for `unavailable` properties (no derivable claims exist
 to falsify) and must not be read as completeness.
- Empirical agreement, including `W0`–`W16`, is not evidence for this
 obligation.

## `OBL-GRAFT-TRANSITION-SOUNDNESS` — Graft transition preserves the state model

**Taxonomy IDs:** `E-GRAFT`.

**Semantic-contract field:** applicability, state update, output
well-formedness, $n$, $k$, and logical-sector effects.

**Claim shape:** `preservation` — **Evidence status:** `proved` (hand derivation
`spec/OPERATIONAL_SEMANTICS.md` §4.12, 2026-10-20; general derivation under the
coverage guard).

**Classification:** theorem.

**Introduced in:** `stdCSS-2`.

**Ledger status:** added 2026-10-19 for ; the transition is specified
and executable, and its derivation under the applicability premises and coverage
guard is recorded at §4.12.

**Intended mechanization status:** well-formedness of the constructed state is
machine-checked (Lean 4, `lean/CodeCalculus/GraftWellFormedness.lean`, , 2026-10-28, no `sorry`, no `native_decide`): `wf_graftState` and
`wf_graft_of_eval`, under the transition's premises. I2 is derived there by
rank counting from the `k`-preservation premise and the dimension bound
(`ranksFit_of_wf`), both output sectors being forced to full rank,
not by §4.12's lifting argument, and the coverage and opposite-sector guards are not
used. `n' = n - 1` is the `instGraftN` row of `judgment_soundness`
(`lean/CodeCalculus/Soundness.lean`); `k' = k` is the transition's own premise.
The §4.12 derivation is unchanged. Evidence status unchanged.

**Statement.** For every well-formed presented CSS state and applicable
`E-GRAFT(q,τ,vec r)` transition as specified in
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §2, the constructed state
is well-formed, has $n'=n-1$ and $k'=k$, and satisfies the stated
selected-sector chain and opposite-sector shortening update. For a fixed input
state and fixed ordered command, the transition is deterministic.

**Hypotheses.** The command lists exactly all selected-sector rows touching
$q$ in chain order; the input display is independent; the output checks pass
CSS commutation and independence; each remaining qubit is touched by both
sectors; and the stated $k$ preservation check holds. The coverage condition
is an empirical guard in the source model, not a universal theorem.

**Dependencies.** `OBL-WELL-FORMEDNESS-PRESERVATION`; the `E-GRAFT` transition
definition; the source's coverage qualification recorded in


**Known edge cases and counterexamples.** On the pinned qLDPC case
an archived internal note, grafting qubit 0 through X rows `a1,a2` yields a valid
$(9,2)$ state under the executable checks. This is one empirical case only and
does not discharge the obligation.

The challenge fieldnote of 2026-10-19, imported verbatim at
,
adds a *negative* case: over board parents, `E-GRAFT` produced **no
survivors** for $n \le 8$, and "grafting did not surface new survivors at the
sizes where exact witness search is affordable". The fieldnote's own boundary
statement limits its negatives to $n \le 20$ parents and witness search up to
weight 6-8, and records that a new mechanism could reopen them. It is cited
here as evidence about the *use* of the move, not about the transition's
soundness.

One recorded case is a **collision with a gate, not a defect**: every pair of
board codes shares the `a1`/`b1` identifier namespace, so the `used`-set
disjointness premise of `C-DIRECT-SUM` fails before any state is built, and
even where the namespaces could be arranged the submission gate rejects the
disconnected result. The `used`-set premise is doing exactly what it is
recorded to do.

## `OBL-PRICED-INTERVAL-SOUNDNESS` — Soundness of interval transport

**Taxonomy IDs:** `C-SKIP`, `C-ADD-CHECK`, `C-DELETE-CHECK`, `E-GRAFT`,
`C-DIRECT-SUM`, `C-SEQUENCE`.

**Semantic-contract field:** distance carry, conditional prices, and target
decision.

**Claim shape:** `preservation` — **Evidence status:** `proved` (hand
derivation `spec/OPERATIONAL_SEMANTICS.md` §4.13, 2026-10-21, under the
corrected E-GRAFT rules).

**Classification:** metatheorem.

**Introduced in:** `stdCSS-2`.

**Ledger status:** added 2026-10-19 for ; consumer rules are
transcribed in [`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2b and
`machine/consumer.json`; interval soundness derivation recorded at §4.13 is
**proved** under the corrected E-GRAFT rules (see §4.13). Mechanization:
`lean/CodeCalculus/PricedInterval.lean` (`priced_interval_soundness`, ,
2026-10-26) mechanizes the interval bookkeeping conditional on the distance
laws §4.13 derives and on price truth as premises over an uninterpreted
distance measure, with the `k = 0` hypothesis and the three monotonicity
hypotheses guarded by well-formedness of the input state since 2026-10-29; witnesses, strict improvement, and `certify`/`prune` remain
outside this slice.

**Statement.** If each input ledger interval contains the corresponding exact
distance and every supplied conditional price, lower bound, strict-improvement
enumeration, and witness validity premise is true, then every interval emitted
by the consumer contains the resulting code's exact distance. Consequently,
`certify` is justified by its lower endpoint and `prune` is justified by its
upper endpoint. A `re-measure` result makes no distance claim.

**Scope note.** This obligation covers only the core
transformers of `JUDGMENT_LAYER.md` §8.3 (`C-SKIP`, `C-ADD-CHECK`,
`C-DELETE-CHECK`, `E-GRAFT`, `C-DIRECT-SUM`, `C-SEQUENCE`). The six Gate 6
cells' interval rules (`JUDGMENT_LAYER.md` §2b/§2f) are outside this slice;
their sound admission is tracked by `OBL-GATE6-CSS-EXTENSIONS`, and
`OPERATIONAL_SEMANTICS.md` §4.13 states the boundary explicitly. No bullet
is added here, and the obligation's `proved` status is unaffected.

*Instance reading (2026-10-28).* Restates this obligation as an instance of
the abstract-interpretation schema (transformers §8.3, soundness/monotonicity
§8.4, composition §8.5, reduced product §8.8, and the `unavailable`-is-not-top
distinction §8.10); the per-primitive soundness bullets of §4.13 are the
instances. See `JUDGMENT_LAYER.md` §8.6. No status change.

**Hypotheses.** `C-ADD-CHECK` uses only carried lower bounds and currently valid
witnesses unless the strict-improvement hypothesis gives an exact old distance
and an exhaustive minimum-weight-class enumeration. Unpriced deletion uses the
proved non-increase upper bound and resets its lower endpoint. Priced deletion
uses true full-distance $w_{\rm del},w_{\rm exp}$ inputs. `E-GRAFT` uses its
coverage guard and true exposure minimum. Direct sum uses the corresponding
minimum law. Every supplied witness is valid in the state where it is used.

**Dependencies.** `OBL-JUDGMENT-SOUNDNESS`; `OBL-JUDGMENT-TRANSPORT`;
`OBL-GRAFT-TRANSITION-SOUNDNESS`; hand derivations at
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4; conditional source
results in .

**Known edge cases and counterexamples.** In the pinned graft replay, an upper
witness of weight 2 coexists with a post-hoc exact distance of 2: the
transported upper bound is *exact* on that instance, and the spliced sector is
unchanged at 3, as the source's sector-wise relation predicts. The randomized
challenge refuter finds no lighter logical in 2860 trials, which is consistent
with that and is still not a lower-bound certificate. The ledger's lower
endpoint remains 0.

Two further cases were found by review on 2026-10-20 and are recorded here
because they are the shapes this obligation must exclude. First, a
full-distance price that moves a **sector** endpoint: the consumer once
raised the `d_X` and `d_Z` lower endpoints from a full-distance deletion
price, which licenses `d' = min(d, w_del, w_exp)` on the full distance and
nothing about the sectors. Second, a price that moves the wrong **sector**:
the graft exposure price is indexed to the non-spliced sector, so it licenses
that sector's interval and the full distance's; the spliced sector carries its
lower endpoint only and drops its upper endpoint unless a child-valid witness
supplies one. Both are fixed in the consumer and covered by regression tests;
both are recorded here because the obligation is stated over the transport
rules, not over the current implementation.

**Empirical cases from the challenge fieldnote of 2026-10-19**, imported
verbatim at

Over board parents with $n \le 20$ and $d \ge 4$, the fieldnote reports 15
gate-passing, board-advancing codes, **all** via `C-DELETE-CHECK` (single and
two-step chains), and none of them advancing on $d$ alone. It also reports
that `C-ADD-CHECK` strict transport found 0 strict improvements out of 736
valid additions for $n \le 10$, and that `E-GRAFT` produced no survivors for
$n \le 8$. Its boundary statement limits these negatives to $n \le 20$
parents and witness search up to weight 6-8. These are cited as evidence
about where the moves *pay*, not about the transport rules. The consumer's
own measurement, on the pinned challenge commit, is in
the conformance harness:
the deletion chain prunes target 4 with zero exact-distance remeasurements in
the consumer path, and the graft's transported upper bound is exact on its
instance.

**A note on the measuring instrument.** The evidence used against this
obligation includes a post-hoc exact-distance oracle in
`the conformance harness`, and that oracle was wrong twice before 2026-10-20: it
returned the first logical in integer order rather than the minimum-weight
one, and it enumerated bit positions rather than the state's qubit labels.
The second error reported a grafted child's distance as 1 where it is 2, and
the "loose witness" reading it produced was an artifact. An obligation
measured by an instrument is only as good as the instrument; the oracle now
has regression tests of its own.

## `OBL-PRICED-INPUT-SEMANTICS` — Meaning and trust boundary of price inputs

**Taxonomy IDs:** `C-DELETE-CHECK`, `C-ADD-CHECK`, `E-GRAFT`.

**Semantic-contract field:** consumer-supplied judgment hypotheses and their
evidence references.

**Claim shape:** `definition` — **Evidence status:** `proved` (typed meanings recorded
in `spec/JUDGMENT_LAYER.md` §2c, 2026-10-20).

**Classification:** framework obligation.

**Introduced in:** `stdCSS-2`.

**Ledger status:** proved (typed meanings recorded in `spec/JUDGMENT_LAYER.md`
§2c, 2026-10-20); JSON input fields are defined as judgment hypotheses, and
the consumer records sources without validating their truth. **Extended
2026-10-23:** the two further `C-ADD-CHECK` inputs (sector-aware
gauging prices; direct-sum extinction) now have typed meanings in §2c and a
computed structural side, so the typed-meaning record matches the consumer's
optional-input set.

**Statement.** Give each supplied lower bound, exact deletion/exposure price,
and minimum-weight-class enumeration a typed meaning that states what fact it
asserts and which state/transition it refers to. The consumer must not treat a
nonempty source string as validation of that fact.

**Hypotheses.** Inputs remain judgment inputs and are not added to state identity.
The external evidence may be trusted by a deployment, but the calculus
soundness statement must expose that trust as an explicit premise.

**Dependencies.** `OBL-JUDGMENT-SOUNDNESS`; the judgment schema in
[`CLAIMS.md`](CLAIMS.md); future evidence or certificate interface decisions.

**Known edge cases and counterexamples.** The qLDPC challenge supplies logical
witnesses that validate as upper bounds; its randomized `distance_not_refuted`
result is not a lower-bound certificate. The current prototype records exact
price evidence references without checking the underlying computation.

The challenge fieldnote of 2026-10-19, imported at
,
sharpens the second half of this. On the parents it tried — negatives bounded
to $n \le 20$ parents and witness search up to weight 6-8 — no support killed
every minimum-weight logical class, so the conditional cell "is effectively a
specification of a move that does not occur in this region". A hypothesis
that no tested parent satisfies is not a hypothesis the consumer can check
for truth -- it is a hypothesis the consumer can only take on trust, which is
precisely the trust boundary this obligation is about. The fieldnote's own
conclusion is that a searcher wanting $d+1$ should not expect this cell to
deliver it cheaply.

The one region where the condition is cheap **by construction** is distance
1: there the hypothesis reduces to a single commuting check that kills every
weight-1 logical, which is Proposition 18.3's condition instantiated at
$d = 1$, not a survey result. A yield statistic claimed for that region
("4 of 12 survivors") circulated in the 2026-10-20 review with no recorded
run behind it and is **withdrawn as unrecorded** (DIARY, 2026-10-20); the
recorded count is the fieldnote's $0$-of-$736$ above.

---

## `OBL-LOCALITY-TRANSPORT` — Transport of the interaction radius under the kernel primitives

**Taxonomy IDs:** `C-SKIP`, `C-DIRECT-SUM`, `C-DELETE-CHECK`, `C-ADD-CHECK`,
`C-SEQUENCE`, `E-GRAFT`.

**Claim shape:** `equality` and `upper-bound` — **Evidence status:**
`proved`.

**Classification:** `lemma`.

**Ledger status:** minted 2026-10-22 on as a
stub, so that the planning note at
an archived internal note could name
it; `scripts/lint_docs.sh` check 3 requires every `OBL-*` token to be defined
here. **Statement fixed 2026-10-22** with the wiring that admits the
interaction radius to the property inventory, and the dated hand derivation
placed at [`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4.21. The
evidence status moves `not-applicable` → `proved` because a derivation is now
in this repository (`AGENTS.md`, *Claim-status discipline*: `proved` is the
evidence status, `established` its proposal-side tag). **No promotion occurs
here**: `promoted` is a review disposition requiring independent review and
maintainer confirmation (`AUTHORITY.md` §B1–§B2), and the claim is
`proved` and not yet `promoted` — the normal state.

**Intended mechanization status:** Lean theorem in the slice.

**Statement.** Let $\lambda$ be a layout covering every qubit of a state's
namespace, and let $r(C,\lambda)=\max\{\mathrm{diam}_\lambda(s):s\in\mathit{rows}\}$
be the interaction radius, with $r=0$ for an empty display. Then:

1. *(exact values)* `C-SKIP` gives $r'=r$; `C-DELETE-CHECK` gives
 $r'=\max\{\mathrm{diam}_\lambda(s):s\in\mathit{rows}'\}$; `C-ADD-CHECK`
 gives $r'=\max(r,\mathrm{diam}_\lambda(r_{\rm new}))$; `C-DIRECT-SUM` gives
 $r=\max(r_A,r_B)$; `E-GRAFT` gives
 $r'=\max\{\mathrm{diam}_{\lambda'}(s):s\in\mathit{rows}'\}$ with
 $\lambda'=\lambda\vert_{Q'}$.
2. *(directions)* `C-DELETE-CHECK` gives $r'\le r$; `C-ADD-CHECK` gives
 $r'\ge r$; `E-GRAFT` gives $r'\le 2r$.
3. *(honesty)* A layout that is honest — at most $\rho$ qubits per site and
 distinct sites at least $1$ apart — stays honest under `C-SKIP`,
 `C-DELETE-CHECK`, `C-ADD-CHECK` and `E-GRAFT`. It is not automatically
 preserved by `C-DIRECT-SUM`.

**Hypotheses.** The state is well-formed (I1–I5). The layout covers every
qubit of the state's namespace, and its coordinates are read at the state's
qubit labels. For the direct-sum cell, the merged layout is honest. No
hypothesis about distances, weights, prices, or witnesses is needed, and none
is admitted: the radius is exactly computable.

**Conclusion.** The radius is a derived property of the display relative to a
ledger parameter, carried exactly under every primitive, with the directions
above. The locality class is **not** part of this obligation: it is a
consumer-side verdict computed from the transported radius against
consumer-supplied caps, and it follows from clause 2 rather than from a cell
of its own.

**Dependencies.** `OBL-JUDGMENT-TRANSPORT` for the schema-composition
condition under `C-SEQUENCE`; `OBL-WELL-FORMEDNESS-PRESERVATION` for the
transitions' state updates; the disposition recorded in the decision log.

**Known edge cases and counterexamples.**

- **The naive graft monotonicity is false.** Across the board entries with
 $n \le 14$ carrying a 2D layout, 277 grafts are applicable and 74 of them
 *increase* the radius, with the largest observed ratio $r'/r = 1.6125$. A
 claim that the graft preserves the interaction radius is therefore refuted
 by example, in the same shape as the refuted graft distance non-increase
 claim ([`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4.13,
 2026-10-20). What is derivable is the weaker bound $r' \le 2r$, from the
 triangle inequality on the graft's adjacent products.
- **The direct sum is the wrong place to look for a layout law.** Its Tanner
 graph is disconnected, so the direct-sum cell certifies a disconnected code
 ([`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2), and the challenge's
 connectivity gate rejects such an entry outright. A layout law for the direct
 sum is of academic interest only, and its honesty conditions are not
 preserved automatically by a disjoint union of two layouts.
- **The unsourced-transcription hazard.** Before this obligation, the adapter
 copied the parent's layout verbatim whenever the qubit namespace was
 unchanged, and no artifact in `spec/` stated that rule. It produced an
 export the challenge's own verifier rejected, because the copied
 `interaction_radius` claim is a function of the check set. The rule is now
 stated in `spec/JUDGMENT_LAYER.md` §2d and the transcription follows it.
- **The radius is not a distance.** No lower bound, interval, price, witness,
 or minimum-weight enumeration enters any rule, because none is needed. The
 radius is exactly computable from the display and the layout, and it is not
 an opacity question of the kind `spec/VOCABULARY.md` records for $d_X$ and
 $d_Z$.

## `OBL-TANNER-CONNECTIVITY-TRANSPORT` — Transport of the Tanner components under the kernel primitives

**Taxonomy IDs:** `C-SKIP`, `C-DIRECT-SUM`, `C-DELETE-CHECK`, `C-ADD-CHECK`,
`C-SEQUENCE`, `E-GRAFT`.

**Claim shape:** `equality` and `direction` — **Evidence status:** `proved`.

**Classification:** `lemma`.

**Ledger status:** minted 2026-10-23 on ; the
dated hand derivation is at
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4.22.
`proved`, not yet `promoted` — the normal state (`AUTHORITY.md` §B1–§B2).

**Intended mechanization status:** Lean theorem in the slice.

**Statement.** For a presented state, let $\Gamma(C)$ be the combined X+Z
Tanner graph of the **displayed** rows and $\kappa(C)$ its number of connected
components. Then $\kappa$ carries under every primitive:

1. *(exact values)* `C-SKIP` gives $\kappa'=\kappa$; `C-DELETE-CHECK` and
 `E-GRAFT` give the recomputed component count of the child; `C-ADD-CHECK`
 gives $\kappa'\le\kappa$; `C-DIRECT-SUM` gives $\kappa'\ge 2$ whenever both
 factors are nonempty, because the disjointness premises leave the two
 factors' graphs with no joining edge.
2. *(the gate)* The direct sum certifies a disconnected code; a disconnected
 graph fails the qLDPC verifier's `tanner_connected` hard gate outright,
 which is why a direct sum is unusable against the board's connectivity
 gate.

**Hypotheses.** The state is well-formed (I1–I5). No hypothesis about
distances, weights, prices, or witnesses is needed, and none is admitted: the
component count is exactly computable by finite traversal.

**Conclusion.** Connectivity is a derived, display-relative property (like
$w$); it is not part of $\equiv$. The strictly stronger stabilizer-group
predicate of the same gate is computed by the consumer but is not carried as a
spec cell.

**Dependencies.** `OBL-WELL-FORMEDNESS-PRESERVATION` for the transitions'
state updates; the disposition recorded in the decision log.

**Known edge cases and counterexamples.** The deletion witness in
`machine/test_priced_calculus.py` `ConnectivityCarryTests` (a redundant
spanning check whose removal separates all four qubits) shows the Tanner
graph reporting one component where the stabilizer-group predicate already
sees four: the redundant spanning row hides four separate blocks behind a
single connected graph, and deleting it exposes them in both predicates.
The group predicate needs no cross-sector reduction on this all-X display; it
was already split.

## `OBL-GATE6-CSS-EXTENSIONS` — Sound admission of the CSS-level Gate 6 extensions

**Taxonomy IDs:** `E-GLUE`, `E-PUNCTURE`, `E-PEEL`, `E-EXTEND`,
`E-LOCAL-HADAMARD`, `P-REBASE`.

**Semantic-contract field:** per-operation contract rows in
[`CLAIMS.md`](CLAIMS.md) (*Initial contract index*): `taxonomy-only` for
`E-GLUE` (no unary grammar production; evaluator transition admitted
2026-10-27, §4.31), `transition-defined` for the other five
(`P-REBASE` §4.26, `E-PEEL` §4.28, `E-PUNCTURE` §4.29, `E-EXTEND` §4.30,
`E-LOCAL-HADAMARD` §4.27); the contract index is unchanged by the
discharge, which does not advance a ladder rung.

**Claim shape:** `definition` / `equality` / `monotonicity` (per move) —
**Evidence status:** `proved` (hand derivation
`spec/OPERATIONAL_SEMANTICS.md` §4.32, 2026-10-28): each of the six admitted
Gate 6 cells has a typed transition (§4.26–§4.31), applicability conditions,
exactly stated state/context update, and a sound, monotone interval
transformer under its stated hypotheses. The cells remain conditional on
their hypotheses; discharge is not promotion.

**Classification:** framework admission obligation (Gate 6).

**Ledger status:** admitted as conditional cells by scope decision
2026-10-23 (decision log); restricted transition definitions landed for all six
(§4.26–§4.31); soundness discharged by hand derivation
`spec/OPERATIONAL_SEMANTICS.md` §4.32. The cells remain
conditional on their hypotheses.

**Statement.** For each admitted CSS-level extension (`E-GLUE`, `E-PUNCTURE`,
`E-PEEL`, `E-EXTEND`, `E-LOCAL-HADAMARD`, `P-REBASE`): state its typed
transition, applicability conditions, exact state/context update, and the
conditional cell under which it carries; then discharge its soundness
obligation. Sound admission is discharged under the stated hypotheses (§4.32); the
moves remain conditional cells, and their property claims keep the evidence
status of their hypotheses.

**Hypotheses.** The core state model $C=(Q,X,Z,\mathsf{pres},\mathsf{used})$
and the taxonomy-to-syntax contract (`spec/CLAIMS.md`).

**Dependencies.** Gate 6 scope decision (recorded 2026-10-23); the non-CSS
extended-state layer is excluded.

**Known edge cases and counterexamples.** Recorded in
`OPERATIONAL_SEMANTICS.md` §4.28–§4.29 (coordinate restriction can raise a
distance: peel/puncture refutations) and §4.30 ($\Delta\neq\varnothing$
carries nothing).

**Discharge ledger (per move, per claim shape).** The following records, for
each move and each claim shape, the section that discharges it under the
2026-10-28 derivation (§4.32). A blank is not a gap: `monotonicity`
rows marked *refusal* record that no monotone carry is derivable
(§4.28–§4.30); `equality` rows marked *conditional* record a cell hypothesis
rather than a theorem. This ledger is the discharge record for
`OBL-GATE6-CSS-EXTENSIONS` (evidence status `proved`); the Gate 0
ratification reading that the soundness obligation remained
open is superseded by this entry and by the dated maintainer discharge
recorded in the decision log.

| Move | definition | equality | monotonicity |
| --- | --- | --- | --- |
| `P-REBASE` | §4.26 (typed transition, GL-ness) | §4.26 (span/`n`/`k`/distance identity) | §4.32 (identity transformer); `JUDGMENT_LAYER.md` §2b row |
| `E-LOCAL-HADAMARD` ($T=Q$) | §4.27 | §4.27 (sector distance exchange, $d'=d$) | §4.32 (swap transformer); `JUDGMENT_LAYER.md` §2b |
| `E-PEEL` | §4.28 (applicability, injectivity) | §4.28 (`n'`, `k'` exact) | §4.32 (reset transformer; no carried endpoint derivable); `JUDGMENT_LAYER.md` §2b reset |
| `E-PUNCTURE` | §4.29 (applicability, structural effects) | §4.29 (`n'`, `k'` exact) | §4.32 (reset transformer; no carried endpoint derivable); `JUDGMENT_LAYER.md` §2b reset |
| `E-EXTEND` | §4.30 (applicability, canonical mint) | §4.30 (`n'`, `k'` exact) | §4.32 (carry/reset under the stated hypotheses); `JUDGMENT_LAYER.md` §2b row |
| `E-GLUE` | §4.31 (applicability, state update) | conditional — seam certificate hypothesis (Theorem 4 / claim 7.4 for $d_Z(Q)=\min(d_A,d_B)$); lower endpoints sound without it (§4.31) | §4.32 (lower endpoints sound without certificate; upper endpoints from witnesses); `JUDGMENT_LAYER.md` §2b/§2e |

The `definition` column discharges the typed-transition and applicability
obligation; the `equality` column discharges the exact state/context update;
the `monotonicity` column discharges the interval-carry (soundness)
obligation, where derivable. Rows marked *refusal* or *conditional* are the
honest refusals recorded in §4.28–§4.31 and are not gaps.

**Seam-vs-seam note.** §4.31's applicability now carries the
missing seam-vs-seam premise (pairwise I1/I2 among the seam checks) in
addition to the seam-vs-factor commutation premise; see
`OPERATIONAL_SEMANTICS.md` §4.31. `E-GLUE`'s equality
$d_Z(Q)=\min(d_A,d_B)$ is recorded above as a hypothesis of the conditional
cell, not as a theorem of §4.31 or a carved-out obligation.
