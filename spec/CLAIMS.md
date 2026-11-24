# Semantic Contracts for CSS-Code Operations

## Purpose

This note defines the semantic contract that an operation must satisfy before it is admitted as a formal calculus rule.

The operation taxonomy in [`spec/TAXONOMY.md`](TAXONOMY.md) records the broader operation space and assigns stable identifiers. This note records the semantic effects and evidence status of operations that are admitted, or are being prepared for admission, to the calculus.

The contract is deliberately broader than a list of parameter formulas. It records what changes, what is preserved, what information is required, what is known about logical operators and distance, how the operation can be computed, and what provenance must survive the transition.

A contract does not require every property to be known. It does require every property to be classified on two separate axes: its **claim shape** (for example equality, lower bound, upper bound, monotonicity, or `unavailable`) and its **evidence status** (`proved`, `conditional`, `empirical`, `conjectural`, `open`, `not-applicable`). A property that the calculus deliberately does not represent is recorded with claim shape `unavailable`; it is never silently dropped, and `unavailable` is never an evidence status.

---

## Contract status

An operation progresses through the following lifecycle:

```text
taxonomy-only
 ↓
syntax-candidate
 ↓
transition-defined
 ↓
state-sound
 ↓
contract-stated
 ↓
contract-proved
 ↓
mechanized
```

| Status | Meaning |
| --- | --- |
| `taxonomy-only` | The operation is classified but has no semantic contract yet |
| `syntax-candidate` | The operation has a proposed syntax position but no defined transition or constructor semantics |
| `transition-defined` | Input types, applicability, state update, and inapplicability behavior are specified |
| `state-sound` | Output well-formedness is proved for every applicable transition |
| `contract-stated` | Every contract field has an explicit value, an explicit `unavailable` claim shape, or evidence status `open` or `not-applicable` |
| `contract-proved` | The transition and every claimed theorem-level judgment have proofs with stated hypotheses |
| `mechanized` | The relevant definitions and proofs are represented in the chosen proof assistant |

`contract-draft` remains a document label for an incomplete contract record; it is not an admission stage. A draft or planned transition is not an admitted calculus rule.

A contract can be `contract-stated` while some distance effects remain `open`. This is preferable to leaving the field implicit.
A `contract-proved` contract may likewise carry fields with evidence status `open`; such a field claims no theorem-level judgment, so the promotion covers every field whose evidence status is `proved` (or `conditional` with stated hypotheses), and an `open` field is not a gap in the proof.

The status applies to the contract as a whole. Individual claims have their own evidence status.

**Conditional-cell scope meaning.** "Admitted conditional cell" means
the move or judgment is included in the current design scope and consumer
prototype with explicit hypotheses. It does **not** bypass the lifecycle above
or mean the transition is a sound formal-calculus rule. In particular,
`E-GRAFT` is currently `transition-defined` — no dated decision has promoted it
past that rung — while its transition soundness is `proved` under the coverage
guard (`OBL-GRAFT-TRANSITION-SOUNDNESS`, §4.12) and its contract fields were
completed for Gate 0 on 2026-10-27.

---

## Claim shape and evidence status

These are separate fields.

**Claim shape:**

- `definition`;
- `equality`;
- `lower-bound`;
- `upper-bound`;
- `preservation`;
- `monotonicity`;
- `weakening` (monotone image of a carried lower bound, re-read at each state and never substituted from the parent; [`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2h, §7.2);
- `unavailable`;
- `probabilistic` (delta-bounded) — see below.

**Probabilistic (delta-bounded) claim shape.**
A claim about a *search*, not about the code: "with probability at least
$1-\delta$, the sampled family contains no witness of weight below $L$."
It carries an explicit event (the sampling procedure and its universe) and an
explicit $\delta \in [0,1]$. Its evidence status may be `proved` (e.g. by
union bound), `conditional`, or `empirical`, but it is never `unavailable`'s
successor: it does **not** imply $d \ge L$, and it never upgrades an
`unavailable` lower bound to `proved`. Composition rule: for independent
searches with parameters $\delta_i$, the combined claim holds with
$\delta = 1 - \prod_i (1-\delta_i)$ (or the stated union bound); a failed
search is reported as a probabilistic claim about the search, never as a
lower-bound certificate. Relation to `unavailable`: `probabilistic` is
orthogonal — `unavailable` says the calculus does not represent the quantity;
`probabilistic` says a sampling procedure found no witness, with stated
confidence.

**Evidence status:**

| Status | Meaning |
| --- | --- |
| `proved` | Established from the operation definition and stated hypotheses |
| `conditional` | Supported only under additional explicit hypotheses |
| `empirical` | Supported by computation or observed examples, but not proved |
| `conjectural` | Proposed on the basis of incomplete evidence |
| `open` | No accepted result is currently available |
| `not-applicable` | The field does not apply to this operation or state model |

**Explicit schema exception for metatheorem entries.** The shapes above are
the shapes of per-operation contract claims. A ledger entry classified
`metatheorem` whose conclusion is not one of them records this as *metatheorem
entry (explicit schema exception)* instead of borrowing a shape — notably
[`OBLIGATIONS.md`](OBLIGATIONS.md)
`OBL-FIXED-NAMESPACE-REACHABILITY` (a path-existence conclusion) and
`OBL-JUDGMENT-SOUNDNESS`; `OBL-JUDGMENT-TRANSPORT` does fit and carries
`preservation`. `not-applicable` stays an evidence status and is never a claim
shape (a red-team review).

Evidence status is attached to each claim, not just to the operation. For example, an operation may have an equality claim for $k$ with `proved` evidence, a conditional lower-bound claim for distance, and an `unavailable` claim shape for deletion-distance lower bounds and equalities.

**External vocabulary crosswalk.** The mapping between these claim/evidence vocabularies and external certificate-strength vocabularies (witnessed upper bound; `solver` / `proof_log` / `formal`) is recorded here. The crosswalk is a reading aid for external evidence; it changes no claim shape, evidence status, or reserved status defined here.

**Reserved future status: `certificate-checked`.** Assigned to no claim of the current release `stdCSS-2`; admitted to the `stdCSS-3` candidate, where the per-state theorems named under *Mechanized checker (2026-11-11)* below carry it. Meaning: a machine-checked certificate — produced by an external search (for example SAT-based distance search) whose translation into the proof assistant is itself verified — has been checked by the mechanized calculus, upgrading the claim without trusting the search program. Candidate trigger: the Lean-QEC verified SAT-distance bridge (arXiv 2605.16523; §5); a second named candidate is the complete branch-and-bound distance search of Okada–Kasai (arXiv 2607.14091v4 §V), whose completed `None` run is a reproducible per-state certificate that $d > W$ ( §1, §6). Adopting it is a Gate 6-candidate decision and an assertion-language-axis release bump (`spec/VERSIONING.md` §4), not a silent edit; until then, no field may carry this status. When adopted it attaches to per-state atomic judgments only: a certificate evidences one instance, never an operation contract, whose claims are schemas over all inputs.

**Review finding (second red-team pass, 2026-09-26) — dispositioned
2026-09-26.** A certificate
establishes the distance of one code instance, while the deletion-distance
claim of `C-DELETE-CHECK` is a schema over all inputs and all deleted rows: no
finite set of certificates evidences it. What a checker can admit is a per-state
atomic judgment — and by a related finding, admitting per-state distance atoms makes
deletion-distance facts about particular states derivable, which the
disposition makes sound by scoping `unavailable` to evaluations.

**Disposition.** `certificate-checked`
attaches to per-state atomic judgments and never to an operation contract; the
*Reserved future status* paragraph above now says so, and the reclassification
path under *Outcome vocabulary* is per state. Decided together with the related findings; see the same review.

**Note.** The second candidate trigger above is recorded from
PRIOR_ART.md §1 (Okada–Kasai v4 specifics): the
complete search is sound and complete for fixed CSS lifts with proved pruning
and cyclic root reduction, so a completed run has exactly the per-state
certificate shape the review defined. Naming it here commits to nothing; adoption
remains the Gate 6-candidate decision this paragraph already requires.

**Disposition (2026-11-10).** The maintainer accepted
both the `probabilistic` claim shape and the `certificate-checked` status for
recording heuristic search outcomes ("no survivor found up to weight `w`")
without upgrading `unavailable` to `proved`. This is a disposition only: it
does not by itself admit either status to a field. Admission still requires an
assertion-language-axis release bump and, for `certificate-checked`, a
mechanized certificate checker; until then no field may carry either status for
this purpose, and the rule that no heuristic result may be presented as a lower
bound stands.

**Admission (2026-11-11).** Two statuses are admitted for
heuristic search outcomes, on the terms below. This paragraph and the two
property-inventory rows that cite it are the `CLAIMS.md` row the disposition
required, and `spec/VERSIONING.md` §4 and §5.1 carry the versioning note,
before any field carries either status.

- *`probabilistic` for heuristic search outcomes.* A bounded or sampled
 search that looks for a survivor (a logical class that survives an added
 check) or a witness (a low-weight logical) records its result as a
 `probabilistic` claim about the search: the procedure, the universe it
 ranged over, how much of that universe was evaluated, the budget and
 whether it was exhausted, the failure probability $\delta$ ($0$ for a
 deterministic search over the stated universe, the derived bound for a
 sampled one), and whether anything was found. Its evidence status is
 `empirical` unless a union bound is derived, in which case it is `proved`.
 The record attaches to a per-state atomic judgment about one search, never
 to an operation contract, and it licenses no ledger endpoint: a negative
 outcome leaves an `unavailable` claim `unavailable` and is never presented
 as a lower bound, in either sector or for the full distance. The shape
 exists since 2026-10-27, so this is a dated note on the current ordinal and
 not a new row. The consumer's record is `heuristic_outcome` in
 `machine/priced_calculus.py`, attached by the enumeration fallback of
 `strict_improvement_feasible` and by the bounded sector search of
 `machine/planner.py`; no ledger rule reads it.
- *`certificate-checked` for per-state certificates.* The reserved status is
 admitted to the `stdCSS-3` candidate's evidence-status vocabulary
 (`spec/VERSIONING.md` §5.1) for per-state atomic judgments keyed as in
 `OPERATIONAL_SEMANTICS.md` §4.24, under the restriction above. It
 attaches only through a mechanized certificate checker: a checker in the
 proof assistant whose acceptance is proved to imply the certified fact.
 `machine/certificates.py` (the kill-certificate format and its total
 Python checker, 2026-10-25) is the prototype of that checker and not the
 checker, so nothing it accepts carries `certificate-checked` and every
 fact it supports stays `conditional`. The mechanized checker landed
 2026-11-11 (*Mechanized checker* below); the status ships with the
 candidate row.

Neither admission changes the rule that no heuristic result may be presented
as a lower bound.

**Mechanized checker (2026-11-11).** The checker the admission
requires is `checkCertificate` in `lean/CodeCalculus/CertificateChecker.lean`,
for the kill-certificate format of `machine/certificates.py`. For a state
$C$, a sector $\sigma$, and a bound $L$, the certified fact is
$L \le d_\sigma(C)$ for the exact sector distance of
`lean/CodeCalculus/ExactDistance.lean`.

- *What is proved.* Acceptance implies that every $\sigma$-logical of $C$
 has weight at least $L$ (`checkCertificate_sound`), restated for the
 three readings of the exact distance (`certificate_lower_bound`,
 `certificate_lower_bound_ext`, `certificate_lower_bound_nat`). With a
 checked $\sigma$-logical of weight $L$, the exact distance is $L$
 (`certificate_equality`). The proofs hold for every state term and depend
 on `propext` and `Quot.sound` only.
- *What carries the status.* A per-state atomic judgment carries
 `certificate-checked` exactly when the repository contains a Lean theorem
 that applies one of those results to a state term and a certificate term
 with the acceptance premise discharged by kernel evaluation (`by decide`).
 The first such theorems are in
 `lean/CodeCalculus/CertificateInstances.lean`: both sector distances of
 the `W3` result state ($d_X = 2$, $d_Z = 1$) and of the pinned
 `codes/10-2-3-b.json` parent ($d_X = d_Z = 3$), each as a lower bound and
 as an equality. They are content of the `stdCSS-3` candidate and ship
 with its row. No consumer field carries the status: no ledger endpoint,
 fixture expectation, or judgment cell reads these theorems, and the
 consumer's own checker stays the prototype.
- *Trust basis.* Trusted: the Lean kernel, the definition of the exact
 sector distance (`isLogicalBool`, `exactDistance?`), and the reading of a
 Lean `CodeState` term as the state it transcribes. Not trusted: the
 search that produced the certificate, the Python checker, and the
 translation from a consumer state and certificate to Lean source
 (`lean_state_term`, `lean_certificate_term`, `lean_instance_block` in
 `machine/certificates.py`). A wrong translation yields a module that does
 not build or a true theorem about a different state term, never a false
 theorem. Each instance state term is also proved well-formed
 (`EncodingWellFormed`), and the `W3` term is proved equal to the fixture
 transcription `fixture_W3_result`. That a state term denotes the consumer
 state it was translated from is checked by reading, not by proof.
- *Scope.* The keying is the triple of state, property, and sector of
 `OPERATIONAL_SEMANTICS.md` §4.24, under the restriction: a theorem
 about one state term evidences no operation contract and transfers to no
 other state. The three Gate 5 questions §4.24 leaves open stay open.

---

# Contract schema

Every operation that is proposed for admission should have the following sections. A field may contain a theorem, a definition, a bound, or a certificate requirement; or it may be explicitly recorded with claim shape `unavailable`; or it may carry evidence status `open` or `not-applicable`. (Recall the two axes: `unavailable` is a claim shape; `not-applicable` is an evidence status. An `unavailable` claim shape pairs with evidence status `not-applicable`, since there is no proposition to evidence.)

## 1. Identity and operation class

Every contract also records its operation kind:

- `expression-constructor`;
- `command`;
- `presentation-operation`;
- `lower-level-constructor`;
- `extended-state-operation`.

This prevents state-expression constructors such as direct sum and command combinators such as sequencing from being forced into a unary transition schema.

```md
## `C-DELETE-CHECK` — Stabilizer/check deletion

**Taxonomy ID:** `C-DELETE-CHECK`

**Introduced in:** `stdCSS-1` (primitive); the conditional sector-split price
cell (full-distance and sector-wise) was introduced in `stdCSS-2`.

**Layer:** Core CSS-code transformation

**Primitive or derived:** Primitive

**Contract status:** `contract-draft`
```

The priced construction extension changes only the **conditional judgment
cells** for deletion: the unconditional upper bound remains available, while
the full-distance equality requires cited $w_{\rm del}$ and $w_{\rm exp}$
inputs. No exact sector-distance equality follows from that global price.

*(The fenced block above is §1's template: illustrative values, including its
`contract-draft` status line. The completed records follow; where the template
and a record disagree, the record governs.)*

## Kernel operation contracts — `contract-proved` (rung 6, 2026-11-18)

The five records below complete the schema §1–§12 (completed 2026-10-27 for
Gate 0, rung 5 `contract-stated`) and are promoted to **rung 6
(`contract-proved`)** by dated maintainer decision on 2026-11-18:
for each kernel operation, the typed transition, applicability conditions,
exact state/context update, unconditional theorem-level judgments, conditional
carry cells (with stated hypotheses), and scoped metatheorem re-discharges
carry dated hand derivations in [`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md)
§4 (including §4.39 for logical-sector quotients and §4.40 for the `stdCSS-3`
metatheorem re-discharge ledger). Rules and derivations stay in
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §2 and §4 and
[`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2–§2h; these records cite them and do
not restate them. Gate 0 records completeness, not soundness: `E-GRAFT` and the
Gate 6 cells remained `transition-defined` at best at Gate 0 ratification
(`E-GLUE` subsequently advanced to `contract-stated` on 2026-11-18, while remaining a conditional cell with Gate 6 unchecked). **Scope
boundary:** `contract-proved` records hand-derivation evidence (`proved`), not
rung 7 (`mechanized`) and not Gate 2–5 ratification — Gates 2–7 remain
unchecked ([`GATES.md`](GATES.md)), `E-GRAFT`, the six Gate 6 cells, and the
ten admitted constructors remain `transition-defined`, and review disposition
`promoted` stays governed by `AUTHORITY.md` §B.

### `C-SKIP` — Identity (`skip`)

**Taxonomy ID:** `C-SKIP`. **Layer:** Core CSS calculus.
**Syntax category / kind:** command (`m ::= \mathrm{skip}`,
[`TERM_LANGUAGE.md`](TERM_LANGUAGE.md) §2).
**Primitive or derived:** primitive production.
**Contract status:** `contract-proved` (promoted 2026-11-18; record completed 2026-10-27).

**Input / output (§2):** presented state $C$; the output is $C$ unchanged,
with one `skip` record appended to `steps` — `steps` is semantically inert:
no `Eval` premise or judgment reads it. **Applicability (§3):**
none; the rule applies to every well-formed state. **State update:** none.
**Inapplicability:** never — the rule has no failing premise.
**Deterministic:** yes (`OBL-PRIMITIVE-DETERMINISM`, §4.8, re-discharged §4.40).
**Well-formedness obligation (§12):** `OBL-WELL-FORMEDNESS-PRESERVATION`,
proved §4.7 (re-discharged §4.40).

**Structural effects (§4):** $n'=n$, $k'=k$, $w'=w$ `[proved]` (carry-table
rows, [`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2, §4.7); $r'=r$ with layout
honesty preserved `[proved]` (§2d.5, §4.21); Tanner connectivity $\kappa'=\kappa$
`[proved]` (§4.22); $\mathsf{preserves}_U$ carries unchanged `[proved]` (§2h,
§4.37); equal-syndrome weight floor $\omega'=\omega$ and carried floor
$\lceil L_d/2\rceil$ unchanged `[proved]` (§2h, §4.37).
**Logical effects (§5):** identity transport: the output state *is* the input
state, so $\mathcal{L}_\sigma(C') = \mathcal{L}_\sigma(C)$ and every logical
class carries both ways `[proved]` (definitional).
**Metric-preservation status (§7):** preserves $d_X$, $d_Z$, and $d$ exactly:
yes `[proved]` (definitional; inventory row *distance identity under skip*);
every monotonicity slot holds as equality. **Conditional carry cell:** none
required — every carry cell is unconditional identity (`JUDGMENT_LAYER.md` §2,
§2b; interval soundness §4.13).

**Required support and interface data (§8):** reads: none; updates: none.
Boundary labels, interfaces, logical witnesses, certificates are `not yet
defined` future-Π data ([`STATE_MODEL.md`](STATE_MODEL.md) §1/§1a) and are not
read; the layout is ledger data ([`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md)
§2d) and is not read. Nothing is invalidated; no inverse data is required.

**Complexity (§9)** (parameters: $n$ qubits, $m$ displayed rows, `nnz`
nonzeros): applicability check — none (O(1)); output construction — O(1) (no
update is performed); CSS-validity check — none needed (output = input);
logical-class transport — not computed (identity); exact-distance computation
— never performed by the calculus, consumer-side if a consumer requires it;
certificate validation — not applicable (no MVP operation reads a
certificate).

**Underivability:** *none.* Skip deliberately withholds no claim: every
quantity of the output equals the quantity of the input.

**Partial inverse (§10):** exact inverse — `skip` itself.

**Provenance (§11):** nothing semantic: the state is unchanged, and the
generic §11 list is vacuous here except the operation ID and contract version
for audit.

**Evidence (§12):** definitional from the base rule
([`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §1, §2); §4.6
(`OBL-SKIP-IDENTITY`), §4.7 (`OBL-WELL-FORMEDNESS-PRESERVATION`), §4.8
(`OBL-PRIMITIVE-DETERMINISM`), §4.11 (`OBL-JUDGMENT-SOUNDNESS`), §4.13
(`OBL-PRICED-INTERVAL-SOUNDNESS`), §4.21–§4.22, §4.37, and §4.40 (metatheorem
re-discharge); carry-table row `C-SKIP`, [`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2, §2b.

### `C-DIRECT-SUM` — Direct sum (`e₁ ⊕ e₂`)

**Taxonomy ID:** `C-DIRECT-SUM`. **Layer:** Core CSS calculus.
**Syntax category / kind:** expression-constructor
(`e ::= e_1 \oplus e_2`, [`TERM_LANGUAGE.md`](TERM_LANGUAGE.md) §2) — not a
unary command, which is the case §1's operation-kind list exists to keep
distinct.
**Primitive or derived:** primitive production.
**Contract status:** `contract-proved` (promoted 2026-11-18; record completed 2026-10-27).

**Input / output (§2):** two presented states $C_A$, $C_B$; the output is the
state on $Q_A \sqcup Q_B$ with rows concatenated and identifier sets unioned.
**Applicability (§3):** $Q_A \cap Q_B = \varnothing$ and
$\mathsf{used}_A \cap \mathsf{used}_B = \varnothing$; either collision makes
the constructor **inapplicable** (no derivation), not malformed. Ambient
containment in $\mathbb{F}_2^{Q_A \sqcup Q_B}$ is inherited from the factors.
**State update:** $Q$, display, and `used` exactly as §2 states; no mint
occurs. **Inapplicability:** either disjointness premise fails.
**Deterministic:** yes (§4.8, re-discharged §4.40).
**Well-formedness obligation (§12):** `OBL-WELL-FORMEDNESS-PRESERVATION`,
proved §4.7 (re-discharged §4.40).

**Structural effects (§4):** $n = n_A + n_B$, $k = k_A + k_B$,
$w = \max(w_A, w_B)$, exact `[proved]` (§4.4, §4.7, carry table §2; laws §4.8);
$r = \max(r_A, r_B)$ `[proved]` with merged-layout honesty `[conditional]` on
an honestly merged consumer layout (§2d.3, §2d.5, §4.21); Tanner connectivity
$\kappa = \kappa_A + \kappa_B$ ($\ge 2$ for nonempty factors — disconnected)
`[proved]` (§4.22); $\mathsf{preserves}_U$ carries when $U$ is supported on one
summand `[proved]` (§2h, §4.37); equal-syndrome weight floor carries by
weakening as $\omega \ge \lceil \min(L_d^A, L_d^B)/2\rceil$ `[proved]` (§2h, §4.37).
**Logical effects (§5):** $k = k_A + k_B$ `[proved]` (§4.4); canonical
quotient-level isomorphism
$\mathcal{L}_\sigma(C_A \oplus C_B) \cong \mathcal{L}_\sigma(C_A) \oplus \mathcal{L}_\sigma(C_B)$
for both sectors $\sigma \in \{X, Z\}$ `[proved]` (§4.39), from which
$d_\sigma(C_A \oplus C_B) = \min(d_\sigma(C_A), d_\sigma(C_B))$ follows (§4.4).
**Metric-preservation status (§7):** exact against the summands:
$d_X = \min(d_X^A, d_X^B)$, $d_Z = \min(d_Z^A, d_Z^B)$, $d = \min(d^A, d^B)$
`[proved]` (§4.4); every monotonicity slot holds as equality.
**Conditional carry cell:** distance carries are unconditional exact `min`
(§2, §2b, §4.13); interaction-radius honesty requires a consumer-supplied
honestly merged layout (`[conditional]`, §2d.3, §2d.5, §4.21), and the
addition clause of `OBL-FRAME-LAW` requires the allocation-compatibility mint
premise (`[conditional]`, §4.9).

**Required support and interface data (§8):** reads: $Q_A$, $Q_B$,
$\mathsf{used}_A$, $\mathsf{used}_B$ — required for applicability (the two
disjointness premises). Updates: $Q$ (union), display (concatenation),
`used` (union). The summand partition is **not** retained in the state (see
*Provenance*). Certificates, boundary labels, interfaces, logical witnesses:
`not yet defined` future-Π data, not read; the layout is ledger data (§2d),
not read — a merged layout must be supplied by the consumer, honestly merged
(§2d.3), for the $r$ row to be computed at all.

**Complexity (§9)** (parameters: $n$, $m$, `nnz`, $|\mathsf{used}|$):
applicability check — two namespace disjointness checks,
$O(n_A + n_B + |\mathsf{used}_A| + |\mathsf{used}_B|)$ with hashing or
sorting; output construction — linear in the total display; CSS-validity
check — none beyond the premises (output well-formedness is §4.7's argument,
not a runtime check); logical-class transport — not computed; exact-distance
computation — never performed by the calculus (the $\min$ law is a judgment,
not a computation); certificate validation — not applicable (no certificate
is read).

**Underivability:** *none.* Nothing about the sum is withheld by design: the
structural and distance laws are exact, and no quantity is withheld that any
admitted input would supply.

**Partial inverse (§10):** partial inverse requiring retained data — the
summand partition (which qubits and rows came from which parent). The kernel
contains no split rule, so inversion is data recovery, not an evaluation; the
disconnectedness note at [`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2 records
why the sum is terminal for connectivity purposes. **Information lost:** the
partition — the merged state alone does not record how it was summed.
**Multiplicity:** non-unique without the retained partition; with it, recovery
is exact.

**Provenance (§11):** the summand partition of $Q$ and of the row set; the
parent state identifiers. Required for the partial inverse above and for any
later factorization; nothing else is consumed or produced.

**Evidence (§12):** §4.4 (parameters and distances), §4.7 (well-formedness),
§4.8 (`OBL-DIRECT-SUM-LAWS`, `OBL-PRIMITIVE-DETERMINISM`), §4.9
(`OBL-FRAME-LAW`), §4.11 (`OBL-JUDGMENT-SOUNDNESS`), §4.13
(`OBL-PRICED-INTERVAL-SOUNDNESS`), §4.21–§4.22, §4.37, §4.39 (quotient
isomorphism), and §4.40 (metatheorem re-discharge); carry-table rows,
[`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2, §2b, §2d.5.

### `C-DELETE-CHECK` — Stabilizer/check deletion (`delete_r`)

**Taxonomy ID:** `C-DELETE-CHECK`. **Layer:** Core CSS-code transformation.
**Syntax category / kind:** command (`m ::= \mathrm{delete}_r`,
[`TERM_LANGUAGE.md`](TERM_LANGUAGE.md) §2).
**Primitive or derived:** Primitive.
**Contract status:** `contract-proved` (promoted 2026-11-18; record
completed 2026-10-27; the template above shows this card's identity block in
illustrative form).

**Input / output (§2):** presented state $C$ and a displayed generator $r$;
the output is the state with exactly $r$ removed. **Applicability (§3):**
$\mathrm{DisplayedGenerator}(r,\mathsf{pres})$ and
$\mathrm{Independent}(r;\mathsf{pres})$ — span non-membership
$r \notin \langle \mathit{rows}_\tau \setminus \{r\}\rangle$ (§4.7), which
holds for every displayed $r$ by I2. **State update:** $Q$ unchanged; $r$
removed from the presentation and its sector row space; the identifier is
**retired but stays in `used`** (no mint). **Inapplicability:** a
non-displayed or dependent $r$ gives no derivation (`W10`: no partial result,
no half-updated state). **Deterministic:** yes (§4.8, re-discharged §4.40).
**Well-formedness obligation (§12):** `OBL-WELL-FORMEDNESS-PRESERVATION`,
proved §4.7 (re-discharged §4.40).

**Structural effects (§4):** $n'=n$, $k'=k+1$, exact `[proved]` (§4.1); $w'$ is
the max over the remaining displayed rows (exact, $\le w$) `[proved]` (§4.7,
carry table §2); $r' = \max\{\mathrm{diam}_\lambda(s) : s \in \mathit{rows}'\}
\le r$ with layout honesty preserved `[proved]` (§2d.5, §4.21); Tanner
connectivity $\kappa'$ recomputed (can decrease) `[proved]` (§4.22);
$\mathsf{preserves}_U$ does not carry (`[false]`, two-qubit counterexample
§4.37); equal-syndrome weight floor carries by weakening as
$\omega' \ge \lceil L_d'/2\rceil$ (recomputed from $L_d'$, parent value does
not substitute, Shor-code counterexample §4.37) `[proved]`.
**Logical effects (§5):** each sector's child logical vectors are supersets
of the parent's — the set-inclusion basis of §4.5 `[proved]`; exact
quotient-level transport `[proved]` (§4.39): for a deleted $\tau$-row $r$,
same-sector canonical surjection
$0 \to \tau/\tau' \to \mathcal{L}_\tau(C') \xrightarrow{\pi_\tau} \mathcal{L}_\tau(C) \to 0$
admitting the promoted class $r + \tau'$ and splitting every parent class into
two child classes, and opposite-sector canonical injection
$0 \to \mathcal{L}_{\bar\tau}(C) \xrightarrow{\iota_{\bar\tau}} \mathcal{L}_{\bar\tau}(C') \xrightarrow{\bar\ell_r} \mathbb{F}_2 \to 0$
admitting the $2^{k(C)}$ exposed classes anticommuting with $r$ (forming a
conjugate logical pair with $r + \tau'$).
**Metric-preservation status (§7):** preserves either sector exactly: claim
shape `unavailable` (inventory row *exact unpriced post-deletion values*,
scoped by the 2026-09-26 review); monotonicity: nonincreasing — $d_X' \le d_X$,
$d_Z' \le d_Z$, $d' \le d$ `[proved]` (§4.5). **Conditional carry cell:**
priced full-distance deletion $d' = \min(d, w_{\rm del}, w_{\rm exp})$ carries
only with consumer-supplied $(w_{\rm del}, w_{\rm exp})$ and evidence reference
`[conditional]` (§2a, §2b, §2c, reproduced at §4.19 Theorem 12.1; interval
soundness §4.13; moves full-distance endpoints only, never sector endpoints).

**Required support and interface data (§8):** reads: the identity of
displayed row $r$ (term data) — required for applicability — and the display's
independence fact. Updates: presentation and sector row space (row removed);
`used` unchanged (retirement, not deletion). **Invalidated:** row-referencing
certificates in consumer ledgers — through the `C-DELETE-CHECK` →
`C-ADD-CHECK` loop they are `unavailable` even though the final code equals
the original (information-losing at the context level;
[`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2, three-claims table; keyed by
§4.24). Boundary labels, interfaces, logical witnesses: `not yet defined`,
not read; layout: ledger data (§2d), not read.

**Complexity (§9)** (parameters: $n$, $m$, `nnz`, $|\mathsf{used}|$):
applicability check — display lookup linear in $m$; independence is span
non-membership, decidable by Gaussian elimination over $\mathbb F_2$ in
polynomial time, with no search (the premise holds for every displayed row by
I2); output construction — linear in the display; CSS-validity check — none
at runtime (output well-formedness is §4.7's argument); logical-class
transport — not computed; exact-distance computation — never performed by the
calculus; certificate validation — not applicable (the transition reads no
certificate).

**Underivability.** Deliberately withheld by this operation:

- **exact unpriced post-deletion values** $d$, $d_X$, $d_Z$ — `unavailable`,
 lower bounds *and* equalities (the same scope, 2026-09-26; exact post-deletion
 distance is a stated non-goal, 2026-10-20): pinning a value needs a
 minimum-weight-coset computation the rule system does not contain. Scope:
 per evaluation, never per state;
- **a row-referencing certificate through the `C-DELETE-CHECK` →
 `C-ADD-CHECK` loop** — `unavailable`, because the deletion step invalidates
 it even when the final code equals the original
 ([`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2, three-claims table).

The non-increase upper bound is **not** withheld: it is derived (§4.5).

**Partial inverse (§10):** partial inverse requiring retained data —
`C-ADD-CHECK` with the removed row's support re-establishes the row space
(`OBL-PARTIAL-INVERSE-LAWS`, `proved`, §4.9). **Information lost:** the
identifier — retired identifiers are never re-minted, so the loop's endpoint
is not $\equiv$-equal to the parent, and the original presentation choice is
recovered only from retained provenance. **Multiplicity:** many parents admit
the same deletion only up to the retained row identity; the choice of $r$
determines the child.

**Provenance (§11):** the removed row's identity, sector, and support —
required for the partial inverse and for auditing any later re-add; the
parent state identifier; the retirement fact is already recorded in `used`.

**Evidence (§12):** §4.1 ($n, k$), §4.5 (non-increase bound; disposition),
§4.7 (well-formedness), §4.8 (`OBL-PRIMITIVE-DETERMINISM`), §4.9 (partial
inverse, frame law), §4.10 (`OBL-CROSS-SECTOR-PERMUTATION`), §4.11
(`OBL-JUDGMENT-SOUNDNESS`, `OBL-JUDGMENT-TRANSPORT`), §4.13
(`OBL-PRICED-INTERVAL-SOUNDNESS`), §4.15 (`OBL-ORDER-INDEPENDENT-DELETION`),
§4.16–§4.18 (`OBL-ROW-REPLACEMENT-FACTOR`, `OBL-FIXED-NAMESPACE-REACHABILITY`),
§4.19 (Theorem 12.1 conditional price), §4.21–§4.22, §4.37, §4.39 (quotient
exact sequences), and §4.40 (metatheorem re-discharge); carry-table rows,
[`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2, §2a–§2c.

### `C-ADD-CHECK` — Stabilizer/check addition (`addStab_r`)

**Taxonomy ID:** `C-ADD-CHECK`. **Layer:** Core CSS-code transformation.
**Syntax category / kind:** command (`m ::= \mathrm{addStab}_r`,
[`TERM_LANGUAGE.md`](TERM_LANGUAGE.md) §2).
**Primitive or derived:** Primitive.
**Contract status:** `contract-proved` (promoted 2026-11-18; record completed 2026-10-27).

**Input / output (§2):** presented state $C$ and a typed check row $r : \tau$
($\tau \in \{X, Z\}$); the output is the state with $r$ added to the display
and its sector row space under a canonically minted identifier.
**Applicability (§3):** four premises (`OPERATIONAL_SEMANTICS.md` §2):
(1) ambient membership $r \in \mathbb{F}_2^Q$, i.e. $\mathrm{supp}(r) \subseteq Q$
(probe `W22`); (2) opposite-sector commutation inside $\mathbb{F}_2^Q$
($r \in Z^\perp$ for $\tau = X$, $r \in X^\perp$ for $\tau = Z$);
(3) same-sector independence ($r \notin X$ for $\tau = X$, $r \notin Z$ for
$\tau = Z$); and (4) identifier capacity (H-4: the fixed
70,000-name enumeration of `STATE_MODEL.md` I3 is not exhausted by `used`).
**State update:** $Q$ unchanged; presentation gains $r$ with sector $\tau$ and
the canonical mint `mint(used)`; sector row space becomes
$\tau' = \tau \oplus \langle r\rangle$; `used` gains the minted identifier.
**Inapplicability:** failure of any of the four premises gives no derivation
(`W22`, H-4). **Deterministic:** yes (§4.8, re-discharged §4.40).
**Well-formedness obligation (§12):** `OBL-WELL-FORMEDNESS-PRESERVATION`,
proved §4.7 (re-discharged §4.40).

**Structural effects (§4):** $n'=n$, $k'=k-1$, exact `[proved]` (§4.2); $w' =
\max(w, \mathrm{wt}(r))$ `[proved]` (§4.7, carry table §2);
$r' = \max(r, \mathrm{diam}_\lambda(r_{\rm new})) \ge r$ with layout honesty
preserved `[proved]` (§2d.5, §4.21); Tanner connectivity $\kappa' \le \kappa$
(cannot decrease) `[proved]` (§4.22); $\mathsf{preserves}_U$ carries at every
angle when all gate generators commute with $r$, carries at all angles $\pi/4$
iff $V_r \in \mathcal{S}(C')$, and remains `not yet defined` when a generator
anticommutes with $r$ at an angle $\neq \pi/4$ `[proved]` (§2h, §4.37);
equal-syndrome weight floor $\omega' \ge \lceil L_d'/2\rceil \ge \lceil L_d/2\rceil$
does not decrease `[proved]` (§2h, §4.37).
**Logical effects (§5):** the child logical vectors are subsets of the
parent's — the set-inclusion basis of §4.3 `[proved]`; exact quotient-level
transport `[proved]` (§4.39): for an added $\tau$-row $r$, same-sector
canonical surjection
$0 \to \tau'/\tau \to \mathcal{L}_\tau(C) \xrightarrow{\pi_\tau} \mathcal{L}_\tau(C') \to 0$
absorbing $r + \tau$ and merging each surviving pair $\{u + \tau, (u + r) + \tau\}$,
and opposite-sector canonical injection
$0 \to \mathcal{L}_{\bar\tau}(C') \xrightarrow{\iota_{\bar\tau}} \mathcal{L}_{\bar\tau}(C) \xrightarrow{\bar\ell_r} \mathbb{F}_2 \to 0$
keeping the commuting subgroup and removing the $2^{k(C)-1}$ parent classes
anticommuting with $r$.
**Metric-preservation status (§7):** resets the upper endpoint to $+\infty$
(tightened only by child-valid witnesses) and carries the lower endpoint;
monotonicity: nondecreasing — $d_X' \ge d_X$, $d_Z' \ge d_Z$, $d' \ge d$
`[proved]` (§4.3; ordinary CSS stabilizer codes only, no gauging); exact
post-addition distance values remain `open`. **Conditional carry cells (§2a):**
three consumer-supplied conditional cells (`JUDGMENT_LAYER.md` §2a, §2c):
(i) *strict improvement* $d' \ge d + 1$ `[conditional]` on exact old $d$ and
exhaustive minimum-weight-class enumeration with all classes killed
(Proposition 18.3, reproduced at §4.19; $d = 1$ screen in §2a);
(ii) *sector-aware gauging* raising $L_\sigma$ to supplied $w_\sigma$
`[conditional]` on surviving-class sector minima $(w_X, w_Z)$ and evidence
reference (Lemma 18.5); and (iii) *direct-sum extinction* $d' = d_B$ exact
`[conditional]` on a two-block stack parent with one block extinguished
($k'_A = 0, k_B \ge 1$) and trusted $d_B > d_A$ (Proposition 18.6 + Corollary
18.7).

**Required support and interface data (§8):** reads: the typed row $r : \tau$
(term data), $Q$, both displayed sectors, and `used` — required for
applicability and canonical minting. Updates: presentation and sector row space
(row added); `used` gains the minted identifier. Boundary labels, interfaces,
logical witnesses: `not yet defined`, not read; layout: ledger data (§2d), not
read.

**Complexity (§9)** (parameters: $n$, $m$, `nnz`, $|\mathsf{used}|$):
applicability check — ambient containment linear in $|r|$; opposite-sector
commutation linear in `nnz`; same-sector independence is span non-membership,
decidable by Gaussian elimination over $\mathbb F_2$ in polynomial time;
capacity check $O(|\mathsf{used}|)$; output construction — linear in the
display; CSS-validity check — none beyond the premises; logical-class transport
— not computed; exact-distance computation — never performed by the calculus;
certificate validation — not applicable.

**Underivability.** Deliberately withheld by this operation: none beyond those
recorded for the loop — a row-referencing certificate through the
`C-DELETE-CHECK` → `C-ADD-CHECK` loop is `unavailable`, and strict improvement
without an exhaustive minimum-weight-class hypothesis is `unavailable`
(`JUDGMENT_LAYER.md` §2, §2a). Exact unconditional post-addition distance is
`open`, not withheld as `unavailable`.

**Partial inverse (§10):** partial inverse requiring retained data —
`C-DELETE-CHECK` removes the added row and restores the row space
(`OBL-PARTIAL-INVERSE-LAWS`, `proved`, §4.9). **Information lost:** the
minted identifier is retired and never re-minted, so the loop's endpoint is
not $\equiv$-equal to the parent. **Multiplicity:** the choice of row $r$
determines the child.

**Provenance (§11):** the added row's identity, sector, and support —
required for the partial inverse and for auditing; the parent state
identifier; the mint fact recorded in `used`; on the judgment side, any
conditional input evidence reference (§2c).

**Evidence (§12):** §4.2 ($n, k$), §4.3 (distance monotonicity), §4.7
(well-formedness), §4.8 (`OBL-PRIMITIVE-DETERMINISM`), §4.9 (partial inverse,
conditional addition clause of `OBL-FRAME-LAW`), §4.10
(`OBL-CROSS-SECTOR-PERMUTATION`), §4.11 (`OBL-JUDGMENT-SOUNDNESS`,
`OBL-JUDGMENT-TRANSPORT`), §4.13 (`OBL-PRICED-INTERVAL-SOUNDNESS`), §4.16–§4.18
(`OBL-ROW-REPLACEMENT-FACTOR`, `OBL-FIXED-NAMESPACE-REACHABILITY`), §4.19
(Proposition 18.3 strict improvement), §4.21–§4.22, §4.37, §4.39 (quotient
exact sequences), and §4.40 (metatheorem re-discharge); conditional cells
Proposition 18.3, Lemma 18.5, Proposition 18.6 + Corollary 18.7 in
[`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2, §2a–§2c.

### `C-SEQUENCE` — Sequencing (`m_1 ; m_2`)

**Taxonomy ID:** `C-SEQUENCE`. **Layer:** Core CSS-code transformation.
**Syntax category / kind:** command combinator (`m ::= m_1 ; m_2`,
[`TERM_LANGUAGE.md`](TERM_LANGUAGE.md) §2).
**Primitive or derived:** Primitive.
**Contract status:** `contract-proved` (promoted 2026-11-18; record completed 2026-10-27).

**Input / output (§2):** presented state $C_0$; the output is the state
produced by running $m_1$ to intermediate state $C_1$ and then $m_2$ against
$C_1$. **Applicability (§3):** none of its own — the premises are those of
$m_1$ on $C_0$ and $m_2$ on $C_1$, composed left-to-right; if either
sub-command is inapplicable, the whole sequence has no derivation (`W10`: no
stuck residual, no half-updated state). **State update:** the output of $m_1$
feeds $m_2$. **Inapplicability:** a failing premise in either sub-command.
**Deterministic:** yes (§4.8, re-discharged §4.40).
**Well-formedness obligation (§12):** `OBL-WELL-FORMEDNESS-PRESERVATION`,
proved §4.7 (re-discharged §4.40).

**Structural effects (§4):** composition of the sub-transitions' carry rows
for $n$, $k$, $w$, $r$, $\kappa$, $\mathsf{preserves}_U$, $\omega$ (weakening),
and output well-formedness `[proved]` (§4.7, §4.11, §4.21–§4.22, §4.37;
inventory row *structural-fact persistence through sequences*).
**Logical effects (§5):** logical-quotient transport maps and exact sequences
compose step by step from the sub-transitions (§4.39); generator-referencing
claims $\mathsf{gen}_i$ transport across surviving steps under the seam
condition and are refused (`W13`) across any retiring step `[proved]` (§4.11,
`JUDGMENT_LAYER.md` §4).
**Metric-preservation status (§7):** single-polarity distance chains (equalities
and same-direction inequalities) compose by L3 `TRANSITIVITY` `[proved]`
(§4.11); mixed opposite-polarity exact-quantity chains remain `open` (no
two-sided composite bound in L3). **Conditional carry cell:** consumer interval
transport composes arbitrary sequences by $F_{m_2} \circ F_{m_1}$ `[proved]`
(`OBL-PRICED-INTERVAL-SOUNDNESS`, §4.13, `JUDGMENT_LAYER.md` §8.5; conditional
on any step-level consumer-supplied prices, bounds, or witnesses, and per
`OBL-GATE6-CSS-EXTENSIONS` §4.32 when Gate 6 steps occur).

**Required support and interface data (§8):** reads: none of its own; the
sub-commands' required data. Updates: none of its own. Boundary labels,
interfaces, logical witnesses: `not yet defined`, not read; layout: ledger
data (§2d), transported step by step (§2d.5).

**Complexity (§9)** (parameters: $n$, $m$, `nnz`, $|\mathsf{used}|$):
applicability check — composition of the sub-checks; output construction —
composition; CSS-validity check — none at runtime; logical-class transport —
composed; exact-distance computation — never performed by the calculus;
certificate validation — not applicable.

**Underivability.** Deliberately withheld by this operation: claims referencing
a generator deleted/retired earlier in the sequence (`W13`, `unavailable` per
evaluation, `OBL-JUDGMENT-TRANSPORT`, `JUDGMENT_LAYER.md` §4); otherwise the
withheld quantities of its sub-transitions.

**Partial inverse (§10):** none in the kernel — there is no inverse combinator;
recovery requires retained per-step data. **Information lost:** the
intermediate state unless retained. **Multiplicity:** non-unique.

**Provenance (§11):** the intermediate state, if retained; the two
sub-command identifiers (and per-step order, since sequencing is not
commutative in general).

**Evidence (§12):** §4.6 (`OBL-SKIP-IDENTITY`), §4.7 (well-formedness), §4.8
(`OBL-SEQUENCE-ASSOCIATIVITY`, `OBL-PRIMITIVE-DETERMINISM`), §4.10
(`OBL-CROSS-SECTOR-PERMUTATION`), §4.11 (`OBL-JUDGMENT-SOUNDNESS`,
`OBL-JUDGMENT-TRANSPORT`), §4.13 (`OBL-PRICED-INTERVAL-SOUNDNESS`), §4.15
(`OBL-ORDER-INDEPENDENT-DELETION`), §4.17 (`OBL-FIXED-NAMESPACE-REACHABILITY`),
§4.21–§4.23, §4.37, and §4.40 (metatheorem re-discharge); carry-table rows,
[`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2, §4, §5, §8.5.

## `E-GRAFT` — Row-space graft transition

**Taxonomy ID:** `E-GRAFT`

**Introduced in:** `stdCSS-2`.

**Layer:** In-scope conditional CSS-code extension; transition soundness proved under the coverage guard (§4.12)

**Primitive or derived:** Primitive transition over a presented CSS state

**Transition status:** `transition-defined`; its contract fields were completed
for Gate 0 on 2026-10-27 and its transition soundness is `proved` under the
coverage guard (§4.12), but no dated decision has promoted the rung to
`contract-proved`. It is included in the design scope.

**Input:** A well-formed presented CSS state, qubit $q$, selected sector
$\tau\in\{X,Z\}$, and an ordered list of all displayed $\tau$ rows touching
$q$.

**Output:** A presented CSS state on $Q\setminus\{q\}$, with the listed
selected-sector chain replaced by adjacent products and opposite-sector rows
shortened at $q$.

**Applicability:** The list is exact, nonempty, and duplicate-free; the output
passes CSS orthogonality and displayed independence; it preserves $k$; and each
remaining qubit is covered by both check sectors. The coverage condition is an
empirical modeling guard, not a universal theorem.

**Distance judgment:** The graft relation is **sector-wise**. The source states
$d'_\sigma=\min(d_\sigma,w_{\rm expose,\sigma})$ for each sector $\sigma$ and
$d'=\min(d,w_{\rm expose,\bar\tau})$ for the full distance, under the stated
exposure-minimum and coverage hypotheses. The spliced sector's exposure set is
empty, so $w_{\rm expose,\tau}=\infty$; but under the transition as specified
in `OPERATIONAL_SEMANTICS.md` §2 the spliced sector satisfies
$d'_\tau\ge d_\tau$ with strict inequality possible, so the source's exact
relation $d'_\tau=d_\tau$ is **false** for this transition (§4.13 and §4.20,
2026-10-21). The spliced sector therefore carries its lower endpoint and drops
its upper endpoint to $+\infty$ unless a witness valid in the child supplies
one; as at every sector, a witness may tighten an upper endpoint and never
widen or discard one. The non-spliced
sector is where exposure happens, so without a numeric price the consumer
carries only the admitted non-increase bound and current valid witnesses, and
infers no positive lower bound. The exposure price is indexed to the
non-spliced sector and so licenses that sector's exact interval as well as
the full distance's.

**Complexity boundary:** State construction and its finite-field guards are
executable. The exposure minimum is supplied externally; this consumer neither
computes nor checks it. The transition's output well-formedness obligation is
`OBL-GRAFT-TRANSITION-SOUNDNESS`.

**Required support and interface data (§8), completed 2026-10-27 (Gate 0):**
reads: qubit $q$, sector $\tau$, and the ordered chain of displayed row
identifiers (term data) — required for applicability. Updates: presentation
(listed rows retired, adjacent products minted canonically), the selected
sector row space, opposite-sector supports (shortened at $q$), and `used`
(grows by the minted identifiers). Prices and lower bounds are **judgment
inputs, not command data** (§2a, §2c). Certificates: none read — the
transition consumes no certificate; boundary labels, interfaces, logical
witnesses: `not yet defined` future-Π data, not read; layout: ledger data
(§2d), not read. Nothing is invalidated by the state update itself.

**Complexity (§9), completed 2026-10-27** (parameters: $n$, $m$, `nnz`,
chain length): applicability check — list exactness linear in the display;
CSS orthogonality and displayed independence by Gaussian elimination over
$\mathbb F_2$ (polynomial); the $k'=k$ and coverage guards are rank and
traversal computations (polynomial); output construction — linear in the
display and chain; CSS-validity check — those guards are it; logical-class
transport — not computed; exact-distance computation — never performed by the
calculus (the exposure minimum is supplied externally); certificate
validation — not applicable (no certificate is read).

**Underivability, completed 2026-10-27.** Deliberately withheld by this
operation:

- **a positive lower bound without a supplied exposure price** — the consumer
 carries only the admitted non-increase bound and child-valid witnesses and
 infers no positive lower bound: refusal is the default for unpriced moves
 ( §3–§4). Scope: evaluations of
 `E-GRAFT` under the admitted graft relation;
- the scalar exact form $d' = \min(d, w_{\mathrm{expose}})$ is **not**
 withheld but **refuted** for this transition (§4.20): only the sector-wise
 form is admissible, and the scalar row reads `open`, never `unavailable`.

**Partial inverse (§10):** partial inverse requiring retained data — the
removed qubit, the touching rows, and inverse presentation information; the
relation is generally non-unique ([`spec/TAXONOMY.md`](TAXONOMY.md) §2.7).
No inverse-direction transition is admitted, so the inverse is data, not a
rule.

**Provenance (§11):** the ordered chain (row identifiers and their order),
$q$, and $\tau$; retired identifiers (already recorded in `used`); the parent
state identifier; on the judgment side, price and lower-bound source
references (§2c).

**Evidence (§12):** §2 (transition); §4.12
(`OBL-GRAFT-TRANSITION-SOUNDNESS`), §4.13 (`OBL-PRICED-INTERVAL-SOUNDNESS`),
§4.14 (`OBL-PRICED-INPUT-SEMANTICS`); §4.19 and §4.20 (reproduced
derivations and the scalar refutation); carry rows §2 and §2a.

The contract must identify whether the operation is:

- a supporting presentation operation;
- a CSS-code transformation;
- a lower-level constructor; or
- an extended-state operation.

It must also say whether the operation is primitive or factors through earlier operations.

---

## Gate 6 CSS extension transitions (conditional cells, 2026-10-23)

**Introduced in:** `stdCSS-2` (cells admitted 2026-10-23; `JUDGMENT_LAYER.md`
§2f). Five of the six admitted CSS-level extensions have typed command transitions
(`TERM_LANGUAGE.md` §2; `OPERATIONAL_SEMANTICS.md` §2, derivations
§4.26–§4.30); `E-GLUE` remains **binary-only, with no unary command
production** (dated maintainer decision 2026-11-18), recorded as
the binary state-expression constructor $e ::= \mathrm{glue}(e_1, e_2; \vec u)$
(`TERM_LANGUAGE.md` §1–§2) with its admitted evaluator transition
(`OPERATIONAL_SEMANTICS.md` §4.31). Both future-$\Pi$ fields are defined in
full (`STATE_MODEL.md` §1a), the CSS-level algebra
of the extracted §4.31/§4.33 derivation is mechanized in Lean
(`lean/CodeCalculus/GlueExtraction.lean`) with the irreducible
geometric move-word gap explicitly recorded, and `E-GLUE` advances to
`contract-stated` (rung 5, dated maintainer decision 2026-11-18).
The other five cards below follow the `E-GRAFT` card's shape at
`transition-defined`; each move's sound admission is
`OBL-GATE6-CSS-EXTENSIONS`. None of these is claimed as a proved
formal-calculus rule, Gate 6 remains unchecked, and the cells remain
conditional on their hypotheses.

### `P-REBASE` — Sector basis change (`rebase`)

**Taxonomy ID:** `P-REBASE`. **Layer:** supporting presentation.
**Transition status:** `transition-defined` (§4.26).

**Input:** a well-formed presented CSS state and, per sector, a matrix
$M\in\mathbb{F}_2^{m\times m}$ over the displayed $\tau$-rows ($m$ = that
sector's display count).

**Output:** the same state on $Q'$=$Q$ with each $\tau$-display row replaced
by $v_i' = \bigoplus_j M_{ij}v_j$, rows minted canonically, supports sorted.

**Applicability:** $M$ invertible over $\mathbb{F}_2$; a singular $M$ gives no
derivation (the inverted-mint output would not register — §4.26's I2
argument). No rows minted beyond the $m$ replacements; `used` grows by exactly
those identifiers.

**Structural and distance judgment:** spans unchanged in the rebased sector
(and untouched elsewhere), so $n$, $k$, $d_X$, $d_Z$, $d$ carry **exactly**
(both endpoints; §4.26). $w$, radius, and Tanner connectivity are
display-relative and are recomputed exactly over the child display.

**Not claimed:** support-sensitive (future-$\Pi$) predicates; equivalence of a
`rebase` command and a delete/add loop at the labeled-state level
(`OBL-DERIVED-TERM-FACTORIZATION` covers factorization for *derived* commands;
`rebase` is stated as primitive, its set identification with the loop lives in
`OBL-REBASE-GENERATION`, discharged §4.26 as a set identity modulo mint).

**Required support and interface data (§8), completed 2026-10-27 (Gate 0):**
reads: the matrix $M$ and the sector (term data) — $M \in \mathrm{GL}(m,2)$
is a checked structural premise, not a trusted input. Updates: the displayed
rows of the rebased sector (the $m$ replacements, each minted canonically, so
`used` grows by exactly $m$); $Q$ and both row spaces unchanged.
Support-sensitive predicates: `not yet defined` future-Π data, not read;
certificates: none read; layout: ledger data (§2d), not read — $w$, $r$, and
connectivity are recomputed over the child display by the consumer.

**Complexity (§9), completed 2026-10-27** (parameters: $m$ displayed rows of
the sector, $n$, `nnz`): applicability check — invertibility of $M$ by
Gaussian elimination over $\mathbb F_2$ ($O(m^3)$ in the sector basis,
polynomial in the display); output construction — the basis change, polynomial
in $m$ and the display size; CSS-validity check — span preservation is the
GL premise, and §4.26's I2 argument is the validity record; logical-class
transport — not computed (spans are unchanged); exact-distance computation —
never performed by the calculus (the span-exact carries are judgments);
certificate validation — not applicable.

**Underivability, completed 2026-10-27.** Deliberately withheld by this
operation:

- **labeled-state equivalence between `rebase` and its delete/add loop** —
 deliberately not claimed: only the set identity modulo mint is proved
 (§4.26), and the labeled-level identification is the withheld statement.
 Scope: statements that quantify over labeled endpoints of a `rebase`
 command.

Support-sensitive (future-$\Pi$) predicates are `not yet defined`, outside
the assertion language — not withheld.

**Partial inverse (§10):** partial inverse requiring retained data — any
other basis change, i.e. a rebase by $M^{-1}$ (`TAXONOMY.md` §1.2); with $M$
or the input basis retained the inverse is exact at set level, while fresh
mints keep labeled endpoints distinct (identification modulo mint, §4.26).

**Provenance (§11):** $M$ (and its inverse, if the inverse direction is
wanted), the sector, the replaced row identifiers (retired, in `used`), the
input basis row identifiers, and the parent state identifier.

### `E-PEEL` — Restricted $r=1$ grafting, the reduction direction (`peel`)

**Taxonomy ID:** `E-PEEL`. **Layer:** conditional CSS transformation.
**Transition status:** `transition-defined` (§4.28).

**Input:** a well-formed presented CSS state, a qubit $q$, a selected sector
$\tau$, and a displayed $\tau$-row $r$ containing $q$.

**Output:** a CSS state on $Q\setminus\{q\}$ with $r$ removed (identifier
retired, retained in `used`), opposite-sector rows shortened at $q$.

**Applicability:** $r$ is the unique displayed $\tau$-row containing $q$.
A redundant zero-check guard (no opposite-sector displayed row with support
exactly $\{q\}$) is carried as a checker-honesty redundancy, not as a
constraint: it cannot bind under a well-formed parent (such a row would meet
$r$ exactly at $q$, an odd overlap — §4.28).

**Structural effects:** $n'=n-1$ exactly; the selected sector's rank drops
exactly one; the opposite sector's rank carries **exactly** (§4.28's
injectivity argument) — so $k'=k$ exactly.

**Distance judgment:** two sector-aware cells, conditional on their prices,
over unpriced carries. §4.28 derives the exact relations
$d_\tau'=w_{\mathrm{avoid},\tau}(q)$ for the selected sector (the lightest
parent $\tau$-logical avoiding $q$) and
$d_{\bar\tau}'=\min(d_{\bar\tau},w_{\mathrm{expose},\bar\tau}(q))$ for the
opposite sector (the graft's exposure relation at $m=1$), so unpriced the
selected lower endpoint carries, the opposite endpoints carry within one
($d_{\bar\tau}-1\le d_{\bar\tau}'\le d_{\bar\tau}$), and the full distance
takes the minima of the two sector intervals; the comparison with $d$ is
bounded in neither direction (the witness takes $(d_X,d_Z)$ from $(2,1)$ to
$(1,2)$). With the avoidance minimum the selected sector is pinned, and with
the exposure price the opposite sector moves as under the graft price
(`JUDGMENT_LAYER.md` §2a, §2b, §2c; carries admitted 2026-11-06; price cells and the sharpened carries 2026-11-10).

**Required support and interface data (§8), completed 2026-10-27 (Gate 0):**
reads: $q$, $\tau$, and the displayed row $r$ (term data) — the unique-touch
premise is required for applicability. Updates: $Q$ (qubit removed),
display ($r$ retired — its identifier stays in `used`, no mint — and every
opposite-sector row touching $q$ shortened). Certificates: none read;
boundary labels, interfaces, logical witnesses: `not yet defined`, not read;
layout: ledger data (§2d), not read — the child's layout is restricted to the
child's qubit labels by the recomputation rule (§2d.2).

**Complexity (§9), completed 2026-10-27** (parameters: $n$, $m$, `nnz`):
applicability check — the unique-touch scan over displayed $\tau$-rows
containing $q$, linear in the display; output construction — restriction of
the touched rows, linear in `nnz`; CSS-validity check — §4.28's odd-overlap
argument is the validity record (the redundant zero-check guard cannot bind
under a well-formed parent); logical-class transport — not computed;
exact-distance computation — never performed by the calculus (the intervals
reset and only witnesses supply endpoints); certificate validation — not
applicable.

**Underivability, completed 2026-10-27 (reworded 2026-10-29):**
*none recorded as `unavailable`.* No external source states a distance
formula for the peel; the two exact sector relations are derived in this
repository (§4.28, 2026-11-10) and admitted as conditional price cells, so
there is nothing withheld: the exact values are `conditional` on the
consumer-supplied minima, as every price cell is, and `open` only where no
price is supplied.

**Partial inverse (§10):** partial inverse requiring retained data —
qubit/check extension with the removed qubit, check, and support data
supplied (`TAXONOMY.md` §2.6).

**Provenance (§11):** the removed qubit's identity; the removed row's
identity, sector, and support; the pre-shortening supports of every
opposite-sector row that touched $q$ (required to undo the restriction); the
parent state identifier.

### `E-PUNCTURE` — Check-puncturing form (`puncture`)

**Taxonomy ID:** `E-PUNCTURE`. **Layer:** conditional CSS transformation.
**Transition status:** `transition-defined` (§4.29).

**Input:** a well-formed presented CSS state and a qubit $q\in Q$.

**Output:** a CSS state on $Q\setminus\{q\}$ with every displayed row of either
sector whose support contains $q$ removed (identifiers retired, retained in
`used`). This is the admitted induced stabilizer update — the §2.8 record
requires exactly such a statement, since raw column restriction without the
update is not a CSS operation.

**Applicability:** $q\in Q$; no further premise (I1–I5 hold automatically for
the registered output — §4.29); deterministic.

**Structural effects:** $n'=n-1$ exactly; the ranks fall by $t_X$ and $t_Z$
(the numbers of displayed $\tau$-rows containing $q$ in each sector), so
$k'=k-1+t_X+t_Z$ exactly (the §2.8 record's "not fixed by $n$ alone" is
true, but the formula is fixed by the ranks).

**Distance judgment:** no rule of either polarity; §4.29's refutation record
(puncturing the unnamed free qubit of $Q=\{0,1,2\}$ with the single $Z$
display $\{0,1\}$ raises the $X$ distance $1\to2$ — the deleted qubit's own
logical direction *was* the parent's lightest $X$ logical) means both sector
and full-distance intervals reset to $(0,\,+\infty)$, and only witnesses
valid in the child supply upper endpoints. Distance *prices* for this move
are deliberately not admitted in this scope: hole-punch pricing is blocked
on the D2 lower-bound question — **no cell and no fixture for it
enters until that lower bound lands**. The reduction is recorded (§4.29,
2026-11-10): a puncture is the deletion of every row through
$q$ followed by the removal of the then-free qubit, so each child sector
distance is the lightest $q$-free logical of that intermediate code,
$\min(w_{\mathrm{avoid},\sigma}(q),w_{\mathrm{hole},\sigma}(q))$; the hole
price has no unpriced bound in either direction (increase $1\to2$ above,
decrease $3\to2$ on $Z$ rows $\{0,1\},\{1,2\}$).

**Required support and interface data (§8), completed 2026-10-27 (Gate 0):**
reads: $q$ (term data) — the only premise is $q \in Q$. Updates: $Q$ (qubit
removed); every displayed row of either sector whose support contains $q$ is
retired (identifiers stay in `used`); no mint. Certificates: none read;
boundary labels, interfaces, logical witnesses: `not yet defined`, not read;
layout: ledger data (§2d), not read (child layout restricted per §2d.2).

**Complexity (§9), completed 2026-10-27** (parameters: $n$, $m$, `nnz`):
applicability check — membership of $q$ in $Q$, O(1) against the state index
(no further premise; I1–I5 hold automatically for the registered output,
§4.29); output construction — the scan for rows containing $q$ plus their
removal, linear in `nnz`; CSS-validity check — §4.29's registered-output
argument is the validity record; logical-class transport — not computed
($t_X$, $t_Z$ are display counts, not logical data); exact-distance
computation — never performed by the calculus; certificate validation — not
applicable.

**Underivability, completed 2026-10-27.** Deliberately withheld by this
operation:

- **hole-punch distance pricing (exact post-puncture distances)** —
 deliberately not admitted in this scope: blocked on the D2 lower-bound
 question, so no cell and no fixture enters until that lower bound lands
 (§2.8 record; §2f). Scope: `E-PUNCTURE` distance cells only. The full
 price reads `unavailable`; the partial facts about rectangular holes are
 records, not cells (`JUDGMENT_LAYER.md` §2f, hole-punch records).
 The refuted candidate carries are separately recorded `open` (§4.29), not
 withheld.

**Partial inverse (§10):** partial inverse requiring retained data —
extension by a qubit together with compatible stabilizer data; generally
many-to-one in the reverse direction (`TAXONOMY.md` §2.8).

**Provenance (§11):** the removed qubit's identity; every retired row's
identity, sector, and support — all of them are needed to invert, since the
update is not reversible from the child alone; the parent state identifier;
the retirement set is already recorded in `used`.

### `E-EXTEND` — Row-added extension (`extend`)

**Taxonomy ID:** `E-EXTEND`. **Layer:** conditional CSS transformation.
**Transition status:** `transition-defined` (§4.30).

**Input:** a well-formed presented CSS state; a new-qubit set $\Delta$ (typed:
disjoint from $Q$); an ordered list of typed additions
$(\tau_i,\mathrm{supp}(u_i))$ with
$\mathrm{supp}(u_i)\subseteq Q\cup\Delta$, no repeated entries, sorted,
nonempty.

**Output:** the state on $Q\cup\Delta$ with the existing display retained and
each addition appended as a displayed $\tau_i$-row, minted canonically in list
order.

**Applicability:** per addition, at its own step: same-sector independence
inside $\mathbb{F}_2^{Q\cup\Delta}$ (the $W22$ ambient reading) and
opposite-sector orthogonality; a failed check gives no derivation;
ill-typed data ($\Delta$ overlapping $Q$, untyped sector, malformed list) is
malformed.

**Structural effects:** $n'=n+|\Delta|$ and
$k'=k+|\Delta|-s_X-s_Z$, exactly (§4.30), where $s_\sigma$ counts sector-$\sigma$
additions.

**Distance judgment:** with $\Delta=\varnothing$, the §2a
`C-ADD-CHECK` monotonicity applies (both sectors carry their lower
endpoints; upper endpoints are rebuilt from child-valid witnesses); with
$\Delta\neq\varnothing$ no distance rule is derivable and none is admitted
(lower endpoints reset; child-valid witnesses only).

**Required support and interface data (§8), completed 2026-10-27 (Gate 0):**
reads: the new-qubit set $\Delta$ (typed, disjoint from $Q$) and the ordered
addition list — each entry's sector and support (term data); the per-step
independence and orthogonality premises are required for applicability.
Updates: $Q$ (grows by $\Delta$), display (additions appended, each minted
canonically in list order), `used` (grows by one identifier per entry);
existing rows unchanged. Certificates: none read; boundary labels,
interfaces, logical witnesses: `not yet defined`, not read; layout: ledger
data (§2d), not read — restricted to the child's labels by §2d.2.

**Complexity (§9), completed 2026-10-27** (parameters: $|\Delta|$, list
length $s$, $n$, `nnz`): applicability check — per addition, same-sector
non-membership by Gaussian elimination over $\mathbb F_2$ and opposite-sector
orthogonality by dot products, polynomial per step and polynomial in total;
typing checks ($\Delta \cap Q = \varnothing$, sorted, nonempty) linear;
output construction — linear in $\sum_i |\mathrm{supp}(u_i)|$ plus the mints;
CSS-validity check — these premises are it (§4.30's applicability argument);
logical-class transport — not computed ($s_X$, $s_Z$ are entry counts);
exact-distance computation — never performed by the calculus; certificate
validation — not applicable.

**Underivability, completed 2026-10-27:** *none.* The $\Delta\neq\varnothing$
refusal is the absence of an admitted formula, not a withheld claim: the
candidate carries are recorded `open` (inventory row, §4.28/§4.29 refutation
family), and no source states a distance formula for the namespace-growing
instance (§2f).

**Partial inverse (§10):** partial inverse requiring retained data — peeling,
and only with retained support and provenance data (`TAXONOMY.md` §2.9).

**Provenance (§11):** $\Delta$; the ordered addition list (sector and support
per entry); the minted identifiers in list order; the parent state identifier.
The list order is semantic (canonical mint follows it).

### `E-LOCAL-HADAMARD` — Sector exchange (`$T=Q$`) (`hadamard`)

**Taxonomy ID:** `E-LOCAL-HADAMARD`. **Layer:** conditional CSS transformation.
**Transition status:** `transition-defined` for the $T=Q$ instance (§4.27).

**Input:** a well-formed presented CSS state and a qubit subset $T\subseteq Q$
listed without repeated labels; the transition is applicable **at $T=Q$** (the
term declares the whole namespace) **and at $T=\varnothing$**, where the empty
conjugation is the identity (`TERM_LANGUAGE.md` §2).

**Output:** at $T=Q$, the code with every displayed row's sector swapped
($X\leftrightarrow Z$); supports, ids, used, $Q$ unchanged; no rows minted. At
$T=\varnothing$, the parent itself: the identity update.

**Applicability:** $T=Q$ or $T=\varnothing$; terms with
$\varnothing\subsetneq T\subsetneq Q$ are inapplicable (the
review-dispositioned split-subset mechanics are not admitted). Ill-typed $T$ is
malformed — a label outside $Q$, a non-qubit label, or a label listed twice (a
list with repeats does not name a subset).

**Structural and distance judgment:** $n'=n$, $k'=k$, $w'=w$;
$d_X'=d_Z$, $d_Z'=d_X$, $d'=d$, exactly (the full Pauli weight-preserving
conjugation is sector-blind on supports — §4.27). The ledger transport swaps
the sector intervals and revalidates each witness with its side swapped
(§2b). Not a presentation identity: the sector distances exchange, so the
output is a distinct CSS code.

**Not claimed:** the general split-subset instance (no cell, no rule);
per-qubit sector typing of future-$\Pi$ predicates.

**Required support and interface data (§8), completed 2026-10-27 (Gate 0):**
reads: $T$ (term data) — applicable only at $T=Q$. Updates: the sector
assignment of every displayed row ($X \leftrightarrow Z$); $Q$, supports,
identifiers, and `used` unchanged — no mint. Certificates: none read;
boundary labels, interfaces, logical witnesses (including per-qubit sector
typing): `not yet defined`, not read; layout: ledger data (§2d), not read —
$w'=w$ and the child $r$ recompute over the same supports in the swapped
display.

**Complexity (§9), completed 2026-10-27** (parameters: $n$, $m$, `nnz`):
applicability check — $T = Q$, a comparison of the declared subset with the
namespace; output construction — swap the sector label of each displayed
row, linear in the display; CSS-validity check — §4.27's sector-exchange
argument is the validity record (the global exchange preserves overlap
symmetry); logical-class transport — not computed (the sector exchange is
stated on distances and ranks, not on quotient data); exact-distance
computation — never performed by the calculus (the exact swap
$d_X' = d_Z$, $d_Z' = d_X$, $d' = d$ is a judgment, not a computation);
certificate validation — not applicable.

**Underivability, completed 2026-10-27.** Deliberately withheld by this
operation:

- **sector-swap claims below $T=Q$** — the split-subset instance
 ($\varnothing \subsetneq T \subsetneq Q$) and per-qubit sector-swap claims
 carry no cell and no rule: the term is inapplicable rather than
 underivable-by-omission, and the review-dispositioned mechanics were not
 admitted (§4.27; `TAXONOMY.md` §2.12, whose record notes the row-wise image
 would need an unspecified rebasing argument). Scope: `hadamard(T)` terms
 below $T=Q$.

**Partial inverse (§10):** exact inverse — itself: the $T=Q$ instance is an
involution, and since it mints nothing and renames nothing, applying
`hadamard(Q)` twice returns $\equiv$-equal labeled states
(`TAXONOMY.md` §2.12).

**Provenance (§11):** the operation ID and the fact of the sector exchange
($T=Q$); the pre-swap sector labels are recoverable by re-application (the
involution), so no state data is lost; the parent state identifier for audit.

### `E-GLUE` — Interface gluing (`glue(e₁, e₂; seams)`); `contract-stated`, conditional cell

**Taxonomy ID:** `E-GLUE`. **Layer:** conditional CSS transformation (Gate 6
CSS extension; admitted as a conditional cell 2026-10-23, Gate 6 unchecked).
**Syntax category / kind (§1):** `expression-constructor`, binary-only
($e ::= \mathrm{glue}(e_1, e_2; \vec u)$, [`TERM_LANGUAGE.md`](TERM_LANGUAGE.md)
§1–§2; dated maintainer decision 2026-11-18 — **no unary command
production**).
**Primitive or derived:** primitive binary expression-constructor; proved
equivalent on every pair of well-formed factors to the closed term
`⟨glueCommand seams, directSum (base A) (base B)⟩` (a direct sum followed by
one `C-ADD-CHECK` per seam check; `evalExpr_glue_iff_evalTerm_glueCommand` in
`lean/CodeCalculus/GlueExtraction.lean`).
**Contract status:** **`contract-stated`** (rung 5; dated maintainer decision
2026-11-18; remains a conditional cell, not `contract-proved` and
not `mechanized`).

**Input / output (§2):** two well-formed presented CSS states $C_A$, $C_B$ and
an ordered list $\vec u = [(\tau_1, \mathrm{supp}_1), \ldots, (\tau_m, \mathrm{supp}_m)]$
of typed seam checks ($\tau_i \in \{X, Z\}$, $\mathrm{supp}_i \subseteq Q_A \cup Q_B$
nonempty, repeat-free, sorted); output is the presented CSS state $C$ on
$Q_A \cup Q_B$ with factor rows followed by one canonically minted row per
seam check.

**Applicability & state update (§3):** $Q_A \cap Q_B = \varnothing$,
$\mathsf{used}_A \cap \mathsf{used}_B = \varnothing$, joint CSS orthogonality
(I1) and same-sector independence (I2) of factor rows plus seam checks
(equivalently step-by-step commutation and independence in list order,
`OPERATIONAL_SEMANTICS.md` §4.31), and canonical-mint capacity over
$\mathsf{used}_A \cup \mathsf{used}_B$ (70,000-name enumeration, H-4). State
update: $Q = Q_A \cup Q_B$, displayed rows concatenated with canonically
minted seam rows, $\mathsf{used} = \mathsf{used}_A \cup \mathsf{used}_B$
grown by the minted seam IDs; no factor row is removed or altered.
**Inapplicability:** namespace or `used` collision, seam support outside
$Q_A \cup Q_B$, failed commutation or independence, or identifier exhaustion
gives `no_derivation`; ill-typed seam data is `malformed`. **Deterministic:**
yes (canonical mint). **Well-formedness:** output satisfies I1 and I2
(joint CSS orthogonality and same-sector independence) `[proved]` (§4.31;
mechanized as `wf_glueState_of_eval_glueCommand`, `GlueExtraction.lean`,
which proves `EncodingWellFormed`, i.e. the I1/I2 list conditions; I3 and I4
are argued by hand in §4.31 and are not mechanized for `glueState`).

**Structural effects (§4):** $n' = n_A + n_B$ `[proved]` (`glueState_Q`);
$k' = k_A + k_B - m$ where $m = |\vec u|$ is the number of independent seam
checks `[proved]` (direct-sum additivity §4.4 plus one `C-ADD-CHECK` drop per
seam check §4.2; relative to $k(C_A \oplus C_B)$ mechanized as
`stateK_glueState_add_seams`); $w' = \max(w_A, w_B, \max_i |\mathrm{supp}_i|)$
`[proved]`; interaction radius $r' = \max(r_A, r_B, \max_i \mathrm{diam}(s_i))$
`[proved]` conditional on an honest merged layout (`JUDGMENT_LAYER.md` §2d.5);
Tanner connectivity recomputed over the glued display.

**Logical effects (§5):** no re-exposed class exists on any admitted glue:
$w_{\mathrm{re},\sigma}(C; C_A, C_B) = +\infty$ `[proved]` (§4.33 Claim 1,
`OBL-GLUE-RE-EXPOSURE`; mechanized as `reExposedVectors_eq_nil`,
`wRe?_eq_none`). Glued $\sigma$-logical classes satisfy
$L_\sigma(C) \cong K_\sigma / W_\sigma$ `[proved]` (§4.33 Claim 2; mechanized
on representatives in `ExactGluePairs.lean`, with Step 1 class invariance and
linearity of $\phi_t$ in `GlueExtraction.lean`; categorical quotient-group
packaging stays a hand derivation). A factor $\sigma$-logical survives iff it
commutes with every opposite-sector seam check and is not pulled into the
glued $\sigma$-span (`ExactGlueSurvival.lean`). Both future-$\Pi$ fields
($\mathsf{log}$ and $\mathsf{bd}$) and their `E-GLUE` transports are defined
outside the state (`STATE_MODEL.md` §1a, `WitnessFields.lean`).

**Distance and metric-preservation status (§6–§7):**
- *Unconditional lower bound:* $d_\sigma(C) \ge \min(d_\sigma(C_A), d_\sigma(C_B))$
 and $d(C) \ge \min(d(C_A), d(C_B))$ `[proved]` (§4.31 repair and §4.33 Claim 1;
 mechanized as `glue_exactDistance_ge_min`, `glue_exactDistance?_ge_min`,
 `glue_theorem4_lower_bound`, and `glue_expr_sound_exact_uncertified`).
- *Exact class-pair formula:* $d_\sigma(C) = \min\{\mu_A(\alpha) + \mu_B(\beta) : (\alpha,\beta) \in K_\sigma \setminus W_\sigma\}$
 `[proved]` (§4.33 Claim 2; mechanized as `glue_exactDistance?_eq_some_iff`,
 `glue_exactDistance?_eq_none_iff`), with Consequence (iii)
 $d_\sigma(C) \ge d_\sigma(C_A) + d_\sigma(C_B)$ when no pure pair survives
 `[proved]` (`glue_exactDistance?_ge_add_of_no_pure_survivor`).
- *Instance-wise equality:* $d_\sigma(C) = \min(d_\sigma(C_A), d_\sigma(C_B))$
 iff a minimum-weight factor class survives `[proved]` (§4.31, §4.33(ii);
 `glue_exactDistance?_eq_min_of_survivesA/B`, `glueExact_iff_carriesMin`).
- *Family-level §2e Z-equality:* $d_Z(Q) = \min(d_Z(C_A), d_Z(C_B))$ under
 an admissible seam certificate (`w(c_A) = w(c_B)`) — **`[conditional]`** on
 seam admissibility and survival of minimum-weight factor representatives
 (`AdmissibleSeam`). Theorem 4 supplies the unconditional lower half
 ($w_{\mathrm{re},Z}=+\infty$, hence
 $d_Z(Q)\ge \min(d_Z(C_A),d_Z(C_B))$) on every admitted glue without a
 certificate; the equality itself is conditional on `AdmissibleSeam` (the
 upper half). Mechanized from `AdmissibleSeam` through `glueField` and
 `glueLedger` (`admissibleSeam_exactDistance?_eq_min`,
 `admissible_family_glueField_exact`,
 `glue_expr_sound_exact_of_admissible`). The certificate (equal move words) is
 the evidence the consumer records for the `AdmissibleSeam` hypothesis.
 **Recorded substrate gap:** the
 geometric implication from planar move-word equality `w(c_A) = w(c_B)` to
`AdmissibleSeam` is not derivable from the CSS state model and stays outside
the Lean mechanization (`ADMISSIBLE_SEAM_FAMILY.md` §4).
- *Refuted / unadmitted claims:* the universal candidate equality
 $d_\sigma(C) = \min(d_\sigma(C_A), d_\sigma(C_B))$ is **`false`** (refuted
 §4.33; mechanized as `glue_universal_min_equality_false`), and
 the scalar relation $d = \min(d_A, d_B)$ is unadmitted
 (`DERIVED_RELATIONS.md` §2).

**Required support and interface data (§8), completed 2026-10-27 (Gate 0),
updated 2026-11-18:** reads the two factor states (disjoint $Q$
and `used`, §4.31), the typed seam list $\vec u$, and (at the judgment layer)
the §2e seam certificate — move words over $\{U,D,L,R\}^*$ with
$w(c_A) = w(c_B)$ — or §2e positive composition criteria (`JUDGMENT_LAYER.md`
§2e). Updates: $Q$ (union), display (seam checks minted canonically), `used`
(union plus seam mints). Logical witnesses and boundary labels are defined
in full as future-$\Pi$ fields outside the state (`STATE_MODEL.md` §1a; `WitnessFields.lean`), not read by state equality or
transitions. Layout is ledger data (§2d), not read — a merged honest layout
must be supplied by the consumer.

**Complexity (§9), completed 2026-10-27** (parameters: $n_A, n_B$, interface
size, move-word length): applicability check — namespace disjointness,
linear; seam-check construction linear in the interface size; commutation and
independence of the minted seam rows by Gaussian elimination over $\mathbb F_2$
(polynomial); output construction — the union plus the seam rows, linear;
CSS-validity check — §4.31's independence premises are it; logical-class
transport — not computed by the transition (the exact class-pair formula
ranges over $2^{k_A+k_B}$ pairs over NP-hard factor class dictionaries, §4.33(iv));
exact-distance computation — never performed by the calculus; **certificate
validation — applicable**: the seam certificate's move word equality is
checkable in time linear in the move word (consumer-side, §2e).

**Underivability, completed 2026-10-27, updated 2026-11-18:**
*none.* The universal candidate seam-distance claim is settled as `false`
(§4.33), the §2e family equality is `conditional` on
`AdmissibleSeam` / seam admissibility with its geometric move-word gap
recorded as a substrate boundary, and no `E-GLUE` property is withheld as
`unavailable`.

**Partial inverse (§10):** `open` as a rule — the operation-level inverse is
a split, only when a cut and its boundary data are retained
(`TAXONOMY.md` §2.10), and `E-SPLIT` carries no admission, so the calculus
contains no inverse transition today.

**Provenance (§11):** both parent state identifiers; the seam certificate
(move word and evidence reference) it consumed; the interface data read
(maps, identifications, $t$); the seam check supports; the minted
identifiers; the union layout if one was supplied.

**Evidence (§12):** [`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md)
§4.31 (transition, repair, extraction), §4.32 (`OBL-GATE6-CSS-EXTENSIONS`),
and §4.33 (`OBL-GLUE-RE-EXPOSURE`); [`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md)
§2b, §2d.5, §2e, §2f; [`STATE_MODEL.md`](STATE_MODEL.md) §1a;
`lean/CodeCalculus/ExactGlue.lean`, `ExactGluePairs.lean`,
`ExactGlueDistance.lean`, `ExactGlueSurvival.lean`, `LogicalWitness.lean`,
`WitnessFields.lean`, `AdmissibleSeamFamily.lean`, `Gate6Soundness.lean`,
`Gate6Exact.lean`, and `GlueExtraction.lean`;
`machine/test_glue_class_pairs.py`, `machine/test_priced_calculus.py`.

A card may record the release that introduced the operation as
`**Introduced in:**`, when later than `stdCSS-1`; see
[`spec/VERSIONING.md`](VERSIONING.md). Absence means `stdCSS-1`.

## Typed constructors admitted 2026-11-11 (`transition-defined`)

The 2026-11-10 disposition accepted nine constructors for
admission as typed constructors with explicit distance hypotheses. Four are
admitted here as expression constructors (`TERM_LANGUAGE.md` §1, §2), with
typed transitions at `OPERATIONAL_SEMANTICS.md` §2 and the well-formedness
and parameter derivations at §4.34: `L-HGP`, `L-LIFTED`, `L-GROUP-ALGEBRA`,
and `A-CONCAT`. Each is `transition-defined`; the rung is recorded in the
contract index below. None carries a distance rule: a constructed state's
ledger starts at $[0, +\infty)$ and moves only on supplied, sourced lower
bounds and validated witnesses (`JUDGMENT_LAYER.md` §2g), which is the
explicit-hypothesis discipline the disposition asked for. `L-BALANCED`,
`L-TANNER`, `L-TILE`, `A-PRODUCT`, and `A-DOUBLE` were admitted the same
day, once their typed inputs were defined as finite objects;
their fields are stated after the four, under *The other five*. The
contract fields common to the four are stated once, then the
per-constructor differences.

**Common fields.**

- *Typed input and output.* Finite constructive data in, one presented CSS
 state out, on the fresh namespace $\{0, \ldots, n-1\}$ with canonically
 minted identifiers (`STATE_MODEL.md` §4).
- *Applicability and state update.* Well-typed inputs always evaluate
 (`A-CONCAT` additionally needs $k_{\mathrm{in}} \ge 1$); the displayed rows
 are the retained display of the natural rows (§4.34).
- *Structural parameter effects.* $n$ exact per constructor; $w$ recomputed
 exactly over the constructed display; $r$ only when a layout is supplied
 and honest (`JUDGMENT_LAYER.md` §2d.3); Tanner components recomputed by
 finite traversal.
- *Logical-sector effects.* $k$ exact (closed form for `L-HGP`,
 `L-GROUP-ALGEBRA`, `A-CONCAT`; rank bookkeeping for `L-LIFTED`), evidence
 `proved` (§4.34).
- *Sector-specific and full distance effects.* Claim shape `unavailable`
 as an automatic rule, evidence `not-applicable`; the judgment inputs are
 supplied sector or full lower bounds with a source, or the conditional
 constructor cells of `JUDGMENT_LAYER.md` §2g.1 (§4.45) together with
 deterministic factor-to-child lifted and validated witnesses, never an
 unvalidated computed lower bound.
- *Metric-preservation status.* Not applicable: there is no parent state.
- *Required support and interface data.* The typed inputs of the §2 card.
- *Computational complexity.* Polynomial in the output size: the natural
 rows are written down and reduced by rank; `A-CONCAT` additionally
 enumerates the inner kernel for its level data (`tower_level_data`
 ceiling).
- *Partial inverse.* None.
- *Provenance retention.* The constructed state records no provenance of
 its inputs beyond the term that built it; `used` is the minted set.
- *Evidence and proof references.* §4.34, §4.44, §4.45;
 `lean/CodeCalculus/ConstructorOverlap.lean`,
 `lean/CodeCalculus/PricedInterval.lean`; `machine/test_constructors.py`.

**Per constructor.**

- `L-HGP`: inputs $H_1 \in \mathbb{F}_2^{m_1 \times n_1}$,
 $H_2 \in \mathbb{F}_2^{m_2 \times n_2}$; $n = n_1 n_2 + m_1 m_2$;
 $k = k_1 k_2 + k_1^{T} k_2^{T}$ with $k_i = n_i - \mathrm{rank}(H_i)$ and
 $k_i^{T} = m_i - \mathrm{rank}(H_i)$. The classical distances
 $(d_1, d_1^T, d_2, d_2^T)$ populate the conditional constructor cell
 $d_X \ge \min(d_2, d_1^T)$, $d_Z \ge \min(d_1, d_2^T)$,
 $d \ge \min(d_1, d_2, d_1^T, d_2^T)$ (`JUDGMENT_LAYER.md` §2g.1, Tillich and
 Zémor 2014, §4.45), with deterministic factor-to-child witness lifting
 (`lift_hgp_witnesses`).
- `L-LIFTED`: inputs a finite group $G$ (abelian by cyclic orders, or
 nonabelian by multiplication table or permutation generators; §4.44) and base
 matrices over $\mathbb{F}_2[G]$ using left regular representations $L(A[a, i])$
 and right regular representations $R(B[b, j])$; $n = |G| (n_A n_B + m_A m_B)$;
 $k$ by rank bookkeeping; the trivial group gives `L-HGP`, and abelian cyclic
 orders coincide with $R = L$.
- `L-GROUP-ALGEBRA`: inputs a finite group $G$ (abelian by cyclic orders, or
 nonabelian by multiplication table or permutation generators; §4.44) and two
 algebra elements $a, b \in \mathbb{F}_2[G]$; $n = 2|G|$;
 $H_X = [L(a) \mid R(b)]$, $H_Z = [R(b)^T \mid L(a)^T] = [R(b^*) \mid L(a^*)]$;
 $k = 2|G| - \mathrm{rank}[L(a) \mid R(b)] - \mathrm{rank}[L(b) \mid R(a)]$
 in general (reducing to $2(|G| - \mathrm{rank}[L(a) \mid L(b)])$ when $G$ is
 abelian); equals the $1 \times 1$ lifted product of $(a)$ and $(b^{*})$.
- `A-CONCAT`: inputs two well-formed CSS states and a block partition;
 $n = n_{\mathrm{in}} n_{\mathrm{out}}$; $k = k_O$; the tower price provider
 (`JUDGMENT_LAYER.md` §2a) supplies deletion/exposure prices and the
 conditional constructor cell
 $d_\sigma \ge \max(\lceil \ell_{O,\sigma}/k_{\mathrm{in}}\rceil, \ell_{\mathrm{block},\sigma}) \cdot \ell_{I,\sigma}$
 (`JUDGMENT_LAYER.md` §2g.1, §4.45) together with deterministic witness lifting
 (`lift_concat_witnesses`) seeds the constructed ledger. Non-CSS inner codes
 are not inputs.

**The other five (admitted 2026-11-11).** `A-PRODUCT`,
`A-DOUBLE`, `L-BALANCED`, `L-TANNER`, and `L-TILE` are `transition-defined`
expression constructors with cards at `OPERATIONAL_SEMANTICS.md` §2 and
derivations at §4.35 (generalized to nonabelian finite groups for `L-BALANCED`
at §4.44, with conditional distance cells and witness lifting for `A-PRODUCT`
and `A-DOUBLE` at §4.45). The common fields above hold for them with these
differences.

- *Applicability.* `A-PRODUCT` and `L-BALANCED` evaluate on every
 well-typed input. `A-DOUBLE`, `L-TANNER`, and `L-TILE` additionally
 require that the natural rows of the two sectors have pairwise even
 overlap, a decidable premise whose failure is a no-derivation.
- *Logical-sector effects.* $k$ exact, evidence `proved` (§4.35): the closed
 form $k_A k_B$ for `A-PRODUCT` and $2 k_C$ for `A-DOUBLE` with the empty
 wiring; rank bookkeeping otherwise.
- *Provenance retention.* `A-PRODUCT` and `A-DOUBLE` read the displays of
 their input states, and `A-DOUBLE`'s wiring is keyed by displayed
 identifiers. The output records none of it.
- *Evidence and proof references.* §4.35, §4.44, §4.45;
 `lean/CodeCalculus/BalancedOverlap.lean`,
 `lean/CodeCalculus/PricedInterval.lean`; `machine/test_constructors.py`.

Per constructor:

- `A-PRODUCT`: inputs two well-formed CSS states; the product structure is
 the CSS tensor product only; $n = m_Z^A m_X^B + n_A n_B + m_X^A m_Z^B$;
 $k = k_A k_B$. The output depends on the two displays, not only on the
 two codes, up to an invertible linear map on two of its three qubit
 blocks, so its conditional distance cell
 (`JUDGMENT_LAYER.md` §2g.1, §4.45) requires an explicit display-specific
 Audoux–Couvreur certificate (`display_certificate`) supplying direct lower
 bounds $d_\sigma \ge \ell_\sigma$ (or multiplicative bounds
 $d_\sigma \ge \underline d_{A,\sigma}\underline d_{B,\sigma}$ when certified
 for the chosen displays; multiplicative scaling is not automatic from factor
 distances alone), while deterministic middle-block witness lifting
 (`lift_product_witnesses`) earns upper bounds directly on the constructed
 display.
- `A-DOUBLE`: inputs a well-formed CSS state, a wiring map on its displayed
 incidences, and an optional sector-duality flag; $n = 2 n_C$. For the empty
 wiring $w = \varnothing$, the conditional constructor cell
 (`JUDGMENT_LAYER.md` §2g.1, §4.45) records $d_\sigma \ge \underline d_{C,\sigma}$
 (or $d_\sigma \ge \min(\underline d_{C,X}, \underline d_{C,Z})$ under
 `conjugate`), and `lift_double_witnesses` lifts parent witnesses to both
 sheets (validating against the twisted rows when $w \neq \varnothing$). The
 factorization question of `TAXONOMY.md` §2.16 stays open.
- `L-BALANCED`: inputs a finite group $G$ (abelian by cyclic orders, or
 nonabelian by multiplication table or permutation generators; §4.44), two
 binary matrices $H_1, H_2$, a right action $\alpha_1$ on $H_1$, and a left
 action $\alpha_2$ on $H_2$ under which the matrices are equivariant; $n$ is
 the number of orbits under $(x, y) \mapsto (\alpha_1(g)(x), \alpha_2(g)^{-1}(y))$;
 the trivial group gives `L-HGP` row for row.
- `L-TANNER`: inputs a qubit count, one local check matrix per vertex
 class, and one embedding per vertex. Expansion and distance hypotheses
 are not inputs.
- `L-TILE`: inputs a tile set, placements on sites, site identifications,
 and removed checks; $n$ is the number of site classes.

**`L-NESTED-CSS` (admitted 2026-11-13).** `L-NESTED-CSS` is a
`transition-defined` expression constructor with a card at
`OPERATIONAL_SEMANTICS.md` §2 and derivations at §4.36 and §4.45. The common
fields above hold for it with these differences.

- *Typed input.* Two binary parity-check matrices with equally many
 columns. Codes given by generator matrices or as subspaces are not
 inputs.
- *Applicability.* Every row of the one matrix has even overlap with every
 row of the other, a decidable premise whose failure is a no-derivation.
 It is the nesting of the two classical codes.
- *Logical-sector effects.* $n$ is the number of columns and
 $k = n - \mathrm{rank}(H_X) - \mathrm{rank}(H_Z)$, exact, evidence
 `proved` (§4.36).
- *Distance.* Claim shape `unavailable` as an automatic rule; the conditional
 constructor cell (`JUDGMENT_LAYER.md` §2g.1, §4.45) accepts supplied classical
 lower bounds $d(\ker H_Z)$ and $d(\ker H_X)$ (or coset distances) to license
 $d_X \ge d(\ker H_Z)$ and $d_Z \ge d(\ker H_X)$ with `status: "conditional"`,
 and `lift_nested_witnesses` deterministically lifts nontrivial codewords in
 $\ker H_Z \setminus \mathrm{rowspan}(H_X)$ and
 $\ker H_X \setminus \mathrm{rowspan}(H_Z)$ as validated upper-bound witnesses.
- *Evidence and proof references.* §4.36, §4.45;
 `lean/CodeCalculus/PricedInterval.lean`; `machine/test_constructors.py`.

**`L-EMPTY`, `L-FREE`, `A-PULLBACK`, and `A-PUSHOUT` (admitted 2026-11-19).**
All four are `transition-defined` expression constructors with cards at
`OPERATIONAL_SEMANTICS.md` §2 and derivations at §4.43. None carries a
distance rule in `JUDGMENT_LAYER.md` §2g: constructed ledgers start at
$[0, +\infty)$ via `DistanceLedger.for_constructed`.

- `L-EMPTY`: 0-ary base constructor (`() -> CSSCode`); $Q = \varnothing$,
 empty display, empty `used`; $n = 0$, $k = 0$, $w = 0$, $\kappa = 0$,
 $r = 0$; semantic $d_X = d_Z = d = +\infty$.
- `L-FREE`: qubit-set base constructor (`(Q : QubitSet) -> CSSCode`);
 empty display, empty `used`; $n = |Q|$, $k = |Q|$, $w = 0$,
 $\kappa = |Q|$, $r = 0$; semantic $d_X = d_Z = d = 1$ for $Q \neq \varnothing$
 and $+\infty$ for $Q = \varnothing$ (`free(∅) ≡ empty`).
- `A-PULLBACK`: fiber product of $C_1, C_2$ over $I$ along CSS code morphisms
 $\phi_1, \phi_2$; $n = |Q_1 \times_{Q_I} Q_2|$, $k$ by rank bookkeeping;
 morphism preservation and pairwise even overlap of the pulled-back rows
 are decidable applicability premises; naive factor-minimum bound is `false`.
- `A-PUSHOUT`: amalgamated sum of $C_1, C_2$ along $S$ via CSS code morphisms
 $\psi_1, \psi_2$; $n = |Q_1 \sqcup_{Q_S} Q_2|$, $k$ by rank bookkeeping;
 morphism preservation and pairwise even overlap of the pushed-forward rows
 are decidable applicability premises; general pushouts with $S \neq 0$
 can drop distance.

**`L-PAIR-PARTITION` and `PP-SCALE` (admitted/promoted 2026-11-22).** Both are
`transition-defined` expression constructors with cards at
`OPERATIONAL_SEMANTICS.md` §2 and derivations at §4.46–§4.47 (`OBL-PP-SCALE`
and `OBL-WELL-FORMEDNESS-PRESERVATION`).

- `L-PAIR-PARTITION` (`pair_partition(p; B_X, B_Z)`): constructs a CSS code on
 $n = L \cdot p$ qubits from paired affine/circulant permutation block matrices
 $B_X, B_Z$ over $\mathbb{Z}_p$ ($p \ge 1$, $L \ge 2$ even); structural rows
 $n = L \cdot p$ exact, $k = L \cdot p - \mathrm{rank}(H_X) - \mathrm{rank}(H_Z)$
 exact by rank bookkeeping (`proved`, §4.46), $w, \kappa, r$ recomputed over
 the retained display; WF rows: output well-formed under unit slopes and
 paired relative-affine orthogonality ($H_X H_Z^T = 0 \pmod 2$); distance
 rows: no automatic cell, ledger starts at $[0, +\infty)$ (the CPM-PP factorial
 ceiling $d \le (J+1)!$ of Okada–Kasai Thm 3 is an external source a consumer
 may cite, while APM-PP escapes that ceiling).
- `PP-SCALE` (`pp_scale(e; P)`): scales a PP-presented CSS state $C_0$ to
 target lift size $P \ge 2$ via the Smith-normal-form slope/shift
 parametrization (Kasai 2026, §2.1); structural rows: $n' = L \cdot P$ exact,
 $k' = L \cdot P - \mathrm{rank}(H_X') - \mathrm{rank}(H_Z')$ exact by rank
 bookkeeping, $w' = L$ carries (each natural row has one 1 in each of the $L$ block columns), $r'$ and Tanner
 connectivity recomputed, fresh namespace $Q' = \{0, \dots, L \cdot P - 1\}$
 with row identifiers canonically minted disjoint from $\mathsf{used}_0$; WF
 rows: output well-formed under applicability premise (vi) (pairwise even
 overlap of the generated natural rows) together with `wf_constructedStateFrom`;
 the claim that the PP conditions at $P_0$ give orthogonality at every
 $P \ge 2$ is cited from Kasai 2026 \S2.1 and is not derived here; $k' > 0$
 checked separately (no derivation when $k' \le 0$); distance rows: no
 automatic rule, $d, d_X, d_Z$ are `not yet defined` unless a verified interval
 $[d_{\mathrm{lo}}, d_{\mathrm{hi}}]$ is supplied, in which case the conditional
 priced cell (`JUDGMENT_LAYER.md` §2g, §2l) applies and is marked `conditional`,
 not `proved`; the family-level structural upper bound $B$ (§2l) is marked
 `conjectural`.
- Evidence and proof references: §4.46, §4.47; `OBL-WELL-FORMEDNESS-PRESERVATION`,
 `OBL-PP-SCALE`; `machine/test_constructors.py`, `lean/CodeCalculus/ConstructorAssembly.lean`,

 `lean/CodeCalculus/ConstructorInstances.lean`.

## 2. Typed input and output

Specify the mathematical objects consumed and produced:

```md
**Input:** Presented CSS-code state `(C, Π)` and a displayed independent
stabilizer row `r`.

**Output:** Presented CSS-code state `(C', Π')`.
```

For lower-level constructors, the input must name the actual ingredient types, such as:

- classical code;
- parity-check matrix;
- chain complex;
- group algebra and representation;
- graph and local code;
- tile and cellulation data.

An opaque constructor name is not a sufficient input type.

## 3. Applicability and state update

Record the exact premises:

```md
**Applicability:**

- `DisplayedGenerator(r, pres)`;
- `Independent(r; X, Z)`;
- selected stabilizer type is known.

**State update:**

- remove `r` from the selected stabilizer presentation and row space;
- retain the qubit set;
- update `Π` and invalidate certificates that mention the removed row.
```

The contract must state:

- all applicability predicates;
- the exact update to $Q$, $X$, $Z$, and `pres`;
- the exact update to $\Pi$;
- behavior when the operation is inapplicable;
- whether the result is deterministic.

## 4. Structural parameter effects

Record exact effects on physical and stabilizer dimensions:

$$
\Delta n = n(C')-n(C),
$$

$$
\Delta k = k(C')-k(C),
$$

$$
\Delta \dim X = \dim X' - \dim X,
\qquad
\Delta \dim Z = \dim Z' - \dim Z.
$$

Each equation or inequality receives an evidence status and hypotheses.

The contract should include `n` and `k` even when they are unchanged. “No change” is a semantic result, not an omitted field.

## 5. Logical-sector effects

Record how logical classes change in each sector:

```md
**Logical effects:**

- transport map for `L_X(C) → L_X(C')`, if defined;
- transport map for `L_Z(C) → L_Z(C')`, if defined;
- newly admitted classes;
- removed classes;
- surviving classes;
- kernel/cokernel or quotient description, when applicable;
- representative or witness transport conditions.
```

A count of logical qubits is not enough. When possible, the contract should describe maps between

$$
\mathcal{L}_X(C)=Z^\perp/X,
\qquad
\mathcal{L}_Z(C)=X^\perp/Z.
$$

For operations that enlarge a logical space, identify the new quotient classes or representatives. For operations that restrict a logical space, identify the removed classes or the kernel of the transport map.

## 6. Sector-specific and full distance effects

Record $d_X$, $d_Z$, and the full code distance separately:

$$
 d(C)=\min(d_X(C),d_Z(C)),
$$

under the proposal's empty-sector convention.

| Quantity | Claim | Hypotheses | Evidence status |
| --- | --- | --- | --- |
| $d_X$ | exact value, equality, or inequality | ... | exact / bound / conditional / ... |
| $d_Z$ | exact value, equality, or inequality | ... | exact / bound / conditional / ... |
| $d$ | full-distance effect | ... | exact / bound / conditional / ... |

The contract must distinguish at least:

- exact preservation;
- nondecrease or nonincrease;
- lower or upper bounds;
- conditional preservation;
- no available result.

## 7. Metric-preservation status

“Metric-preserving” is not a single global Boolean. Record the status per sector and for the full distance:

| Metric property | Status |
| --- | --- |
| Preserves $d_X$ exactly | yes / no / conditional / open |
| Preserves $d_Z$ exactly | yes / no / conditional / open |
| Preserves full $d$ exactly | yes / no / conditional / open |
| $d_X$ monotonicity | nondecreasing / nonincreasing / neither / open |
| $d_Z$ monotonicity | nondecreasing / nonincreasing / neither / open |
| Full-distance monotonicity | nondecreasing / nonincreasing / neither / open |

The hypotheses for a conditional status must be listed in the contract rather than hidden in prose.

## 8. Required support and interface data

List every context field read or updated by the operation:

- displayed generator identity;
- row-space or rebasing witness;
- qubit/check incidence and support ownership;
- boundary labels;
- interface maps and qubit identifications;
- algebra actions and representation conventions;
- logical witnesses;
- validated certificates;
- construction inputs and parameters.

For each field, state whether it is:

- required for applicability;
- required only for a property judgment;
- updated by the operation;
- invalidated by the operation; or
- required for a partial inverse.

## 9. Computational complexity

Complexity must be stated relative to an input representation. Record separately:

| Complexity field | Required information |
| --- | --- |
| Applicability check | Cost of deciding whether the operation can apply |
| Output construction | Cost of producing the new presentation and context |
| CSS-validity check | Cost of checking commutation and independence |
| Logical-class transport | Cost of computing or validating the transport data |
| Exact-distance computation | Cost when exact distance is claimed or required |
| Certificate validation | Cost of checking supplied witnesses or certificates |
| **Underivability** | **Required field.** What this operation **deliberately withholds**, as a named list with the reason and the scope it applies in; or the explicit word *none*. This is the field that makes "auditable by card review" true rather than aspirational — an unavailability commitment is a property of the recorded table, never a decision procedure about derivations. An explicit *none* is a **positive assertion**, not an omission. |

The complexity parameters should be named, for example:

- number of physical qubits $n$;
- number of stabilizer rows;
- number of nonzero matrix entries;
- interface size;
- graph size;
- group order;
- algebraic representation size.

The cost of applying a sparse matrix operation must not be confused with the cost of computing exact distance, which may be substantially harder.

## 10. Partial inverse

Record whether the operation has an inverse-direction operation:

```md
**Partial inverse:** `C-ADD-CHECK`

**Inverse conditions:** The deleted row, or an equivalent valid row, must be
retained in provenance and must satisfy the addition premises.

**Information lost:** The original presentation choice and any invalidated
certificates are not recoverable without retained provenance.

**Multiplicity:** Multiple parent states may produce the same child state.
```

Use one of:

- exact inverse;
- partial inverse requiring retained data;
- non-unique inverse;
- no meaningful inverse;
- open.

## 11. Provenance retention

The contract must state what must survive for later composition, audit, or inversion:

- parent state identifier;
- operation ID and contract version;
- selected rows, qubits, supports, and interfaces;
- presentation changes performed before the operation;
- lower-level constructor inputs and parameters;
- theorem and certificate references;
- logical witnesses;
- computational artifact and implementation version;
- data required by any partial inverse.

Provenance is part of the semantic context when a later rule depends on it. It is not merely an annotation for display.

## 12. Evidence and proof references

Each nontrivial claim should point to its evidence:

```md
**Evidence:**

- definition, lemma, theorem, or metatheorem identifier;
- hypotheses used;
- proof or mechanization location;
- counterexamples and edge cases;
- computational experiment, if empirical;
- implementation or certificate version.
```

Empirical evidence may falsify a conjecture or validate an implementation, but it does not replace a soundness proof for a calculus judgment.

---

# Admission rule

An operation may be admitted as a sound formal-calculus transition only when:

1. its taxonomy ID, operation kind, and layer are fixed;
2. its input and output types are defined;
3. its applicability, inapplicability behavior, and state/context update are specified;
4. output well-formedness is proved;
5. structural effects on $n$, $k$, and stabilizer ranks are recorded;
6. logical-sector and distance fields are recorded with separate claim shapes and evidence statuses;
7. required support, interface, complexity, inverse, and provenance data are listed.

A contract may be `contract-stated` with a property whose evidence status is `open` or whose claim shape is `unavailable`. That does not weaken the requirement that the transition itself be `state-sound` before it is admitted as a sound calculus rule. An operation with only an assigned proof obligation remains a candidate, not an admitted rule. The conditional-cell scope includes `E-GRAFT` and its cells in the current design and executable prototype, but does not promote it to `state-sound` or claim it as a proved rule.

The admission boundary therefore distinguishes:

- a syntax candidate;
- a defined transition or constructor;
- a state-sound transition;
- a proved property judgment;
- an unavailable property;
- an empirical observation; and
- a conjecture.

---

# Property inventory

 deliverable: the table of included, deferred, and unavailable properties for
the historical MVP operation set, extended with 's `stdCSS-2` priced
construction claims explicitly marked below. Per-primitive judgment detail lives in
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md); the property names below are
claim shapes and predicates from the proposal §5–§6 assertion language.

| Property | Claim shape | Operations | Status | Evidence status | Source |
| --- | --- | --- | --- | --- | --- |
| output well-formedness | preservation | all MVP primitives | included | `proved` (per-primitive obligations, 2026-10-20) | `OBL-WELL-FORMEDNESS-PRESERVATION` |
| $n$ effects | equality | all MVP primitives | included | `proved` (dimension counts) | proposal §7; derivation `spec/OPERATIONAL_SEMANTICS.md §4` |
| $k$ effects | equality | `C-DELETE-CHECK`, `C-ADD-CHECK`, `C-DIRECT-SUM` | included | `proved` (dimension counts) | proposal §7.1–7.3; derivation `spec/OPERATIONAL_SEMANTICS.md §4`–§4.2, §4.4 |
| $w$ effects (max stabilizer weight) | equality | `C-SKIP`, `C-DELETE-CHECK`, `C-ADD-CHECK`, `C-DIRECT-SUM`, `C-SEQUENCE`, `E-GRAFT`; and the 2026-10-23 conditional cells: `P-REBASE`/`E-PEEL`/`E-PUNCTURE`/`E-EXTEND`/`E-LOCAL-HADAMARD` ($T=Q$) recomputed exactly over the child display (`E-LOCAL-HADAMARD` additionally carries $w'=w$) | included | `proved` (trivial max over displayed rows) | disposition 2026-10-20; derivation `spec/OPERATIONAL_SEMANTICS.md §4` (well-formedness preservation); Gate 6 recomputations §4.26–§4.30 |
| $r$ effects (interaction radius, relative to a supplied layout) | equality and upper-bound | `C-SKIP`, `C-DELETE-CHECK`, `C-ADD-CHECK`, `C-DIRECT-SUM`, `C-SEQUENCE`, `E-GRAFT`, and since 2026-11-10 `E-PEEL`, `E-PUNCTURE`, `E-LOCAL-HADAMARD` ($T=Q$), `P-REBASE`, `E-EXTEND`, `E-GLUE`: one layout cell per transition, recomputed exactly over the child display and its transported layout (`JUDGMENT_LAYER.md` §2d.5), with the layout restricted to the child's qubit labels, merged blockwise, or supplied, as the cell states | included | `proved` (trivial max over displayed rows in the layout metric; the graft's factor-of-two bound by the triangle inequality; the extension cells by restriction and composition, §4.21 addendum of 2026-11-10) | disposition 2026-10-22; derivation `spec/OPERATIONAL_SEMANTICS.md §4.21` (interaction-radius transport); judgment cells in `JUDGMENT_LAYER.md` §2 and §2d.5; transcription `machine/semantics.json` (`layout_cells`) |
| Tanner-connectivity effects (components of the combined X+Z Tanner graph of the displayed rows) | equality and direction | `C-SKIP`, `C-DELETE-CHECK`, `C-ADD-CHECK`, `C-DIRECT-SUM`, `C-SEQUENCE`, `E-GRAFT`; Gate 6 conditional cells recomputed exactly by finite traversal over the child display | included | `proved` (finite traversal; the directions per primitive by the node-and-edge description) | disposition 2026-10-23; derivation `spec/OPERATIONAL_SEMANTICS.md §4.22`; judgment cells in `JUDGMENT_LAYER.md` §2; the strictly stronger stabilizer-group predicate is computed but not carried |
| direct-sum distance law ($d_X$, $d_Z$ equal the minimum of the summands) | equality | `C-DIRECT-SUM` | included | `proved` (derivation recorded) | proposal §7.1; derivation `spec/OPERATIONAL_SEMANTICS.md §4`; **2026-10-08 (fourth round):** usable *in a derivation* only since L3 gained `MIN-ORDER` — before that it was an included entry no rule could apply, since nothing related a `min` term to its arguments (disposition §3.4.1) |
| distance monotonicity under addition | lower-bound | `C-ADD-CHECK` | included | `proved` (ordinary CSS stabilizer codes only, not gauge constraints; derivation recorded) | proposal §7.3; derivation `spec/OPERATIONAL_SEMANTICS.md §4` |
| strict improvement of distance (**Introduced in:** `stdCSS-2`) | monotonicity | `C-ADD-CHECK` | conditional (requires exact old $d$ and exhaustive minimum-weight-class enumeration) | `conditional` | Proposition 18.3, *code-deformation* §5.2; derivation reproduced at `spec/OPERATIONAL_SEMANTICS.md` §4.19 |
| heuristic search outcome (a bounded or sampled survivor or witness search; **admitted 2026-11-11**, as a dated note on the current ordinal) | `probabilistic` | consumer searches: the enumeration fallback of `strict_improvement_feasible` and the planner's bounded sector search | included as a record about the search only; licenses no endpoint and never upgrades `unavailable` | `empirical` (`proved` when a union bound is derived) | *Admission (2026-11-11)* above; `machine/priced_calculus.py` `heuristic_outcome` |
| per-state distance lower bound or equality through a checked certificate (**Introduced in:** `stdCSS-3` candidate; admitted to it 2026-11-11) | `lower-bound` or `equality`, on a per-state atomic judgment | none: keyed to a state, a property, and a sector (`OPERATIONAL_SEMANTICS.md` §4.24), never to an operation | admitted to the candidate; carried by the per-state theorems of `lean/CodeCalculus/CertificateInstances.lean` since the mechanized checker landed (2026-11-11), by no consumer field, and by nothing under `stdCSS-2`; ships with the candidate row | `certificate-checked` | *Reserved future status*, *Admission (2026-11-11)*, and *Mechanized checker (2026-11-11)* above; `lean/CodeCalculus/CertificateChecker.lean` is the checker, `machine/certificates.py` the prototype |
| sector-aware gauging of distance (**Introduced in:** `stdCSS-2`) | lower-bound | `C-ADD-CHECK` | conditional (requires supplied sector minima $w_X,w_Z$ over the surviving logical classes and an evidence reference) | `conditional` | Lemma 18.5, *code-deformation* §5.2; judgment cell in `spec/JUDGMENT_LAYER.md` §2a |
| direct-sum extinction of distance (**Introduced in:** `stdCSS-2`) | equality | `C-ADD-CHECK` | conditional (requires exact old $d$, a trusted factor distance $d_B>d_A$, and the computed structural side) | `conditional` | Proposition 18.6 + Corollary 18.7, *code-deformation* §5.2; judgment cell in `spec/JUDGMENT_LAYER.md` §2a |
| newly admitted logical classes in both sectors and their quotient-level transport | definition | `C-DELETE-CHECK` | included | `proved` (hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.39, 2026-11-18; Gate 2 remains unchecked and Lean builds no logical quotient) | proposal §7.2; derivation `spec/OPERATIONAL_SEMANTICS.md` §4.39 (also covers `C-DIRECT-SUM` and `C-ADD-CHECK` quotient exact sequences) |
| exact unpriced post-deletion values ($d$, $d_X$, $d_Z$) | `unavailable` | `C-DELETE-CHECK` | unavailable under the current inputs | `not-applicable` | proposal §7.2 (scoped by [`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2a); `unavailable` follows the non-goals list |
| full-distance and sector-wise post-deletion price (**Introduced in:** `stdCSS-2` (full-distance half); sector split) | equality | `C-DELETE-CHECK` | conditional on consumer-supplied $w_{\rm del}$ (deleted sector) and $w_{\rm exp}$ (opposite sector) minima; sector-wise $d'_\tau=\min(d_\tau,w_{\mathrm{del}})$, $d'_{\bar\tau}=\min(d_{\bar\tau},w_{\mathrm{exp}})$ | `conditional` | Theorem 12.1 (manuscript Theorem 7), *code-deformation* §4.1; sector split derived at `spec/OPERATIONAL_SEMANTICS.md` §4.19; judgment cell in `JUDGMENT_LAYER.md` §2a |
| distance non-increase under deletion ($d_X(C')\leq d_X(C)$, $d_Z(C')\leq d_Z(C)$, and $d(C')\leq d(C)$) | `upper-bound` | `C-DELETE-CHECK` | included | `proved` (hand derivations recorded at [`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4 and its full-distance consequence, 2026-09-26 and 2026-10-05; mechanized for the exact distance in `ExactDistance.lean`) | proposal §7.2; **corrected 2026-10-08** — the source column read "§6 monotonicity" (disposition §3.4.1). **Revised 2026-10-09:** the bound *is* a consequence of the two sector bounds — $d$ is the derived term $\min(d_X,d_Z)$, which unfolds, so `MIN-ORDER` plus `TRANSITIVITY` derive $d(C')\leq d(C)$ — and both 2026-10-08 reasons ("not a consequence of the two sector bounds"; "needs $d=\min$ as a premise, which instantiation cannot supply") are withdrawn as false (disposition §3.4.1, round 5). The row and §4.5's derivation stay as a redundant registry entry |
| distance identity under skip ($d_X(C')=d_X(C)$, $d_Z(C')=d_Z(C)$) | `equality` | `C-SKIP` | included | `proved` (definitional; asserted by a schema, not unfolded from the pinned update) | [`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) `C-SKIP` card; **added 2026-10-08**, review, so that a chain through `skip` is derivable under L3 `TRANSITIVITY` |
| exact post-addition distance values | equality | `C-ADD-CHECK` | deferred (bounds only) | `open` | proposal §7.3; the split from post-deletion (`unavailable`) follows the non-goals list: post-deletion is a stated non-goal, post-addition is not |
| exact post-graft full distance (**Introduced in:** `stdCSS-2`) | equality | `E-GRAFT` | conditional on exposure minimum and coverage guard | `open` (refuted as transcribed for the transition in this repository; the scalar form $d'=\min(d,w_{\mathrm{expose},\bar\tau})$ is false for this transition — only the sector-wise form survives; see `OPERATIONAL_SEMANTICS.md` §4.13, 2026-10-21) | Theorem 28.3, *code-deformation* §9.5; **refuted** for this transition at `OPERATIONAL_SEMANTICS.md` §4.19 (Theorem 28.3) and §4.20 |
| unpriced graft full-distance non-increase (**Introduced in:** `stdCSS-2`) | upper-bound | `E-GRAFT` | conditional on coverage guard | `open` (refuted as transcribed for the transition in this repository; see `OPERATIONAL_SEMANTICS.md` §4.13, 2026-10-21) | Theorem 28.3, *code-deformation* §9.5; **refuted** for this transition at `OPERATIONAL_SEMANTICS.md` §4.19 (Theorem 28.3) and §4.20 |
| interval endpoint transport and target decisions (**Introduced in:** `stdCSS-2`) | preservation | in-scope consumer transitions | included in executable consumer; soundness proved under the corrected E-GRAFT rules | `proved` (hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.13, 2026-10-21) | `OBL-PRICED-INTERVAL-SOUNDNESS` |
| Gate 6 extension structural effects (**Introduced in:** `stdCSS-2`, 2026-10-23) | equality | `P-REBASE` ($n,k,d_X,d_Z,d$ span-exact), `E-PEEL` ($n$ exact; $k'=k$ exactly), `E-PUNCTURE` ($n$ exact; $k'=k-1+t_X+t_Z$), `E-EXTEND` ($n'=n+|\Delta|$, $k'=k+|\Delta|-s_X-s_Z$), `E-LOCAL-HADAMARD` ($T=Q$: $n,k,w$ exact; $d_X'=d_Z$, $d_Z'=d_X$, $d'=d$) | included | `proved` (hand derivations `spec/OPERATIONAL_SEMANTICS.md` §4.26–§4.30, 2026-10-23) | the typed transitions and their §2 blocks; evidence, not machine-checked |
| post-peel/puncture/extend distance rules for the touched sectors | `equality` | `E-PEEL`, `E-PUNCTURE`, `E-EXTEND` ($\Delta\neq\varnothing$) | refuted for the candidate exact carry (§4.28/§4.29). For `E-PEEL` the two sector relations are exact with a price, $d_\tau'=w_{\mathrm{avoid},\tau}(q)$ and $d_{\bar\tau}'=\min(d_{\bar\tau},w_{\mathrm{expose},\bar\tau}(q))$ (§4.28, 2026-11-10), so unpriced $d_\tau'\ge d_\tau$ and $d_{\bar\tau}-1\le d_{\bar\tau}'\le d_{\bar\tau}$ carry and the two price cells are admitted (after the earlier carries); for `E-PUNCTURE` the reduction to deletions plus a free-qubit removal is recorded (§4.29) and no unpriced endpoint carries in either direction, the hole price blocked on D2; for `E-EXTEND` ($\Delta\neq\varnothing$) no bound is licensed (§4.30) | `E-PEEL`: `conditional` (price cells) over `proved` carries; `E-PUNCTURE`, `E-EXTEND`: `open` (refuted as transcribed; see `OPERATIONAL_SEMANTICS.md` §4.29/§4.30) | `JUDGMENT_LAYER.md` §2a, §2f |
| structural-fact persistence through sequences | preservation | `C-SEQUENCE` | included | `proved` (hand derivations `spec/OPERATIONAL_SEMANTICS.md` §4.7, §4.11, §4.15, §4.21, §4.22, §4.37; reconciled 2026-11-18; mixed opposite-polarity exact-quantity distance chains remain `open`, and claims referencing deleted generators remain `unavailable`) | proposal §7.4; `OBL-JUDGMENT-TRANSPORT` (§4.11), `OBL-WELL-FORMEDNESS-PRESERVATION` (§4.7), `OBL-ORDER-INDEPENDENT-DELETION` (§4.15), `OBL-LOCALITY-TRANSPORT` (§4.21), `OBL-TANNER-CONNECTIVITY-TRANSPORT` (§4.22), §4.37 |
| transport of claims referencing deleted generators | `unavailable` | `C-SEQUENCE` | unavailable | `not-applicable` | proposal §4 |
| certificate, interface, metric, and logical-witness judgments | (various) | all | partly defined: the **interaction-radius** metric judgment is included; certificate, interface, and logical-witness judgments remain not-yet-defined (future $\Pi$ data) | `not-applicable` | [`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2 (property inventory); [`CLAIMS.md`](CLAIMS.md) property inventory (certificate, interface, logical-witness rows, not-yet-defined) |
| support-sensitive predicates under rebasing | (various) | `P-REBASE` | not-yet-defined | `not-applicable` | `spec/TAXONOMY.md` §1.4 |
| circuit, DEM, and realization predicates | (various) | — | not-yet-defined (separate realization layer) | `not-applicable` | proposal §8 |
| codespace preservation of a commuting Pauli-rotation gate ($\mathsf{preserves}_U$ on a CSS display; **Introduced in:** `stdCSS-3` / `v0.3.0`) | `preservation` | `C-SKIP`, `C-ADD-CHECK` (commuting generators at any angle; all angles $\pi/4$ iff $V_s \in \mathcal{S}(C')$), `C-DIRECT-SUM` (supported on one summand), `C-SEQUENCE` (`C-DELETE-CHECK`: does not carry, `false`) | included for CSS displays (no operation identifier minted); addressability, logical action, and the non-$\pi/4$ anticommuting `C-ADD-CHECK` branch remain `not yet defined` (logical-witness frame) | `proved` (hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.37, 2026-11-18) | arXiv 2610.17612 Theorem 1 & Corollary 3; derived for CSS displays at `spec/OPERATIONAL_SEMANTICS.md` §4.37 and `GATE_REALIZATION_ROWS.md` §2; carry cells in `spec/JUDGMENT_LAYER.md` §2 and §2h |
| equal-syndrome generator weight floor ($\omega(C) \ge \lceil d(C)/2 \rceil$; **Introduced in:** `stdCSS-3` / `v0.3.0`) | `lower-bound` (`weakening` carry shape: $\omega \ge \lceil L_d/2 \rceil$ re-read from the full-distance lower endpoint $L_d$ at each state, never substituted from the parent) | `C-SKIP`, `C-ADD-CHECK`, `C-DELETE-CHECK`, `C-DIRECT-SUM`, `C-SEQUENCE` | included | `proved` (hand derivation `spec/OPERATIONAL_SEMANTICS.md` §4.37, 2026-11-18) | arXiv 2610.17612 Corollary 2; derived for CSS displays at `spec/OPERATIONAL_SEMANTICS.md` §4.37 and `GATE_REALIZATION_ROWS.md` §3; carry cells and weakening schema in `spec/JUDGMENT_LAYER.md` §2, §2h, and §7.2 |
| family-level one-shot level-map transport ($k' = k$, $n(\bar\Gamma(C)) > m \cdot n(C)$ per application of $\bar\Gamma$, RG failure-probability `upper-bound` ceiling over $\ell$ levels, amplified distance `unavailable`; **Introduced in:** `stdCSS-3` / `v0.3.0`) | `equality` ($k$), `upper-bound` (RG failure probability and check-weight bounds, scoped as a decoder/noise quantity rather than a §7.1 property), and `unavailable` (amplified distance lower bound) | none (family-level transport rule; no taxonomy operation ID minted) | conditional on Hypotheses 102–103, Lemma 118 ($H_Q(\bar\Gamma) \cong H_Q(C)$), Theorem 81 Eq. (1) (in $\ell$), and Remark 39 seed local triviality (`SCOPE.md` §3–§4) | `conditional` (imported framework hypotheses; finite-seed `bar Gamma` probes separated as `empirical`) | arXiv:2610.02137v1 (Appendix A Defs. 104/106/111/113/116, Lemmas 117–118; Theorem 81 Eq. (1); Remark 39); judgment cells in `spec/JUDGMENT_LAYER.md` §2j; design note and probe separation in `the one-shot level-map transport note` |
| existence of a fixed-point-free ZX duality ($\pi$ with $\pi(S_X) = S_Z$) | (various) | — | not-yet-defined (extended-state layer) | `not-applicable` | [`spec/TAXONOMY.md`](TAXONOMY.md) §4.3 |

**Review finding (second red-team pass, 2026-09-26) — dispositioned
2026-09-26.** The `unavailable` row
for deletion distance covered a bound that is true and derivable: deletion never
increases either sector distance, because the output logical vectors of each
sector are supersets of the input's and a minimum over a superset is no larger
(the $+\infty$ convention included). The MVP rules derive the same bound
whenever judgments transport across row-space equality — delete $r$, re-add its
support (`OBL-PARTIAL-INVERSE-LAWS`, converse order, restores both row spaces),
then addition monotonicity gives the original distance as an upper bound on the
intermediate state. The alternative of forbidding transport across row-space
equality would also block relabeling congruence of judgments.

**Disposition.** The upper bound is
admitted: the inventory above carries a new `upper-bound` row for distance
non-increase under deletion, and `unavailable` is scoped to deletion-distance
lower bounds and equalities. Row-space transport stays available, so relabeling
congruence of judgments is unaffected. The row's evidence status was
`conjectural` pending a hand derivation.

**Update:** the hand derivation is recorded at
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4, so the row now reads
`proved` under the contract's definition (established from the operation
definition and stated hypotheses), with mechanical re-derivation owed at
Gate 2 like every §5 derivation. See that review.

**Flagged inconsistency.** The `P-RELABEL`
taxonomy record (`spec/TAXONOMY.md` §1.1) originally promised transport of
logical witnesses, while this inventory classifies logical-witness judgments as
not-yet-defined. The record's transport claim has since been narrowed to
stabilizer supports only; the dependency
remains open, pending definition of the logical-witness field, which is
future-$\Pi$ data and not MVP state data
([`STATE_MODEL.md`](STATE_MODEL.md) §1). The design-level type sketch lives in the
superseded
CONTEXT_FIELD_INVENTORY.md
§4.1, retained as provenance; the updated future-$\Pi$ sketch is in
[`STATE_MODEL.md`](STATE_MODEL.md) §1/§1a.

*(Intentional provenance: `CONTEXT_FIELD_INVENTORY.md` is superseded; the type sketch above is a design proposal, not a normative
definition. Citation retained for the historical record; not a normative
dependency.)*

**Note.** A `not-yet-defined` slot is recorded for the
applicability judgment of the deferred `X-SYMPLECTIC-HALVE` record: whether a
presented CSS state admits a fixed-point-free qubit involution $\pi$ with
$\pi(S_X) = S_Z$ (a ZX duality of the parent). This is a decidable
linear-algebra property of the state, but no proposition for it is formulable
in the MVP assertion language, so the row is `not-yet-defined`, not
`unavailable` — nothing is deliberately underivable here; the predicate simply
does not exist yet (Outcome vocabulary below). The judgment would become
load-bearing only if the extended-state extension enters at Gate 6;
no transition, obligation, or fixture changes now.

## Outcome vocabulary

Four outcomes are distinct and must not be conflated. Each label attaches to
*one claim in a stated scope* — exactly one label is recorded per claim — and
the four together separate the three axes that survive the red-team review: truth,
derivability, and deliberate exclusion. They are **not** a disjoint partition of
mathematical facts: `unavailable` is by design a species of underivable, and
soundness makes a `false` assertion underivable as well. What the vocabulary
commits to is which of these the calculus is asserting about the claim at hand,
and every `not derivable` label must name its scope — the rule system it refers
to and the date of the record.

- **false** — a semantic counterexample exists: the assertion is untrue of the
 state.
- **not derivable** — the current rule system has no derivation of the
 assertion. This is a fact about derivability and may hold by absence (the
 system is incomplete here) or by design.
- **unavailable** — claim shape `unavailable`: a property deliberately
 represented as not derivable in the MVP, such as deletion-distance lower
 bounds and equalities (the non-increase upper bound is an included
 `upper-bound` claim; see *Disposition* above). Its
 underivability is a design commitment, not a gap, and it cannot be derived by
 omission (`spec/VOCABULARY.md`, *Unavailable judgment*). Unavailability is claimed
 per evaluation, not per state.
- **not yet defined** — outside the current assertion language or deferred
 design surface (rate predicates, future-$\Pi$ fields): no proposition is yet
 formulable.

A specified future path exists for one of these outcomes: an `unavailable`
per-state claim (such as a deletion-distance lower bound or equality) may be
reclassified in a future release as a `lower-bound`/`equality` claim with
evidence status `certificate-checked`, through the mechanized certificate
checker (see *Mechanized checker* above), and only on a per-state atomic
judgment — never on an operation contract. The search that produced the certificate remains non-normative
computation; the calculus checks the certificate. Until that release, the claim
stays `unavailable`.

**Qualification (second red-team pass, 2026-09-26) — superseded by the
dispositions below.** The reclassification path above was
provisional: whether `unavailable` attaches to evaluations or to states was
undecided, and `certificate-checked` evidences an instance rather than a
schema.

**Dispositions (two findings, 2026-09-26).** Both questions
are settled: `unavailable` attaches to evaluations, not to states, and
`certificate-checked` attaches to per-state atomic judgments, never to an
operation contract. The wording above is updated in place; the
worked-example record is at
WORKED_EXAMPLES.md `W13`.

*(Intentional provenance: `WORKED_EXAMPLES.md` is superseded; no
clean successor in `spec/` for this worked-example record. The instance is
retained as fixture `W13` in `machine/fixtures/mvp_fixtures.json`; the
judgment-transport half is recorded at `spec/JUDGMENT_LAYER.md` §4 and
`spec/OPERATIONAL_SEMANTICS.md` §4.11. Citation retained for the historical
record; not a normative dependency.)*

**Review finding (a red-team review, 2026-09-25) — dispositioned.** **A red-team finding** held that the four labels are
not four disjoint semantic outcomes — `unavailable` is a subset of underivable
and soundness makes `false` underivable too — that `W13` gives no separate
not-derivable-but-not-unavailable example, and that a new underivability claim
needs an explicit scope rather than an unsupported claim of no derivation.

**Disposition.** The vocabulary is
restated rather than replaced: the four labels classify a claim *in a scope*,
one label per claim, and they separate truth, derivability and deliberate
exclusion instead of asserting a semantic partition — which is what the opening
paragraph above now says. Two further conditions travel with it: every
`not derivable` label names its scope (rule system plus record date), and no
bare not-derivable label is recorded until the general derivation system is
fixed (Gate 5), which is why `W13` contains none. See that review, and the
matching records in `spec/JUDGMENT_LAYER.md` and
`spec/OPERATIONAL_SEMANTICS.md`, and `WORKED_EXAMPLES.md` `W13`.

WORKED_EXAMPLES.md `W13` exhibits all four labels on a
single state, one per claim and each with its scope.

*(Intentional provenance: see the note above — `WORKED_EXAMPLES.md` is
superseded and the instance is retained as fixture `W13` in
`machine/fixtures/mvp_fixtures.json`; the citations above are historical
record, not normative dependencies.)*

---

# Initial contract index

The initial calculus should develop contracts in this order:

| Taxonomy ID | Operation | Initial contract status |
| --- | --- | --- |
| `C-SKIP` | Identity / `skip` | `contract-proved` (promoted 2026-11-18) |
| `C-DIRECT-SUM` | Direct sum | `contract-proved` (promoted 2026-11-18) |
| `C-DELETE-CHECK` | Stabilizer/check deletion | `contract-proved` (promoted 2026-11-18) |
| `C-ADD-CHECK` | Stabilizer/check addition | `contract-proved` (promoted 2026-11-18) |
| `C-SEQUENCE` | Sequential composition | `contract-proved` (promoted 2026-11-18) |
| `P-RELABEL` | Qubit relabeling | `taxonomy-only` |
| `P-REBASE` | Generator rebasing | `transition-defined` |
| `E-PEEL` | Qubit/check peeling | `transition-defined` |
| `E-GRAFT` | Row-space grafting | `transition-defined` |
| `E-PUNCTURE` | Puncturing | `transition-defined` |
| `E-GLUE` | Interface gluing | `contract-stated` (2026-11-18: binary-only expression constructor; algebraic extraction mechanized in `GlueExtraction.lean` with geometric move-word gap recorded; conditional cell, Gate 6 unchecked) |
| `E-EXTEND` | Patch growth / breeding | `transition-defined` |
| `E-LOCAL-HADAMARD` | Local Hadamard | `transition-defined` |
| `E-SPLIT` | Split | `taxonomy-only` |
| `L-HGP` | Hypergraph product | `transition-defined` (admitted 2026-11-11) |
| `L-LIFTED` | Lifted product | `transition-defined` (admitted 2026-11-11) |
| `L-NESTED-CSS` | CSS code from nested classical codes | `transition-defined` (admitted 2026-11-13) |
| `L-EMPTY` | Empty code (nullary base constructor) | `transition-defined` (admitted 2026-11-19) |
| `L-FREE` | Free code (qubit-set base constructor) | `transition-defined` (admitted 2026-11-19) |
| `A-PULLBACK` | Pullback / fiber product | `transition-defined` (admitted 2026-11-19) |
| `A-PUSHOUT` | Pushout / amalgamated sum | `transition-defined` (admitted 2026-11-19) |
| `L-PAIR-PARTITION` | Pair-partition relative-permutation construction | `transition-defined` (admitted 2026-11-22) |
| `PP-SCALE` | Explicit extension of a pair-partition code | `transition-defined` (promoted 2026-11-22) |

| `L-TILE` | Tile or cellulation construction | `transition-defined` (admitted 2026-11-11) |
| `L-TANNER` | Local code on a graph / quantum Tanner construction | `transition-defined` (admitted 2026-11-11) |
| `L-BALANCED` | Balanced product | `transition-defined` (admitted 2026-11-11) |
| `L-GROUP-ALGEBRA` | Group-algebra and two-block constructions | `transition-defined` (admitted 2026-11-11) |
| `A-DOUBLE` | Duplication ("double it") | `transition-defined` (admitted 2026-11-11) |
| `A-PRODUCT` | Algebraic product of code-level objects | `transition-defined` (admitted 2026-11-11) |
| `A-CONCAT` | Concatenation | `transition-defined` (admitted 2026-11-11; the tower price provider is separate) |
| `A-QUOTIENT` | Quotient and subspace transformation | `taxonomy-only` (monomial-quotient specialization row in `TAXONOMY.md` §2.15 and conditional transfer-theorem cell in `JUDGMENT_LAYER.md` §2i; constructor remains at rung 1) |
| `X-SYMPLECTIC-DOUBLE` | Symplectic doubling | `taxonomy-only` |
| `X-SYMPLECTIC-HALVE` | Symplectic halving | `taxonomy-only` |
| `X-SUBSYSTEM` | Subsystem-code deformation | `taxonomy-only` |
| `X-GAUGE-FIX` | Gauge fixing | `taxonomy-only` |
| `X-LOCAL-CLIFFORD` | Local/block-Clifford conjugation | `taxonomy-only` |
| `X-DRESSED-QUOTIENT` | Dressed quotient | `taxonomy-only` |
| `X-WEIGHT-REDUCTION` | Weight reduction to subsystem codes | `taxonomy-only` |
| `X-GAUGING` | Commuting-check gauging | `taxonomy-only` |

For Gate 7 constructors (`A-*`, `L-*`, `X-*`), rung 1 records taxonomy presence
only and does not imply in-scope status. Typed input signatures for the
fifteen Gate 7 candidates are recorded in the taxonomy: the typed objects each
consumes, the obligations it incurs, and whether each input is constructive or
axiomatic. Ten of the fifteen (`L-HGP`, `L-LIFTED`, `L-GROUP-ALGEBRA`,
`A-CONCAT`, `L-BALANCED`, `L-TANNER`, `L-TILE`, `A-PRODUCT`, `A-DOUBLE`,
`L-NESTED-CSS`) were subsequently admitted as `transition-defined` expression
constructors (2026-11-11/13); `A-QUOTIENT` and the
`X-*` extended-state entries remain at `taxonomy-only`.

The initial five contracts test the schema against the planning kernel. Their
records were completed for Gate 0 on 2026-10-27 (rung 5, `contract-stated`) and
promoted to **rung 6 (`contract-proved`)** by dated maintainer decision on
2026-11-18 ( see *Kernel operation contracts* above,
`OPERATIONAL_SEMANTICS.md` §4.39 for logical-sector quotients, and §4.40 for
the `stdCSS-3` metatheorem re-discharge ledger). Rung 6 records hand-derivation
evidence (`proved`), not rung 7 (`mechanized`) and not Gate 2–5 ratification:
mechanization remains owed and Gates 2–7 remain unchecked. `E-GRAFT` remains at
`transition-defined`: its contract fields were completed in the Gate 0 pass,
while its lifecycle position is unchanged. `OBL-GRAFT-TRANSITION-SOUNDNESS` is
discharged at §4.12, but no dated decision has promoted `E-GRAFT` past
`transition-defined` (promotion is not implicit). Without a supplied price,
exact deletion distance is `unavailable` and distance non-increase remains an
included `upper-bound` claim. The full-distance price is a separate conditional
cell, not an implicit or empirical claim.

A Lean skeleton now exists under `lean/` (mechanization authorization: maintainer directive 2026-09-26, Addenda item 2, restated in `AGENTS.md` under *Mechanization boundary*). Syntax, relabeling equivalence, and `EvalExpr` remain content not yet delivered.
