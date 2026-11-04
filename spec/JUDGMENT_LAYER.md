# Judgment Layer

**Status:** normative. What the calculus can *claim* about a state, and how it
says "no".

Consolidated from the property inventory and claim inventory in
[`CLAIMS.md`](CLAIMS.md).

---

## 1. Two vocabularies, at different levels

They are not the same thing, and conflating them is the most common misreading of
the framework.

**Evaluation outcomes** — what happens when a term is run:

| | |
| --- | --- |
| `derivable` | a derivation exists and the assertion is included |
| `no_derivation` | well-typed, but no evaluation derivation — **absence of derivation *is* the behaviour** |
| `malformed` | rejected by the grammar alone |

**Claim statuses** — what may be asserted about a property:

| | |
| --- | --- |
| `false` | a semantic counterexample exists |
| `not derivable` | no derivation in the current rule system; may be a gap or by design |
| `unavailable` | **deliberately** underivable, by design commitment; cannot be derived by omission |
| `not yet defined` | outside the current assertion language |

A `no_derivation` evaluation is a **fact about a term**. An `unavailable` claim is
a **commitment about the calculus**. The same run produces both, and they are
recorded separately.

## 2. The carry table

Cell-major: one row per property, one column per primitive. This is the
transposition of the property-major inventory in
[`CLAIMS.md`](CLAIMS.md), and it is the deliverable the
scope note specifies as *"for each property and for each transformation, carries /
does not carry / not yet defined, scoped per evaluation."*

Verdicts: **carries** · **does not carry** · **not yet defined**. Evidence status
in brackets.

| Property | `C-SKIP` | `C-DIRECT-SUM` | `C-DELETE-CHECK` | `C-ADD-CHECK` | `C-SEQUENCE` | Instance of (S1–S3) |
| --- | --- | --- | --- | --- | --- | --- |
| $n$ | carries, $n'=n$ `[proved]` | carries, $n=n_A+n_B$ `[proved]` | carries, $n'=n$ `[proved]` | carries, $n'=n$ `[proved]` | carries `[proved]` | derived transfer (§7.2.1); S3 monotone (§9.4) |
| $k$ | carries, $k'=k$ `[proved]` | carries, $k=k_A+k_B$ `[proved]` | carries, $k'=k+1$ `[proved]` | carries, $k'=k-1$ `[proved]` | carries `[proved]` | derived transfer (§7.2.1); S3 monotone (§9.4) |
| $w$ (max stabilizer weight) | carries, $w'=w$ `[proved]` | carries, $w=\max(w_A,w_B)$ `[proved]` | carries, $w'=\max\{\mathrm{wt}(r):r\in\mathit{rows}'\}$ `[proved]` (exact; $\le w$) | carries, $w'=\max(w,\mathrm{wt}(r))$ `[proved]` | carries `[proved]` | derived transfer + monotonicity (§7.2.1–2); S3 monotone (§9.4) |
| Tanner connectivity (displayed rows) | carries, unchanged `[proved]` (§4.22) | always decreases: the direct sum is a disjoint union, so the graph is disconnected; the child certifies a disconnected code, which is why the challenge's `tanner_connected` hard gate rejects it `[proved]` (§4.22) | can decrease: a deleted check may be a cut vertex `[proved]` (§4.22) | cannot decrease: a new check adds a node and edges `[proved]` (§4.22) | carries by composition `[proved]` (§4.22) | monotonicity (§7.2.2); S3 monotone (§9.4); §4.22 |
| $r$ (interaction radius, relative to a layout) | carries, $r'=r$ `[proved]` | carries, $r=\max(r_A,r_B)$ `[proved]` (conditional on an honest merged layout; §2d.3) | carries, $r'=\max\{\mathrm{diam}_\lambda(s):s\in\mathit{rows}'\}$ `[proved]` (exact; $\le r$) | carries, $r'=\max(r,\mathrm{diam}_\lambda(r_{\rm new}))$ `[proved]` | carries by composition `[proved]` | derived transfer + monotonicity (§7.2.1–2); S3 monotone (§9.4); §2d |
| $d_X$ | carries, $d_X'=d_X$ `[proved]` | carries, $d_X=\min(d_X^A,d_X^B)$ `[proved]` | carries **as a bound only**: $d_X'\le d_X$ `[proved]`; exact value remains **`unavailable`** under the current input schema (a sector-specific price would need separate admission) | lower bound `[proved]`; exact value `open` | carries by composition `[open]` | atomic opaque (§7.1, opacity `distance`); S2 transformers (§8.3) + soundness (§8.4); S2 precision (§8.2); S3 (§9.1); §4.13; §7.3 (C-SEQUENCE: composition on single-polarity chains only) |
| $d_Z$ | carries, $d_Z'=d_Z$ `[proved]` | carries, $d_Z=\min(d_Z^A,d_Z^B)$ `[proved]` | carries as a bound only: $d_Z'\le d_Z$ `[proved]`; exact value remains **`unavailable`** under the current input schema (a sector-specific price would need separate admission) | as $d_X$ | carries by composition `[open]` | atomic opaque (§7.1, opacity `distance`); S2 transformers (§8.3) + soundness (§8.4); S2 precision (§8.2); S3 (§9.1); §4.13; §7.3 (C-SEQUENCE: composition on single-polarity chains only) |
| $d$ | carries, $d'=d$ `[proved]` | carries, $d=\min(d^A,d^B)$ `[proved]` | carries **as a bound only**: $d'\le d$ `[proved]`; exact value **`unavailable`** unless $w_{\mathrm{del}},w_{\mathrm{exp}}$ are supplied, in which case $d'=\min(d,w_{\mathrm{del}},w_{\mathrm{exp}})$ `[conditional]` | lower bound `[proved]`; exact value `open`; strict improvement `[conditional]` | carries by composition `[open]` | derived from the two atoms by `min` (§7.1); S2 reduced product (§8.8); S2 precision (§8.2); S3 (§9.1); §4.13/§4.19; §7.3 (C-SEQUENCE: composition on single-polarity chains only) |
| output well-formedness | carries `[proved]` | carries `[proved]` | carries `[proved]` | carries `[proved]` | carries `[proved]` | predicate preservation (§7.3); S2 soundness (§8.4); §4.7–§4.9 |

**Reading the last column.** The "Instance of (S1–S3)" column cites, for each
row, the schema of S1 (`JUDGMENT_LAYER.md` §7.2) under which its cells are
instances, and, where applicable, the abstract-interpretation transformer of S2
(§8.3) that licenses the endpoint update and the refinement-preorder axis of S3
(§9.1 for interval precision, §9.4 for move monotonicity) that the verdicts are
monotone in. The mapping is the one recorded in §7.3, read with §7.4; the
column only brings it to the cell level. No cell verdict, evidence label, or
qualification changes; the column is citation, not re-derivation. Rows whose
exact value is `unavailable` or whose cell is `[open]` cite the schema that
would license them and note the absence of a transformer or composition instance
where it applies (see §8.10 for the distinction between `unavailable` and top).
Pointers of the form §4.x refer to `spec/OPERATIONAL_SEMANTICS.md` §4;
§7.x/§8.x/§9.x refer to this document.

**Connectivity (display-relative, `E-GRAFT` included).** The five-column table
above covers the MVP primitives; `E-GRAFT` is not an MVP primitive and is
recorded here separately:

| Primitive | Tanner connectivity |
| --- | --- |
| `C-SKIP` | unchanged `[proved]` (§4.22) |
| `C-ADD-CHECK` | cannot decrease `[proved]` (§4.22) |
| `C-DELETE-CHECK` | can decrease `[proved]` (§4.22) |
| `E-GRAFT` | can decrease `[proved]` (§4.22) |
| `C-DIRECT-SUM` | always decreases (disconnected) — the child certifies a disconnected code, which is why the challenge's connectivity gate rejects it `[proved]` (§4.22) |

The `E-GRAFT` row's applicability guard ("every remaining qubit is touched
by both check types") is already connectivity-shaped; carrying connectivity
would let the calculus state it precisely. The stabilizer-group connectivity
check (strictly stronger) is not yet carried.

**Three claims do not carry unconditionally: two are `unavailable`, and the
third is the $d$ row's strict-improvement half above, `conditional`:**

| Claim | Through | Status | Why |
| --- | --- | --- | --- |
| a claim referencing a **deleted generator** | `C-SEQUENCE` | **`unavailable`** | claimed **per evaluation, not per state**  — the `W13` half, `OBL-JUDGMENT-TRANSPORT` |
| a **row-referencing certificate** through the `W7` loop | `C-DELETE-CHECK` → `C-ADD-CHECK` | **`unavailable`** | invalidated at the deletion step even though the final code equals the original — information-losing at the context level |
| **strict improvement** of distance | `C-ADD-CHECK` | **`conditional`** | carries $d' \ge d+1$ when the consumer supplies the minimum-weight-class hypothesis; otherwise `unavailable` |

**Everything outside this table is `not yet defined`** — certificates and
interface/metric/logical-witness judgments generally, support-sensitive predicates
under rebasing, circuit/DEM/realization predicates, and the fixed-point-free ZX
duality. These are not gaps in the table; they are outside the current assertion
language.

**`C-DIRECT-SUM` is exact, and terminal.** The direct-sum law
$d=\min(d^A,d^B)$, $k=k_A+k_B$ is exact and free, but the state it produces is
a **disjoint union**: the two blocks share no qubit, so the code's Tanner
graph is **disconnected**. The calculus has no move that connects them, so a
direct sum is a terminal step for any purpose that needs a connected code.
The law is about the property, not about the code's usefulness; a consumer
that needs connectivity must supply a connecting move the calculus does not
provide, and until it does, the direct-sum cell certifies a disconnected
code.

**Two equivalence relations, and neither takes a column.** The table indexes the
five MVP primitives. Presentation equivalence $\approx$ — transport of qubits,
displayed rows, identifiers, and sector labels along a relabeling
([`TAXONOMY.md`](TAXONOMY.md) §1.4) — is performed by no primitive, so it takes
no column. `P-REBASE` is neither an MVP command nor a quotient, so the
presentations it relates are **not identified by any equivalence the calculus
states**, and a property judgment here is offered *per operation*, never *per
class of presentations*. Reading a distance bound across a rebasing is
therefore `not yet defined` — the same status, and for the same reason, as
`OBL-REBASE-GENERATION`: no grammar production, so no cases to range over. **The
absence of such a row is a position, not an oversight.** An equivalence-class axis
is a Gate 6 decision, out of scope under the stopping point
(SCOPE.md §4).

*(Clarification, 2026-10-13. This states positions already of record in
[`TAXONOMY.md`](TAXONOMY.md) §1.4, SCOPE.md §4–§5, and
`OBL-REBASE-GENERATION`. It takes no new position, changes no cell, mints no
identifier, and asserts nothing a cited artifact does not already assert.)*

## 2a. Admitted priced construction moves (conditional cells)

These moves are not MVP primitives, but their conditional cells are included in
the current design scope under the priced-construction-calculus decision of
2026-10-19. This scope decision does not establish the transition or judgment
soundness obligations. A cell carries an exact or improved bound only when the
consumer supplies the stated hypothesis; otherwise the corresponding cell is
`unavailable`, not a guess.

| Move | Property | Carries when hypothesis supplied | Hypothesis (consumer-supplied) | Source |
| --- | --- | --- | --- | --- |
| `E-GRAFT` | $d$ | sector-wise: $d'_\sigma=\min(d_\sigma,w_{\mathrm{expose},\sigma})$ for the non-spliced sector; the spliced sector carries its lower endpoint and drops its upper; the scalar form $d'=\min(d,w_{\mathrm{expose},\bar\tau})$ is false for this transition (see §4.13) | exposure minimum in the non-spliced sector and the structural coverage condition | Theorem 28.2 (external input; see REFERENCES.md); claim remains conditional on the consumer-supplied hypothesis; derivation at `OPERATIONAL_SEMANTICS.md` §4.13 |
| `C-DELETE-CHECK` (priced) | $d$ | exact: $d'=\min(d,w_{\mathrm{del}},w_{\mathrm{exp}})$ | $w_{\mathrm{del}},w_{\mathrm{exp}}$ minima over the promoted and exposed sets | Theorem 12.1 (external input; see REFERENCES.md); derivation reproduced at `OPERATIONAL_SEMANTICS.md` §4.19; claim remains conditional on the consumer-supplied hypothesis |
| `C-ADD-CHECK` (strict improvement) | $d$ | $d'\ge d+1$ | exact old $d$ and exhaustive minimum-weight-class enumeration, all killed | Proposition 18.3 (external input; see REFERENCES.md); derivation reproduced at `OPERATIONAL_SEMANTICS.md` §4.19; claim remains conditional on the consumer-supplied hypothesis |
| `C-ADD-CHECK` (sector-aware gauging) | $d_X$, $d_Z$ | the supplied sector's lower endpoint is raised to $w_\sigma$ (never below the carried bound); the unpriced sector keeps its carried lower bound; when both $w_X,w_Z$ are supplied the full-distance lower endpoint may be raised to their minimum ($d=\min(d_X,d_Z)$) | sector minima $w_X,w_Z$ over the surviving logical classes and an evidence reference | Lemma 18.5 (external input; see REFERENCES.md); claim remains conditional on the consumer-supplied hypothesis |
| `C-ADD-CHECK` (direct-sum extinction) | $d$ | $d'=d_B$ (exact) when $d_B>d_A$ | exact old $d$ ($=d_A$), the trusted factor distance $d_B$ with an evidence reference, and the computed structural side — a two-block disjoint union, the added check inside one block, $k$ of the block containing the added check equal to zero, $k$ of the surviving block at least one, and no carried sector bound exceeding $d_B$ | Proposition 18.6 + Corollary 18.7 (external input; see REFERENCES.md); **stack family only**: the cell is stated for stack parents, and no family other than the source's stack/direct-sum family is licensed; claim remains conditional on the trusted $d_B$; general $k'>0$ remains open and is not claimed solved |
| `A-CONCAT` towers ($k_{\mathrm{in}}=1$), price provider | deletion/exposure price input | factorization from tower level data | tower structure, class dictionary, outer presentation | Theorems 27.2 / 27.5 (external input; see REFERENCES.md); not a calculus constructor. A $k_{\mathrm{in}}>1$ generalization exists in the source (Theorem 27.8) with a refined class dictionary; it is proved but not sweep-verified here (tracked in `spec/OBLIGATIONS.md`). Its cost tables have size $2^{2k_{\mathrm{in}}}$. |
| `E-GRAFT` | $r$ (interaction radius) | exact: $r'=\max\{\mathrm{diam}_{\lambda'}(s):s\in\mathit{rows}'\}$; and $r'\le 2r$ | **none** — the radius is exactly computable, so no hypothesis is needed; §2d.2 | derivation [`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4.21 (interaction-radius transport) |

The radius row is listed here because §2a is the conditional-cell table; its
hypothesis is vacuous (the radius is exactly computable, so no consumer input
is needed), and §2d.2 carries the authoritative cell.

**Where the strict-improvement cell is cheap, and where it is not.** The cell
is conditional, and the condition is rarely satisfiable: the challenge
fieldnote of 2026-10-19 (imported reference),
reports 0 strict improvements out of 736 valid single-check additions for
$n \le 10$, with its negatives bounded to $n \le 20$ parents and witness
search up to weight 6-8. The condition is not vacuous: at distance 1 it
reduces to one commuting check that kills every weight-1 logical, which is
Proposition 18.3's condition instantiated at $d = 1$, not a survey result. A
yield statistic claimed for that region ("4 of 12 survivors") is **withdrawn
as unrecorded** (DIARY, 2026-10-20). The region is a property of the *search*,
not of the cell: the cell carries $d' \ge d+1$ wherever its hypothesis holds,
and the hypothesis is what is hard to come by. The search-side procedure is
recorded as an external recipe in §7.

A conditional formula is not an executable certificate. The consumer checks
that inputs are present and records their evidence reference; it does not
establish their truth or computational cost. Without a deletion price, the
proved deletion upper bound remains available and the lower endpoint is reset
to zero. Without a graft price, the admitted graft non-increase cell can carry
an input upper bound, but no positive lower endpoint is inferred. Without the
minimum-weight-class enumeration, strict improvement is `unavailable`.

## 2b. Consumer interval rules

For each of $d,d_X,d_Z$, the consumer keeps $[L,U]$ where $L$ is a sourced
lower bound and $U$ is justified by a currently valid logical witness or a
licensed monotonicity/price rule. The initial default is $[0,+\infty]$ with
challenge witnesses supplying only upper endpoints. $+\infty$ is also the
distance when $k=0$. The ledger is not part of state identity.

| Transition | Lower endpoint | Upper endpoint |
| --- | --- | --- |
| `C-SKIP` | unchanged | unchanged |
| `C-ADD-CHECK` | carry the old lower bound; strict improvement may raise it under §2a | discard stale endpoints and retain only witnesses revalidated in the child |
| `C-DELETE-CHECK` | reset to zero unless the explicit price formula supplies a stronger endpoint | carry the proved $d'\le d$ bound and tighten from surviving or new witnesses |
| `E-GRAFT` | full distance: reset to zero unless a supplied exposure price tightens it. Spliced sector: carry the lower endpoint; drop the upper endpoint to $+\infty$ unless a witness valid in the child supplies one. Non-spliced sector: reset to zero | full distance: lower endpoint resets to zero unless priced; upper endpoint is the non-spliced sector's carried bound, tightened by child-valid witnesses. Spliced sector: carries the lower endpoint only; upper endpoint from child-valid witnesses. Non-spliced sector: carry the non-increase bound and tighten from surviving or new witnesses |
| `P-REBASE` | unchanged (the row spaces are unchanged, so every span-expressible endpoint stays valid for the child) | unchanged (a parent-valid witness is valid for the identical child spans; revalidation is unnecessary and never discriminates) |
| `E-LOCAL-HADAMARD` ($T=Q$) | swap the two sector lower endpoints (§4.27: $d_X'=d_Z$, $d_Z'=d_X$); the full-distance lower endpoint keeps — $d'=d$ | swap the two sector upper endpoints likewise and *then* revalidate every witness against the child with its side swapped (an old $\sigma$-side witness is checked as a $\bar\sigma$-side witness of the child); the full-distance upper endpoint keeps |
| `E-PEEL` | reset to zero in every sector and the full distance. The reset is a refusal by design, not an impossibility: §4.28 derives $d_\tau'\ge d_\tau$ for the selected sector and $d_{\bar\tau}'\le d_{\bar\tau}$ for the opposite sector (the $m=1$ instance of §4.13's graft argument), and no cell carrying either direction is admitted; the full distance is bounded in neither direction (§4.28's witness) | only witnesses valid in the child (a parent-valid witness is not automatically a child-valid one: the child's sample space and spans both changed) |
| `E-PUNCTURE` | reset to zero in every sector and the full distance — a refusal by design, not an impossibility: §4.29's unnamed free-qubit instance (puncturing qubit $2$ of $Q=\{0,1,2\}$ with the $Z$ display $\{0,1\}$) raises the $X$ distance $1\to2$, showing that the direction of change depends on the deleted qubit and the induced stabilizer update; no universal $\le$- or $\ge$-claim is derivable for either sector or the full distance, and no cell carrying an endpoint is admitted. The reset is sound; full-distance endpoints remain refused unless a separately admitted price supports them | only witnesses valid in the child, as for the peel |
| `E-EXTEND` | with $\Delta=\varnothing$: every sector carries its lower endpoint (distance cannot decrease under an added check); with $\Delta\neq\varnothing$: every interval's lower endpoint resets to zero | with $\Delta=\varnothing$: every sector rebuilds its upper endpoint from child-valid witnesses only (the pre-change upper endpoint is not a sound bound); with $\Delta\neq\varnothing$: only witnesses revalidating in the child |
| `C-DIRECT-SUM` | combine corresponding endpoints with `min` | combine corresponding endpoints with `min` |
| `E-GLUE` | in every sector and the full distance, `min` of the two factor ledgers' lower endpoints (sound without a certificate: the glued code is $C_A\oplus C_B$ with seam checks added, each sector distance of the direct sum is the minimum of the factors', and adding a check never lowers a distance, so each glued distance is at least the factor minimum, §4.31) | only the Z sector's, as `min` of the two factors' Z upper endpoints, and only under an admissible seam certificate (§2e); the X and full upper endpoints are left to witnesses valid in the child |

For a supplied price $p$ the monotone map $f(x)=\min(x,p)$ transports an
input interval to $[\min(L,p),\min(U,p)]$. **A price moves the endpoints its
own relation covers, and no others.** The two prices the consumer accepts are
indexed differently, and the difference is load-bearing:

- The **deletion** price is a *full-distance* price. The source states the
 deletion relation on the full distance,
 $d'=\min(d,w_{\mathrm{del}},w_{\mathrm{exp}})$, with no sector-wise
 counterpart, so it moves the full-distance endpoints and **no sector
 endpoint**. A sector-specific deletion price would need separate admission.
- The **graft exposure** price is indexed to the **non-spliced** sector, and
 the source's graft relation is stated sector-wise, so it moves that sector's
 endpoints as well as the full distance's.

Every upper-bound witness is checked against the child state by finite-field
arithmetic. A witness is only ever an upper bound: it may **tighten** a
carried endpoint, and may never widen or discard one. The consumer never
searches the distance itself.

**The graft's sector rules are sector-wise, but the spliced sector is not
carried exactly.** Under the transition as specified in
`spec/OPERATIONAL_SEMANTICS.md` §2, $C'_\tau=\{x|_{Q\setminus\{q\}}:x\in
C_\tau,\,x_q=0\}$, so $d_\tau(C')\ge d_\tau(C)$ with strict inequality
possible. The previously stated rule $d'_\tau=d_\tau$ exactly is **false** for
this transition, and so is the unpriced non-increase bound $d'\le d$
(see `spec/OPERATIONAL_SEMANTICS.md` §4.13, 2026-10-21). The corrected
unpriced rule: the spliced sector carries its lower endpoint and drops its
upper endpoint to $+\infty$ unless a witness valid in the child supplies one;
the non-spliced sector keeps its non-increase bound; and the full distance
resets its lower endpoint to zero unless priced and carries the non-spliced
sector's upper bound, tightened by child-valid witnesses. The
exposure-price relation $d'_{\bar\tau}=\min(d_{\bar\tau},
w_{\mathrm{expose},\bar\tau})$ for the non-spliced sector is retained.

The relation's derivation is now reproduced in this repository
(`OPERATIONAL_SEMANTICS.md` §4.13, 2026-10-21), so the metatheorem
`OBL-PRICED-INTERVAL-SOUNDNESS` is `proved` under the corrected rules; the
cell itself stays `conditional` on the consumer-supplied exposure minimum.

For target $T$, return `certify` when $L_d\ge T$, `prune` when finite
$U_d<T$, and `re-measure` otherwise. These are decisions relative to the
ledger's explicit inputs. A `certify` result inherits the evidence status of
its lower-bound source; it does not upgrade that source.

## 2c. Typed meanings of priced inputs (`OBL-PRICED-INPUT-SEMANTICS`)

Each consumer-supplied input is a typed judgment hypothesis, not a state field.
The calculus's soundness statement exposes each input as an explicit premise: if
the hypothesis is false, the derived conclusion is not licensed, but the
transition itself may still be applicable. The consumer records the source
reference as provenance only; a nonempty source string is not validation.

- **Lower bound $L$ (nonnegative integer).** Binds to a specific state $C$ and a
 property: asserts $d(C)\ge L$ (and $d_\sigma(C)\ge L$ per sector where
 applicable). Recorded with a source reference; the consumer does not verify the
 underlying computation.

- **Deletion price $(w_{\mathrm{del}},w_{\mathrm{exp}})$.** Binds to a
 transition $C\xrightarrow{\operatorname{delete}_r}C'$. Asserts
 $d(C')=\min(d(C),w_{\mathrm{del}},w_{\mathrm{exp}})$ for the full distance.
 Here $w_{\mathrm{del}}=\min\{\operatorname{wt}(g):g\in S\setminus S'\}$ over
 the deleted stabilizer coset and
 $w_{\mathrm{exp}}=\min\{\operatorname{wt}(E):E\in N(S')\setminus N(S)\}$
 over newly exposed normalizer elements. Sector-specific deletion values
 require separately stated sector prices; no global price is reused.

- **Exposure price $w_{\mathrm{expose}}$.** Binds to a transition
 $C\xrightarrow{\operatorname{E-GRAFT}(q,\tau,\vec r)}C'$ and to the exposed
 set in the non-spliced sector $\bar\tau$: the exposed set is the child
 $\sigma$-logicals whose lift touches $q$, with
 $w_{\mathrm{expose},\sigma}=\min\{|z|-1:z\text{ a parent }\sigma\text{-logical with }z_q=1\}$
 (or $+\infty$ if none), and the relation is
 $d'_\sigma=\min(d_\sigma,w_{\mathrm{expose},\sigma})$. The spliced sector
 needs no price. No carry rule for the spliced sector's upper endpoint is
 licensed by this hypothesis (see §4.13 and §2b).

- **Sector-aware gauging prices $(w_X, w_Z)$ (added 2026-10-23, ;
 extends this obligation, not discharged).** Binds to a transition
 $C\xrightarrow{\operatorname{addStab}_{r:\tau}}C'$ with a sector-pure added
 check. For each supplied sector $\sigma$: asserts
 $d_\sigma(C')=w_\sigma$, where $w_\sigma$ is the minimum weight over the
 surviving $\sigma$-logical classes (the classes that survive the added
 check — Lemma 18.5's anticommutation/membership split); the unpriced sector
 keeps its carried lower bound. The consumer raises the supplied sector's
 lower endpoint to $w_\sigma$ without lowering a carried bound and does not
 verify the minimization. General stabilizer codes remain out of scope.

- **Direct-sum extinction (added 2026-10-23, ; extends this
 obligation, not discharged).** Binds to a stack/direct-sum parent
 $C = A \sqcup B$ and a transition adding a sector-pure check inside one
 block. Asserts $d(C')=d_B$ *exactly* (the child interval is
 $[d_B,d_B]$), where $d_B$ is the surviving block's min-sector distance,
 trusted with an evidence reference. The cheap structural side is
 **computed, not trusted**: the parent is a two-block disjoint union, the
 added check lies inside one block, $k$ of the block containing the added
 check is zero, $k$ of the surviving block is at least one, and no carried
 sector bound exceeds $d_B$. **Stack family only**: no other
 family is licensed, and the general $k'>0$ case remains open and is not
 claimed solved.

- **Strict-improvement enumeration.** Binds to a transition
 $C\xrightarrow{\operatorname{addStab}_{r:\tau}}C'$ and to a state $C$ with
 $d(C)=\text{base\_distance}$: asserts that every weight-$d(C)$ logical in
 $C$ either anticommutes with $r$ (in sector $\bar\tau$) or lies in
 $C_\tau+\langle r\rangle$ (in sector $\tau$). The cell carries
 $d'\ge d+1$ only under that hypothesis.

- **Witness.** A subset $u\subseteq Q(C')$ with $|u|=w>0$ such that
 $u\in (C'_{\bar\sigma})^\perp\setminus C'_\sigma$ for the stated sector
 $\sigma$ in the stated state $C'$; checked by finite-field linear algebra,
 and certifies $d_\sigma(C')\le w$. The consumer validates structural shape
 only, not truth of the minimum.


## 2d. The layout as a ledger parameter

### 2d.1 What the layout is, and is not

A **layout** $\lambda$ assigns a coordinate to every qubit of a state, together
with a layer count $\rho$ and optionally a module id per qubit. It is
**ledger data**: supplied per code, not minted, not part of state identity, and
not transported by `used` ([`STATE_MODEL.md`](STATE_MODEL.md) §1, §3). Two
states that differ only in their layout are the same state, and a layout
without a state has nothing to describe.

The **interaction radius** $r(C,\lambda)$ is the largest Euclidean diameter of
any displayed row's support in $\lambda$. It is a **derived property of the
display relative to the layout**, in the same sense that $w$ is a derived
property of the display: it is computed, never stored, and no search is
involved. It is a function of the *pair* (state, layout), so a state with no
layout has no radius, and the calculus never claims one for the state alone.

Unlike every distance cell above, **no radius cell needs a hypothesis**. The
quantity is exactly computable from the display and the layout, so the
consumer computes it rather than trusting a price, a bound, or a witness.

**Arithmetic.** The calculus's $r$ is exact over the
supplied coordinates. The executable consumer reads the coordinates as exact
rationals — a JSON float (a JSON number carrying a fraction or an exponent)
at the exact value of the binary64 the parser produces, a decimal string at
its exact decimal value — and compares **squared** diameters, using
$\lVert p-q\rVert\le c\iff\lVert p-q\rVert^2\le c^2$ for two coordinates
$p$, $q$ of one support and a cap $c\ge 0$, so a cap verdict (and the
$r'\le 2r$ check) never depends on a square root or a tolerance. A decimal
string is a repo-local input form: the challenge export emits coordinates as
JSON numbers, and a decimal string is not emitted. A decimal radius is a
rounding of the square root of the exact maximum squared diameter, computed
by integer arithmetic, and is **not** the quantity the cap comparison uses:
the exported qLDPC claim rounds *up* (an upper bound on the real value),
while trace and report displays round to nearest.

### 2d.2 How the layout travels

Every transition either preserves the qubit namespace, removes one qubit from
it, or forms a disjoint union; and the state keeps the parent's qubit labels.
So the child's layout is the parent's layout read at the child's qubits, and
the radius is recomputed against the child's own display:

| Transition | The child's layout | The child's radius | Direction |
| --- | --- | --- | --- |
| `C-SKIP` | $\lambda$ | $r'=r$ | unchanged |
| `C-DELETE-CHECK` | $\lambda$ | $r'=\max\{\mathrm{diam}_\lambda(s):s\in\mathit{rows}'\}$ | $\le r$ |
| `C-ADD-CHECK` | $\lambda$ | $r'=\max(r,\mathrm{diam}_\lambda(r_{\rm new}))$ | $\ge r$ |
| `E-GRAFT` at $q$ | $\lambda\vert_{Q\setminus\{q\}}$ | $r'=\max\{\mathrm{diam}_{\lambda'}(s):s\in\mathit{rows}'\}$, and $r'\le 2r$ | **may increase** |
| `C-DIRECT-SUM` | the two summand layouts, blockwise up to isometry (not their set-theoretic union, which need not be a layout) | $r=\max(r_A,r_B)$ | maximum of the summands |

The graft's bound is a **factor of two, not a non-increase**. A graft row is
$a_i\oplus a_{i+1}$ restricted to $Q'$, with $q$ in both rows; two points of
the new row lying in different parts are at distance at most
$\mathrm{diam}(a_i)+\mathrm{diam}(a_{i+1})$, and the opposite-sector rows are
shortened at $q$, which cannot increase a diameter. The derivation is at
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4.21 (interaction-radius transport). The naive claim
that the graft preserves the radius is **false**, and a survey over the
challenge's board entries records grafts that increase the radius
( §5;
see the survey report for counts).

### 2d.3 The honesty conditions

A layout is **honest** when at most $\rho$ qubits share a site and distinct
sites are at least $1$ apart. Honesty is a property of the layout alone, not
of the check set. It is inherited unchanged by `C-SKIP`, `C-DELETE-CHECK` and
`C-ADD-CHECK`, and it is **preserved by `E-GRAFT`**: removing a qubit from a
site can only lower that site's occupancy, and removing a site from the point
set can only raise the minimum distance between distinct sites. A direct sum
does **not** preserve honesty automatically — merging two layouts can place
two qubits on one site — so the direct-sum cell requires a merged layout that
is honest.

### 2d.4 The locality class is a verdict, not a property

The qLDPC challenge derives a locality class from the radius against fixed
caps. Those caps are the challenge's constants, not the calculus's, so **the
class is not a calculus property**: it is a consumer-side verdict, computed
from the transported radius and a consumer-supplied cap. The caps are recorded
as consumer configuration in [`machine/consumer.json`](../machine/consumer.json).

The classes **nest by radius, not by layer count**: a code qualifies for every
class whose layer cap and radius cap it satisfies, and the consumer assigns the
tightest. A one-layer code of radius $4.1$ fails the single-layer radius cap
$4.0$ but satisfies the bilayer caps (two layers, radius $7.0$), so it is
`local-2d-bilayer`.

The class is assigned only when the layout is **planar** (all coordinates in
a 2D plane) and **honest** (§2d.3); otherwise the verdict is
`unrestricted`, since the caps are 2D-radius constants.

The consumer's class verdict is exact, while the challenge verifier
(an archived internal note at challenge commit 9d30c66a) compares a
floating-point `math.dist` radius against `cap + 1e-9`; a radius within
$10^{-9}$ above a cap can therefore be `in` for the challenge and `out` for
the consumer. The two are not the same verdict.

The class's transport needs no separate cell, because it follows from §2d.2:
deletion can only preserve or improve it, addition can only preserve or
degrade it, and the graft can degrade it — but only where the parent's radius
was within a factor of two of the cap, since $r'\le 2r$. Where the cap is at
least twice the parent's radius, the graft preserves the class outright.


## 2e. Seam certificate for `E-GLUE` (conditional, admitted 2026-10-23)

`E-GLUE` is not a calculus primitive or a priced construction move; it is a
candidate CSS extension ([`TAXONOMY.md`](TAXONOMY.md)). Its seam certificate is
admitted here as a **conditional** judgment, on the surface-code / planar scope,
with circuit-level preservation empirically verified only. No new calculus
primitive is added; the certificate is a judgment over factor codes and a seam.

| Seam condition | Verdict | Certified bound |
| --- | --- | --- |
| `w(c_A)=w(c_B)` (identical move words over `{U,D,L,R}^*`) | admissible | $H_1(Q)\cong\mathbb F_2$ and $d_Z(Q)=\min(d_A,d_B)$, realised by the embedded factor representative |
| otherwise | inadmissible | no certified bound; the check returns `inconclusive` |

The predicate is decidable in time linear in the grid size (move-word equality).
It is strictly stronger than matching per-layer crossing counts: equal crossing
counts can still differ in total length (different numbers of horizontal detour
edges), which would make the gluing ill-defined.

**No-go obstruction row.** Factor data plus connectivity is provably
insufficient to certify a general merge, so a flat-DEM check that sees only
factor data and connectivity **must return `inconclusive`** rather than a
verdict. The seam certificate above is the only licensed route, and it
requires the full move word, not a summary.

**Interval transformer (§2b `E-GLUE` row).** Under an admissible seam
certificate the Z-sector upper endpoint is the minimum of the two factors'
Z upper endpoints; in every sector and the full distance the lower endpoint
is the minimum of the two factors' lower endpoints (sound without a
certificate). The X and full upper endpoints are left to witnesses valid in
the child. This is the transformer whose soundness is derived at
`OPERATIONAL_SEMANTICS.md` §4.32.

Scope: monotone top-to-bottom seams only (surface code / planar). Perpendicular
seams, arbitrary removed plaquette checks, and circuit-level preservation are
out of scope or empirically verified only. No flat-DEM composition recognition
is claimed.

**Dated note.** The consumer refuses to execute
`E-GLUE` without an admissible seam certificate even though the lower
endpoints are sound without one; that refusal is consumer policy, not a
calculus gap, and the lower endpoints remain sound regardless.


## 2f. Admitted CSS-level extension cells (conditional, admitted 2026-10-23)

The following Gate 6 CSS-level extensions are admitted **as conditional cells**
under the scope decision recorded in `SCOPE.md`: they are in scope
as moves. Some rows carry structural facts with no consumer-supplied
hypothesis (namespace arithmetic, rank bookkeeping, sector exchange); others
are conditional on a hypothesis or refuse outright. Otherwise the
corresponding cell is `unavailable`/`not yet defined`. The non-CSS
extended-state layer (`X-SYMPLECTIC-DOUBLE`/`HALVE`) is **not** admitted by
this decision.

**Transitions.** Five of the six now have typed transitions
(`TERM_LANGUAGE.md` §2; `OPERATIONAL_SEMANTICS.md` §2, §4.26–§4.30):
`peel`, `puncture`, `extend`, `hadamard` (admitted for $T=Q$ only), and
`rebase`. `E-GLUE` has no unary grammar production — gluing is binary — but
its evaluator transition was admitted 2026-10-27
(`OPERATIONAL_SEMANTICS.md` §4.31), with the logical-witness prerequisite
(`TAXONOMY.md` §2.10) still unmet, so its index row stays `taxonomy-only`.
Sound admission is discharged under the stated hypotheses
(`OBL-GATE6-CSS-EXTENSIONS`, `OPERATIONAL_SEMANTICS.md` §4.32,
2026-10-28); the cells remain conditional on their hypotheses and `promoted`
remains a review disposition. The consumer's interval behavior for the six is
transcribed in §2b with the unsourced-transcription hazard in mind (each
rule's *source* is the named section, not this table alone).

| Move | Property | Carries when hypothesis supplied | Hypothesis (consumer-supplied) | Source | Status |
| --- | --- | --- | --- | --- | --- |
| `E-GLUE` | $d_Z$ | $d_Z(Q)=\min(d_A,d_B)$ for an admissible seam; lower endpoints are sound without a certificate (the glued code is the direct sum with seam checks added, so each sector distance is at least the factor minimum: §4.31) | full move word over `{U,D,L,R}^*` with `w(c_A)=w(c_B)` (§2e), **plus** Theorem 4 / claim 7.4 (*composition-distance*) as a hypothesis for the equality $d_Z(Q)=\min(d_A,d_B)$; lower endpoints are sound without it | seam certificate (§2e); Theorem 4 / claim 7.4 (*composition-distance* §6.1) as a **cell hypothesis**, not a theorem of §4.31 | conditional cell admitted; **evaluator transition admitted 2026-10-27** (§4.31); logical-witness prerequisite still open; equality is a cell hypothesis, not a carved-out obligation |
| `E-PUNCTURE` | $n$ | $n'=n-1$, exactly | **none** — the namespace arithmetic is the update itself | `OPERATIONAL_SEMANTICS.md` §2, §4.29 | transition defined; cell carried; sound admission discharged (§4.32), conditional on hypotheses |
| `E-PUNCTURE` | $k$ | $k'=k-1+t_X+t_Z$, exactly ($t_\tau$ = number of displayed $\tau$-rows containing $q$; §4.29) | **none** — the rank bookkeeping is derivable, not supplied | §2, §4.29 | transition defined; cell carried |
| `E-PUNCTURE` | $d$, $d_X$, $d_Z$ | *(not stated in this scope)* | *(no hypothesis exists for a price: hole-punch pricing is blocked on the D2 lower bound, — no cell, no fixture)* | §2, §4.29 | **nothing carries** (§4.29's unnamed-free-qubit increase: $d_X\;1\!\to\!2$); ledger resets |
| `E-PEEL` | $n$ | $n'=n-1$, exactly | **none** | §2, §4.28 | transition defined; cell carried |
| `E-PEEL` | $k$ | $k'=k$, exactly (§4.28's injectivity argument: the opposite sector's restriction never loses rank) | **none** — the rank bookkeeping is derivable, not supplied | §4.28 | transition defined; no price cell |
| `E-PEEL` | $d$,$d_X$,$d_Z$ | *(not stated in this scope)* | *(none stated)* | §2, §4.28 | **nothing carries**, by design: §4.28 derives $d_\tau'\ge d_\tau$ and $d_{\bar\tau}'\le d_{\bar\tau}$, and no cell carrying either is admitted; ledger resets |
| `E-EXTEND` (patch growth / breeding) | $n$, $k$ | $n'=n+|\Delta|$; $k'=k+|\Delta|-s_X-s_Z$, exactly | **none** — the row-count arithmetic is the update | §2, §4.30 | transition defined; cell carried |
| `E-EXTEND` (patch growth / breeding) | $d$,$d_X$,$d_Z$ | with $\Delta=\varnothing$: the §2a `C-ADD-CHECK` monotonicity in both sectors (lower endpoints carry; no sector's upper endpoint carries, since an added $X$ row can raise $d_Z$: §4.30); with $\Delta\neq\varnothing$: none | *(no hypothesis is needed for the $\Delta\neq\varnothing$ refusal — no formula is admitted)* | §2, §4.30 | no distance rule for the namespace-growing instance |
| `E-LOCAL-HADAMARD` | sector swap ($T=Q$) | exact: $d_X'=d_Z$, $d_Z'=d_X$, $d'=d$; $n,k,w$ unchanged | **none** — the $T=Q$ instance needs no consumer input | §2, §4.27 | transition defined; the general split-subset instance has **no** cell and no rule |
| `P-REBASE` | presentation | everything span-expressible carries exactly: $n,k,d_X,d_Z,d$ (spans unchanged); $w$/$r$/Tanner recomputed exactly over the child display | *(GL-ness of $M$ is a checked structural premise, not a trusted input; no hypothesis is needed)* | §2, §4.26 | transition defined; `OBL-REBASE-GENERATION` discharged §4.26 |

The cells above are **admission decisions plus their carried judgments**. A
distance judgment with no stated hypothesis is a **refusal**, not a gap: the
§2.8/§2.9 records demand the formulas state their hypotheses, and none of
these moves has a source-stated distance formula to reproduce. Sound admission is discharged under the stated hypotheses
(`OPERATIONAL_SEMANTICS.md` §4.32, 2026-10-28); the cells remain conditional
on their hypotheses, and `promoted` remains a review disposition.

**Instance reading (2026-10-28).** The extension cells above are among the
bespoke items S1 §7.3 leaves out of the generic core (the distance atoms, the
conditional price cells, the seam certificate, and the extension cells whose
transitions are new); `P-REBASE` and `E-GRAFT` are already recorded in §7.3 as
carrier-typing instances, not bespoke. Where interval behavior is stated for
these moves, it is cited through the move-monotonicity lemmas of S3 (§9.4)
only; no transformer of S2 (§8.3) is claimed for a move outside §8.3's scope.
No cell verdict, evidence label, or qualification changes.

## 3. What `unavailable` means, and why it is a position
`unavailable` is **withheld by design commitment**. It is not ignorance, not a gap
awaiting closure, and not a synonym for `false`.

Two review passes fixed the boundary and the artifacts respect it:

- **Review finding.** The `unavailable` row once covered deletion
 *distance*, which is true and derivable — $d'\le d$ follows from the two sector
 bounds by `MIN-ORDER` and `TRANSITIVITY`. The row was narrowed to **exact
 post-deletion distance values**, which are genuinely underivable.
- **Review finding.** `not_derivable` must be labelled for **one
 claim in a stated scope**, naming the rule system and the record date.

**Consequence, stated plainly:** the calculus will not be complete, and no
artifact may describe it as aiming at completeness in the MVP.

## 4. The `W13` half — absence of derivation as the witness

*Dispositioned 2026-10-11 (maintainer). Full analysis is recorded in the
review notes.*

The `W13` half — *"a claim referring to a deleted generator is not transported"* —
needs **no rule whose conclusion is a negative**. Transport is already a
derivability property: L3 `TRANSITIVITY` composes claims whose schemas compose,
and a claim referencing a deleted generator fails that schema condition, so **no
derivation closes**. That failure is the machine-checkable per-evaluation witness.

This is cheap because the MVP half already works this way: the positive half is
enforced by a schema condition that *fails to fire*, not by a rule that succeeds.
The `W13` case is the same mechanism observed in the negative direction.

**Three costs travel with it, and every artifact saying "the calculus refuses"
means the refutation, not the theorem:**

- It **re-reads D2.** Non-transport becomes a consequence of the logic's shape
 where D2 recorded it as a registry commitment. Weaker than reversing it, no
 field added — so **not** a release bump — but owed a dated note.
- It establishes *no derivation closes*, **not** *no derivation can close*. A
 later release adding a rule could close a gap today's refutation reports.
- **Decidability of the search is owed as an argument** for the instance.

Mechanized shape: `not_derivable_of_false` in
`lean/CodeCalculus/Transport.lean` is the per-evaluation witness, for the
slice's sentence language, which has no claim that refers to a generator; the
`W13` half itself therefore has no instance there, and each refutation is
relative to that inventory, per the second cost above.

## 5. Transport through sequences

`C-SEQUENCE` carries the positive half: a claim mentioning only invariant fields
composes, by L3 `TRANSITIVITY` plus a syntactic condition on schemas. The
schema-composition condition and its argument are recorded in
`spec/OPERATIONAL_SEMANTICS.md` §4.11 (`OBL-JUDGMENT-TRANSPORT`); the half is
**`proved`** (hand derivation, 2026-10-20), subject to that condition. It remains
a Gate 3 input. Mechanized 2026-10-27 as `Derives.weaken`,
`Derives.shift`, and the seam compositions of `lean/CodeCalculus/Transport.lean`;
the record is at `spec/OBLIGATIONS.md`, `OBL-JUDGMENT-TRANSPORT`.

Structural-fact persistence through sequences is likewise `open`.

## 7. Property signature and structural schemas (S1)

This section states no new rule and changes no cell; it gives the carry table of
§2 a typed signature and names the five structural schemas under which its cells
are instances.

### 7.1 The signature

A **property** is a record with five fields:

```text
Property :=
 { carrier : span | display | presentation | consumer | state
 , quantity : State → V -- derived, or an opaque atom
 , update : Primitive → State → State → V
 , transfer : claim schema -- the carry rule, if any
 , opacity : none | distance | certificate | price
 }
```

The `carrier` field is the load-bearing addition: the current table mixes
quantities at different levels without a formal type. `used` is **not** a
property at all — it is part of identity
([`STATE_MODEL.md`](STATE_MODEL.md) §2). Treating a display-level carry as if it
were span-level is the shape of the graft's spliced-sector error
([`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4.13, §4.20).

| Property | Carrier | Kind | Opacity |
| --- | --- | --- | --- |
| $n$ | span | derived from `Q` | none |
| $k$ | span | derived from rank | none |
| $w$ | display | derived (max weight) | none |
| $r$ | display | derived (max diameter) | none |
| $\kappa$ (Tanner components) | display | derived (finite traversal) | none |
| $d_X$, $d_Z$ | span | atomic | distance |
| $d$ | span | derived from the two atoms by `min` | distance |
| output well-formedness | state | predicate (I1–I5) | none |
| presentation data (ids, sectors) | presentation | data | none |
| ledger interval | consumer | abstract value | price |

The `opacity` field records whether the quantity is opaque (distance,
certificate, price) or not, so that distance atoms stay opaque by convention:
no rule or procedure computes a distance from the state
([`VOCABULARY.md`](VOCABULARY.md), *Opaque distance term*). A generic core
must not become a distance oracle by the back door; in the MVP this is
enforced by review rather than by the Lean type.

### 7.2 The five structural schemas

Each is a lemma about the existing L3, not a new rule. The table of §2 cites
them instead of re-arguing each cell.

1. **Derived transfer.** If $q$ is a function of the display and the
 primitive's update of the display is explicit, then $q'$ is the value of the
 updated display. Covers the $n$, $k$, $w$, $r$, and $\kappa$ rows, including
 the `C-SEQUENCE` and `C-DIRECT-SUM` rows.
2. **Monotonicity.** If $q$ is monotone in the display under an explicit order
 (inclusion for supports, max for $w$, max for $r$), the direction of the cell
 follows from the update.
3. **Frame.** A property that mentions only one summand of a direct sum carries
 across the other summand, provided the disjointness premises (and, for the
 addition clause, the allocation-compatibility mint premise of
 `OBL-FRAME-LAW`) hold. This is the frame law derived at
 `OPERATIONAL_SEMANTICS.md` §4.9 and the direct-sum block, stated once.
4. **Composition.** If each step's transfer is a relation of the right polarity
 (equality, or a one-sided bound of fixed direction), the sequence composes by
 the existing `TRANSITIVITY` and the order theory on
 $\mathbb{N}\cup\{+\infty\}$ (`OPERATIONAL_SEMANTICS.md` §4.11). This is the
 positive half of `OBL-JUDGMENT-TRANSPORT`, and what the single-polarity `C-SEQUENCE`
 distance chains are instances of; mixed delete/add chains stay `[open]`.
5. **Substitution.** Equality claims compose by replacing equal subterms; the
 equality half of composition.

### 7.3 What becomes an instance

| Cell or group | Instance of |
| --- | --- |
| `n`, `k` rows for all five primitives | derived transfer over `Q` and rank |
| `w`, `r`, $\kappa$ rows | derived transfer + monotonicity |
| `C-SEQUENCE` `n`, `k`, `w`, `r`, $\kappa$ | composition |
| `C-SEQUENCE` `d_X`, `d_Z`, `d` | composition on single-polarity chains only; mixed chains stay `[open]` |
| `C-DIRECT-SUM` all rows | frame + derived transfer |
| `C-SKIP` all rows | identity instance |
| `P-REBASE` span-expressible claims | carrier typing (span-level survives a span-preserving rebase) |
| `E-GRAFT` spliced-sector correction | carrier typing (a display-level carry was read as span-level) |
| well-formedness rows | predicate preservation, already proved for the MVP |

The genuinely bespoke items remain: the distance atoms' per-primitive
instantiations, the conditional price cells, the seam certificate, and the
extension cells whose transitions are new.

### 7.4 The `n`, `k`, `w`, `r`, and $\kappa$ rows as instances

Each of these five rows of §2 is, under the signature of §7.1, an instance of
the schemas of §7.2 rather than a fresh argument. The derived-transfer formula
and the schema cited are recorded here; the cell verdicts and evidence labels of
§2 are unchanged.

| Property | Carrier | Quantity | Update (per primitive) | Schema |
| --- | --- | --- | --- | --- |
| $n$ | span | $\lvert Q\rvert$ | $n'=n$ (skip/delete/add/sequence); $n=n_A+n_B$ (direct sum) | derived transfer |
| $k$ | span | $\lvert Q\rvert - \operatorname{rank}(\mathit{rows})$ | $k'=k$ (skip); $k'=k+1$ (delete); $k'=k-1$ (add); $k=k_A+k_B$ (direct sum); carries (sequence) | derived transfer |
| $w$ | display | $\max\{\mathrm{wt}(r):r\in\mathit{rows}\}$ | $w'=w$ (skip); $w=\max(w_A,w_B)$ (direct sum); $w'=\max\{\mathrm{wt}(r):r\in\mathit{rows}'\}$ (delete, $\le w$); $w'=\max(w,\mathrm{wt}(r_{\rm new}))$ (add); carries (sequence) | derived transfer + monotonicity |
| $r$ | display | $\max\{\mathrm{diam}_\lambda(s):s\in\mathit{rows}\}$ | $r'=r$ (skip); $r=\max(r_A,r_B)$ (direct sum, conditional on honest merged layout); $r'=\max\{\mathrm{diam}_\lambda(s):s\in\mathit{rows}'\}$ (delete, $\le r$); $r'=\max(r,\mathrm{diam}_\lambda(r_{\rm new}))$ (add); carries by composition (sequence) | derived transfer + monotonicity |
| $\kappa$ | display | $\kappa(C)$, the component count of the displayed-row Tanner graph $\Gamma(C)$ | $\kappa'=\kappa$ (skip); $\kappa=\kappa_A+\kappa_B$ (direct sum); $\kappa'\ge\kappa$, recomputed (delete); $\kappa'\le\kappa$ (add); composition (sequence) | derived transfer + monotonicity |

The distance atoms ($d_X$, $d_Z$, $d$) are **not** in this list: they are
atomic, span-level, and opaque (opacity `distance`); their per-primitive
instantiations remain bespoke, as recorded in §7.3.

**Hand-derivation check.** No rule, premise, or cell of §2 changed; §7 only
re-presents existing rows. The hand derivations of
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4.7 (well-formedness),
§4.8 (determinism, associativity, and the direct-sum laws), and §4.9
(partial inverses and the frame law) therefore still close unchanged.



## 8. Ledger as an abstract interpretation (S2)

This section states no new rule, admits no cell, and changes no claim status; it
reconstructs the interval ledger of §2b as an abstract domain so that
`OBL-PRICED-INTERVAL-SOUNDNESS` reads as a schema with the §4.13 bullets as
instances.

### 8.1 The two domains

**Concrete domain.** For a single distance, the concrete domain is
$D=\mathbb{N}\cup\{+\infty\}$, ordered by the usual $\le$ (the concrete
order on exact distances). For the full distance together with its two sectors,
the concrete domain is the product $D_X\times D_Z$ with the componentwise
order, and the full distance is the meet $d=\min(d_X,d_Z)$.

**Abstract domain.** The abstract domain for one distance is the set of
intervals
\[
\mathcal{I}=\{[L,U]:L,U\in D,\;L\le U\},
\]
with bottom-ish exact values $[x,x]$ and top $[0,+\infty]$. The abstract
domain for a state is the product of the sector intervals together with the
full-distance interval, subject to the reduced-product constraint of §8.8.

### 8.2 Concretization and the two orders

**Concretization.** $\gamma([L,U])=\{d\in D:L\le d\le U\}$. An interval is
sound for an exact distance $d$ iff $d\in\gamma([L,U])$.

**Precision order (abstract).** Write $a\sqsubseteq b$ (read "$a$ is at least
as precise as $b$") iff $\gamma(a)\subseteq\gamma(b)$, equivalently
$L_b\le L_a$ and $U_a\le U_b$. Smaller interval = more precise. The top of
this order is $[0,+\infty]$; it has no bottom (singletons $[x,x]$ are
pairwise incomparable minimal elements, and the meet of disjoint intervals is
not in the domain).

**Concrete order.** The concrete order is $\le$ on $D$. It is the order the
endpoint arithmetic of §2b and §4.11 uses; it is not the precision order, and
the two must not be interchanged. A theorem is unsound if it states
monotonicity in $\le$ where it means $\sqsubseteq$, or soundness in
$\sqsubseteq$ where it means $\le$.

### 8.3 Transformers

For each primitive $m$ there is one transformer $F_m:\mathcal{I}\to\mathcal{I}$
(more generally, one over the product domain) given exactly by the endpoint
rows of §2b:

- $F_{\mathrm{skip}}$: identity.
- $F_{\mathrm{add}}$: lower endpoint carried (or raised to $d+1$ under the
 strict-improvement hypothesis, and sector lower endpoints raised to $w_\sigma$
 under the sector-aware gauging row); upper endpoint reset to $+\infty$, then
 tightened by child-valid witnesses.
- $F_{\mathrm{delete}}^{\mathrm{unpriced}}$: lower endpoint reset to $0$;
 upper endpoint carried.
- $F_{\mathrm{delete}}^{\mathrm{priced}}(p)$ with
 $p=\min(w_{\mathrm{del}},w_{\mathrm{exp}})$: both endpoints mapped by
 $x\mapsto\min(x,p)$.
- $F_{\mathrm{graft}}$: sector-wise per the corrected rules of §2b and
 §4.13 (spliced sector carries its lower endpoint and drops its upper;
 non-spliced sector carries its upper and resets its lower; full distance
 resets both endpoints unless priced; sector upper endpoints remain sound
 upper bounds for $d$).
- $F_{\mathrm{directsum}}$: corresponding endpoints combined by `min`.
- $F_{\mathrm{sequence}}(a,b)=F_b\circ F_a$.

An exact-value cell marked `unavailable` is not the absence of every
transformer: a sound, non-singleton (bound) transformer may still be supplied
for that (primitive, property) pair, as in the half-line rows of §2b. What is
withheld is the exact-value claim — the transformer's concretization is not a
singleton. `unavailable` is therefore a statement about precision, not a missing
transformer and not a value the transformer may return.

### 8.4 Soundness and monotonicity schema

For a primitive $m$ and a state transition $C\xrightarrow{m}C'$:

1. **Soundness.** If $d(C)\in\gamma(a)$ and every supplied hypothesis for $m$
 is true, then $d(C')\in\gamma(F_m(a))$.
2. **Monotonicity.** $a\sqsubseteq b\;\Rightarrow\;F_m(a)\sqsubseteq F_m(b)$.

The §4.13 induction is the instance of (1) for the interval transformers of
§2b: each bullet verifies soundness for one $F_m$; the `C-SEQUENCE` step is
the composition theorem below, and the base case is the hypothesis on the
inputs. The §4.13 derivation is therefore re-read as an instance of this
schema; no bullet changes status.

Monotonicity is what licenses tightening an input interval before applying a
transformer: a tighter input yields a tighter output. It is stated in the
precision order $\sqsubseteq$, never in $\le$.

### 8.5 Composition theorem

If $F$ and $G$ are sound and monotone, then $G\circ F$ is sound and monotone.
Consequently, for a sequence of transitions, the composite transformer is
sound whenever each step's transformer is. This is the positive half of
`OBL-JUDGMENT-TRANSPORT` at the interval level (already mechanized as
`priced_interval_soundness_seq`); it settles interval transport, not the
`[open]` exact-quantity carry laws for mixed delete/add chains, which remain
governed by §7's qualification. The equality half is substitution (S1 schema 5).

### 8.6 Restating `OBL-PRICED-INTERVAL-SOUNDNESS`

`OBL-PRICED-INTERVAL-SOUNDNESS` is the schema of §8.4 instantiated to the
transformers of §8.3, with the per-primitive soundness bullets of §4.13 as its
instances. Its hypotheses (price truth, witness validity, coverage guard,
strict-improvement enumeration) are exactly the hypotheses under which the
corresponding $F_m$ is sound. No obligation status changes: the obligation
remains `proved` as a hand derivation, now read as an instance of a schema
rather than as an ad hoc induction.

### 8.7 Order discipline

Each theorem names the order it uses, and a proof that mixes them is invalid:

| Result | Order used | Why |
| --- | --- | --- |
| Soundness (§8.4 (1)) | concrete $\le$ inside $\gamma$ | membership, not precision |
| Monotonicity (§8.4 (2)) | precision $\sqsubseteq$ | tighter input $\Rightarrow$ tighter output |
| Endpoint arithmetic (§2b, §4.11) | concrete $\le$ on $D$ | $\min$, $\max$, non-increase |
| Composition (§8.5) | both: precision for $F,G$, concrete for endpoints | the two are composed, not identified |
| `certify`/`prune` (§2b) | concrete $\le$ against target $T$ | $L\ge T$, $U<T$ |

### 8.8 Reduced product for the disjunctive half

The full distance is not an independent quantity: $d=\min(d_X,d_Z)$. Treating
its interval as independent of the sector intervals admits spurious states, so
the abstract domain is the reduced product of the sector interval domains with
the full-distance interval domain, quotiented by the meet constraints. The
closure is:

- raise each sector lower endpoint: $L_\sigma \mapsto \max(L_\sigma, L_d)$;
- raise the full-distance lower endpoint:
 $L_d \mapsto \max(L_d, \min(L_X,L_Z))$;
- lower the full-distance upper endpoint:
 $U_d \mapsto \min(U_d, U_X, U_Z)$;

and nothing lowers a sector upper endpoint, since $\min(d_X,d_Z)\le U_d$ only
says that one of the two sectors is at most $U_d$. A closed element therefore
has $L_d=\min(L_X,L_Z)$ and $U_d\le \min(U_X,U_Z)$.

The unsatisfiable shapes are $L_d>\min(U_X,U_Z)$ and
$U_d<\min(L_X,L_Z)$; the shapes $L_d>\min(L_X,L_Z)$ and
$U_d<\min(U_X,U_Z)$ are satisfiable and are not the defect.

The full-distance interval is thus not a third independent transformer: it is
the meet of the sector intervals. But a reduced product of three intervals is
still three intervals; it cannot represent the disjunctive half
$d_X\le U \lor d_Z\le U$ that §3.2 says
needs a relational or disjunctive component. Whether that half is handled
inside the interval domain or left as a ledger design decision is a design
question, not a theorem of this domain. The Lean meet lemmas
`ExtNat.min_le_left` and `ExtNat.min_le_right` state only
$\min(a,b)\le a$ and $\min(a,b)\le b$ over `ExtNat`; they impose no product
constraint.

### 8.9 Bounded unfolding and oracle refinement

The calculus itself has no iteration: `C-SEQUENCE` is finite composition. The
consumer's `re-measure` loop is an iteration over the abstract domain, and its
soundness is the iterated soundness of `compose_sound`:

- **Bounded unfolding.** If each of $k$ steps has a sound, monotone
 transformer, then the composition of those $k$ transformers is sound. The
 code's `plan_chain` (`machine/planner.py`) is depth-limited (default 2), so
 the loop is a bounded unfolding, not a fixpoint computation. No widening or
 narrowing operator is required for soundness; termination is by the depth
 bound.
- **Refinement.** A witness or supplied price refines an interval by tightening
 an endpoint (a $\sqsubseteq$-monotone map); refinement after a sound step
 keeps the result sound. This is `compose_sound` with a refinement
 transformer.
- **Oracle refinement.** A supplied price or witness is an oracle that refines
 the interval by $\min$ with the price or by tightening an upper endpoint.
 It is monotone and sound only under its stated hypothesis; the consumer
 records the source reference and does not verify the hypothesis.
- **Widening.** If a consumer extrapolates beyond the evidence set, it must
 coarsen (move up in $\sqsubseteq$); coarsening a sound interval stays
 sound. This is soundness restated, not a convergence operator, and the
 domain has infinite chains, so termination is an evidence-set/depth property.

A `re-measure` result is the signal that the current interval is too coarse to
decide the target; it is not a failure of soundness.

### 8.10 `unavailable` is not top

Top $[0,+\infty]$ is a value: it is the least precise sound interval, and a
transformer may legitimately emit it (for example, when no child-valid
witness survives a graft). `unavailable` is not a value at all: it marks a
cell in which the exact-value claim is withheld even though a sound,
non-singleton (bound) transformer may exist for that (primitive, property)
pair. A cell marked `unavailable` in the carry table therefore does not mean
"the consumer emits top"; it means "no exact value is licensed by this rule;
any interval the consumer does emit comes from a different, available rule
(for example, a carried bound or a reset to $[0,+\infty]$ from a sound
transformer elsewhere in the table)". Conflating the two would make the
calculus appear to claim precision it does not have.
---

## 9. The consumer refinement preorder (S3)

*Non-normative reorganization, 2026-10-27. This section states no new rule,
admits no cell, and changes no claim status. It supplies the missing interface
between the ledger and the consumer's target: a preorder on ledger states under
which the `certify`/`prune` verdicts of §2b are monotone, and under which the
transformers of §8.3 are monotone. Authority:
 §2.4 (form (a)) and §4 (S3); `spec/`
still wins on any disagreement. Form (b) (a calculus-level preorder on states,
which would mint a new judgment and touch the assertion-language axis of
[`VERSIONING.md`](VERSIONING.md) §4) is out of scope until form (a) earns its
keep.*

### 9.1 The preorder

Fix a **property profile** $P$: the list of axes the consumer exports and
compares. For the verdicts of §2b the profile is $P=\{d\}$ (the full-distance
interval alone); for the planner's domination pruning (see
[`machine/planner.py`](../machine/planner.py)) it extends to
$\{d, d_X, d_Z\}$, $k$, $n$, and the verdict class. Each axis carries its own
order, and the ledger preorder is the conjunction over $P$.

**Definition (consumer refinement preorder, form (a)).** For ledger states $A$,
$B$ and a profile $P$, write $A\sqsubseteq_P B$ ("$A$ refines $B$" / "$A$ is at
least as informative as $B$, relative to $P$") iff on every axis in $P$, $A$'s
exported value is at least as informative as $B$'s:

- **Distance axes** ($d$, $d_X$, $d_Z$): the interval precision order of §8.2,
 lifted componentwise to endpoints,
 \[
 L_B\le L_A\quad\text{and}\quad U_A\le U_B.
 \]
 Write $\sqsubseteq^{\mathrm{low}}$ for the lower half ($L_B\le L_A$, "$A$
 certifies at least as much as $B$") and $\sqsubseteq^{\mathrm{up}}$ for the
 upper half ($U_A\le U_B$, "$A$ prunes at least as much as $B$"). The combined
 relation is $\sqsubseteq\;=\;\sqsubseteq^{\mathrm{low}}\cap\sqsubseteq^{\mathrm{up}}$.
- **$k$ and $n$**: the orders the planner scores them with — larger $k$ is more
 informative, smaller $n$ is more informative.
- **Verdict class** (when included in $P$): $\texttt{certify}\succeq
 \texttt{re-measure}\succeq\texttt{prune}$.

For $P=\{d\}$ (the profile the verdicts of §2b actually use), write $\sqsubseteq$
for $\sqsubseteq_{\{d\}}$. The relation is a **preorder**: reflexive and
transitive (reflexivity and transitivity are componentwise from the underlying
orders; §8.2's precision order is already a partial order on intervals, so
$\sqsubseteq_P$ is a partial order whenever each axis order is).

**Reading.** $A\sqsubseteq B$ says "$A$ is at least as useful to the consumer as
$B$". It is a statement about the **ledger**, not about the underlying state: two
ledgers for the same state can be $\sqsubseteq$-incomparable (one has the better
lower bound, the other the better upper bound), and two ledgers for different
states are related whenever their exported facts line up. No new judgment is
minted: this is not $C\sqsubseteq C'$ on states, only $A\sqsubseteq B$ on the
consumer's ledger.

### 9.2 Verdict monotonicity

The verdicts of §2b are monotone under $\sqsubseteq$, and this is the property
the consumer uses when it replaces a ledger with a more informative one.

**Lemma (verdict monotonicity).** Let $A\sqsubseteq B$ and let $t$ be a target.

1. If $B$ returns `certify` on $t$, so does $A$.
2. If $B$ returns `prune` on $t$, so does $A$.

*Proof.* `certify` reads $L_d\ge t$; from $L_B\le L_A$ and $L_B\ge t$ we get
$L_A\ge t$. `prune` reads finite $U_d<t$; from $U_A\le U_B$, finite $U_B<t$
gives finite $U_A<t$. Both use the respective half of $\sqsubseteq$; the two
halves are not interchangeable, which is the ledger-level counterpart of §8.7's
order discipline. $\square$

Equivalently: `certify(t)` and `prune(t)` are each **downward-closed** under
$\sqsubseteq$ (going more informative preserves them), and `re-measure(t)` is
their complement, hence **upward-closed**. Refinement can move a target from
`re-measure` to either of the other two verdicts; it can never move a `certify`
or a `prune` to anything else. This is the sense in which `re-measure` is "the
interval is too coarse to decide" (§8.9) and not a soundness failure: the
preorder says a refinement can only help.

### 9.3 Reference ledgers and the verdict derivation

The verdicts can be read off the preorder alone. For a target $t$ define two
**reference ledgers** (full-distance projection only):

- $\mathrm{cert}_t = [t, +\infty]$ — the least informative ledger that certifies
 $t$; any ledger with $L\ge t$ refines it.
- $\mathrm{prune}_t = [0, t-1]$ (for $t\ge 1$) — the least informative ledger
 that prunes $t$; any ledger with finite $U<t$ refines it.

**Lemma (verdict derivation).** For a full-distance ledger $A$ and a target $t$:

\[
A\ \texttt{certifies}\ t \iff A\sqsubseteq\mathrm{cert}_t,
\qquad
A\ \texttt{prunes}\ t \iff A\sqsubseteq\mathrm{prune}_t\quad(t\ge 1).
\]

*Proof.* $A\sqsubseteq\mathrm{cert}_t$ is $t\le L_A\wedge U_A\le+\infty$, i.e.
$L_A\ge t$. $A\sqsubseteq\mathrm{prune}_t$ is $0\le L_A\wedge U_A\le t-1$, i.e.
finite $U_A<t$. Both are the §2b decision rule read as a preorder comparison.
$\square$

So `certify(t)` is the principal down-set generated by $\mathrm{cert}_t$, and
`prune(t)` is the principal down-set generated by $\mathrm{prune}_t$. The two
reference ledgers are the canonical certificates the judgment layer hands to the
consumer; the §2b endpoint tests $L_d\ge t$, $U_d<t$ are the derived
characterization. This is the "certify/prune verdicts are derivable from the
preorder plus the carry table" half of the slice's done-when: the preorder
supplies the order, the carry table (§2b) supplies the reference ledgers and the
transformers below.

### 9.4 Move-monotonicity lemmas

The transformers of §8.3 lift to the product domain componentwise (each axis
gets its own transformer; the reduced-product constraint of §8.8 is preserved
because each component is). The moves the consumer actually performs are
monotone in $\sqsubseteq$, which is what licenses carrying a bound across a
move.

**Lemma (move-monotonicity).** For each primitive $m$ and profile $P$,
$A\sqsubseteq_P B\Rightarrow F_m(A)\sqsubseteq_P F_m(B)$. Concretely, for each
axis of $P$:

| Move | Per-axis monotonicity | Source in the carry table |
| --- | --- | --- |
| `C-SKIP` | identity is monotone | §2b `C-SKIP` row (unchanged) |
| `C-ADD-CHECK` | $x\mapsto\min(x,\cdot)$ is monotone in $\sqsubseteq$; the carried lower bound is monotone in $\sqsubseteq^{\mathrm{low}}$ | §2b `C-ADD-CHECK` row |
| `C-DELETE-CHECK` (unpriced) | lower reset to $0$ is a constant (monotone); upper carry is monotone in $\sqsubseteq^{\mathrm{up}}$ | §2b `C-DELETE-CHECK` row |
| `C-DELETE-CHECK` (priced, $p=\min(w_{\mathrm{del}},w_{\mathrm{exp}})$) | $x\mapsto\min(x,p)$ is monotone in $\sqsubseteq$ | §2b price paragraph |
| `E-GRAFT` | per-sector: splice carries lower (monotone in $\sqsubseteq^{\mathrm{low}}$), non-splice carries upper (monotone in $\sqsubseteq^{\mathrm{up}}$), full distance resets unless priced (monotone via the $x\mapsto\min(x,p)$ map) | §2b `E-GRAFT` row, §4.13 |
| `P-REBASE` | identity is monotone | §2b `P-REBASE` row (unchanged) |
| `E-LOCAL-HADAMARD` ($T=Q$) | the swap $X\leftrightarrow Z$ is monotone | §2b `E-LOCAL-HADAMARD` row |
| `E-PEEL`, `E-PUNCTURE` | lower reset to $0$ is constant (monotone); upper endpoints from child-valid witnesses are monotone in $\sqsubseteq^{\mathrm{up}}$ | §2b `E-PEEL`/`E-PUNCTURE` rows |
| `E-EXTEND` | $\Delta=\varnothing$: lower carry is monotone in $\sqsubseteq^{\mathrm{low}}$, upper rebuild is monotone in $\sqsubseteq^{\mathrm{up}}$; $\Delta\ne\varnothing$: lower reset to $0$ is constant, upper endpoints from child-valid witnesses are monotone in $\sqsubseteq^{\mathrm{up}}$ | §2b `E-EXTEND` row |
| `E-GLUE` | lower endpoints: $\min$ of the two factor lowers is monotone in $\sqsubseteq^{\mathrm{low}}$; Z upper endpoint: $\min$ of the two factor Z uppers is monotone in $\sqsubseteq^{\mathrm{up}}$ under an admissible certificate; X and full upper endpoints from child-valid witnesses are monotone in $\sqsubseteq^{\mathrm{up}}$ | §2b `E-GLUE` row, §2e |
| `C-DIRECT-SUM` | `min` on endpoints is monotone in $\sqsubseteq$ | §2b `C-DIRECT-SUM` row |
| `C-SEQUENCE` | composition of monotone maps is monotone (S2 §8.5) | §5, §4.11 |

Two consequences the plan calls out as becoming "special cases rather than
bespoke cells":

- **Distance non-increase** ($d'\le d$ under unpriced deletion) is the
 $\sqsubseteq^{\mathrm{up}}$ half of the `C-DELETE-CHECK` row: the transformer
 maps the upper endpoint by $U\mapsto U$, and the resulting upper bound is the
 parent's. No separate claim is needed beyond the row.
- **The direct-sum law** ($d=\min(d^A,d^B)$) is the $\sqsubseteq$ statement that
 `min` on endpoints is the *best abstraction* of the concrete meet in the
 precision order: $[\min(L_A,L_B),\min(U_A,U_B)]$ is the tightest interval
 containing $\min(d^A,d^B)$ whenever $d^A\in\gamma([L_A,U_A])$ and
 $d^B\in\gamma([L_B,U_B])$. The §2 remark that `C-DIRECT-SUM` is also
 *terminal* — no move reconnects a direct sum, because the state it produces is
 a disjoint union — is a fact about move applicability, not about $\sqsubseteq$,
 and is not subsumed by the preorder.

### 9.5 Why this is a derivation, and what it does not do

The derivation is: the carry table (§2b) gives the transformers and the
reference ledgers, and the preorder (§9.1) gives the order the verdicts are
monotone in. The verdicts of §2b are then *re-derived* as the principal
down-sets of the reference ledgers (§9.3), and the moves are shown monotone
(§9.4). No consumer behavior changes: `machine/priced_calculus.py`'s
`decide` returns `certify` / `prune` / `re-measure` exactly as before, and no
transformer is rewritten. What changes is that the verdicts now sit inside an
order, so a consumer may replace a ledger with a $\sqsubseteq$-smaller one (a
more informative one) without changing any verdict it has already reached.

It does **not** mint a new judgment: $\sqsubseteq$ is a relation on ledgers, not
on states. Form (b) (a calculus-level preorder $C\sqsubseteq C'$ on states) is
deferred; if it is ever admitted, it touches the assertion-language axis of
[`VERSIONING.md`](VERSIONING.md) §4 and would be a release event. It does not
close any obligation; the `proved` / `conditional` / `open` labels of §2 are
unchanged, and `OBL-PRICED-INTERVAL-SOUNDNESS`'s status is untouched.

### 9.6 Lean

[`lean/CodeCalculus/Refinement.lean`](../lean/CodeCalculus/Refinement.lean)
states the preorder, the verdict, and the two monotonicity lemmas, building on
S2's `Interval.lean` (`ExtNat`, `AbsInterval`, `gamma`, `preciseLe`). The Lean
development is a transcription aid, not a proof assistant result; it does not
establish soundness, and no cell's evidence status depends on it.

---

## 6. What this document does not do

It does not claim any cell is established by a proof assistant — none is. The
`proved` tags are evidence statuses meaning *a derivation is in this repository*;
they are not `promoted`, which is a human-owned review disposition
(`AUTHORITY.md` §B1–§B2).

It does not admit a claim into the calculus. Admission is the schema rule of
[`CLAIMS.md`](CLAIMS.md), and its conformance-contract
half (****) is implemented — the
structured premise fields are wired through `machine/fixtures/mvp_fixtures.json`
and checked by `machine/fixture_conformance.py`. The remaining mechanized
judgment-layer work is tracked separately, not by .

The three obligations added for (graft transition, interval transport,
and price-input trust boundary) are discharged by hand derivation (§4.12,
§4.13, §4.14). Remaining open obligations are tracked in
[`OBLIGATIONS.md`](OBLIGATIONS.md).

---
