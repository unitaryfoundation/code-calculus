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

| Property | `C-SKIP` | `C-DIRECT-SUM` | `C-DELETE-CHECK` | `C-ADD-CHECK` | `C-SEQUENCE` | Instance of |
| --- | --- | --- | --- | --- | --- | --- |
| $n$ | carries, $n'=n$ `[proved]` | carries, $n=n_A+n_B$ `[proved]` | carries, $n'=n$ `[proved]` | carries, $n'=n$ `[proved]` | carries `[proved]` | derived transfer (§7.2.1); monotone (§9.4) |
| $k$ | carries, $k'=k$ `[proved]` | carries, $k=k_A+k_B$ `[proved]` | carries, $k'=k+1$ `[proved]` | carries, $k'=k-1$ `[proved]` | carries `[proved]` | derived transfer (§7.2.1); monotone (§9.4) |
| $w$ (max stabilizer weight) | carries, $w'=w$ `[proved]` | carries, $w=\max(w_A,w_B)$ `[proved]` | carries, $w'=\max\{\mathrm{wt}(r):r\in\mathit{rows}'\}$ `[proved]` (exact; $\le w$) | carries, $w'=\max(w,\mathrm{wt}(r))$ `[proved]` | carries `[proved]` | derived transfer + monotonicity (§7.2.1–2); monotone (§9.4) |
| Tanner connectivity (displayed rows) | carries, unchanged `[proved]` (§4.22) | always decreases: the direct sum is a disjoint union, so the graph is disconnected; the child certifies a disconnected code, which is why the challenge's `tanner_connected` hard gate rejects it `[proved]` (§4.22) | can decrease: a deleted check may be a cut vertex `[proved]` (§4.22) | cannot decrease: a new check adds a node and edges `[proved]` (§4.22) | carries by composition `[proved]` (§4.22) | monotonicity (§7.2.2); monotone (§9.4); §4.22 |
| $r$ (interaction radius, relative to a layout) | carries, $r'=r$ `[proved]` | carries, $r=\max(r_A,r_B)$ `[proved]` (conditional on an honest merged layout; §2d.3) | carries, $r'=\max\{\mathrm{diam}_\lambda(s):s\in\mathit{rows}'\}$ `[proved]` (exact; $\le r$) | carries, $r'=\max(r,\mathrm{diam}_\lambda(r_{\rm new}))$ `[proved]` | carries by composition `[proved]` | derived transfer + monotonicity (§7.2.1–2); monotone (§9.4); §2d; one layout cell per transition in §2d.5 |
| $d_X$ | carries, $d_X'=d_X$ `[proved]` | carries, $d_X=\min(d_X^A,d_X^B)$ `[proved]` | carries **as a bound only**: $d_X'\le d_X$ `[proved]`; exact value **`unavailable`** unpriced, **`conditional`** on the matching sector deletion price (§2a) | lower bound `[proved]`; exact value `open` | single-polarity chains and interval transport carry by composition `[proved]` (§4.11, §4.13, §8.5; conditional on step prices); mixed opposite-polarity exact-quantity chains `open` | atomic opaque (§7.1, opacity `distance`); transformers (§8.3) + soundness (§8.4); precision (§8.2); refinement (§9.1); §4.13; §7.3 (C-SEQUENCE: composition on single-polarity chains only) |
| $d_Z$ | carries, $d_Z'=d_Z$ `[proved]` | carries, $d_Z=\min(d_Z^A,d_Z^B)$ `[proved]` | carries as a bound only: $d_Z'\le d_Z$ `[proved]`; exact value **`unavailable`** unpriced, **`conditional`** on the matching sector deletion price (§2a) | as $d_X$ | single-polarity chains and interval transport carry by composition `[proved]` (§4.11, §4.13, §8.5; conditional on step prices); mixed opposite-polarity exact-quantity chains `open` | atomic opaque (§7.1, opacity `distance`); transformers (§8.3) + soundness (§8.4); precision (§8.2); refinement (§9.1); §4.13; §7.3 (C-SEQUENCE: composition on single-polarity chains only) |
| $d$ | carries, $d'=d$ `[proved]` | carries, $d=\min(d^A,d^B)$ `[proved]` | carries **as a bound only**: $d'\le d$ `[proved]`; exact value **`unavailable`** unless $w_{\mathrm{del}},w_{\mathrm{exp}}$ are supplied, in which case $d'=\min(d,w_{\mathrm{del}},w_{\mathrm{exp}})$ `[conditional]` | lower bound `[proved]`; exact value `open`; strict improvement `[conditional]` | single-polarity chains and interval transport carry by composition `[proved]` (§4.11, §4.13, §8.5; conditional on step prices); mixed opposite-polarity exact-quantity chains `open` | derived from the two atoms by `min` (§7.1); reduced product (§8.8); precision (§8.2); refinement (§9.1); §4.13/§4.19; §7.3 (C-SEQUENCE: composition on single-polarity chains only) |
| $\mathsf{preserves}_U$ (codespace preservation of a commuting Pauli-rotation gate $U$, CSS display; §2h) | carries `[proved]` (§4.37) | carries when $U$ is supported on one summand `[proved]` (§4.37) | does not carry `[false]` (counterexample §4.37; the child's own Lemma 7 test over its remaining rows decides it at every rational angle; at $\pi/4$ this is Lemma 3) | adding row $s$: carries iff $\Phi_{J(s)}(l)\in\pi\mathbb{Z}$ for every sign pattern $l\in\Lambda(\mathcal{S}(C'),J(s))$ `[proved]` (Corollary 7.1, one test at $s$, decided for rational angles $\theta_j\in\pi\mathbb{Q}$ by at most $2^{\lvert J(s)\rvert}$ sign patterns and membership tests, polynomial in the display for a fixed number of generators; `not yet defined` as a decision for other angles); in particular at every angle when every generator commutes with $s$, and at all angles $\pi/4$ iff $V_s\in\mathcal{S}(C')$ (§4.37) | carries by composition of the step cells `[proved]` (§4.37) | predicate preservation + frame (§7.2.3–4); carrier `span` (§7.1); §2h, §4.37 |
| $\mathsf{preserves}_U(\cdot\mid F)$ (frame-sector preservation; §2h Row C) | carries `[proved]` | carries when $U$ is supported on one summand, frame $F_1\oplus F_2$ `[proved]` | does not carry `[false]` (counterexample §4.37) | when the transported frame $F'$ is consistent and $\mathcal{S}_F(C)\subseteq\mathcal{S}_{F'}(C')$: carries iff $\Phi_{J(s)}(l)\in\pi\mathbb{Z}$ for every $l\in\Lambda(\mathcal{S}_{F'}(C'),J(s))$, the source's eigenvalue condition when $F'$ resolves $J(s)$ `[proved]` (decided for rational angles $\theta_j\in\pi\mathbb{Q}$ by at most $2^{\lvert J(s)\rvert}$ sign patterns and membership tests, polynomial in the display for a fixed number of generators; `not yet defined` as a decision for other angles); when $F'$ is consistent and the inclusion fails: does not carry `[false]`; when $F'$ is not consistent on $C'$: `not yet defined` (the predicate is not stated at the child) (§4.37) | carries by composition `[proved]` | predicate preservation (restriction to a sub-sector) + frame + composition (§7.2.3–4); carrier `span`, frame parameter (§7.1); §2h, §4.37 |
| $\mathsf{phase}_U(\cdot\mid F)$ (logical action on a frame sector; §2h Row D) | carries `[proved]` | carries, same scalar, when $U$ is supported on one summand `[proved]` | does not carry `[false]` (counterexample §4.37) | when $F'$ is consistent and the inclusion of the row above holds: carries, same scalar `[proved]`; when $F'$ is consistent and the inclusion fails: does not carry `[false]`; when $F'$ is not consistent on $C'$: `not yet defined` (§4.37) | carries by composition `[proved]` | as the row above |
| $\mathsf{image}_U(\cdot;e)$ (logical action by conjugation; §2h Row E) | carries `[proved]` | carries when $U$ is supported on one summand `[proved]` | does not carry `[false]` (counterexample §4.37) | carries for every entry the transport keeps `[proved]` | carries by composition `[proved]` | as the $\mathsf{preserves}_U(\cdot\mid F)$ row |
| $\mathsf{addresses}_U(\cdot;F,A)$ (addressability; §2h Row F) | carries `[proved]` | carries on $C_1\oplus C_2$ when $U$ is supported on $Q_1$, frame $F_1\oplus F_2$, and $A\subseteq F_1$ `[proved]` | does not carry `[false]` (counterexample §4.37) | holds at $(C';F',A\cap F')$ iff the $\mathsf{preserves}_U$ test at $s$ `[proved]` | carries by composition `[proved]` | as the $\mathsf{preserves}_U(\cdot\mid F)$ row |
| $\omega$ (equal-syndrome generator weight floor; §2h) | carries, $\omega'=\omega$ and floor $\lceil L_d/2\rceil$ unchanged `[proved]` (§4.37) | carries **by weakening**: $\omega\ge\lceil\min(d^A,d^B)/2\rceil$, recomputed from $\min(L_d^A,L_d^B)$ `[proved]` (§4.37) | carries **by weakening**: $\omega'\ge\lceil d'/2\rceil$, recomputed from the child's lower endpoint $L_d'$ (the parent's value does not substitute: counterexample §4.37) `[proved]` | carries, floor $\lceil L_d'/2\rceil\ge\lceil L_d/2\rceil$ does not decrease `[proved]` (§4.37) | carries **by weakening** (recomputed from $L_d$ at each state) `[proved]` (§4.37) | weakening transport (monotone image of a carried bound, §7.2.6 / §2h); monotone in $\sqsubseteq^{\mathrm{low}}$ (§9.1); §4.37 |
| output well-formedness | carries `[proved]` | carries `[proved]` | carries `[proved]` | carries `[proved]` | carries `[proved]` | predicate preservation (§7.3); soundness (§8.4); §4.7–§4.9 |

**Reading the last column.** The "Instance of" column cites, for each
row, the schema of §7.2 under which its cells are
instances, and, where applicable, the abstract-interpretation transformer of
§8.3 that licenses the endpoint update and the refinement-preorder axis
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
| a claim referencing a **deleted generator** | `C-SEQUENCE` | **`unavailable`** | claimed **per evaluation, not per state** — the `W13` half, `OBL-JUDGMENT-TRANSPORT` |
| a **row-referencing certificate** through the `W7` loop | `C-DELETE-CHECK` → `C-ADD-CHECK` | **`unavailable`** | invalidated at the deletion step even though the final code equals the original — information-losing at the context level |
| **strict improvement** of distance | `C-ADD-CHECK` | **`conditional`** | carries $d' \ge d+1$ when the consumer supplies the minimum-weight-class hypothesis; otherwise `unavailable` |

**Everything outside this table is `not yet defined`** — certificates and
interface/metric/logical-witness judgments generally (the frame-reading
predicates of §2h, Rows C–F, excepted: they read the logical-witness field
as a frame supplied with the state), support-sensitive predicates
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
([`GATES.md`](GATES.md) §11).

*(Clarification, 2026-10-13. This states positions already of record in
[`TAXONOMY.md`](TAXONOMY.md) §1.4, [`GATES.md`](GATES.md) §11, and
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
| `E-GRAFT` | $d$ | sector-wise: $d'_\sigma=\min(d_\sigma,w_{\mathrm{expose},\sigma})$ for the non-spliced sector; the spliced sector carries its lower endpoint and drops its upper; the scalar form $d'=\min(d,w_{\mathrm{expose},\bar\tau})$ is false for this transition (see §4.13) | exposure minimum in the non-spliced sector and the structural coverage condition | Theorem 28.2, *code-deformation* §9.5; claim remains conditional on the consumer-supplied hypothesis; derivation at `OPERATIONAL_SEMANTICS.md` §4.13 |
| `C-DELETE-CHECK` (priced) | $d$, $d_X$, $d_Z$ | sector-wise: deleted sector $\tau$: $d'_\tau=\min(d_\tau,w_{\mathrm{del}})$; opposite sector $\bar\tau$: $d'_{\bar\tau}=\min(d_{\bar\tau},w_{\mathrm{exp}})$; full distance $d'=\min(d,w_{\mathrm{del}},w_{\mathrm{exp}})$ | $w_{\mathrm{del}}$ minimum over the promoted $\tau$-stabilizers and $w_{\mathrm{exp}}$ minimum over the exposed $\bar\tau$-normalizers | Theorem 12.1 (manuscript Theorem 7), *code-deformation* §4.1; sector split derived at `OPERATIONAL_SEMANTICS.md` §4.19 (2026-11-18); claim remains conditional on the consumer-supplied hypothesis |
| `C-ADD-CHECK` (strict improvement) | $d$ | $d'\ge d+1$ | exact old $d$ and exhaustive minimum-weight-class enumeration, all killed | Proposition 18.3, *code-deformation* §5.2; derivation reproduced at `OPERATIONAL_SEMANTICS.md` §4.19; claim remains conditional on the consumer-supplied hypothesis |
| `C-ADD-CHECK` (sector-aware gauging) | $d_X$, $d_Z$ | the supplied sector's lower endpoint is raised to $w_\sigma$ (never below the carried bound); the unpriced sector keeps its carried lower bound; when both $w_X,w_Z$ are supplied the full-distance lower endpoint may be raised to their minimum ($d=\min(d_X,d_Z)$) | sector minima $w_X,w_Z$ over the surviving logical classes and an evidence reference | Lemma 18.5, *code-deformation* §5.2; claim remains conditional on the consumer-supplied hypothesis |
| `C-ADD-CHECK` (direct-sum extinction) | $d$ | $d'=d_B$ (exact) when $d_B>d_A$ | exact old $d$ ($=d_A$), the trusted factor distance $d_B$ with an evidence reference, and the computed structural side — a two-block disjoint union, the added check inside one block, $k$ of the block containing the added check equal to zero, $k$ of the surviving block at least one, and no carried sector bound exceeding $d_B$ | Proposition 18.6 + Corollary 18.7, *code-deformation* §5.2; **stack family only**: the cell is stated for stack parents, and no family other than the source's stack/direct-sum family is licensed; claim remains conditional on the trusted $d_B$; general $k'>0$ remains open and is not claimed solved |
| `E-PEEL` at $q$ in sector $\tau$ (opposite sector $\sigma$) | $d_\sigma$ | exact: $d'_\sigma=\min(d_\sigma,w_{\mathrm{expose},\sigma}(q))$; the interval $[L_\sigma,U_\sigma]$ moves to $[\min(L_\sigma,p),\min(U_\sigma,p)]$, as for the graft | the exposure price $w_{\mathrm{expose},\sigma}(q)=\min\{|u|-1:u\text{ a parent }\sigma\text{-logical with }u_q=1\}$ (§2c), bound to the peel | derivation `OPERATIONAL_SEMANTICS.md` §4.28 (2026-11-10): the graft's non-spliced relation at $m=1$; claim remains conditional on the consumer-supplied minimum; unpriced corollary $d_\sigma-1\le d'_\sigma\le d_\sigma$ carried by §2b |
| `E-PEEL` at $q$ in sector $\tau$ (selected sector) | $d_\tau$ | exact: $d'_\tau=w_{\mathrm{avoid},\tau}(q)$; the interval becomes $[w,w]$ | the avoidance minimum $w_{\mathrm{avoid},\tau}(q)=\min\{|v|:v\text{ a parent }\tau\text{-logical with }v_q=0\}$ (§2c) | derivation `OPERATIONAL_SEMANTICS.md` §4.28 (2026-11-10); claim remains conditional on the consumer-supplied minimum; a value below the carried lower bound $L_\tau$ contradicts $d'_\tau\ge d_\tau$ and is refused |
| `E-SPLIT` at cut $(Q_A, R)$ (priced) | $d_X$, $d_Z$, $d$ | sector $\sigma$: $[\min(L_A, L_B),\; \min(U_A, U_B, U_\sigma)]$ where $U_\sigma$ is the parent's upper endpoint in sector $\sigma$; full distance $d$: endpoint-by-endpoint minimum of the two priced sector intervals intersected with the parent full upper endpoint $U$ | consumer-supplied intervals $[L_A, U_A]$ and $[L_B, U_B]$ for the sector distance of the two restriction displays $C'\vert_A$ and $C'\vert_B$, with a nonempty evidence reference (`split_block_intervals`, §2c) | derivation `OPERATIONAL_SEMANTICS.md` §4.48 (2026-11-25): $d_\sigma(C') = \min(d_\sigma(C'\vert_A), d_\sigma(C'\vert_B)) \le d_\sigma(C)$; claim remains conditional on the supplied block intervals; unpriced upper endpoints carry and lower endpoints reset to zero |
| `E-EXTEND` with $\Delta\neq\varnothing$ (distance loss) | $d_X$, $d_Z$, $d$ | sector $\tau$ with a supplied loss: lower endpoint $\max(0, L_\tau-\ell_\tau)$, where $L_\tau$ is the parent's carried lower endpoint; upper endpoints only from child-valid witnesses, as unpriced; full distance: lower endpoint $\min$ of the two sector lower endpoints, so an unpriced sector keeps it at $0$ | a loss $\ell_\tau\in\mathbb N$ for one or both sectors with an evidence reference, read as $d'_\tau\ge d_\tau-\ell_\tau$; refused with $\Delta=\varnothing$ (the lower endpoints already carry) and when the parent has no $\tau$-logical; the consumer checks shape only, never the loss | `OPERATIONAL_SEMANTICS.md` §4.30, *Distance-loss cell*; `OBL-EXTEND-DISTANCE-LOSS`; prior-art instance: the appending construction (`TAXONOMY.md` §2.9) |
| `A-CONCAT` towers (deleting lifted outer checks, any $k_{\mathrm{in}}$), price provider | deletion/exposure price input | factorization from tower level data | tower structure, class dictionary, outer presentation | Theorems 27.2 / 27.5, *code-deformation* §9.4; not a calculus constructor. A $k_{\mathrm{in}}>1$ generalization exists in the source (Theorem 27.8) with a refined class dictionary; the provider for arbitrary $k_{\mathrm{in}}$ is derived in this repository (`DERIVED_RELATIONS.md` §2a, 2026-11-11) and sweep-verified for $n_{\mathrm{in}}=4$, $k_{\mathrm{in}}\in\{1,2,3\}$; the source's theorems are cited, not reproduced. Its cost tables have size $2^{2k_{\mathrm{in}}}$ in the source; the derivation here uses two dictionaries of $2^{k_{\mathrm{in}}}$ entries. |
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
as unrecorded** (the decision log, 2026-10-20). The region is a property of the *search*,
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

**d=1 discharge (2026-11-13).** At distance 1 the exhaustive
enumeration is not exponential: the minimum-weight classes are bare
(singletons), so the scan is $O(n)$. When the parent carries a
currently-valid weight-1 witness in sector $\sigma$ and $k > 0$, the
parent's distance is exact ($d = 1$) with the witness as evidence, and the
cell discharges on the kill condition that the added opposite-sector check's
support contains every bare qubit of $\sigma$. The same-sector absorption
path ($K = S + \langle a\rangle$) absorbed nothing in the measured
campaign (a single same-sector check absorbs at most one coset), so it is
effectively dead weight; opposite-sector anticommutation is the productive
branch. The consumer-side screen is `strict_improvement_d1_feasible` /
`d1_discharge` in `machine/priced_calculus.py`; it does not validate the
supplied witness beyond shape, and it does not change any calculus axis.

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
| `C-DELETE-CHECK` | unpriced: reset to zero in every sector and the full distance. Priced: deleted sector $\tau$ lower endpoint $\min(L_\tau,w_{\mathrm{del}})$; opposite sector $\bar\tau$ lower endpoint $\min(L_{\bar\tau},w_{\mathrm{exp}})$; full distance $\min(L,w_{\mathrm{del}},w_{\mathrm{exp}})$ | unpriced: carry the proved $d'\le d$ bound and tighten from surviving or new witnesses. Priced: $U'_\tau=\min(U_\tau,w_{\mathrm{del}})$, $U'_{\bar\tau}=\min(U_{\bar\tau},w_{\mathrm{exp}})$, $U'=\min(U,w_{\mathrm{del}},w_{\mathrm{exp}})$ |
| `E-GRAFT` | full distance: reset to zero unless a supplied exposure price tightens it. Spliced sector: carry the lower endpoint; drop the upper endpoint to $+\infty$ unless a witness valid in the child supplies one. Non-spliced sector: reset to zero | full distance: lower endpoint resets to zero unless priced; upper endpoint is the non-spliced sector's carried bound, tightened by child-valid witnesses. Spliced sector: carries the lower endpoint only; upper endpoint from child-valid witnesses. Non-spliced sector: carry the non-increase bound and tighten from surviving or new witnesses |
| `P-REBASE` | unchanged (the row spaces are unchanged, so every span-expressible endpoint stays valid for the child) | unchanged (a parent-valid witness is valid for the identical child spans; revalidation is unnecessary and never discriminates) |
| `C-COLUMN-CNOT` | $[\lceil L_\sigma / \rho_\sigma^- \rceil,\; L_{\mathrm{full}}']$ with $L_{\mathrm{full}}' = \min(\lceil L_X / \rho_X^- \rceil, \lceil L_Z / \rho_Z^- \rceil)$ (§2k, §4.42) | $[\lceil L_\sigma / \rho_\sigma^- \rceil,\; \rho_\sigma U_\sigma]$ per sector and $\min(\rho_X U_X, \rho_Z U_Z)$ for full distance; witnesses are not carried automatically and must be transported by the sector map and revalidated in the child (§4.42) |
| `E-LOCAL-HADAMARD` ($T=Q$) | swap the two sector lower endpoints (§4.27: $d_X'=d_Z$, $d_Z'=d_X$); the full-distance lower endpoint keeps — $d'=d$ | swap the two sector upper endpoints likewise and *then* revalidate every witness against the child with its side swapped (an old $\sigma$-side witness is checked as a $\bar\sigma$-side witness of the child); the full-distance upper endpoint keeps |
| `E-LOCAL-HADAMARD` (split subset $\varnothing\subsetneq T\subsetneq Q$) | both sector lower endpoints become the parent's lower bound on $d$, namely $\max(\ell_d,\min(\ell_X,\ell_Z))$ (§4.27(b): $d_\sigma'\ge d$); the full-distance lower endpoint keeps, since $d'=d$ | the sector upper endpoints reset to $+\infty$, so only witnesses valid in the child bound them. A witness inside $T$ is revalidated with its side swapped, one disjoint from $T$ with its side kept, and a mixed witness is dropped. The full-distance upper endpoint keeps |
| `E-PEEL` | selected sector: carry the lower endpoint ($d_\tau'\ge d_\tau$, §4.28); opposite sector: carry the lower endpoint less one, floored at $0$ ($d_{\bar\tau}'\ge d_{\bar\tau}-1$, §4.28, 2026-11-10); full distance: the minimum of the two sector lower endpoints ($d'=\min(d_\tau',d_{\bar\tau}')$, so $d'\ge\min(L_\tau,L_{\bar\tau}-1)\ge d-1$; the comparison with $d$ itself is bounded in neither direction, §4.28's witness). Priced (§2a): the exposure price $p$ moves the opposite sector's lower endpoint to $\min(L_{\bar\tau},p)$ and the avoidance minimum $w$ pins the selected sector to $w$. The selected-sector carry was admitted 2026-11-06; the opposite-sector and full-distance carries and the two price cells 2026-11-10 | selected sector: reset to $+\infty$ (may exceed any prior upper, §4.28) unless the avoidance minimum pins it; opposite sector: carry the upper endpoint ($d_{\bar\tau}'\le d_{\bar\tau}$, §4.28), tightened to $\min(U_{\bar\tau},p)$ by the exposure price; full distance: the minimum of the two sector upper endpoints, tightened by child-valid witnesses |
| `E-PUNCTURE` | reset to zero in every sector and the full distance, a refusal by design, not an impossibility: §4.29's unnamed free-qubit instance (puncturing qubit $2$ of $Q=\{0,1,2\}$ with the $Z$ display $\{0,1\}$) raises the $X$ distance $1\to2$, showing that the direction of change depends on the deleted qubit and the induced stabilizer update; no universal $\le$- or $\ge$-claim is derivable for either sector or the full distance, and no cell carrying an endpoint is admitted. The reset is sound; full-distance endpoints remain refused unless a separately admitted price supports them. The reduction is recorded at §4.29 (2026-11-10): a puncture is the deletion of every row through $q$ followed by the removal of the then-free qubit, so each child sector distance is the lightest $q$-free logical of that intermediate code, $\min(w_{\mathrm{avoid},\sigma}(q),w_{\mathrm{hole},\sigma}(q))$; the hole price has no unpriced bound in either direction (increase $1\to2$, decrease $3\to2$), and its cell waits on the D2 lower bound; the full price is `unavailable` (§2f, hole-punch records) | only witnesses valid in the child, as for the peel |
| `E-EXTEND` | with $\Delta=\varnothing$: every sector carries its lower endpoint (distance cannot decrease under an added check); with $\Delta\neq\varnothing$: every interval's lower endpoint resets to zero, unless a distance loss is supplied (§2a), when sector $\tau$'s lower endpoint is $\max(0,L_\tau-\ell_\tau)$ | with $\Delta=\varnothing$: every sector rebuilds its upper endpoint from child-valid witnesses only (the pre-change upper endpoint is not a sound bound); with $\Delta\neq\varnothing$: only witnesses revalidating in the child |
| `C-DIRECT-SUM` | combine corresponding endpoints with `min` | combine corresponding endpoints with `min` |
| `E-GLUE` | in every sector and the full distance, `min` of the two factor ledgers' lower endpoints (sound without a certificate: the glued code is $C_A\oplus C_B$ with seam checks added, each sector distance of the direct sum is the minimum of the factors', and adding a check never lowers a distance, so each glued distance is at least the factor minimum, §4.31) | only the Z sector's, as `min` of the two factors' Z upper endpoints, and only under an admissible seam certificate (§2e); the X and full upper endpoints are left to witnesses valid in the child |
| `E-SPLIT` | unpriced: reset to zero in every sector and the full distance (splitting can lower distance: §4.48). Priced (§2a, §2c `split_block_intervals`): in each priced sector $\sigma$, $\min(L_A, L_B)$ from the supplied restriction-display intervals $[L_A, U_A]$ and $[L_B, U_B]$; full distance takes $\min(L'_X, L'_Z)$ when both sectors are priced (else $0$); an infinite lower bound when $k' > 0$, a sector or block lower endpoint above $1$ contradicted by a validated weight-1 singleton logical in the child, or a lower endpoint exceeding any carried/witness upper endpoint is refused (`no_derivation`) | unpriced: carry the proved $d_\sigma'\le d_\sigma$ and $d'\le d$ bounds and tighten from surviving or new witnesses (§4.48). Priced: in each priced sector $\sigma$, $\min(U_A, U_B, U_\sigma)$, tightened by child-valid witnesses; full distance takes $\min(U'_X, U'_Z, U)$ |

For a supplied price $p$ the monotone map $f(x)=\min(x,p)$ transports an
input interval to $[\min(L,p),\min(U,p)]$. **A price moves the endpoints its
own relation covers, and no others.** The two prices the consumer accepts are
indexed differently, and the difference is load-bearing:

- The **deletion** price is now admitted sector-wise: $w_{\mathrm{del}}$
 is the deleted sector's promotion minimum and $w_{\mathrm{exp}}$ the
 opposite sector's exposure minimum, so it moves the deleted sector's and the
 opposite sector's endpoints as well as the full-distance endpoints:
 $d'_\tau=\min(d_\tau,w_{\mathrm{del}})$ and
 $d'_{\bar\tau}=\min(d_{\bar\tau},w_{\mathrm{exp}})$, with
 $d'=\min(d,w_{\mathrm{del}},w_{\mathrm{exp}})$. The unpriced rule still
 resets lower endpoints to zero.
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
 transition $C\xrightarrow{\mathrm{delete}_r}C'$ with deleted check in sector
 $\tau$. Asserts, sector-wise,
 $d_\tau(C')=\min(d_\tau(C),w_{\mathrm{del}})$ and
 $d_{\bar\tau}(C')=\min(d_{\bar\tau}(C),w_{\mathrm{exp}})$, and
 consequently $d(C')=\min(d(C),w_{\mathrm{del}},w_{\mathrm{exp}})$ for the
 full distance. Here
 $w_{\mathrm{del}}=\min\{\mathrm{wt}(g):g\in S_\tau\setminus S'_\tau\}$
 over the promoted $\tau$-stabilizers and
 $w_{\mathrm{exp}}=\min\{\mathrm{wt}(E):E\in N_{\bar\tau}(S')\setminus
 N_{\bar\tau}(S)\}$ over newly exposed $\bar\tau$-normalizer elements.
 The two minima are sector-specific by construction: $w_{\mathrm{del}}$ is the
 deleted sector's promotion minimum and $w_{\mathrm{exp}}$ the opposite
 sector's exposure minimum; no global price is reused.

- **Exposure price $w_{\mathrm{expose}}$.** Binds to a transition
 $C\xrightarrow{\mathrm{E-GRAFT}(q,\tau,\vec r)}C'$ and to the exposed
 set in the non-spliced sector $\bar\tau$: the exposed set is the child
 $\sigma$-logicals whose lift touches $q$, with
 $w_{\mathrm{expose},\sigma}=\min\{|z|-1:z\text{ a parent }\sigma\text{-logical with }z_q=1\}$
 (or $+\infty$ if none), and the relation is
 $d'_\sigma=\min(d_\sigma,w_{\mathrm{expose},\sigma})$. The spliced sector
 needs no price. No carry rule for the spliced sector's upper endpoint is
 licensed by this hypothesis (see §4.13 and §2b). The same input, with the
 same definition over the parent's logicals through $q$, binds to a
 transition $C\xrightarrow{\mathrm{E-PEEL}(q,\tau,r)}C'$ for the opposite
 sector $\sigma=\bar\tau$, where §4.28 derives the same relation
 $d'_\sigma=\min(d_\sigma,w_{\mathrm{expose},\sigma})$ (added 2026-11-10; extends this obligation, not discharged).

- **Avoidance minimum $w_{\mathrm{avoid},\tau}$ (added 2026-11-10; extends this obligation, not discharged).** Binds to a transition
 $C\xrightarrow{\mathrm{E-PEEL}(q,\tau,r)}C'$ and to the selected sector
 $\tau$: asserts $d'_\tau=w_{\mathrm{avoid},\tau}(q)$, where
 $w_{\mathrm{avoid},\tau}(q)=\min\{|v|:v\text{ a parent }\tau\text{-logical with }v_q=0\}$
 is the least weight of a parent $\tau$-logical avoiding the peeled qubit
 (§4.28: the child's $\tau$-logicals are exactly those). It is at least
 $d_\tau$; a supplied value below the carried lower bound contradicts the
 sound carry and is refused rather than widened. The consumer validates the
 shape (a positive integer and an evidence reference), not the minimization.

- **Sector-aware gauging prices $(w_X, w_Z)$ (added 2026-10-23, ;
 extends this obligation, not discharged).** Binds to a transition
 $C\xrightarrow{\mathrm{addStab}_{r:\tau}}C'$ with a sector-pure added
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
 $C\xrightarrow{\mathrm{addStab}_{r:\tau}}C'$ and to a state $C$ with
 $d(C)=\text{base\_distance}$: asserts that every weight-$d(C)$ logical in
 $C$ either anticommutes with $r$ (in sector $\bar\tau$) or lies in
 $C_\tau+\langle r\rangle$ (in sector $\tau$). The cell carries
 $d'\ge d+1$ only under that hypothesis.

- **Split block intervals (`split_block_intervals`, added 2026-11-25, issue #546).** Binds to a transition
 $C\xrightarrow{\mathrm{split}_{Q_A;R}}C'$ and to one or both sectors $\sigma \in \{X, Z\}$.
 Supplies intervals $[L_A, U_A]$ and $[L_B, U_B]$ (with $+\infty$ permitted for a
 $k=0$ block) together with a nonempty evidence reference, asserting
 $L_A \le d_\sigma(C'|_A) \le U_A$ and $L_B \le d_\sigma(C'|_B) \le U_B$ for
 the two restriction displays $C'|_A$ and $C'|_B$ (§4.48). Because
 $d_\sigma(C') = \min(d_\sigma(C'|_A), d_\sigma(C'|_B)) \le d_\sigma(C)$, the
 cell carries $[\min(L_A, L_B), \min(U_A, U_B, U_\sigma)]$ for sector $\sigma$,
 and full-distance endpoints $\min$ across both sectors when both are supplied.
 The consumer validates interval shape, the nonempty evidence reference, and
 structural consistency (no infinite lower endpoint when $k' > 0$, no sector
 or block lower endpoint above $1$ against a validated weight-1 singleton
 logical — a child qubit in no opposite-sector displayed row whose singleton
 lies outside the same-sector span — and no lower endpoint above a carried
 upper endpoint or validated witness); it does not otherwise validate the
 supplied block bounds, and the cell remains `conditional`.

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
| `E-PEEL` at $q$ | $\lambda\vert_{Q\setminus\{q\}}$ | $r'=\max\{\mathrm{diam}_{\lambda'}(s):s\in\mathit{rows}'\}$ | $\le r$ |
| `E-PUNCTURE` at $q$ | $\lambda\vert_{Q\setminus\{q\}}$ | $r'=\max\{\mathrm{diam}_{\lambda'}(s):s\in\mathit{rows}'\}$ | $\le r$ |
| `E-LOCAL-HADAMARD` ($T=Q$) | $\lambda$ | $r'=r$ | unchanged |
| `E-LOCAL-HADAMARD` (split subset) | $\lambda$ | $r'=\max\{\mathrm{diam}_\lambda(s):s\in\mathit{rows}'\}$ | $\le r$ (every output support is a subset of a parent support) |
| `P-REBASE` | $\lambda$ | $r'=\max\{\mathrm{diam}_\lambda(s):s\in\mathit{rows}'\}$ | recomputed; no guaranteed direction |
| `E-SPLIT` | $\lambda$ | $r'=\max\{\mathrm{diam}_\lambda(s):s\in\mathit{rows}'\}$ | $\le r$ |
| `E-EXTEND` | not inherited: a layout $\lambda'$ on $Q\cup\Delta$ with $\lambda'\vert_Q=\lambda$ must be supplied (with $\Delta=\emptyset$, $\lambda$ itself) | $r'=\max(r,\max\{\mathrm{diam}_{\lambda'}(s):s\in\mathit{rows}'_{\rm new}\})$ when supplied | $\ge r$ (when supplied) |

The graft's bound is a **factor of two, not a non-increase**. A graft row is
$a_i\oplus a_{i+1}$ restricted to $Q'$, with $q$ in both rows; two points of
the new row lying in different parts are at distance at most
$\mathrm{diam}(a_i)+\mathrm{diam}(a_{i+1})$, and the opposite-sector rows are
shortened at $q$, which cannot increase a diameter. The derivation is at
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4.21 (interaction-radius transport). The naive claim
that the graft preserves the radius is **false**: over the challenge's board
entries with $n\le 14$ at the pinned commit 9d30c66a, 198 of 823 applicable
grafts increase it
([`machine/experiments/layout_graft_survey.json`](../machine/experiments/layout_graft_survey.json)).

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
(`verify/qldpc_verify.py` at challenge commit 9d30c66a) compares a
floating-point `math.dist` radius against `cap + 1e-9`; a radius within
$10^{-9}$ above a cap can therefore be `in` for the challenge and `out` for
the consumer. The two are not the same verdict.

The class's transport needs no separate cell, because it follows from §2d.2:
deletion can only preserve or improve it, addition can only preserve or
degrade it, and the graft can degrade it — but only where the parent's radius
was within a factor of two of the cap, since $r'\le 2r$. Where the cap is at
least twice the parent's radius, the graft preserves the class outright.

### 2d.5 Layout cells

The transport facts of §2d.2 are judgment cells: one row per transition, with
the child's layout, the radius cell and its direction, and the honesty cell,
each with its evidence status in brackets. Throughout, $\lambda$ is the
parent's layout and $\lambda'$ the child's, $r$ and $r'$ are the parent's and
the child's interaction radius (§2d.1), $Q$ is the parent's qubit set,
$\mathit{rows}'$ is the child's display, and, for the two binary transitions,
$r_A$ and $r_B$ are the factors' radii in their own layouts. "Recomputed"
means $r'=\max\{\mathrm{diam}_{\lambda'}(s):s\in\mathit{rows}'\}$, exact and
with no hypothesis. The derivations are at
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4.21 (the
2026-11-10 addendum for the transitions after `E-GRAFT`), the cells are
transcribed in [`machine/semantics.json`](../machine/semantics.json) under
`layout_cells`, and the randomized layout-conformance harness
(`machine/experiments/layout_conformance_harness.py`) checks every row on
random states and layouts. A harness run is evidence, never confirmation.

| Transition | Child's layout $\lambda'$ | Radius cell | Direction | Honesty cell |
| --- | --- | --- | --- | --- |
| `C-SKIP` | $\lambda$ | carries, $r'=r$ `[proved]` | unchanged | preserved `[proved]` |
| `C-DELETE-CHECK` | $\lambda$ | carries, recomputed `[proved]` | $r'\le r$ | preserved `[proved]` |
| `C-ADD-CHECK` | $\lambda$ | carries, $r'=\max(r,\mathrm{diam}_\lambda(r_{\rm new}))$ `[proved]` | $r'\ge r$ | preserved `[proved]` |
| `C-SEQUENCE` | the layout after the last step | carries by composition of the per-step cells `[proved]` (§4.11) | per step | per step; a merged or supplied layout is owed at the step that needs it |
| `C-DIRECT-SUM` | the two summand layouts, blockwise up to isometry; a merged layout must be supplied | carries, $r=\max(r_A,r_B)$ `[proved]` | maximum of the summands | **conditional**: the merged layout must be honest (§2d.3); honesty of the summands does not imply it |
| `E-GRAFT` at $q$ | $\lambda\vert_{Q\setminus\{q\}}$ | carries, recomputed, and $r'\le 2r$ `[proved]` | may increase; the non-increase $r'\le r$ is **false** | preserved `[proved]`: a restriction of an honest layout is honest |
| `E-PEEL` at $q$ | $\lambda\vert_{Q\setminus\{q\}}$ | carries, recomputed `[proved]` | $r'\le r$ | preserved `[proved]`: restriction |
| `E-PUNCTURE` at $q$ | $\lambda\vert_{Q\setminus\{q\}}$ | carries, recomputed `[proved]` | $r'\le r$ | preserved `[proved]`: restriction |
| `E-LOCAL-HADAMARD` ($T=Q$) | $\lambda$ | carries, $r'=r$ `[proved]` | unchanged | preserved `[proved]` |
| `E-LOCAL-HADAMARD` (split subset) | $\lambda$ | carries, recomputed `[proved]` | $r'\le r$ | preserved `[proved]` |
| `P-REBASE` | $\lambda$ | carries, recomputed `[proved]` | none guaranteed: both $r'>r$ and $r'<r$ occur | preserved `[proved]` |
| `C-COLUMN-CNOT` | $\lambda$ | carries, recomputed `[proved]` | none guaranteed: row supports change, so both $r'>r$ and $r'<r$ occur | preserved `[proved]`: same qubit set and layout |
| `E-SPLIT` | $\lambda$ | carries, recomputed `[proved]` (§4.48) | $r'\le r$ | preserved `[proved]`: same qubit set and layout |
| `E-EXTEND`, $\Delta\neq\emptyset$ | not inherited: a layout $\lambda'$ on $Q\cup\Delta$ with $\lambda'\vert_Q=\lambda$ must be supplied | carries when supplied, $r'=\max(r,\max\{\mathrm{diam}_{\lambda'}(s):s\in\mathit{rows}'_{\rm new}\})$ `[proved]`; no radius otherwise | $r'\ge r$ when supplied | **conditional**: the supplied layout must be honest; the parent's honesty does not imply it |
| `E-EXTEND`, $\Delta=\emptyset$ | $\lambda$ | as `C-ADD-CHECK`, once per added row `[proved]` | $r'\ge r$ | preserved `[proved]` |
| `E-GLUE` | the two factor layouts, blockwise as for `C-DIRECT-SUM`; a merged layout must be supplied | carries, $r=\max(r_A,r_B,\max\{\mathrm{diam}(s):s\ \text{a seam row}\})$ `[proved]` (the direct-sum cell, then one `C-ADD-CHECK` cell per seam check) | $r\ge\max(r_A,r_B)$ | **conditional**: the merged layout must be honest |
| `L-HGP`, `L-LIFTED`, `L-GROUP-ALGEBRA`, `A-CONCAT`, `L-BALANCED`, `L-TANNER`, `L-TILE`, `A-PRODUCT`, `A-DOUBLE` (constructors, 2026-11-11), `L-NESTED-CSS` (constructor, 2026-11-13), `L-MAPPING-CONE` (constructor, 2026-11-18), `L-EMPTY`, `L-FREE`, `A-PULLBACK`, `A-PUSHOUT` (constructors, 2026-11-19), `L-PAIR-PARTITION`, `PP-SCALE` (constructors, 2026-11-22) | none inherited: there is no parent; a layout on the constructed qubits must be supplied | recomputed when supplied, $r=\max\{\mathrm{diam}_{\lambda}(s):s\in\mathit{rows}\}$ over the constructed display `[proved]` (exact computation, §2d.1; $r=0$ for empty displays); no radius otherwise | none: no parent to compare with | **conditional**: the supplied layout must be honest (§2d.3) |


Four entries are recorded as non-transfer cases rather than as monotone cells:
`E-GRAFT`'s factor-of-two bound, `E-EXTEND`'s supplied layout, `P-REBASE`'s
recomputed radius with no direction, and the honest-merge premise of
`C-DIRECT-SUM` and `E-GLUE`. A conditional cell's verdict applies only once
its layout premise is met; the interval consumer does not build merged or
supplied layouts, so those premises are inputs, and the radius is never a
distance (no lower bound, price, or witness enters any row). A supplied layout
may come from the consumer-side layout provider
(`machine/layout_provider.py`), which synthesizes a planar integer-grid layout
from the displayed Tanner graph. Its output is a supplied layout like any
other: it is ledger data beside the state, it meets the honesty premise only
by passing the §2d.3 check, and the radius it yields is a property of that
layout, with no claim that a smaller radius is unattainable. The locality class
follows from the direction column as §2d.4 states; it takes no row of its own.


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
requires the full move word, not a summary. Scope qualifier: this no-go is
stated at graph-homology / selected-sector scope only; it does not prove
that every composition loses distance, nor that no richer certificate can
work — it says only that a flat check over factor data and connectivity
cannot certify within that scope.

**Positive composition criteria.** The seam certificate above is
the baseline. Three further conditional criteria grow `E-GLUE` into a family
of typed, conditional judgments and certificate providers. Each is a
separate conditional row with its hypothesis attached; none is a universal
composition rule. Odd-cycle table omission and an incomplete certificate
producer stay visible (they are not discharged here); circuit preservation
is empirical where the source says so.

| Criterion | Hypothesis (consumer-supplied) | Verdict when hypothesis holds | Verdict otherwise |
| --- | --- | --- | --- |
| Interface classification | the seam interface is classified as a monotone top-to-bottom surface-code seam with compatible move words (the §2e move-word equality) | the interface class is admissible; the seam certificate applies | `inconclusive` — the interface is not licensed |
| Union-layout immunity | the union layout has no odd cycle in the seam graph (the seam graph is bipartite) | the layout is immune: gluing does not introduce a new logical of weight below the factor minimum | not certified; odd-cycle omission stays visible and the check returns `inconclusive` |
| Boundary-signature certificates | the boundary signatures of the two factors agree on the shared boundary | a certified bound $d_Z(Q)=\min(d_A,d_B)$ is issued under the agreed signature | no certificate; the check returns `inconclusive` |

Scope and visibility: these rows inherit the §2e scope (monotone top-to-bottom
seams, surface code / planar). The odd-cycle table may be omitted and the
certificate producer may be incomplete; both stay visible rather than being
silently treated as discharged. Circuit-level preservation remains empirical.
No flat-DEM composition recognition is claimed, and no universal composition
rule is added.

**Completion (2026-11-14).** The "Done when" criteria of are met:
the baseline seam certificate is already admitted in §2e, and the remaining
delta (interface classification, union-layout immunity, boundary-signature
certificates) is admitted here as conditional rows with hypotheses attached,
with odd-cycle omission, incomplete producer, and empirical circuit
preservation kept visible.

**Interval transformer (§2b `E-GLUE` row).** Under an admissible seam
certificate the Z-sector upper endpoint is the minimum of the two factors'
Z upper endpoints; in every sector and the full distance the lower endpoint
is the minimum of the two factors' lower endpoints (sound without a
certificate). The X and full upper endpoints are left to witnesses valid in
the child, the factors' own witnesses among them once revalidated there
(`OPERATIONAL_SEMANTICS.md` §4.31, instance-wise equality, 2026-11-10). This
is the transformer whose soundness is derived at `OPERATIONAL_SEMANTICS.md`
§4.32.

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
under the 2026-10-23 scope decision ([`VERSIONING.md`](VERSIONING.md) §5): they are in scope
as moves. Some rows carry structural facts with no consumer-supplied
hypothesis (namespace arithmetic, rank bookkeeping, sector exchange); others
are conditional on a hypothesis or refuse outright. Otherwise the
corresponding cell is `unavailable`/`not yet defined`. The non-CSS
extended-state layer (`X-SYMPLECTIC-DOUBLE`/`HALVE`) is **not** admitted by
this decision.

**Transitions.** Five of the six now have typed transitions
(`TERM_LANGUAGE.md` §2; `OPERATIONAL_SEMANTICS.md` §2, §4.26–§4.30):
`peel`, `puncture`, `extend`, `hadamard` (admitted for every $T\subseteq Q$ along which both row spaces split), and
`rebase`. `E-GLUE` remains **binary-only, with no unary command production** (decided
2026-11-18), carrying the binary state-expression constructor
$e ::= \mathrm{glue}(e_1, e_2; \vec u)$ (`TERM_LANGUAGE.md` §1–§2) and its
admitted evaluator transition (`OPERATIONAL_SEMANTICS.md` §4.31). Both
future-$\Pi$ fields are defined in full (`STATE_MODEL.md` §1a), the CSS-level algebra of the extracted Theorem 4 / claim 7.4
derivation is mechanized in `lean/CodeCalculus/GlueExtraction.lean` with the geometric move-word $\to$ `AdmissibleSeam` substrate gap
explicitly recorded, and `E-GLUE` sits at `contract-stated` (rung 5,
2026-11-18; Gate 6 ratified 2026-11-19).
Sound admission is discharged under the stated hypotheses
(`OBL-GATE6-CSS-EXTENSIONS`, `OPERATIONAL_SEMANTICS.md` §4.32,
2026-10-28); the cells remain conditional on their hypotheses and `promoted`
remains a review disposition. The consumer's interval behavior for the six is
transcribed in §2b with the unsourced-transcription hazard in mind (each
rule's *source* is the named section, not this table alone).

| Move | Property | Carries when hypothesis supplied | Hypothesis (consumer-supplied) | Source | Status |
| --- | --- | --- | --- | --- | --- |
| `E-GLUE` | $d_Z$ | $d_Z(Q)=\min(d_A,d_B)$ for an admissible seam; lower endpoints are sound without a certificate (the glued code is the direct sum with seam checks added, so each sector distance is at least the factor minimum: §4.31) | `AdmissibleSeam`: a minimum-weight factor logical survives (§4.33(ii)); Theorem 4 supplies the unconditional lower half ($w_{\mathrm{re},Z}=+\infty$, hence $d_Z(Q)\ge \min(d_A,d_B)$) on every admitted glue without a certificate, and the equality itself is conditional on `AdmissibleSeam` (the upper half). The certificate (equal move words $w(c_A)=w(c_B)$, §2e) is the evidence the consumer records for the `AdmissibleSeam` hypothesis; the geometric move-word $\to$ `AdmissibleSeam` implication stays a substrate gap; lower endpoints are sound without a certificate | seam certificate (§2e); Theorem 4 lower bound unconditional (§4.31; `wRe?_eq_none`, `glue_theorem4_lower_bound`); equality conditional on `AdmissibleSeam` (`admissibleSeam_exactDistance?_eq_min`), mechanized algebraically (`GlueExtraction.lean`), not discharged by extraction | conditional cell admitted; binary-only expression constructor `glue(e₁, e₂; seams)` (`TERM_LANGUAGE.md` §1–§2); **`contract-stated` (rung 5, 2026-11-18)**; future-$\Pi$ fields defined (`STATE_MODEL.md` §1a) |
| `E-PUNCTURE` | $n$ | $n'=n-1$, exactly | **none** — the namespace arithmetic is the update itself | `OPERATIONAL_SEMANTICS.md` §2, §4.29 | transition defined; cell carried; sound admission discharged (§4.32), conditional on hypotheses |
| `E-PUNCTURE` | $k$ | $k'=k-1+t_X+t_Z$, exactly ($t_\tau$ = number of displayed $\tau$-rows containing $q$; §4.29) | **none** — the rank bookkeeping is derivable, not supplied | §2, §4.29 | transition defined; cell carried |
| `E-PUNCTURE` | $d$, $d_X$, $d_Z$ | `unavailable`: no exact post-puncture value is derived, and the full hole-punch price reads `unavailable` (hole-punch records below) | *(no hypothesis is admitted for a price: the reduction of §4.29, deletions then a free-qubit removal, makes the price a hole price, blocked on the D2 lower bound; no cell, no fixture)* | §2, §4.29 | **nothing carries** (§4.29's unnamed-free-qubit increase $d_X\;1\!\to\!2$ and deleted-row decrease $d_X\;3\!\to\!2$); ledger resets; reduction recorded 2026-11-10 |
| `E-PEEL` | $n$ | $n'=n-1$, exactly | **none** | §2, §4.28 | transition defined; cell carried |
| `E-PEEL` | $k$ | $k'=k$, exactly (§4.28's injectivity argument: the opposite sector's restriction never loses rank) | **none** — the rank bookkeeping is derivable, not supplied | §4.28 | transition defined; no price cell |
| `E-PEEL` | $d_\tau$ (selected sector) | lower endpoint carries: $d_\tau'\ge d_\tau$ (§4.28); exact under the avoidance minimum: $d_\tau'=w_{\mathrm{avoid},\tau}(q)$ (§2a, §2c) | **none** for the carry; the avoidance minimum for the exact cell | §2, §4.28 | cell admitted 2026-11-06: selected-sector lower carry; price cell admitted 2026-11-10 |
| `E-PEEL` | $d_{\bar\tau}$ (opposite sector) | both endpoints carry within one: $d_{\bar\tau}-1\le d_{\bar\tau}'\le d_{\bar\tau}$ (§4.28); exact under the exposure price: $d_{\bar\tau}'=\min(d_{\bar\tau},w_{\mathrm{expose},\bar\tau}(q))$, the graft's relation at $m=1$ (§2a, §2c) | **none** for the carries; the exposure price for the exact cell | §2, §4.28 | upper carry admitted 2026-11-06; lower carry less one and price cell admitted 2026-11-10 |
| `E-PEEL` | $d$ (full distance) | both endpoints are the minima of the two sector endpoints: $d'=\min(d_\tau',d_{\bar\tau}')\ge\min(d_\tau,d_{\bar\tau}-1)\ge d-1$ (§4.28) | *(none)*; the two sector prices pin it when both are supplied | §2, §4.28 | admitted 2026-11-10; the comparison $d'\;\mathrm{vs.}\;d$ is bounded in neither direction (§4.28's witness) |
| `E-EXTEND` (patch growth / breeding) | $n$, $k$ | $n'=n+|\Delta|$; $k'=k+|\Delta|-s_X-s_Z$, exactly | **none** — the row-count arithmetic is the update | §2, §4.30 | transition defined; cell carried |
| `E-EXTEND` (patch growth / breeding) | $d$,$d_X$,$d_Z$ | with $\Delta=\varnothing$: the §2a `C-ADD-CHECK` monotonicity in both sectors (lower endpoints carry; no sector's upper endpoint carries, since an added $X$ row can raise $d_Z$: §4.30); with $\Delta\neq\varnothing$: none unpriced; under a supplied loss $\ell_\tau$, $d'_\tau\ge\max(0,L_\tau-\ell_\tau)$ (§2a) | none for the unpriced refusal; the conditional cell takes a sourced loss $\ell_\tau$ (§2a) | §2, §4.30 | no unconditional distance rule for the namespace-growing instance; one conditional cell |
| `E-LOCAL-HADAMARD` | sector swap ($T=Q$) | exact: $d_X'=d_Z$, $d_Z'=d_X$, $d'=d$; $n,k,w$ unchanged | **none** — the $T=Q$ instance needs no consumer input | §2, §4.27(a) | transition defined |
| `E-LOCAL-HADAMARD` | split subset ($\varnothing\subsetneq T\subsetneq Q$, under the row-space splitting guard) | exact: $n,k$ unchanged, $d'=d$; sector lower bound $d_\sigma'\ge d$; $w'\le w$. The sector distances follow the $T$-split decomposition and are **not** exchanged | **none** — the guard is checked structurally | §2, §4.27(b) | transition defined 2026-11-26 |
| `P-REBASE` | presentation | everything span-expressible carries exactly: $n,k,d_X,d_Z,d$ (spans unchanged); $w$/$r$/Tanner recomputed exactly over the child display | *(GL-ness of $M$ is a checked structural premise, not a trusted input; no hypothesis is needed)* | §2, §4.26 | transition defined; `OBL-REBASE-GENERATION` discharged §4.26 |
| `E-SPLIT` (separating deletion, admitted 2026-11-25) | $n$, $k$, $w$, $r$, $\kappa$ | $n'=n$, $k'=k+t=k(C'\vert_A)+k(C'\vert_B)$ ($t=|R|$), $w'\le w$, $r'\le r$ (layout unchanged, honesty preserved), $\kappa'$ recomputed ($\kappa'\ge 2$ when $Q_A,Q_B\neq\varnothing$), child separated at $Q_A$, all exact | **none** — derived over `C-DELETE-CHECK` | §2, §4.48 | transition defined (`split(Q_A; R)`, 2026-11-25); cell carried; two-state projection refused |
| `E-SPLIT` | $d_X$, $d_Z$, $d$ (unpriced) | upper endpoints carry ($d_\sigma'\le d_\sigma$, $d'\le d$); lower endpoints reset to zero; exact unpriced values `unavailable` | **none** | §2, §4.48 | proved upper carry; lower-endpoint carry refuted (§4.48, $d_Z : 2\to 1$); exact unpriced `unavailable` |
| `E-SPLIT` | $d_X$, $d_Z$ (priced) | interval becomes $[\min(L_A,L_B),\;\min(U_A,U_B,U_\sigma)]$, where $U_\sigma$ is the parent's upper endpoint in sector $\sigma$ | `split_block_intervals`: intervals $[L_A,U_A]$ and $[L_B,U_B]$ for the sector distance of restriction displays $C'\vert_A$ and $C'\vert_B$, with a nonempty evidence reference (§2c) | §4.48 | conditional cell admitted 2026-11-25; sound and monotone under stated hypotheses (§4.48; mechanized in `SplitCommand.lean`, `Gate6Soundness.lean`, `Gate6Exact.lean`) |
| `E-SPLIT` | $d$ (priced) | endpoint-by-endpoint minimum of the two priced sector intervals, intersected with the parent full upper endpoint $U$ | both sector hypotheses (`split_block_intervals` for $X$ and $Z$) | $d=\min(d_X,d_Z)$; §4.48 | conditional cell admitted 2026-11-25 |

The cells above are **admission decisions plus their carried judgments**. A
distance judgment with no stated hypothesis is a **refusal**, not a gap: the
§2.8/§2.9 records demand the formulas state their hypotheses, and none of
these moves has a source-stated distance formula to reproduce. Sound admission is discharged under the stated hypotheses
(`OPERATIONAL_SEMANTICS.md` §4.32, 2026-10-28); the cells remain conditional
on their hypotheses, and `promoted` remains a review disposition.

**Hole-punch price: property records and the `unavailable` full price.**
The full price of a hole punch is the exact value of $d$, $d_X$, and $d_Z$ of
the punched code. It is `unavailable`: no `E-PUNCTURE` evaluation derives an
exact post-puncture distance, the consumer's rule is the reset of §2b, and no
price cell and no fixture is admitted. The word has its §3 meaning and
attaches to the evaluation. A state of this calculus carries no patch
geometry (the layout is ledger data, §2d), so nothing in a state identifies a
hole.

The partial facts held in this repository concern one geometric family and
are recorded below. The family is a square-cellulated surface-code patch
occupying the rectangle with corners $(0,0)$ and $(L_x,L_y)$, with rough rows
at heights $0$ and $L_y$, from which one rectangular hole with corners
$(x_0,y_0)$ and $(x_0+a,\,y_0+b)$ is removed. Write $h=L_y$ for the patch
height, and write $d_{\mathrm{hole}}$ for the minimum weight of a nontrivial
relative $Z$-cycle with odd winding around the center of the hole
(`the D2 Z-distance reduction note`, *Definitions used*). The hole is
strictly interior when $x_0\ge 1$, $y_0\ge 1$, $x_0+a\le L_x-1$, and
$y_0+b\le L_y-1$. It is degenerate when no bottom-to-top column of the patch
survives.

| Record | Statement | Scope | Source | Status |
| --- | --- | --- | --- | --- |
| Reduction | $d_Z=\min(h,d_{\mathrm{hole}})$ | strictly interior hole | `the D2 Z-distance reduction note` | derivation in the repository; not `promoted`; no cell |
| Lower bound | $d_{\mathrm{hole}}\ge\min\bigl(2(a+b),\;2(y_0+b)+a,\;2(L_y-y_0)+a,\;L_y\bigr)$ | strictly interior hole | `the D2 lower-bound attempt note` | derivation in the repository; maintainer acceptance pending; no cell |
| Witnesses | four odd-winding relative cycles whose weights are the four terms of the lower bound | strictly interior hole | `the D2 lower-bound attempt note`, *Matching witnesses* | described only: the checker that the note cites is not in this repository, so no equality for $d_{\mathrm{hole}}$ is recorded |
| Boundary-touching hole | $d_Z=h$ | hole meeting the patch boundary, not degenerate | `the D2 boundary-touching case note` | argument in the repository; not `promoted`; no cell; the four-term expression does not apply in this scope |
| Full price | exact $d$, $d_X$, $d_Z$ of the punched patch | every hole | none | `unavailable` |

These rows are records, not admitted cells. The consumer reads none of them,
and none changes a ledger endpoint. They concern $d_Z$ only, and nothing is
recorded for $d_X$ or $d$. Degenerate instances are outside every row. No
closed form is to be read as a price: the label of Conjecture 21.5 in the
companion paper *code-deformation* is unchanged, and the four-term expression
enters this document only as the lower bound above.

Admitting a conditional hole-price cell, with the geometry as a
consumer-supplied hypothesis, is a separate maintainer decision that waits on
acceptance of the D2 lower bound. That wait is a deferral. It is
not what `unavailable` records here ([`VOCABULARY.md`](VOCABULARY.md),
*Underivability field*): the full price stays `unavailable` for `E-PUNCTURE`
evaluations whether or not such a cell is later admitted.

**Instance reading (2026-10-28).** The extension cells above are among the
bespoke items §7.3 leaves out of the generic core (the distance atoms, the
conditional price cells, the seam certificate, and the extension cells whose
transitions are new); `P-REBASE` and `E-GRAFT` are already recorded in §7.3 as
carrier-typing instances, not bespoke. Where interval behavior is stated for
these moves, it is cited through the move-monotonicity lemmas of §9.4
only; no transformer of §8.3 is claimed for a move outside §8.3's scope.
No cell verdict, evidence label, or qualification changes.

**Disposition (2026-11-10).** The following were accepted
for work in v0.2: sector-aware price cells for `E-PUNCTURE`/`E-PEEL`
(puncture blocked on the D2 lower bound), promotion of `E-GLUE` from
conditional lower-bound connector to a licensed connected-code composition with
seam-certificate equality (conditional on the logical-witness prerequisite),
and layout-transfer judgment cells. The layout cells landed 2026-11-10 ( §2d.5). Neither of the other two is admitted by the disposition; the
cells above remain as recorded.

## 2g. Admitted typed constructors (`transition-defined`, 2026-11-11)

The nine constructors admitted on 2026-11-11 (
`TERM_LANGUAGE.md` §2, `OPERATIONAL_SEMANTICS.md` §2 cards, §4.34, and
§4.35) build a presented state from finite data. `A-PRODUCT`, `A-DOUBLE`,
and `A-CONCAT` take presented states among their inputs, and the output is
still a new state on a fresh namespace: no cell of an input state is
carried to it. `L-NESTED-CSS` was admitted on the same terms on 2026-11-13
(`OPERATIONAL_SEMANTICS.md` §4.36). So nothing is carried: every
cell below is computed exactly over the constructed display or starts
unknown. Distances are the point of the explicit-hypothesis discipline the
2026-11-10 disposition asked for: no constructor computes or asserts a
distance, the constructed state's ledger starts at $[0, +\infty)$ in every
sector and for the full distance, a lower endpoint rises only through a
supplied bound with a source (recorded as an `input lower bound` condition),
and an upper endpoint only through a witness validated in the state (§2c).
The consumer realizes this as `DistanceLedger.for_constructed`.

| Constructor | $n$ | $k$ | $w$, Tanner components, $r$ | $d$, $d_X$, $d_Z$ |
| --- | --- | --- | --- | --- |
| `L-HGP` | $n_1 n_2 + m_1 m_2$, exact | $k_1 k_2 + k_1^{T} k_2^{T}$, exact (§4.34) | recomputed exactly over the constructed display; $r$ only under a supplied honest layout (§2d.3) | `[0, +\infty)` by default; **conditional** (§2g.1, §4.45): $d_X \ge \min(\ell(C_2), \ell(C_1^T))$ and $d_Z \ge \min(\ell(C_1), \ell(C_2^T))$ from supplied sourced classical factor bounds (Tillich–Zémor 2014); upper endpoints from validated Kronecker witness lifts $c_1 \otimes e_j, e_a \otimes c_2^T, e_i \otimes c_2, c_1^T \otimes e_b$ |
| `L-LIFTED` | $|G| (n_A n_B + m_A m_B)$, exact (§4.34, §4.44); with a subgroup argument $[G:H] (n_A n_B + m_A m_B)$, exact (§4.49) | rank bookkeeping of the display, exact, no closed form | as above | no automatic cell; $[0, +\infty)$ until a sourced bound or validated witness is supplied |
| `L-GROUP-ALGEBRA` | $2|G|$, exact | $2|G| - \mathrm{rank}[L(a) \mid R(b)] - \mathrm{rank}[L(b) \mid R(a)]$, exact (reducing to $2(|G| - \mathrm{rank}[L(a) \mid L(b)])$ when $G$ is abelian; §4.34, §4.44) | as above | no automatic cell; as above |
| `A-CONCAT` | $n_{\mathrm{in}} n_{\mathrm{out}}$, exact | $k_O$, exact (§4.34) | as above | `[0, +\infty)` by default; **conditional** (§2g.1, §4.45): $d_\sigma \ge \max(\lceil \ell_\sigma(O)/k_{\mathrm{in}} \rceil, \ell_{\mathrm{block},\sigma}(O)) \cdot \ell_\sigma(I)$ from supplied sourced outer/inner bounds ($\ell_\sigma(O) \cdot \ell_\sigma(I)$ when $k_{\mathrm{in}}=1$); upper endpoints from validated block-representative lifts of outer logical witnesses; the §2a tower price provider supplies deletion and exposure prices from level data |
| `A-PRODUCT` | $m_Z^A m_X^B + n_A n_B + m_X^A m_Z^B$, exact | $k_A k_B$, exact (§4.35) | as above | `[0, +\infty)` by default; **conditional** (§2g.1, §4.45): $d_\sigma \ge \ell_\sigma$ from a display-certified sourced Audoux–Couvreur factor-overlap bound (direct `(d_X, d_Z)`, or multiplicative $\underline d_{A,\sigma}\underline d_{B,\sigma}$ when certified for the chosen displays); upper endpoints from validated central-block Kronecker witness lifts $w_A \times w_B$ of weight $\mathrm{wt}(w_A)\mathrm{wt}(w_B)$. Distances may depend on the factor displays (§4.35) |
| `A-DOUBLE` | $2 n_C$, exact | rank bookkeeping of the display, exact; $2 k_C$ for the empty wiring (§4.35) | as above | `[0, +\infty)` by default; **conditional** (§2g.1, §4.45): $d_\sigma \ge \ell_\sigma$ from supplied sourced cover bounds (or $\ell_\sigma(C)$ / $\min(\ell_X(C),\ell_Z(C))$ for the empty wiring); upper endpoints from validated sheet witness lifts |
| `L-BALANCED` | the number of orbits on the two families of index pairs, exact (§4.35, §4.44) | rank bookkeeping of the display, exact, no closed form | as above | no automatic cell; as above |
| `L-TANNER` | the supplied $n$ | rank bookkeeping of the display, exact, no closed form | as above | no automatic cell; as above. No expansion hypothesis is an input |
| `L-TILE` | the number of site classes, exact | rank bookkeeping of the display, exact, no closed form | as above | no automatic cell; as above |
| `L-NESTED-CSS` | the common number of columns, exact | $n - \mathrm{rank}(H_X) - \mathrm{rank}(H_Z)$, exact (§4.36) | as above | `[0, +\infty)` by default; **conditional** (§2g.1, §4.45): $d_X \ge \ell(\ker H_Z)$ and $d_Z \ge \ell(\ker H_X)$ from supplied sourced classical kernel distance bounds (§4.36); upper endpoints from validated classical codeword witnesses in $\ker H_{\bar\sigma} \setminus \mathrm{rowspan}(H_\sigma)$ |
| `L-MAPPING-CONE` | $\dim A_0 + \dim B_1$, exact | rank bookkeeping of the display, exact; equivalently $\dim Z(B) - \dim f_1(Z(A)) + \dim \ker \bar f_0$ (§4.41) | as above | conditional: $d_Z = \min(D_B, D_A)$ and $d_X$ the same for the transposed input; $D_A$, $D_B$ as defined in `OPERATIONAL_SEMANTICS.md` §4.41; lower endpoint $\min(\ell_B, \ell_A)$ from supplied sourced bounds, with $\ell_B$ alone when $\bar f_0$ is injective; upper witnesses from $B$ (§4.41). No constructor computes a distance |
| `L-EMPTY` | $0$, exact (§4.43) | $0$, exact (§4.43) | $w=0$, $\kappa=0$, $r=0$ when layout supplied | no §2g cell; $[0, +\infty)$ per `DistanceLedger.for_constructed` (semantic $d_X=d_Z=d=+\infty$ at $k=0$, §4.43) |
| `L-FREE` | $|Q|$, exact (§4.43) | $|Q|$, exact (§4.43) | $w=0$, $\kappa=|Q|$, $r=0$ when layout supplied | no §2g cell; $[0, +\infty)$ per `DistanceLedger.for_constructed` (semantic $d_X=d_Z=d=1$ for $Q\neq\varnothing$, $+\infty$ for $Q=\varnothing$; any singleton witness $\{q\}$ tightens the upper endpoints to $1$, §4.43) |
| `A-PULLBACK` | $|Q_1 \times_{Q_I} Q_2|$, exact (§4.43) | rank bookkeeping of the display, exact, no closed form | as above | no cell; as above. Naive lower bound $d(A\times_C B)\ge\min(d_A,d_B)$ is `false` (`the left-in-papers note` §6.3) |
| `A-PUSHOUT` | $|Q_1 \sqcup_{Q_S} Q_2|$, exact (§4.43) | rank bookkeeping of the display, exact, no closed form | as above | no cell; as above. General pushouts with $S\neq 0$ can drop distance (`the left-in-papers note` claims 3.5, 4.1) |
| `L-PAIR-PARTITION` | $L \cdot p$, exact (§4.46) | rank bookkeeping of the display, exact, no closed form | recomputed exactly over the constructed display; $r$ only under a supplied honest layout (§2d.3) | no cell; $[0, +\infty)$ until a sourced bound or validated witness is supplied (for CPM-PP, the structural factorial ceiling $d \le (J+1)!$ of Okada–Kasai Thm 3 is an external bound a consumer may name; APM-PP escapes that ceiling, §4.46) |
| `PP-SCALE` | $L \cdot P$, exact (§4.47) | $L \cdot P - \mathrm{rank}(H_X') - \mathrm{rank}(H_Z')$, exact (§4.47) | $w = L$ carries (each natural row has one 1 in each of the $L$ block columns); $r$ and Tanner connectivity recomputed from the generated presentation | `unavailable` automatically unless a supplied interval $[d_{\mathrm{lo}}, d_{\mathrm{hi}}]$ is recorded as a priced hypothesis, in which case `conditional` (§2l): ledger starts at $[0, +\infty)$ and the supplied interval sets the endpoints as a trusted input (consumer checks shape and witness consistency only; no automatic distance rule) |

### 2g.1 Conditional distance cells and factor-to-child witness lifting for admitted constructors

For the five constructors with established parameter theorems (`L-HGP`,
`L-NESTED-CSS`, `A-CONCAT`, `A-PRODUCT`, `A-DOUBLE`), `OPERATIONAL_SEMANTICS.md`
§4.45 derives both the **conditional lower-bound cells** from consumer-supplied,
sourced factor hypotheses and the **deterministic factor-to-child witness-lifting
maps**. In keeping with `OBL-PRICED-INPUT-SEMANTICS`, no constructor computes or
verifies a distance lower bound: supplied factor bounds are trusted inputs whose
sources and cell conditions are recorded on the constructed `DistanceLedger`,
whereas lifted candidate witnesses are validated against the constructed state
via `validate_witness` (§2c) before tightening any upper endpoint.

| Constructor | Conditional lower-bound cell ($d_X, d_Z, d$) | Sourced factor hypotheses (consumer input) | Deterministic factor-to-child witness lifting (validated via `validate_witness`) | Evidence status |
| --- | --- | --- | --- | --- |
| `L-HGP` | $d_X \ge \min(\ell_2, \ell_1^T)$, $d_Z \ge \min(\ell_1, \ell_2^T)$, $d \ge \min(d_X, d_Z)$ | $\ell_1 \le d(\ker H_1)$, $\ell_2 \le d(\ker H_2)$, $\ell_1^T \le d(\ker H_1^T)$, $\ell_2^T \le d(\ker H_2^T)$ (Tillich–Zémor 2014) | Left-block $c_1 \otimes e_j$ ($e_j \notin \mathrm{rowspan}\,H_2$) and right-block $e_a \otimes c_2^T$ ($e_a \notin \mathrm{colspan}\,H_1$) for $Z$; $e_i \otimes c_2$ and $c_1^T \otimes e_b$ for $X$ (`lift_hgp_witnesses`, §4.45) | **`conditional`** (lower bound); **`proved`** (witness validity once checked) |
| `L-NESTED-CSS` | $d_X \ge \ell_X$, $d_Z \ge \ell_Z$, $d \ge \min(\ell_X, \ell_Z)$ | $\ell_X \le d(\ker H_Z)$, $\ell_Z \le d(\ker H_X)$ (§4.36, §4.45) | Classical codewords $w_X \in \ker H_Z \setminus \mathrm{rowspan}\,H_X$ and $w_Z \in \ker H_X \setminus \mathrm{rowspan}\,H_Z$ directly on $Q$ (`lift_nested_witnesses`, §4.45) | **`conditional`** |
| `A-CONCAT` | $d_\sigma \ge \max(\lceil \ell_\sigma(O)/k_{\mathrm{in}}\rceil, \ell_{\mathrm{block},\sigma}(O)) \cdot \ell_\sigma(I)$, $d \ge \min(d_X, d_Z)$ | $\ell_\sigma(O) \le d_\sigma(O)$, $\ell_\sigma(I) \le d_\sigma(I)$, optional $\ell_{\mathrm{block},\sigma}(O) \le d_{\mathrm{block},\sigma}(O)$ (§4.45) | Block-by-block lift of each outer $\sigma$-logical witness $w_O$ through the inner dual logical representatives $\mathrm{rep}_{\sigma, p}$ (`lift_concat_witnesses`, §4.45) | **`conditional`** |
| `A-PRODUCT` | $d_X \ge \ell_X$, $d_Z \ge \ell_Z$, $d \ge \min(\ell_X, \ell_Z)$ | Display-certified sourced Audoux–Couvreur factor-overlap bounds $\ell_X, \ell_Z$ (direct `(d_X, d_Z)`, or multiplicative $\ell_\sigma = \underline d_{A,\sigma}\underline d_{B,\sigma}$ when the display certificate licenses multiplicative scaling; Audoux–Couvreur 2019, §4.45) | Central-block Kronecker lift $w_A \times w_B \subseteq Q_A \times Q_B$ (at offset $m_Z^A m_X^B + i n_B + j$) of weight $\mathrm{wt}(w_A)\mathrm{wt}(w_B)$ (`lift_product_witnesses`, §4.45) | **`conditional`** |
| `A-DOUBLE` | $d_X \ge \ell_X$, $d_Z \ge \ell_Z$, $d \ge \min(\ell_X, \ell_Z)$ | Sourced cover bounds $\ell_X, \ell_Z$ (or $\ell_\sigma(C)$ / $\min(\ell_X(C),\ell_Z(C))$ for the empty wiring, §4.45) | Sheet-$0$, sheet-$1$ (sector-swapped if `conjugate`), and two-sheet diagonal lifts of parent witnesses $w_C$ (`lift_double_witnesses`, §4.45) | **`conditional`** |

A supplied bound that contradicts a validated witness is a failed premise
(`no_derivation`), as everywhere in §2b. For `A-DOUBLE`, `L-TANNER`,
`L-TILE`, `L-NESTED-CSS`, `L-MAPPING-CONE`, `A-PULLBACK`, `A-PUSHOUT`, and `L-PAIR-PARTITION` the cells above are stated for an evaluation: an input whose
natural rows do not commute (or whose interface maps fail the CSS-morphism premise) has no derivation and no cells.


## 2h. Gate-realization judgment rows: codespace preservation, frame reading, and transport by weakening (admitted 2026-11-18; Rows C–F 2026-11-26)

Rows A and B were admitted to `stdCSS-3` / `v0.3.0` on 2026-11-18, and Rows
C–F together with the any-angle `C-ADD-CHECK` cell of Row A were admitted on
2026-11-26 (issue #572) and folded into `stdCSS-3` / `v0.3.2` by maintainer
decision (2026-11-26); derivations at
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4.37 and
`GATE_REALIZATION_ROWS.md`.
Source statements: Nelson, Danageozian, Cao, Economou, and Barnes, arXiv
2610.17612v1 (Theorem 1 and Corollaries 2 and 3), re-derived for a CSS display
in §4.37.

**No operation identifier is minted for a logical gate.** A logical gate
$U = \prod_{j=1}^{q} \exp(i\epsilon_j \theta_j G_j)$ (with pairwise commuting
Hermitian Pauli generators $G_1, \dots, G_q$ on $Q$, signs
$\epsilon_j \in \{+1, -1\}$, and angles $\theta_j \ge 0$) leaves the state
$C = (Q, X, Z, \mathsf{pres}, \mathsf{used})$ unchanged and defines no state
update, so it never reaches [`TAXONOMY.md`](TAXONOMY.md) §3.8's bar for a
taxonomy operation identifier. A gate is an operator parameter of a judgment
predicate, not a state field or a command.

**Row A — Gate survival ($\mathsf{preserves}_U$, assertion-language extension,
axis 3).** For a fixed gate $U$ on $Q$, the predicate $\mathsf{preserves}_U(C)$
asserts that $U$ maps the codespace $\mathcal{V}(C)$ (the common $+1$
eigenspace of the displayed rows) into itself. Because $\mathcal{V}(C)$ depends
only on the stabilizer group $\mathcal{S}(C) = \langle X, Z \rangle$, the
carrier of $\mathsf{preserves}_U$ is `span`. On a CSS display, by Lemma 1 of
`OPERATIONAL_SEMANTICS.md` §4.37, $i^t X(a) Z(b) \in \mathcal{S}(C)$ iff
$t = 0$, $a \in X$, and $b \in Z$ (so $-I \notin \mathcal{S}(C)$ and the phase
of any product of displayed CSS rows is determined by `(sector, support)`
without a per-row sign field). At $\theta_j = \pi/4$ for all $j$, by Lemma 3
of §4.37, $U^\dagger g U = g V_g$ where
$V_g = \prod_{j \in J(g)} i\epsilon_j G_j$ over the set $J(g)$ of generators
anticommuting with row $g$, and $\mathsf{preserves}_U(C)$ holds iff
$V_g \in \mathcal{S}(C)$ for every displayed row $g$ — a decidable polynomial-time
test over the display (two $\mathbb{F}_2$ span-membership tests and one phase
check per displayed row). At every angle, by Lemma 7 of §4.37,
$\mathsf{preserves}_U(C)$ holds iff, for every displayed row $g$,
$\Phi_{J(g)}(l) = \sum_{j\in J(g)}\epsilon_j\theta_j l_j \in \pi\mathbb{Z}$
for every sign pattern $l$ in $\Lambda(\mathcal{S}(C), J(g))$, the patterns of
eigenvalues of $(G_j)_{j\in J(g)}$ that occur on $\mathcal{V}(C)$: those
satisfying $\prod_{j\in T} l_j = c_T$ whenever $c_T\prod_{j\in T}G_j\in
\mathcal{S}(C)$ (Lemma 6). The test ranges over at most $2^{\lvert J(g)\rvert}$
patterns and finds the relations by at most $2^{\lvert J(g)\rvert}$
membership tests per row: polynomial in the display for a fixed number of
generators, exponential in the number anticommuting with the row. It is a
decision procedure for *rational angles* $\theta_j = a_j\pi$,
$a_j \in \mathbb{Q}_{\ge 0}$, on which $\Phi \in \pi\mathbb{Z}$ is the
integrality of a rational, decided exactly with no floating-point tolerance
(§4.37, *Angle domain*). For a gate with an angle outside $\pi\mathbb{Q}$ no
decision procedure is admitted, and a cell that needs one is
`not yet defined` (issue #572).

| Transition | Verdict for $\mathsf{preserves}_U$ | Condition / scope | Evidence |
| --- | --- | --- | --- |
| `C-SKIP` | carries | none | `[proved]` (§4.37) |
| `C-ADD-CHECK`, adding row $s$, every generator $G_j$ commuting with $s$ | carries at every angle $\theta_j \ge 0$ | none beyond the stated commutation ($U$ commutes with $s$) | `[proved]` (§4.37) |
| `C-ADD-CHECK`, adding row $s$, all angles $\theta_j = \pi/4$ | carries iff $V_s \in \mathcal{S}(C')$ for the child $C'$ | one stabilizer-membership test at the added row $s$ (contains the commuting case, where $J(s) = \varnothing$ and $V_s = I$) | `[proved]` (§4.37) |
| `C-ADD-CHECK`, adding row $s$, some generator anticommuting with $s$ and some angle $\theta_j \neq \pi/4$ | carries iff $\Phi_{J(s)}(l) \in \pi\mathbb{Z}$ for every $l \in \Lambda(\mathcal{S}(C'), J(s))$ | one test at the added row $s$ (Corollary 7.1, which contains the two rows above), decided for rational angles $\theta_j\in\pi\mathbb{Q}$ by at most $2^{\lvert J(s)\rvert}$ sign patterns and membership tests, polynomial in the display for a fixed number of generators; `not yet defined` as a decision for other angles; its reading in a frame is the source's eigenvalue condition (Row C) | `[proved]` (§4.37, issue #572) |
| `C-DELETE-CHECK` | does not carry | refuted by counterexample (§4.37: deleting $X_0 X_1$ from rows $X_0 X_1, Z_0 Z_1$ under $G_1 = X_0, G_2 = X_1$, $\epsilon = (+1, -1)$ at $\pi/4$); the child's own Lemma 7 test over its remaining rows decides $\mathsf{preserves}_U(C')$ at every rational angle | `[false]` (§4.37) |
| `C-DIRECT-SUM`, gate $U$ supported on one summand | carries | generators of $U$ supported on $Q_A$ (or $Q_B$); instance of the Frame schema (§7.2.3) | `[proved]` (§4.37) |
| `C-SEQUENCE` | carries by composition | where each step's cell carries | `[proved]` (§4.37) |

**Scope of Row A.** Addressability and the logical action of an accepted
gate, which read a logical frame, are Rows D–F below, and the reading of
the non-$\pi/4$ `C-ADD-CHECK` cell in a frame is Row C (issue #572). Every
row in this section is stated for a CSS display only: mixed (non-CSS) rows
require an independent sign bit per row (`TAXONOMY.md` §4.3, refused for
`v0.3.0`), without which Lemma 1 fails. `E-GRAFT` and the Gate 6 transitions
carry no positive cell for $\mathsf{preserves}_U$ or for Rows C–F; in particular,
`E-SPLIT` does not carry $\mathsf{preserves}_U$ (`false`, by the $t=1$
`C-DELETE-CHECK` counterexample of §4.37, see §4.48), while
$\omega \ge \lceil L_d'/2 \rceil$ weakens at `E-SPLIT` from the child's lower
endpoint $L_d'$.

**Row B — Equal-syndrome generator weight floor ($\omega$) and transport by
weakening (axis 3).** A family of pairwise commuting Hermitian Pauli generators
$G_1, \dots, G_q$ ($q \ge 2$) is *equal-syndrome* on $C$ when all its members
have one common nonempty syndrome on the displayed rows of $C$, and
*nontrivial* on $C$ when some product $G_1 G_j$ is not in $\mathcal{S}(C)$ up
to sign. With $w_{\max} = \max_{1 \le j \le q} \mathrm{wt}(G_j)$, define
$\omega(C)$ as the least $w_{\max}$ over nontrivial equal-syndrome families on
$C$, and $+\infty$ when none exists. Its carrier is `span`. By Lemma 4 of
`OPERATIONAL_SEMANTICS.md` §4.37, every well-formed CSS state $C$ satisfies

$$
\omega(C) \ge \lceil d(C)/2 \rceil.
$$

**Weakening transport (recorded carry shape).** At any state whose consumer
ledger for the full distance $d$ has lower endpoint $\ell = L_d$, the state
carries the lower bound $\omega(C) \ge \lceil \ell/2 \rceil$ (and $+\infty$
when $L_d = +\infty$ at $k = 0$). Because $\ell \mapsto \lceil \ell/2 \rceil$
is nondecreasing on $\mathbb{N} \cup \{+\infty\}$, the bound is sound at every
state where the interval of $d$ is sound and is monotone in the lower-endpoint
refinement order $\sqsubseteq^{\mathrm{low}}$ (§9.1):

| Transition | Effect on the carried floor $\omega \ge \lceil L_d/2 \rceil$ |
| --- | --- |
| `C-SKIP` | unchanged ($L_d' = L_d$) |
| `C-ADD-CHECK` | does not decrease ($L_d' \ge L_d$) |
| `C-DELETE-CHECK` | recomputed from the child's lower endpoint $L_d'$ ($0$ unpriced, $\min(L_d, w_{\mathrm{del}}, w_{\mathrm{exp}})$ priced): **the floor weakens**, and the parent's value does not substitute (§4.37, nine-qubit Shor-code deletion counterexample where $d : 3 \to 1$ and $\omega : 2 \to 1$) |
| `C-DIRECT-SUM` | recomputed from $\min(L_d^A, L_d^B)$ |
| `C-SEQUENCE` | recomputed from $L_d$ at each state along the chain |

This carry shape — **transport by weakening**: a bound on one property whose
carried content is the image $f(L_q)$ of another property's carried lower
endpoint $L_q$ under a nondecreasing map $f$, re-read at each state and never
substituted from the parent — is recorded as structural schema 6 in §7.2 and
implemented on the consumer ledger as
`DistanceLedger.equal_syndrome_weight_floor` (`machine/intervals.py`). Neither
Row A nor Row B modifies any distance interval endpoint ($d, d_X, d_Z$).

**Rows C–F — Frame-reading predicates (assertion-language extension, axis 3;
admitted 2026-11-26, `stdCSS-3` / `v0.3.2`, issue #572).** Derivations:
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4.37, Lemmas 5–11.
A *frame* $F$ is a logical-witness field $\mathsf{log}$
([`STATE_MODEL.md`](STATE_MODEL.md) §1a) supplied with the state as a
parameter of the predicate, like the gate. No part of
$C = (Q, X, Z, \mathsf{pres}, \mathsf{used})$ changes, no operation
identifier is minted, and the consumer ledger does not carry the frame. Its
eigenvalue reading (§1a): $F$ is *consistent* on $C$ when its entries
commute pairwise (F1) and its eigenvalues respect every relation among the
entries of one sector modulo the displayed rows (F2). Then the *frame group*
$\mathcal{S}_F(C)$, generated by $\mathcal{S}(C)$ and the signed entry
operators $\varepsilon_e f_e$, is a stabilizer group, and the *frame sector*
$\mathcal{V}_F(C)$, the vectors of $\mathcal{V}(C)$ on which every entry
takes its eigenvalue, is nonzero (Lemma 8). A frame-indexed predicate is
stated only for a frame consistent on its state (Rows C and D) or well
formed on it (Rows E and F).

| Row | Predicate | Holds iff | Carrier |
| --- | --- | --- | --- |
| C | $\mathsf{preserves}_U(C\mid F)$: $U$ maps $\mathcal{V}_F(C)$ into $\mathcal{V}(C)$ | $\Phi_{J(g)}(l)\in\pi\mathbb{Z}$ for every displayed row $g$ and every $l\in\Lambda(\mathcal{S}_F(C),J(g))$ (Lemma 9) | span, frame parameter |
| D | $\mathsf{phase}_U(C\mid F)=z$: $U\psi=z\psi$ on $\mathcal{V}_F(C)$, the logical action of $U$ on a frame sector | $\exp(i\Phi(l))=z$ for every $l\in\Lambda(\mathcal{S}_F(C),\{1,\dots,q\})$ (Lemma 10); for rational angles $z=\exp(i\pi r)$ is named by a rational $r\in[0,2)$ | span, frame parameter |
| E | $\mathsf{image}_U(C;e)\equiv P$: $U^\dagger f_eU\psi=P\psi$ on $\mathcal{V}(C)$, for an entry $e$; with $\mathsf{preserves}_U(C)$, the logical action of $U$ by conjugation | all angles $\pi/4$: $P^{-1}f_eV_{f_e}\in\mathcal{S}(C)$; every angle with $P=\eta f_e$, $\eta=\pm1$: $\exp(2i\Phi_{J(f_e)}(l))=\eta$ for every $l\in\Lambda(\mathcal{S}(C),J(f_e))$ (Lemma 11); other pairs `open` | span, frame parameter |
| F | $\mathsf{addresses}_U(C;F,A)$: $\mathsf{preserves}_U(C)$, and $U$ commutes on $\mathcal{V}(C)$ with $f_e$ for every entry $e$ of $F$ outside $A$ | Lemma 7, and Row E with $P=f_e$ for each entry outside $A$ | span, frame parameter |

**Angle domain and cost.** Rows C–F, like Row A, are decision procedures
for rational angles $\theta_j\in\pi\mathbb{Q}$, where every test is exact
rational arithmetic (§4.37, *Angle domain*); for other angles their
decision is `not yet defined`. Each test enumerates at most $2^{m}$ sign
patterns and finds the relations among the generators by at most $2^{m}$
membership tests, with $m$ the number of generators involved ($\lvert J(g)\rvert$
for Rows C and F, $\lvert J(f_e)\rvert$ for Row E, $q$ for Row D): polynomial in
the display for a fixed number of generators. Row C asserts that the sector
is mapped into $\mathcal{V}(C)$, not into itself; that the sector is mapped
into itself follows from Row D, not from Row C.

**The eigenvalue condition and the source's Theorem 1.** When the
transported frame $F'$ *resolves* $J(s)$, so that every zero-syndrome
product $L_j=G_{j_0}G_j$ ($j\in J(s)$) acts on the child's sector as its
eigenvalue $l_j^{(F')}$, Row C's `C-ADD-CHECK` cell is the single equation
$\sum_{j\in J(s)}\epsilon_j\theta_j\,l_j^{(F')}\in\pi\mathbb{Z}$
(Corollary 9.1): the source's condition, with the logical sector named by
the frame. For a family with one common nonempty syndrome that $F$
resolves, $\mathsf{preserves}_U(C\mid F)$ and
$\mathsf{phase}_U(C\mid F)=(-1)^{\Phi^{(F)}/\pi}$ hold iff
$\Phi^{(F)}=\sum_j\epsilon_j\theta_j l_j^{(F)}\in\pi\mathbb{Z}$
(Corollary 10.1): the source's Theorem 1 in CSS form, a diagonal logical
gate. Row A's frame-free cell is the conjunction of Row C's cell over every
consistent eigenvalue assignment (Lemma 9), which is why it needs no frame.

**Addressability.** Row F states that the accepted gate fixes every logical
operator that $F$ names outside $A$. When the classes of those entries span
a subspace of the logical space on which the commutation form is
nondegenerate, they generate the logical algebra of a tensor factor of
$\mathcal{V}(C)$, and the gate acts as the identity on that factor: it acts
on the other logical qubits only. The field carries no pairing of $X$- and
$Z$-logicals into qubits, so that reading depends on the choice of $F$ and
$A$.

| Transition | Row C | Row D | Row E | Row F | Evidence |
| --- | --- | --- | --- | --- | --- |
| `C-SKIP` | carries | carries | carries | carries | `[proved]` (§4.37) |
| `C-ADD-CHECK`, adding row $s$, frame transported to $F'$ consistent on $C'$, $\mathcal{S}_F(C)\subseteq\mathcal{S}_{F'}(C')$ | carries iff $\Phi_{J(s)}(l)\in\pi\mathbb{Z}$ for every $l\in\Lambda(\mathcal{S}_{F'}(C'),J(s))$ | carries, same $z$ | carries for every entry the transport keeps | $\mathsf{addresses}_U(C';F',A\cap F')$ holds iff Row A's test at $s$ | `[proved]` (§4.37) |
| `C-ADD-CHECK`, $F'$ consistent on $C'$, $\mathcal{S}_F(C)\not\subseteq\mathcal{S}_{F'}(C')$ | does not carry | does not carry | as above | as above | `[false]` (one-qubit counterexample, §4.37); Lemmas 9 and 10 at the child decide Rows C and D |
| `C-ADD-CHECK`, $F'$ not consistent on $C'$ | `not yet defined` | `not yet defined` | as above | as above | the predicates of Rows C and D are not stated at the child (§4.37); Rows E and F need only a well-formed frame |
| `C-DELETE-CHECK` | does not carry | does not carry | does not carry | does not carry | `[false]` (three-qubit counterexample, §4.37); Lemmas 9–11 at the child decide it |
| `C-DIRECT-SUM`, $C_1\oplus C_2$, $U$ supported on $Q_1$, frame $F_1\oplus F_2$ extended by zero | carries | carries, same $z$ | carries; an entry of $F_2$ has image $f_e$ | carries for $A\subseteq F_1$ | `[proved]` (§4.37) |
| `C-SEQUENCE` | carries by composition of the step cells | by composition | by composition | by composition | `[proved]` (§4.37) |

The inclusion $\mathcal{S}_F(C)\subseteq\mathcal{S}_{F'}(C')$ holds when the
transport keeps every entry. It fails when the transport drops an entry
that anticommutes with $s$, drops an entry that $s$ brings into the span
with eigenvalue $-1$, or merges two entries whose eigenvalues disagree; the
child's sector is then not inside the parent's, and Lemma 9 or 10 at the
child decides it. The transported frame can also fail to be consistent:
the transport discards no entry for a new relation among the survivors, so
three entries whose vectors $s$ brings into one relation with eigenvalue
product $-1$ all survive and violate F2 (§4.37); Rows C and D are then not
stated at the child.

**What Rows C–F do not define.** The conjugation image for a target other
than $\pm f_e$ at angles that are not all $\pi/4$ (`open`: away from
$\pi/4$ the image of a Pauli operator is in general not one). A pairing of
frame entries into logical qubits (the field has none). Mixed ($Y$-type)
frame entries, since the field's entries are single-sector vectors; a
zero-syndrome product with a mixed logical part may then have no resolving
frame, and the general form of the test applies. Cells for `E-GRAFT` and
the Gate 6 transitions. None of Rows C–F modifies $C$, a distance interval,
or the frame.

## 2i. Monomial-quotient specialization of `A-QUOTIENT` (conditional)

The monomial quotient is a specialization of `A-QUOTIENT`
([`TAXONOMY.md`](TAXONOMY.md) §2.15; source: Hsin, arXiv 2611.09538v1 §3.3,
`PRIOR_ART.md`), not an admitted constructor
(`A-QUOTIENT` remains `taxonomy-only` at rung 1) and not a grammar production.
Because only a summary of Hsin's §3.3 transfer theorem is recorded in this
repository (not the theorem's full statement, hypotheses, or bound directions),
**this section records the existence of the transfer-theorem conditional slot
and provides no usable automatic bound or $k$ formula**: under the
priced-hypothesis boundary (§2c, §2g), the consumer holds `[0, +∞)` unless the
caller explicitly supplies a sourced lower bound (`input lower bound`) or a
validated child witness.

| Cell / Property | Statement | Hypothesis (consumer-supplied) | Source | Status |
| --- | --- | --- | --- | --- |
| Logical qudits ($k$) | Existence of a transfer-theorem slot for quotient logical dimension; **no usable $k$ formula is recorded in this repository** | supplied quotient $k$ and Tate-cohomology count with source provenance (never computed or validated by the consumer) | Hsin, arXiv 2611.09538v1 §3.3 (`PRIOR_ART.md`; statement not reproduced here) | conditional slot (existence recorded; no usable formula) |
| Logical operators | Existence of a transfer-theorem slot where parent logicals descend along $\pi$ and Tate cohomology counts new logicals (candidate "does not carry / new" record); **no automatic transport rule is recorded** | supplied logical descent / Tate-cohomology count with source provenance | Hsin, arXiv 2611.09538v1 §3.3 (`PRIOR_ART.md`; statement not reproduced here) | conditional slot (existence recorded; no usable rule) |
| Distance bounds ($d_X, d_Z, d$) | **No usable distance bound from the transfer theorem is recorded in this repository** (direction and hypotheses are not stated here); intervals stay `[0, +∞)` unless raised via general §2c/§2g inputs | explicit sourced lower bound (`input lower bound`, §2c/§2g) or validated child witness (§2c) | Hsin, arXiv 2611.09538v1 §3.3 (`PRIOR_ART.md`); §2b, §2c, §2g | conditional slot (no usable bound; §2c/§2g defaults only) |
| CSS-preserving instance | Pure qudit-permutation actions, or monomial-Clifford actions whose single-qudit Cliffords $c_g$ preserve both the $X$ and $Z$ sectors individually (no $X \leftrightarrow Z$ swap and no $X/Z$ mixing) | free monomial-Clifford action $(G, \{c_g\})$ and CSS parent (checked consumer-side by `machine/quotient_specialization.py`) | [`TAXONOMY.md`](TAXONOMY.md) §2.15 | applicability constraint (`A-QUOTIENT` has no calculus transition; checked consumer-side) |
| Duality-quotient instance | Global CSS sector swaps route to `E-LOCAL-HADAMARD` (`TAXONOMY.md` §2.12, $T = Q$); quotients leaving the ordinary-CSS model route to the deferred general-stabilizer extended-state layer (`TAXONOMY.md` §4, cf. §4.3/§4.4; refused for `v0.3.0`) | non-CSS / sector-swapping $c_g$ | [`TAXONOMY.md`](TAXONOMY.md) §2.12, §2.15, §4 | routing recorded, not a cell |

No constructor evaluates this cell: `A-QUOTIENT` remains `taxonomy-only`, and
no usable automatic distance bound or $k$ transfer rule enters the calculus from
this record.

## 2j. Family-level one-shot level-map transport (conditional, `v0.3.0` candidate)

Admitted to the `stdCSS-3` / `v0.3.0` candidate scope by dated maintainer
decision extending `SCOPE.md` §3–§4; the conditional rule is described in
the family-level transport note.
Source statements: Yuan, *One-Shot any Code*, arXiv:2610.02137v1 (Appendix A
Definitions 104, 106, 111, 113, 116, Eq. (249), Lemmas 117–118; Theorem 81 Eq. (1);
Remark 39). Equation numbers in parentheses are those of the HTML rendering of
arXiv:2610.02137v1; the PDF of the same version numbers the appendix (A1)–(A24).
Where a number is ambiguous, the statement is cited by definition or lemma
instead.

**No taxonomy operation identifier is minted.** Unlike a single-state transition
in $C = (Q, X, Z, \mathsf{pres}, \mathsf{used})$, the tower-level transport
statement governs a family-level renormalization / amplification across levels on
QLDPC seeds satisfying Hypotheses 102 ($|x \wedge z| = 2$ whenever $x \prec z$)
and 103 ($G^x$ connected for every $X$-check $x$, and the transpose condition
holds: the graph on the cells below each $Z$-check $z$ is connected for every
$z$); per [`TAXONOMY.md`](TAXONOMY.md) §3.8, that family-level rule enters the
judgment layer as a conditional transport rule rather than an operation identifier
or single-state command. (The single-code map $\bar\Gamma(C)$ itself is
constructor-candidate material — typed input, identifier allocation, well-formedness
obligation — but that ladder step is left for another PR; see the closing
paragraph of this section.)

**Transcribed finite construction (Appendix A, arXiv:2610.02137v1).** Let $C = (X \xrightarrow{\delta_X} Q \xrightarrow{\delta_Z} Z)$ satisfy Hypotheses 102–103 and let $R = V \to E$ be the $m$-vertex repetition path ($m \ge 2$, $|V|=m$, $|E|=m-1$, $\partial^R e = v_- + v_+$):

1. **Local graphs and cones (Definitions 104, 106).** For an $X$-check $x$, $G^x = V^x \to E^x$ has vertices $\{\succ x\}$ (cells $q, z \succ x$) and edges $qz$ for $q \prec z$. Its cone $K^x$ adds apex $x$, edges $xq, qz$, removes the cone edges $xz$, and merges the two triangles $xqz, xq'z$ (unique by $|x \wedge z|=2$) into a square face $xz$. For $q \in Q$, $G^q = \{z \succ q\}$ (no edges) and $K^q = \mathrm{cone}\,G^q$ has vertices $q, \{z \succ q\}$ and edges $qz$. For $z \in Z$, $G^z = \varnothing$ and $K^z = \{z\}$.
2. **Hollowed tensor and meta-checks (Definitions 111, 113).** For $u \in \{x, q, z\}$, define $Y^u = K^u \otimes V + G^u \otimes R$. Meta-check completions $\bar Y^u$ equip $Y^x$ with 3-cells $c(\gamma, e) = \sum_{z \in \gamma} xz \otimes \partial^R e + \sum_{qz \in \gamma} qz \otimes e$ for a simple-cycle basis $\{\gamma\}$ of $H_1(G^x)$, equip $Y^q$ with 2-cells $\gamma(z_0 z_i, e) = \sum_{u \in \{z_0, z_i\}} (qu \otimes \partial^R e + u \otimes e)$ (selecting an anchor $z_0 \succ q$ against each $z_i \neq z_0$), and extend $Y^z$ to $\bar Y^z = z \otimes R \cong R$.
3. **Induction step (Definition 116).** Gluing $\bar Y^x \xrightarrow{g^{qx}} \bar Y^q \xrightarrow{g^{zq}} \bar Y^z$ ($g^{zx} = 0$, $x \prec q \prec z$) forms the cochain complex $\bar\Gamma(C) \equiv X(\Gamma) \to Q(\Gamma) \to Z(\Gamma) \to MZ(\bar\Gamma)$ with:
 $$X(\Gamma) = \bigoplus_x Y^x_0, \qquad Q(\Gamma) = \bigoplus_x Y^x_1 \oplus \bigoplus_q Y^q_0,$$
 $$Z(\Gamma) = \bigoplus_x Y^x_2 \oplus \bigoplus_q Y^q_1 \oplus \bigoplus_z Y^z_0, \qquad MZ(\bar\Gamma) = \bigoplus_x \bar Y^x_3 \oplus \bigoplus_q \bar Y^q_2 \oplus \bigoplus_z \bar Y^z_1.$$
 The dual map is $\bar\Gamma_*(C) = \bar\Gamma(C^\top)^\top$, and the full level map is $\bar\Theta = \bar\Gamma_* \circ \bar\Gamma$.

**Conditional family-level transport cells.** The rows below describe one application of $\bar\Gamma$ (a full *level* is $\bar\Theta = \bar\Gamma_* \circ \bar\Gamma$, two applications); the tower-level threshold row is stated in the number of levels $\ell$.

| Property / Quantity | Judgment cell | Imported hypothesis / side condition | Source & Evidence status |
| --- | --- | --- | --- |
| Logical qubits ($k$) | $k(\bar\Gamma(C)) = k(C)$ and $k(\bar\Theta(C)) = k(C)$ (`equality`) | Hypotheses 102–103 and Lemma 118 cohomology isomorphism $H_Q(\bar\Gamma) \cong H_Q(C)$ (citation-based proof via [25] and Remark 114) | arXiv:2610.02137v1 Lemma 118 (Appendix A); **`conditional`** (imported framework hypothesis, never self-discharged) |
| Block length ($n$) | $n(\bar\Gamma(C)) = |\bigoplus_x Y^x_1 \oplus \bigoplus_q Y^q_0| > m \cdot n(C)$ per application of $\bar\Gamma$ (`lower-bound` on inflation; $n \cdot m^{\text{levels}}$ is only the bare sheet floor, not $n'$ or a block-length ceiling) | Finite cell enumeration of Definitions 104/106/111 and 116 | Finite cell count **`proved`** (dated derivation `spec/OPERATIONAL_SEMANTICS.md` §4.38, 2026-11-18); family tower cost scaling **`conditional`** |
| Check weights & degrees | $\mathfrak{w}_X' \le \max(\mathfrak{w}_X, \mathfrak{d}_Z + c, 2 + c)$, $\mathfrak{w}_Z' \le \max(\mathfrak{w}_Z, \mathfrak{d}_X + 2, 4)$, $\mathfrak{d}_X' \le \max(\mathfrak{d}_X, 2)$, $\mathfrak{d}_Z' \le \max(\mathfrak{d}_Z, 4)$ ($c = 3$ if $m=2$, $4$ if $m\ge 3$; the printed bound (251) uses $c$, while Lemma 117's proof notes the $z \otimes e$ rail has $Z$-degree $4$ for $m=2$ as well, giving $\max(\mathfrak{d}_Z, 4)$ in both cases) (`upper-bound`) | Hypotheses 102–103 ($|x \wedge z| = 2$, connected local graphs) | arXiv:2610.02137v1 Lemma 117 (Appendix A); **`conditional`** |
| Transport direction (RG decoding failure probability) | For $p < p_{\mathrm{RG}}$ and a tower of $\ell$ levels of the 3-sheet level map ($\bar\Gamma$ with $m = 3$ sheets; Remark 38 notes the 2-sheet construction has contraction $1/2$ and that 3 sheets, or two composed 2-sheet maps taken as one level, are used to obtain contraction below $1/2$, so the threshold statement is not claimed for a single 2-sheet level): $\Pr[T\text{ rounds fail}] \le O(T n)(p / p_{\mathrm{RG}})^{\Omega(\tilde\kappa^{-\ell})}$, equivalently the overhead form $\Omega(M^\alpha)$ with overhead $M = 3^\ell$ (`upper-bound` ceiling only, not a lower guarantee on distance or noise tolerance) | Theorem 81 threshold $p_{\mathrm{RG}} > 0$ and Remark 39 tower constants $(\Delta_{\mathrm{sh}}, \mathfrak{w}, \mathfrak{d}, \kappa, c_f, \varepsilon)$ with seed local triviality in the source sense: every error supported in one seed $X$-check or in one qubit with zero syndrome is a stabilizer (the condition $d_{\mathrm{err}}(C^{(0)}) > \mathfrak{w}_X(C^{(0)})$ is sufficient, not equivalent) | arXiv:2610.02137v1 Theorem 81 Eq. (1) and Remark 39; **`conditional`** (upper ceiling on failure probability only) |
| Amplified distance lower bound ($d, d_X, d_Z$) | **`unavailable`** (held at `[0, +\infty)` on any unpriced ledger; Lemma 118 and Theorem 81 license no distance lower bound beyond the failure-probability ceiling) | none (design boundary §3) | Design boundary (`VOCABULARY.md`); **`unavailable`** (`not-applicable`) |
| Finite-seed $\bar\Gamma(C)$ cohomology / sparsity check | Recorded separately (`machine/experiments/one_shot_level_map_transport.py`: `build_hollowed_tensor_level_map`, `empirical_gamma_bar_probe`, `repetition_tensor_code`) | Checked by `gf2.rank` on finite satisfying seeds (e.g. $2 \times 3$ and $3 \times 3$ toric codes); never upgrades `conditional` or `unavailable` | **`empirical`** (strictly separated from the conditional theorem) |

No constructor evaluates this cell: $\bar\Gamma$ as a single-code map is constructor-candidate material (typed input, identifier allocation, well-formedness obligation), but that ladder step is left for another PR. Here no term denotes $\bar\Gamma(C)$, so no evaluation yields a state these cells describe and no consumer path uses them; the tower-level threshold statement is the only family-level content, and no usable automatic distance bound or $k$ transport rule enters the calculus from this record.

## 2k. CSS-preserving column CNOT/SWAP transformation (`C-COLUMN-CNOT`, admitted 2026-11-18)

Admitted to the `stdCSS-3` candidate scope. The command
$\mathrm{cnotSwap}_U$, $U \in \mathrm{GL}(Q,2)$, transforms a presented CSS
state by

$$
 H_X \mapsto H_X U^{-1}, \qquad H_Z \mapsto H_Z U^{\mathsf{T}},
$$

which preserves the CSS orthogonality premise. It is a state transformer,
not a constructor: it rewrites an already-formed presented state.

**Output well-formedness.** The image of a well-formed CSS display under an
invertible column map is again a well-formed CSS display; `I1`–`I5` carry
(`OBL-WELL-FORMEDNESS-PRESERVATION`), with the per-invariant argument at
`OPERATIONAL_SEMANTICS.md` §4.42.

**Parameter effects.**

| Quantity | Effect |
| --- | --- |
| $n$ | $n' = n$ (exact) |
| $k$ | $k' = k$ (exact) |
| $w$ | recomputed on the image display, $w' = \max\{\mathrm{wt}(r') : r' \in \mathrm{rows}'\}$ |
| $r$ | recomputed on the image display |
| $d_\sigma$ | **window only**: $\lceil d_\sigma / \rho_\sigma^- \rceil \le d_\sigma' \le \rho_\sigma d_\sigma$ |

The four norms are decidable from $U$ and are **computed, not supplied**:

$$
\begin{aligned}
\rho_Z &= \max_j \mathrm{wt}(\text{column }j\text{ of }U), \\
\rho_Z^- &= \max_j \mathrm{wt}(\text{column }j\text{ of }U^{-1}), \\
\rho_X &= \max_j \mathrm{wt}(\text{column }j\text{ of }U^{-\mathsf{T}})
 = \max_i \mathrm{wt}(\text{row }i\text{ of }U^{-1}), \\
\rho_X^- &= \max_j \mathrm{wt}(\text{column }j\text{ of }U^{\mathsf{T}})
 = \max_i \mathrm{wt}(\text{row }i\text{ of }U).
\end{aligned}
$$

The $Z$ window uses $\rho_Z, \rho_Z^-$; the $X$ window uses $\rho_X, \rho_X^-$.
The distance cell is therefore not a priced hypothesis and W13 is not the
relevant rule: $U$ is the argument of the command, and the four quantities are
column and row weights of $U$ and $U^{-1}$, all decidable from the term. No
equality of distances is claimed, and the universal equality tail stays open.

**Hamming-weight non-invariance.** Under general $U \in \mathrm{GL}(Q,2)$
the Hamming weight of a check row is not preserved; a single column CNOT can
increase it. No generic CNOT layer is modelled as a zero-price operation:
its cost is recorded as the depth/sector hypothesis and never defaulted to
zero.

**Consumer rule.** The interval endpoints transform by the same window:
$[\lceil L_\sigma / \rho_\sigma^- \rceil,\; \rho_\sigma U_\sigma]$.
Parent-valid witnesses are not carried automatically; their supports must be
transported by the sector map and revalidated in the child.

## 2l. PP-SCALE family-level structural upper bound (conjectural, optional)

Recorded as a conditional family-level rule over PP-scale families with fixed
parameters, analogous to §2j. **No taxonomy operation identifier is minted**
(`TAXONOMY.md` §3.8). The paper's conjecture of a finite, size-independent
structural distance upper bound $B$, with improvement toward it as $P$ grows, is
scoped as an upper ceiling, marked `conjectural`, with monotonicity explicitly
not assumed. Family closure and amplified lower bounds remain `unavailable`
(`design/SCOPE.md` §4). Admission is a separate maintainer
decision.

| Property / Quantity | Judgment cell | Imported hypothesis / side condition | Source & Evidence status |
| --- | --- | --- | --- |
| Structural distance upper bound ($d, d_X, d_Z$) | upper ceiling $B$ only; monotonicity not assumed | $B$ supplied as a trusted (conjectural) input | Kasai, arXiv submit/8406448 §2.1; **`conjectural`** |
| Per-state supplied distance interval ($d, d_X, d_Z$) | $[d_{\mathrm{lo}}, d_{\mathrm{hi}}]$ recorded on the constructed ledger | sourced interval supplied as a priced hypothesis; consumer checks shape and witness consistency only | Kasai, arXiv submit/8406448 §3; **`conditional`** |
| Amplified family-level lower bound ($d, d_X, d_Z$) | `unavailable` unless a sourced per-state interval is supplied | none | `design/SCOPE.md` §4; **`not-applicable`** (`unavailable`) |

## 3. What `unavailable` means, and why it is a position
`unavailable` is **withheld by design commitment**. It is not ignorance, not a gap
awaiting closure, and not a synonym for `false`.

Two red-team passes fixed the boundary and the artifacts respect it:

- **The narrowing finding.** The `unavailable` row once covered deletion
 *distance*, which is true and derivable — $d'\le d$ follows from the two sector
 bounds by `MIN-ORDER` and `TRANSITIVITY`. The row was narrowed to **exact
 post-deletion distance values**, which are genuinely underivable.
- **The labelling finding.** `not_derivable` must be labelled for **one
 claim in a stated scope**, naming the rule system and the record date.

**Consequence, stated plainly:** the calculus will not be complete, and no
artifact may describe it as aiming at completeness in the MVP.

## 4. The `W13` half — absence of derivation as the witness

*Dispositioned 2026-10-11 (maintainer). Full analysis in
EXPRESSIBILITY.md.*

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

**The generator-referencing claim (2026-11-11; assertion-language
extension, candidate release `stdCSS-3`).** For a position $i$ of the
evaluation chain of a closed term, an identifier $r$, a sector $\sigma$, and
a support $S \subseteq Q$, the claim $\mathsf{gen}_i(r,\sigma,S)$ reads: the
state at position $i$ displays a row with identifier $r$, sector $\sigma$,
and support $S$. It refers to a generator by its identifier, so at a position
where $r$ is not displayed it has no denotation; the language has no negation,
and nothing false of a row is asserted there. Its rules are instantiation rows
of L3, one per transition of the evaluation chain:

| Step from position $i$ to $i+1$ | Rule | Reading |
| --- | --- | --- |
| none (position $0$) | concludes $\mathsf{gen}_0(r,\sigma,S)$ for every row $(r,\sigma,S)$ the input state displays | source: the input display is the base expression of the closed term |
| `C-ADD-CHECK` of $(\sigma,S)$ | concludes $\mathsf{gen}_{i+1}(r,\sigma,S)$ for the canonical mint $r$ of the input's `used` | source: the claim originates where its generator is minted |
| `C-SKIP` | from $\mathsf{gen}_i(r,\sigma,S)$ concludes $\mathsf{gen}_{i+1}(r,\sigma,S)$ | the state is unchanged |
| `C-DELETE-CHECK` of $r'$, with $r \ne r'$ | from $\mathsf{gen}_i(r,\sigma,S)$ concludes $\mathsf{gen}_{i+1}(r,\sigma,S)$ | the referenced generator survives |
| `C-ADD-CHECK` of any row | from $\mathsf{gen}_i(r,\sigma,S)$ concludes $\mathsf{gen}_{i+1}(r,\sigma,S)$ | displayed rows are kept |
| `C-DELETE-CHECK` of $r$ | **no rule** | the `W13` half |
| `E-GRAFT` at $q$ in sector $\tau$ along the chain $\vec r$, with $r \notin \vec r$ | from $\mathsf{gen}_i(r,\sigma,S)$ concludes $\mathsf{gen}_{i+1}(r,\sigma,S')$, where $S' = S \setminus \{q\}$ when $\sigma$ is the sector opposite to $\tau$ and $q \in S$, and $S' = S$ otherwise | the referenced generator survives; an opposite-sector row loses the grafted qubit |
| `E-GRAFT` at $q$ in sector $\tau$ along $\vec r = (r_1,\ldots,r_m)$ | concludes $\mathsf{gen}_{i+1}(r'_j,\tau,S_j \mathbin{\triangle} S_{j+1})$ for $1 \le j < m$, with $S_j$ the support of $r_j$ at position $i$ and $r'_j$ the $j$-th identifier the graft mints | source: the claim originates where the adjacent-product row is minted |
| `E-GRAFT` along $\vec r$, with $r \in \vec r$ | **no rule** | the graft retires the chain's generators: the `W13` half for the graft |
| `E-EXTEND` (any displayed row) | from $\mathsf{gen}_i(r,\sigma,S)$ concludes $\mathsf{gen}_{i+1}(r,\sigma,S)$ | the displayed rows are kept; the claim follows the identifier |
| `E-EXTEND` (minted row) | concludes $\mathsf{gen}_{i+1}(r',\sigma,S')$ for each row the command mints, with $r'$ the canonical mint, $\sigma$ the sector of the addition, and $S'$ its sorted support | source: the claim originates where the row is minted |
| `E-PEEL` at $q$ in sector $\tau$, with $r \ne r_{\mathrm{id}}$ | from $\mathsf{gen}_i(r,\sigma,S)$ concludes $\mathsf{gen}_{i+1}(r,\sigma,S')$, where $S' = S \setminus \{q\}$ when $\sigma$ is the sector opposite to $\tau$ and $q \in S$, and $S' = S$ otherwise | the referenced generator survives; an opposite-sector row loses the peeled qubit (the claim changes support). The shortening agrees with `peelSupport` because `E-PEEL` requires exactly one row of sector $\tau$ through $q$ (`peelSupport_eq_graftSupport_of_eval`) |
| `E-PEEL` at $q$ in sector $\tau$, with $r = r_{\mathrm{id}}$ | **no rule** | the peel retires the named row: no claim $\mathsf{gen}_{i+1}(r_{\mathrm{id}},\sigma,S)$ is derivable for any $\sigma, S$ — the `W13` half for the peel |
| `E-PUNCTURE` at $q$, with $q \notin S$ | from $\mathsf{gen}_i(r,\sigma,S)$ concludes $\mathsf{gen}_{i+1}(r,\sigma,S)$ | the referenced generator survives (its support does not contain $q$) |
| `E-PUNCTURE` at $q$, with $q \in S$ (or $r$ a retired row through $q$) | **no rule** | the puncture deletes every row through $q$: no claim with $q \in S$ is derivable, and for any retired identifier $r$ (whose input row contained $q$) no claim $\mathsf{gen}_{i+1}(r,\sigma,S)$ is derivable for any $\sigma, S$ by I3 identifier injectivity — the `W13` half for the puncture |
| `E-LOCAL-HADAMARD` ($T=Q$ or $T=\varnothing$) | from $\mathsf{gen}_i(r,\sigma,S)$ concludes $\mathsf{gen}_{i+1}(r,\sigma',S)$, with $\sigma' = \overline{\sigma}$ when $T$ is non-empty and $\sigma' = \sigma$ otherwise | the referenced generator survives and keeps its identifier; its sector swaps when $T \ne \varnothing$ (design choice) |
| `E-LOCAL-HADAMARD` (split subset) | concludes $\mathsf{gen}_{i+1}(r',\sigma',S')$ for every row $(r',\sigma',S')$ of the canonical update (§2 card) | every output row is a source, as `P-REBASE`'s minted rows are. A $T$-pure row keeps its identifier and support, with its sector exchanged exactly when it lies inside $T$. A mixed row's identifier names its first kept piece, if any (design choice) |
| `P-REBASE` at sector $\tau$, with $\sigma \ne \tau$ | from $\mathsf{gen}_i(r,\sigma,S)$ concludes $\mathsf{gen}_{i+1}(r,\sigma,S)$ | the referenced generator survives (it is of the untouched sector) |
| `P-REBASE` at sector $\tau$, with `r` an old row of sector $\tau$ (`σ = τ`: no transport rule) | **no rule** | the rebase retires every old row of sector $\tau$: for an old row `r` of sector $\tau$, no claim $\mathsf{gen}_{i+1}(r,\sigma,S)$ is derivable for any $\sigma, S$ by I3 identifier injectivity and mint freshness — the `W13` half for the rebase |
| `P-REBASE` at sector $\tau$ (minted row) | concludes $\mathsf{gen}_{i+1}(r',\tau,S')$ for each row the rebase mints, with $r'$ the canonical mint and $S'$ the $\mathbb{F}_2$ combination of the sector's displayed rows selected by the coefficient row | source: the claim originates where the row is minted |
| `E-SPLIT` at cut $(Q_A, R)$, with $r \notin R$ | from $\mathsf{gen}_i(r,\sigma,S)$ concludes $\mathsf{gen}_{i+1}(r,\sigma,S)$ | the referenced generator survives unchanged (`OPERATIONAL_SEMANTICS.md` §4.48) |
| `E-SPLIT` at cut $(Q_A, R)$, with $r \in R$ | **no rule** | the split retires every row in $R$: no claim $\mathsf{gen}_{i+1}(r,\sigma,S)$ is derivable for any $\sigma, S$ — the `W13` half for `E-SPLIT` |

The survival side conditions ($r \ne r'$ for `C-DELETE-CHECK`, $r \notin \vec r$
for `E-GRAFT`, $r \ne r_{\mathrm{id}}$ for `E-PEEL`, $q \notin S$ for
`E-PUNCTURE`, and $\sigma \ne \tau$ for `P-REBASE`) are the schema-composition
condition of `spec/OPERATIONAL_SEMANTICS.md` §4.11 read on this claim. In a
minted graft row, $q$ belongs to both $S_j$ and $S_{j+1}$, so the symmetric
difference $S_j \mathbin{\triangle} S_{j+1}$ lies in $Q \setminus \{q\}$. Under
`E-GRAFT` and `E-PEEL`, a transported opposite-sector claim changes its support
by dropping $q$; under `E-LOCAL-HADAMARD` at $T=Q$, a
transported claim changes its sector to $\overline{\sigma}$, and at a split
subset every output row is sourced rather than transported. In every case the
claim follows the identifier of the rewritten row.

The input-display rule is a rule about position $0$ of the chain the
derivation is over. For a sequence $m_1; m_2$, a derivation over the second
segment may use it at the seam state, which is position $0$ of that segment
and an interior position of the composed chain. Such a derivation transports
to the composed chain under a **seam condition**: the composed chain derives
$\mathsf{gen}(r,\sigma,S)$ at the seam for every row the seam state
displays. This is the schema-composition condition of the positive half for
this claim. A row produced by a Gate 6 command can carry a derivation. The
seam condition is proved on every chain of single (non-sequence) steps —
kernel primitives, the graft, and the five Gate 6 commands (§4.11, *Seam
condition on chains of kernel, graft, and Gate 6 steps*) — by
`derives_gen_of_displayed`, `seamRowsDerived_of_stepChain`, and
`seamRowsDerived_of_prefix_stepChain`, and unconditionally on the evaluation
trace of every command sequence by `Trace.stepChain` and
`seamRowsDerived_of_trace` (`Derives.shift_gen_of_trace`).
Sentences that are not generator-referencing claims transport with no seam
condition, because no rule concludes one of them from a
generator-referencing claim. Soundness of the rows, the `W13` halves, and
decidability of the extended witness search are derived at §4.11.

Mechanized shape: `not_derivable_of_false` in
`lean/CodeCalculus/Transport.lean` is the per-evaluation witness. With the
generator-referencing claim in the sentence language (`Ann.gen`, rows
`Derives.genMint`, `genSkip`, `genDelete`, `genAdd`), the `W13` half has its
derivation-level instance there: `not_derivable_gen_of_deleted`, with
`derives_gen_across_other_deletion` and
`not_derivable_gen_across_own_deletion` as the two halves on one parent. The
input-display rule is `Derives.genInput`, the two graft rows are
`Derives.genGraft` (with the support `graftSupport`) and
`Derives.genGraftMint`, the graft's refusal is
`not_derivable_gen_of_grafted`, and the seam condition is `SeamRowsDerived`
with `Derives.shift_gen`. The Gate 6 rows for the claim are
`Derives.genExtend`, `genExtendMint`, `genPeel` (with
`peelSupport_eq_graftSupport_of_eval` in `Soundness.lean`), `genPuncture`,
`genHadamard`, `genRebase`, `genRebaseMint`, and `genSplit` (2026-11-25,
`E-SPLIT`), with refusals
`not_derivable_gen_of_peeled`, `not_derivable_gen_of_punctured` (support form),
`not_derivable_gen_of_punctured_id` (identifier form, arbitrary $\sigma, S$),
`not_derivable_gen_of_rebased` (identifier form, arbitrary $\sigma, S$),
and `not_derivable_gen_of_split` (identifier form, arbitrary $\sigma, S$),
together with worked instances for all five Gate 6 commands and `E-SPLIT`. The seam condition is discharged on every chain of single (non-sequence)
steps and on every command evaluation trace by `seamRowsDerived_of_stepChain`,
`stepChain_append`, `Trace.stepChain`, `seamRowsDerived_of_trace`,
`Derives.shift_gen_of_stepChain`, `Derives.shift_gen_of_trace`,
`derives_gen_iff_displayed`, and `derives_gen_iff_displayed_of_trace` in
`lean/CodeCalculus/SeamChains.lean`, with a worked three-step Gate 6 seam chain. Each refutation is relative to that inventory, per
the second cost above.

## 5. Transport through sequences

`C-SEQUENCE` carries the positive half: a claim mentioning only invariant fields
composes, by L3 `TRANSITIVITY` plus a syntactic condition on schemas. The
schema-composition condition and its argument are recorded in
`spec/OPERATIONAL_SEMANTICS.md` §4.11 (`OBL-JUDGMENT-TRANSPORT`); the half is
**`proved`** (hand derivation, 2026-10-20), subject to that condition. It remains
a Gate 3 input. Mechanized 2026-10-27 as `Derives.weaken`,
`Derives.shift`, and the seam compositions of `lean/CodeCalculus/Transport.lean`;
the record is at `spec/OBLIGATIONS.md`, `OBL-JUDGMENT-TRANSPORT`.

Structural-fact persistence through sequences is **`proved`** by
`OBL-WELL-FORMEDNESS-PRESERVATION` (§4.7), `OBL-JUDGMENT-TRANSPORT` (§4.11),
`OBL-ORDER-INDEPENDENT-DELETION` (§4.15), `OBL-LOCALITY-TRANSPORT` (§4.21),
`OBL-TANNER-CONNECTIVITY-TRANSPORT` (§4.22), and §4.37 (reconciled 2026-11-18); mixed opposite-polarity exact-quantity distance chains remain
`open`, and claims referencing deleted generators remain `unavailable`.

## 7. Property signature and structural schemas

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
| $\mathsf{preserves}_U$ | span | operator-indexed predicate ($U\mathcal{V}(C)\subseteq\mathcal{V}(C)$) | none |
| $\mathsf{preserves}_U(\cdot\mid F)$, $\mathsf{phase}_U(\cdot\mid F)$, $\mathsf{image}_U(\cdot;e)$, $\mathsf{addresses}_U(\cdot;F,A)$ | span | operator- and frame-indexed predicates (§2h Rows C–F); the frame is a parameter, not state data | none |
| $\omega$ (equal-syndrome weight floor) | span | atomic (bounded below by $\lceil d/2\rceil$) | distance |
| output well-formedness | state | predicate (I1–I5) | none |
| presentation data (ids, sectors) | presentation | data | none |
| ledger interval | consumer | abstract value | price |

The `opacity` field records whether the quantity is opaque (distance,
certificate, price) or not, so that distance atoms stay opaque by convention:
no rule or procedure computes a distance from the state
([`VOCABULARY.md`](VOCABULARY.md), *Opaque distance term*). A generic core
must not become a distance oracle by the back door; in the MVP this is
enforced by review rather than by the Lean type.

### 7.2 The structural schemas

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
6. **Weakening (monotone image).** If a property $p(C)$ satisfies a state-wise
 lower bound $p(C) \ge f(q(C))$ for a nondecreasing map $f : D \to D$ and a
 property $q$ whose lower endpoint $L_q$ is carried by the ledger, then every
 state $C$ with sound lower endpoint $L_q \le q(C)$ carries $p(C) \ge f(L_q)$.
 Across a transition $C \to C'$, the child carries the re-evaluated bound
 $p(C') \ge f(L_q(C'))$ rather than substituting the parent's value
 $f(L_q(C))$; when $L_q(C') < L_q(C)$ (as under `C-DELETE-CHECK`), the carried
 floor weakens. Covers the $\omega(C) \ge \lceil d(C)/2 \rceil$ row with
 $f(\ell) = \lceil \ell/2 \rceil$ (§2h; `OPERATIONAL_SEMANTICS.md` §4.37).

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
| $\mathsf{preserves}_U$ rows (`C-SKIP`, `C-ADD-CHECK`, `C-DIRECT-SUM`, `C-SEQUENCE`) | predicate preservation + frame + composition (§2h, §4.37) |
| §2h Rows C–F (`C-SKIP`, `C-ADD-CHECK`, `C-DIRECT-SUM`, `C-SEQUENCE`) | predicate preservation (restriction to a sub-sector under $\mathcal{S}_F(C)\subseteq\mathcal{S}_{F'}(C')$) + frame + composition (§2h, §4.37) |
| $\omega$ row (equal-syndrome weight floor) | weakening (monotone image $\lceil L_d/2 \rceil$ of the distance lower endpoint $L_d$, §7.2.6, §2h, §4.37) |
| well-formedness rows | predicate preservation, already proved for the MVP |

The genuinely bespoke items remain: the distance atoms' per-primitive
instantiations, the conditional price cells, the seam certificate, and the
extension cells whose transitions are new.

### 7.4 The `n`, `k`, `w`, `r`, $\kappa$, $\mathsf{preserves}_U$, §2h Rows C–F, and $\omega$ rows as instances

Each of these rows of §2 is, under the signature of §7.1, an instance of
the schemas of §7.2 rather than a fresh argument. The derived-transfer or
weakening formula and the schema cited are recorded here; the cell verdicts and
evidence labels of §2 are unchanged.

| Property | Carrier | Quantity | Update (per primitive) | Schema |
| --- | --- | --- | --- | --- |
| $n$ | span | $\lvert Q\rvert$ | $n'=n$ (skip/delete/add/sequence); $n=n_A+n_B$ (direct sum) | derived transfer |
| $k$ | span | $\lvert Q\rvert - \mathrm{rank}(\mathit{rows})$ | $k'=k$ (skip); $k'=k+1$ (delete); $k'=k-1$ (add); $k=k_A+k_B$ (direct sum); carries (sequence) | derived transfer |
| $w$ | display | $\max\{\mathrm{wt}(r):r\in\mathit{rows}\}$ | $w'=w$ (skip); $w=\max(w_A,w_B)$ (direct sum); $w'=\max\{\mathrm{wt}(r):r\in\mathit{rows}'\}$ (delete, $\le w$); $w'=\max(w,\mathrm{wt}(r_{\rm new}))$ (add); carries (sequence) | derived transfer + monotonicity |
| $r$ | display | $\max\{\mathrm{diam}_\lambda(s):s\in\mathit{rows}\}$ | $r'=r$ (skip); $r=\max(r_A,r_B)$ (direct sum, conditional on honest merged layout); $r'=\max\{\mathrm{diam}_\lambda(s):s\in\mathit{rows}'\}$ (delete, $\le r$); $r'=\max(r,\mathrm{diam}_\lambda(r_{\rm new}))$ (add); carries by composition (sequence) | derived transfer + monotonicity |
| $\kappa$ | display | $\kappa(C)$, the component count of the displayed-row Tanner graph $\Gamma(C)$ | $\kappa'=\kappa$ (skip); $\kappa=\kappa_A+\kappa_B$ (direct sum); $\kappa'\ge\kappa$, recomputed (delete); $\kappa'\le\kappa$ (add); composition (sequence) | derived transfer + monotonicity |
| $\mathsf{preserves}_U$ | span | $U\mathcal{V}(C)\subseteq\mathcal{V}(C)$ | carries (skip); carries when supported on one summand (direct sum); does not carry (delete); carries iff the test of Corollary 7.1 at $s$ (add; every $G_j$ commuting with $s$, and $\theta_j=\pi/4$ with $V_s\in\mathcal{S}(C')$, are instances); composition (sequence) | predicate preservation + frame + composition |
| $\mathsf{preserves}_U(\cdot\mid F)$, $\mathsf{phase}_U(\cdot\mid F)$, $\mathsf{image}_U(\cdot;e)$, $\mathsf{addresses}_U(\cdot;F,A)$ (§2h Rows C–F) | span (frame parameter) | frame-sector preservation, sector scalar phase, conjugation image of an entry, and addressability (§2h Rows C–F) | carries (skip); carries on $C_1\oplus C_2$ when $U$ is supported on $Q_1$ with $F_1\oplus F_2$ and $A\subseteq F_1$ (direct sum); does not carry (delete); with $F'$ consistent and $\mathcal{S}_F(C)\subseteq\mathcal{S}_{F'}(C')$, Row C iff Corollary 9.1 and Row D same $z$, with $F'$ consistent and the inclusion failing, Rows C and D do not carry, and with $F'$ not consistent on $C'$, Rows C and D are `not yet defined`; Row E carries for kept entries; Row F holds at $(C';F',A\cap F')$ iff Corollary 7.1 at $s$ (add); composition (sequence) | predicate preservation (sub-sector restriction) + frame + composition |
| $\omega$ | span | $\min w_{\max}$ over nontrivial equal-syndrome families ($\ge\lceil d(C)/2\rceil$) | carried floor $\lceil L_d/2\rceil$: unchanged (skip); $\ge\lceil L_d/2\rceil$ (add); recomputed $\lceil L_d'/2\rceil$, weakens (delete); $\lceil\min(L_d^A,L_d^B)/2\rceil$ (direct sum); recomputed at each state (sequence) | weakening (monotone image) |

The distance atoms ($d_X$, $d_Z$, $d$) are **not** in this list: they are
atomic, span-level, and opaque (opacity `distance`); their per-primitive
instantiations remain bespoke, as recorded in §7.3.

**Hand-derivation check.** No rule, premise, or cell of §2 changed; §7 only
re-presents existing rows. The hand derivations of
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4.7 (well-formedness),
§4.8 (determinism, associativity, and the direct-sum laws), and §4.9
(partial inverses and the frame law) therefore still close unchanged.



## 8. Ledger as an abstract interpretation

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
governed by §7's qualification. The equality half is substitution (schema 5).

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

## 9. The consumer refinement preorder

*Non-normative reorganization, 2026-10-27. This section states no new rule,
admits no cell, and changes no claim status. It supplies the missing interface
between the ledger and the consumer's target: a preorder on ledger states under
which the `certify`/`prune` verdicts of §2b are monotone, and under which the
transformers of §8.3 are monotone. Authority:
 §2.4 (form (a)) and §4; `spec/`
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
| `E-LOCAL-HADAMARD` (split subset) | $\max$, $\min$ and a constant $+\infty$ endpoint are monotone | §2b `E-LOCAL-HADAMARD` split-subset row |
| `E-PEEL` | selected lower carry is monotone in $\sqsubseteq^{\mathrm{low}}$; opposite upper carry and the full-distance upper carry are monotone in $\sqsubseteq^{\mathrm{up}}$; reset lower endpoints are constant | §2b `E-PEEL` row, §4.28 |
| `E-PUNCTURE` | lower reset to $0$ is constant (monotone); upper endpoints from child-valid witnesses are monotone in $\sqsubseteq^{\mathrm{up}}$ | §2b `E-PUNCTURE` row |
| `E-EXTEND` | $\Delta=\varnothing$: lower carry is monotone in $\sqsubseteq^{\mathrm{low}}$, upper rebuild is monotone in $\sqsubseteq^{\mathrm{up}}$; $\Delta\ne\varnothing$: lower reset to $0$ is constant, upper endpoints from child-valid witnesses are monotone in $\sqsubseteq^{\mathrm{up}}$ | §2b `E-EXTEND` row |
| `E-GLUE` | lower endpoints: $\min$ of the two factor lowers is monotone in $\sqsubseteq^{\mathrm{low}}$; Z upper endpoint: $\min$ of the two factor Z uppers is monotone in $\sqsubseteq^{\mathrm{up}}$ under an admissible certificate; X and full upper endpoints from child-valid witnesses are monotone in $\sqsubseteq^{\mathrm{up}}$ | §2b `E-GLUE` row, §2e |
| `C-DIRECT-SUM` | `min` on endpoints is monotone in $\sqsubseteq$ | §2b `C-DIRECT-SUM` row |
| `C-SEQUENCE` | composition of monotone maps is monotone (§8.5) | §5, §4.11 |

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
's `Interval.lean` (`ExtNat`, `AbsInterval`, `gamma`, `preciseLe`). The Lean
development is a transcription aid, not a proof assistant result; it does not
establish soundness, and no cell's evidence status depends on it.

[`lean/CodeCalculus/Gate6Soundness.lean`](../lean/CodeCalculus/Gate6Soundness.lean)
states the §2b and §2e transformers of the Gate 6 cells (`propagateGate6`,
`glueLedger`) with the soundness of `OPERATIONAL_SEMANTICS.md` §4.32
(`gate6_interval_soundness`, `glue_transformer_sound`) and the
move-monotonicity of §9.4 (`propagateGate6_monotone`, `glueLedger_monotone`),
conditional on the distance relations of §4.26 to §4.30 as hypotheses. It is a transcription aid in the same sense and changes no
cell's evidence status.

---

## 6. What this document does not do

It does not claim any cell is established by a proof assistant — none is. The
`proved` tags are evidence statuses meaning *a derivation is in this repository*;
they are not `promoted`, which is a human-owned review disposition
(`AUTHORITY.md` §B1–§B2).

It does not admit a claim into the calculus. Admission is the schema rule of
[`CLAIMS.md`](CLAIMS.md), and its conformance-contract
half (**D-1**) is implemented — the
structured premise fields are wired through `machine/fixtures/mvp_fixtures.json`
and checked by `machine/fixture_conformance.py`. The remaining mechanized
judgment-layer work is tracked separately, not by D-1.

The three obligations added for (graft transition, interval transport,
and price-input trust boundary) are discharged by hand derivation (§4.12,
§4.13, §4.14). Remaining open obligations are tracked in
[`OBLIGATIONS.md`](OBLIGATIONS.md).

---
