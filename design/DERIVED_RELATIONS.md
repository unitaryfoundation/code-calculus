# Derived relations — conditional prices and provider results

**Status:** non-normative reference note. It inventories external
draft results that motivate conditional distance-price cells and the tower price
provider. Normative admission is recorded in
[`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md) §2a and the associated
obligations. The executable consumer is in `machine/`; this note is not its
specification and its cited results have not been re-derived here.

**Why it exists.** A review on 2026-10-18 asked whether
judgment-transport statements can be extracted from the literature and from the
companion distance-ledger work, and how many relations of the form
$d\ [\le,\ge,=]\ d' + k$ ($k > 0$) are extractable. This note answers with a
citable inventory. **Superseded disposition (2026-10-18):** strict improvement
and the exact deletion price were initially left outside the carry table. The
2026-10-19 decision admitted the full-distance deletion price,
`E-GRAFT`, and strict improvement as conditional judgment cells; the later
decision is recorded in the development repository.

---

## 1. The firewall: what "derived" means here

- **The calculus attests only what the carry table licenses.** `C-ADD-CHECK`
 carries $L' = L$; `C-DELETE-CHECK` carries $U' = U$; `C-DIRECT-SUM` is exact;
 `C-SKIP` is identity; $n$, $k$ are exact for the core transitions. Conditional
 deletion and graft prices and strict improvement are listed separately in
 §2a of the normative judgment layer.
- **Every relation below requires a hypothesis the calculus does not contain** —
 minima over deleted or exposed sets ($w_{\mathrm{del}}$, $w_{\mathrm{exp}}$),
 a re-exposure minimum ($w_{\mathrm{re}}$), or a minimum-weight logical
 enumeration. These are consumer-supplied quantities, of the same kind as the
 future $\Pi$ certificate fields ([`spec/STATE_MODEL.md`](../spec/STATE_MODEL.md)
 §1: not MVP data).
- **The calculus's role for an admitted relation is to attest the
 implication and record its evidence status — never to compute the hypothesis.**
 If the hypothesis is not supplied, the outcome is `unavailable`, not a guess.
  The refusal discipline is unchanged; the ablation study identified it as the
  calculus's distinctive asset (§6, third finding).
- **The hypothesis remains external.** The consumer records its source but does
 not compute or validate deletion/exposure minima or a minimum-weight-class
 enumeration. Tower factorization is only a price provider; it does not admit
 an `A-CONCAT` construction command.

## 2. The inventory

**Scope update, 2026-10-19.** Three of these relations are now included as
*conditional* carry cells rather than merely documented: the exact deletion
price, the graft price, and strict improvement (when its hypothesis is supplied).
They remain conditional on consumer-supplied hypotheses and are not tagged
`established` until the companion papers are published or their derivations are
reproduced here. This does not pass the sound-admission lifecycle in
[`spec/CLAIMS.md`](../spec/CLAIMS.md); the direct-sum and gluing rows are
unchanged.

Status columns record the status **in the source**; see §6 for what these rows
are not. Weights are physical support weights; empty minima are $+\infty$; all
statements are code-level only (no DEM, circuit, or decoder claim).

| Move or price provider | Derived relation | Shape | Hypothesis supplied by the consumer | Cost of the hypothesis | Source | Status in the source |
| --- | --- | --- | --- | --- | --- | --- |
| `C-DIRECT-SUM` (disjoint) | $d = \min(d_A, d_B)$, $k = k_A + k_B$ | equality | none — already licensed by the carry table | free | carry table, [`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md) §2; external corroboration: coproduct Theorem 3.3 / claim 3.4 (*composition-distance* §2.2) | `proved` here; `PROVEN` there |
| `C-DIRECT-SUM` / `E-GLUE` (shared interface) | $d_\sigma(P) \ge \min\bigl(d_\sigma(A), d_\sigma(B), w_{\mathrm{re},\sigma}\bigr)$, **per sector** | lower bound | $w_{\mathrm{re},\sigma}$, the least weight of a class re-exposed by the split | NP-hard in general (*composition-distance* Prop 5.2) | re-exposure bound, MS Theorem 4 = claims 7.4 / 6.3b (*composition-distance* §6.1) | `PROVEN` under the stated hypotheses (specified subcomplexes, common edge basis; claim 7.4 `PROVEN (packaging)`); under the admitted `E-GLUE`, disjoint factors plus seam checks, no class is re-exposed and the term is vacuous ([`spec/OPERATIONAL_SEMANTICS.md`](../spec/OPERATIONAL_SEMANTICS.md) §4.33, 2026-11-11) |
| `E-GLUE` (shared interface) | **no** relation of the form $d = \min(\ldots)$ exists | obstruction | — | — | insufficiency, MS Theorem 5 = proof-ledger Theorem 7.1 / claim 7.7 (*composition-distance* §3.1) | `PROVEN, stated family` (Z-sector; **not** a full-Pauli-$d$ statement) |
| `E-PEEL` at $q$ in sector $\tau$, opposite sector $\sigma$ | $d'_\sigma = \min(d_\sigma,\, w_{\mathrm{expose},\sigma}(q))$; unpriced $d_\sigma - 1 \le d'_\sigma \le d_\sigma$ | equality (priced); two-sided bound (unpriced) | $w_{\mathrm{expose},\sigma}(q) = \min\{|u|-1 : u \text{ a parent } \sigma\text{-logical with } u_q = 1\}$, the graft's exposure price bound to the peel | a minimum over a logical class; NP-hard in general, as $w_{\mathrm{exp}}$ | in-repository derivation, [`spec/OPERATIONAL_SEMANTICS.md`](../spec/OPERATIONAL_SEMANTICS.md) §4.28 (2026-11-10): the §4.13 graft relation at $m=1$ | `proved` here (hand derivation); no external source |
| `E-PEEL` at $q$ in sector $\tau$, selected sector | $d'_\tau = w_{\mathrm{avoid},\tau}(q)$; unpriced $d'_\tau \ge d_\tau$ | equality (priced); lower bound (unpriced) | $w_{\mathrm{avoid},\tau}(q) = \min\{|v| : v \text{ a parent } \tau\text{-logical with } v_q = 0\}$, the avoidance minimum | a minimum over a logical class; NP-hard in general | in-repository derivation, §4.28 (2026-11-10): the child's $\tau$-logicals are the $q$-free parent $\tau$-logicals | `proved` here (hand derivation); no external source |
| `E-PUNCTURE` at $q$ | $d'_\sigma = \min(w_{\mathrm{avoid},\sigma}(q),\, w_{\mathrm{hole},\sigma}(q))$ per sector, the avoidance minimum of the intermediate code (every row through $q$ deleted) | equality (reduction; **not admitted as a cell**) | $w_{\mathrm{hole},\sigma}(q)$, the lightest $q$-free operator the deleted rows expose: the hole price | NP-hard in general; its structural lower bound is the D2 question | in-repository reduction, §4.29 (2026-11-10): deletions, then the removal of the then-free qubit | reduction recorded; no unpriced direction (increase $1\to2$, decrease $3\to2$); cell blocked on D2 |
| `C-DELETE-CHECK` (rank drop $r$) | $d' = \min(d,\, w_{\mathrm{del}},\, w_{\mathrm{exp}})$, $k' = k + r$ | equality | $w_{\mathrm{del}} = \min\{\mathrm{wt}(g) : g \in S \setminus S'\}$ (lightest **promoted combination**), $w_{\mathrm{exp}} = \min\{\mathrm{wt}(E) : E \in N(S') \setminus N(S)\}$ (lightest newly exposed normalizer operator) | both are minima over sets; $w_{\mathrm{exp}}$ NP-hard in general (Theorem 24.1) | Theorem 7 = proof-ledger Theorem 12.1 (*code-deformation* §4.1) | `PROVEN` (claim row 12.1) |
| `C-DELETE-CHECK` (safety at floor $d_\star$) | safe at $d_\star$ **iff** $w_{\mathrm{del}} \ge d_\star$ and $w_{\mathrm{exp}} \ge d_\star$ | iff | as above | as above | unnumbered prose, *code-deformation* §4.3 (immediate from Theorem 7); order-ideal companion Lemma 21.2 | `PROVEN` as prose — **not a numbered result**; Lemma 21.2 `PROVEN` (safe sets form an order ideal under inclusion from a fixed basis, **not** closed under union) |
| `C-ADD-CHECK` (gauging) | $d' \ge d$; exact surviving-logical minimum $d' = \min\{\mathrm{wt}(g) : g \in N(S) \cap A^\perp,\ g \notin S + \langle A\rangle\}$; $k' = k - r$ | lower bound + equality | added checks $A$: commute with $S$, pairwise commuting, independent mod $S$ | linear algebra plus one minimum over surviving logicals; "not a claim of efficient evaluation" | Theorem 7′ = proof-ledger Theorem 18.1 + Proposition 18.2 (*code-deformation* §5.1) | `PROVEN` (claim row 15.1) |
| `C-ADD-CHECK` (strict improvement) | $d' > d$ **iff** every old logical class of coset-minimum weight $d$ either anticommutes with an added check or lies in the killed span $K = (S + \langle A\rangle)/S$ | iff; as integers $d' \ge d + 1$ under the hypothesis | the minimum-weight class enumeration of the old code | NP-hard in general (Corollary 18.4); commutation and span exclusion alone are cheap linear-algebra checks, and a surviving weight-$d$ class cheaply witnesses $d' = d$ | Proposition 18.3 + Corollary 18.4 (*code-deformation* §5.2) | `PROVEN` / `PROVEN, inherited` (claim row 15.2) |
| `C-SEQUENCE` (deletion-only chains) | $d_T = \min\bigl(d_0, w_{\mathrm{del}}(1), w_{\mathrm{exp}}(1), \ldots\bigr)$ — exact, horizon-free telescoping | equality | per-step prices against the **current** presentation | per-step minima | Proposition 19.1 (*code-deformation* §6.2) | `PROVEN` |
| `C-SEQUENCE` (mixed chains) | $d_T \ge \min\bigl(d_0, w_{\mathrm{del}}(t), w_{\mathrm{exp}}(t) \text{ over deletion steps } t\bigr)$; gauging steps contribute only $d_t \ge d_{t-1}$ | lower bound | as above | as above | Proposition 19.3 (*code-deformation* §6.2) | `PROVEN (bound)`; the "permanent loss of exactness" wording is **withdrawn as false** (H2 adjudication, 2026-09-30) — bound-only ledger propagation, recertification possible |
| `E-GRAFT` (admitted conditional extension) | **Sector-wise:** $d'_\sigma=\min(d_\sigma,\, w_{\mathrm{expose},\sigma})$ for the non-spliced sector; the spliced sector carries its lower endpoint and drops its upper endpoint to $+\infty$ unless a child-valid witness supplies one; the scalar form $d'=\min(d,\,w_{\mathrm{expose},\bar\tau})$ is **not** valid as $d'\le d$ (refuted) | equality + monotonicity, sector-wise | coverage condition: a graft must leave every qubit touched by a check of each type | exposure minimum; the search space is bounded by the interface, no complexity bound claimed | Theorem 28.2 (sector-wise), *code-deformation* §9.5; claim row 28.4 | `PROVEN` for the sector-wise price under the corrected rules (see `OPERATIONAL_SEMANTICS.md` §4.13, 2026-10-21; reproduced and corrected at §4.19); coverage condition `EMPIRICAL` (row 28.3) |
| `E-LOCAL-HADAMARD` ($T=Q$) composed with any admitted unary move $m_\sigma$ | $H \circ m_\sigma = m_{\bar\sigma} \circ H$ on states and on the carried ledgers; $d' = d$ under $H$ | equality (conjugation) | none | free | in-repository derivation, §2b (2026-11-11) | `proved` here (hand derivation); state-update conjugation mechanized in `lean/CodeCalculus/DualityAdjunction.lean` ; randomized check `machine/test_sector_swap.py` |
| `A-CONCAT` towers (deleting lifted outer checks) | exposure prices factor from level-only data: $w_{\mathrm{exp}}^T$ computable from the class dictionary and the outer presentation, **never enumerating the tower normalizer**; deletion-only chains telescope exactly | equality | tower structure, class dictionary, outer presentation | level data plus an outer-level search (the outer code's exposure and deletion minima under the dictionary weight) | Theorems 27.2 / 27.5, Corollaries 27.6 / 27.7 (*code-deformation* §9.4, proof ledger §27); generalization to $k_{\mathrm{in}}>1$ at Theorem 27.8 with refined class dictionary, cost tables of size $2^{2k_{\mathrm{in}}}$; the provider for arbitrary $k_{\mathrm{in}}$ is derived in this repository, §2a (2026-11-11) | `PROVEN` there (claim rows 27.1–27.6); `proved` here by the §2a hand derivation, sweep-verified for $n_{\mathrm{in}} = 4$ and $k_{\mathrm{in}} \in \{1, 2, 3\}$ (`machine/experiments/tower_sweep.py`) |

Two corrections to any secondhand reading of these sources, both load-bearing
and both reflected above: the graft price has **exactly two terms** — the
three-term sector-wise form's promoted term is $\equiv \infty$ (Lemma 28.1a), so
a three-term graft formula must not be cited; and the safety biconditional is
**unnumbered §4.3 prose**, not a theorem number.

### 2a. Tower prices from level data (derived 2026-11-11)

**Setting.** The inner code is a CSS code on $n_{\mathrm{in}}$ qubits with
$k_{\mathrm{in}} \ge 1$ logical qubits; its $X$-checks span the row space $R_X$
and its $Z$-checks the row space $R_Z$. Fix dual logical bases: $X$-logical
representatives $\bar X_1, \ldots, \bar X_{k_{\mathrm{in}}}$ and $Z$-logical
representatives $\bar Z_1, \ldots, \bar Z_{k_{\mathrm{in}}}$ whose overlap
parities satisfy $\langle \bar X_a, \bar Z_b \rangle = [a = b]$. For
$h \in \mathbb{F}_2^{k_{\mathrm{in}}}$ write $\bar X(h)$ for the sum of the
$\bar X_a$ with $h_a = 1$, and $\bar Z(h)$ likewise; both are linear in $h$. An
$X$-type vector $v$ on the inner qubits that commutes with every inner
$Z$-check has the class $\mathrm{cl}_X(v) \in \mathbb{F}_2^{k_{\mathrm{in}}}$
with coordinates $\langle v, \bar Z_b \rangle$, and $v$ lies in the coset
$\bar X(\mathrm{cl}_X(v)) + R_X$. A $Z$-type vector $z$ that commutes with
every inner $X$-check has the class $\mathrm{cl}_Z(z)$ with coordinates
$\langle \bar X_a, z \rangle$ and lies in $\bar Z(\mathrm{cl}_Z(z)) + R_Z$.

**Level data.** The class dictionary of the inner code in sector $\sigma$ is
the table $\mu_\sigma : \mathbb{F}_2^{k_{\mathrm{in}}} \to \mathbb{N}$ whose
entry at $h$ is the least weight of a $\sigma$-type vector of class $h$ that
commutes with every inner check of the other sector. It has
$2^{k_{\mathrm{in}}}$ entries, $\mu_\sigma(0) = 0$, every other entry is
positive, and the inner sector distance is
$d^{\mathrm{in}}_\sigma = \min_{h \ne 0} \mu_\sigma(h)$. The two tables
$\mu_X$ and $\mu_Z$ are the level data; `tower_level_data` in
`machine/priced_calculus.py` computes them by enumerating the kernel of the
opposite sector's checks.

**The outer code and the tower.** The outer code is a CSS code on
$N = n_{\mathrm{out}} k_{\mathrm{in}}$ qubits partitioned into
$n_{\mathrm{out}}$ blocks of $k_{\mathrm{in}}$ qubits each, every block
carrying a fixed order of its qubits. For $c \in \mathbb{F}_2^{N}$ write
$c_j \in \mathbb{F}_2^{k_{\mathrm{in}}}$ for its restriction to block $j$,
and define its dictionary weight in sector $\sigma$ as
$\mu_\sigma(c) = \sum_j \mu_\sigma(c_j)$. The tower $T$ has
$n_{\mathrm{out}}$ copies of the inner qubits, copy $j$ serving block $j$,
and these displayed rows: every inner check on every copy, and for every
outer row $h$ of sector $\sigma$ its lift $L_\sigma(h)$, whose part on copy
$j$ is $\bar X(h_j) + s_j$ when $\sigma = X$ and $\bar Z(h_j) + s_j$ when
$\sigma = Z$, with $s_j$ an arbitrary element of the inner $\sigma$-row space
(the representative choice). The deletion priced here removes the lifts of a
set $D$ of outer rows of one sector $\tau$; $\sigma$ denotes the other sector,
$E(\cdot, D)$ the exposure set of §3a (even overlap with every remaining
$\tau$-row, odd overlap with at least one row of $D$), $S_\tau(\cdot)$ the span
of a code's displayed $\tau$-rows, and $D^T$ the set of lifts of $D$.

**Claim.** The exposure price of the tower deletion is the least dictionary
weight of an outer-level vector exposed by the same deletion in the outer
code,

$$
w_{\mathrm{exp}}(T, D^T) = \min\{\mu_\sigma(c) : c \in E(\mathrm{outer}, D)\},
$$

and the deletion price is the least dictionary weight of an outer
$\tau$-stabilizer that uses a deleted row,

$$
w_{\mathrm{del}}(T, D^T) = \min\{\mu_\tau(\gamma) : \gamma \in S_\tau(\mathrm{outer}) \setminus S_\tau(\mathrm{outer} \setminus D)\}.
$$

For $k_{\mathrm{in}} = 1$ the dictionary weight is the inner sector distance
times the Hamming weight, so
$w_{\mathrm{exp}}(T, D^T) = d^{\mathrm{in}}_\sigma w_{\mathrm{exp}}(\mathrm{outer}, D)$
and
$w_{\mathrm{del}}(T, D^T) = d^{\mathrm{in}}_\tau w_{\mathrm{del}}(\mathrm{outer}, D)$.

**Derivation.**

1. *The tower is a valid state.* Inner checks of opposite sectors commute on
 a copy and are disjoint across copies. An inner $X$-check $x$ on copy $j$
 meets a lift $L_Z(g)$ only there, in $\langle x, \bar Z(g_j) + s_j \rangle$,
 and both terms vanish: $\bar Z(g_j)$ commutes with every inner $X$-check
 by definition of a $Z$-logical representative, and $s_j$ is an inner
 $Z$-stabilizer. Two lifts pair as
 $\langle L_X(h), L_Z(g) \rangle = \sum_j \langle \bar X(h_j), \bar Z(g_j) \rangle = \sum_j h_j \cdot g_j = h \cdot g = 0$,
 the stabilizer parts contributing nothing and the last equality holding
 because the outer rows commute; here $h \cdot g$ is the overlap parity of
 two outer vectors. For independence, a dependency among the $\sigma$-rows
 of $T$ restricted to copy $j$ reads
 $\sum_h \lambda_h (\bar X(h_j) + s_{h,j}) + r_j = 0$ with $r_j \in R_X$, so
 $\bar X\bigl((\sum_h \lambda_h h)_j\bigr) \in R_X$, so
 $(\sum_h \lambda_h h)_j = 0$ for every $j$, so $\sum_h \lambda_h h = 0$,
 so every $\lambda_h$ is zero by the independence of the outer rows; the
 inner-check coefficients then vanish by the independence of the inner
 rows. The same argument covers $\sigma = Z$.
2. *Block classes.* A $\sigma$-type vector $v$ on $T$ commutes with every
 inner check of the other sector iff each copy part $v_j$ does, in which
 case $\mathrm{cl}_\sigma(v_j)$ is defined; write $\mathrm{cl}(v) \in
 \mathbb{F}_2^{N}$ for the vector whose block-$j$ restriction is
 $\mathrm{cl}_\sigma(v_j)$. For such $v$ and any lift of an outer
 $\tau$-row $g$, $\langle v, L_\tau(g) \rangle = \sum_j \mathrm{cl}_\sigma(v_j) \cdot g_j = \mathrm{cl}(v) \cdot g$,
 the stabilizer parts $s_j$ contributing nothing. Every
 $c \in \mathbb{F}_2^{N}$ is $\mathrm{cl}(v)$ for some $v$, for instance
 the $v$ with $v_j = \bar X(c_j)$ or $\bar Z(c_j)$.
3. *Exposure.* A $\sigma$-type vector $v$ lies in $E(T, D^T)$ iff it commutes
 with every inner check of the other sector (those rows remain) and
 $\mathrm{cl}(v)$ has even overlap with every remaining outer $\tau$-row
 and odd overlap with some row of $D$ (step 2), that is, iff
 $\mathrm{cl}(v) \in E(\mathrm{outer}, D)$. The least weight of $v$ with
 $\mathrm{cl}(v) = c$ is $\sum_j \mu_\sigma(c_j) = \mu_\sigma(c)$, attained
 by a minimum-weight representative of class $c_j$ on every copy. The
 exposure identity follows.
4. *Promotion.* The parent $\tau$-span of $T$ is spanned by the inner
 $\tau$-checks and the lifts, which are independent (step 1), so a span
 element $z$ has a unique coefficient vector and lies outside the child
 span iff its coefficient on some lift in $D^T$ is nonzero. With
 $\lambda$ the coefficients on the lifts and
 $\gamma = \sum_g \lambda_g g \in S_\tau(\mathrm{outer})$, the copy-$j$
 part of $z$ is $\bar Z(\gamma_j)$, or $\bar X(\gamma_j)$ when $\tau = X$,
 plus an inner $\tau$-stabilizer, so its class is $\gamma_j$ and the least
 weight over the inner-check coefficients for fixed $\lambda$ is
 $\sum_j \mu_\tau(\gamma_j) = \mu_\tau(\gamma)$. The set of $\gamma$ with a
 nonzero coefficient on $D$ is
 $S_\tau(\mathrm{outer}) \setminus S_\tau(\mathrm{outer} \setminus D)$ by
 the independence of the outer rows. The deletion identity follows.
5. *Representatives.* Changing an $s_j$ changes a lift by inner checks, which
 are rows of $T$, so neither the $\tau$-span nor the exposure conditions
 change: the prices do not depend on the representative choice.
6. *The case $k_{\mathrm{in}} = 1$.* Then $\mu_\sigma(0) = 0$ and
 $\mu_\sigma(1) = d^{\mathrm{in}}_\sigma$, so
 $\mu_\sigma(c) = d^{\mathrm{in}}_\sigma |c|$ and both minima factor.

Q.E.D.

**The provider and its sweep.** `tower_deletion_prices` searches at the
outer level: the kernel of the remaining outer $\tau$-rows for the exposure
term and the span of the outer $\tau$-rows for the deletion term, each
weighted by the dictionary, and refuses above a recorded search ceiling. The
tower is never enumerated. The verdict carries a ledger-ready
`deletion_price` for the priced `C-DELETE-CHECK` cell.
`machine/experiments/tower_sweep.py` builds towers from inner codes with
$n_{\mathrm{in}} = 4$ and $k_{\mathrm{in}} \in \{1, 2, 3\}$ over random outer
codes of up to four blocks, lifts through randomly perturbed representatives,
deletes one or two lifts, and compares the provider with exhaustive
enumeration on the built tower; `machine/test_tower_sweep.py` pins hand
instances and a seeded run. In 120 seeded trials no price disagreed, the
priced cell $d' = \min(d, w_{\mathrm{del}}, w_{\mathrm{exp}})$ agreed with the
exact-distance oracle in all 96 trials whose parent had a logical, and the
inner distance alone (the unrefined dictionary) mispriced 30 trials.
Agreement is evidence that the derivation is transcribed as stated; it is
not a proof.

**What this settles, and what it does not.** Settled: the prices of deleting
lifted outer checks of a two-level tower are computable from the two inner
class dictionaries and the outer presentation by an outer-level search, and
the refined dictionary is load-bearing. Not settled, and not claimed:
deletions of inner checks (the exposed operator's copy part is then not a
class), towers of more than two levels, and anything about the source's own
definitions. Theorems 27.2 / 27.5 / 27.8 of *code-deformation* are cited,
not reproduced; their cost-table figure $2^{2k_{\mathrm{in}}}$ is kept as
recorded (`tower_cost_table_size`), while the derivation here uses two
dictionaries of $2^{k_{\mathrm{in}}}$ entries. The outer-level search inherits
the outer code's hardness (Theorem 24.1 for the exposure term). `A-CONCAT`
remains a price provider: the tower state built by the experiment is
oracle-side and no constructor is admitted.

### 2b. Sector-swap conjugation (derived 2026-11-11)

Write $H$ for the `E-LOCAL-HADAMARD` update at $T = Q$: every displayed row
keeps its identifier and its support and exchanges its sector label, and
$Q$ and `used` are unchanged ([`spec/OPERATIONAL_SEMANTICS.md`](../spec/OPERATIONAL_SEMANTICS.md)
§4.27). For a sector $\sigma$ write $\bar\sigma$ for the opposite sector.
For a unary transition $m$ whose term names a sector, write $m_\sigma$ for
its instance at $\sigma$; for `C-DELETE-CHECK` and `E-PUNCTURE`, whose
terms name no sector, $m_\sigma$ is $m$ itself. Write $T_m$ for the ledger
transport of $m$ in the carry table of
[`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md) §2b, and $T_H$ for
the swap transport of its `E-LOCAL-HADAMARD` row.

**Claim.** For every admitted unary transition $m$ and every state $C$, the
instance $m_{\bar\sigma}$ derives on $H(C)$ exactly when $m_\sigma$ derives on
$C$, and then
$$
 H(m_\sigma(C)) = m_{\bar\sigma}(H(C)).
$$
For every ledger $L$ that contains the distances of $C$, which is the input
condition of the carry table, and whose priced hypotheses, if any, are
mirrored together with the sector, the transports agree as well,
$T_H(T_{m_\sigma}(L)) = T_{m_{\bar\sigma}}(T_H(L))$. (The condition is
load-bearing for the executable consumer: on a parent with no logical qubit
it normalizes every carried endpoint to $+\infty$ on the step it sees that
state, so a finite endpoint carried into such a parent, a false input, is
normalized on one side of the identity and not on the other.)

**Derivation.** The state model names the two sectors only through the row
labels, and the invariants are symmetric under exchanging the labels: I1 is
the even-intersection condition between the two displays, I2 is
independence within each display, and I3 to I5 mention no sector. Each
transition's premises and update refer to a sector only as the selected
sector, the opposite sector, or the row's own sector (§4.1, §4.2, §4.13,
§4.26, §4.28 to §4.30), and the canonical mint reads `used` alone, so
relabeling the sectors before the update or after it yields the same
display, identifier by identifier, and a premise fails on one side exactly
when its mirror fails on the other. For the ledger, every cell of the carry
table is stated per sector in the same roles, the full-distance cell is
symmetric in the two sectors, and a witness is valid in a sector exactly
when its support commutes with the opposite display and lies outside that
sector's span, which is the same test with the roles exchanged; the swap
transport exchanges the two sector intervals and the two witness lists and
keeps the full interval. The mirrored cell applied to the swapped ledger is
therefore the swapped result of the cell. The state-update conjugation
identities $H(m_\sigma(C)) = m_{\bar\sigma}(H(C))$ across the kernel and Gate 6
moves (`deleteState`, `addState`, `directSumState`, `glueState`, `peelState`,
`punctureState`, `hadamardState`, `rebaseState`, `extendState`, `graftState`)
are mechanized in `lean/CodeCalculus/DualityAdjunction.lean` .
$\square$

**Consequence for the consumer.** Sector-targeted planning toward $\sigma$ on
$C$ is sector-targeted planning toward $\bar\sigma$ on $H(C)$, so the swap is
exploited by applying it once, at the start of a sector-targeted search,
when the carried interval of $\bar\sigma$ is the stronger one for the target.
It is a presentation symmetry, not a distance move: $d' = d$ (§4.27), and a
full-distance target gains nothing from it. No new judgment cell is needed;
the `E-LOCAL-HADAMARD` row of the carry table and the §4.27 exchange carry
everything the exploitation uses. `machine/priced_calculus.py`
(`sector_swap_exploitation`) records the decision with its reason and the
invariance, `machine/planner.py` offers the swap as a candidate under
`sector_swap=True` and applies it first in `bounded_sector_search`, and
`machine/test_sector_swap.py` checks the identity on random states and
moves for the unpriced transports of deletion, addition, graft, peel,
puncture, rebase, and extension, an aid and not a proof.

## 3. The cost boundary — where the hypotheses are hard

| Quantity | Cost | Source | Status in the source |
| --- | --- | --- | --- |
| $w_{\mathrm{exp}}$ (general) | NP-hard — exact reduction from syndrome decoding, already with no $X$-checks | Theorem 24.1 (*code-deformation* §8.1) | `PROVEN (reduction)` |
| $w_{\mathrm{exp}}$ (graphlike, one-dimensional complexes) | polynomial — closed formula, BFS | Theorem 25.1 + Corollary 25.2 | `PROVEN` |
| $w_{\mathrm{exp}}$ (column weight at most three) | NP-hard: column-splitting reduction from the general case, §3a | derived in this repository (2026-11-10) | hand derivation in §3a; not carried by either external source |
| $w_{\mathrm{re}}$ (re-exposure) | NP-hard for shared-interface splits; $+\infty$ (no re-exposed class) under the admitted `E-GLUE` | Proposition 5.2 (*composition-distance*); [`spec/OPERATIONAL_SEMANTICS.md`](../spec/OPERATIONAL_SEMANTICS.md) §4.33 (2026-11-11) | `PROVEN (reduction)` there, for a setting the calculus does not admit; `proved` here that the admitted transition has no re-exposed class |
| minimum-weight logical enumeration | NP-hard in general | Corollary 18.4 (*code-deformation*) | `PROVEN, inherited` |

Guardrails stated by the sources and inherited here: a heuristic that finds no
short exposed operator supplies **no** lower bound; a found operator is an upper
witness only; and the sources claim no hardness at column weight three (the
sharpening is excluded from their claims pending a citation). That sharpening
is derived in this repository in §3a; the history of the question (accepted as
an investigation 2026-11-10, settled the same day) is recorded in the development repository's decision log.

### 3a. Column weight three is as hard as the general case (derived 2026-11-10)

The exposure price is the second term of the `C-DELETE-CHECK` price of §2. Fix
a parent state $C$ with qubit set $Q$ of size $n$, whose displayed $Z$-checks
are the $m$ rows of a binary matrix $H$ (independent, by the state model's
invariants) and whose displayed $X$-checks are the rows of a binary matrix
$G$. Let $D$ be the set of deleted $Z$-rows and $H'$ the matrix of the
remaining ones. The exposed set $E(C,D)$ consists of the binary vectors $v$ on
$Q$ with even overlap against every row of $H'$ and odd overlap against at
least one row of $D$. These are exactly the $X$-operators in
$N(S')\setminus N(S)$ of §2: odd overlap with a deleted row already places $v$
outside the $X$-stabilizer span, so no span test is needed. The exposure price
is the least weight in the exposed set,

$$
 w_{\mathrm{exp}}(C,D)=\min\{|v| : v\in E(C,D)\},
$$

and is $\infty$ when the set is empty, which for a nonempty $D$ cannot happen in
a valid state, since the deleted rows lie outside the span of the remaining
ones. The column weight of a qubit is the number of $Z$-rows of the parent that
contain it, and $c_{\max}$ denotes the largest column weight. Theorem 25.1
computes the price in polynomial time when $c_{\max}\le 2$, and Theorem 24.1
shows the unrestricted problem NP-hard. A gadget closes the gap between the two.

**The split.** Fix an integer $t\ge 1$. The $t$-fold split $C^{(t)}$ has as
qubits the copies $q^{1},\dots,q^{t}$ of every qubit $q$ of $Q$, and three kinds
of rows:

1. for each $Z$-row $r$ of the parent, deleted or not, a split row $r^{(t)}$
 containing exactly one copy of each qubit of $r$;
2. for each qubit $q$ and each index $i<t$, the equality row $\{q^{i},q^{i+1}\}$
 in the $Z$ sector;
3. for each $X$-row $g$ of the parent, the row $g^{(t)}$ containing every copy
 of each qubit of $g$.

The copies in item 1 are assigned so that an end copy ($i=1$ or $i=t$) receives
at most two parent rows and an inner copy at most one, which is possible exactly
when $c_{\max}\le t+2$ for $t\ge 2$ and when $c_{\max}\le 3$ for $t=1$. The
deleted set becomes $D^{(t)}=\{c^{(t)} : c\in D\}$. The least admissible copy
count is $t=\max(1, c_{\max}-2)$, and for $c_{\max}\le 3$ the split is the
parent itself.

**Claim.** For every admissible $t$, the split instance has $Z$ column weight at
most three and

$$
 w_{\mathrm{exp}}\bigl(C^{(t)},D^{(t)}\bigr)=t w_{\mathrm{exp}}(C,D).
$$

**Derivation.**

1. *Well-formedness.* An $X$-row $g^{(t)}$ meets a split row $r^{(t)}$ in
 exactly $|g\cap r|$ copies and meets an equality row in zero or two copies,
 so every $X$-row of the split commutes with every $Z$-row of the split. The
 $Z$-rows of the split are independent: in a vanishing combination of them,
 summing the coordinates over the copies of one qubit $q$ removes the
 equality rows (each contributes two copies of $q$) and leaves the parent
 combination's value at $q$; ranging over $q$, the parent combination
 vanishes, so its coefficients vanish by the parent's independence, and the
 equality rows of each qubit form a path, which is independent on its own.
 The $X$-rows of the split are independent because the parent's are. Hence
 $C^{(t)}$ is a valid state.
2. *Column weight and size.* A copy lies in at most two equality rows and in
 its assigned parent rows: at most $2+1$ for an inner copy and at most $1+2$
 for an end copy, so the $Z$ column weight of the split is at most three.
 Split rows keep their parent's weight and equality rows have weight two,
 so row weights do not grow. The split has $nt$ qubits and $m+n(t-1)$
 $Z$-rows, polynomial in the parent.
3. *Kernel correspondence.* Let $\varphi$ send a vector $v$ on $Q$ to the
 vector on the copies that takes the value $v_q$ on every copy of $q$. A
 vector on the copies satisfies every equality row if and only if it is
 constant on the copies of each qubit, that is, if and only if it equals
 $\varphi(v)$ for exactly one $v$. For every parent $Z$-row $r$, the overlap
 of $r^{(t)}$ with $\varphi(v)$ equals the overlap of $r$ with $v$, because
 $r^{(t)}$ holds exactly one copy of each qubit of $r$. So $\varphi$ maps
 $E(C,D)$ bijectively onto $E(C^{(t)},D^{(t)})$.
4. *Weight.* The weight of $\varphi(v)$ is $t$ times the weight of $v$.
 Minimizing over the bijection of step 3 gives the claimed equality, and
 the two sides are $\infty$ together.
5. *Hardness.* Deciding whether $w_{\mathrm{exp}}(C,D)\le w$ is in NP, the
 exposed vector being the certificate. Given any instance $(C,D,w)$ of the
 unrestricted problem, the instance $(C^{(t)},D^{(t)},tw)$ with
 $t=\max(1, c_{\max}-2)$ is computable in polynomial time, has $Z$ column
 weight at most three by step 2, and has the same answer by step 4. Composed
 with Theorem 24.1, whose instances carry no $X$-checks and which rests on
 the NP-completeness of syndrome decoding (Berlekamp, McEliece, and van
 Tilborg 1978; [`PRIOR_ART.md`](PRIOR_ART.md) §6), this shows the exposure
 price NP-hard on parents of $Z$ column weight at most three, already with
 no $X$-checks and with the row weights of the unrestricted instances.
 Q.E.D.

**What this settles, and what it does not.** Column weight two is exactly the
boundary: Theorem 25.1 on one side, the reduction above on the other. The
consumer's provider stays weight-2-only, and its refusal above weight two is by
design, an `unavailable` outcome in the sense of
[`spec/CLAIMS.md`](../spec/CLAIMS.md), with `citation_status` naming this
section. Not claimed here: hardness under a simultaneous bound on row weight
(the gadget leaves row weights as they were, so the question for parents
bounded on both sides stays open), anything about approximation, and anything
about further structure (planarity, bounded treewidth of the Tanner graph) that
might give polynomial special cases above weight two. The gadget is executable
in an internal experiment
(oracle-only enumeration; never a consumer path) and pinned by
`machine/test_weight3_split_reduction.py`; agreement there is evidence that the
transcription matches the derivation, not a proof.

## 4. Counting: relations of the form $d\ [\le,\ge,=]\ d' + k$

The human-review question, answered from §2:

- **Equalities (exact prices):** four — deletion price, gauging surviving-logical
 minimum, graft price, tower factorization — plus the exact direct sum, which
 the kernel already carries; since 2026-11-10 also the two peel
 prices, the opposite sector's exposure relation and the selected sector's
 avoidance minimum (§4.28), and the puncture reduction's price shape, which
 is recorded but not admitted.
- **Lower bounds:** three — gauging monotonicity $d' \ge d$, mixed-chain
 propagation, and the per-sector re-exposure bound; since 2026-11-10 also the
 peel's unpriced two-sided bound $d_\sigma - 1 \le d'_\sigma \le d_\sigma$ on
 the opposite sector, which is the one place a carried lower endpoint drops
 by exactly one.
- **Biconditionals:** two — safety at floor $d_\star$, and strict improvement.
- **Positive offset $k > 0$:** exactly **one** is extractable — strict
 improvement yields $d' \ge d + 1$ as integers, and only under its
 minimum-weight-class hypothesis. No source states a $+2$ upgrade, and none is
 claimed here. The carry table's conditional "strict improvement" cell
 therefore has one citable shape. Its hypothesis remains external and its
 source derivation has not been reproduced in this repository.

## 5. Relationship to `certificate-checked`

[`spec/CLAIMS.md`](../spec/CLAIMS.md) reserves `certificate-checked` for
machine-checked **per-state** certificates (a separate Gate 6-candidate
decision and assertion-language-axis release bump; no field may carry the
status until then). The admitted relations here are **conditional schemas**
whose hypotheses are consumer-supplied data about the input states, not
machine-checked certificates about one instance. On 2026-11-11
the status was admitted to the `stdCSS-3` candidate for per-state atomic
judgments. The mechanized checker landed the same day (
`lean/CodeCalculus/CertificateChecker.lean`); the Python kill-certificate
checker of `machine/certificates.py` stays the prototype, and the relations
here stay conditional schemas (`spec/CLAIMS.md`, *Admission* and *Mechanized
checker*).

## 6. What this note does not do

- **Carry-table changes are recorded in `spec/JUDGMENT_LAYER.md` §2a.** The base
 deletion cell remains $U' = U$ and the addition cell $L' = L$; the admitted
 conditional cells (exact deletion price, graft, strict improvement) are
 additive and do not replace them.
- **No claim status moves, and nothing here is tagged `established`.** FD7 rule
 B requires a derivation or citation to be *in this repository*; these rows are
 citations to companion drafts that record themselves as "split draft; not
 publication-ready" (dated 2026-09-16, content current 2026-10-16). Evidence
 statuses above are the **sources'** vocabularies, not this repository's
 ([`spec/CLAIMS.md`](../spec/CLAIMS.md) evidence axis), and are not
 translatable without an admission decision.
- **The 2026-10-19 admission minted three open obligations** for graft
 transition soundness, interval soundness, and price-input semantics. No
 obligation is discharged by the table or by the executable examples.
- **The consumer is now built** in `machine/priced_calculus.py`; this reference
 note does not specify its interface. It accepts explicit hypotheses and does
 not verify their truth.
- **§7 records a search procedure, not a relation.** It changes no row of §2,
 no carry-table cell, and no hypothesis type. Its one outstanding
 obligation is a check against a source document this repository does not
 hold.
- **It claims nothing about soundness.** As everywhere in this repository,
 agreement between an example and a rule is evidence, never confirmation.

## 7. An external search recipe for `C-ADD-CHECK` (recorded, not part of the calculus)

**Status:** a *consumer-side* procedure, recorded here because it is the
operational form of the strict-improvement cell and the project should not
rediscover it. **It is not a calculus rule, not a carry-table cell, and not
part of the consumer in `machine/`.** It computes the *hypothesis* that the
cell consumes; the calculus still only attests the implication.

**Provenance and its limits.** The structure below is the strict-improvement
relation already recorded in §2 (Proposition 18.3 and Corollary 18.4 of
*code-deformation*), read as a procedure. The 2026-10-20 review attributed
the operational recipe and its cost model to the challenge fieldnote of
2026-10-19 and left that attribution owed a check; **the check is done and
  the attribution is withdrawn as wrong** (the dated review disposition,
  2026-10-20). The fieldnote itself states no procedure or cost model — only
  that on the parents tried, no
support killed every minimum-weight logical class, so the rule "is
effectively a specification of a move that does not occur in this region".
This section is therefore this repository's own reading of Proposition 18.3
as a procedure; the odd-intersection condition is the definition of
anticommutation, not a quoted recipe.

**The procedure.**

1. **Enumerate the old minimum-weight logical classes.** Take the old code's
 classes of coset-minimum weight $d$, where $d$ is the exact old distance.
 This is the expensive step: Corollary 18.4 records minimum-weight
 enumeration as NP-hard in general, while commutation and span exclusion
 alone are cheap linear-algebra checks.
2. **Build candidate supports per class.** For each surviving class, the
 supports of an added check that would *anticommute* with it — that is,
 whose support meets the class's support in an **odd** number of qubits.
 The odd-intersection condition is what makes the added check kill the
 class rather than merely commute with it.
3. **Solve the parity hitting set.** Choose a support that meets *every*
 surviving class in odd parity, subject to the added check commuting with
 the opposite sector's rows and being independent of its own sector's rows.
 A class may also be killed by lying in the killed span
 $K=(S+\langle A\rangle)/S$ instead, which is the second disjunct of
 Proposition 18.3 and is the cheaper of the two tests.
4. **Certify the hypothesis.** If every old class of coset-minimum weight $d$
 is killed, the strict-improvement cell's hypothesis holds and the cell
 carries $d' \ge d+1$. If any class of weight $d$ survives, the cell does
 not apply — and a surviving weight-$d$ class cheaply witnesses $d'=d$.

**Cost.** Step 1 dominates and is NP-hard in general. Steps 2 and 3 are
linear algebra plus a hitting-set search over the candidate supports, and
step 4 is cheap. Corollary 18.4's split is the operative one: the *cheap*
half is commutation and span exclusion, the *expensive* half is the
minimum-weight enumeration.

**Where it pays, and where it does not.** The **distance-1** corner is cheap
by construction: a single commuting check that kills every weight-1 logical
satisfies the hypothesis, which is Proposition 18.3's condition instantiated
at $d = 1$, not a survey result. Everywhere the challenge fieldnote of
2026-10-19 looked — 0 strict improvements out of 736 valid single-check
additions for $n \le 10$, negatives bounded to $n \le 20$ parents and witness
search up to weight 6-8 — it found no yield, with the minimum-weight
enumeration as the cost that eats it. A "4 of 12 survivors" statistic for the
  distance-1 corner circulated in the 2026-10-20 review with no recorded run
  behind it and is **withdrawn as unrecorded** (the dated review disposition,
  2026-10-20). Those are
findings about the *search*, not about the cell: the cell is correct wherever
its hypothesis holds, and the hypothesis is the hard part.

**What this is not.** It is not a move, not a price, and not a new
hypothesis type: the strict-improvement cell's hypothesis remains "exact old
$d$ and an exhaustive minimum-weight-class enumeration, all killed", as
recorded in [`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md) §2a. A
search that has not enumerated the classes cannot supply the hypothesis, and
the cell stays `unavailable` for it.

## 8. The direct-sum exchange rate — a reproducible benchmark

**Status:** an *external empirical measurement*, cited here as a **v0.2
candidate input** to a proposed complexity-ladder classification (that
candidate is not implemented by this
section: the free/polynomial/exponential classification table is still owed
its own disposition, and none is taken here). It decides no gate, changes no
claim status, and discharges no obligation.

The one place the instrumented calculus's edge grows with $n$ — a
`C-DIRECT-SUM` step is $O(1)$ set work while computing the assembled code's
distance by brute force is exponential-shaped — is now a single-command
benchmark with recorded hardware and timing caveats:
an internal benchmark harness (not shipped). The ladder keeps
the study's $n = 7, 14, 21$ and adds $28$ and $35$:

| $n$ | $k$ | direct-sum fusion (s) | exact $d$ brute force (s) | ratio | candidates |
| --- | --- | --- | --- | --- | --- |
| 7 | 1 | $\approx 5\times10^{-6}$ | $\approx 1\times10^{-4}$ | $\approx 10^{1}$–$10^{2}$ | $2^{4}$ |
| 14 | 2 | $\approx 8\times10^{-6}$ | $\approx 3\times10^{-3}$ | $\approx 10^{2}$–$10^{3}$ | $2^{8}$ |
| 21 | 3 | $\approx 1\times10^{-5}$ | $\approx 1\times10^{-1}$ | $\approx 10^{3}$–$10^{4}$ | $2^{12}$ |
| 28 | 4 | $\approx 2\times10^{-5}$ | $\approx 2\times10^{0}$ | $\approx 10^{5}$ | $2^{16}$ |
| 35 | 5 | $\approx 2\times10^{-5}$ | $\approx 4\times10^{1}$ | $\approx 10^{6}$ | $2^{20}$ |

Numbers above are rounded readings of the recorded run; the file carries the
exact figures, the UTC timestamp and the machine block. Per
[`AGENTS.md`](../AGENTS.md), this is evidence — it can falsify a
candidate complexity reading and can never confirm soundness; the wall-clock
trend, not the constants, is the content, and the cited table is a
measurement of *this* brute-force instrument on one machine. The prior
measurement in the ablation study's §9 stands as recorded; the benchmark is its
reproducible successor, not a
correction of it.

## 9. Specializations of `C-ADD-CHECK` surfaced by the 2026-11-10 arXiv watch

**Status:** a *derived-procedure* note, not a new cell, not a new hypothesis
type. It records two constructions found by the 2026-11-10 arXiv watch triage
that reduce to the already-admitted `C-ADD-CHECK` conditional cell, so that
the calculus does not rediscover them and so that their hypothesis shape is
visible. It changes no row of §2, no carry-table cell, and no obligation.

### 9.1 Expurgation (Girard, arXiv 2611.08744)

**Move.** Promote low-weight logical operators of a primary code to
stabilizers, after enumerating every logical operator below a target distance,
so that each low-weight logical anticommutes with at least one promoted
operator; optionally puncture first and repair. Increases distance at cost in
\(k\).

**Reduction to `C-ADD-CHECK`.** Promoting a logical operator to a stabilizer
is adding a check whose support is a physical representative of that logical:
it commutes with the opposite sector (because the representative is a logical)
and is independent of its own sector (because it was not already in the row
space). The added rows are supplied as check data; \(n\) and the original
generators are preserved; \(k' = k - r\). Hence the whole procedure is a
finite sequence of `C-ADD-CHECK` commands, and the strict-improvement cell's
hypothesis (Proposition 18.3 / Corollary 18.4) is exactly the condition that
every minimum-weight logical class is killed. **No new cell.**

**Hypothesis supplied by the consumer.** An exhaustive enumeration of the old
code's minimum-weight logical classes and a parity hitting-set selection over
them. This is the same NP-hard hypothesis as the strict-improvement cell
(Corollary 18.4); the paper's meet-in-the-middle enumeration up to
\(4\times10^{13}\) Pauli operators is one way to supply it. The calculus
attests the implication and records the source; it does not compute or validate
the enumeration.

### 9.2 Logical Protection Code augmentation (Rabeti et al., arXiv 2611.07062)

**Move.** Impose additional stabilizer constraints on selected logical qubits of
a primary code via an auxiliary LPC (Logical Protection Code); decode by
conditioning belief propagation on LPC-syndrome hypotheses.

**Reduction to `C-ADD-CHECK`.** The augmented code differs from the primary code
only by the rows \(G_X L_X\), \(G_Z L_Z\), which are vectors in
\(\mathbb F_2^Q\) (the \(L\)'s are physical representatives). Commutation with
the opposite sector and same-sector independence are the standard
`C-ADD-CHECK` premises (verified in
[`PRIOR_ART.md`](PRIOR_ART.md), §*Logically augmented CSS codes*).
**No new cell.** The decoding half (HLLD, BP conditioning) is a decoding
procedure and is out of the calculus's scope (code lineage/decoder is
consumer-side); it does not move any obligation or claim status.

### 9.3 What these do not change

Neither construction earns a distinct operation identifier under
[`spec/TAXONOMY.md`](../spec/TAXONOMY.md) §3.8: the state update is
identical to `C-ADD-CHECK`, and the only added content is a *recipe* for
choosing the added rows (via an LPC or an enumeration). They are recorded here
as hypothesis sources and worked examples of `C-ADD-CHECK` sequencing, not as
taxonomy entries or grammar productions.

## Sources

Both sources live outside this repository, in the companion research tree, and
are cited by path rather than by link:

- *A distance ledger for code deformation* (companion research tree) — *A distance ledger for code
 deformation: exact pricing and sound chaining for the standard moves*.
 Split draft, 2026-09-16; content current 2026-10-16. Citations verified
 2026-10-18 against the companion manuscript, claim ledger, and proof-ledger
 statements. Numbering convention: manuscript theorem numbers are local; named IDs
 retain legacy numbers (Theorem 7 = proof-ledger Theorem 12.1; Theorem 7′ =
 Theorem 18.1 + Proposition 18.2).
- *Merge Conflict: factor distances cannot tell you how CSS codes compose* (companion research tree) — *Merge Conflict: factor
 distances cannot tell you how CSS codes compose*. Split draft, 2026-09-16;
 content current 2026-10-16. Citations verified the same way. The identifier
  map in the companion manuscript's Appendix C.1 is authoritative: "MS Theorem 5" =
 "proof-ledger Theorem 7.1", and the split bound "MS Theorem 4" is not the seam
 result and not the graphlike special case "MS Theorem 3".

Read scope of the verification: statement text and claim rows of each
repository's manuscript, claims ledger and proof ledger; proofs themselves not
re-derived; toy scripts and review notes not read. The rows above may not be
cited past what that read covers.

---

## Disposition (2026-11-10)

- **Tower sweep for `k_in > 1`.** Landed 2026-11-11: the
 level-data provider is derived in §2a for arbitrary `k_in` and swept against
 exhaustive enumeration at `n_in = 4`, `k_in` in 1, 2, 3
 (`machine/experiments/tower_sweep.py`, `machine/test_tower_sweep.py`); the
 cost-table size `2^{2 k_in}` is recorded in §2a and in the complexity ladder
 below. Theorem 27.8 itself is cited, not reproduced.
- **Complexity-ladder documentation and benchmark.** Accepted: complete the
 free/polynomial/exponential classification table and an ablation-style
 benchmark (internal harness) that already reproduces the direct-sum
 exchange-rate table (default ladder n=7,14,21 under a second; a `--full`
 mode is recorded in the benchmark results).



---

## 6. Complexity ladder (dispositioned 2026-11-10C5)

Classification of the quantities the calculus and its consumer touch. "Free" means
read directly from the state or its display; "polynomial" means computable in
time polynomial in the size of the presented state (and layout, where noted);
"exponential" means no polynomial algorithm is claimed and the source records a
hardness result or an enumeration. A consumer-supplied hypothesis is not
classified here: its cost is the consumer's, not the calculus's.

| Quantity | Cost | Band | Notes |
| --- | --- | --- | --- |
| `n`, `k` | free | cheap | read from the presented state |
| qubit namespace / `used` | free | cheap | finite enumeration (70,000 names) |
| canonical mint | free | cheap | first unused name in fixed order |
| Tanner components / connectivity | polynomial | cheap | union-find over displayed rows |
| interaction radius `r` | polynomial | cheap | exact rational arithmetic over supplied coordinates (§2d) |
| layout honesty | polynomial | cheap | occupancy and minimum site distance |
| graphlike exposure price `w_exp` (column weight ≤ 2) | polynomial | cheap | BFS on the sector incidence graph (Theorem 25.1) |
| exposure price `w_exp` (column weight 3 and above) | exponential / NP-hard | hard | column-splitting reduction from the general case (§3a, 2026-11-10); the provider refuses by design |
| deletion price `w_del`, `w_exp` (general) | exponential / NP-hard | hard | minima over cosets; Theorem 24.1 for `w_exp` |
| re-exposure `w_re` (general) | exponential / NP-hard | hard | Proposition 5.2 (*composition-distance*) |
| re-exposure `w_re` (admitted `E-GLUE`, any seam) | free | cheap | no re-exposed class exists, so `w_re` is `+inf` on every admitted glue (`OPERATIONAL_SEMANTICS.md` §4.33); the glued sector distance from factor class pairs costs `2^{k_A + k_B}` pairs given the factor class dictionaries |
| strict improvement (feasibility screen) | polynomial screen + exponential enumeration | cheap (screen) + hard (enumeration) | linear-algebra exclusion is cheap; full minimum-weight-class enumeration is NP-hard (Corollary 18.4); the consumer's bounded enumeration fallback caps the search and carries a `heuristic_outcome` record |
| sector-aware gauging prices `w_X`, `w_Z` | exponential (consumer-supplied) | hard | minima over surviving logical classes (Lemma 18.5) |
| tower factorization (`k_in = 1`) | polynomial in level data | cheap | Theorems 27.2 / 27.5; no normalizer enumeration; §2a: the inner sector distance times the outer price |
| tower factorization (`k_in > 1`) | exponential table | hard | cost tables of size `2^{2 k_in}` (Theorem 27.8); the §2a provider uses two dictionaries of `2^{k_in}` entries and an outer-level search; sweep landed 2026-11-11 |
| direct-sum extinction (structural side) | polynomial | cheap | rank checks on the two blocks |
| exact distance `d` | exponential / NP-hard | hard | external oracle only; never a calculus move |
| `E-PEEL` avoidance minimum `w_avoid` | exponential / NP-hard | hard | minimum over a logical class (§4.28, 2026-11-10) |
| `E-PEEL` exposure minimum `w_expose` (bound to peel) | exponential / NP-hard | hard | minimum over a logical class; the graft's exposure price at `m = 1` (§4.28, 2026-11-10) |
| `bounded_support_search` | bounded enumeration under `budget` / `max_weight` | bounded | enumerates supports by weight; a found witness tightens the affected sector's upper endpoint through the consumer's transport; carries no `heuristic_outcome` record; no lower endpoint is ever raised |
| `bounded_sector_search` | bounded enumeration under `budget` | bounded | interval transport only; attaches a `heuristic_outcome` record |

**Cheap, bounded, or hard.** Each row of the table above is tagged with a band
in the new column: **cheap** (free or polynomial — direct-sum fusion, canonical
mint, Tanner components, graphlike exposure price, tower factorization at
`k_in = 1`, the strict-improvement linear-algebra screen, and the rest tagged
cheap), **bounded** (an otherwise exponential search capped by a recorded
budget — `bounded_support_search`, `bounded_sector_search`, and the
strict-improvement enumeration fallback), and **hard** (no polynomial algorithm
claimed — exact distance, general deletion/exposure/re-exposure minima,
exposure price from column weight 3 on, tower factorization at `k_in > 1`,
sector-aware gauging prices, and the `E-PEEL` avoidance and exposure minima).
Of the three bounded searches, only the strict-improvement enumeration
fallback and `bounded_sector_search` attach a `heuristic_outcome` record; `bounded_support_search` carries no such record, and a witness it finds
tightens the affected sector's upper endpoint through the consumer's transport
rather than moving a ledger endpoint itself. A consumer-supplied hypothesis is
not classified here; its cost is the consumer's, not the calculus's.

**Benchmark (internal).** an internal harness reproduces the direct-sum
exchange-rate table (default ladder `n = 7, 14, 21` in under a second;
with hardware and timing
caveats). Abstraction benchmarks for newly admitted providers are owed by the
accepted candidates above.
## 5a. Re-exposure in constrained splits (dispositioned 2026-11-10C1; derived 2026-11-11)

For the admitted `E-GLUE` transition (two factors on disjoint qubit sets plus
admissible seam checks) no class is re-exposed: every logical of the glued
state restricts to a logical of at least one factor, so the re-exposure
minimum `w_re` is `+inf` on every admitted glue and the per-sector bound
carries no re-exposure term ([`spec/OPERATIONAL_SEMANTICS.md`](../spec/OPERATIONAL_SEMANTICS.md)
§4.33, `OBL-GLUE-RE-EXPOSURE`). The same derivation gives the glued sector
distance exactly as the least sum of factor class weights over the class
pairs that commute with the opposite-sector seam checks and are not absorbed
by the same-sector seam checks, a relation on factor class data and seam data,
not on factor distances alone, so the obstruction row of §2 stands. The
question of `w_re`'s polynomiality on monotone top-to-bottom seams therefore
does not arise on the admitted scope. The NP-hardness of `w_re` (Proposition
5.2, *composition-distance*) and the split bound's `w_re` term concern that
source's shared-interface splits, where the two pieces overlap on qubits; the
calculus has no such composition. The 2026-11-10 sketch, that on monotone
seams with equal move words a re-exposed class must cross the seam and the
lightest one is a shortest seam-crossing path in the combined factor graph,
describes that unadmitted setting; it is kept here as a sketch only, is not
derived, and must not be cited as a result.
