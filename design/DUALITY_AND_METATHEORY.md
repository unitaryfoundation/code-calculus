# Duality, approximation, and the missing metatheory

**Status:** non-normative design note. It discharges no obligation, admits no
operation, property, or judgment, and changes no claim status. Where it and
[`spec/`](../spec/) disagree, `spec/` wins.

**Role:** records three foundational readings of the calculus—code/matroid
duality for the move set, the abstract-interpretation reading of the interval
ledger, and the resource/rewriting metatheory for the frame and order
obligations—and states the probabilistic boundary. None of these is a new
calculus rule.

---

## 1. Why this note exists

The move set is a set of classical code operations: removing a check row
restricts a row space, removing a qubit punctures a coordinate, and the
admitted Gate 6 extensions vary those two themes. The repository records the
resulting distance behaviour case by case, and records several refutations:
the scalar graft price (§4.13/§4.20 of
[`spec/OPERATIONAL_SEMANTICS.md`](../spec/OPERATIONAL_SEMANTICS.md)), the
peel and puncture carries (§4.28/§4.29), and the $\Delta\neq\varnothing$
extension (§4.30). Those records are correct as far as they go, but they do not
name the common structure.

The common structure is **duality**. Puncturing and shortening are dual
classical operations; the two CSS sectors are dual-type objects; the
$T=Q$ local Hadamard is the sector swap. The repository already uses the word
once — [`LEADERBOARD_TAXONOMY.md`](LEADERBOARD_TAXONOMY.md) calls puncturing
"the classical dual of shortening" — but no `spec/` artifact uses the duality
to organize a cell or to predict a refutation.

The second observation is that the ledger is already an abstract
interpretation, and the third is that the metatheory has a standard proof
architecture the repository has not named. The probabilistic boundary is
included because it is the one place where a new claim modality is tempting and
must be separated from the existing four outcomes.

**What this note is not.** It is not a proof, a soundness argument, a
completeness claim, or a release proposal. It does not compute a distance. It
does not add a state field. It does not change any `proved`, `conditional`,
`open`, or `unavailable` label.

---

## 2. The duality dictionary

### 2.1 Classical codes

For a linear code $C\le\mathbb F_2^n$ and a coordinate $i$:

- the **puncture** $P_i(C)=\{(v_j)_{j\neq i}:v\in C\}$ deletes the coordinate;
- the **shorten** $S_i(C)=\{(v_j)_{j\neq i}:v\in C,\ v_i=0\}$ keeps only the
 codewords that vanish there, then deletes the coordinate.

The two are dual:

$$
P_i(C)^\perp=S_i(C^\perp),
\qquad
S_i(C)^\perp=P_i(C^\perp).
$$

Equivalently, a linear code is a represented binary matroid on its coordinate
set: puncturing is matroid deletion, shortening is matroid contraction, and the
dual code is the dual matroid. The weight enumerator and its dual are related
by MacWilliams; the Tutte polynomial specializes to the weight enumerator and
carries the deletion–contraction recurrence.

**Mechanized Galois-connection form.** On vector
predicates ordered by length-indexed inclusion, zero-extension at $i$ is left
adjoint to $S_i$ (`zeroExtend_adj_shorten`), $P_i$ is left adjoint to preimage
under coordinate drop (`puncture_adj_pullDrop`), and $(-)^\perp$ is an antitone
Galois connection (`sub_dualCode_iff_symm`) that intertwines the two pairs via
the bilinear transpose $\langle \iota_i u, v \rangle = \langle u, \pi_i v \rangle$
(`dotPar_insertAt_false` in [`lean/CodeCalculus/ExactPeel.lean`](../lean/CodeCalculus/ExactPeel.lean)),
yielding $P_i(C)^\perp = S_i(C^\perp)$ (`dualCode_puncture_iff_shorten_dualCode`)
and $P_i(C^\perp) \subseteq S_i(C)^\perp$
(`puncture_dualCode_sub_dualCode_shorten`) in
[`lean/CodeCalculus/DualityAdjunction.lean`](../lean/CodeCalculus/DualityAdjunction.lean).
No category-theory library is imported ([`spec/GATES.md`](../spec/GATES.md) §11).

This is the language the move set is missing.

### 2.2 CSS codes

A presented CSS state carries two classical row spaces $X,Z\le\mathbb F_2^Q$
with $X\subseteq Z^\perp$ (and symmetrically). Its sector logicals are

$$
\mathcal L_X=Z^\perp/X,
\qquad
\mathcal L_Z=X^\perp/Z,
$$

and the distances are the minimum weights of the nontrivial classes. The
sector swap $H^{\otimes Q}$ exchanges $X$ and $Z$, hence exchanges
$\mathcal L_X$ and $\mathcal L_Z$ and swaps $d_X,d_Z$. The $T=Q$ instance of
`E-LOCAL-HADAMARD` is exactly this exchange
([`spec/OPERATIONAL_SEMANTICS.md`](../spec/OPERATIONAL_SEMANTICS.md) §4.27,
[`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md) §2f), and its involution
and transition-conjugation laws $H(m_\sigma(C)) = m_{\bar\sigma}(H(C))$ across
the kernel and Gate 6 state updates are derived in
[`DERIVED_RELATIONS.md`](DERIVED_RELATIONS.md) §2b and mechanized in
[`lean/CodeCalculus/DualityAdjunction.lean`](../lean/CodeCalculus/DualityAdjunction.lean).

So the CSS state is not one matroid but a pair of classical codes with an
orthogonality constraint. The "dual" of the pair is the sector swap. That is
the sense in which the two sectors are dual-type objects, and it is why a
one-sided rule on one sector can fail while the other sector behaves.

### 2.3 The move dictionary

The table is deliberately stated as a **dictionary**, not as a theorem. The
"classical shadow" column names the operation the transition most closely
implements; the "dual reading" column names what the duality predicts; the
"repo record" column says whether the prediction is already visible.

| Move | Classical shadow | Dual reading | Expected effect | Repo record |
| --- | --- | --- | --- | --- |
| `C-SKIP` | identity | identity | all properties carry | §2 table, `[proved]` |
| `C-DIRECT-SUM` | disjoint union / direct sum | independent composition (separating conjunction / tensor in the resource reading) | $d=\min(d_A,d_B)$, $k=k_A+k_B$ | §2 table, `[proved]`; `OBL-DIRECT-SUM-LAWS` |
| `C-DELETE-CHECK` | remove a generator/check row: restrict the sector row space | the dual move extends the dual row space | the sector distance cannot increase; exact value is `unavailable` | §2 table and §4; `OBL-ORDER-INDEPENDENT-DELETION` |
| `C-ADD-CHECK` | add a generator/check row: extend the sector row space | the dual move restricts the dual row space | the sector distance cannot decrease; strict improvement is conditional | §2 table and §2a; strict-improvement cell |
| `E-PEEL` | remove a qubit in exactly one selected-sector row, remove that row, shorten the opposite rows | mixed puncture/shorten | selected sector lower carries ($d_\tau'\ge d_\tau$); opposite sector upper carries ($d_{\bar\tau}'\le d_{\bar\tau}$); full-distance upper carries the opposite upper | §4.28 |
| `E-PUNCTURE` | remove a qubit and every displayed row touching it (the induced stabilizer update) | coordinate puncture plus the induced row shortening | the touched sector may lose its lightest logical; the other sector may also change | §4.29 refutation ($d_X:1\to2$) |
| `E-GRAFT` | replace a chain by adjacent products and remove the spliced qubit | row-space 2-sum/minor-type move | the spliced sector's non-increase fails; the non-spliced sector is where exposure is priced | §4.13/§4.20 refutation |
| `E-EXTEND` | add rows; optionally add qubits | extension; the $\Delta=\varnothing$ case is the add-check dual | $\Delta=\varnothing$ reduces to `C-ADD-CHECK`; $\Delta\neq\varnothing$ has no distance rule | §4.30 |
| `E-GLUE` | glue two factor codes along a seam | gluing/descent, not a matroid minor | the seam certificate is conditional; factor data plus connectivity is insufficient | [`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md) §2e |
| `P-REBASE` | invertible row-space basis change | presentation change, not a code change | every span-expressible property carries exactly | §4.26; `OBL-REBASE-GENERATION` |
| `P-RELABEL` | qubit relabeling | coordinate permutation | presentation equivalence, not a state change | [`spec/TAXONOMY.md`](../spec/TAXONOMY.md) §1.4 |

**Why this is not a relabeling exercise.** The classical puncture $P_i(C)$ is
not the same as `E-PUNCTURE`: the transition also deletes every displayed row
that touches the qubit, because raw column restriction without the induced
stabilizer update is not a CSS operation
([`spec/CLAIMS.md`](../spec/CLAIMS.md), `E-PUNCTURE` card). That extra row
deletion is the load-bearing difference. The duality does not paper over it; it
predicts why the naive carry fails. The same caveat applies to `E-PEEL`, where
the selected-sector row is removed and the opposite-sector rows are shortened.

### 2.4 What the dictionary explains

1. **The one-sided/no-rule pattern.** Puncturing one code shortens its dual, so
 a rule stated only on the punctured sector cannot have a single polarity.
 The §4.29 witness ($d_X:1\to2$) is the expected shape, not an anomaly.
2. **The peel's two failures.** `E-PEEL` is a mixed puncture/shorten: the
 selected sector loses a row (shortening-type) while the opposite sector is
 shortened at the qubit. A single-polarity carry is not available, which is
 what §4.28 records.
3. **The graft's spliced sector.** The graft replaces a chain by adjacent
 products. The scalar form $d'=\min(d,w_{\mathrm{expose},\bar\tau})$ treats
 the operation as if it were a single-sector exposure; the sector-wise
 reading is the one the transition licenses. The 2-sum/minor reading predicts
 that the spliced sector is not carried exactly.
4. **The local Hadamard symmetry.** `E-LOCAL-HADAMARD` at $T=Q$ is the sector
 swap, so $d_X'=d_Z$, $d_Z'=d_X$, $d'=d$ is a symmetry statement, not a
 special case.
5. **A home for the extended-state layer.** `X-SYMPLECTIC-DOUBLE` and
 `X-SYMPLECTIC-HALVE` are the self-dual/duality-data case. The deferred
 non-CSS layer is where the pair-of-codes picture becomes a single stabilizer
 object.
6. **A price check.** MacWilliams and the Tutte polynomial give exact
 identities relating a code's weight enumerator to its dual's. They are not
 efficient algorithms, and this note does not claim they yield a price; they
 are a check on the $w_{\mathrm{del}}$/$w_{\mathrm{exp}}$ formulas and a
 source of proof obligations for a future price provider.

### 2.5 What it does not buy

- **No exact distance.** The duality is structural. It does not compute a
 minimum weight, and it does not close the `unavailable` cells.
- **No completeness.** It does not make the calculus complete, and it does not
 weaken the deliberate-incompleteness position
 ([`SCOPE.md`](SCOPE.md) §2).
- **No new state field by itself.** Treating the dual code as a first-class
 datum would be a state-model/Gate 6 decision, not an inference from this
 note.
- **No proof of the dictionary.** The table is a reading of the transitions and
 the refutations. Checking each row against the exact transition is the
 follow-up work; the row-space restriction and coordinate deletion are
 different operations, and the dictionary must keep them apart.

---

## 3. Abstract interpretation: the interval ledger

The interval ledger ([`machine/intervals.py`](../machine/intervals.py)) is an
abstract interpretation: concrete domain $D=\mathbb N\cup\{+\infty\}$, abstract
intervals $[L,U]$, concretization $\gamma([L,U])=\{d:L\le d\le U\}$, one
transformer $F_m$ per primitive, and the local-soundness-plus-monotonicity
theorem (`OBL-PRICED-INTERVAL-SOUNDNESS`).

Four structural points govern how this abstract domain behaves.

### 3.1 The order discipline

Ordering intervals by **reverse inclusion** places exact singletons at the
bottom and $[0,+\infty]$ at the top. That is a *precision* order. The standard
abstract-interpretation soundness schema is stated in the **information**
order, where $[0,+\infty]$ is the top (no information) and exact singletons are
maximal. The two are dual, and mixing them turns "monotone" into "antitone"
without warning.

There is a second issue: the interval poset is not a complete lattice in the
precision order. Singletons are minimal but not unique, and the meet of
disjoint intervals is empty, which is not in the domain. For straight-line
composition that is harmless. For a fixpoint or widening argument it is not:
one should either use the information order with an explicit $\varnothing$ (or
a flat domain), or state the fixpoint theorem in the precision order and prove
the required completeness separately. Each theorem should name the order it uses.

### 3.2 The reduced product

The ledger keeps $d$, $d_X$, $d_Z$ as three independent intervals, constrained by
$d=\min(d_X,d_Z)$. The independent product loses the correlation. The simple
projection closure is:

- raise each sector's lower endpoint to the full lower endpoint
  ($d\le d_\sigma$);
- raise the full lower endpoint to the minimum of the sector lowers
  ($d\ge\min(d_X,d_Z)$);
- lower the full upper endpoint to the minimum of the sector uppers
  ($d\le\min(d_X,d_Z)$).

While a synthetic ledger with $d\in[0,10]$ and $d_X,d_Z\in[5,10]$ moves from
`re-measure` to `certify` at target $5$ under this closure, on the current
rule set the easy half of the correlation is already maintained by the existing
rules. The interesting half is **disjunctive** — "at least one sector is at
least $L$" — and three independent intervals cannot represent it. A genuinely
more precise domain would need a relational or disjunctive component.

### 3.3 Fixpoint and widening

The composition theorem is for a finite sequence. The consumer planner is
depth-bounded and greedy
([`machine/planner.py`](../machine/planner.py)); a real "certify/prune/
re-measure until decided" loop is a fixpoint. If the planner ever iterates to
closure — repeated deletion chains, a worklist, repeated refinement — the
per-step soundness theorem no longer covers the loop. A fixpoint semantics and
a widening/narrowing argument (or an explicit bounded-unfolding theorem) are
then owed.

This is not a defect in the current planner: its depth bound is an honest
consumer policy. It is a gap in the *theory* of the loop, and it becomes
load-bearing the moment the loop is used to justify a claim.

### 3.4 Refinement as an oracle

`re-measure` is an oracle refinement step. Abstract interpretation gives the
right statement: refinement shrinks $\gamma$, so a `certify` after refinement
is still sound, and refinement only improves precision. This separates
**soundness** (never certify a false target) from **economy** (do not
re-measure when the interval suffices). The current design states the economy
property informally; the AI reading gives it a place to live.

### 3.5 `unavailable` is not the top

The plan's best line is that `unavailable` is the **absence of a transformer**,
not a value of "unknown." That is exactly right, with one qualification:
absence is relative to the chosen signature and domain. The top interval
$[0,+\infty]$ is still a value; `unavailable` is "there is no $F_m$ here." The
question of whether $F_m$ is the *best* correct transformer is a completeness
question, not a soundness one. Do not conflate the two: a sound but imprecise
transformer is the normal case, and the four-outcome vocabulary already
distinguishes "no information" from "deliberately withheld."

---

## 4. Probabilistic formal methods: the boundary

Probabilistic methods do not weaken soundness. They give a language for the
side the repository already cares about — the falsification side — and they
make the existing informal statements precise.

### 4.1 One-sided error

A witness is a sound upper bound. A randomized search that finds no witness is
**not** a lower bound. The honest statement is:

$$
\Pr[\text{the sampled family contains a witness of weight }<L]\le\delta.
$$

That is a statistical claim about the search, not the claim $d\ge L$. The
qLDPC replay's "2860 randomized refuter trials find no lighter logical ... not
a lower-bound certificate" is the informal version of this sentence. The
formal version is a **probabilistic claim shape** with an explicit event and
$\delta$ — a new claim shape, not a new evidence status, and not an overload of
`conditional` (which means "under explicit hypotheses," not "with
probability"). It would be an assertion-language change and therefore a
release bump under [`spec/VERSIONING.md`](../spec/VERSIONING.md). It must never
upgrade `unavailable` to `proved`.

### 4.2 Randomized moves

If a move is randomized — a random code ensemble, a random graft, a random
deletion — the state becomes a distribution, and the ledger becomes a
distribution over intervals. Soundness becomes almost-sure soundness or an
expectation bound. The right semantics is a monad (Giry/quasi-Borel) plus a
quantitative judgment; the right proof rule is pRHL-style, with couplings and
union bounds. This is a new *effect*, not a new cell, and it is a scope change.

### 4.3 Probabilistic abstract interpretation

If the project wants the ensemble reading, probabilistic abstract
interpretation (linear-operator semantics over the abstract domain) is the
technical vehicle. It gives expected/typical distance under an ensemble —
useful for the consumer's ranking, not for the calculus's worst-case
judgments. Concentration inequalities (union bounds over logicals, matrix
Chernoff, martingales) give ensemble statements, not per-state ones. A
coupling or stochastic-dominance order is the right generalization of the
interval order if prices become distributions.

### 4.4 The hard rule

The repository's rule that empirical work can falsify but never confirm
soundness is exactly the right boundary. Probabilistic methods can quantify
the **refuter's power** — a completeness statement — without touching
soundness. They cannot make the soundness theorem probabilistic without a new
theorem, a new threat model, and a new claim modality. If that is wanted, it
is a product decision, not a proof shortcut.

---

## 5. The metatheory: separation, traces, proof search

The project's proof burden is concentrated in the frame, order, and
associativity obligations. Three standard TCS architectures apply.

### 5.1 Separation logic and the frame law

`OBL-FRAME-LAW` has the shape of the frame rule of separation logic. The
disjoint qubit namespaces and disjoint `used` sets of `C-DIRECT-SUM` are the
resource invariant; the direct sum is the separating conjunction/tensor; a
property that mentions only one summand carries across the other. Proving the
frame rule once from the disjointness invariants would replace the bespoke
argument, and it would explain why the `used`-disjointness premise is
load-bearing rather than hygiene (the `W21` counterexample is exactly a
resource-invariant failure).

### 5.2 Trace theory and rewriting

`OBL-ORDER-INDEPENDENT-DELETION`, `OBL-CROSS-SECTOR-PERMUTATION`,
`OBL-SEQUENCE-ASSOCIATIVITY`, and `OBL-PRIMITIVE-DETERMINISM` are properties of
a deterministic rewriting system: independence of disjoint moves, conditional
permutation, associativity of composition, and uniqueness of the step. The
canonical mint makes the system deterministic (there is no fresh-name choice),
so the standard tools — Newman's lemma, critical pairs — apply once a
termination measure is fixed.

This is the natural proof architecture for deriving several rewriting laws from
one abstract rewriting theorem instead of proving them one by one.

### 5.3 Proof search and the `not derivable` claim

The decidability argument owed for the `W13` refutation
is a completeness-of-proof-search question:
absence in one search is not absence of all derivations unless the search is
complete. A cut-elimination or focusing theorem for the L3 rule system — or a
semantic countermodel — would turn "no derivation closes" into a theorem
rather than a search artifact. The current argument ("the schema condition
fails to fire") is a search argument; it is correct for the instance, but it is
not the general theorem the vocabulary's `not derivable` label would need.

### 5.4 Sheaf and descent for `E-GLUE`

The `E-GLUE` seam certificate is a descent condition: local factor data plus a
compatible seam should glue to a global code. The no-go row ("factor data plus
connectivity is insufficient, so a flat-DEM check must return
`inconclusive`") is a descent obstruction. A sheaf on the poset of patches
would make the obstruction precise and give the seam certificate a cohomological
home. This is narrower than the other items — the current scope is
monotone top-to-bottom seams on the planar surface code — and its concrete
linear-algebraic content is already cashed out in
[`spec/OPERATIONAL_SEMANTICS.md`](../spec/OPERATIONAL_SEMANTICS.md) §4.33
(`OBL-GLUE-RE-EXPOSURE`, mechanized in `lean/CodeCalculus/ExactGluePairs.lean`
and `ExactGlueDistance.lean`): $L_\sigma(C) \cong K_\sigma / W_\sigma$, where
$K_\sigma = \bigcap_{t \in T_\tau} \ker \phi_t$ is the 0-cocycle kernel of
factor logical pairs commuting with the opposite-sector seam and
$W_\sigma = \mathrm{span}(\pi(T_\sigma))$ is the 0-coboundary subspace absorbed
by the same-sector seam. In the current scope, the sheaf/fibration framing stays
a descriptive reading rather than a separate constructor or proof obligation.

### 5.5 A bilattice for the four outcomes

The four outcomes — `false`, `not derivable`, `unavailable`, `not yet defined`
— are explicitly **not** a partition
([`spec/CLAIMS.md`](../spec/CLAIMS.md), *Outcome vocabulary*). They separate
truth, derivability, and deliberate exclusion. A bilattice with a truth order
and an information order (Belnap–Dunn) is a candidate structure for the
two-axis reading: `unavailable` records a design commitment rather than an
information gap, while `not derivable` records a gap in the current rule
system. The vocabulary does not need to change; the lattice would explain why
the labels are not disjoint and give transport a monotonicity statement.

### 5.6 Resource theory as the umbrella

A priced construction calculus has the shape of an ordered monoid of
conversions with monotones: the properties are the monotones, the moves are the
conversions, and the prices are the costs. That is a high-level reading of the
project, not a claim it has already been stated that way.
The ordered-monoid core is not category theory, so it does not collide with the
non-goal in [`spec/GATES.md`](../spec/GATES.md) §11; the categorical dressing
would, and is not needed.

---

## 6. Open design directions

1. **Duality dictionary.** Checking each row of the move dictionary (§2.3)
   against its exact transition semantics remains open follow-up work; adding
   a dual-code presentation datum to the state model would require a separate
   specification decision.
2. **Relational / disjunctive interval domain.** Extending the three-interval
   ledger to represent disjunctive sector constraints ("at least one sector is
   at least $L$") is a future consumer-domain design choice.
3. **Probabilistic claim shape.** Any randomized refuter or ensemble bound must
   remain separated from worst-case soundness via an explicit `probabilistic`
   claim shape with a stated event and $\delta$ ([`spec/CLAIMS.md`](../spec/CLAIMS.md)).
4. **Proof architecture.** Separation logic, trace rewriting, cut-elimination
   for `not derivable`, sheaf descent, and bilattice orderings offer unified
   proof architectures for the Lean development without changing the underlying
   calculus cells.

---

## 7. What this note does not do

- It adds no operation, no property, and no judgment.
- It changes neither $\equiv$, `used`, nor the canonical mint.
- It does not make the calculus complete, and it does not weaken the
  deliberate-incompleteness position.
- It discharges no obligation, passes no gate, and admits no cell.
- It is not evidence for soundness.
- It does not claim the duality dictionary is a theorem; checking each row
  against the exact transition is separate follow-up work.
