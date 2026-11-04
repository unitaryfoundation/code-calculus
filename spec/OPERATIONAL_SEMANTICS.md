# Operational Semantics

**Status:** normative. The transition relation: which terms have an evaluation
derivation, and what state they yield.

This document consolidates the proposal's operational semantics.

---

## 1. The relation

$$
\operatorname{Eval}(m,\,S,\,S')
$$

is a **partial big-step** relation over phase-insensitive presented CSS states.
There is no judgment when a command is inapplicable, and no partial result is
ever exposed: no residual commands, no half-updated states.

$$
\operatorname{Eval}(m\triangleright e,\, S')
\quad\text{when}\quad
\operatorname{EvalExpr}(e,\,S)\ \text{and}\ \operatorname{Eval}(m,\,S,\,S')
$$

**Base rule.** $\operatorname{Eval}(\operatorname{skip}, S, S)$.

**Sequencing.**

$$
\frac{\operatorname{Eval}(m_1,S_0,S_1)\qquad\operatorname{Eval}(m_2,S_1,S_2)}
 {\operatorname{Eval}(m_1;m_2,S_0,S_2)}
$$

If either subcommand is inapplicable the sequence has **no** evaluation
derivation. Associativity and denotational adequacy are
`OBL-SEQUENCE-ASSOCIATIVITY` — proof obligations, **not assumed equations**
(the denotation the adequacy half is stated against is §1a).

## 1a — The derived denotation

The relation above is the **primary** semantics, and the denotation is derived
from it. The disciplines that remain in force: erasure of `steps`, no
consequence and no computation, and the `Option`-shaped carrier.

$$
\llbracket m\rrbracket(S) \;=\;
\begin{cases}
\mathsf{some}\ S' & \text{if } \operatorname{Eval}(m,\,S,\,S'),\\
\mathsf{none} & \text{otherwise,}
\end{cases}
\qquad
\llbracket e\rrbracket \;=\;
\begin{cases}
\mathsf{some}\ S & \text{if } \operatorname{EvalExpr}(e,\,S),\\
\mathsf{none} & \text{otherwise.}
\end{cases}
$$

Adequacy is definitional in this direction: $\operatorname{Eval}(m,S,S')$
holds iff $\llbracket m\rrbracket(S) = \mathsf{some}\ S'$, by the clause
itself. The clause reads $\llbracket m\rrbracket(S) = \mathsf{some}\ S'$ for
the unique $S'$ with $\operatorname{Eval}(m,S,S')$, and $\mathsf{none}$ if
there is none; uniqueness is §4.8's determinism derivation for the five MVP
primitives (`C-SKIP`, `C-DIRECT-SUM`, `C-DELETE-CHECK`, `C-ADD-CHECK`,
`C-SEQUENCE`) and the explicit update functions of the §2 and §4 transitions
(`graftState`, `rebaseState`, and so on) for the rest. The mechanized relation
is literally single-valued (`eval_unique` in `lean/CodeCalculus/Eval.lean`,
one line from `denote_eval`). The denotation adds no rule and
computes no distance (D2), and `steps` is read by no `Eval` premise, so
erasing it loses nothing (D1). A command with no derivation denotes `none`,
and no partial result is ever exposed (`W10`) — the `Option` carrier is the
archived decision's.

The mechanization carries the same reading: `denoteExpr`, `denote` and the
equivalence theorems `denoteExpr_eval`, `denote_eval`
(`denote m S = some S' ↔ Eval m S S'`) in
[`lean/CodeCalculus/Eval.lean`](../lean/CodeCalculus/Eval.lean).
`OBL-SEQUENCE-ASSOCIATIVITY` is unchanged by this subsection — no obligation
status changes here.

## 2. Kernel rules and in-scope construction transition

Each rule carries: a typed signature; applicability preconditions; an explicit
update of the check structure; an explicit update of presentation data; output
well-formedness; and sound property judgments where available
([`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md)).

### `C-SKIP`

No preconditions. State unchanged; one `skip` record appended to `steps`.

### `C-DIRECT-SUM`

$$
\operatorname{EvalExpr}(S_1\oplus S_2,\,S)
$$

premises: $Q_1\cap Q_2=\varnothing$ and
$\mathsf{used}_1\cap\mathsf{used}_2=\varnothing$. Result: $Q=Q_1\cup Q_2$, rows
concatenated, identifier sets unioned. Both collisions make the constructor
**inapplicable**.

### `C-DELETE-CHECK`

$$
\frac{\operatorname{DisplayedGenerator}(r,\mathsf{pres})\qquad
 \operatorname{Independent}(r;\mathsf{pres})}
 {\operatorname{Eval}(\operatorname{delete}_r,\,C,\,C')}
$$

$C'$ removes exactly the selected generator. The qubit namespace is unchanged; the
identifier is **retired but stays in `used`**.

### `C-ADD-CHECK`

$$
\frac{r\in Z^\perp\qquad r\notin X}
 {\operatorname{Eval}(\operatorname{addStab}_{r:X},\,C,\,C')}
\qquad
\frac{r\in X^\perp\qquad r\notin Z}
 {\operatorname{Eval}(\operatorname{addStab}_{r:Z},\,C,\,C')}
$$

The premises are the standard CSS commutation and same-sector independence
conditions, **with both complements taken inside $\mathbb{F}_2^Q$**
([`STATE_MODEL.md`](STATE_MODEL.md) §1): $r\in Z^\perp$ presupposes
$r\in\mathbb{F}_2^Q$, i.e. $\operatorname{supp}(r)\subseteq Q$. A candidate row
whose support leaves $Q$ fails the premise and the outcome is **no derivation**,
not malformation — the term is well-typed, and the same row applies against a
state whose namespace contains its support (probe `W22`). Reading $Z^\perp$ as a
bare dot product accepts such a row and produces a display that satisfies I1–I5
while not being a code on $Q$. The identifier is minted **canonically** — there
is no fresh-name choice.

**Gauging-as-merge boundary (face-set model only).** A gauging step equals a
one-face union merge iff the added row is the face boundary of a defect face
(edge-present, unchecked) — the merge is defect filling. On a defect-free patch
no gauging step is a merge. Multi-defect combined gauging ($k-1$) differs from
multi-face filling ($k-|D'|$). This is an identification under the face-set
model; the remainder (graft as a one-qubit split; check deletion as a mapping
cone or sui generis) is open. Source: external input (see REFERENCES.md).

### `C-SEQUENCE`

The rule in §1.

**Order dependence (face-set model only).** Sequencing is not commutative in
general. Punch and fuse commute iff the punched faces are disjoint from the
fusion partner's face set; when they are not disjoint, order moves the
distance (punch-then-fuse $d_Z=5$ versus fuse-then-punch $d_Z=4$ on the
frame+plug family). Sequence certificates must record row order. This is a
conditional statement about the face-set model, not a claim about general
schedules. Source: external input (see REFERENCES.md).

### `E-GRAFT`

**Introduced in:** `stdCSS-2`.

For a qubit $q\in Q$, selected sector $\tau\in\{X,Z\}$, and ordered list
$\vec r=(r_1,\ldots,r_m)$ of displayed $\tau$-rows, the list must name exactly
all selected-sector rows whose supports contain $q$. The move is inapplicable
when the list is empty, incomplete, duplicated, or names a non-live row.

The transition removes $q$ from $Q$ and retires the listed row identifiers.
It inserts canonically named $\tau$-rows for the adjacent products
$r_i+r_{i+1}$, restricted to $Q\setminus\{q\}$, for $1\le i<m$; selected-sector
rows not touching $q$ are retained. Every opposite-sector row is retained with
$q$ removed from its support. The ordered chain is part of the command, so the
transition is deterministic for a fixed state and command.

Ambient containment (W22 reading). Every row the transition introduces or
transforms has support in the new namespace $Q'=Q\setminus\{q\}$: surviving
selected-sector rows are $q$-free by construction (they were not in the
touching chain), every opposite-sector row is shortened at $q$, and each minted
adjacent-product row $r_i\oplus r_{i+1}$ has $q$-coordinate $0$ because $q$
belongs to both endpoints, so its support lies in $Q'$. No row leaves the
ambient space $\mathbb{F}_2^{Q'}$; a constructed row that did would be
malformed at the encoding, not a no-derivation.

Applicability additionally requires that the result is CSS-orthogonal, that
both displayed sectors remain independent, that $k'=k$, and that every
remaining qubit is touched by at least one check of each sector. The grafted
qubit must also belong to at least one opposite-sector row. This guard
restricts the admitted domain to the source's modeling regime and carries no
distance rationale: the relation it was introduced to protect, the source's
spliced-sector-unchanged relation $d'_\tau=d_\tau$, is refuted with the guard
in place (§4.20), and no derivation of this document reads the guard (§4.13's
sector arguments use only a nonempty chain, and the Lean well-formedness
proof `wf_graftState` takes neither guard as a hypothesis; ,
`OBL-GRAFT-TRANSITION-SOUNDNESS` row). The
coverage condition and this opposite-sector condition are empirical modeling
guards from the admitted graft relation, not general theorems about all CSS
families. A failed condition gives no derivation. Conditional distance prices
are not read by this state transition; they enter only in the judgment layer.
Output well-formedness and the conditional distance rule remain subject to
`OBL-GRAFT-TRANSITION-SOUNDNESS` and `OBL-JUDGMENT-SOUNDNESS`.

## 3. The two derivations the rules rest on

These are the ranking arguments the deletion and addition laws depend on. Both are
**proved by hand** and recorded with their dated qualifications; both are to be
re-derived mechanically.

**Deletion.** The deleted row is displayed and independent (I2), so removing it
drops the rank of its sector's row space by exactly one and leaves the other
sector unchanged; $Q$ is unchanged. With $k=n-\dim X-\dim Z$: $n'=n$ and
$k'=k+1$. Output well-formedness: removing rows cannot violate $X\perp Z$.

**Addition.** The premise $r\notin X$ (resp. $r\notin Z$) makes $r$ independent of
the target sector's row space, whose rank therefore rises by exactly one: $n'=n$
and $k'=k-1$.

**Both steps are valid because the display spans** — under I1 as definitional). Deleting an independent row from a *spanning* set drops the
span's dimension by one; from a non-spanning independent set it need not, and
§2's addition premise is a row-space condition while display independence is a
span-of-displayed-rows condition. The two coincide **by construction**, not by
hypothesis. The review qualification that raised this is kept at
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4 and its disposition in
an archived internal note.

**Distance non-increase under deletion** ($d_X'\le d_X$, $d_Z'\le d_Z$, and
$d'\le d$ by `MIN-ORDER` + `TRANSITIVITY`) and **the skip identity** are recorded
at [`OBLIGATIONS.md`](OBLIGATIONS.md)'s §5.5 and §5.6. The skip
identity is the one obligation discharged to date — `proved`, and **not yet
`promoted`**, since promotion is a human-owned review disposition.


## 4. The dated hand derivations

Folded here 2026-10-11 from an archived internal note §5.
These are **evidence in this repository, not machine-checked proofs**, and each is to be
re-derived mechanically. Their qualifications are retained verbatim, per `AGENTS.md`:
*review findings are dispositions, not silent edits.*

Dated hand derivations behind the
`established` claim-status tags of the proposal. Each is to be re-derived
– — these are not machine-checked. All parameters are the
the research proposal (see REFERENCES.md) definitions.

**§4.1 — Deletion (`C-DELETE-CHECK`).** The deleted row is displayed and
independent (I2), so removing it drops the rank of its sector's row space by
exactly one and leaves the other sector unchanged; $Q$ is unchanged. With
$k=n-\dim X-\dim Z$: $n'=n$ and $k'=k+1$. Output well-formedness: removing
rows cannot violate $X\perp Z$.

**Qualification (review finding, 2026-10-10 — DISPOSITIONED the same day: reading (A), I1's span clause is
*definitional*).** The pass raised that the step "drops the rank of its sector's
row space by exactly one" is valid **only if the displayed rows span that
sector's row space** — deleting an independent row from a *spanning* set drops
the span's dimension by one; deleting one from a non-spanning independent set
need not — and that §4.2's $r\notin X$ is a *row-space* condition while display
independence is a *span-of-displayed-rows* condition, the two coinciding only
under spanning. **Both derivations above now stand as written**: under reading
(A), $X=\langle rows\_X\rangle$ holds by construction for every well-formed
state, so the coincidence is not a hypothesis but a fact, and $k'=k+1$ and
$k'=k-1$ follow from I1 together with I2 rather than from I2 alone. The
"conditional" branch — under which these two `established` claims would have
needed restating — **was not taken**. The qualification is superseded by this
dated disposition and kept rather than deleted, per `AGENTS.md`. See
an archived internal note
for the disposition record and for what survives it (repair work in
other artifacts, not here).

**§4.2 — Addition (`C-ADD-CHECK`).** The premise $r\notin X$ (resp.
$r\notin Z$) makes $r$ independent of the target sector's row space, whose
rank therefore rises by exactly one: $n'=n$, $k'=k-1$. *(Qualification 
above covers this step too; the premise is row-space-based and display
independence is span-based — they coincide only under spanning. Note also:
no `C-ADD-CHECK` premise mentions spanning of the existing display, so the gap
under (B) is incompleteness, not unsoundness.)*

**§4.3 — Distance monotonicity under addition.** $X$-type case ($Z$-type
symmetric). $X\subseteq X'$ and $Z'=Z$, so $Z'^\perp\setminus X'\subseteq
Z^\perp\setminus X$ (a subtracted superset shrinks the remainder), and
dually $X'^\perp\subseteq X^\perp$ gives $X'^\perp\setminus Z\subseteq
X^\perp\setminus Z$. Taking minima over subsets (with $+\infty$ for the empty
set) yields $d_X(C')\ge d_X(C)$ and $d_Z(C')\ge d_Z(C)$. The argument uses
CSS stabilizer inclusions only; for gauge constraints the inclusions fail,
which is the proposal's scoping caveat.

**§4.4 — Direct-sum parameters and distances.** Block-disjoint unions give
$n=n_A+n_B$, $\dim X=\dim X_A+\dim X_B$, $\dim Z=\dim Z_A+\dim Z_B$, hence
$k=k_A+k_B$. For distances, orthogonality splits per block:
$Z^\perp=Z_A^\perp\oplus Z_B^\perp$. Then:

- ($\le$) every $u\in Z_A^\perp\setminus X_A$ embeds as
 $(u,0)\in Z^\perp\setminus X$, so $d_X(A\oplus B)\le d_X(A)$; symmetrically
 for $B$; hence $d_X(A\oplus B)\le\min(d_X(A),d_X(B))$.
- ($\ge$) every $(u_A,u_B)\in Z^\perp\setminus X$ has some block outside its
 summand's row space (else it lies in $X$), say $u_A\notin X_A$. Then
 $\mathrm{wt}(u_A,u_B)\ge\mathrm{wt}(u_A)\ge
 d_X(A)\ge\min(d_X(A),d_X(B))$.

So $d_X(A\oplus B)=\min(d_X(A),d_X(B))$, and symmetrically for $d_Z$ with
$X^\perp=X_A^\perp\oplus X_B^\perp$; empty sectors obey the $+\infty$
convention on both sides.

**§4.5 — Deletion distance non-increase.**
Deleting a displayed row drops one generator from its sector's row space and
leaves the other sector and $Q$ unchanged, so $X'\subseteq X$ and $Z'=Z$ (a
deleted $X$ row; the $Z$ case is symmetric). For $d_X$ the forbidden set is
$Z^\perp\setminus X$, and since $X'\subseteq X$,
$Z^\perp\setminus X\subseteq Z^\perp\setminus X'$: removing fewer forbidden
vectors only enlarges the remainder. For $d_Z$, orthogonal complement reverses
inclusion, $X^\perp\subseteq X'^\perp$, so
$X'^\perp\setminus Z\supseteq X^\perp\setminus Z$. In both sectors the
relevant set only grows, and with the $+\infty$ convention for the empty set a
minimum over a superset never exceeds a minimum over a subset. Hence
$d_X(C')\leq d_X(C)$ and $d_Z(C')\leq d_Z(C)$; if either original set was
empty the bound reads $+\infty\leq+\infty$ or a finite value $\leq+\infty$,
both true. The argument uses only CSS stabilizer inclusions (same scoping caveat
as §4.3) and the definition of distance. This is the hand derivation behind the
`upper-bound` row of [`CLAIMS.md`](CLAIMS.md) *MVP
property inventory*; like the others it is evidence, not a machine-checked
proof, and is re-derived .

**§4.5 full-distance consequence.**
[`CLAIMS.md`](CLAIMS.md) §6 defines
$d(C)=\min(d_X(C),d_Z(C))$. The minimum is monotone non-decreasing in each
argument, so the two sector bounds already derived above jointly give
$$ d(C')=\min(d_X(C'),d_Z(C'))\ \leq\ \min(d_X(C),d_Z(C))\ =\ d(C). $$
The $+\infty$ convention preserves this: $+\infty$ is the top element of the
extended reals, so monotonicity is unaffected. This is a **consequence** of the
two sector bounds, not an independent argument, and it is re-derived
together with them.

**§4.6 — Skip identity.** The
first obligation discharged end to end; the five above back per-operation
properties, this one is a metatheorem about the rule system's own machinery.

**Lemma (framing).** If two states agree on every field except `steps`, then
`Eval` has the same derivability on them. This is not a new assumption: it is
the recorded design decision at
[`STATE_MODEL.md`](STATE_MODEL.md) §2 — *"no `Eval`
premise, conclusion, or property judgment reads `steps`; derivability is
unchanged if `steps` is dropped"* — under the resolution that made `used`,
not `steps`, the semantic field. Write $S_1 \equiv_{\mathrm{sem}} S$ for
agreement on all semantic fields ($Q$, $X$, $Z$, labeled rows, `used`).

**Premises used.** The `C-SKIP` card: the only derivable form of
`Eval(skip,·,·)` is $Eval(\operatorname{skip},S,S)$; state update $S'=S$ on every
semantic field; applicability *none*, so always applicable. The `C-SEQUENCE`
card: $\dfrac{Eval(m_1,S_0,S_1)\quad Eval(m_2,S_1,S_2)}{Eval(m_1;m_2,S_0,S_2)}$.

**Forward ($m \Rightarrow \operatorname{skip};m$).** Assume
$Eval(m,S,S')$. The bare `C-SKIP` rule gives $Eval(\operatorname{skip},S,S)$ with
no premises. Applying `C-SEQUENCE` to that and the assumption yields
$Eval(\operatorname{skip};m,S,S')$, i.e. the left conjunct holds with
$S''=S'$.

**Reverse ($\operatorname{skip};m \Rightarrow m$).** Assume
$Eval(\operatorname{skip};m,S,S'')$. By `C-SEQUENCE` there is an intermediate
$S_1$ with $Eval(\operatorname{skip},S,S_1)$ and $Eval(m,S_1,S'')$. The `C-SKIP`
card forces $S_1\equiv_{\mathrm{sem}}S$ — the rule's conclusion is $S$ itself,
and only the semantically inert step record differs. By the framing lemma,
$Eval(m,S_1,S'')$ is equivalent to $Eval(m,S,S'')$. Hence the right conjunct
holds.

**Sequencing on the right is the same argument.** $Eval(m;\operatorname{skip},S,S''')$
holds iff there is $S_1$ with $Eval(m,S,S_1)$ and $Eval(\operatorname{skip},S_1,S''')$,
and the `C-SKIP` card forces $S'''\equiv_{\mathrm{sem}}S_1$; conversely
$Eval(m,S,S')$ together with the bare skip rule on $S'$ gives
$Eval(m;\operatorname{skip},S,S')$ directly, with no lemma needed. $\square$

**Stronger than the obligation states.** The obligation asserts $S''$ and $S'''$
"agree with $S'$ up to $\equiv$". The derivation delivers more: they agree on
**every field $\equiv$ reads**, and differ only in a field no judgment reads, so
$\equiv$ holds a fortiori. No congruence of `Eval` under $\equiv$ is used or
needed — worth recording, since dispositioned the relabeling congruence
narrowly and this obligation was its most likely consumer.

**Standing of this derivation.** Hand-written 2026-10-11, evidence and not a
machine-checked proof; it is re-derived mechanically in the slice, per the
obligation's *Intended mechanization status*. It discharges the obligation's
`open` evidence status to `proved` and nothing else: `promoted` is a review
disposition and remains human-owned (`AUTHORITY.md` §B1–§B2), so no promotion
occurs here.

## 4.7 — Well-formedness preservation (`OBL-WELL-FORMEDNESS-PRESERVATION`)

Hand derivations, for the five MVP instances. Each assumes the input
state satisfies I1–I5 and the primitive's applicability premises
(`spec/STATE_MODEL.md` §3, §4). Output well-formedness is then checked
invariant by invariant. These are evidence, not machine-checked proofs, and are
re-derived –; the `C-SKIP`, `C-DELETE-CHECK`,
`C-ADD-CHECK`, and `C-SEQUENCE` instances are mechanized in
`lean/CodeCalculus/WellFormedness.lean` (`wf_of_eval`), the
`C-DIRECT-SUM` instance as `directSum_wellFormed`, and the
`E-GRAFT` instance of §4.12 in `lean/CodeCalculus/GraftWellFormedness.lean`
(`wf_graft_of_eval`); `wf_of_eval_all` there lifts preservation to
every command.

**`C-SKIP`.** The rule's state update is $S'=S$ on every semantic field, so
I1–I5 hold of $S'$ by identity. One line.

**`C-DELETE-CHECK`.** Let the deleted row be $r$ in sector $\tau$; the premise
`Independent(r; pres)` gives $r\notin\langle\mathit{rows}_\tau\setminus\{r\}\rangle$.

- I1: if $\tau=X$, then $X'=\langle\mathit{rows}_X\setminus\{r\}\rangle\subseteq X$ and
 $Z'=Z$. Since $X\perp Z$ and a subspace of an orthogonal complement is still
 orthogonal, $X'\perp Z$. The $\tau=Z$ case is symmetric.
- I2: deleting a row from an independent set leaves an independent set; the
 remaining rows of $\tau$ were independent in $S$ by I2 and stay so, and the
 other sector is untouched.
- I3: no identifier is minted or retired; `used` is unchanged; live identifiers
 remain injective and subset of `used`.
- I4, I5: sector labels and provenance are unchanged.

**`C-ADD-CHECK`.** Let the added row be $r$ in sector $\tau$, with support in
$Q$, commuting with the opposite sector (applicability), and independent of
$\tau$'s row space (applicability).

- I1: if $\tau=X$, then $X'=X+\langle r\rangle$ and $Z'=Z$. The commutation
 premise gives $r\perp Z$, and $X\perp Z$ by input I1, so every vector in
 $X'$ is orthogonal to every vector in $Z'$; hence $X'\perp Z'$. The
 $\tau=Z$ case is symmetric.
- I2: the existing $\tau$-rows are independent by input I2; $r$ is not in their
 span by the independence premise; therefore the enlarged set is independent.
 The opposite sector is untouched.
- I3: the new identifier is minted canonically as the first element of the fixed
 enumeration not in `used`, so injectivity and the no-reuse rule hold; `used`
 is updated to include it.
- I4, I5: sector label is fixed by the command; provenance is append-only.

**`C-DIRECT-SUM`.** Inputs $S_A,S_B$ well-formed, with disjoint qubit
namespaces and disjoint `used` sets.

- I1: row spaces are block-disjoint, so $X'=X_A\oplus X_B$ and
 $Z'=Z_A\oplus Z_B$ (as subspaces of $\mathbb F_2^{Q_A\sqcup Q_B}$). Cross-block
 dot products vanish because supports are disjoint, and within each block
 $X_A\perp Z_A$, $X_B\perp Z_B$ by input I1; hence $X'\perp Z'$.
- I2: a linear combination of all rows that is zero splits into a combination
 in block $A$ and one in block $B$, both zero; independence in each block
 (input I2) forces all coefficients zero.
- I3: live identifiers are the union of the two disjoint live sets, hence
 injective; `used` is the union of the disjoint `used` sets, so no reuse and
 canonical minting is preserved.
- I4, I5: sector labels and provenance are inherited blockwise.

**`C-SEQUENCE`.** If $\operatorname{Eval}(m_1,S_0,S_1)$ and
$\operatorname{Eval}(m_2,S_1,S_2)$ with $S_0$ well-formed, then $S_1$ is
well-formed by the instance for $m_1$, and $S_2$ is well-formed by the instance
for $m_2$. By induction on the sequence length, every intermediate state and the
final state satisfy I1–I5.

$\square$

## 4.8 — Primitive determinism, sequencing associativity, and direct-sum laws

Hand derivations. Evidence, not machine-checked; re-derived
–.

**`OBL-PRIMITIVE-DETERMINISM`.** Each MVP primitive's state update is a
function of the complete semantic input state and its explicit term data:

- `C-SKIP`: $S'=S$.
- `C-DELETE-CHECK`: the identifier names the row; the output is the input with
 that row removed and `used` unchanged. The canonical mint is not invoked.
- `C-ADD-CHECK`: the new row's support, sector and identifier are determined
 by the term and the canonical mint (first enumeration element not in
 `used`), which is a function of `used`; `used' = used ∪ {id}`.
- `C-DIRECT-SUM`: $Q'=Q_A\sqcup Q_B$, rows' = rows$_A$ + rows$_B$, used' =
 used$_A$ ∪ used$_B$; the disjointness premises are part of applicability.
- `C-SEQUENCE`: $S'=S_2$ where $S_1$ is the unique output of the first command
 and $S_2$ the unique output of the second (induction).

`steps` is semantically inert and is read by no rule, so it cannot affect the
output. Hence on its applicability domain each primitive is functional: two
derivations with the same input and term yield $\equiv$-equal outputs. $\square$

**`OBL-SEQUENCE-ASSOCIATIVITY`.** $\operatorname{Eval}(m_1;m_2,S,S')$ holds iff
there is an intermediate $S_1$ with $\operatorname{Eval}(m_1,S,S_1)$ and
$\operatorname{Eval}(m_2,S_1,S')$. For $(m_1;m_2);m_3$ this requires
$S_{12}$ with $\operatorname{Eval}(m_1;m_2,S,S_{12})$ and
$\operatorname{Eval}(m_3,S_{12},S')$, i.e. $S_1$ with
$\operatorname{Eval}(m_1,S,S_1)$ and $S_2$ with
$\operatorname{Eval}(m_2,S_1,S_2)$ and $\operatorname{Eval}(m_3,S_2,S')$ —
exactly the chain for $m_1;(m_2;m_3)$. When a middle command is inapplicable,
no intermediate exists in either bracketing, so both are undefined together
(`W10`). $\square$

**`OBL-DIRECT-SUM-LAWS`.** Direct sum is $Q'=Q_A\sqcup Q_B$, rows' =
rows$_A$ + rows$_B$, used' = used$_A$ ∪ used$_B$, with disjointness
premises. Set union is associative and commutative, and the summands' rows,
identifiers and supports are retained unchanged; no relabeling occurs. Hence
$(C_A\oplus C_B)\oplus C_C \equiv C_A\oplus (C_B\oplus C_C)$ and
$C_A\oplus C_B \equiv C_B\oplus C_A$ as literal equality. $\square$

**Re-evidenced 2026-10-29.** $\equiv$ reads $Q$ since that date
([`STATE_MODEL.md`](STATE_MODEL.md) §2). The three conclusions of this section
agree on $Q$: a function's two outputs are equal on every field, and the sum's
namespace is the set union $Q_A\sqcup Q_B$, associative and commutative. They
stand as written.


## 4.9 — Partial-inverse laws and frame law for direct-sum blocks

Hand derivations. Evidence, not machine-checked; re-derived
–.

**`OBL-PARTIAL-INVERSE-LAWS`.**

- *Add-then-delete.* `add_check` appends a row $r$ with support $s$ that is
 independent of its sector's row space and commutes with the opposite sector;
 `delete_check` on $r$'s (canonically minted) identifier removes exactly that
 row. The displayed rows and row space are restored to the start; `used`
 strictly grows (the minted identifier is retired but retained), so the
 endpoint is not $\equiv$ to the start — only displayed-row and row-space
 identity holds.
- *Delete-then-add.* Deleting $r$ removes it from the display; re-adding
 support $s$ restores the row space and displayed supports, but the mint yields
 a fresh identifier (the retired one is never reused), so the endpoint is
 not $\equiv$ to the start by the identifier-visibility ruling. Multiplicity
 is recorded by the retained identifier history.

$\square$

**`OBL-FRAME-LAW`.**

- *Deletion clause (unconditional).* If $r$ is displayed in exactly one summand
 of $A\oplus B$, its independence and displayedness are per-block properties,
 and `delete_r` on the sum is applicable iff applicable on that summand; the
 result is that summand's deletion result plus the untouched other summand.
 `used` bookkeeping is per-block (the retired identifier stays in the owning
 summand's `used`). Hence the frame law holds.
- *Addition clause (conditional).* If $\operatorname{supp}(r)\subseteq Q_A$,
 then $r$ annihilates $Z_B$ and cannot meet $X_B$, so applicability splits
 per block and holds on the sum iff it holds on $A$. The result is $A'\oplus B$
 provided the allocation-compatibility premise holds:
 $\operatorname{mint}(\mathsf{used}_A\cup\mathsf{used}_B)=
 \operatorname{mint}(\mathsf{used}_A)$, i.e.
 $\operatorname{mint}(\mathsf{used}_A)\notin\mathsf{used}_B$. Every
 identifier before $\operatorname{mint}(\mathsf{used}_A)$ in the fixed
 enumeration lies in $\mathsf{used}_A$, so under the `C-DIRECT-SUM`
 disjointness of the two `used` sets the premise says that
 $\mathsf{used}_B$ starts strictly after $\operatorname{mint}(\mathsf{used}_A)$.
 Without that premise the summands are still applicable but mint
 differently, and the clause fails, which is why it is a hypothesis.

$\square$


## 4.10 — Cross-sector conditional permutation (`OBL-CROSS-SECTOR-PERMUTATION`)

 Evidence, not machine-checked; re-derived
–.

Let $m_X$ be a command of $X$-sector type and $m_Z$ a command of $Z$-sector
type, both over the same well-formed single state $S = (Q, X, Z, \mathsf{pres},
\mathsf{used})$. Applicability of each command on $S$ is a decidable property
of $S$ and the command's explicit data (card premises,
`spec/OPERATIONAL_SEMANTICS.md` §2), so for each order either it applies or it
does not. This gives four exhaustive, mutually exclusive situations. The
analysis below is by command pair; there are no summands and no per-sector
$\mathsf{used}_X, \mathsf{used}_Z$ sets — $m_X$ and $m_Z$ act sequentially
on one state.

- **`Delete` / `Delete` ($\operatorname{delete}_{r_X}, \operatorname{delete}_{r_Z}$).**
 Deletions do not mint identifiers and do not change $\mathsf{used}$, and
 opposite-sector deletions do not affect each other's `DisplayedGenerator` or
 `Independent` premises. Both orders apply iff both deletions apply on $S$; when
 both apply the outputs are always $\equiv$-equal (**Case 1**), and otherwise
 **Case 4**.

- **`Delete` / `Add` ($\operatorname{delete}_{r_X}, \operatorname{addStab}_{s:Z}$
 or the symmetric pair).** Because deletion leaves $\mathsf{used}$ unchanged,
 $\operatorname{addStab}$ mints $\operatorname{mint}(\mathsf{used})$ in
 both orders whenever both orders apply, yielding $\equiv$-equal outputs
 (**Case 1**). **Case 3** (exactly one order applies) arises iff $r_X$ is
 displayed and independent in $S$, $s \in \mathbb{F}_2^Q \setminus Z$
 commutes with $\mathit{rows}_X \setminus \{r_X\}$, and
 $s \cdot r_X = 1$: then $\operatorname{delete}_{r_X};\operatorname{addStab}_{s:Z}$
 applies while $\operatorname{addStab}_{s:Z};\operatorname{delete}_{r_X}$
 fails (fixture `W8`). The reverse single-order case
 ($\operatorname{addStab};\operatorname{delete}$ applies while
 $\operatorname{delete};\operatorname{addStab}$ fails) is impossible because
 deleting $r_X$ only shrinks $X$ (weakening $s \in X^\perp$) and leaves $Z$
 untouched.

- **`Add` / `Add` ($\operatorname{addStab}_{r:X}, \operatorname{addStab}_{s:Z}$).**
 Both orders apply iff each applies on $S$ and $r \cdot s = 0$. When both
 apply, the first command always mints $i_1 = \operatorname{mint}(\mathsf{used})$
 and the second always mints
 $i_2 = \operatorname{mint}(\mathsf{used} \cup \{i_1\}) \neq i_1$,
 swapping the identifier-to-sector assignment between
 $m_X;m_Z$ and $m_Z;m_X$ (the witness). Thus when both orders apply for
 `Add`/`Add`, they always fall into **Case 2** (never Case 1). And if
 $r \cdot s = 1$ while both apply individually on $S$, **both** sequential
 orders fail at the second step (**Case 4**, never Case 3).

Every pair $(m_X,m_Z,S)$ falls into exactly one of (1)–(4) because
applicability is binary for each order and the mint equality is binary when
both apply. The side conditions $\Pi(m_X,m_Z,S)$ selecting Case 1 over Case 2
among applicable pairs are simply that **not both** $m_X$ and $m_Z$ are
`C-ADD-CHECK` (equivalently, at least one of the two commands is a
`C-DELETE-CHECK`). The allocation-compatibility premises of the frame law
(`OBL-FRAME-LAW`, addition clause) are the underlying mint-equality
conditions. $\square$

## 4.11 — Judgment soundness and judgment transport

Hand derivations. Evidence, not machine-checked; re-derived
–. First mechanization slice landed 2026-10-25,  (`lean/CodeCalculus/Soundness.lean`, `lake build` green with no `sorry`):
the models predicate `Models` over the chain a closed command unfolds through,
the L3 rule inventory below as the inductive `Derives`, and
`judgment_soundness` by induction on a derivation, for a well-formed
evaluation chain (`Chain cs` and `WellFormedContext cs`). `Models` returns the
chain hypothesis unchanged, so the slice proves the `⊨` half under an assumed
evaluation: the `Eval` conjunct is assumed rather than proved, and the chain
hypothesis cannot be dropped (`le_refl` and the pure order rows are derivable
over any list of states). The slice proves the instantiation base for skip's
identity (every field) and the `n` cells of deletion, addition, and the graft,
and the `k` cells and the distance monotonicity/bounds
cells of deletion and addition, the latter two taken as premises at the row
rather than discharged by per-primitive lemmas; and
the output well-formedness cells of skip, deletion, addition, and the graft,
the first three discharged by the §4.7 lemmas of
`lean/CodeCalculus/WellFormedness.lean` and the graft's by `wf_graft_of_eval` of
`lean/CodeCalculus/GraftWellFormedness.lean`, with the `k` cells of deletion
and addition discharged by the rank-decrease lemmas under the dimension bound
`rank X + rank Z ≤ |Q|`, which `ranksFit_of_wf`
(`lean/CodeCalculus/RanksFit.lean`, , 2026-10-28) derives from
well-formedness. The measure's monotonicity is taken once, as the hypothesis
`MeasureMonotone dMeasure` of `judgment_soundness`,
with the deletion and addition span inclusions proved and the span form
`SpanMonotone` bridged to it, and discharged for the exact sector distance by
`lean/CodeCalculus/ExactDistance.lean`;
`OBL-JUDGMENT-TRANSPORT` is mechanized in `lean/CodeCalculus/Transport.lean`. In the transcription `d` is defined as

$\min(d_X,d_Z)$, matching the unfolding this section's `TRANSITIVITY` argument
uses.

**`OBL-JUDGMENT-SOUNDNESS`.** The judgment system $\vdash$ is the L3 rule
inventory recorded in 
§3.4 and §3.4.1: instantiation (the only source of a distance fact),
`TRANSITIVITY`, `MIN-ORDER` (three order rules), and the ambient order theory on
$\mathbb{N}\cup\{+\infty\}$. Soundness is proved by induction on a
derivation in this system.

Define satisfaction $(S,m,S')\models R$ by claim shape: for each carry-table cell
property $P$ ($n$, $k$, $d_X$, $d_Z$, $d$, output well-formedness),
$(S,m,S')\models P$ iff $P$ holds of the denoted evaluation; for `unavailable`
cells no derivable claim exists, so soundness is vacuous.

- *Instantiation (base).* The rule looks up the card of $m$ and checks each cell
 it records as `included` at the input/output pair $(S,S')$. Each such cell is
 true of the denoted evaluation by the per-primitive derivations already
 recorded: dimension counts (bold labels §4.1–§4.2, §4.4 folded in §4),
 distance monotonicity and bounds (§4.3, §4.5), well-formedness preservation
 (§4.7), and the skip identity (§4.6). `unavailable` cells contribute no
 derivable claim.
- *`TRANSITIVITY`.* If $t_1 \lesssim t_2$ and $t_2 \lesssim t_3$ are
 derivable in the same closed term, then $t_1 \lesssim t_3$ is derivable.
 Sound because $\le$ and $=$ are transitive on
 $\mathbb{N}\cup\{+\infty\}$, and because $d(C)$ unfolds syntactically to
 $\min(d_X(C),d_Z(C))$, so a $\min$ of transitive chains composes.
- *`MIN-ORDER` (three rules).* Sound because the order on
 $\mathbb{N}\cup\{+\infty\}$ is a total order with $\min$; each rule is an
 instance of order-theoretic monotonicity of $\min$.
- *Ambient order theory.* Sound by the standard order theory on
 $\mathbb{N}\cup\{+\infty\}$.
- *Context.* $\Gamma$ contains only well-formedness assumptions , which
 hold of $S$ by hypothesis, so no unsound assumption is introduced.

Hence every derivable annotation is true of the denoted evaluation. $\square$

**`OBL-JUDGMENT-TRANSPORT`.** Structural judgments compose through valid
sequences when their schemas compose. Schema-composition condition: a claim's
schema mentions only fields that are invariant (or compose by substitution or
equality) across the sequence; for a claim referencing a generator $r$, $r$ must
survive (not be deleted) along the sequence.

- *`W13` half (deleted generator).* If $r$ is deleted, the claim's schema fails
 the composition condition (the deleted identifier is not in the output's live
 set and not in its row space), so **no derivation closes** for the transported
 claim. This is the refutation witness of Reading III: non-transport is a
 consequence of the composition schema failing to fire, not a rule concluding a
 negative. See `spec/JUDGMENT_LAYER.md` §4 (the `W13` half) and the
 2026-10-20 diary entry on decidability of the search for the MVP instance.
- *Positive half (surviving generator).* If $r$ survives, its schema persists and
 the claim transports. For the carry-table properties: across `C-SEQUENCE`,
 equalities compose by substitution; one-sided bounds of the same polarity
 compose by transitivity of $\le$ on $\mathbb{N}\cup\{+\infty\}$;
 opposite-polarity bounds on mixed delete/add chains do not compose into a
 two-sided bound. This discharges the positive half's schema-composition
 condition and argument. $\square$

Mechanization, 2026-10-27:
the positive half as `Derives.weaken` and `Derives.shift` (a derivation over
either segment of a sequence is a derivation over the composed chain, the
second segment's positions shifted past the first) with the seam compositions
`transport_eq_eq`, `transport_le_le_down`, `transport_le_le_up`,
`transport_le_eq`, and `transport_eq_le`, closed by `judgment_soundness` on
the composed chain (`transport_models`); the fixed-reference-set model of
§4.15 over an arbitrary certificate type; and the `W13` shape as
`not_derivable_of_false`, with the non-composition clause above witnessed on
a delete-then-add chain (`not_derivable_mixed_le`, `not_derivable_mixed_ge`,
and, for every measure, `not_derivable_mixed_eq`). The slice's sentence
language has no claim that refers to a generator, so the `W13` half's
derivation-level instance is not in it; the record, with what is not
mechanized, is at `spec/OBLIGATIONS.md`, `OBL-JUDGMENT-TRANSPORT`, *Intended
mechanization status*.

## 4.12 — Graft transition soundness (`OBL-GRAFT-TRANSITION-SOUNDNESS`)

 Evidence, not machine-checked. The
well-formedness conclusion is mechanized as `wf_graftState`
(`lean/CodeCalculus/GraftWellFormedness.lean`, , 2026-10-28) under
the transition's premises; the Lean proof derives I2 by counting ranks from the
$k'=k$ premise and the dimension bound (`ranksFit_of_wf`), which
forces both output sectors to full rank, rather than by the lifting argument
below, which is unchanged.

Let $S$ be well-formed and $\operatorname{E-GRAFT}(q,\tau,\vec r)$ applicable
per `spec/OPERATIONAL_SEMANTICS.md` §2: $q\in Q$; $\vec r$ names exactly all
$\tau$-rows touching $q$ in chain order; the opposite-sector guard holds
($q$ belongs to at least one $\bar\tau$-row, guard); coverage holds
(every qubit in $Q\setminus\{q\}$ is touched by both sectors); and $m\ge 1$.

Ambient membership (W22). Every surviving, shortened, and minted row has support
in $Q'=Q\setminus\{q\}$ by construction: surviving $\tau$-rows and all
$\bar\tau$-rows are shortened by deleting coordinate $q$, and each minted
adjacent-product row $r_i\oplus r_{i+1}$ has $q$-coordinate $0$ because $q$
belongs to both $r_i$ and $r_{i+1}$, so its support lies in $Q'$.

- **$n'=n-1$.** By construction $Q'=Q\setminus\{q\}$, so $n'=n-1$.
- **I1 (CSS orthogonality).** Every new $\tau$-row is $r_i\oplus r_{i+1}$ with
 $q\in \operatorname{supp}(r_i)\cap\operatorname{supp}(r_{i+1})$, so its
 $q$-coordinate vanishes ($x_q=0$); every untouched $\tau$-row already has
 $x_q=0$. Thus for any shortened $\bar\tau$-row $z'=z|_{Q\setminus\{q\}}$,
 $x'\cdot z' = x\cdot z = 0$ by input I1. No check is needed.
- **I2 (displayed independence).** In sector $\tau$, the $m-1$ adjacent sums
 $r_1\oplus r_2,\dots,r_{m-1}\oplus r_m$ together with the untouched
 $\tau$-rows are independent: a nontrivial zero combination lifts to a
 combination of the input $\tau$-rows, contradicting input I2, and their span
 is $\{x\in C_\tau : x_q=0\}$ of dimension $\dim C_\tau-1$. In sector
 $\bar\tau$, a nontrivial dependency among the shortened rows
 $z|_{Q\setminus\{q\}}$ would yield a nonzero $z\in C_{\bar\tau}$
 supported inside $\{q\}$, i.e. $z=e_q$, which has $z\cdot r_1=1$,
 contradicting input I1 ($C_\tau\perp C_{\bar\tau}$). No check is needed.
- **$k'=k$.** Since $n'=n-1$, $\dim C'_\tau = \dim C_\tau-1$, and
 $\dim C'_{\bar\tau}=\dim C_{\bar\tau}$, we have
 $k'=(n-1)-(\dim C_\tau-1)-\dim C_{\bar\tau}=k$. Coverage is independent
 of $k'=k$; on any well-formed input with $m\ge 1$ touching $\tau$-rows and
 at least one touching $\bar\tau$-row, $k'=k$ holds whether or not coverage
 holds.
- **I3 (identifier discipline).** The touching $\tau$-row identifiers are retired
 but retained in `used` (never reused); the $m-1$ adjacent-product rows are
 minted sequentially against the running `used` set (`next_used`), matching
 `CodeState.graft` in `machine/priced_calculus.py`, and `used'` is updated to
 include them. Injectivity holds because minting avoids `used`.
- **I4 (sector typing).** New adjacent-product rows are labeled $\tau$; retained
 and shortened rows keep their sector labels.
- **I5 (provenance).** Provenance is append-only and inherited; retired
 identifiers remain referenced only as retired.

The guards with content are coverage and opposite-sector presence; neither is
needed for the state model, and neither is a distance statement — distance
transport is outside the scope of this obligation. Determinism holds because the
ordered chain $\vec r$ is part of the command and the mint is canonical.
$\square$

## 4.13 — Priced interval soundness (`OBL-PRICED-INTERVAL-SOUNDNESS`)

 Evidence, not machine-checked in full; the
interval bookkeeping is mechanized in
`lean/CodeCalculus/PricedInterval.lean` (`priced_interval_soundness`, ,
2026-10-26) conditional on the distance laws this section derives and on price
truth as premises; witnesses, strict improvement, and `certify`/`prune` remain
outside this slice. Re-derived –.

*Instance reading (2026-10-27).* Each bullet below verifies soundness for
one transformer $F_m$ of `JUDGMENT_LAYER.md` §8.3; the `C-SEQUENCE` step is
the composition theorem of §8.5, and the base case is the hypothesis on the
inputs. The obligation
`OBL-PRICED-INTERVAL-SOUNDNESS` is therefore re-read as an instance of the
schema of §8.4, not as an ad hoc induction. No bullet, evidence status, or
claim status changes.
Assume every input ledger interval contains the corresponding exact distance
and every supplied price, lower bound, strict-improvement enumeration, and
witness is true. We show by induction on the transition that every emitted
interval contains the resulting exact distance.

- *Base.* The initial ledger is constructed so that each interval contains the
 corresponding exact distance (by hypothesis on the inputs).
- *`C-SKIP`.* Identity on both state and interval; containment preserved.
- *`C-ADD-CHECK`.* The rule resets the upper endpoint to $+\infty$ and carries
 the lower endpoint; exact distance is non-decreasing under addition (bold label §4.3 in §4),
 so the new exact distance is $\ge$ the carried lower bound. Containment holds.
 Under the strict-improvement hypothesis, the lower bound becomes $d+1$ and
 the hypothesis asserts every minimum-weight class is killed, so the new
 exact distance is $\ge d+1$; containment holds.
- *`C-DELETE-CHECK` (unpriced).* The rule resets the lower endpoint to $0$ and
 carries the upper endpoint; exact distance is non-increasing under deletion
 (bold label §4.5 in §4), so the new exact distance is $\le$ the carried upper bound.
 Containment holds.
- *`C-DELETE-CHECK` (priced).* The full-distance price gives
 $d'=\min(d,w_{\rm del},w_{\rm exp})$; the interval becomes
 $[\min(L,w_{\rm del},w_{\rm exp}),\min(U,w_{\rm del},w_{\rm exp})]$,
 which contains $d'$ by construction. Sector endpoints are untouched, and the
 sector rules are sound by the same non-increase argument.
- *`E-GRAFT`.* Under the transition of §2, the spliced sector's child
 logicals are a subset of the parent's:
 $C'_\tau=\{x|_{Q\setminus\{q\}}:x\in C_\tau,\,x_q=0\}$, so
 $d_\tau(C')\ge d_\tau(C)$; and the non-spliced sector is a projection,
 so $d_{\bar\tau}(C')\le d_{\bar\tau}(C)$. The projection inequality uses
 the nonempty chain (the $e_q$ argument below): a parent $\sigma$-logical
 restricts to a child $\sigma$-logical: the restriction is orthogonal to
 each child $\tau$-row and the $e_q$ step keeps it out of the child
 $\sigma$-span. Touching $q$ only lowers the weight by one (the case split
 $d'_\sigma=\min(d_\sigma,w_{\rm expose,\sigma})$).
 From these two facts:
 - **Spliced sector.** $L_\tau\le d_\tau(C)\le d_\tau(C')$, so the
 lower endpoint carries; $d_\tau(C')$ may exceed any prior upper bound, so
 the upper endpoint is reset to $+\infty$ and tightened only by witnesses
 valid in the child.
 - **Non-spliced sector.** $U_{\bar\tau}\ge d_{\bar\tau}(C)\ge
 d_{\bar\tau}(C')$, so the upper endpoint carries; the lower endpoint
 resets to $0$.
 - **Full distance (unpriced).** $d'=\min(d_\tau',d_{\bar\tau}')$ has no
 monotonicity in either direction, so both endpoints reset to $[0,+\infty)$;
 the sector uppers remain sound upper bounds because
 $d'\le d_{\bar\tau}'\le U_{\bar\tau}$ and, when a witness supplies
 one, $d'\le d_\tau'\le U_\tau$.
 - **Full distance (priced).** With a true exposure minimum
 $p=w_{\mathrm{expose},\bar\tau}$, the non-spliced sector satisfies
 $d_{\bar\tau}'=\min(d_{\bar\tau},p)\ge\min(L_{\bar\tau},p)$ (the input
 interval contains the exact distance, so $d_{\bar\tau}\ge L_{\bar\tau}$),
 so the sector's lower endpoint $\min(L_{\bar\tau},p)$ is sound; whence
 $d'=\min(d_\tau',\min(d_{\bar\tau},p))\ge
 \min(d_\tau,\min(d_{\bar\tau},p))=\min(d,p)$, so the lower
 endpoint $\min(L,p)$ is sound; and $d'\le\min(d_{\bar\tau},p)\le p$
 and $d'\le d_{\bar\tau}'\le U_{\bar\tau}$, so the upper endpoint
 $\min(p,U_{\bar\tau},\text{child witnesses})$ is sound. The spliced
 sector is unaffected by the price.
 The priced bullet rests on the following relation for the non-spliced
 sector ($\sigma=\bar\tau$), which is derived here. Let the chain be
 nonempty and let $r$ be any retired $\tau$-row. Restriction to
 $Q\setminus\{q\}$ is a bijection from parent $\sigma$-logicals to child
 $\sigma$-logicals. A parent $\sigma$-logical $z$ restricts to a vector
 orthogonal to every child $\tau$-row, because each child $\tau$-row is the
 restriction of a parent $\tau$-span element vanishing at $q$. Its
 restriction lies in the child $\sigma$-span only if $z+s\in\{0,e_q\}$ for
 some parent $\sigma$-stabilizer $s$; $z\neq s$, and $e_q$ is not
 orthogonal to $r$ while $z+s$ is, so $z|_{Q\setminus\{q\}}$ is a child
 $\sigma$-logical. Conversely a child $\sigma$-logical $y$ lifts uniquely to
 $\tilde y$ with $\tilde y_q=\langle y,r|\rangle$: the child rows
 $(r_i+r_{i+1})|$ force $\langle y,r_i|\rangle$ to be the same for every
 chain row, so $\tilde y$ is orthogonal to every parent $\tau$-row, and
 $\tilde y$ in the parent $\sigma$-span would put $y$ in the child
 $\sigma$-span. The two maps are inverse, since $\langle z,r\rangle=0$
 gives $z_q=\langle z|,r|\rangle$, and
 $|z|_{Q\setminus\{q\}}|=|z|-z_q$. Hence
 $d'_\sigma=\min$ over parent $\sigma$-logicals $z$ of $(|z|-z_q)$, which
 lies in $\{d_\sigma-1,d_\sigma\}$, with $d'_\sigma=d_\sigma-1$ exactly
 when some minimum-weight parent $\sigma$-logical touches $q$. Define the
 exposed set as the child $\sigma$-logicals whose lift touches $q$, so that
 $w_{\mathrm{expose},\sigma}=\min\{|z|-1:z\text{ a parent }\sigma\text{-logical with }z_q=1\}$,
 or $+\infty$ if none. Then
 $d'_\sigma=\min(d_\sigma,w_{\mathrm{expose},\sigma})$, the relation the
 priced bullet needs. ( derivation, 2026-10-21.)

 Containment therefore holds for $d$, $d_X$, and $d_Z$ under the corrected
 rules.
- *`C-DIRECT-SUM`.* Both bounds are exact minima of the summands; containment
 holds by the direct-sum distance law (bold label §4.4 in §4).
- *`C-SEQUENCE`.* By induction on the two sub-transitions; transport composes.

`certify` is justified by its lower endpoint and `prune` by its upper endpoint
by construction of `decide`. A `re-measure` result makes no distance claim.

**Scope boundary — the six Gate 6 cells are outside this slice.** The
transformers named in `OBL-PRICED-INTERVAL-SOUNDNESS` and restated as the
§8.3 transformers are the core consumer transitions `C-SKIP`,
`C-ADD-CHECK`, `C-DELETE-CHECK`, `E-GRAFT`, `C-DIRECT-SUM`, and
`C-SEQUENCE`. The six Gate 6 cells (`P-REBASE`, `E-LOCAL-HADAMARD`,
`E-PEEL`, `E-PUNCTURE`, `E-EXTEND`, `E-GLUE`) are not transformers of that
set: their interval behavior is recorded as conditional cells in
`JUDGMENT_LAYER.md` §2b/§2f and their distance relations are the
refusals/conditional hypotheses of §4.26–§4.31. Their sound admission is
governed by `OBL-GATE6-CSS-EXTENSIONS`, not by this obligation; no bullet
is added here, and none is owed for this obligation to read as proved. The
consumer's reset-to-full-interval rows for `E-PEEL`/`E-PUNCTURE` are sound
by construction (a reset interval contains every distance), and the
conditional rows for the others carry the soundness burden of their named
hypothesis.

The `E-GRAFT` bullet above is the re-attempt under the corrected rules;
the consumer rules in `spec/JUDGMENT_LAYER.md` §2b and `machine/consumer.json`
have been updated to those rules. $\square$

## 4.14 — Priced input semantics (`OBL-PRICED-INPUT-SEMANTICS`)

The typed meanings of priced inputs are recorded in
`spec/JUDGMENT_LAYER.md` §2c, which is the authority for
judgment inputs; this section is retained as a pointer only. The consumer
records sources and checks structural shape; it does not validate supplied
lower bounds, exact prices, or exhaustive minimum-weight-class enumerations.
$\square$

## 4.15 — Order-independent deletion (`OBL-ORDER-INDEPENDENT-DELETION`)

**State-level part.** Let $S$ be a finite set of displayed, independent
generator identifiers in a well-formed state. Deleting a displayed independent
row removes it from the display and from its sector's row space, lowers that
sector's rank by one, and leaves $Q$ and the other sector unchanged
(`C-DELETE-CHECK`, §2 and §4.1). `C-DELETE-CHECK` does not mint identifiers, so
$\mathsf{used}$ is unchanged by every deletion; hence the final semantic state
is $(Q,\mathit{rows}\setminus S,\mathsf{used})$ for every enumeration order,
and the two outputs are $\equiv$-equal (not merely equal on rows, parameters,
and spaces). For two rows $r_1,r_2$ in $S$, deleting $r_1$ then $r_2$ removes
both from the display and lowers the rank by two, regardless of order, because
the second row is independent of the remaining set after the first deletion
(independence of the subset is preserved under deletion of an independent row).
The qubit namespace, surviving rows, surviving row spaces, and parameters
($n$, $k$) are therefore the same for every enumeration order. Both orders are
applicable (each deletion applies because a subset of an independent set is
independent). Provenance step records differ in order only, which is allowed.

**Annotation-transport part.** Under the fixed-reference-set model, deleting
identifier $r$ updates the valid set by
$V\mapsto V\setminus\{c:r\in\operatorname{Ref}(c)\}$. The composition over
$S=\{r_1,\dots,r_t\}$ is
$(f_{r_t}\circ\cdots\circ f_{r_1})(V)=V\setminus\bigcup_{r\in S}\{c:r\in
\operatorname{Ref}(c)\}$, which makes set-level commutativity and idempotence
immediate from set difference. Hence the transported context depends only on the
deleted-identifier set $S$, not on enumeration order. $\square$

## 4.16 — Row-replacement factorization, loop part (`OBL-ROW-REPLACEMENT-FACTOR`)

 Evidence, not machine-checked; re-derived
–. Only the delete-then-add loop is proved here. ****
the generation conjunct is proved at §4.18, where its classical citation
(Artin, *Geometric Algebra*) is recorded; the `proposed (classical)`
framing above is retained and marked.

Let $r$ be a displayed independent generator of one stabilizer type in a
well-formed state, and let $s$ lie in the span of the surviving displayed
generators of the same type.

- *Applicability of deletion.* $r$ is displayed and independent, so
 `C-DELETE-CHECK` on $r$ applies.

- *Applicability of addition.* `C-ADD-CHECK` has three applicability premises
 (`spec/OPERATIONAL_SEMANTICS.md` §2; `machine/semantics.json`):
 1. Ambient membership (W22): $\operatorname{supp}(r+s)\subseteq Q$, since
 $r\in\mathbb{F}_2^Q$ and $s\in\langle\mathit{rows}_\tau\setminus\{r\}\rangle
 \subseteq\mathbb{F}_2^Q$.
 2. Opposite-sector commutation: $r+s\in(\mathit{rows}_{\bar\tau})^\perp$,
 because $r\perp\mathit{rows}_{\bar\tau}$ and every row in
 $\mathit{rows}_\tau\setminus\{r\}$ is orthogonal to
 $\mathit{rows}_{\bar\tau}$ by input I1, deletion leaves
 $\mathit{rows}_{\bar\tau}$ unchanged, and
 $(\mathit{rows}_{\bar\tau})^\perp$ is linear.
 3. Same-sector independence: $r+s\notin\langle\mathit{rows}_\tau\setminus
 \{r\}\rangle$. After deletion, the surviving generators span the
 codimension-1 subspace $\langle\mathit{rows}_\tau\setminus\{r\}\rangle$,
 which does not contain $r$ by I2; since $s$ is in their span, $r+s$ is not
 in their span (otherwise $r$ would be). Hence `C-ADD-CHECK` on $r+s$
 applies.

- *Row space restoration.* Deletion removes $r$; addition appends $r+s$.
 The final row space is $\langle \mathit{rows}\setminus\{r\}\rangle + \langle r+s\rangle
 = \langle \mathit{rows}\setminus\{r\}\rangle + \langle r\rangle = \mathit{rows}$,
 because $s$ is in the span of the survivors. Thus the row space is unchanged
 and $k$ returns to its original value.

- *Presentation change.* The final displayed set has $r$ replaced by $r+s$ with
 a fresh identifier (the retired one is never reused), and `used` strictly
 grows. Hence the composite is not a state identity ($\not\equiv$), only a
 row-space/presentation identity.

$\square$

## 4.17 — Fixed-namespace reachability (`OBL-FIXED-NAMESPACE-REACHABILITY`)

Let $C_0,C_1$ be well-formed phase-insensitive CSS states on the same finite
qubit namespace $Q$. We construct a finite `C-SEQUENCE` from $C_0$ to a state
whose supports are those of $C_1$ (canonical identifiers).

- *Delete all.* The displayed rows of each sector of $C_0$ are independent (I2).
 Deleting an independent row from an independent set leaves the remainder
 independent, so each `C-DELETE-CHECK` is applicable until the sector is empty.
 `C-DELETE-CHECK` does not mint identifiers, so $\mathsf{used}$ is unchanged by
 every deletion; the result is the zero state on $Q$: no rows, $k=n$, with the
 original $\mathsf{used}$ set retained. Apply deletions for every displayed
 row of $C_0$ in a fixed order. The result is the zero state on $Q$:
 no rows, $k=n$.
- *Add all.* The target $C_1$'s rows in each sector are independent and each
 commutes with every row of the opposite target sector (well-formedness of
 $C_1$). Adding them in a fixed order to the zero state: each new row is
 independent of the current same-sector rows (a subset of an independent set)
 and commutes with the current opposite-sector rows (a subset of the target
 opposite sector), so `C-ADD-CHECK` is applicable. Each addition mints one
 fresh identifier per row of $C_1$, which assumes sufficient remaining
 capacity in the fixed 70,000-identifier enumeration of I3; if the enumeration
 is exhausted the construction is inapplicable. The final
 displayed rows have the exact supports and sectors of $C_1$'s displayed rows
 (all in $\mathbb{F}_2^Q$), with canonically minted identifiers; row spaces
 match. Exact labeled reachability and $\mathsf{used}$-set equality are not
 claimed .

Thus $C_1$'s supports are reachable from $C_0$ at fixed namespace, with all
deletions before all additions. $\square$

## 4.18 — Generation conjunct of `OBL-ROW-REPLACEMENT-FACTOR`

 Evidence, not machine-checked.

The composite of `C-DELETE-CHECK` followed by `C-ADD-CHECK` on $r+s$ replaces a
basis vector $r$ by $r+s$ (§4.16, proved there). This is an elementary row
operation: adding a multiple of one basis vector to another. Over
$\mathbb F_2$ the elementary matrices $I+E_{ij}$ (add row $j$ to row $i$)
generate $\mathrm{GL}_m(\mathbb F_2)$, where $m$ is the sector rank (not the
qubit count $n$): Gaussian elimination by row additions alone clears all
non-pivot entries in each column, reducing any invertible $m\times m$ binary
matrix to a permutation matrix, and any transposition of two rows over
$\mathbb F_2$ factors into three transvections
($r_i\mapsto r_i+r_j$, $r_j\mapsto r_j+r_i$, $r_i\mapsto r_i+r_j$); equivalently,
E. Artin, *Geometric Algebra* (1957), Ch. IV, on transvections generating
$\mathrm{SL}_m(\mathbb F_2)=\mathrm{GL}_m(\mathbb F_2)$. Each elementary
matrix is realized by one delete-add loop on a suitable displayed basis.
Deletion alone reduces rank; addition alone increases it; the loop preserves
rank and changes the basis. Generation holds up to canonical identifier
allocation and `used`-set growth: each loop retires one identifier and mints a
fresh one, so the generated basis changes are realized up to canonical
identifier allocation . Hence the core moves generate all basis changes
of a fixed-dimensional row space. $\square$



## 4.19 — Reproduced derivations for the conditional construction cells

Hand derivations, reproduced from an external manuscript (Theorem 12.1 —
manuscript Theorem 7 —, Proposition 18.3, Theorem 28.1–28.3) and adapted to
this repository's CSS state model and vocabulary. Evidence, not machine-checked.
See `REFERENCES.md`.

Three of the source's steps do not transfer to the transition as specified in
§2, and are marked **corrected** below: Lemma 28.1a, the spliced-sector
paragraph of Theorem 28.2, and the non-spliced $(\le)$ step of Theorem 28.2.
Theorem 28.3 is **refuted** for this transition, not reproduced; the
counterexample is at §4.20.

### Theorem 12.1 (check deletion) — reproduced

Setting: a CSS code with stabilizer group $S$ of rank $s$ on $n$ qubits,
$k=n-s$ logicals; delete $r$ independent generators, giving $S'$ of rank
$s-r$, $k'=k+r$.

1. $k'=k+r$ exactly: independence of the kept generators is inherited, so
 $\dim S'=s-r$ and $k'=n-(s-r)=k+r$.
2. $d'\le d$: $S'\subseteq S$ gives $N(S')\supseteq N(S)$, hence
 $N(S')\setminus S'\supseteq N(S)\setminus S$, and the minimum over the
 larger set is $\le d$.
3. $d'=\min\bigl(d,\ \min_{g\in S\setminus S'}|g|,\ \min\{|E|:E\in N(S')\setminus N(S)\}\bigr)$:
 since $S$ is abelian, $S\subseteq N(S')$ and $N(S)\subseteq N(S')$, so
 $N(S')\setminus S'$ is the disjoint union of (i) old logicals
 $N(S)\setminus S$, (ii) promoted stabilizers $S\setminus S'$, and
 (iii) newly exposed operators $N(S')\setminus N(S)$. Taking minimum
 weights over the three parts gives the formula. $\square$

The two-term formula $\min(d,\min_{S\setminus S'}|g|)$ is false: the third
class (operators anticommuting with a deleted generator) can be lighter, as in
the $[[4,2,2]]$ code $S=\langle XXXX, ZZZZ\rangle$ deleting $ZZZZ$:
$d=2$, the promoted generator has weight $4$, and $X_1$ commutes with
$XXXX$ while anticommuting with $ZZZZ$, so $d'=1$ while the two-term
formula gives $2$. The full-distance deletion
price $d'=\min(d,w_{\rm del},w_{\rm exp})$ is the consumer-supplied form of
this three-class minimum. $\square$

### Proposition 18.3 (strict improvement) — reproduced

Setting: stabilizer $S$, add $r$ independent commuting Paulis $A$ with
$S'=S+\langle A\rangle$, $k'=k-r$, killed span $K=S+\langle A\rangle$ over
$S$.

By Proposition 18.2, $d'=\min\{\operatorname{wt}(g):g\in N(S),\ g\in A^\perp,\
g\notin S+\langle A\rangle\}$. Thus $d'=d$ iff some weight-$d$ old logical
survives (commutes with every $a\in A$ and avoids $K$); negating gives

$$
d'>d \iff \text{every old logical class of coset-min-weight }d
\text{ anticommutes with some }a_i\text{ or lies in }K.
$$

Both conditions are class-invariant because $S$ commutes with $A$ and
$K$ is a union of $S$-cosets. $\square$

The consumer's strict-improvement cell carries $d'\ge d+1$ exactly when the
caller supplies an exact old $d$ and an exhaustive enumeration showing every
minimum-weight class is killed; the proposition is the justification for that
hypothesis. $\square$

### Theorem 28.1 (only deleted rows can expose a logical) — reproduced

In an `E-GRAFT` at qubit $q$, the opposite sector's checks are only shortened:
$c\mapsto c\setminus\{q\}$. For any logical $E$ of the child, $E_q=0$, so

$$
\operatorname{popcount}(E\cap(c\setminus\{q\}))
=\operatorname{popcount}(E\cap c),
$$

because $E$ has zero weight at $q$. Commutation parity is unchanged, so a
shortened check imposes exactly the constraint it imposed before. New logicals
can arise only from the $r$ deleted rows. $\square$

### Lemma 28.1a (the promoted term is vacuous) — reproduced, corrected

Let $S_1,\dots,S_m$ be the same-type stabilizers through $q$ and
$C_i=S_iS_{i+1}$ the chain products. The even-weight subspace
$E\subseteq\mathbb{F}_2^{m}$ (vectors with $\sum_i e_i=0$) is spanned by
$e_i+e_{i+1}$, which map under the natural map to $C_i$; any old stabilizer's
part through $q$ has even total multiplicity in the retired rows, so its
restriction to $Q\setminus\{q\}$ lies in the span of the $C_i$ together
with the unchanged $\tau$-rows not through $q$ and the shortened
$\sigma$-rows. Every old stabilizer whose $q$-coordinate is $0$ therefore
**remains a child stabilizer** — it is neither promoted nor killed. The
retired rows $S_i$, whose $q$-coordinate is $1$, are *killed* rather than
promoted: provided at least one opposite-sector row passes through $q$,
$S_i|_{Q\setminus\{q\}}$ anticommutes with every shortened
opposite-sector row through $q$, so it is not a child logical; if no such row
passes through $q$, then $e_q$ commutes with every $\sigma$-row, and
$S_i|_{Q\setminus\{q\}}$ is either a child stabilizer ($e_q$ in the
$\tau$-span) or the restriction of the parent $\tau$-logical $S_i+e_q$,
and the promoted term remains vacuous in either case. No old stabilizer is
promoted to a logical, and the promoted term is $\infty$.
$\square$

> **Correction to the source's wording.** The source's Lemma 28.1a reads
> "no old stabilizer survives a graft", which states the opposite of what the
> argument shows. The argument shows that old stabilizers with $q$-coordinate
> $0$ *do* survive as child stabilizers, and that the retired ones are killed
> rather than promoted; it is the *promotion* that is vacuous, which is what
> the lemma is used for. The even-parity subspace is a subspace of
> $\mathbb{F}_2^{m}$, not of $\mathbb{Z}^{m}$.

### Theorem 28.2 (sector-wise graft price) — reproduced, corrected

For a graft at qubit $q$ in sector $\tau$, with coverage guard, define for the
non-spliced sector $\sigma=\bar\tau$ the **exposed set** as the child
$\sigma$-logicals whose lift touches $q$ (§4.13), and set

$$
w_{\mathrm{expose},\sigma}
=\min\{|z|-1 : z \text{ a parent }\sigma\text{-logical with } z_q=1\},
$$

with $\min\emptyset=\infty$. Then
$d'_\sigma=\min(d_\sigma,w_{\mathrm{expose},\sigma})$.
For the spliced sector $\tau$, the exposure set is **empty** — exactly as
Theorem 28.1 shows, the shortened opposite-sector checks impose no new
constraint, so no new $\tau$-logical appears. The equality $d'_\tau=d_\tau$
fails for a different reason: the child's $\tau$-logicals are the parent
$\tau$-logicals restricted to $Q\setminus\{q\}$ with $x_q=0$, so

$$
d'_\tau=\min\{|x| : x \text{ a parent }\tau\text{-logical with } x_q=0\},
$$

which exceeds $d_\tau$ when every minimum-weight parent $\tau$-logical
touches $q$. The source's $(\le)$ step needs a minimum-weight parent
$\tau$-logical that avoids $q$, and such a logical need not exist. The
spliced sector's lower endpoint therefore carries and its upper endpoint is
reset to $+\infty$ unless a child-valid witness supplies one. The scalar form
$d'=\min(d,w_{\mathrm{expose},\bar\tau})$ and the claim $d'\le d$ are
refuted for this transition (see §4.20).

> **Note on the source's wording of the exposed set.** The source states the
> exposed set set-based, over candidate vectors $E$ with $E_q=0$ that are
> orthogonal to every new opposite-sector check, are outside $S'_\sigma$, and
> fail to commute with some old check. The definition used here is the one
> §4.13 derives and `spec/JUDGMENT_LAYER.md` §2c states: the exposed set is
> the child $\sigma$-logicals whose lift touches $q$, and the price is its
> minimum weight, which is $|z|-1$ for the parent $\sigma$-logical $z$ it
> comes from. The two are the same set *in this repository's transition*,
> because §4.13's bijection identifies the child $\sigma$-logicals with the
> restrictions of the parent $\sigma$-logicals; the source's set-based wording
> is recorded here for provenance.

*Proof (non-spliced sector).* The promoted term is vacuous for the
non-spliced sector for a simpler reason: the child $\sigma$-span is the
restriction of the parent $\sigma$-span, so no $\sigma$-stabilizer can
become a $\sigma$-logical. (Lemma 28.1a, which concerns $\tau$-type
stabilizers through $q$, is not needed here.) Restriction to
$Q\setminus\{q\}$ is a
bijection from parent $\sigma$-logicals to child $\sigma$-logicals (§4.13),
and $|z|_{Q\setminus\{q\}}|=|z|-z_q$ for a parent $\sigma$-logical $z$.
Split the parent $\sigma$-logicals by $z_q$, and write
$A=\min\{|z|:z\text{ a parent }\sigma\text{-logical with }z_q=0\}$ and
$B=\min\{|z|-1:z\text{ a parent }\sigma\text{-logical with }z_q=1\}
=w_{\mathrm{expose},\sigma}$, with $A=+\infty$ or $B=+\infty$ when the
corresponding set is empty. The bijection gives
$d'_\sigma=\min(A,B)$ and $d_\sigma=\min(A,B+1)$, hence
$d'_\sigma=\min(d_\sigma,w_{\mathrm{expose},\sigma})$.

> **Correction to the source's proof.** The source argues that "a surviving
> old logical is also a child logical, so the minimum is attained at one of
> the two terms". That covers only parent $\sigma$-logicals with $z_q=0$ —
> the case $A\le B+1$. When every minimum-weight parent $\sigma$-logical
> touches $q$, $A>B+1$ and the minimum is attained on the $z_q=1$ side
> instead: a minimum-weight parent $\sigma$-logical $z$ has $z_q=1$, and its
> restriction has weight $d_\sigma-1=|z|-1$, which is exactly what the
> exposure term counts. The equality survives, but the stated reason for it
> does not, and the case split has to be made explicit.

For $\sigma=\tau$ (spliced sector), the lower endpoint carries and the upper
endpoint is reset to $+\infty$ (§4.13). $\square$

### Theorem 28.3 (scalar monotonicity) — refuted for this transition

The source's Theorem 28.3 states a scalar price
$d'=\min(d,w_{\mathrm{expose},\bar\tau})$ together with the monotonicity
$d'\le d$. For the transition as specified in §2, **both statements are
false**, so this is a refutation and not a reproduction. The $8$-qubit
example of §4.20 has $d=2$ in the parent and $d'=3$ in the child, so
$d'\le d$ fails for every value of the price, and no scalar minimum can
reproduce the child's distance. What survives is the sector-wise form of
Theorem 28.2, $d'_\sigma=\min(d_\sigma,w_{\mathrm{expose},\sigma})$ for the
non-spliced sector, together with the spliced sector's $d'_\tau\ge d_\tau$.
The full distance $d'=\min(d'_\tau,d'_{\bar\tau})$ is therefore neither
$\le$ nor $\ge d$ in general. $\square$

These derivations are reproduced in-repository; the cells remain **conditional**
on the consumer-supplied hypotheses, but their source derivations are no longer
external. $\square$

## 4.20 — The graft examples that refute the scalar form

Two worked examples, checked with the repository's own exact-distance oracle
(`the conformance harness`, `exact_distances`). The
oracle is an external exhaustive enumeration kept in that experiment only; it
is evidence, not a proof, and the consumer never calls it.

Throughout, $Q=\{0,\dots,n-1\}$, rows are given as supports, $d_X$ and $d_Z$
are the sector distances, and $d=\min(d_X,d_Z)$.

### The spliced sector is not carried exactly — 7 qubits

$X$ rows $(0,4,6)$, $(2,4)$, $(0,1,4,5,6)$, $(0,2,3,5,6)$; $Z$ rows
$(1,2,3,4,5,6)$, $(0,2,4)$. Graft at $q=0$, $\tau=Z$, chain $[(0,2,4)]$.
The opposite-sector guard holds ($0$ lies in the $X$ row $(0,4,6)$), coverage
holds, $k'=k=1$.

| | $d_X$ | $d_Z$ | $d$ |
| --- | --- | --- | --- |
| parent | 2 | 2 | 2 |
| child | 2 | **3** | 2 |

The only weight-2 $Z$-logical of the parent is $Z$ on $\{0,6\}$, which touches
$q$, so it does not survive; and no weight-2 $Z$-logical of the child exists,
because on $\{1,\dots,6\}$ every qubit has a distinct membership pattern
across the child's $X$ rows. The spliced sector's distance rises from $2$ to
$3$, so the rule $d'_\tau=d_\tau$ is false, and an interval that carried the
spliced upper endpoint $2$ would exclude the child's exact $3$.

### The full distance can increase — 8 qubits

$X$ rows $(2,5,6,7)$, $(0,4,6,7)$, $(0,2,3,6)$, $(0,1,2,5,6)$; $Z$ rows
$(0,4,6,7)$, $(0,1,2,3,6)$, $(3,4,5,6)$. Graft at $q=1$, $\tau=X$, chain
$[(0,1,2,5,6)]$.

| | $d_X$ | $d_Z$ | $d$ |
| --- | --- | --- | --- |
| parent | 2 | 3 | 2 |
| child | **3** | 3 | **3** |

The parent's only weight-2 $X$-logical is $X$ on $\{1,2\}$, which touches
$q=1$; its restriction has weight $1$, and the child has no weight-2
$X$-logical at all, so the child's $X$-distance is $3$. The full distance
rises from $2$ to $3$, which refutes $d'\le d$ for every value of the
exposure price: a price of $3$ bounds $d'$ by $3$, not by the parent's $2$,
and the child's exact $3$ is excluded by any interval whose upper endpoint
is the parent's $2$.

### What the corrected rules emit on these two examples

Seeded with the parent's exact intervals, the consumer under the corrected
rules of §4.13 emits, on the 7-qubit example, full $[0,2]$, $X$ $[0,2]$ and
$Z$ $[2,+\infty)$ — the spliced lower endpoint carries and its upper endpoint
is dropped — and on the 8-qubit example, full $[0,3]$, $X$ $[2,+\infty)$ and
$Z$ $[0,3]$. Every emitted interval contains the child's exact distance in
both cases. Under a supplied exposure price of $3$, the 8-qubit example emits
full $[2,3]$, $X$ $[2,+\infty)$ and $Z$ $[3,3]$, again containing the exact
distances. The rules before the 2026-10-21 correction carried the parent's
upper endpoint instead, and on the 8-qubit example that excluded the exact
$3$ and made `decide(3)` return `prune`.

These two examples are also regression inputs in
`machine/test_priced_calculus.py`.


## 4.21 — Interaction-radius transport (`OBL-LOCALITY-TRANSPORT`)

 Evidence, not machine-checked; re-derived
.

Let $C$ be well-formed, let $\lambda$ be a layout covering every qubit of $Q$
— one coordinate per qubit, a layer count $\rho$, optionally a module id per
qubit — and let

$$\mathrm{diam}_\lambda(s)=\max_{a,b\in s}\|\lambda(a)-\lambda(b)\|_2$$

be the diameter of a support in that layout. Define the **interaction
radius**

$$r(C,\lambda)=\max\{\mathrm{diam}_\lambda(s): s\in\mathit{rows}\},$$

and $r=0$ for an empty display.

The radius is a derived property of the display **relative to the layout**, in
the same sense that $w$ is a derived property of the display: it is computed,
never stored, and no search is involved. The layout is ledger data, not state
data ([`spec/STATE_MODEL.md`](STATE_MODEL.md) §1, §3): it is not minted, not
part of identity, and not transported by `used`. The radius is therefore a
function of the *pair* (state, layout); a state with no layout has no radius,
and the calculus never claims one for the state alone.

Throughout, $\lambda'=\lambda\vert_{Q'}$ is the layout restricted to a qubit set
$Q'$. Every transition either preserves $Q$, removes one qubit from it, or
forms a disjoint union; and the state keeps the parent's qubit labels, so the
child's coordinates are the parent's coordinates read at the child's qubits.

- **`C-SKIP`.** $Q'=Q$ and the display is unchanged, so $r'=r$.

- **`C-DELETE-CHECK`.** $Q'=Q$ and the display loses one row $r_0$, so
 $$r'=\max\{\mathrm{diam}_\lambda(s): s\in\mathit{rows}'\}\le r.$$
 The inequality is deletion of one element from the set the maximum is taken
 over. The value is exact and no hypothesis is needed, and the direction is
 the useful one: a deletion can only lower the radius.

- **`C-ADD-CHECK`.** $Q'=Q$ and the display gains one row $r_{\mathrm{new}}$, so
 $$r'=\max\bigl(r,\ \mathrm{diam}_\lambda(r_{\mathrm{new}})\bigr).$$
 Exact, and no hypothesis is needed.

- **`C-DIRECT-SUM`.** $Q'=Q_A\sqcup Q_B$ and the display is the concatenation of
 the two displays, so with $\lambda'$ the disjoint union of the two layouts,
 $$r=\max(r_A,r_B).$$
 The *radius* law needs no hypothesis. The *honesty* of the merged layout
 does, and this cell is conditional on it — see below.

- **`E-GRAFT` at $q$.** $Q'=Q\setminus\{q\}$ and $\lambda'=\lambda\vert_{Q'}$.
 The selected-sector rows touching $q$ are replaced by their adjacent products
 $a_i\oplus a_{i+1}$ restricted to $Q'$, and the opposite-sector rows are
 shortened at $q$. The exact value is
 $$r'=\max\{\mathrm{diam}_{\lambda'}(s): s\in\mathit{rows}'\},$$
 a recomputation that needs no hypothesis. The **bound** is the substantive
 part:

 > **Claim.** $r'\le 2r$.

 *Proof.* Let $a_i,a_{i+1}$ be two consecutive rows of the graft chain, so
 $q\in\operatorname{supp}(a_i)\cap\operatorname{supp}(a_{i+1})$, and let
 $b=(a_i\oplus a_{i+1})\cap Q'$ be the support of the minted row. Take
 $u,v\in b$. Each of $u,v$ lies in $a_i\setminus\{q\}$, in
 $a_{i+1}\setminus\{q\}$, or one in each.

 - Both in $a_i\setminus\{q\}$: $u,v\in a_i$, so
 $\|u-v\|\le\mathrm{diam}_\lambda(a_i)\le r$.
 - Both in $a_{i+1}\setminus\{q\}$: likewise
 $\|u-v\|\le\mathrm{diam}_\lambda(a_{i+1})\le r$.
 - One in each: say $u\in a_i\setminus\{q\}$ and
 $v\in a_{i+1}\setminus\{q\}$. Since $q$ belongs to both rows, the
 triangle inequality gives
 $$\|u-v\|\le\|u-q\|+\|q-v\|
 \le\mathrm{diam}_\lambda(a_i)+\mathrm{diam}_\lambda(a_{i+1})\le 2r.$$

 Hence $\mathrm{diam}_{\lambda'}(b)\le 2r$. The untouched selected-sector rows
 keep their diameter, at most $r$. The opposite-sector rows are shortened at
 $q$, and removing a point from a set cannot increase its diameter, so each
 is at most $r$. Every row of the child therefore has diameter at most $2r$,
 and $r'\le 2r$. $\square$

 **The non-increase claim is false.** $r'\le r$ does not hold: a graft can
 increase the radius. Over the qLDPC challenge's board entries with $n\le 14$
 carrying a two-dimensional layout, 277 grafts are applicable and 74 of them
 increase the radius, the largest observed ratio being $r'/r=1.6125$
 (`the conformance harness` and its recorded report). The
 survey is evidence, never confirmation; what it shows is that the naive
 monotonicity is refuted by example, and the factor-of-two bound is what
 survives.

**Honesty.** A layout is *honest* when at most $\rho$ qubits share a site and
distinct sites are at least $1$ apart. Honesty is a property of the layout
alone, not of the check set. It is inherited unchanged by `C-SKIP`,
`C-DELETE-CHECK` and `C-ADD-CHECK`, and it is preserved by `E-GRAFT`: removing
a qubit from a site can only lower that site's occupancy, and removing a site
from the point set can only raise the minimum distance between distinct sites.
A direct sum does **not** preserve honesty automatically — merging two layouts
can place two qubits on one site — so the direct-sum cell requires a merged
layout that is honest.

**What this does not claim.** The radius is not a distance. No lower bound,
interval, price, witness, or minimum-weight enumeration enters any rule
above, because none is needed: the quantity is exactly computable from the
display and the layout. The locality class is not claimed here either; it is a
consumer-side verdict computed from the transported radius against
consumer-supplied caps, and its transport follows from the rules above rather
than from a separate cell.

## 4.22 — Tanner-connectivity transport

 Evidence, not machine-checked; re-derived
.

Let $\Gamma(C)$ be the combined X+Z Tanner graph of a presented state's
**displayed** rows: one node per qubit of $Q$, one node per displayed row, one
edge for every row–qubit incidence. Let $\kappa(C)$ be its number of connected
components. Like $w$, $\kappa$ is a derived property of the display: computed,
never stored, no hypothesis. Each construction is a one-liner on the
node-and-edge description of the primitive's state update.

- **`C-SKIP`.** The state is unchanged, so $\kappa'=\kappa$. $\square$

- **`C-ADD-CHECK`.** The child's node set is the parent's plus one check node,
 and its edge set is the parent's plus that node's support edges; existing
 adjacency is retained. So any two nodes that were in one component are in
 one component after the step, and $\kappa'\le\kappa$. $\square$

- **`C-DELETE-CHECK`.** The child's node set drops one check node and its
 incident edges. An already-connected graph can disconnect: the parent can
 lose a cut vertex. The exact child value is a recomputation; no hypothesis
 is needed. $\square$

- **`C-DIRECT-SUM`.** Under the disjointness premises no edge joins the two
 factors (no shared qubit; each displayed row is in exactly one factor), so
 the child's Tanner graph is the disjoint union of the factors' graphs and
 $\kappa'\ge 2$ whenever both are nonempty: the direct sum certifies a
 disconnected code. **This is the reason the qLDPC challenge's
 `tanner_connected` hard gate rejects a direct sum as a board-advancing
 submission** — moving that fact out of the 2026-10-19 fieldnote. $\square$

- **`E-GRAFT` at $q$.** The child drops the qubit node $q$; the chain rows
 touching $q$ are replaced by the products $a_i\oplus a_{i+1}$ restricted to
 $Q'$, and the opposite-sector rows are shortened at $q$. Edges through $q$
 and the touching rows vanish, so a parent connected through them can
 disconnect; the exact child value is a recomputation. $\square$

**What this does not claim.** The Tanner graph is built from the displayed
rows, so connectivity is display-relative (like $w$ and $r$): $\kappa$ is not
part of $\equiv$ and not a code-level invariant. The strictly stronger
stabilizer-group predicate of the same gate is implemented in the consumer
(`stabilizer_group_components`, matching the verifier's per-sector reduction)
but is not carried as a spec cell.

## 4.23 — Factorization of derived terms (`OBL-DERIVED-TERM-FACTORIZATION`)

 Evidence, not machine-checked; re-derived
–. Discharges `OBL-DERIVED-TERM-FACTORIZATION`.

A *derived command* is, by the admission rule of `spec/CLAIMS.md`, a named
operation whose signature and equivalence notion ($\equiv$ or $\approx$) are
fixed at admission time. The calculus admits such a command only after it has
been proved equivalent to a sequence of elementary commands
(`C-SKIP`, `C-DIRECT-SUM`, `C-DELETE-CHECK`, `C-ADD-CHECK`, `C-SEQUENCE`).

**Claim.** Every derived command admitted under that rule factors into a
canonical finite sequence of elementary commands, and its equivalence to that
sequence is inherited from the elementary steps.

The argument is structural and uses only results already in this repository:

1. **Closure under sequencing.** `C-SEQUENCE` (`spec/OPERATIONAL_SEMANTICS.md`
 §2) composes two evaluations sharing an intermediate state, so any finite
 sequence of elementary commands is itself a command of the calculus. A
 derived command is therefore expressible as a single `C-SEQUENCE` tree.

2. **Associativity of sequencing.** `OBL-SEQUENCE-ASSOCIATIVITY` is discharged
 at §4.8: $(m_1;m_2);m_3 \equiv m_1;(m_2;m_3)$ as commands, because the
 intermediate state is unique up to $\equiv$ and `steps` is semantically inert. Hence the factorization is insensitive to parenthesization;
 a derived command has a canonical flat sequence.

3. **Canonical minting.** I3 makes the identifier allocated by each
 `C-ADD-CHECK` a function of the current $\mathsf{used}$ set, and `C-DELETE-CHECK`
 does not mint. Thus the identifiers produced by a fixed elementary sequence
 are determined by the initial $\mathsf{used}$ set and the order of the
 additions in the sequence; two factorizations with the same elementary steps
 in the same order mint identically. Reordering additions changes which
 minted identifier labels which row, and the two results are in general
 neither $\equiv$ nor $\approx$: $\approx$ transports qubits and leaves
 identifiers untouched (§4.22), and §4.10's `Add`/`Add` case (the 
 witness of `OBL-CROSS-SECTOR-PERMUTATION`) gives two orders of
 opposite-sector additions whose outputs no admitted equivalence
 identifies. The factorization is therefore stated for a fixed ordered
 elementary expansion: a derived command is admitted with one order of its
 additions, and its identifiers are those of that order. Associativity
 (step 2) flattens an expansion; it does not identify its reorderings.

4. **Equivalence inheritance.** Each elementary step's carry/equivalence
 properties are recorded in `spec/JUDGMENT_LAYER.md` §2. A sequence's
 overall equivalence is the composition of its steps' equivalences, by
 `C-SEQUENCE`'s transitivity of $\equiv$ (and $\approx$ where the signature
 demands it). Therefore a derived command's equivalence to its factorization
 is the composition of the steps' equivalences, all of which are already
 proved or recorded as conditional.

5. **Instances already identified.** Multi-row deletion as a batch operation
 factors into repeated `C-DELETE-CHECK` (order independence discharged at
 `OBL-ORDER-INDEPENDENT-DELETION`, §4.10's Case 1 for delete/delete). The
 row-replacement loop factors into `C-DELETE-CHECK` then `C-ADD-CHECK`
 (§4.16, generation at §4.18). Both satisfy the admission rule above.

**Conclusion.** The admission rule is satisfiable: every derived command whose
signature and equivalence notion are fixed at admission time factors into a
canonical elementary sequence, with deterministic minting and inherited
equivalence. No derived command is admitted without such a factorization
proof; the framework provides the primitives and the associativity/canonical-minting
results that make the proof mechanical. $\square$

## 4.24 — Certificate-path keying and route-scoping (`OBL-CERTIFICATE-PATH-KEYING`)

 Evidence
status of `OBL-CERTIFICATE-PATH-KEYING`: `proved`. Discharges
`OBL-CERTIFICATE-PATH-KEYING`. The three Gate 5 questions recorded
at the end of this section remain explicitly open and are not settled by this
discharge.

The reserved `certificate-checked` path attaches to **per-state atomic
judgments** and never to operation contracts (.
Two things are owed: keying and route-scoping.

**Keying.** A certificate speaks for an instance identified by the
triple $(C, P, \sigma)$: the state $C$, the property $P$, and the sector
$\sigma$ where $P$ is sector-indexed. The certificate is keyed to that triple;
it is not transferable to a different state, property, or sector. An
operation-contract claim is over a triple $(m, S, S')$ of command and two
states, not a single state, so a per-state certificate can never support an
operation-contract claim: the keying domains do not match. This is the typing
discipline that makes 's distinction checkable.

**Route-scoping.** To establish that a claim labelled
`unavailable` on route $R$ is not derivable on route $R'$, the checker
re-runs the calculus's derivability check — the same syntax-directed rule
system and the same premises — on $R'$. Because derivability is a property of
the rule system applied to a stated state, and the rules are syntax-directed
with finite premises (card conditions, independence, commutation), absence of a
derivation on $R'$ is verified by the same procedure that would find one:
failure of the premises, not a search over distances. Opacity (D2) forbids a
rule from *computing* a distance; route-scoping asks only about derivability
of the judgment, so the two obligations do not discharge each other.

**What this does not settle.** Whether the keying above is the intended one,
whether a checker must additionally discharge a non-derivability proof, and
whether `certificate-checked` ever gains a second (operation-contract) variant.
These remain Gate 5 decisions. $\square$ (discharge)

## 4.25 — Presentation conjugation (`OBL-PRESENTATION-CONJUGATION`)

 Evidence, not machine-checked; re-derived
–. Discharges `OBL-PRESENTATION-CONJUGATION`.

Let $\sigma$ be a permitted qubit relabeling: a bijection on the qubit
namespace $Q$ that transports the display (qubits, displayed rows, sector
labels) and leaves identifiers and the $\mathsf{used}$ set untouched, so that
$S\approx \tilde S$ with $\tilde S=\sigma S$. Presentation equivalence
transports qubits and displayed rows but not identifiers
([`TAXONOMY.md`](TAXONOMY.md) §1.4); $\sigma$ acts on supports and qubit
labels only. Supports are presented in increasing order by the display
contract, so a transported support is presented in the child's label order.

**Claim.** For every command $m$ in the MVP kernel and every state $S$:
$$\operatorname{Eval}(m,S,S') \iff
\operatorname{Eval}(\sigma m,\tilde S,\widetilde{S'})$$
where $\sigma m$ is the transported command (support-transported for
additions, identifier-stable for deletions, pointwise for sequences), and
$\widetilde{S'}=\sigma S'$.

The proof is by structural induction on the evaluation derivation. Each
clause below checks that every premise of the rule is invariant under
$\sigma$ and that the conclusion state transports.

- **`C-SKIP`.** $\operatorname{Eval}(\mathsf{skip},S,S)$ holds iff
 $S'=S$. Under $\sigma$, $\operatorname{Eval}(\mathsf{skip},\tilde S,\tilde S)$
 holds iff $\widetilde{S'}=\tilde S$, i.e. $\sigma S'=\sigma S$, i.e.
 $S'=S$ since $\sigma$ is a bijection. $\square$ for skip.

- **`C-DIRECT-SUM` (expression level).** For $\oplus$, a global bijection
 preserves disjointness:
 $\sigma Q_A\cap \sigma Q_B=\sigma(Q_A\cap Q_B)$, and $\mathsf{used}$ is
 untouched by $\sigma$, so $\mathsf{used}$-disjointness is label-invariant.
 Hence $\operatorname{EvalExpr}(e_1\oplus e_2,S)$ iff
 $\operatorname{EvalExpr}(\sigma(e_1\oplus e_2),\tilde S)$, with output
 $\widetilde{S_1\oplus S_2}=\tilde S_1\oplus \tilde S_2$. Per-summand
 relabelings compose with the summand embedding; relabelings cutting across a
 summand boundary are outside the congruence's scope (scoping). $\square$
 for direct sum.

- **`C-DELETE-CHECK`.** Premises:
 1. $\operatorname{DisplayedGenerator}(r,S)$: $r$ names a live row of $S$.
 The row set transports bijectively and identifiers are untouched, so $r$
 names a live row of $\tilde S$. Conversely the same map back.
 2. $\operatorname{IndependentGenerator}(r,S)$: $r$'s vector is not in the
 span of the other rows in its sector. Linear span membership is invariant
 under the coordinate permutation $\sigma$ on qubit labels, so independence
 transports in both directions.
 Conclusion: $\operatorname{deleteState}(S,r)$ removes the row with id $r$
 and leaves $\mathsf{used}$ unchanged. Since $\sigma$ commutes with filtering
 by id, $\sigma(\operatorname{deleteState}(S,r))=
 \operatorname{deleteState}(\tilde S,r)$. Thus
 $\operatorname{Eval}(\operatorname{delete}_r,S,S')$ iff
 $\operatorname{Eval}(\operatorname{delete}_r,\tilde S,\widetilde{S'})$,
 with the same identifier $r$ on both sides (identifier-stable).
 $\square$ for deletion.

- **`C-ADD-CHECK`.** The transported command is
 $\operatorname{addStab}_{\sigma r}$, where $\sigma r$ is the transported
 support. Premises:
 1. $\operatorname{supportSubset}(r,Q)$: $\sigma$ maps $Q$ to $\tilde Q$, so
 $\sigma r\subseteq \tilde Q$.
 2. $r.\mathrm{Nodup}$ and $r$ sorted: $\sigma$ is injective, so nodup
 transports; sortedness is re-presented in the child's label order by the
 display contract.
 3. Commutation: for every opposite-sector row $x\in S$,
 $\operatorname{supportIntersectionSize}(r,x.\mathrm{support})\bmod 2=0$.
 $\sigma$ is a bijection, so
 $|\sigma r\cap \sigma x.\mathrm{support}|=|r\cap x.\mathrm{support}|$;
 parity is preserved for every transported opposite-sector row.
 4. Independence:
 $\neg\operatorname{inSpanRows}(S.Q,\mathit{sectorRows}(S,\tau),
 \operatorname{rowVector}(S.Q,\langle\operatorname{mint}(\mathsf{used}),\tau,r\rangle))$.
 Coordinate permutation $\sigma$ preserves span membership, and
 $\operatorname{mint}(\mathsf{used})$ is unchanged because $\sigma$ does not
 touch $\mathsf{used}$ (identifiers are not qubit labels), so the minted
 identifier agrees on both sides.
 Conclusion: $\operatorname{addState}(S,\tau,r)$ appends a row with id
 $\operatorname{mint}(\mathsf{used})$, sector $\tau$, support $r$, and updates
 $\mathsf{used}$. Transporting gives $\operatorname{addState}(\tilde S,\tau,
 \sigma r)$ with the same minted id and $\mathsf{used}$, so
 $\widetilde{S'}=\operatorname{addState}(\tilde S,\tau,\sigma r)$.
 Hence $\operatorname{Eval}(\operatorname{addStab}_{r:\tau},S,S')$ iff
 $\operatorname{Eval}(\operatorname{addStab}_{\sigma r:\tau},\tilde S,\widetilde{S'})$.
 The transported command **must** be used: with the same command
 $\operatorname{addStab}_{r:\tau}$ on both sides the congruence fails for
 additions, as the witness shows (swap of qubits 1 and 2 makes an
 $X$-addition applicable on $S$ but not on $\sigma S$ because the
 commutation parity changes). $\square$ for addition.

- **`C-SEQUENCE`.** By induction on the two sub-derivations: if
 $\operatorname{Eval}(m_1,S,S_1)$ iff
 $\operatorname{Eval}(\sigma m_1,\tilde S,\widetilde{S_1})$ and
 $\operatorname{Eval}(m_2,S_1,S')$ iff
 $\operatorname{Eval}(\sigma m_2,\widetilde{S_1},\widetilde{S'})$, then
 $\operatorname{Eval}(m_1;m_2,S,S')$ iff
 $\operatorname{Eval}(\sigma m_1;\sigma m_2,\tilde S,\widetilde{S'})$.
 $\square$ for sequences.

- **`E-GRAFT` (extension).** The graft is not in the MVP kernel statement's
 scope, but the same transported-command pattern applies: the grafted qubit
 transports to $\sigma q$; touching rows transport bijectively; the chain
 order is preserved up to the bijection on identifiers; coverage, sortedness
 of minted supports, and $\mathsf{stateK}$ preservation are all invariant
 under coordinate permutation $\sigma$ (bitmask rank is invariant under
 column permutation) and under identifier-stable minting ($\mathsf{used}$
 unchanged). Hence the graft clause transports with command
 $\operatorname{graft}_{\sigma q,\tau,\sigma(\vec r)}$. $\square$ for graft.

**Expression congruence (scoped).** For $\oplus$, the congruence holds for
relabelings applied uniformly to the whole sum: a global bijection preserves
disjointness as above, and $\mathsf{used}$-disjointness is label-invariant.
Per-summand relabelings are covered by composing with the summand's embedding
into the sum. Relabelings that cut across a summand boundary are outside the
congruence's scope; this scoping is part of the disposition and is not a
gap to be closed by a later rule.

**`P-REBASE`.** Deferred in the MVP: its clause cannot be exercised until
support-sensitive applicability is formalized, so it contributes no case to
the induction above. This is a position, not an omission.

**Conclusion.** The transported-command congruence holds for the MVP kernel
(skip, direct sum, delete, add, sequence) and extends to the in-scope graft
by the same argument. Same-command congruence is false for additions; the
counterexample is the motivation for the transported form and is not
repaired by any rule in the kernel. $\square$

## 4.26 — `P-REBASE` presentation identity and `OBL-REBASE-GENERATION`

 Evidence, not a
machine-checked proof; re-derivation target is the / slices.

**Set-up.** In a well-formed presented CSS state the displayed $\tau$-rows of a
sector $V_\tau=(v_1,\ldots,v_m)$ are independent (I2) and span the sector's
row space (reading (A) of : $X=\langle \mathit{rows}_X\rangle$ by
construction). The command $\operatorname{rebase}_{\tau;M}$ names a matrix
$M\in\mathbb{F}_2^{m\times m}$; the registered output replaces each $v_i$ by
$v_i'=\bigoplus_j M_{ij}v_j$ with canonical mint identifiers. (Sterile technicality:
a nonempty display is presupposed by the $m\times m$ shape; the empty sector
($m=0$) has no rebase command — there is nothing to rebase, and the move is
inapplicable.)

**Ambient membership (W22).** The output rows are $\mathbb{F}_2$-combinations
(symmetric differences) of the input sector's displayed supports, so each new
support is a subset of $Q$; the qubit namespace $Q$ is unchanged. No row leaves
the ambient space $\mathbb{F}_2^Q$. A constructed row that did would be
malformed at the encoding, not a no-derivation.

**Row space.** $\langle v_1',\ldots,v_m'\rangle = \langle V_\tau M\rangle =
\langle V_\tau\rangle$ because the columns of $M$ span
$\mathbb{F}_2^m$ (M invertible): every $v_i' = V_\tau M_i$ with $M$'s rows
spanning — so the matrix of row combinations has full column rank, and the
combination map $\mathbb{F}_2^m \to \langle V_\tau\rangle$,
$c \mapsto \bigoplus_j c_j v_j$ is a bijection (I2 independence: only
$c=0$ gives the zero vector). Hence the *span* of $\{v_i'\}$ equals the span
of $\{V_\tau M\} = $ span of $\{V_\tau M c: c \in \mathbb{F}_2^m\}$, and
$\{V_\tau c\} = \{c' \in \langle V_\tau\rangle\}$ exhausts $\langle
V_\tau\rangle$ exactly — so span$(v_i') = $ span$(v_i)$. ∎

**Output I1.** The opposite sector's row space is untouched, and each new
$X$-candidate's *subspace* is the same old $X$-span: mutual orthogonality
depends only on the two row spaces, so $X'\perp Z'$ iff $X\perp Z$ ⟸ I1 of
the input. ∎

**Output I2 (independence).** The $v_i'$ are exactly $V_\tau M$; they are
independent iff $M$ is invertible on $\mathbb{F}_2^m$-column space over I2-independence
— $\bigoplus c_i v_i' = V_\tau (M^{\intercal} c)$-combination is $0$ iff
$M^{\intercal}c = 0$ iff $c = 0$. ∎ (So the applicability premise "$M$ is
invertible over $\mathbb{F}_2$" — GL($m$,$2$)-ness — is exactly what makes
the output display register; a singular M has no derivation.)

**Semantic identity.** The spans are unchanged in both sectors and $Q$ is
unchanged, so every property computed from the spans and $Q$ alone is
carried **exactly**: $n'=n$, $k'=k$, $d_\sigma' = d_\sigma$ for both sectors,
$d'=d$, with the $+\infty$ convention respected. Supplied lower-bound
endpoints and witnesses remain valid *for the same spans*: the consumer
carries them unchanged (no revalidation needed — the validated fact is
unchanged), though a revalidation must also pass, trivially. Display-relative
properties — $w$, the Tanner connectivity of the displayed rows, and the
interaction radius relative to a layout — are **not** span facts: they change
and are recomputed exactly over the child display.

**Support shape.** The columns of $M$ are ordered by ascending identifier
rank of the sector\u2019s displayed rows; the consumer sorts the displayed rows by
identifier rank before applying $M$, so the result does not depend on storage
order. Each new support is a binary sum of old supports; it is recorded
sorted (the display contract; the consumer sorts — no order claim is made by
the sort). Fresh identifiers come from the canonical mint over
$\mathsf{used}$; the replaced rows are retired into $\mathsf{used}\setminus\mathsf{live}$;
`used` strictly grows
by the minted identifiers.

**`OBL-REBASE-GENERATION` — discharge.** 

- *Conjunct 1* is proved at §4.18 (the `C-DELETE-CHECK`/`C-ADD-CHECK`
 loop generates $\mathrm{GL}(m,2)$ of a fixed row space, up to canonical
 identifier allocation and `used`-set growth, classical citation recorded
 there).
- *Conjunct 2* became stateable on 2026-10-23, when the Gate 6 decision
 admitted `P-REBASE` as a conditional cell and the §2 transition fixed its
 transformation set. With the transition defined as the
 $\mathrm{GL}(m,2)$ action on the display of each sector — the output rows
 are $V_\tau M$ for $M \in \mathrm{GL}(m,2)$, exactly — the transformation
 set of the move is **by definition** the basis-change group
 $\mathrm{GL}(m,2)$ per sector, up to row-identifier conventions (the child
 rows carry mint identifiers, so the identification is modulo the
 identifier-visibility reading, not an identity of labeled rows). Reading
 the two conjuncts together: the loop (§4.16/§4.18) and the admitted
 `rebase` command have the same transformation set,
 $\mathrm{GL}(m,2)$ per sector, modulo mint conventions. The conjunction is
 the obligation's stated conclusion. ∎

**Not claimed.** The obligation's discharge is a set identification modulo
minting, not any claim that sequences of core moves *can be shortcut* by one
`rebase` command with identical labeled states — the two procedures emit
different identifiers on distinct paths (their outputs are not $\equiv$), and
factorization of a *semantically labeled* derivation is what
`OBL-DERIVED-TERM-FACTORIZATION` rules for, satisfied by nothing here: no
`rebase`-vs-loop equivalence at the labeled-state level is claimed or implied.
Support-sensitive predicates stay `not yet defined` (future-$\Pi$); the
display-relative recomputations above are not support-sensitive-Pi claims.

## 4.27 — `E-LOCAL-HADAMARD` ($T=Q$): the sector-exchange instance

 Evidence, not a
machine-checked proof.

**Set-up.** The registered output swaps the sector of every displayed row:
$X' $-display $=$ old $Z$-display, $Z'$-display $=$ old $X$-display;
supports, ids, `used`, $Q$ unchanged.

**Ambient membership (W22).** Supports, identifiers, `used`, and $Q$ are
unchanged by the sector exchange, so every displayed row remains a subset of
$Q$; the ambient space $\mathbb{F}_2^Q$ is unchanged. No row leaves it.

**Output I1.** Orthogonality of the two sectors is the condition "every
$X$-$Z$ support-pair intersects evenly", which is *symmetric under the
exchange of the two row spaces*: $\{x\perp z\ \\ x\in X\text{-span},z\in
Z\text{-span}\}$ re-read with the sectors swapped is the same set of parity
facts. The parent satisfies it (I1), so the child does. ∎

**Output I2.** Same-sector independence is sector-blind for the same reason:
the family of row masks is unchanged setwise; only its sector labels moved.
Independence was checked inside the family, so it holds inside the swapped
labels. ∎

**Ranks and $k$.** Rank counts are label-blind: $\mathrm{rank}(X') =
\mathrm{rank}(\text{old } Z\text{-display})$, and I2 makes each count equal
its display size; so rank$_{X'}=$ rank$_{Z\text{ (old)}}$, rank$_{Z'} =$
rank$_{X\text{ (old)}}$, $k' = n - \text{both} = k$. $n'=n$. $w' = w$ (a
row's support size is sector-blind). ∎

**Distances.** By definition (spec: `CLAIMS.md` §6) $d_\sigma(C)$ reads the
$Z$-orthogonal-complement-minus-$X$-span minimum (for $\sigma = X$). Under
the exchange: $d_X(C') = \min \mathrm{wt}(Z'^{\perp}\setminus X') =
\min\mathrm{wt}(X^{\perp}\setminus Z) = d_Z(C)$ (the $+\infty$ convention
respected: an empty sector stays empty after the exchange), and
symmetrically $d_Z(C')=d_X(C)$. $d'=\min(d_X',d_Z')=\min(d_X,d_Z)=d$. ∎

**Ledger transport (mechanical).** The consumer swaps the two sector intervals
— both endpoints — and swaps each witness's side, *then revalidates against
the child* (an old sector-$\sigma$ witness of support $s$: in the child it is
checked as a sector-$\bar\sigma$ witness; the check commutation side and the
span side are the old opposite/old same sectors, so every parent-valid
witness revalidates; the revalidation is recorded, not assumed). The full
interval keeps both endpoints.

**Not claimed.** The term-$\operatorname{hadamard}_T$ general instance
($\varnothing \subsetneq T \subsetneq Q$) — §2.12's record splits along both
row spaces under the dispositioned condition — is **not** admitted here: a
row $v$ with $v\cap T \ne \varnothing$ and $v\setminus T \ne \varnothing$
conjugates under $H_T$ to a mixed $X/Z$ operator, whose pure-sector
re-presentation needs a rebasing argument the phase-insensitive row-swap does
not carry. Only the $T=Q$ instance is specified; a later revision may state
the subset mechanics explicitly. The $T=\varnothing$ instance needs no
derivation of this kind: it is the identity on both state and ledger, so it is
stated as such at `TERM_LANGUAGE.md` §2 and is not re-derived here. The move is
not a presentation identity (the
group changes; the sector distances exchange — that is the point of the
move).

## 4.28 — `E-PEEL`: applicability well-formedness and the exact rank bookkeeping

 Evidence, not a
machine-checked proof.

**Set-up.** $q \in Q$, $r$ displayed of sector $\tau$ with
$q \in \mathsf{supp}(r)$, and $r$ is the **unique** displayed $\tau$-row
containing $q$. The output is $Q' = Q \setminus\{q\}$; $r$'s row removed
(retired; identifier stays in `used`); every surviving opposite-sector row
keeps its identifier and sector and drops $q$ from its support; selected-sector
rows (all $q$-free by uniqueness) are untouched.

**Ambient membership (W22).** The output namespace is $Q'=Q\setminus\{q\}$.
Surviving selected-sector rows are $q$-free (uniqueness of $r$), so their
supports lie in $Q'$; every surviving opposite-sector row has $q$ removed from
its support; the removed row $r$ is retired. No row leaves
$\mathbb{F}_2^{Q'}$. A constructed row that did would be malformed at the
encoding.

**I2 of the opposite sector is automatic — the injectivity argument.** Let
$\mathcal{R}_q:\mathbb{F}_2^Q\to\mathbb{F}_2^{Q'}$ be the coordinate
restriction and $\sigma$ the opposite sector. First, no surviving
$\sigma$-row has support exactly $\{q\}$: I1 of the parent (vs $r$, which
contains $q$) gives $|s\cap r|$ even for every displayed $\sigma$-row $s$, so
a row $s$ with $\mathsf{supp}(s)=\{q\}$ would meet $r$ exactly in
$q$ — an odd overlap — and is excluded on the parent side. Second, every
displayed $\sigma$-row is $r$-even, so $\sigma$'s display — and with it, by
 reading (A), its entire row space $\sigma$-span — lies inside the
**$r$-even hyperplane**
$\{v: v\cap r \text{ even}\}\subseteq\mathbb{F}_2^Q$. Every vector of that
hyperplane meets $r$ evenly; in particular it cannot be $e_q$
($\{q\}\subseteq r$, so $e_q\cap r = 1$, odd). Hence
$\ker\mathcal{R}_q\cap\sigma\text{-span} =
\{v\in\sigma\text{-span}: \mathrm{supp}(v) \subseteq \{q\}\} = \{0\}$:
$\mathcal{R}_q$ is **injective on the $\sigma$-span**. Consequences:
(i) $\dim\sigma' = \dim\sigma$ exactly (the restricted span's dimension is
carried); (ii) the restricted display is independent (a vanishing combination
of restricted rows is the restriction of a vanishing combination of the
display rows, which I2 forbids); (iii) no restricted row is the zero vector
(a zero restriction would put the row's support inside $\{q\}$, excluded
above). The child's opposite-sector display registers under I2 on its own. ∎

*(History, kept per `AGENTS.md`: an earlier draft of this derivation described
a pair of opposite-sector rows differing exactly at $q$ as a possible I2
failure. Such a pair cannot occur under a well-formed parent: their sum would
be $e_q$, and (i)–(iii) exclude $e_q$ from the $\sigma$-span. The earlier
"boundary regime" alternative for $k'$ under this entry is withdrawn with the
same stroke.)*

**I1 is automatic.** A restricted pair-overlap's parity is the pair's
overlap parity minus its shared-$q$ contribution. A shared-$q$ contribution
needs a surviving row of *each* sector containing $q$. Surviving
selected-sector rows are $q$-free (uniqueness of $r$), so the term vanishes
for every pair; restricted parity $=$ parent parity; the parent satisfies
I1. ∎

**Selected-sector I2 is automatic.** Its display is unchanged, and a
sub-display of an independent display is independent. ∎

**Ranks.** $\dim\tau' = m_\tau - 1$ exactly: the deleted $r$ is displayed and
independent of its peers (I2), and the surviving $\tau$-display's span — all
its rows $q$-free, so $\mathcal{R}_q$ acts on them as the identity — is
simply that sub-span. $\dim\sigma' = \dim\sigma$ exactly (the injectivity
argument). So
$$k' = (n-1) - (\dim\tau - 1) - \dim\sigma = k,$$
exactly: the peel neither creates nor destroys logical dimension, and the
namespace removal is fully accounted for by the removed row's sector. ∎

**Distances: the two sector directions, and the refusal by design
(corrected 2026-10-29).** Write $S_\tau$ and $S_\sigma$ for the
parent's sector row spaces and $S'_\tau$ and $S'_\sigma$ for the child's,
with $\sigma$ the opposite sector as above. The peel is the $m=1$ instance of
the graft update of §2 without the graft's coverage and opposite-sector
guards, and §4.13's two sector arguments go through for it unchanged, using
only the uniqueness of $r$. (When $k=0$ both sides have no logicals and both
distances are $+\infty$; since $k'=k$, the child has logicals exactly when
the parent does, and the two inequalities below are about nonempty minima.)

- *Selected sector: $d_\tau(C')\ge d_\tau(C)$.* Let $v'$ be a child
 $\tau$-logical, so $v'\in (S'_\sigma)^\perp\setminus S'_\tau$, and let $v$
 be $v'$ padded with $0$ at $q$. Each parent $\sigma$-row agrees with its
 restriction off $q$, and $v_q=0$, so $v\perp S_\sigma$. If $v\in S_\tau$,
 write $v=c\,r+\sum_u c_u u$ over the $q$-free $\tau$-rows $u$; coordinate
 $q$ forces $c=0$, so $v'=\sum_u c_u u\in S'_\tau$, a contradiction. Hence
 $v$ is a parent $\tau$-logical of the same weight as $v'$.
- *Opposite sector: $d_\sigma(C')\le d_\sigma(C)$.* Let $u$ be a parent
 $\sigma$-logical, so $u\in S_\tau^\perp\setminus S_\sigma$, and let
 $u'=\mathcal{R}_q u$. The child's $\tau$-rows are the $q$-free parent
 $\tau$-rows, so $u'\perp S'_\tau$. If $u'\in S'_\sigma$, lift the
 combination to $Q$: $\tilde u=u+\sum_s c_s s$ over parent $\sigma$-rows
 $s$ has support inside $\{q\}$, lies in $S_\tau^\perp$ (I1), and is
 nonzero because $u\notin S_\sigma$, so $\tilde u=e_q$; but $e_q\cdot r=1$,
 contradicting $\tilde u\perp r$. Hence $u'$ is a child $\sigma$-logical of
 weight at most $\mathrm{wt}(u)$.

The restriction can collapse a parent $\tau$-logical supported on $\{q\}$
alone to the zero vector (then $d_\tau(C)=1$), and a child $\sigma$-logical
can be lighter than every parent $\sigma$-logical; both are consistent with
the inequalities. The full distance $d'=\min(d_X',d_Z')$ is bounded in
neither direction. Witness (three qubits): $Q=\{0,1,2\}$ with $X$ display
$\{0,1\}$ and $Z$ display $\{0,1,2\}$; peeling $q=2$ in sector $Z$ takes
$(d_X,d_Z)$ from $(2,1)$ to $(1,2)$, with the full distance $1$ before and
after. Before 2026-10-29 this section read that witness as refuting every
carried endpoint; it refutes the exact carry and the full-distance bounds
only.

The consumer's ledger rule is nonetheless the full reset with child-valid
witnesses only (`JUDGMENT_LAYER.md` §2b): a refusal by design, recorded as
such. The two inequalities would license carrying the selected sector's
lower endpoint and the opposite sector's upper endpoint; no cell doing so is
admitted. The priced cells of §4.13 are not affected; no price cell is
admitted for this move. The two directions are checked on random peels by
`PeelSectorMonotonicity` in an archived internal note and by
`test_rg11_hand_derivation_counterexamples_glue_and_peel` in
an archived internal note (empirical aids; they falsify nothing
here and prove nothing).

The regression fixture for the collapse of a parent logical supported on the
removed qubit alone is in `machine/test_priced_calculus.py` (the `E-PUNCTURE`
unnamed-qubit case) — and
there is **no** fixture for the priced hole-punch cell.

## 4.29 — `E-PUNCTURE`: applicability well-formedness under the check-puncturing update

 Evidence, not a
machine-checked proof.

**Set-up.** $q \in Q$; the output deletes $q$ and every displayed row of
either sector whose support contains $q$. Surviving rows (both sectors) are
$q$-free.

**Ambient membership (W22).** The output namespace is $Q'=Q\setminus\{q\}$.
Every surviving row of either sector is $q$-free by construction (only rows
containing $q$ were deleted), so its support lies in $Q'$. No row leaves
$\mathbb{F}_2^{Q'}$.

**I1 is automatic.** Both sectors of every surviving pair are $q$-free, so
the restricted overlap is the parent's overlap minus its shared-$q$
contribution — which is $0$ because no surviving row contains $q$. Restricted
parity $=$ parent parity; the parent satisfies I1. ∎

**Each sector's I2 is automatic.** Surviving rows of a sector form a subset
of the parent's display of that sector, all $q$-free. I2's span test is
ambient-independent (each participant's mask is unchanged by restriction —
they are the same vectors): a combination over the survivors vanishing
over $\mathbb{F}_2^{Q'}$ vanishes over the parent ambient too, contradicting
I2 of the parent. ∎ (Its corollary: a row whose support became empty cannot
survive — only rows *containing* $q$ were deleted, so a survivor's support is
a nonempty subset of $Q'$.)

**Structural effects.** $n' = n - 1$ exactly. Let $t_X$ and $t_Z$ be the
numbers of deleted displayed rows in sectors $X$ and $Z$. Under I2 the
display is a basis of its span, so removing the $t_\tau$ rows that contain
$q$ lowers that sector's rank by exactly $t_\tau$; hence
$k' = k - 1 + t_X + t_Z$ exactly. (Not fixed by $n$ alone, but fixed by
the display.)

**Distances — the same honest refusal.** No surviving row of either sector
contains $q$, and the coordinate restriction has no universal direction:
puncturing the *unnamed* free qubit $2$ of $Q=\{0,1,2\}$ with the single
$Z$ display $\{0,1\}$ raises the $X$ distance from $1$ to $2$ (the deleted
qubit's own free direction **was** the parent's lightest `X` logical, and its
restriction collapses to the zero vector). That instance is a special case,
not a universal refutation: it shows that for that qubit the $X$-sector
distance can rise, while other deletions may leave a sector's distance
unchanged or move it in either direction, depending on the deleted qubit and
the induced stabilizer update. Hence no single `≤`- or `≥`-claim holds for all
punctures, and no carried endpoint is derivable for either sector or the full
distance. Beyond this absence of a universal rule nothing licenses a rule:
exact post-puncture values are deliberately underivable in this scope, the
consumer's ledger rule is a full reset with child-valid witnesses only
(`JUDGMENT_LAYER.md` §2b), and distance *prices* for this move are
deliberately **not** admitted — hole-punch pricing is blocked on the D2
lower-bound question tracked by (no price cell and no fixture for
it enters until that lower bound lands). The regression fixture for the
unnamed-qubit increase is in `machine/test_priced_calculus.py`.

## 4.30 — `E-EXTEND`: applicability, canonical mint, and the $k$ formula

 Evidence, not a
machine-checked proof.

**Set-up.** $\Delta \cap Q = \varnothing$; additions typed
$(\tau_i, \mathrm{supp}(u_i))$, $\mathrm{supp}(u_i) \subseteq Q\cup\Delta$,
no repeated entries, sorted. Each $u_i$ is checked at its own list position:
(i) $u_i \notin$ span of the rows displayed so far in sector $\tau_i$
*(computed inside* $\mathbb{F}_2^{Q\cup\Delta}$ — the ambient is the *new*
namespace, the complement reading of `W22`); (ii) $u_i \perp$ every row
displayed so far of the opposite sector; (iii) the addition's support is
nonempty (its mask is nonzero — an empty support is the zero vector, which
lies in every span and fails (i) outright).

**Ambient membership (W22).** The ambient grows to $Q\cup\Delta$ *before*
the first addition, and every added support is checked to be a subset of
$Q\cup\Delta$ (the $W22$ reading); surviving and minted rows all have
support in $Q\cup\Delta$. The complement reading of `W22` is stated
explicitly here: complements are taken inside $\mathbb{F}_2^{Q\cup\Delta}$.

**Output I1–I5.** Cumulative: §4.7's $\operatorname{addStab}$ instance —
applied at each addition's step against the intermediate state's display —
gives I1–I5 for each intermediate state. The intermediate states here differ
from the §4.7 case only in that the ambient grew *before* the first addition;
that ambient change carries no well-formedness content of its own (the
$\Delta$-qubits are named by no displayed row yet), so the §4.7 derivation's
steps apply verbatim with $Q\cup\Delta$ in the ambient position. ∎
(Canonical mint (I3): the row identifiers are minted sequentially over
$\mathsf{used}$ as in §4.7's instance; no fresh-name choice.)

**$n$ and $k$.** $n' = n + |\Delta|$ (namespace addition). Each addition is
independent of the cumulative same-sector span by premise (i), so its sector's
rank rises by exactly $1$ per addition: $\text{rank}_\tau' = \text{rank}_\tau + s_\tau$ ($s_\tau$ = number of sector-$\tau$ additions). Then
$$k' = (n+|\Delta|) - (\text{rank}_X + s_X) - (\text{rank}_Z + s_Z) =
k + |\Delta| - s_X - s_Z,$$
exactly. ∎ (The formula is *the child's* $k$, not a separate invariant.)

**Distances.** With $\Delta = \varnothing$ the move is a
$C$-$\operatorname{ADD}$-$\operatorname{CHECK}$ sequence in the ambient the
§4.3 monotonicity is stated over: every sector carries its lower endpoint
(distance cannot decrease under an added check) and rebuilds its upper
endpoint from child-valid witnesses only. The pre-change upper endpoint is
not a sound bound for the child, because adding a check can raise a
distance; the untouched opposite sector's spanning set and namespace are
unchanged but its upper endpoint is likewise stale. With
$\Delta \ne \varnothing$ **no** distance rule is derivable and none is
admitted: the logical vectors range over $\mathbb{F}_2^{Q\cup\Delta}$, and
the parent's $d_\sigma$ (over $\mathbb{F}_2^Q$) neither upper- nor
lower-bounds the child's in general — lower endpoints reset to $0$; upper
endpoints are supplied only by witnesses that revalidate in the child (the
ambiguity the §2.9 record's "no generic $k$ or distance formula" rows
correctly refuse to admit a formula for).

**Not claimed.** No support-sensitive predicate or logical-witness field is
read; no boundary-label data enters (the $\Delta$ qubits are unlabeled); the
move does not read or produce an abstract *patch* structure beyond its rows.


## 4.31 (EDITED) — `E-GLUE`: applicability and state update (`OBL-GATE6-CSS-EXTENSIONS`)

 Evidence,
not a machine-checked proof.

**Applicability.** Two presented CSS states $(C_A,\Pi_A)$ and $(C_B,\Pi_B)$
with disjoint qubit namespaces $Q_A \cap Q_B = \varnothing$ and disjoint used
sets $\mathsf{used}_A \cap \mathsf{used}_B = \varnothing$. The seam checks
supplied (by the consumer, through the §2e seam certificate or directly) are
typed $(\tau, \mathrm{supp})$ with $\tau\in\{X,Z\}$, $\mathrm{supp}\subseteq
Q_A\cup Q_B$, nonempty, non-repeating. Each seam check must commute with every
displayed row of the opposite sector (independence) and must not lie in the
span of the displayed rows of its own sector (independence of the seam from the
factor codes).

In addition, the seam checks must be well-formed as a CSS display **jointly
with the factor rows**, not merely among themselves: every X seam check must
commute with every Z row of both factors and every Z seam check (I1), and the
combined set of factor rows plus seam checks of each sector must be
independent in that sector (I2). Equivalently, in the order supplied, each
seam check must commute with all factor rows of the opposite sector and all
previously admitted seam checks of the opposite sector, and must not lie in
the span of the factor rows of its own sector together with the previously
admitted seam checks of its own sector. This joint premise is not implied by
the seam-vs-factor checks above: two seam checks of the same sector can be
independent of each other and of the factor rows individually yet dependent in
combination (e.g. $s_1=f+v$, $s_2=v$ with $f$ a factor row and $v$ outside
its span), and two seam checks of opposite sectors can fail to commute without
any factor row being involved. Pairwise admissibility among the seam checks
alone is insufficient.

**State update.** The child's qubit set is $Q_A\cup Q_B$; its displayed rows
are the factor rows followed by one minted row per admissible seam check,
with identifiers minted canonically over $\mathsf{used}_A\cup\mathsf{used}_B$;
its used set is that union together with the minted seam identifiers. The seam
checks are the only new rows; no factor row
is removed or altered. Well-formedness (I1–I5) is preserved by the same
arguments as `C-DIRECT-SUM` plus the independence premises above (each new row
is independent and commutes with the opposite sector by construction).

**Ambient membership (W22).** The child's qubit set is $Q_A\cup Q_B$.
Factor rows retain their supports in $Q_A$ or $Q_B$ (hence in the union), and
every seam check is typed with $\mathrm{supp}\subseteq Q_A\cup Q_B$ and
rejected otherwise (no-derivation at the term level, malformed at the encoding
for a state carrying such a row). No row leaves $\mathbb{F}_2^{Q_A\cup Q_B}$.

**Distances.** No distance relation is admitted beyond the §2e conditional
cell: the §2f cell's carries-when hypothesis (the seam certificate) is the
only license, and the logical-witness prerequisite (`TAXONOMY.md` §2.10)
remains `not-yet-defined`. Lower endpoints are sound without a certificate,
by the following repair. First, for the direct sum,
$d(A\oplus B)=\min(d_A,d_B)$ in every sector and for the full distance
(*Direct-sum parameters and distances*, §4). Second, each admitted seam check
is an added CSS check, and *Distance monotonicity under addition* (§4) gives
that adding a check cannot lower a distance; applied per sector, each glued
sector distance is therefore at least $\min(d_A,d_B)$, and the full distance
is at least $\min(d_A,d_B)$. The same argument applies per sector. The
Z-sector equality $d_Z(Q)=\min(d_A,d_B)$ is **not** a theorem of this
section and is not admitted as a rule; it remains the hypothesis of the
`E-GLUE` conditional cell of `JUDGMENT_LAYER.md` §2e/§2f, underwritten for
that cell by the seam certificate's Theorem 4 / claim 7.4
(`composition-distance`). The lower-endpoint half (each glued distance is at
least the minimum of the factor distances) is covered by this section and
§4.31; the equality half is not. The scalar relation $d=\min(d_A,d_B)$ is
likewise **not** admitted (obstruction, an archived internal note). Upper
endpoints come only from witnesses that revalidate in the child.

**What this does not settle.** The logical-witness field
(`TAXONOMY.md` §2.10). Composition-distance exactness (Theorem 4 / claim 7.4
of *composition-distance*) is not settled as a theorem here: it remains a
hypothesis of the `E-GLUE` conditional cell (see *Distances* above), not a
carved-out obligation. Sound admission for `E-GLUE` is discharged under the stated hypotheses
(§4.32); the logical-witness prerequisite (`TAXONOMY.md` §2.10) and the
equality hypothesis (Theorem 4 / claim 7.4) remain open and are not settled
by this section, which defines the transition's state update only. ∎

## 4.32 — Soundness of the Gate 6 interval transformers (`OBL-GATE6-CSS-EXTENSIONS`)

 Evidence, not a machine-checked proof; the
interval bookkeeping is the same as §4.13, and the distance relations are
those of §4.26–§4.31. Under the §4.13 hypotheses (every input interval
contains the corresponding exact distance; every supplied price, lower bound,
strict-improvement enumeration, and witness is true) we show that each Gate 6
interval transformer of `JUDGMENT_LAYER.md` §2b/§2e is sound and monotone in
the sense of §8.4. The refusals of §4.27–§4.29 are not gaps: a reset to the
full interval is a sound, monotone transformer. For `E-PUNCTURE` and for
`E-EXTEND` with $\Delta\neq\varnothing$ no carried endpoint is derivable
(§4.29, §4.30); for `E-PEEL` the two sector directions are derivable (§4.28)
and the reset is a refusal by design.

Let $F_m$ be the transformer named in §2b/§2e for move $m$.

- **`P-REBASE`.** $F$ is the identity on every interval. Soundness:
 §4.26 gives $n'=n$, $k'=k$, $d_\sigma'=d_\sigma$, $d'=d$, so the
 contained exact distance is unchanged and the unchanged interval still
 contains it. Monotonicity: identity is monotone (§9.4). ∎

- **`E-LOCAL-HADAMARD` ($T=Q$).** $F$ swaps the two sector intervals and
 keeps the full-distance interval. Soundness: §4.27 gives
 $d_X'=d_Z$, $d_Z'=d_X$, $d'=d$; swapping intervals maps a contained
 $d_X$ to a contained $d_Z'$ and vice versa, and the full interval is
 unchanged. Monotonicity: the swap is order-preserving in $\sqsubseteq$
 (§9.4). ∎

- **`E-PEEL`.** $F$ resets every lower endpoint to $0$ and takes every
 upper endpoint from witnesses valid in the child. Soundness: the reset
 lower bound $0$ is below every distance in $D$, and a witness valid in the
 child is an upper bound for the child's distance by the witness-validation
 rule, so containment holds however the coordinate restriction moves the
 distance. Monotonicity: the constant lower
 reset is monotone and the witness-set upper rule depends on the child, not
 on the input interval (§9.4). ∎
 §4.28 derives $d_\tau'\ge d_\tau$ and $d_{\bar\tau}'\le d_{\bar\tau}$, so
 carrying the selected sector's lower endpoint and the opposite sector's
 upper endpoint would also be sound; neither carry is admitted (the §2b row
 records the reset as a refusal by design), and the reset is the transformer
 this section certifies.

- **`E-PUNCTURE`.** $F$ resets every lower endpoint to $0$ and takes every
 upper endpoint from witnesses valid in the child. Soundness and
 monotonicity are the same as for the peel, using §4.29's refutation
 (the unnamed-qubit increase $d_X\;1\!\to\!2$). ∎

- **`E-EXTEND`.** With $\Delta=\varnothing$, $F$ carries each lower
 endpoint and rebuilds each upper endpoint from child-valid witnesses only.
 Soundness: with $\Delta=\varnothing$ the move is a `C-ADD-CHECK` sequence
 over the ambient code (§4.30), so adding a check cannot decrease a
 distance and the lower endpoint carries; the pre-change upper endpoint is
 not a sound bound, so it is rebuilt from witnesses valid in the child.
 With $\Delta\neq\varnothing$, $F$ resets every lower endpoint to $0$ and
 takes upper endpoints only from witnesses revalidating in the child;
 soundness holds because §4.30 gives no bound in that case and the reset
 interval contains every distance. Monotonicity: lower carry and the
 witness-based upper rule are monotone in $\sqsubseteq$ (§9.4). ∎

- **`E-GLUE`.** $F$ takes, in every sector and the full distance, the
 lower endpoint to be the minimum of the two factor ledgers' lower
 endpoints, and takes the Z-sector upper endpoint to be the minimum of the
 two factors' Z upper endpoints under an admissible seam certificate
 (§2e); the X and full upper endpoints are left to witnesses valid in the
 child. Soundness: the glued code is $C_A\oplus C_B$ with the seam checks
 added (§4.30). Write $L_A^\sigma$ and $L_B^\sigma$ for the factor ledgers'
 lower endpoints in sector $\sigma$, and $L_A$ and $L_B$ for their
 full-distance lower endpoints. In each sector,
 $d_\sigma(C_A\oplus C_B)=\min(d_\sigma(C_A),d_\sigma(C_B))$ (*Direct-sum
 parameters and distances*, §4) and adding a check never lowers a distance
 (*Distance monotonicity under addition*, §4), so
 $d_\sigma(\mathrm{glued})\ge\min(d_\sigma(C_A),d_\sigma(C_B))\ge
 \min(L_A^\sigma,L_B^\sigma)$; the same two steps give
 $d(\mathrm{glued})\ge\min(d(C_A),d(C_B))\ge\min(L_A,L_B)$ for the full
 distance. The stronger step $d_{\mathrm{glued}}\ge d_A,d_B$, which this
 bullet stated before 2026-10-29, is false: with no seam checks the glued
 code is the direct sum, whose distance is the factor minimum (a free qubit,
 $d=1$, and the $[[4,2,2]]$ code give $d=1<2$; reproducer
 `Section431GlueStep` in an archived internal note). Under an
 admissible certificate §2e certifies $d_Z(Q)=\min(d_A,d_B)$, and
 $\min(U_A^Z,U_B^Z)$ is an upper bound for that minimum. The X and full
 upper endpoints are justified by witnesses valid in the child.
 Monotonicity: the two minima are monotone in their inputs and the
 witness-based upper rule is monotone (§9.4). The equality
 $d_Z(Q)=\min(d_A,d_B)$ remains a hypothesis of the conditional cell
 (Theorem 4 / claim 7.4 of *composition-distance*), not a theorem of this
 section. ∎

By §8.5, any finite sequence of these transformers is sound whenever each
step's transformer is. Hence `OBL-GATE6-CSS-EXTENSIONS` is discharged: every
admitted Gate 6 cell has a typed transition (§4.26–§4.31), applicability
conditions, exact state/context update, and a sound, monotone interval
transformer under its stated hypotheses. The cells remain conditional on
their hypotheses (the seam certificate and Theorem 4 / claim 7.4 for
`E-GLUE`'s equality; checked structural premises for `P-REBASE` and
`E-LOCAL-HADAMARD`'s $T=Q$ instance); discharge is not promotion, and
`promoted` remains a review disposition. ∎

## 5. What the semantics deliberately does not do

- **It does not compute distance.** The transition relation has no exact-distance
 search. Unpriced exact post-deletion values are **`unavailable`**; exact
 post-addition values remain `open` except for the conditional strict
 improvement cell. See [`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md).
- **It does not exhibit a residual.** An inapplicable command has no derivation;
 the semantics is big-step, so nothing says *where* a sequence got stuck.
- **It does not read `steps`.** No premise and no judgment consults provenance.
- **It does not quotient by presentation.** `P-RELABEL` is a congruence to be
 *proved* (`OBL-PRESENTATION-CONJUGATION`), not a built-in equality.

## 6. What this document does not claim

**It does not claim the semantics is mechanized.** The hand derivations in §4
are evidence in this repository, not kernel-checked results. A Lean development
exists under `lean/`; what it covers and the trust basis it rests on are
recorded once, at [`../lean/README.md`](../lean/README.md), with
per-obligation progress under each obligation's *Intended mechanization
status* in `spec/OBLIGATIONS.md`. What is mechanized there does not verify
these hand derivations in full, and the transcription is subordinate to this
document: where the two disagree, this document wins and the transcription is
fixed.

Nor does it claim machine-checked soundness. The soundness metatheorem is
`OBL-JUDGMENT-SOUNDNESS`: its evidence status is `proved` (hand derivation §4.11,
2026-10-20); its Lean form `judgment_soundness` is stated for a well-formed
evaluation chain with the `Eval` conjunct assumed rather than proved, and the
`k` and distance cells enter it as hypotheses at the row (§4.11); and promoted
remains a review disposition. The obligations themselves
are tracked in [`OBLIGATIONS.md`](OBLIGATIONS.md); it is their ledger, and this
section does not restate it.
