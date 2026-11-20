# Operational Semantics

**Status:** normative. The transition relation: which terms have an evaluation
derivation, and what state they yield.

This document consolidates the proposal's operational semantics.

---

## 1. The relation

$$
\mathrm{Eval}(m,\,S,\,S')
$$

is a **partial big-step** relation over phase-insensitive presented CSS states.
There is no judgment when a command is inapplicable, and no partial result is
ever exposed: no residual commands, no half-updated states.

$$
\mathrm{Eval}(m\triangleright e,\, S')
\quad\text{when}\quad
\mathrm{EvalExpr}(e,\,S)\ \text{and}\ \mathrm{Eval}(m,\,S,\,S')
$$

**Base rule.** $\mathrm{Eval}(\mathrm{skip}, S, S)$.

**Sequencing.**

$$
\frac{\mathrm{Eval}(m_1,S_0,S_1)\qquad\mathrm{Eval}(m_2,S_1,S_2)}
 {\mathrm{Eval}(m_1;m_2,S_0,S_2)}
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
\mathsf{some}\ S' & \text{if } \mathrm{Eval}(m,\,S,\,S'),\\
\mathsf{none} & \text{otherwise,}
\end{cases}
\qquad
\llbracket e\rrbracket \;=\;
\begin{cases}
\mathsf{some}\ S & \text{if } \mathrm{EvalExpr}(e,\,S),\\
\mathsf{none} & \text{otherwise.}
\end{cases}
$$

Adequacy is definitional in this direction: $\mathrm{Eval}(m,S,S')$
holds iff $\llbracket m\rrbracket(S) = \mathsf{some}\ S'$, by the clause
itself. The clause reads $\llbracket m\rrbracket(S) = \mathsf{some}\ S'$ for
the unique $S'$ with $\mathrm{Eval}(m,S,S')$, and $\mathsf{none}$ if
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
\mathrm{EvalExpr}(S_1\oplus S_2,\,S)
$$

premises: $Q_1\cap Q_2=\varnothing$ and
$\mathsf{used}_1\cap\mathsf{used}_2=\varnothing$. Result: $Q=Q_1\cup Q_2$, rows
concatenated, identifier sets unioned. Both collisions make the constructor
**inapplicable**.

### `C-DELETE-CHECK`

$$
\frac{\mathrm{DisplayedGenerator}(r,\mathsf{pres})\qquad
 \mathrm{Independent}(r;\mathsf{pres})}
 {\mathrm{Eval}(\mathrm{delete}_r,\,C,\,C')}
$$

$C'$ removes exactly the selected generator. The qubit namespace is unchanged; the
identifier is **retired but stays in `used`**.

### `C-ADD-CHECK`

$$
\frac{r\in Z^\perp\qquad r\notin X}
 {\mathrm{Eval}(\mathrm{addStab}_{r:X},\,C,\,C')}
\qquad
\frac{r\in X^\perp\qquad r\notin Z}
 {\mathrm{Eval}(\mathrm{addStab}_{r:Z},\,C,\,C')}
$$

The premises are the standard CSS commutation and same-sector independence
conditions, **with both complements taken inside $\mathbb{F}_2^Q$**
([`STATE_MODEL.md`](STATE_MODEL.md) §1): $r\in Z^\perp$ presupposes
$r\in\mathbb{F}_2^Q$, i.e. $\mathrm{supp}(r)\subseteq Q$. A candidate row
whose support leaves $Q$ fails the premise and the outcome is **no derivation**,
not malformation — the term is well-typed, and the same row applies against a
state whose namespace contains its support (probe `W22`). Reading $Z^\perp$ as a
bare dot product accepts such a row and produces a display that satisfies I1–I5
while not being a code on $Q$. The identifier is minted **canonically** — there
is no fresh-name choice.

**Capacity premise (H-4, decided 2026-10-31; aligned 2026-11-11).** The mint must exist: the fixed enumeration of 70,000 identifiers
(`STATE_MODEL.md` I3) is not exhausted by $\mathsf{used}$. When every
identifier is in $\mathsf{used}$ the command is inapplicable, a
no-derivation outcome and not a malformation. The same premise, one mint per
new row, governs every minting rule: `E-GRAFT` (the $m-1$ adjacent-product
rows), `P-REBASE` (the $m$ mixes, §4.26), `E-EXTEND` (one per addition,
§4.30), and `E-GLUE` (one per seam check, §4.31). `machine/priced_calculus.py`
raises `NoDerivation` at exhaustion, and `lean/CodeCalculus/Eval.lean` carries
the premise on the five rules (`canonicalMint s.used < totalIdentifiers` for
`Eval.add`, `MintsWithinCapacity` for the multi-mint rules), with
`eval_used_within_capacity` showing that no evaluation mints an identifier
outside the enumeration.

**Gauging-as-merge boundary (face-set model only).** A gauging step equals a
one-face union merge iff the added row is the face boundary of a defect face
(edge-present, unchecked) — the merge is defect filling. On a defect-free patch
no gauging step is a merge. Multi-defect combined gauging ($k-1$) differs from
multi-face filling ($k-|D'|$). This is an identification under the face-set
model; the remainder (graft as a one-qubit split; check deletion as a mapping
cone or sui generis) is open. Source: *code-deformation* claim 15.10
(Theorem 22.1 + Corollary 22.2).

### `C-SEQUENCE`

The rule in §1.

**Order dependence (face-set model only).** Sequencing is not commutative in
general. Punch and fuse commute iff the punched faces are disjoint from the
fusion partner's face set; when they are not disjoint, order moves the
distance (punch-then-fuse $d_Z=5$ versus fuse-then-punch $d_Z=4$ on the
frame+plug family). Sequence certificates must record row order. This is a
conditional statement about the face-set model, not a claim about general
schedules. Source: *code-deformation* claims 15.8 (Prop. 20.2) and 15.9
(Witness 20.3).

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
transition is deterministic for a fixed state and command. The $m-1$ minted
identifiers are subject to the capacity premise of the `C-ADD-CHECK` card: past the enumeration's capacity the graft is inapplicable.

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

### `L-HGP`

**Introduced in:** `stdCSS-3` candidate (admitted 2026-11-11;
`transition-defined`).

$$
\mathrm{EvalExpr}(\mathrm{hgp}(H_1, H_2), S)
$$

Typed inputs: binary matrices $H_1 \in \mathbb{F}_2^{m_1 \times n_1}$ and
$H_2 \in \mathbb{F}_2^{m_2 \times n_2}$ with $m_i, n_i \ge 1$, given row by
row. Applicability: the inputs are well-typed (rows of equal length, entries
in $\{0, 1\}$); every well-typed input evaluates. State update: the qubit set
is $Q = \{0, \ldots, n-1\}$ with $n = n_1 n_2 + m_1 m_2$, the left qubit
$(i, j)$ for $i < n_1$, $j < n_2$ at label $i n_2 + j$ and the right qubit
$(a, b)$ for $a < m_1$, $b < m_2$ at label $n_1 n_2 + a m_2 + b$. The natural
$X$-rows, one per pair $(a, j)$, have support
$\{(i, j) : H_1[a, i] = 1\} \cup \{(a, b) : H_2[b, j] = 1\}$; the natural
$Z$-rows, one per pair $(i, b)$, have support
$\{(i, j) : H_2[b, j] = 1\} \cup \{(a, b) : H_1[a, i] = 1\}$. The displayed
rows are the retained display of the natural rows (§4.34: within each
sector, in index order, a natural row is kept when it lies outside the span
of the rows of its sector kept before it), with identifiers minted
canonically from the empty used set, $X$-rows first; $\mathsf{used}$ is the
set of minted identifiers. Ambient membership: every natural row has support
in $Q$ by construction. Inapplicability: none beyond malformed input (a
matrix that is not binary or not rectangular is malformed at the encoding).
Output well-formedness, $n$, and $k = k_1 k_2 + k_1^{T} k_2^{T}$, with
$k_i = n_i - \mathrm{rank}(H_i)$ and $k_i^{T} = m_i - \mathrm{rank}(H_i)$,
are derived in §4.34. No distance rule is attached (§4.34, *Distances*).

### `L-LIFTED`

**Introduced in:** `stdCSS-3` candidate (admitted 2026-11-11;
`transition-defined`).

$$
\mathrm{EvalExpr}(\mathrm{lift}_G(A, B), S)
$$

Typed inputs: a finite abelian group
$G = \mathbb{Z}_{\ell_1} \times \cdots \times \mathbb{Z}_{\ell_r}$ given by
its cyclic orders (the empty product is the trivial group), and base
matrices $A \in \mathbb{F}_2[G]^{m_A \times n_A}$ and
$B \in \mathbb{F}_2[G]^{m_B \times n_B}$, an entry being a finite set of
exponent tuples read modulo the orders, with repeated terms cancelling.
Write $\ell = |G|$, fix the enumeration of $G$ by exponent tuples in
lexicographic order with $\mathrm{idx}(g)$ the position of $g$, write
$L(x)$ for the regular representation of $x \in \mathbb{F}_2[G]$ (the
$\ell \times \ell$ binary matrix with $L(x)[h, h'] = 1$ exactly when
$h - h'$ is a term of $x$), and $x^{*}$ for the image of $x$ under the
involution that negates every term. Applicability: well-typed inputs only.
State update: the qubits are the left triples $(i, j, g)$ at label
$(i n_B + j)\ell + \mathrm{idx}(g)$ and the right triples $(a, b, g)$ at
label $n_A n_B \ell + (a m_B + b)\ell + \mathrm{idx}(g)$, so that
$n = \ell (n_A n_B + m_A m_B)$. The natural $X$-rows, one per triple
$(a, j, h)$, carry row $h$ of $L(A[a, i])$ on the left qubits $(i, j, g)$,
$g \in G$, for every $i$, and row $h$ of $L(B[b, j]^{*})$ on the right qubits
$(a, b, g)$ for every $b$; the natural $Z$-rows, one per triple $(i, b, h)$,
carry row $h$ of $L(B[b, j])$ on the left qubits $(i, j, g)$ for every $j$
and row $h$ of $L(A[a, i]^{*})$ on the right qubits $(a, b, g)$ for every
$a$. The displayed rows are the retained display with canonically minted
identifiers, $X$-rows first. Over the trivial group the transition is
`hgp(A, B)` read with entries $\{()\}$ for $1$ and $\varnothing$ for $0$.
Output well-formedness and $n$ are derived in §4.34; $k$ is the rank
bookkeeping of the output, with no closed form claimed; no distance rule
is attached.

### `L-GROUP-ALGEBRA`

**Introduced in:** `stdCSS-3` candidate (admitted 2026-11-11;
`transition-defined`).

$$
\mathrm{EvalExpr}(\mathrm{twoblock}_G(a, b), S)
$$

Typed inputs: a finite abelian group $G$ as for `L-LIFTED` and two elements
$a, b \in \mathbb{F}_2[G]$. Applicability: well-typed inputs only. State
update: $n = 2\ell$, the left qubits $(0, g)$ at label $\mathrm{idx}(g)$ and
the right qubits $(1, g)$ at label $\ell + \mathrm{idx}(g)$; the natural
$X$-row $h$ carries row $h$ of $L(a)$ on the left and row $h$ of $L(b)$ on
the right, and the natural $Z$-row $h$ carries row $h$ of $L(b)^{T}$ on the
left and row $h$ of $L(a)^{T}$ on the right, so that the natural check
matrices are $[L(a) \mid L(b)]$ and $[L(b)^{T} \mid L(a)^{T}]$; the displayed
rows are the retained display with canonically minted identifiers. The
transition equals, row for row, `lift_G((a), (b^*))` (§4.34). Output
well-formedness and $k = 2(\ell - \mathrm{rank}[L(a) \mid L(b)])$ are
derived in §4.34; no distance rule is attached.

### `A-CONCAT`

**Introduced in:** `stdCSS-3` candidate (admitted 2026-11-11;
`transition-defined`). The constructor is distinct from the `A-CONCAT`
tower price provider of `JUDGMENT_LAYER.md` §2a, which supplies deletion and
exposure prices for the constructed state and remains the only distance
input path for it.

$$
\mathrm{EvalExpr}(\mathrm{concat}(e_O, e_I; \vec B), S)
$$

Typed inputs: the outer factor $O$, the value of $e_O$, a well-formed CSS
state on $N$ qubits; the inner factor $I$, the value of $e_I$, a well-formed
CSS state on $n_{\mathrm{in}}$ qubits with $k_{\mathrm{in}} \ge 1$ logical
qubits; a block list $\vec B = (B_1, \ldots, B_{n_{\mathrm{out}}})$ of
ordered $k_{\mathrm{in}}$-tuples of outer labels that partition $Q_O$, the
position of a label in its block naming the inner logical that encodes it;
and, optionally, representatives, which are $k_{\mathrm{in}}$ $X$-logical
and $k_{\mathrm{in}}$ $Z$-logical representatives of $I$ forming dual bases,
defaulting to the dual logical bases of the inner level data
(`tower_level_data`, `DERIVED_RELATIONS.md` §2a). Applicability:
$k_{\mathrm{in}} \ge 1$ and the inner level data within its enumeration
ceiling; a block list that is not a partition into
$k_{\mathrm{in}}$-tuples is malformed at the encoding. Non-CSS inner codes
are not inputs (the flagged gap of `TAXONOMY.md` §2.14 stands). State
update: $Q = \{0, \ldots, n_{\mathrm{in}} n_{\mathrm{out}} - 1\}$, copy $j$ of
the inner qubits at labels $j n_{\mathrm{in}} + \iota$ for $\iota$ the index
of the inner label; the natural rows are every inner row on every copy,
then every outer row lifted block by block through the representatives
(the lift of an outer row $h$ of sector $\sigma$ carries, on copy $j$, the
$\sigma$-representative of the class $h_j$ read off block $B_j$); the
displayed rows are the retained display, which drops nothing (§4.34), with
canonically minted identifiers. Output well-formedness,
$n = n_{\mathrm{in}} n_{\mathrm{out}}$, and $k = k_O$ are derived in §4.34;
no distance rule is attached.

### `A-PRODUCT`

**Introduced in:** `stdCSS-3` candidate (admitted 2026-11-11;
`transition-defined`).

$$
\mathrm{EvalExpr}(\mathrm{product}(e_A, e_B), S)
$$

Typed inputs: two well-formed CSS states $A$ and $B$, the values of $e_A$
and $e_B$. For a factor $F$ write $n_F$ for its number of qubits, taken in
the order of $Q_F$, and $m_X^F$ and $m_Z^F$ for its numbers of displayed
$X$-rows and $Z$-rows, taken in display order. The product structure is
fixed: it is the CSS tensor product of Audoux and Couvreur
(`TAXONOMY.md` §2.13), the middle three terms of the tensor product of the
two factors read as chain complexes ($Z$-rows, then qubits,
then $X$-rows; §4.35). Homological products of longer complexes and mapping
cones are not inputs. Applicability: both factors well-formed; every such
pair evaluates. State update: the qubits are, in this order, the pairs
$(z, x)$ of a $Z$-row $z$ of $A$ and an $X$-row $x$ of $B$ at label
$z m_X^B + x$; the pairs $(i, j)$ of a qubit of $A$ and a qubit of $B$ at
label $m_Z^A m_X^B + i n_B + j$; and the pairs $(x, z)$ of an $X$-row of $A$
and a $Z$-row of $B$ at label $m_Z^A m_X^B + n_A n_B + x m_Z^B + z$. So
$n = m_Z^A m_X^B + n_A n_B + m_X^A m_Z^B$. The natural $X$-rows are, first,
one per pair $(i, x)$ of a qubit of $A$ and an $X$-row of $B$, with support
the pairs $(z, x)$ for which $z$ contains $i$ and the pairs $(i, j)$ for
which $x$ contains $j$; then one per pair $(x, j)$ of an $X$-row of $A$ and
a qubit of $B$, with support the pairs $(i, j)$ for which $x$ contains $i$
and the pairs $(x, z)$ for which $z$ contains $j$. The natural $Z$-rows are,
first, one per pair $(z, j)$ of a $Z$-row of $A$ and a qubit of $B$, with
support the pairs $(i, j)$ for which $z$ contains $i$ and the pairs
$(z, x)$ for which $x$ contains $j$; then one per pair $(i, z)$ of a qubit
of $A$ and a $Z$-row of $B$, with support the pairs $(x, z)$ for which $x$
contains $i$ and the pairs $(i, j)$ for which $z$ contains $j$. The
displayed rows are the retained display (§4.34), with canonically minted
identifiers; this is repair (a) of `TAXONOMY.md` §2.13, the retention
decision being fixed by the index order of this card. The output is a
function of the two displays and not only of the two codes: two displays
of one factor code give outputs with the same $n$ and $k$ that need not be
equal up to relabeling (§4.35). Output well-formedness, $n$, and
$k = k_A k_B$ are derived in §4.35. No distance rule is attached.

### `A-DOUBLE`

**Introduced in:** `stdCSS-3` candidate (admitted 2026-11-11;
`transition-defined`).

$$
\mathrm{EvalExpr}(\mathrm{double}_{w,s}(e), S)
$$

Typed inputs: a well-formed CSS state $C$ on $n_C$ qubits, the value of $e$;
a wiring map $w$, which assigns to each displayed row $r$ of $C$ a subset
$w(r)$ of its support, the twisted incidences of $r$; and an optional
sector-duality choice $s$, a flag that is absent or `conjugate`. A wiring
that names an identifier not displayed in $C$, or a qubit outside the row's
support, is malformed at the encoding. State update: the qubits are the
pairs $(q, t)$ of a qubit $q$ of $C$ and a sheet $t \in \{0, 1\}$, at label
$t n_C + \iota(q)$ with $\iota(q)$ the index of $q$ in $Q_C$, so
$n = 2 n_C$. Each displayed row $r$ gives two natural rows $(r, 0)$ and
$(r, 1)$, in display order with sheet $0$ first: the support of $(r, t)$ is
the set of $(q, t)$ for $q$ in the support of $r$ and outside $w(r)$,
together with the $(q, 1 - t)$ for $q \in w(r)$. The sector of $(r, t)$ is
the sector of $r$, except that under `conjugate` the rows of sheet $1$ take
the opposite sector. Applicability: the natural rows of the two sectors
have pairwise even overlap; a wiring for which they do not gives no
derivation. The displayed rows are the retained display with canonically
minted identifiers. The output is a function of the display of $C$ and of
$w$, which is keyed by displayed identifiers. Output well-formedness and
$n$ are derived in §4.35; $k$ is the rank bookkeeping of the output, with
$k = 2 k_C$ for the empty wiring. No distance rule is attached. This card
fixes one mechanism for the record of `TAXONOMY.md` §2.16, the two-sheet
cover of the incidence structure. It does not settle that record's
factorization question (§4.35).

### `L-BALANCED`

**Introduced in:** `stdCSS-3` candidate (admitted 2026-11-11;
`transition-defined`).

$$
\mathrm{EvalExpr}(\mathrm{balanced}_G(H_1, \alpha_1; H_2, \alpha_2), S)
$$

Typed inputs: a finite abelian group $G$ given by its cyclic orders, as for
`L-LIFTED`; binary matrices $H_1 \in \mathbb{F}_2^{m_1 \times n_1}$ and
$H_2 \in \mathbb{F}_2^{m_2 \times n_2}$; and for each $H_c$ an action
$\alpha_c$ of $G$, given by one permutation of the row indices and one
permutation of the column indices of $H_c$ for each cyclic generator. The
permutations of one index set must commute, the permutation of a generator
must have order dividing that generator's cyclic order, and $H_c$ must be
equivariant: $H_c[g a, g i] = H_c[a, i]$ for every generator $g$, row $a$,
and column $i$. An input that fails one of these is malformed at the
encoding. Applicability: well-typed inputs only. State update: $G$ acts on
a pair $(x, y)$ of an index of $H_1$ and an index of $H_2$ by
$g (x, y) = (g x, g^{-1} y)$, so that its orbits are the classes of the
relation $(g x, y) \sim (x, g y)$. The qubits are the orbits of the pairs
$(i, j)$ of two column indices, then the orbits of the pairs $(a, b)$ of two
row indices, each family in the order of the least pair of an orbit, pairs
compared lexicographically; $n$ is the number of these orbits. There is
one natural $X$-row for each orbit of the pairs $(a, j)$ of a row index of
$H_1$ and a column index of $H_2$, and one natural $Z$-row for each orbit of
the pairs $(i, b)$, in the same order. With $\xi(a, j)$ and $\zeta(i, b)$
the natural rows of `hgp(H₁, H₂)` (the `L-HGP` card), the natural $X$-row of
an orbit $c$ contains the qubit orbit $o$ exactly when an odd number of the
pairs $(a, j) \in c$ have the least pair of $o$ in $\xi(a, j)$; the natural
$Z$-row of an orbit with least pair $(i, b)$ contains the qubit orbit $o$
exactly when an odd number of the qubits of $\zeta(i, b)$ lie in $o$. The
displayed rows are the retained display with canonically minted
identifiers. Over the trivial group the transition is `hgp(H₁, H₂)`, row
for row. Output well-formedness and $n$ are derived in §4.35; $k$ is the
rank bookkeeping of the output, with no closed form claimed. No distance
rule is attached.

### `L-TANNER`

**Introduced in:** `stdCSS-3` candidate (admitted 2026-11-11;
`transition-defined`).

$$
\mathrm{EvalExpr}(\mathrm{tanner}(n; \Lambda_X, \Lambda_Z; \iota_X, \iota_Z), S)
$$

Typed inputs: a qubit count $n \ge 1$; two local codes, binary matrices
$\Lambda_X$ with $w_X$ columns and $\Lambda_Z$ with $w_Z$ columns, whose rows
are the local $X$-checks and the local $Z$-checks; and the typed graph with
its embeddings, given as two lists $\iota_X$ and $\iota_Z$. Each entry of
$\iota_X$ is a vertex of the $X$ class with its embedding, an ordered list
of $w_X$ distinct labels below $n$, and each entry of $\iota_Z$ is a vertex
of the $Z$ class with an ordered list of $w_Z$ distinct labels. The graph is
the bipartite incidence structure these lists define: a vertex is incident
to the qubits of its embedding. State update: $Q = \{0, \ldots, n - 1\}$.
The natural rows are, for each vertex of the $X$ class in list order and
each row $\lambda$ of $\Lambda_X$ in order, the $X$-row whose support is the
set of labels at the positions where $\lambda$ is $1$; then the same for
the $Z$ class with $\Lambda_Z$. Applicability: the natural rows of the two
sectors have pairwise even overlap (cross-partition commutation); an input
for which they do not gives no derivation. The displayed rows are the
retained display with canonically minted identifiers. Output
well-formedness and $n$ are derived in §4.35, with a sufficient condition
for the commutation premise when the local codes are tensor codes; $k$ is
the rank bookkeeping of the output. No distance rule is attached, and no
expansion hypothesis is an input of the transition.

### `L-TILE`

**Introduced in:** `stdCSS-3` candidate (admitted 2026-11-11;
`transition-defined`).

$$
\mathrm{EvalExpr}(\mathrm{tile}(\tau; \alpha; \beta), S)
$$

Typed inputs: a tile set $\tau$, a nonempty list of tiles, a tile being a
local qubit count $t \ge 1$ with a list of local $X$-row supports and a
list of local $Z$-row supports over $\{0, \ldots, t - 1\}$; a cellulation
$\alpha$, a nonempty list of placements, a placement being a tile of $\tau$
with an ordered list of $t$ distinct site labels (natural numbers), one per
local qubit; and boundary rules $\beta$, a list of pairs of placed sites to
identify and a list of removed checks, each naming a placement, a sector,
and a local row of that placement's tile. Two placements that name one site
share it. State update: the site classes are the classes of the placed
sites under the equivalence generated by the identifications; the qubits
are the site classes in the order of their least site, relabeled
$0, \ldots, n - 1$, so $n$ is the number of site classes. The natural rows
are, placement by placement in list order, the local $X$-rows and then the
local $Z$-rows of the placement's tile that are not removed; the support of
a natural row is the set of site classes that contain an odd number of the
sites of the local row's qubits. Applicability: the natural rows of the two
sectors have pairwise even overlap (interface orthogonality); an assembly
for which they do not gives no derivation. The displayed rows are the
retained display with canonically minted identifiers, so a check imposed
by two placements is displayed once. Output well-formedness and $n$ are
derived in §4.35; $k$ is the rank bookkeeping of the output. No distance
rule is attached.

### `L-NESTED-CSS`

**Introduced in:** `stdCSS-3` / `v0.2.0` (admitted 2026-11-13;
`transition-defined`).

$$
\mathrm{EvalExpr}(\mathrm{nested}(H_X, H_Z), S)
$$

Typed inputs: two binary matrices $H_X$ and $H_Z$, each with at least one
row, with the same number $n \ge 1$ of columns. They are read as
parity-check matrices of two classical codes of length $n$, the kernels of
$H_X$ and of $H_Z$. State update: $Q = \{0, \ldots, n - 1\}$. The natural
rows are the rows of $H_X$ in order, each an $X$-row whose support is the
set of columns where the row is $1$, then the rows of $H_Z$ in order as
$Z$-rows. Applicability: every row of $H_X$ has even overlap with every
row of $H_Z$, that is, $H_X H_Z^{T} = 0$, which says that the dual of each
code is contained in the other code (the nesting, §4.36); an input for
which it fails gives no derivation. The displayed rows are the retained
display with canonically minted identifiers, so a sector with no check is
given as one zero row. Output well-formedness, $n$, and the closed form
$k = n - \mathrm{rank}(H_X) - \mathrm{rank}(H_Z)$ are derived in §4.36. No
distance rule is attached, and no classical distance is an input of the
transition.

### `L-MAPPING-CONE`

**Introduced in:** `stdCSS-3` / `v0.3.0` (admitted 2026-11-18;
`transition-defined`).

$$
\mathrm{EvalExpr}(\mathrm{cone}(\partial_A, \partial_B, f_1, f_0), S)
$$

Typed inputs: four binary matrices $\partial_A$, $\partial_B$, $f_1$, $f_0$,
with $\partial_A$ of shape $a_1 \times a_0$, $\partial_B$ of shape
$b_1 \times b_0$, $f_1$ of shape $a_1 \times b_1$, and $f_0$ of shape
$a_0 \times b_0$. They are read as the differentials and chain map of two
two-term complexes $A$ and $B$ over $\mathbb{F}_2$. State update:
$Q = \{0, \ldots, a_0 + b_1 - 1\}$, with the first $a_0$ labels the
basis of $A_0$ and the remaining $b_1$ labels the basis of $B_1$. The
natural $Z$-rows are, for each basis element of $A_1$, the support of
$\delta_2(a_1) = (\partial_A a_1, f_1 a_1)$, and the natural $X$-rows
are, for each basis element of $B_0$, the support of the corresponding row
of $\delta_1(a_0, b_1) = f_0 a_0 + \partial_B b_1$. Applicability: the
chain-map premise $\partial_B f_1 = f_0 \partial_A$; an input for which
it fails gives no derivation. Under the premise the natural rows of the two
sectors have pairwise even overlap, so the retained display is well-formed.
The displayed rows are the retained display with canonically minted
identifiers. Output well-formedness, $n = a_0 + b_1$, and
$k = a_0 + b_1 - \mathrm{rank}(\text{natural }X) - \mathrm{rank}(\text{natural }Z)$
are derived in §4.41. No distance rule is attached: the ledger starts at
$[0, +\infty)$, and the conditional sector-distance cells are
$\min(D_B, D_A)$ as recorded in `JUDGMENT_LAYER.md` §2g.

### `L-EMPTY`

**Introduced in:** `stdCSS-4` / `v0.4.0` candidate (admitted 2026-11-19;
`transition-defined`).

$$
\mathrm{EvalExpr}(\mathrm{empty}, S)
$$

Typed inputs: none (`()`). State update: $Q = \varnothing$, empty display
(`rows = []`), empty `used`. Applicability: always applicable. Output
well-formedness ($n = 0$, $k = 0$) and semantic distance ($d_X = d_Z = d = +\infty$)
are derived in §4.43. No automatic distance rule is attached beyond §2g.

### `L-FREE`

**Introduced in:** `stdCSS-4` / `v0.4.0` candidate (admitted 2026-11-19;
`transition-defined`).

$$
\mathrm{EvalExpr}(\mathrm{free}(Q), S)
$$

Typed inputs: a finite set $Q \subset \mathbb{N}$ of distinct nonnegative
qubit labels, stored in strictly increasing order. State update: $Q$, empty
display (`rows = []`), empty `used` (`free(∅) ≡ empty`). Applicability: always
applicable for a well-typed $Q$. Output well-formedness ($n = |Q|$, $k = |Q|$)
and semantic distance ($d_X = d_Z = d = 1$ for $Q \neq \varnothing$, $+\infty$
for $Q = \varnothing$) are derived in §4.43. No automatic distance rule is
attached beyond §2g.

### `A-PULLBACK`

**Introduced in:** `stdCSS-4` / `v0.4.0` candidate (admitted 2026-11-19;
`transition-defined`).

$$
\mathrm{EvalExpr}(\mathrm{pullback}(e_1, e_2, e_I; \phi_1, \phi_2), S)
$$

Typed inputs: three state expressions $e_1, e_2, e_I$ evaluating to well-formed
CSS states $C_1, C_2, I$, together with total qubit maps $\phi_1 : Q_1 \to Q_I$
and $\phi_2 : Q_2 \to Q_I$. State update: the qubits are the fiber-product pairs
$P = \{(q_1, q_2) \in Q_1 \times Q_2 : \phi_1(q_1) = \phi_2(q_2)\}$ in
lexicographic order ($Q_1$ outer, $Q_2$ inner), relabeled $0, \dots, n - 1$ where
$n = |P|$. The natural rows are, for each displayed row $r$ of $C_1$ in order,
its pullback $\pi_1^*(r) = \{i \in \{0,\dots,n-1\} : q_1^{(i)} \in \mathrm{supp}(r)\}$
in the same sector, followed by, for each displayed row $r$ of $C_2$ in order,
its pullback $\pi_2^*(r) = \{i \in \{0,\dots,n-1\} : q_2^{(i)} \in \mathrm{supp}(r)\}$
in the same sector. The displayed rows are the retained independent display
(§4.34) with canonically minted identifiers from empty `used`. Applicability:
(i) $\phi_1$ and $\phi_2$ are **CSS code morphisms** into $I$, i.e., for each
$i \in \{1, 2\}$ and every displayed $\sigma$-row $r$ of $C_i$, its
$\mathbb{F}_2$-pushforward $(\phi_i)_*(\mathrm{supp}(r)) = \{y \in Q_I : |\phi_i^{-1}(y) \cap \mathrm{supp}(r)| \equiv 1 \pmod 2\}$
lies in the $\sigma$-row space of $I$; and (ii) the natural rows of the two
sectors on $0, \dots, n - 1$ have pairwise even overlap ($X \perp Z$). A failed
premise gives no derivation. Output well-formedness and $n$ are derived in §4.43;
$k$ is the rank bookkeeping of the output. No distance rule is attached.

### `A-PUSHOUT`

**Introduced in:** `stdCSS-4` / `v0.4.0` candidate (admitted 2026-11-19;
`transition-defined`).

$$
\mathrm{EvalExpr}(\mathrm{pushout}(e_1, e_2, e_S; \psi_1, \psi_2), S)
$$

Typed inputs: three state expressions $e_1, e_2, e_S$ evaluating to well-formed
CSS states $C_1, C_2, S$, together with total qubit maps $\psi_1 : Q_S \to Q_1$
and $\psi_2 : Q_S \to Q_2$. State update: form the disjoint union
$Q_1 \sqcup Q_2$ (tagged $(0, q_1)$ for $q_1 \in Q_1$ and $(1, q_2)$ for
$q_2 \in Q_2$) and quotient by the equivalence relation $\sim$ generated by
$(0, \psi_1(s)) \sim (1, \psi_2(s))$ for all $s \in Q_S$. Order the equivalence
classes by first appearance in $[(0, q_1) : q_1 \in Q_1] \mathbin{++} [(1, q_2) : q_2 \in Q_2]$
and relabel $0, \dots, n - 1$ where $n = |Q_1 \sqcup_{Q_S} Q_2|$. The natural
rows are, for each displayed row $r$ of $C_1$ in order, its $\mathbb{F}_2$-pushforward
to the quotient classes (class $c$ is in the support iff an odd number of
$(0, q_1)$ with $q_1 \in \mathrm{supp}(r)$ lie in $c$), followed by, for each
displayed row $r$ of $C_2$ in order, its $\mathbb{F}_2$-pushforward to the
quotient classes (class $c$ is in the support iff an odd number of $(1, q_2)$
with $q_2 \in \mathrm{supp}(r)$ lie in $c$). The displayed rows are the retained
independent display (§4.34) with canonically minted identifiers from empty
`used`. Applicability: (i) $\psi_1$ and $\psi_2$ are **CSS code morphisms** from
$S$, i.e., for each $i \in \{1, 2\}$ and every displayed $\sigma$-row $r$ of $S$,
$(\psi_i)_*(\mathrm{supp}(r))$ lies in the $\sigma$-row space of $C_i$; and
(ii) the natural rows of the two sectors on $0, \dots, n - 1$ have pairwise even
overlap ($X \perp Z$). A failed premise gives no derivation. Output
well-formedness and $n$ are derived in §4.43; $k$ is the rank bookkeeping of
the output. No distance rule is attached.


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
hypothesis. The red-team qualification that raised this is kept at
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4 and its disposition in
REDTEAM_D3_SPANNING_2026-10-10.md.

**Distance non-increase under deletion** ($d_X'\le d_X$, $d_Z'\le d_Z$, and
$d'\le d$ by `MIN-ORDER` + `TRANSITIVITY`) and **the skip identity** are recorded
at [`OBLIGATIONS.md`](OBLIGATIONS.md)'s §5.5 and §5.6. The skip
identity is the one obligation discharged to date — `proved`, and **not yet
`promoted`**, since promotion is a human-owned review disposition.


## 4. The dated hand derivations

Folded here 2026-10-11 from OPERATION_SEMANTICS.md §5.
These are **evidence in this repository, not machine-checked proofs**, and each is to be
re-derived mechanically. Their qualifications are retained verbatim, per `AGENTS.md`:
*review findings are dispositions, not silent edits.*

Dated hand derivations behind the
`established` claim-status tags of the proposal. Each is to be re-derived
– — these are not machine-checked. All parameters are the
proposal §3.1 definitions.

**§4.1 — Deletion (`C-DELETE-CHECK`).** The deleted row is displayed and
independent (I2), so removing it drops the rank of its sector's row space by
exactly one and leaves the other sector unchanged; $Q$ is unchanged. With
$k=n-\dim X-\dim Z$: $n'=n$ and $k'=k+1$. Output well-formedness: removing
rows cannot violate $X\perp Z$.

**Qualification (red-team a review finding, 2026-10-10 — DISPOSITIONED the same day, D-3
closed, : reading (A), I1's span clause is
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
REDTEAM_D3_SPANNING_2026-10-10.md
for the disposition record and for what survives it (a review finding, T-4 — repair work in
other artifacts, not here).

**§4.2 — Addition (`C-ADD-CHECK`).** The premise $r\notin X$ (resp.
$r\notin Z$) makes $r$ independent of the target sector's row space, whose
rank therefore rises by exactly one: $n'=n$, $k'=k-1$. *(Qualification a review finding
above covers this step too; the premise is row-space-based and display
independence is span-based — they coincide only under spanning. Note also T-7:
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
proof, and is re-derived in Lean (`ExactDistance.lean`).

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
`Eval(skip,·,·)` is $Eval(\mathrm{skip},S,S)$; state update $S'=S$ on every
semantic field; applicability *none*, so always applicable. The `C-SEQUENCE`
card: $\dfrac{Eval(m_1,S_0,S_1)\quad Eval(m_2,S_1,S_2)}{Eval(m_1;m_2,S_0,S_2)}$.

**Forward ($m \Rightarrow \mathrm{skip};m$).** Assume
$Eval(m,S,S')$. The bare `C-SKIP` rule gives $Eval(\mathrm{skip},S,S)$ with
no premises. Applying `C-SEQUENCE` to that and the assumption yields
$Eval(\mathrm{skip};m,S,S')$, i.e. the left conjunct holds with
$S''=S'$.

**Reverse ($\mathrm{skip};m \Rightarrow m$).** Assume
$Eval(\mathrm{skip};m,S,S'')$. By `C-SEQUENCE` there is an intermediate
$S_1$ with $Eval(\mathrm{skip},S,S_1)$ and $Eval(m,S_1,S'')$. The `C-SKIP`
card forces $S_1\equiv_{\mathrm{sem}}S$ — the rule's conclusion is $S$ itself,
and only the semantically inert step record differs. By the framing lemma,
$Eval(m,S_1,S'')$ is equivalent to $Eval(m,S,S'')$. Hence the right conjunct
holds.

**Sequencing on the right is the same argument.** $Eval(m;\mathrm{skip},S,S''')$
holds iff there is $S_1$ with $Eval(m,S,S_1)$ and $Eval(\mathrm{skip},S_1,S''')$,
and the `C-SKIP` card forces $S'''\equiv_{\mathrm{sem}}S_1$; conversely
$Eval(m,S,S')$ together with the bare skip rule on $S'$ gives
$Eval(m;\mathrm{skip},S,S')$ directly, with no lemma needed. $\square$

**Stronger than the obligation states.** The obligation asserts $S''$ and $S'''$
"agree with $S'$ up to $\equiv$". The derivation delivers more: they agree on
**every field $\equiv$ reads**, and differ only in a field no judgment reads, so
$\equiv$ holds a fortiori. No congruence of `Eval` under $\equiv$ is used or
needed — worth recording, since the review dispositioned the relabeling congruence
narrowly and this obligation was its most likely consumer.

**Standing of this derivation.** Hand-written 2026-10-11, evidence and not a
machine-checked proof; it is re-derived mechanically in the sequencing slice, per the
obligation's *Intended mechanization status*. It discharges the obligation's
`open` evidence status to `proved` and nothing else: `promoted` is a review
disposition and remains human-owned (`AUTHORITY.md` §B1–§B2), so no promotion
occurs here.

## 4.7 — Well-formedness preservation (`OBL-WELL-FORMEDNESS-PRESERVATION`)

Hand derivations, for the five MVP instances. Each assumes the input
state satisfies I1–I5 and the primitive's applicability premises
(`spec/STATE_MODEL.md` §3, §4). Output well-formedness is then checked
invariant by invariant. These are evidence, not machine-checked proofs, and are
re-derived in Lean: the `C-SKIP`, `C-DELETE-CHECK`,
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

**`C-SEQUENCE`.** If $\mathrm{Eval}(m_1,S_0,S_1)$ and
$\mathrm{Eval}(m_2,S_1,S_2)$ with $S_0$ well-formed, then $S_1$ is
well-formed by the instance for $m_1$, and $S_2$ is well-formed by the instance
for $m_2$. By induction on the sequence length, every intermediate state and the
final state satisfy I1–I5.

$\square$

## 4.8 — Primitive determinism, sequencing associativity, and direct-sum laws

Hand derivations. Evidence, not machine-checked; re-derived in Lean (`KernelObligations.lean`).

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

**`OBL-SEQUENCE-ASSOCIATIVITY`.** $\mathrm{Eval}(m_1;m_2,S,S')$ holds iff
there is an intermediate $S_1$ with $\mathrm{Eval}(m_1,S,S_1)$ and
$\mathrm{Eval}(m_2,S_1,S')$. For $(m_1;m_2);m_3$ this requires
$S_{12}$ with $\mathrm{Eval}(m_1;m_2,S,S_{12})$ and
$\mathrm{Eval}(m_3,S_{12},S')$, i.e. $S_1$ with
$\mathrm{Eval}(m_1,S,S_1)$ and $S_2$ with
$\mathrm{Eval}(m_2,S_1,S_2)$ and $\mathrm{Eval}(m_3,S_2,S')$ —
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

Hand derivations. Evidence, not machine-checked; re-derived in Lean (`KernelObligations.lean`).

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
- *Addition clause (conditional).* If $\mathrm{supp}(r)\subseteq Q_A$,
 then $r$ annihilates $Z_B$ and cannot meet $X_B$, so applicability splits
 per block and holds on the sum iff it holds on $A$. The result is $A'\oplus B$
 provided the allocation-compatibility premise holds:
 $\mathrm{mint}(\mathsf{used}_A\cup\mathsf{used}_B)=
 \mathrm{mint}(\mathsf{used}_A)$, i.e.
 $\mathrm{mint}(\mathsf{used}_A)\notin\mathsf{used}_B$. Every
 identifier before $\mathrm{mint}(\mathsf{used}_A)$ in the fixed
 enumeration lies in $\mathsf{used}_A$, so under the `C-DIRECT-SUM`
 disjointness of the two `used` sets the premise says that
 $\mathsf{used}_B$ starts strictly after $\mathrm{mint}(\mathsf{used}_A)$.
 Without that premise the summands are still applicable but mint
 differently, and the clause fails, which is why it is a hypothesis.

$\square$


## 4.10 — Cross-sector conditional permutation (`OBL-CROSS-SECTOR-PERMUTATION`)

 Evidence, not machine-checked; re-derived in Lean (`KernelObligations.lean`).

Let $m_X$ be a command of $X$-sector type and $m_Z$ a command of $Z$-sector
type, both over the same well-formed single state $S = (Q, X, Z, \mathsf{pres},
\mathsf{used})$. Applicability of each command on $S$ is a decidable property
of $S$ and the command's explicit data (card premises,
`spec/OPERATIONAL_SEMANTICS.md` §2), so for each order either it applies or it
does not. This gives four exhaustive, mutually exclusive situations. The
analysis below is by command pair; there are no summands and no per-sector
$\mathsf{used}_X, \mathsf{used}_Z$ sets — $m_X$ and $m_Z$ act sequentially
on one state.

- **`Delete` / `Delete` ($\mathrm{delete}_{r_X}, \mathrm{delete}_{r_Z}$).**
 Deletions do not mint identifiers and do not change $\mathsf{used}$, and
 opposite-sector deletions do not affect each other's `DisplayedGenerator` or
 `Independent` premises. Both orders apply iff both deletions apply on $S$; when
 both apply the outputs are always $\equiv$-equal (**Case 1**), and otherwise
 **Case 4**.

- **`Delete` / `Add` ($\mathrm{delete}_{r_X}, \mathrm{addStab}_{s:Z}$
 or the symmetric pair).** Because deletion leaves $\mathsf{used}$ unchanged,
 $\mathrm{addStab}$ mints $\mathrm{mint}(\mathsf{used})$ in
 both orders whenever both orders apply, yielding $\equiv$-equal outputs
 (**Case 1**). **Case 3** (exactly one order applies) arises iff $r_X$ is
 displayed and independent in $S$, $s \in \mathbb{F}_2^Q \setminus Z$
 commutes with $\mathit{rows}_X \setminus \{r_X\}$, and
 $s \cdot r_X = 1$: then $\mathrm{delete}_{r_X};\mathrm{addStab}_{s:Z}$
 applies while $\mathrm{addStab}_{s:Z};\mathrm{delete}_{r_X}$
 fails (fixture `W8`). The reverse single-order case
 ($\mathrm{addStab};\mathrm{delete}$ applies while
 $\mathrm{delete};\mathrm{addStab}$ fails) is impossible because
 deleting $r_X$ only shrinks $X$ (weakening $s \in X^\perp$) and leaves $Z$
 untouched.

- **`Add` / `Add` ($\mathrm{addStab}_{r:X}, \mathrm{addStab}_{s:Z}$).**
 Both orders apply iff each applies on $S$ and $r \cdot s = 0$. When both
 apply, the first command always mints $i_1 = \mathrm{mint}(\mathsf{used})$
 and the second always mints
 $i_2 = \mathrm{mint}(\mathsf{used} \cup \{i_1\}) \neq i_1$,
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

Hand derivations. Evidence, not machine-checked; re-derived in Lean (`KernelObligations.lean`). First mechanization slice landed 2026-10-25 (`lean/CodeCalculus/Soundness.lean`, `lake build` green with no `sorry`):
the models predicate `Models` over the chain a closed command unfolds through,
the L3 rule inventory below as the inductive `Derives`, and
`judgment_soundness` by induction on a derivation, for a well-formed
evaluation chain (`Chain cs` and `WellFormedContext cs`). `Models` returns the
chain hypothesis unchanged, so the slice proves the `⊨` half under an assumed
evaluation: the `Eval` conjunct is assumed rather than proved, and the chain
hypothesis cannot be dropped (`le_refl` and the pure order rows are derivable
over any list of states). The chain is supplied from the evaluation in
`lean/CodeCalculus/TermSoundness.lean` (2026-11-12):
`Trace m s cs t` is the list of states the command `m` passes through from
`s` to `t`, one per primitive step; a command has a trace exactly when it
evaluates (`eval_iff_trace`), the trace is unique (`Trace.unique`), and it
is a `Chain` from `s` to `t` (`Trace.chain`, `Trace.getLast`).
`judgment_soundness_of_eval` and `judgment_soundness_of_term` conclude
`Models` over that trace from `Eval m s t`, respectively `EvalTerm`, and the
well-formedness of the input state, with `_exact` forms for the exact
distance. The well-formedness of the state the term's expression evaluates
to stays the FD1 hypothesis.
The expanded-operation-set mechanization is
`lean/CodeCalculus/ExpandedSoundness.lean`:
`ExtDerives` over `ExtNat = ℕ ∪ {+∞}`, with `TermModels`,
`ext_judgment_soundness`, and its `_exact`, `_exact_uncertified`, and
`_exact_admissible` instances; seam-certificate equality is retained as
`SeamCertSound` and proved for `AdmissibleSeam`. It covers the kernel
commands, `E-GRAFT`, all five unary Gate 6 moves, `C-DIRECT-SUM`,
`E-GLUE` (uncertified and certified), and the ten typed constructors; the
conditional priced cells are mechanized in `PricedInterval.lean` and
`Gate6Exact.lean`. `Soundness.lean` / `TermSoundness.lean` keep the
`Nat`-valued sentinel reading for fixed-namespace rows; the two systems
relate by documentation only. The slice proves the instantiation base for skip's
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
(`lean/CodeCalculus/RanksFit.lean`, 2026-10-28) derives from
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
- *Context.* $\Gamma$ contains only well-formedness assumptions, which
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

 *Instance for the generator-referencing claim (2026-11-11).*
 Let $\mathsf{gen}_i(r,\sigma,S)$ be the claim of `spec/JUDGMENT_LAYER.md`
 §4: the state at chain position $i$ displays a row with identifier $r$,
 sector $\sigma$, and support $S$. Its rules are sound. The source rule
 concludes $\mathsf{gen}_{i+1}(r,\sigma,S)$ at a `C-ADD-CHECK` of
 $(\sigma,S)$ with $r$ the canonical mint, and the addition's update appends
 exactly that row. The three transport rules pass from position $i$ to
 $i+1$: `C-SKIP` leaves the state unchanged, `C-ADD-CHECK` keeps every
 displayed row, and `C-DELETE-CHECK` of $r'$ keeps every row whose
 identifier differs from $r'$, which includes the row named $r$ because
 $r \ne r'$ is the rule's side condition. Now let the step from position $i$
 to $i+1$ be `C-DELETE-CHECK` of $r$. The output display is the input
 display with every row of identifier $r$ removed (§2), so no row of the
 output has identifier $r$, and $\mathsf{gen}_{i+1}(r,\sigma,S)$ holds for
 no $\sigma$ and no $S$. By soundness of the whole inventory it has no
 derivation over that chain: no derivation closes. The claim is derivable
 at position $i$ whenever it was derived there, so the refusal is of the
 transport and not of the claim. $\square$

 *The input display and the graft (2026-11-11).* The
 input-display rule concludes $\mathsf{gen}_0(r,\sigma,S)$ for a row
 $(r,\sigma,S)$ displayed by the state at position $0$, which is what the
 claim says. Let the step from position $i$ to $i+1$ be `E-GRAFT` at $q$ in
 sector $\tau$ along the chain $\vec r = (r_1,\ldots,r_m)$. By the §2 card
 the output display consists of the rows of the input whose identifiers are
 not in $\vec r$, each with its identifier and sector and with $q$ removed
 from its support when it is an opposite-sector row that contains $q$, and
 of the $m-1$ minted rows, of sector $\tau$, with supports the adjacent
 products restricted to $Q \setminus \{q\}$. The surviving-generator rule
 concludes exactly the first kind of row from the claim of its input row,
 with $r \notin \vec r$ as its side condition, and the minted-row rule
 concludes the second kind, the restricted adjacent product being
 $S_j \mathbin{\triangle} S_{j+1}$ because $q$ is in both supports. Both are
 sound. Now let $r \in \vec r$. No surviving row has identifier $r$,
 because surviving rows keep identifiers outside $\vec r$. No minted row
 has identifier $r$ either: $r$ names a displayed row of the well-formed
 input, so $r \in \mathsf{used}$ (I3), and the canonical mints are not in
 $\mathsf{used}$. So $\mathsf{gen}_{i+1}(r,\sigma,S)$ holds for no $\sigma$
 and no $S$, and by soundness of the inventory it has no derivation: the
 `W13` half holds across the graft for the generators the graft retires.

 *Transport of the input-display rule.* Let a derivation over the second
 segment of a sequence conclude a generator-referencing claim. Every rule
 it uses other than the input-display rule is an instantiation at a step of
 that segment, and it is the same instantiation at the same step of the
 composed chain, at the shifted position. A use of the input-display rule
 concludes the claim of a row of the seam state at the segment's position
 $0$; in the composed chain that is the claim at the seam position, which
 the seam condition of `spec/JUDGMENT_LAYER.md` §4 supplies. So under the
 seam condition the derivation transports. A derivation of a sentence that
 is not a generator-referencing claim uses no generator rule, since each
 rule with such a sentence as its conclusion has premises of the same kind,
 so it transports with no condition, as before. $\square$

 *Seam condition on chains of kernel, graft, and Gate 6 steps.* Let every
 step of a chain be a single (non-sequence) command. Then at every
 position $i$ the claim $\mathsf{gen}_i(r,\sigma,S)$ of every row
 $(r,\sigma,S)$ the state at position $i$ displays is derivable, by
 induction on $i$. At $i = 0$ it is the input-display rule. Across a step
 from position $i$ to $i+1$, read the output display off the transition.
 After `skip` the display is unchanged, and the `skip` row carries the
 claim. After the deletion of $r'$ a displayed row has $r \ne r'$ and was
 displayed before, and the deletion row carries it. After an addition a
 displayed row was displayed before, and the addition row carries it, or it
 is the minted row, which the minting rule sources. After a graft a
 displayed row is a minted adjacent-product row, which the graft's minting
 rule sources, or it is the image
 $(r,\sigma,\mathrm{graftSupport}(S_0))$ of a row $(r,\sigma,S_0)$
 displayed before with $r$ outside the graft's chain, and the graft's
 survival row carries the claim of $(r,\sigma,S_0)$ to it. After a peel at
 $q$ of the row $r_{\mathrm{id}}$ in sector $\tau$, every displayed output row
 is the shortening at $q$ of an input row $(r,\sigma,S_0)$ with
 $r \ne r_{\mathrm{id}}$ (same-sector survivors are $q$-free by uniqueness of
 $r_{\mathrm{id}}$, so `peelSupport` agrees with `graftSupport`), and the
 peel row carries its claim; the retired row $r_{\mathrm{id}}$ has no
 derivation for any $\sigma, S$. After a puncture at $q$, every displayed
 output row was displayed before with $q \notin S$ and its claim is carried
 unchanged; no claim with $q \in S$ is derivable, and by I3 identifier
 injectivity no retired identifier whose input row contained $q$ has a
 derivable claim for any $\sigma, S$. After an extend, a displayed row was
 displayed before and its claim is carried unchanged, or it is a minted row,
 which the minting rule sources. After a local Hadamard ($T=Q$ or
 $T=\varnothing$), when $T$ is empty the display is unchanged and the claim is
 carried with its sector unchanged; when $T$ is non-empty the sector of every
 displayed row is swapped and the claim follows the swap. After a rebase at
 sector $\tau$, every displayed output row is either a surviving
 opposite-sector row (carried unchanged) or a minted row of sector $\tau$
 (sourced by the minting rule); by I3 identifier injectivity and mint
 freshness, no retired identifier of sector $\tau$ has a derivable claim for
 any $\sigma, S$. In each case the claim at position $i$ is derivable by the
 induction hypothesis. Because every command evaluation unfolds through its
 trace (`Trace`) into a chain of single (non-sequence) steps, the seam
 condition holds unconditionally at the seam of every sequence $m_1; m_2$.
 With soundness of the rows, on any well-formed single-step chain or command
 trace from a well-formed input, $\mathsf{gen}_i(r,\sigma,S)$ is derivable
 exactly when the state at position $i$ displays $(r,\sigma,S)$. $\square$

 *The Gate 6 rows (2026-11-14; completed 2026-11-18).*
 The rows of `Derives` for `Ann.gen` under `E-EXTEND`, `E-PEEL`, `E-PUNCTURE`,
 `E-LOCAL-HADAMARD`, and `P-REBASE` are sound. `E-EXTEND` keeps every
 displayed row and mints rows for the additions; a claim of a displayed row
 is carried with its identifier, sector and support unchanged, and each
 minted row is a source. `E-PEEL` at $q$ in sector $\tau$ retires the
 named row $r_{\mathrm{id}}$ and shortens the support of every surviving
 opposite-sector row at $q$ (agreeing with `peelSupport` because $r_{\mathrm{id}}$
 is the unique $\tau$-row containing $q$); a claim with $r \ne r_{\mathrm{id}}$
 is carried with its support shortened, and $r_{\mathrm{id}}$ names no output
 row, so $\mathsf{gen}_{i+1}(r_{\mathrm{id}},\sigma,S)$ has no derivation
 for any $\sigma, S$ (the `W13` half for the peel). `E-PUNCTURE` at $q$
 deletes every row whose support contains $q$; a claim with $q \notin S$ is
 carried unchanged, no claim with $q \in S$ is derivable, and by I3 identifier
 injectivity of a well-formed input state no retired identifier whose input
 row contained $q$ names any output row, so $\mathsf{gen}_{i+1}(r,\sigma,S)$
 has no derivation for any $\sigma, S$ (the `W13` half for the puncture).
 `E-LOCAL-HADAMARD` ($T=Q$ or $T=\varnothing$) keeps every displayed row and
 swaps its sector when $T$ is non-empty; the claim keeps its identifier and
 support and follows the sector swap (design choice: under this command the
 claim keeps its identifier and changes sector). `P-REBASE` at sector $\tau$
 retires every old row of sector $\tau$, keeps every opposite-sector row, and
 mints fresh rows for sector $\tau$ outside $\mathsf{used}$; a claim of an
 opposite-sector row is carried unchanged, each minted row is a source, and
 by I3 identifier injectivity (excluding opposite-sector survivors) together
 with mint freshness (excluding minted rows), a retired identifier of sector
 $\tau$ names no output row, so $\mathsf{gen}_{i+1}(r,\sigma,S)$ has no
 derivation for any $\sigma, S$ (the `W13` half for the rebase). *Decidability
 re-check (per the 2026-10-20 diary obligation).* For the extended `Ann.gen`
 inventory (kernel, `E-GRAFT`, and the five Gate 6 commands), the rule set is
 finite, every state's display and `used` set are finite, and every transport
 row strictly decreases chain position $i$ in its premise while source rows
 have no `Ann.gen` premise; each step has only finitely many premises, because
 a shortened support $S'$ is drawn from $S'$ or $S' \cup \{q\}$ and a swapped
 sector from a single sector; derivation search for $\mathsf{gen}_i(r,\sigma,S)$
 therefore terminates in at most $i$ steps, so failure to close remains a
 decidable refutation on the extended inventory. On a well-formed trace the
 same conclusion follows from `derives_gen_iff_displayed_of_trace` (Lean,
 `SeamChains.lean`), which reduces it to a membership test on the display.
 $\square$
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
and, for every measure, `not_derivable_mixed_eq`). Mechanization,
2026-11-11: the generator-referencing claim is `Ann.gen` with
the rows `Derives.genMint`, `genSkip`, `genDelete`, and `genAdd`, proved
sound in `judgment_soundness` and carried through `Derives.weaken` and
`Derives.shift`; the `W13` half's derivation-level instance is
`not_derivable_gen_of_deleted`, and on one parent the claim transports
across the deletion of another generator
(`derives_gen_across_other_deletion`) and has no derivation across its own
(`not_derivable_gen_across_own_deletion`). Mechanization, 2026-11-11: the input-display rule is `Derives.genInput` and the graft's rows are
`Derives.genGraft` and `Derives.genGraftMint`, proved sound in
`judgment_soundness` and carried through `Derives.weaken`; the graft's
refusal is `not_derivable_gen_of_grafted`; `Derives.shift` is restated for
sentences that are not generator-referencing claims, and `Derives.shift_gen`
transports any derivation under the seam condition `SeamRowsDerived`. The
Gate 6 rows for the claim are `Derives.genExtend`, `genExtendMint`,
`genPeel`, `genPuncture`, `genHadamard`, `genRebase`, and `genRebaseMint`,
with refusals `not_derivable_gen_of_peeled`,
`not_derivable_gen_of_punctured`, `not_derivable_gen_of_punctured_id`, and
`not_derivable_gen_of_rebased`. The
instances are an input row claimed, transported across an addition, and
refused across its own deletion
(`derives_gen_input_across_addition`,
`not_derivable_gen_input_across_own_deletion`), a graft with a shortened
row, a kept row, a minted row, and its two retired generators
(`derives_gen_graft_shortened`, `derives_gen_graft_kept`,
`derives_gen_graft_minted`, `not_derivable_gen_graft_chain`), and worked
instances for all five Gate 6 commands on `graftableState`
(`derives_gen_extend_kept`, `derives_gen_extend_minted`,
`derives_gen_peel_shortened`, `derives_gen_peel_kept`,
`not_derivable_gen_peel_retired`, `derives_gen_puncture_kept`,
`not_derivable_gen_puncture_retired`, `derives_gen_hadamard_swapped`,
`derives_gen_hadamard_empty`, `derives_gen_rebase_kept`,
`derives_gen_rebase_minted`, `not_derivable_gen_rebase_retired`).
Mechanization, 2026-11-12 (`lean/CodeCalculus/SeamChains.lean`)
and 2026-11-15: the seam condition on chains of single
(non-sequence) kernel, graft, and Gate 6 steps is
`derives_gen_of_displayed`, `seamRowsDerived_of_stepChain`, and
`derives_gen_iff_displayed`, with `Derives.shift_gen_of_stepChain`
the resulting unconditional shift. Mechanization, 2026-11-18:
`peelSupport_eq_graftSupport_of_eval` (`Soundness.lean`) proves `peelSupport`
agrees with `graftSupport` on surviving rows of `E-PEEL`;
`not_derivable_gen_of_punctured_id` and the strengthened
`not_derivable_gen_of_rebased` (`Transport.lean`) refuse any retired
punctured or rebased generator for arbitrary sector and support via I3
identifier injectivity; `stepChain_append`, `Trace.stepChain`,
`seamRowsDerived_of_prefix_stepChain`, `seamRowsDerived_of_trace`,
`Derives.shift_gen_of_trace`, and `derives_gen_iff_displayed_of_trace`
(`SeamChains.lean`) connect `StepChain` to `Trace` so the seam condition
discharges unconditionally on every command sequence trace, exercised on a
three-step `P-REBASE` / `E-LOCAL-HADAMARD` / `E-PEEL` chain
(`derives_gate6_seam_row3`, `derives_gate6_seam_row5`,
`not_derivable_gate6_seam_peeled_minted`). The record, with what is not
mechanized, is at `spec/OBLIGATIONS.md`, `OBL-JUDGMENT-TRANSPORT`, *Intended
mechanization status*.

## 4.12 — Graft transition soundness (`OBL-GRAFT-TRANSITION-SOUNDNESS`)

 Evidence, not machine-checked. The
well-formedness conclusion is mechanized as `wf_graftState`
(`lean/CodeCalculus/GraftWellFormedness.lean`, 2026-10-28) under
the transition's premises; the Lean proof derives I2 by counting ranks from the
$k'=k$ premise and the dimension bound (`ranksFit_of_wf`, `lean/CodeCalculus/RanksFit.lean`), which
forces both output sectors to full rank, rather than by the lifting argument
below, which is unchanged.

Let $S$ be well-formed and $\mathrm{E-GRAFT}(q,\tau,\vec r)$ applicable
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
 $q\in \mathrm{supp}(r_i)\cap\mathrm{supp}(r_{i+1})$, so its
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
`lean/CodeCalculus/PricedInterval.lean` (`priced_interval_soundness`,
2026-10-26) conditional on the distance laws this section derives and on price
truth as premises; witnesses, strict improvement, and `certify`/`prune` remain
outside this slice.

*Mechanization for the exact distance (2026-11-11).* The two
unpriced graft relations of this section are proved for the exact sector
distance in `lean/CodeCalculus/ExactGraft.lean`
(`exactDist_graft_relations`): the spliced sector's distance does not fall
and the opposite sector's does not rise. The direct-sum law
$d_\sigma(A \oplus B) = \min(d_\sigma(A), d_\sigma(B))$ is proved in
`ExactDirectSum.lean` (`exactDist_directSumState`) for states on disjoint
namespaces whose rows are supported on their own namespace, which is where
`C-DIRECT-SUM` and `E-GLUE` put their factors; it is false without those
two conditions. The addition law of `E-EXTEND` with $\Delta = \varnothing$
is proved in `Gate6Exact.lean` (`exactDist_extend_nil`), through the
invariance of the exact distance under a reordering of the namespace
(`ExactPermute.lean`, `exactDist_perm`), since the extension re-sorts it.
With these, `gate6_interval_soundness_exact` has no hypothesis about a
distance left. Two premises of the `E-GLUE` statement are kept by decision
and are not missing proofs: the seam certificate's equality, which is the
hypothesis of the certified cell (`JUDGMENT_LAYER.md` §2e) and is used only
when the certificate is supplied, and the glued state's well-formedness,
which is a premise of the §4.31 transition.

*Instance reading ( 2026-10-27).* Each bullet below verifies soundness for
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
- *`C-DELETE-CHECK` (priced, sector-split, 2026-11-18).* The
 deletion price is sector-specific: the deleted sector $\tau$ gets
 $d'_\tau=\min(d_\tau,w_{\rm del})$ and the opposite sector
 $\bar\tau$ gets $d'_{\bar\tau}=\min(d_{\bar\tau},w_{\rm exp})$,
 with $d'=\min(d,w_{\rm del},w_{\rm exp})$. The interval becomes, in
 sector $\tau$, $[\min(L_\tau,w_{\rm del}),\min(U_\tau,w_{\rm del})]$,
 in sector $\bar\tau$,
 $[\min(L_{\bar\tau},w_{\rm exp}),\min(U_{\bar\tau},w_{\rm exp})]$,
 and in the full distance
 $[\min(L,w_{\rm del},w_{\rm exp}),\min(U,w_{\rm del},w_{\rm exp})]$,
 each of which contains the corresponding exact distance by construction.
 The unpriced non-increase argument still covers the unpriced rule.
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
  priced bullet needs. (dated derivation, 2026-10-21.)

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
is added here, and none is owed for this obligation to read as proved. The consumer's reset rows for `E-PUNCTURE` (and the `E-PEEL`
full-distance lower endpoint and selected-sector upper endpoint) are sound by
construction (a reset interval contains every distance); the admitted
`E-PEEL` carries (selected-sector lower, opposite-sector upper,
full-distance upper) are sound by the §4.28 inequalities, and the
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
$V\mapsto V\setminus\{c:r\in\mathrm{Ref}(c)\}$. The composition over
$S=\{r_1,\dots,r_t\}$ is
$(f_{r_t}\circ\cdots\circ f_{r_1})(V)=V\setminus\bigcup_{r\in S}\{c:r\in
\mathrm{Ref}(c)\}$, which makes set-level commutativity and idempotence
immediate from set difference. Hence the transported context depends only on the
deleted-identifier set $S$, not on enumeration order. $\square$

## 4.16 — Row-replacement factorization, loop part (`OBL-ROW-REPLACEMENT-FACTOR`)

 Evidence, not machine-checked; re-derived in Lean (`KernelObligations.lean`). Only the delete-then-add loop is proved here;
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
 1. Ambient membership (W22): $\mathrm{supp}(r+s)\subseteq Q$, since
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
 is exhausted the construction is inapplicable. This is the capacity premise
 of the `C-ADD-CHECK` card, carried by the Lean rules since 2026-11-11, so the reachability statement is scoped to histories with at least
 as many unused identifiers as $C_1$ has displayed rows. The final
 displayed rows have the exact supports and sectors of $C_1$'s displayed rows
 (all in $\mathbb{F}_2^Q$), with canonically minted identifiers; row spaces
 match. Exact labeled reachability and $\mathsf{used}$-set equality are not
 claimed.

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
identifier allocation. Each loop also mints one identifier, so the generation statement is scoped,
like §4.17, to histories with remaining capacity: past the enumeration's
capacity the add step of a loop is inapplicable (capacity premise). Hence the core moves generate all basis changes
of a fixed-dimensional row space within capacity. $\square$



## 4.19 — Reproduced derivations for the conditional construction cells

Hand derivations, reproduced from
the code-deformation manuscript (`PROOFS.md`) (Theorem 12.1 / manuscript
Theorem 7, Proposition 18.3, Theorem 28.1–28.3) and adapted to this
repository's CSS state model and vocabulary. Evidence, not machine-checked.

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

**Sector split ( 2026-11-18).** Deleting a $\tau$-check
leaves the opposite stabilizer span $S_{\bar\tau}$ unchanged, and,
symmetrically, the deleted sector's normalizer $N_\tau(S)$ is unchanged:
the normalizer of $\tau$ is cut out by the rows of the other sector, which
are untouched by a $\tau$-deletion. The promoted stabilizers are $\tau$-type
and become $\tau$-logicals, so the newly introduced logicals in the deleted
sector are exactly the promoted ones:
$d'_\tau=\min(d_\tau,w_{\mathrm{del}})$. The newly exposed normalizer
vectors are $\bar\tau$-type and become $\bar\tau$-logicals, so the newly
introduced logicals in the opposite sector are exactly the exposed ones:
$d'_{\bar\tau}=\min(d_{\bar\tau},w_{\mathrm{exp}})$.
The full distance is $d'=\min(d'_\tau,d'_{\bar\tau})
=\min(d,w_{\mathrm{del}},w_{\mathrm{exp}})$, recovering the three-class
minimum above. $\square$

The two sector minima agree with the earlier all-Pauli reading: a Pauli in
$S\setminus S'$ has a $\tau$-part that is itself in the $\tau$-span and
outside the child's, of no larger weight, so the promoted minimum is the
same; a Pauli in $N(S')\setminus N(S)$ has an other-sector part that is
itself exposed, of no larger weight, so the exposure minimum is the same.
$\square$

### Proposition 18.3 (strict improvement) — reproduced

Setting: stabilizer $S$, add $r$ independent commuting Paulis $A$ with
$S'=S+\langle A\rangle$, $k'=k-r$, killed span $K=S+\langle A\rangle$ over
$S$.

By Proposition 18.2, $d'=\min\{\mathrm{wt}(g):g\in N(S),\ g\in A^\perp,\
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
\mathrm{popcount}(E\cap(c\setminus\{q\}))
=\mathrm{popcount}(E\cap c),
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
(`machine/experiments/priced_conformance_harness.py`, `exact_distances`). The
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
 $q\in\mathrm{supp}(a_i)\cap\mathrm{supp}(a_{i+1})$, and let
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
 carrying a two-dimensional layout, at the pinned commit 9d30c66a, 823 grafts
 are applicable and 198 of them increase the radius, the largest observed
 ratio being $r'/r=1.6125$ (`machine/experiments/layout_graft_survey.py`;
 report `machine/experiments/layout_graft_survey.json`, reproduced
 2026-11-10). The survey is evidence, never confirmation; what it shows is
 that the naive monotonicity is refuted by example, and the factor-of-two
 bound is what survives.

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

**Extension transitions (added 2026-11-10).** The layout cells of
[`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2d.5 for the transitions admitted
after the derivation above rest on two observations already used for the
graft: removing a point from a support cannot increase its diameter, and a
maximum over a subset is no larger than the maximum over the set. As above,
$\lambda'=\lambda\vert_{Q'}$ for a child namespace $Q'$, and every exact value
is a recomputation over the child's display that needs no hypothesis.

- **`E-PEEL` at $q$** (§4.28). $Q'=Q\setminus\{q\}$. The peeled row is
 retired, the other selected-sector rows are $q$-free and unchanged, and every
 opposite-sector row is shortened at $q$. Each child row's support is a subset
 of some parent row's support, so its diameter in $\lambda'$ is at most that
 row's diameter in $\lambda$, which is at most $r$; taking the maximum over
 the child's rows gives $r'\le r$.
- **`E-PUNCTURE` at $q$** (§4.29). $Q'=Q\setminus\{q\}$ and only the $q$-free
 rows survive, each unchanged. The child's display is a subset of the
 parent's, so $r'\le r$.
- **`E-LOCAL-HADAMARD` at $T=Q$** (§4.27). The namespace and every support
 are unchanged; only the sector labels swap. The set of supports is the same,
 so $r'=r$.
- **`P-REBASE`** (§4.26). The namespace and the layout are unchanged, and the
 selected sector's rows are replaced by $\mathbb{F}_2$-combinations whose
 supports are symmetric differences of the old supports. The exact value is
 the recomputation, and no direction holds. On the three-qubit state with
 $X$ rows $\{0,1\}$ and $\{1,2\}$, an empty $Z$ display, and the qubits at
 $0$, $1$, and $2$ on a line, the mix with rows $(1,1)$ and $(0,1)$ replaces
 $\{0,1\}$ by $\{0,2\}$ and raises the radius from $1$ to $2$; the same mix
 applied to the result replaces $\{0,2\}$ by $\{0,1\}$ and lowers it back to
 $1$. Both directions occur, so the cell records none.
- **`E-EXTEND`** (§4.30). With $\Delta=\emptyset$ the transition appends
 `C-ADD-CHECK` rows over $Q$, and the `C-ADD-CHECK` cell applies once per
 added row. With $\Delta\neq\emptyset$ the parent's layout covers $Q$ only,
 so the child has a radius only when a layout $\lambda'$ on $Q\cup\Delta$ is
 supplied. The cell reads the parent's radius $r$ in $\lambda$, so the old
 rows must keep their diameters, which holds exactly when $\lambda'$ agrees
 with $\lambda$ on $Q$; the cell takes that agreement as its premise. Under
 it, $r'=\max(r,\max\{\mathrm{diam}_{\lambda'}(s):s\in\mathit{rows}'_{\rm new}\})\ge r$.
- **`E-GLUE`** (§4.31). The state update is the direct-sum update followed by
 one canonically minted row per seam check, so the layout is the two factor
 layouts blockwise, as for `C-DIRECT-SUM`, with a merged layout supplied, and
 the radius is the direct-sum cell followed by one `C-ADD-CHECK` cell per
 seam check: $r=\max(r_A,r_B,\max\{\mathrm{diam}(s):s\ \text{a seam row}\})$,
 with every diameter read in the merged layout, so $r\ge\max(r_A,r_B)$.

**Honesty under restriction.** If $\lambda$ is honest, at most $\rho$ qubits
per site and distinct sites at least $1$ apart, then so is $\lambda\vert_{Q'}$
for every $Q'\subseteq Q$: removing qubits can only lower a site's occupancy,
and removing sites can only raise the least distance between distinct sites.
This is the honesty cell of `E-GRAFT`, `E-PEEL`, and `E-PUNCTURE`. For the
transitions that leave the layout unchanged (`C-SKIP`, `C-DELETE-CHECK`,
`C-ADD-CHECK`, `E-LOCAL-HADAMARD`, `P-REBASE`, and `E-EXTEND` with
$\Delta=\emptyset$) the cell is immediate, since honesty is a property of the
layout alone. The blockwise merge of `C-DIRECT-SUM` and `E-GLUE` and the
supplied layout of `E-EXTEND` are not restrictions of the parent's layout:
two honest summands can share a site or sit closer than $1$ once merged, and
a new qubit can be placed on a full site. Their cells are therefore
conditional on the honesty of the merged or supplied layout.

**Evidence, not confirmation.** The randomized layout-conformance harness
(`machine/experiments/layout_conformance_harness.py`) transits every
transition on random small states and layouts, checks each cell's direction,
formula, and honesty claim in exact arithmetic, and compares the consumer's
own layout transport with the cells. A run with no violation fails to falsify
the cells and establishes nothing beyond the derivations above.

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

 Evidence, not machine-checked; re-derived in Lean (`KernelObligations.lean`). Discharges `OBL-DERIVED-TERM-FACTORIZATION`.

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
judgments** and never to operation contracts .
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

**Mechanized checker.** The checker of
`lean/CodeCalculus/CertificateChecker.lean` has this keying: its
soundness theorems conclude a fact about one state term, with the sector
distance as the property and one sector, and no premise or conclusion
mentions a command or a second state. It does not mechanize route-scoping.

**What this does not settle.** Whether the keying above is the intended one,
whether a checker must additionally discharge a non-derivability proof, and
whether `certificate-checked` ever gains a second (operation-contract) variant.
These remain Gate 5 decisions. $\square$ (discharge)

## 4.25 — Presentation conjugation (`OBL-PRESENTATION-CONJUGATION`)

 Evidence, not machine-checked; re-derived in Lean (`KernelObligations.lean`). Discharges `OBL-PRESENTATION-CONJUGATION`.

Let $\sigma$ be a permitted qubit relabeling: a bijection on the qubit
namespace $Q$ that transports the display (qubits, displayed rows, sector
labels) and leaves identifiers and the $\mathsf{used}$ set untouched, so that
$S\approx \tilde S$ with $\tilde S=\sigma S$. Presentation equivalence
transports qubits and displayed rows but not identifiers
([`TAXONOMY.md`](TAXONOMY.md) §1.4); $\sigma$ acts on supports and qubit
labels only. Supports are presented in increasing order by the display
contract, so a transported support is presented in the child's label order.

**Claim.** For every command $m$ in the MVP kernel and every state $S$:
$$\mathrm{Eval}(m,S,S') \iff
\mathrm{Eval}(\sigma m,\tilde S,\widetilde{S'})$$
where $\sigma m$ is the transported command (support-transported for
additions, identifier-stable for deletions, pointwise for sequences), and
$\widetilde{S'}=\sigma S'$.

The proof is by structural induction on the evaluation derivation. Each
clause below checks that every premise of the rule is invariant under
$\sigma$ and that the conclusion state transports.

- **`C-SKIP`.** $\mathrm{Eval}(\mathsf{skip},S,S)$ holds iff
 $S'=S$. Under $\sigma$, $\mathrm{Eval}(\mathsf{skip},\tilde S,\tilde S)$
 holds iff $\widetilde{S'}=\tilde S$, i.e. $\sigma S'=\sigma S$, i.e.
 $S'=S$ since $\sigma$ is a bijection. $\square$ for skip.

- **`C-DIRECT-SUM` (expression level).** For $\oplus$, a global bijection
 preserves disjointness:
 $\sigma Q_A\cap \sigma Q_B=\sigma(Q_A\cap Q_B)$, and $\mathsf{used}$ is
 untouched by $\sigma$, so $\mathsf{used}$-disjointness is label-invariant.
 Hence $\mathrm{EvalExpr}(e_1\oplus e_2,S)$ iff
 $\mathrm{EvalExpr}(\sigma(e_1\oplus e_2),\tilde S)$, with output
 $\widetilde{S_1\oplus S_2}=\tilde S_1\oplus \tilde S_2$. Per-summand
 relabelings compose with the summand embedding; relabelings cutting across a
 summand boundary are outside the congruence's scope ( scoping). $\square$
 for direct sum.

- **`C-DELETE-CHECK`.** Premises:
 1. $\mathrm{DisplayedGenerator}(r,S)$: $r$ names a live row of $S$.
 The row set transports bijectively and identifiers are untouched, so $r$
 names a live row of $\tilde S$. Conversely the same map back.
 2. $\mathrm{IndependentGenerator}(r,S)$: $r$'s vector is not in the
 span of the other rows in its sector. Linear span membership is invariant
 under the coordinate permutation $\sigma$ on qubit labels, so independence
 transports in both directions.
 Conclusion: $\mathrm{deleteState}(S,r)$ removes the row with id $r$
 and leaves $\mathsf{used}$ unchanged. Since $\sigma$ commutes with filtering
 by id, $\sigma(\mathrm{deleteState}(S,r))=
 \mathrm{deleteState}(\tilde S,r)$. Thus
 $\mathrm{Eval}(\mathrm{delete}_r,S,S')$ iff
 $\mathrm{Eval}(\mathrm{delete}_r,\tilde S,\widetilde{S'})$,
 with the same identifier $r$ on both sides (identifier-stable).
 $\square$ for deletion.

- **`C-ADD-CHECK`.** The transported command is
 $\mathrm{addStab}_{\sigma r}$, where $\sigma r$ is the transported
 support. Premises:
 1. $\mathrm{supportSubset}(r,Q)$: $\sigma$ maps $Q$ to $\tilde Q$, so
 $\sigma r\subseteq \tilde Q$.
 2. $r.\mathrm{Nodup}$ and $r$ sorted: $\sigma$ is injective, so nodup
 transports; sortedness is re-presented in the child's label order by the
 display contract.
 3. Commutation: for every opposite-sector row $x\in S$,
 $\mathrm{supportIntersectionSize}(r,x.\mathrm{support})\bmod 2=0$.
 $\sigma$ is a bijection, so
 $|\sigma r\cap \sigma x.\mathrm{support}|=|r\cap x.\mathrm{support}|$;
 parity is preserved for every transported opposite-sector row.
 4. Independence:
 $\neg\mathrm{inSpanRows}(S.Q,\mathit{sectorRows}(S,\tau),
 \mathrm{rowVector}(S.Q,\langle\mathrm{mint}(\mathsf{used}),\tau,r\rangle))$.
 Coordinate permutation $\sigma$ preserves span membership, and
 $\mathrm{mint}(\mathsf{used})$ is unchanged because $\sigma$ does not
 touch $\mathsf{used}$ (identifiers are not qubit labels), so the minted
 identifier agrees on both sides.
 Conclusion: $\mathrm{addState}(S,\tau,r)$ appends a row with id
 $\mathrm{mint}(\mathsf{used})$, sector $\tau$, support $r$, and updates
 $\mathsf{used}$. Transporting gives $\mathrm{addState}(\tilde S,\tau,
 \sigma r)$ with the same minted id and $\mathsf{used}$, so
 $\widetilde{S'}=\mathrm{addState}(\tilde S,\tau,\sigma r)$.
 Hence $\mathrm{Eval}(\mathrm{addStab}_{r:\tau},S,S')$ iff
 $\mathrm{Eval}(\mathrm{addStab}_{\sigma r:\tau},\tilde S,\widetilde{S'})$.
 The transported command **must** be used: with the same command
 $\mathrm{addStab}_{r:\tau}$ on both sides the congruence fails for
 additions, as the witness shows (swap of qubits 1 and 2 makes an
 $X$-addition applicable on $S$ but not on $\sigma S$ because the
 commutation parity changes). $\square$ for addition.

- **`C-SEQUENCE`.** By induction on the two sub-derivations: if
 $\mathrm{Eval}(m_1,S,S_1)$ iff
 $\mathrm{Eval}(\sigma m_1,\tilde S,\widetilde{S_1})$ and
 $\mathrm{Eval}(m_2,S_1,S')$ iff
 $\mathrm{Eval}(\sigma m_2,\widetilde{S_1},\widetilde{S'})$, then
 $\mathrm{Eval}(m_1;m_2,S,S')$ iff
 $\mathrm{Eval}(\sigma m_1;\sigma m_2,\tilde S,\widetilde{S'})$.
 $\square$ for sequences.

- **`E-GRAFT` (extension).** The graft is not in the MVP kernel statement's
 scope, but the same transported-command pattern applies: the grafted qubit
 transports to $\sigma q$; touching rows transport bijectively; the chain
 order is preserved up to the bijection on identifiers; coverage, sortedness
 of minted supports, and $\mathsf{stateK}$ preservation are all invariant
 under coordinate permutation $\sigma$ (bitmask rank is invariant under
 column permutation) and under identifier-stable minting ($\mathsf{used}$
 unchanged). Hence the graft clause transports with command
 $\mathrm{graft}_{\sigma q,\tau,\sigma(\vec r)}$. $\square$ for graft.

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
machine-checked proof; re-derivation target is the generic-core slices. The distance
identity is machine-checked for the exact sector distance
(`exactDistance_rebaseState`, `lean/CodeCalculus/Gate6Soundness.lean`); the rank identity is `sectorRank_rebaseState`
(`lean/CodeCalculus/RebaseRankSector.lean`).

**Set-up.** In a well-formed presented CSS state the displayed $\tau$-rows of a
sector $V_\tau=(v_1,\ldots,v_m)$ are independent (I2) and span the sector's
row space (reading (A) of D-3: $X=\langle \mathit{rows}_X\rangle$ by
construction). The command $\mathrm{rebase}_{\tau;M}$ names a matrix
$M\in\mathbb{F}_2^{m\times m}$; the registered output replaces each $v_i$ by
$v_i'=\bigoplus_j M_{ij}v_j$ with canonical mint identifiers, $m$ of them, under
the capacity premise of the `C-ADD-CHECK` card: a history that
cannot mint $m$ more identifiers makes the rebase inapplicable. (Sterile technicality:
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
machine-checked proof. The distance exchange is machine-checked for the
exact sector distance (`exactDistance_swapState`,
`lean/CodeCalculus/Gate6Soundness.lean`).

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

**Not claimed.** The term-$\mathrm{hadamard}_T$ general instance
($\varnothing \subsetneq T \subsetneq Q$) — §2.12's record splits along both
row spaces under the review-dispositioned condition — is **not** admitted here: a
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
D-3 reading (A), its entire row space $\sigma$-span — lies inside the
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

The admission was ratified 2026-11-06: the selected sector's
lower endpoint carries ($d_\tau'\ge d_\tau$) and the opposite sector's
upper endpoint carries ($d_{\bar\tau}'\le d_{\bar\tau}$); the full distance's
upper endpoint carries the opposite sector's upper bound, since
$d'=\min(d_X',d_Z')\le d_{\bar\tau}'\le d_{\bar\tau}$, tightened by
child-valid witnesses. The comparison $d'\;\mathrm{vs.}\;d$ is bounded in
neither direction (the witness above). The pre-admission refusal (everything
resets) remains available as the opt-out mode `reset` in
`machine/priced_calculus.py`.

**The two sector relations are exact (added 2026-11-10).** The
two maps in the inequalities above are bijections, and reading them as such
gives each sector's child distance exactly, in terms of the parent's logicals
and the peeled qubit. Write $L_\tau(C)$ for the parent's $\tau$-logicals and
$L_\sigma(C)$ for its $\sigma$-logicals, and recall that $r$ is the unique
displayed $\tau$-row containing $q$.

- *Selected sector.* Padding a child $\tau$-logical with $0$ at $q$ gives a
 parent $\tau$-logical avoiding $q$ (shown above), and restricting a parent
 $\tau$-logical $v$ with $v_q=0$ gives a child $\tau$-logical: $v\perp
 S_\sigma$ implies $v|_{Q'}\perp S'_\sigma$ because the child's $\sigma$-rows
 are the parent's restricted at $q$ and $v_q=0$, and $v|_{Q'}\in S'_\tau$
 would put $v\in S_\tau$ since the surviving $\tau$-rows are $q$-free. The
 two maps are inverse and preserve weight, so the child's $\tau$-logicals are
 the $q$-free parent $\tau$-logicals, and
 $$d_\tau(C')=w_{\mathrm{avoid},\tau}(q):=\min\{|v|:v\in L_\tau(C),\ v_q=0\},$$
 the **avoidance minimum**. It is finite whenever $k\ge 1$ ($v+r$ avoids
 $q$ for any parent $\tau$-logical $v$ through $q$), it is at least $d_\tau$,
 and it equals $d_\tau$ exactly when some minimum-weight parent
 $\tau$-logical avoids $q$.
- *Opposite sector.* Restriction takes a parent $\sigma$-logical $u$ to a
 child $\sigma$-logical of weight $|u|-u_q$ (shown above). Conversely a
 child $\sigma$-logical $y$ lifts to the parent $\sigma$-logical
 $\tilde y$ with $\tilde y_q=\langle y,r|_{Q'}\rangle$: the lift is
 orthogonal to $r$ by construction and to the $q$-free $\tau$-rows because
 $y$ is, and $\tilde y\in S_\sigma$ would put $y\in S'_\sigma$. The two
 maps are inverse, so
 $$d_\sigma(C')=\min\{|u|-u_q:u\in L_\sigma(C)\}=\min\bigl(d_\sigma,\ w_{\mathrm{expose},\sigma}(q)\bigr),$$
 with $w_{\mathrm{expose},\sigma}(q)=\min\{|u|-1:u\in L_\sigma(C),\ u_q=1\}$
 ($+\infty$ if none), the **exposure price** of
 [`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2c bound to the peel. This is
 the graft's non-spliced relation of §4.13 at $m=1$, as the opening of this
 paragraph already says the peel is, and its corollary is unpriced:
 $$d_\sigma-1\le d_\sigma(C')\le d_\sigma,$$
 with $d_\sigma(C')=d_\sigma-1$ exactly when some minimum-weight parent
 $\sigma$-logical contains $q$.

On the witness above ($Q=\{0,1,2\}$, $X$ display $\{0,1\}$, $Z$ display
$\{0,1,2\}$, peel $q=2$ in sector $Z$): the parent $Z$-logicals are $\{2\}$
and $\{0,1\}$, so $w_{\mathrm{avoid},Z}(2)=2$; the parent $X$-logicals are
$\{0,2\}$ and $\{1,2\}$, both through $q$, so $w_{\mathrm{expose},X}(2)=1$
and $d_X(C')=\min(2,1)=1$. Both agree with the direct computation $(1,2)$.

The two relations give the **sector-aware price cells** of
[`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2a, each conditional on its
consumer-supplied minimum: the avoidance minimum pins the selected sector to
$[w_{\mathrm{avoid},\tau},w_{\mathrm{avoid},\tau}]$, and the exposure price
moves the opposite sector's interval $[L_\sigma,U_\sigma]$ to
$[\min(L_\sigma,p),\min(U_\sigma,p)]$ exactly as the graft price does. They
also sharpen the unpriced transport: the opposite sector's lower endpoint
carries as $L_\sigma-1$ (floored at $0$), and the full distance, which is
$\min(d_\tau',d_\sigma')$, takes both endpoints as the minima of the two
sector intervals, so $d'\ge\min(L_\tau,L_\sigma-1)\ge d-1$ while the
comparison with $d$ itself stays unbounded in both directions. Soundness of
the transformer is derived in §4.32; the priced cells and the unpriced
sharpening are mechanized in `lean/CodeCalculus/Gate6Soundness.lean`
(`peelLedger`, `peel_transformer_sound`) conditional on the three relations
above as hypotheses, and the three relations are machine-checked for the
exact sector distance in `lean/CodeCalculus/ExactPeel.lean`
(`exactDist_peel_relations`, 2026-11-11), by the padding,
restriction, and parity-lift maps of the two sector arguments above; the
instance with no distance hypothesis is `peel_transformer_sound_exact`.
The relations are checked on random peels against the exhaustive oracle by
the priced-conformance harness (`machine/experiments/priced_conformance_harness.py`,
unpriced and priced, with the prices computed by the oracle as a consumer's
would be by its own enumeration) and on worked states in
`machine/test_peel_prices.py`; these are empirical aids that falsify nothing
here and prove nothing.

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

**The reduction, recorded (2026-11-10).** The disposition of
2026-11-10 asked either for sector-aware price cells or for the reduction
that keeps the refusal honest; for the puncture it is the reduction. A
puncture at $q$ is the composite of two moves the calculus already has:
first the deletion of every displayed row containing $q$, in either sector
(a `C-DELETE-CHECK` sequence, $t_X+t_Z$ steps, after which $q$ is touched by
no row and is a free qubit of the intermediate code $C_q$), and then the
removal of that free qubit, which is the projection onto the other factor of
the direct sum $C_q=C'\oplus(\text{free }q)$. The second step is the step
that makes the price a hole price: the free qubit contributes the weight-one
logicals $e_q$ in both sectors, so $d(C_q)=1$ whatever the parent was, and
removing it leaves, in each sector,
$$d_\sigma(C')=\min\{|v|:v\in L_\sigma(C_q),\ v_q=0\}=w_{\mathrm{avoid},\sigma}^{C_q}(q),$$
the avoidance minimum of the intermediate code at $q$. Since
$L_\sigma(C_q)\supseteq L_\sigma(C)$ (deleting rows only exposes
operators), this is $\min\bigl(w_{\mathrm{avoid},\sigma}(q),\
w_{\mathrm{hole},\sigma}(q)\bigr)$, where $w_{\mathrm{avoid},\sigma}(q)$ is
the parent's avoidance minimum of §4.28 and $w_{\mathrm{hole},\sigma}(q)$ is
the least weight of a $q$-free operator that the deleted rows expose (one
that commutes with the surviving rows of the opposite sector but not with
some deleted one, or that lies in the parent's $\sigma$-span but not in the
survivors'). The first term bounds the child from above once supplied; the
second term is the hole price, and it has no unpriced bound in either
direction: the unnamed-qubit instance above raises $d_X$ from $1$ to $2$,
and on $Q=\{0,1,2\}$ with the $Z$ display $\{0,1\},\{1,2\}$ and no $X$ row,
puncturing $q=2$ deletes the row $\{1,2\}$ and lowers $d_X$ from $3$ (the
only parent $X$-logical is $\{0,1,2\}$) to $2$ (the child $X$-logical
$\{0,1\}$). Both directions therefore occur, no unpriced endpoint carries,
and the reset of `JUDGMENT_LAYER.md` §2b stands. A conditional price cell
of the deletion shape, $d_\sigma(C')$ exact under supplied
$w_{\mathrm{avoid},\sigma}$ and $w_{\mathrm{hole},\sigma}$, is what the
reduction licenses once the hole price can be supplied with a justified
lower bound; that is the D2 question, and the cell is not admitted here.
The reduction is checked on the two instances above and on a third by
`machine/test_peel_prices.py` (an empirical aid, not a proof).

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
lies in every span and fails (i) outright). Each addition mints one
identifier, under the capacity premise of the `C-ADD-CHECK` card.

**Ambient membership (W22).** The ambient grows to $Q\cup\Delta$ *before*
the first addition, and every added support is checked to be a subset of
$Q\cup\Delta$ (the $W22$ reading); surviving and minted rows all have
support in $Q\cup\Delta$. The complement reading of `W22` is stated
explicitly here: complements are taken inside $\mathbb{F}_2^{Q\cup\Delta}$.

**Output I1–I5.** Cumulative: §4.7's $\mathrm{addStab}$ instance —
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
$C$-$\mathrm{ADD}$-$\mathrm{CHECK}$ sequence in the ambient the
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
its used set is that union together with the minted seam identifiers, one per
seam check, under the capacity premise of the `C-ADD-CHECK` card.
The seam checks are the only new rows; no factor row
is removed or altered. Well-formedness (I1–I5) is preserved by the same
arguments as `C-DIRECT-SUM` plus the independence premises above (each new row
is independent and commutes with the opposite sector by construction). In the Lean development this update is both the binary state-expression
constructor `StateExpr.glue` (rule `EvalExpr.glue`, `TERM_LANGUAGE.md` §1–§2;
binary-only, no unary command production, decided 2026-11-18) and
the direct sum followed by the seam additions in order, the closed term
`⟨glueCommand seams, directSum (base A) (base B)⟩`
(`lean/CodeCalculus/Gate6Soundness.lean`). The two are proved
equivalent on every pair of well-formed factors, deriving
`EncodingWellFormed (glueState a b seams)` from step-by-step seam
admissibility and `stateK (directSumState a b) = stateK (glueState a b seams) + seams.length`
(`evalExpr_glue_iff_evalTerm_glueCommand`, `wf_glueState_of_eval_glueCommand`,
`stateK_glueState_add_seams` in `lean/CodeCalculus/GlueExtraction.lean`).

**Ambient membership (W22).** The child's qubit set is $Q_A\cup Q_B$.
Factor rows retain their supports in $Q_A$ or $Q_B$ (hence in the union), and
every seam check is typed with $\mathrm{supp}\subseteq Q_A\cup Q_B$ and
rejected otherwise (no-derivation at the term level, malformed at the encoding
for a state carrying such a row). No row leaves $\mathbb{F}_2^{Q_A\cup Q_B}$.

**Distances.** No distance relation is admitted beyond the §2e conditional
cell: the §2f cell's carries-when hypothesis (the seam certificate) is the
only license; the logical-witness field and boundary/edge-label field are
defined as future-$\Pi$ type sketches (`STATE_MODEL.md` §1/§1a). Lower endpoints are sound without a certificate,
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
likewise **not** admitted (obstruction, `DERIVED_RELATIONS.md`). Upper
endpoints come only from witnesses that revalidate in the child.

**What this does not settle.** The initial 2026-10-27 transition derivation did
not define the logical-witness field (`TAXONOMY.md` §2.10) or settle
composition-distance exactness (Theorem 4 / claim 7.4 of
*composition-distance*); both were subsequently addressed below (2026-11-11; `STATE_MODEL.md` §1/§1a). Sound admission for
`E-GLUE` is discharged under the stated hypotheses (§4.32). ∎

**Instance-wise equality through a surviving witness (added 2026-11-10).** The equality half of the §2e cell can be read per instance
from what this section already has, with no certificate. Let the factor
$C_A$ attain the minimum, so that $d_Z(C_A)=\min(d_Z(C_A),d_Z(C_B))$, and
let $u$ be a $Z$ witness of $C_A$ of weight $d_Z(C_A)$ in the sense of
[`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2c: a support that commutes with
every $X$ row of $C_A$ and lies outside its $Z$ span. Whether $u$ is still a
$Z$ logical of the glued state $C$ is decided by finite-field linear algebra
in $C$: it must commute with every $X$ seam check, and the $Z$ seam rows must
not have pulled it into the glued $Z$ span. When it is, the witness semantics
of §2c give $d_Z(C)\le|u|=\min(d_Z(C_A),d_Z(C_B))$, and with the lower bound
of the repair above, $d_Z(C)=\min(d_Z(C_A),d_Z(C_B))$ for that instance.
Nothing beyond §2c and the repair is used. What the seam certificate adds is
the guarantee of survival for a family (planar seams with equal move words)
without exhibiting the witness; that guarantee is the Theorem 4 / claim 7.4
hypothesis, and it stays a hypothesis here. The promotion accepted
2026-11-10 therefore needs exactly a survival
statement, which factor representatives remain logical across the seam, and
that is the content the logical-witness field of
[`TAXONOMY.md`](TAXONOMY.md) §2.10 carries under `E-GLUE`
(`STATE_MODEL.md` §1, 2026-11-11; `E-GLUE` contract-index row moved to
`transition-defined`). The consumer realizes the instance route:
`DistanceLedger.glue` carries both factors' witnesses into the glued child
and keeps those that revalidate there, so the $X$ and full upper endpoints,
which the certificate never licenses, come from surviving factor witnesses,
and a surviving minimum-weight $Z$ witness closes the $Z$ interval without
the certificate's claim. A factor witness that meets a seam check of the
opposite sector in an odd number of qubits, or that a seam row turns into a
stabilizer, is dropped, which is why the factors' witnesses enter the child
as candidates and never as current witnesses.

**Attempted family-level derivation of the §2e equality under admissible
(planar) seams (added 2026-11-11, maintainer decision to derive
in §4).** The maintainer asked whether the instance-wise route above can be
lifted to a family statement for admissible seams (equal move words, §2e).
The lift would need: for an admissible seam, every minimum-weight $Z$ witness
of the factor attaining the minimum survives the seam — commutes with every
$X$ seam check and is not pulled into the glued $Z$ span by the $Z$ seam
rows. By §4.33 statement 2, the glued $Z$-logical classes are the pairs of
factor classes commuting with the opposite-sector seam checks, modulo the
same-sector seam checks, and by statement 3 the equality holds exactly when a
pure pair of that weight survives. The lift therefore reduces to showing
that an admissible seam's $X$ seam checks do not anticommute with the
factor's minimum-weight $Z$ witness and that its $Z$ seam rows do not absorb
it.

That showing is not available from the state model. The state $C=(Q,X,Z,
\mathsf{pres},\mathsf{used})$ carries no geometry, planarity, or interface
label (the logical-witness field of `TAXONOMY.md` §2.10 is the designated
carrier and remains `not-yet-defined` by the maintainer's decision to keep it
deferred, 2026-11-11). Whether an $X$ seam check anticommutes with a factor
$Z$ witness depends on how the seam's checks are supported on the factor's
qubits, which is exactly the survival statement the seam certificate
asserts; the move-word equality of §2e is a condition on the seam, not a
proof that the support pattern is compatible. The counterexample of §4.33
(an $X$ seam check supported on all four qubits of two one-row two-qubit
factors, which kills both weight-one $Z$ classes and gives $d_Z(C)=2$) is
not excluded by admissibility as stated: its move words can be chosen equal.
Admissibility as §2e defines it (equal move words plus an evidence
reference) therefore does not, by itself, guarantee survival, and the
equality cannot be derived from §4.31's lower bound and witness semantics
alone.

**Extraction of Theorem 4 / claim 7.4 (2026-11-11).** The
maintainer directed that Theorem 4 and claim 7.4 be extracted from
*composition-distance* rather than merely cited. The extracted content is:

- Theorem 4 (re-exposure bound, *composition-distance* §6.1, "Legacy MS
 Theorem 4", proven, intersection setting): for an intersection
 $P=A\times_C B$ with a common edge basis, in each sector $\sigma$,
 $d_\sigma(P)\ge \min(d_\sigma(A), d_\sigma(B), w_{\mathrm{re},\sigma})$,
 where $w_{\mathrm{re},\sigma}$ is the least weight of a class that is
 trivial in at least one factor. A nontrivial class either becomes trivial
 in a factor (costing at least $w_{\mathrm{re},\sigma}$) or remains
 nontrivial in both (costing at least both factor distances).
- Claim 7.4 (gluing theorem, pullback, split dual,
 *composition-distance* CLAIMS.md row 7.4, "proven (packaging)"): restates
 Theorem 4 as $d(A\times_C B)\ge \min(\min(d_A,d_B),w_{\mathrm{re-exposed}})$,
 the mechanism being re-exposed cycles rather than 2-cell rerouting.

Under the admissible seam of §2e (equal move words), the seam checks are
symmetric along the interface and no factor representative is re-exposed:
$w_{\mathrm{re},Z}=\infty$ for the glued code, so Theorem 4 reduces to
$d_Z(Q)\ge \min(d_Z(C_A),d_Z(C_B))$. With the lower bound of §4.31
($d_Z(Q)\ge \min(d_Z(C_A),d_Z(C_B))$) and the upper bound from a
surviving minimum-weight factor witness (§2c), the equality
$d_Z(Q)=\min(d_Z(C_A),d_Z(C_B))$ holds for admissible seams, conditioned
on survival of the factor representative — which is exactly the survival
statement the logical-witness field carries.

**Conclusion.** The family-level guarantee for admissible seams is split by
Theorem 4 / claim 7.4 of *composition-distance*: Theorem 4 supplies the
unconditional lower half ($w_{\mathrm{re},Z}=+\infty$, hence
$d_Z(Q)\ge \min(d_A,d_B)$) on every admitted glue without a certificate,
while the equality $d_Z(Q)=\min(d_A,d_B)$ remains conditional on
`AdmissibleSeam` (the upper half), i.e. on survival of the factor
representative (which the logical-witness field of `STATE_MODEL.md` §1
carries). It is therefore not discharged by extraction alone; the certificate
(equal move words) is the evidence the consumer records for the
`AdmissibleSeam` hypothesis. The instance-wise route remains as
the decidable per-instance check. The consumer's certificate-gated
transport is unchanged in behavior; the certificate's role narrows from
underwriting the equality to attesting admissibility of the seam. No Lean
statement changes in this extraction; the lower-endpoint, instance-wise
equality, and class-pair parts of the extracted derivation are mechanized
(`lean/CodeCalculus/ExactGlue.lean`,
`lean/CodeCalculus/ExactGlueSurvival.lean`,
`lean/CodeCalculus/ExactGlueDistance.lean`). The family-level statement is mechanized in `lean/CodeCalculus/LogicalWitness.lean`
( `family_glueExact_iff`), `lean/CodeCalculus/AdmissibleSeamFamily.lean`
( `AdmissibleSeam`, `admissible_carriesMin`,
`admissible_family_exactDistance_eq_min`), and `lean/CodeCalculus/GlueExtraction.lean`: `wRe?_eq_none` and `glue_theorem4_lower_bound` mechanize
$w_{\mathrm{re},\sigma} = +\infty$ and the Theorem 4 / claim 7.4 lower bound
in `Option Nat`; `admissibleSeam_exactDistance?_eq_min` and
`admissible_family_exactDistance?_eq_min` prove the `Option Nat` equality
directly from `AdmissibleSeam` without `HasMinLogical` or `LogField`;
`admissible_carriesMin_glueField` and `admissible_family_glueField_exact`
bridge `AdmissibleSeam` to the §1a normalized transport `glueField`
(`WitnessFields.lean`); and `glue_expr_sound_exact_of_admissible` /
`glue_term_sound_exact_of_admissible` discharge the `hcert` equality premise
of `Gate6Exact.lean` from `AdmissibleSeam` for $\sigma = Z$. **Recorded
mechanization gap:** the geometric implication that identical
planar move words `w(c_A) = w(c_B)` (§2e) imply `AdmissibleSeam` is not
mechanized and is not derivable from the state model, for the reason given
under the attempted derivation above: move words and planarity are not state
data (`ADMISSIBLE_SEAM_FAMILY.md` §4). Likewise, shared-interface
Theorem 4 (overlapping qubits with finite $w_{\mathrm{re},\sigma}$) lies
outside the admitted disjoint-namespace transition.

**Boundary/edge labels (added 2026-11-12).** The field is defined
as a future-$\Pi$ type sketch in [`STATE_MODEL.md`](STATE_MODEL.md) §1: a
finite set of boundary supports $(S,\sigma,i)$ with $S\subseteq Q$ a
boundary segment, $\sigma\in\{X,Z\}$ a sector, and $i$ the index of a
logical operator of sector $\sigma$ whose support $S$ carries. Under
`E-GLUE`, a factor label $(S,\sigma,i)$ is carried unchanged when
$S\subseteq Q_A$ or $S\subseteq Q_B$ (segments contained in a factor);
a segment meeting the seam is refined by the seam checks; and a label crosses
the seam only when the logical representative it names survives it, so
boundary transport is the restriction of the logical-witness survival
statement of §4.31 / §4.33 Claim 2 to boundary supports and the two fields
are coupled. `E-LOCAL-HADAMARD` applied along a boundary edge exchanges the
sector component of every label on that edge. The field does not enter the
consumer. Both fields are defined in full, with their transport along
every admitted transition, in [`STATE_MODEL.md`](STATE_MODEL.md) §1a, and are mechanized in `lean/CodeCalculus/WitnessFields.lean`.
The definition there carries a factor label across the seam exactly when
its representative survives, and defines no refinement of a segment. ∎

## 4.32 — Soundness of the Gate 6 interval transformers (`OBL-GATE6-CSS-EXTENSIONS`)

 Evidence, not machine-checked in full; the
interval bookkeeping is the same as §4.13 and is mechanized in
`lean/CodeCalculus/Gate6Soundness.lean` (`gate6_interval_soundness`,
`glue_transformer_sound`, 2026-11-10) conditional on the
distance relations as premises, as §4.13's is; the distance relations are
those of §4.26–§4.31, of which §4.26, §4.27, and §4.28 are machine-checked
for the exact sector distance (`lean/CodeCalculus/ExactPeel.lean` for
§4.28). Under the §4.13 hypotheses (every input interval
contains the corresponding exact distance; every supplied price, lower bound,
strict-improvement enumeration, and witness is true) we show that each Gate 6
interval transformer of `JUDGMENT_LAYER.md` §2b/§2e is sound and monotone in
the sense of §8.4. The refusals of §4.27–§4.29 are not gaps: a reset to the
full interval is a sound, monotone transformer. For `E-PUNCTURE` and for
`E-EXTEND` with $\Delta\neq\varnothing$ no carried endpoint is derivable
(§4.29, §4.30); for `E-PEEL` the selected-sector lower and opposite-sector
upper directions are admitted (§4.28), with the full-distance upper carrying
the opposite sector's upper bound.

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

- **`E-PEEL`.** Admitted 2026-11-06 and sharpened 2026-11-10 on §4.28's relations $d_\tau'=w_{\mathrm{avoid},\tau}(q)\ge
 d_\tau$ and $d_\sigma'=\min(d_\sigma,w_{\mathrm{expose},\sigma}(q))$, so
 that $d_\sigma-1\le d_\sigma'\le d_\sigma$, for the selected sector $\tau$
 and the opposite sector $\sigma$. Unpriced, $F$ carries the selected
 sector's lower endpoint and resets its upper endpoint, carries the opposite
 sector's lower endpoint less one (floored at $0$) and its upper endpoint,
 and gives the full distance the minima of the two sector endpoints; upper
 endpoints are tightened by witnesses valid in the child. Priced, the
 exposure price $p$ moves the opposite sector to
 $[\min(L_\sigma,p),\min(U_\sigma,p)]$ and the avoidance minimum $w$ pins
 the selected sector to $[w,w]$, the full distance again the minima.
 Soundness: $L_\tau\le d_\tau\le d_\tau'$ and $d_\tau'\le U_\tau'$ only
 through child-valid witnesses; $L_\sigma-1\le d_\sigma-1\le d_\sigma'\le
 d_\sigma\le U_\sigma$; $d'=\min(d_\tau',d_\sigma')$ lies between the minima
 of two intervals containing $d_\tau'$ and $d_\sigma'$; under a true
 exposure price $d_\sigma'=\min(d_\sigma,p)\in[\min(L_\sigma,p),\min(U_\sigma,p)]$
 since $d_\sigma\in[L_\sigma,U_\sigma]$, and under a true avoidance minimum
 $d_\tau'=w$. Monotonicity: carry, predecessor, minimum, and reset are
 monotone in $\sqsubseteq$ (§9.4). ∎
 (Mechanized as `peelLedger`, `peel_transformer_sound`, and the peel case of
 `propagateGate6_monotone` in `lean/CodeCalculus/Gate6Soundness.lean`, with
 the three relations and the two price equalities as hypotheses; the three
 relations are discharged for the exact sector distance in
 `lean/CodeCalculus/ExactPeel.lean`, so `peel_transformer_sound_exact` keeps
 only the two price equalities as hypotheses. The pre-admission refusal,
 everything resets, remains available as the opt-out mode `reset` in
 `machine/priced_calculus.py`.)

- **`E-PUNCTURE`.** $F$ resets every lower endpoint to $0$ and takes every
 upper endpoint from witnesses valid in the child. Soundness and
 monotonicity are the same as for the reset, using §4.29's two refutations
 (the unnamed-qubit increase $d_X\;1\!\to\!2$ and the deleted-row decrease
 $d_X\;3\!\to\!2$); §4.29 records the reduction to deletions followed by a
 free-qubit removal, whose price is the hole price, not admitted. ∎

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
 `Section431GlueStep` in `machine/test_review_228_claude.py`). Under an
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

## 4.33 `E-GLUE`: no re-exposed class under the admitted transition; the glued sector distance from factor class data (`OBL-GLUE-RE-EXPOSURE`)

Dated hand derivation, 2026-11-11 (the re-exposure item of the
disposition). Evidence, not a machine-checked proof, except where a Lean
statement is named: Claim 1 and its distance bound are `glue_claim1` and
`glue_exactDistance_ge_min` (`lean/CodeCalculus/ExactGlue.lean`), and steps 3 and 4 of Claim 2 are machine-checked on representatives
in `lean/CodeCalculus/ExactGluePairs.lean` as
`glue_normalizer_iff`, `glue_stabilizer_iff`, `glueW_subset_glueK`,
`glue_class_eq_iff`, and `glue_logical_iff`. Step 5 of Claim 2, the
displayed distance formula, is machine-checked for a well-formed glued state
in `lean/CodeCalculus/ExactGlueDistance.lean` as
`glue_exactDistance?_eq_some_iff` and `glue_exactDistance?_eq_none_iff`,
with the class weights $\mu_A$ and $\mu_B$ as `classWeight`. The Lean
statements carry a class by a representative and build no quotient group.
Consequence (ii) under *What follows*, with the instance-wise equality of
§4.31, is machine-checked in `lean/CodeCalculus/ExactGlueSurvival.lean`: `survivesA_iff` and `survivesB_iff` are the survival
criterion, `survivesA_congr` and `survivesB_congr` show that it depends only
on the class, `glue_exactDistance_eq_min_of_survivesA` and its `B` form give
the equality from a survivor of weight
$\min(d_\sigma(C_A), d_\sigma(C_B))$, and `glue_survivor_of_min_logical`
gives a survivor of that weight from a glued logical of that weight. In `lean/CodeCalculus/GlueExtraction.lean`, `reExposedVectors_eq_nil`,
`wRe?_eq_none`, `glue_exactDistance?_ge_min`, and `glue_theorem4_lower_bound`
mechanize $w_{\mathrm{re},\sigma} = +\infty$ and the `Option Nat` lower bound;
`phiSeam_congr` and `phiSeam_linear` mechanize Step 1 of Claim 2 on
representatives (class invariance modulo the full factor spans and
$\mathbb{F}_2$-linearity); `glue_exactDistance?_ge_add_of_no_pure_survivor`
mechanizes consequence (iii); and `glue_universal_min_equality_false`
mechanizes the refutation below. Only the categorical
quotient-group packaging of $L_\sigma(C) \cong K_\sigma / W_\sigma$ and
complexity remark (iv) remain hand derivations.

**Setting.** The admitted `E-GLUE` transition of §4.31: factor states $C_A$
and $C_B$ on disjoint qubit sets $Q_A$ and $Q_B$, and the glued state $C$ on
$Q = Q_A \cup Q_B$ whose displayed rows are the factor rows together with the
admissible seam checks. Fix a sector $\sigma$ and write $\tau$ for the other
sector. A vector $v$ on $Q$ is a subset of $Q$ read as a vector over
$\mathbb{F}_2$, and a $\sigma$-type vector is one read as a product of
$\sigma$ operators on its support; for any vector $v$ write
$v_A = v \cap Q_A$ and $v_B = v \cap Q_B$ for its restrictions, so that
$v = v_A + v_B$, and write $\langle u, w \rangle$ for the overlap parity
$|u \cap w| \bmod 2$ of two vectors $u$ and $w$. For a state $D$ among
$C_A$, $C_B$, and $C$, let $S_\sigma(D)$ be the span of its displayed
$\sigma$-rows, $N_\sigma(D)$ the set of $\sigma$-type vectors on its qubits
with even overlap against every displayed $\tau$-row (the
$\sigma$-normalizer), $L_\sigma(D) = N_\sigma(D)/S_\sigma(D)$ the group of
$\sigma$-logical classes, and $d_\sigma(D)$ the least weight of an element of
$N_\sigma(D) \setminus S_\sigma(D)$, with $d_\sigma(D) = +\infty$ when that
set is empty. The seam checks of sector $\tau$ form the set $T_\tau$ and
those of sector $\sigma$ the set $T_\sigma$; by §4.31 every seam check
commutes with every factor row of the opposite sector and with every seam
check of the opposite sector, and lies outside the span of the factor rows
of its own sector. For a class $\alpha \in L_\sigma(C_A)$ let $\mu_A(\alpha)$
be the least weight of a representative of $\alpha$, so that $\mu_A(0) = 0$
and $d_\sigma(C_A) = \min_{\alpha \ne 0} \mu_A(\alpha)$; define $\mu_B$
likewise on $L_\sigma(C_B)$.

**Re-exposure, read for this transition.** The split bound of
*composition-distance* recorded in `DERIVED_RELATIONS.md` §2 carries a
term $w_{\mathrm{re},\sigma}$, the least weight of a class re-exposed by the
split. For the admitted transition this repository reads a re-exposed
$\sigma$-logical of $C$ as one whose restrictions are both factor
stabilizers, $v_A \in S_\sigma(C_A)$ and $v_B \in S_\sigma(C_B)$: a logical
of the whole that neither factor sees. Write
$w_{\mathrm{re},\sigma}(C; C_A, C_B)$ for the least weight of such a logical,
$+\infty$ when there is none.

**Claim 1.** Every $\sigma$-logical $v$ of $C$ has
$v_A \in N_\sigma(C_A) \setminus S_\sigma(C_A)$ or
$v_B \in N_\sigma(C_B) \setminus S_\sigma(C_B)$. Hence
$w_{\mathrm{re},\sigma}(C; C_A, C_B) = +\infty$ for every admitted glue, and
$d_\sigma(C) \ge \min(d_\sigma(C_A), d_\sigma(C_B))$ with no re-exposure
term.

*Derivation.*

1. The $\tau$-rows of $C_A$ are rows of $C$ with support in $Q_A$, so
 $\langle v, r \rangle = \langle v_A, r \rangle = 0$ for each such row $r$:
 $v_A \in N_\sigma(C_A)$. Likewise $v_B \in N_\sigma(C_B)$.
2. The $\sigma$-rows of both factors are rows of $C$, so
 $S_\sigma(C_A) + S_\sigma(C_B) \subseteq S_\sigma(C)$.
3. If $v_A \in S_\sigma(C_A)$ and $v_B \in S_\sigma(C_B)$, then
 $v = v_A + v_B \in S_\sigma(C)$ by step 2, contradicting that $v$ is a
 logical of $C$. So one restriction lies outside its factor's span and, by
 step 1, is a factor $\sigma$-logical.
4. Weight is monotone under restriction, $|v| \ge |v_A|$ and
 $|v| \ge |v_B|$, so by step 3 $|v| \ge d_\sigma(C_A)$ or
 $|v| \ge d_\sigma(C_B)$. ∎

**Claim 2.** For a $\tau$-seam check $t \in T_\tau$ the map
$\phi_t(\alpha, \beta) = \langle a, t_A \rangle + \langle b, t_B \rangle$,
with $a$ and $b$ any representatives of $\alpha \in L_\sigma(C_A)$ and
$\beta \in L_\sigma(C_B)$, is a well-defined linear functional on
$L_\sigma(C_A) \oplus L_\sigma(C_B)$. Let $K_\sigma$ be the common kernel of
the $\phi_t$ over $t \in T_\tau$, the pairs that commute with the
$\tau$-seam. Each $\sigma$-seam check $s \in T_\sigma$ has
$s_A \in N_\sigma(C_A)$ and $s_B \in N_\sigma(C_B)$ and so a class pair
$\pi(s) = ([s_A], [s_B])$; let $W_\sigma$ be the span of these pairs, the
pairs the $\sigma$-seam absorbs. Then $W_\sigma \subseteq K_\sigma$, the
restriction map induces an isomorphism $L_\sigma(C) \cong K_\sigma / W_\sigma$,
and the glued sector distance is the least sum of factor class weights over
the surviving pairs,

$$
d_\sigma(C) = \min\{\mu_A(\alpha) + \mu_B(\beta) : (\alpha, \beta) \in K_\sigma \setminus W_\sigma\},
$$

the minimum of the empty set being $+\infty$.

*Derivation.*

1. *Well-definedness.* Changing $a$ by an element of $S_\sigma(C_A)$ changes
 $\langle a, t_A \rangle$ by the overlap parity of a factor $\sigma$-row
 with $t$, which is $0$ by admissibility; likewise for $b$. Linearity is
 the linearity of the overlap parity in its first argument.
2. *The seam classes.* For $s \in T_\sigma$ and a $\tau$-row $r$ of $C_A$,
 $\langle s_A, r \rangle = \langle s, r \rangle = 0$ by admissibility, so
 $s_A \in N_\sigma(C_A)$; likewise $s_B \in N_\sigma(C_B)$. For
 $t \in T_\tau$, $\phi_t(\pi(s)) = \langle s, t \rangle = 0$ because seam
 checks of opposite sectors commute (§4.31, joint well-formedness), so
 $W_\sigma \subseteq K_\sigma$.
3. *The normalizer as pairs.* A $\sigma$-type vector $v$ on $Q$ lies in
 $N_\sigma(C)$ iff $v_A \in N_\sigma(C_A)$ and $v_B \in N_\sigma(C_B)$ (the
 factor $\tau$-rows see only the restrictions, as in step 1 of Claim 1)
 and $\langle v, t \rangle = \phi_t([v_A], [v_B]) = 0$ for every
 $t \in T_\tau$. So the class map $\bar\rho(v) = ([v_A], [v_B])$ is a
 homomorphism from $N_\sigma(C)$ onto $K_\sigma$: onto because for
 $(\alpha, \beta) \in K_\sigma$ with representatives $a$ and $b$ the vector
 $a + b$ lies in $N_\sigma(C)$ and maps to $(\alpha, \beta)$. Its kernel is
 the set of $v$ with $v_A \in S_\sigma(C_A)$ and $v_B \in S_\sigma(C_B)$,
 which is $S_\sigma(C_A) + S_\sigma(C_B)$.
4. *The stabilizer as pairs.* $S_\sigma(C) = S_\sigma(C_A) + S_\sigma(C_B) +
 \mathrm{span}(T_\sigma)$, so $\bar\rho(S_\sigma(C)) = W_\sigma$.
 Conversely, if $\bar\rho(v) \in W_\sigma$ then $\bar\rho(v) = \bar\rho(s)$
 for some $s \in \mathrm{span}(T_\sigma)$, so $v + s \in \ker \bar\rho
 \subseteq S_\sigma(C)$ and $v \in S_\sigma(C)$. Hence
 $\bar\rho^{-1}(W_\sigma) = S_\sigma(C)$ and $\bar\rho$ induces
 $L_\sigma(C) \cong K_\sigma / W_\sigma$.
5. *Weights.* The $\sigma$-logicals of $C$ are the $v \in N_\sigma(C)$ with
 $\bar\rho(v) \in K_\sigma \setminus W_\sigma$. For a fixed pair
 $(\alpha, \beta)$ the vectors with $\bar\rho(v) = (\alpha, \beta)$ are the
 sums $a + b$ of representatives, of weight $|a| + |b|$ because $Q_A$ and
 $Q_B$ are disjoint, so the least weight over the fiber is
 $\mu_A(\alpha) + \mu_B(\beta)$. Minimizing over $K_\sigma \setminus
 W_\sigma$ gives the display. ∎

**What follows.** (i) Claim 1 again: $(0, 0) \in W_\sigma$, so every pair in
$K_\sigma \setminus W_\sigma$ has a nonzero component. (ii) The equality
$d_\sigma(C) = \min(d_\sigma(C_A), d_\sigma(C_B))$ holds iff some pure pair
$(\alpha, 0)$ or $(0, \beta)$ of weight $\min(d_\sigma(C_A), d_\sigma(C_B))$
lies in $K_\sigma \setminus W_\sigma$: a minimum-weight class of the lighter
factor commutes with the $\tau$-seam and is not absorbed by the
$\sigma$-seam. This is the survival statement of §4.31's instance-wise
equality, stated for classes rather than for one witness; by step 1 of
Claim 2 it depends only on the class, so testing one representative decides
it. (iii) When no pure pair survives,
$d_\sigma(C) \ge d_\sigma(C_A) + d_\sigma(C_B)$: a seam can raise a sector
distance above both factors'. (iv) The formula ranges over
$2^{k_A + k_B}$ pairs, with $k_A$ and $k_B$ the factors' logical qubit
counts, and consumes the two class dictionaries $\mu_A$ and $\mu_B$, which
contain the factor distances and are NP-hard in general
(`DERIVED_RELATIONS.md` §3); it is an exact relation on factor class
data and seam class data, not a polynomial route to $d_\sigma(C)$ and not a
relation on factor distances alone, so the obstruction row of
`DERIVED_RELATIONS.md` §2 stands.

**What this settles, and what it does not.** On the admitted scope the
re-exposure minimum is $+\infty$ on every instance and in every sector, so
the question of its polynomiality on monotone seams, or on any seams, does
not arise: nothing admitted computes it. Proposition 5.2 of
*composition-distance* (NP-hardness of $w_{\mathrm{re}}$) and the split
bound with its $w_{\mathrm{re}}$ term concern that source's shared-interface
splits, where the two pieces overlap on qubits and a logical of the whole
can restrict to a stabilizer on each; the calculus has no such composition
(§4.31 requires disjoint namespaces, and `TERM_LANGUAGE.md` has no
shared-qubit production), so the hardness boundary stays recorded against a
setting that is not admitted. The shortest-path reduction sketched in
`DERIVED_RELATIONS.md` §5a describes that unadmitted setting; it is
not derived here, and no admitted cell depends on it. The §2e seam
certificate's equality $d_Z(C) = \min(d_Z(C_A), d_Z(C_B))$ remains a cell
hypothesis: by (ii) it asserts that a minimum-weight $Z$ class of the
lighter factor survives the seam, which the certificate guarantees for
planar seams with equal move words without exhibiting the class, and no
planar model is part of this derivation. Evidence:
`machine/experiments/glue_class_pairs.py` enumerates the glued logicals of
random glues (factors on two to five qubits, zero to three admissible seam
checks), finds no re-exposed class, and its class-pair formula agreed with
the exact-distance oracle in both sectors on 120 seeded glues, in 18 sector
instances of which the seam raised the distance above the factor minimum;
`machine/test_glue_class_pairs.py` pins the two-qubit factors of
`test_glue_witnesses.py` under three seams. Agreement is evidence that the
derivation is transcribed as stated, not a proof.

**Settlement of the candidate seam-distance claim (2026-11-12).**
The universal claim $d_\sigma(C)=\min(d_\sigma(C_A),d_\sigma(C_B))$ is
`false`: the counterexample above (an admissible seam whose $X$ seam check
kills both weight-one $Z$ classes, giving $d_Z(C)=2$) is a semantic
counterexample (mechanized as `glue_counterexample_distances` and
`glue_universal_min_equality_false` in `lean/CodeCalculus/GlueExtraction.lean`). The relation holds only instance-wise, when a minimum-weight
factor class survives the seam (item (ii) above); it is not admitted as an
operation contract. The scalar relation $d=\min(d_A,d_B)$ therefore remains
unadmitted, and the obstruction row of `DERIVED_RELATIONS.md` §2
stands. ∎

## 4.34 Typed constructors: output well-formedness and the parameter bookkeeping (`OBL-WELL-FORMEDNESS-PRESERVATION`, constructor instances)

Dated hand derivation, 2026-11-11. Evidence, not a
machine-checked proof. It covers the four constructors admitted as
`transition-defined` on this date (`L-HGP`, `L-LIFTED`, `L-GROUP-ALGEBRA`,
`A-CONCAT`; §2 cards). The five constructors admitted later the same day are derived in §4.35.

**The retained display.** Each constructor lists natural check rows per
sector in a fixed index order, and its displayed rows are, within each
sector, the natural rows that lie outside the span of the rows of that
sector kept before them.

*Claim.* The retained display is independent (I2), spans the natural row
space of its sector (I1's span clause), and drops exactly as many natural
rows as the natural row count exceeds the rank. If the natural rows of the
two sectors have even overlap pairwise, the retained display is CSS
orthogonal (I1's orthogonality clause), and the remaining invariants hold
by construction: labels are $0, \ldots, n-1$, identifiers are minted
canonically from the empty used set, every live identifier is in
$\mathsf{used}$, and every row carries one sector.

*Derivation.* By induction along the index order, a kept row is outside the
span of the rows kept before it, so the kept rows are independent, and a
dropped row lies in the span of the rows kept before it, so the span of the
kept rows is the span of all natural rows; the count follows. Dropping rows
cannot create an odd overlap, so orthogonality is inherited from the
natural rows. ∎

What remains, per constructor, is the pairwise even overlap of the natural
rows and the parameter bookkeeping.

**`L-HGP`.** With the notation of the §2 card, the overlap of the natural
$X$-row $(a, j)$ and the natural $Z$-row $(i, b)$ is
$H_1[a, i] H_2[b, j]$ from the left qubit $(i, j)$ and $H_1[a, i] H_2[b, j]$
from the right qubit $(a, b)$, so it is even. Hence the output is
well-formed and $n = n_1 n_2 + m_1 m_2$. For $k$, read the natural $X$-rows
as the rows of $[H_1 \otimes I_{n_2} \mid I_{m_1} \otimes H_2^{T}]$ and the
natural $Z$-rows as the rows of $[I_{n_1} \otimes H_2 \mid H_1^{T} \otimes I_{m_2}]$,
the left block indexed by the pairs $(i, j)$ and the right block by the
pairs $(a, b)$. Write $r_i = \mathrm{rank}(H_i)$, $k_i = n_i - r_i$, and
$k_i^{T} = m_i - r_i$. The rank of the $X$-row space is $m_1 n_2$ minus the
dimension of the left kernel of that matrix, and a vector
$c \in \mathbb{F}_2^{m_1 n_2}$ lies in the left kernel exactly when
$(H_1^{T} \otimes I_{n_2}) c = 0$ and $(I_{m_1} \otimes H_2) c = 0$, that is,
when $c \in (\ker H_1^{T} \otimes \mathbb{F}_2^{n_2}) \cap (\mathbb{F}_2^{m_1} \otimes \ker H_2)$.
For subspaces $U \subseteq V$ and $W \subseteq V'$ one has
$(U \otimes V') \cap (V \otimes W) = U \otimes W$: extend a basis of $U$ to a
basis of $V$ and a basis of $W$ to a basis of $V'$, and read coordinates in
the product basis. So the left kernel is $\ker H_1^{T} \otimes \ker H_2$, of
dimension $k_1^{T} k_2$, and $\mathrm{rank}(H_X) = m_1 n_2 - k_1^{T} k_2$;
symmetrically $\mathrm{rank}(H_Z) = n_1 m_2 - k_1 k_2^{T}$. Then
$k = n - \mathrm{rank}(H_X) - \mathrm{rank}(H_Z) = k_1 k_2 + k_1^{T} k_2^{T}$,
as expanding $(n_i - r_i)$ and $(m_i - r_i)$ shows. ∎ Evidence:
`machine/test_constructors.py` checks $n$, $k$, and both ranks against the
state's own bookkeeping on random factors, and the product of two cyclic
length-three repetition checks is the $[[18, 2, 3]]$ toric code by the
exact-distance oracle.

**`L-LIFTED`.** The group algebra $R = \mathbb{F}_2[G]$ of a finite abelian
group is commutative, and the regular representation $L$ is a ring
homomorphism from $R$ to $\ell \times \ell$ binary matrices with
$L(x)^{T} = L(x^{*})$, because $L(g)$ is the permutation matrix of
translation by $g$, whose transpose is translation by $-g$. Lifting a matrix
$M$ over $R$ entry by entry to a binary matrix $\mathcal{L}(M)$ preserves
sums and products, and $\mathcal{L}(M)^{T} = \mathcal{L}(M^{\dagger})$ with
$M^{\dagger}$ the transpose of $M$ with the involution applied to every
entry. The natural rows of the §2 card are the rows of $\mathcal{L}(H_X)$
and $\mathcal{L}(H_Z)$ for
$H_X = [A \otimes I_{n_B} \mid I_{m_A} \otimes B^{\dagger}]$ and
$H_Z = [I_{n_A} \otimes B \mid A^{\dagger} \otimes I_{m_B}]$ over $R$. Pairwise
even overlap is $\mathcal{L}(H_X) \mathcal{L}(H_Z)^{T} = 0$, and

$$
H_X H_Z^{\dagger} = (A \otimes I_{n_B})(I_{n_A} \otimes B^{\dagger}) + (I_{m_A} \otimes B^{\dagger})(A \otimes I_{m_B}) = A \otimes B^{\dagger} + A \otimes B^{\dagger} = 0,
$$

using $(I \otimes B)^{\dagger} = I \otimes B^{\dagger}$,
$(A^{\dagger} \otimes I)^{\dagger} = A \otimes I$, and the mixed-product rule,
which holds over a commutative ring. Hence the output is well-formed with
$n = \ell (n_A n_B + m_A m_B)$. Over the trivial group $B^{\dagger} = B^{T}$
and $A^{\dagger} = A^{T}$, which are the `L-HGP` matrices. No closed form for
$k$ is claimed: it is the rank bookkeeping of the constructed display. ∎
Evidence: the tests compare the trivial-group lifted product with the
hypergraph product row for row.

**`L-GROUP-ALGEBRA`.** The natural check matrices are
$[L(a) \mid L(b)]$ and $[L(b)^{T} \mid L(a)^{T}]$, and
$[L(a) \mid L(b)] [L(b)^{T} \mid L(a)^{T}]^{T} = L(a) L(b) + L(b) L(a) = L(ab) + L(ba) = 0$
by commutativity, so the output is well-formed with $n = 2\ell$. The lifted
product of the $1 \times 1$ base matrices $(a)$ and $(b^{*})$ has
$X$-block $[L(a) \mid L((b^{*})^{*})] = [L(a) \mid L(b)]$ and $Z$-block
$[L(b^{*}) \mid L(a^{*})] = [L(b)^{T} \mid L(a)^{T}]$, so the two transitions
agree row for row. For $k$: the rank of the $\ell \times 2\ell$ matrix
$[L(b)^{T} \mid L(a)^{T}]$ is $\ell$ minus the dimension of its left kernel,
and $v$ lies in that left kernel exactly when $L(b) v = 0$ and $L(a) v = 0$,
so $\mathrm{rank}(H_Z) = \ell - \kappa$ with
$\kappa = \dim(\ker L(a) \cap \ker L(b))$; likewise
$\mathrm{rank}(H_X) = \ell - \dim(\ker L(a^{*}) \cap \ker L(b^{*}))$. The
map $v \mapsto v^{*}$ on $R = \mathbb{F}_2^{\ell}$ is a linear bijection with
$L(x^{*}) v^{*} = (L(x) v)^{*}$, because $(x v)^{*} = x^{*} v^{*}$ in $R$, so
it carries $\ker L(a) \cap \ker L(b)$ onto $\ker L(a^{*}) \cap \ker L(b^{*})$
and the two ranks agree. Hence $k = 2\ell - 2(\ell - \kappa) = 2\kappa =
2(\ell - \mathrm{rank}[L(a) \mid L(b)])$. ∎ Evidence: the tests check this
on a cyclic example and recover $k = 12$ for the $72$-qubit bivariate
bicycle code of Bravyi et al. (2024), with $a = x^3 + y + y^2$ and
$b = y^3 + x + x^2$ over $\mathbb{Z}_6 \times \mathbb{Z}_6$.

**`A-CONCAT`.** The natural rows are the inner rows on every copy and the
lifted outer rows. Their pairwise even overlap and their independence are
step 1 of `DERIVED_RELATIONS.md` §2a, restated: inner rows of
opposite sectors commute within a copy and are disjoint across copies; an
inner row and a lift meet only on one copy, where the lift's part is a
logical representative, which commutes with the inner rows of the opposite
sector by definition; two lifts of opposite sectors pair to the overlap
parity of the two outer rows, which is $0$; and a dependency among the
natural rows of one sector forces, copy by copy, a dependency among the
outer rows or among the inner rows, both excluded by the factors'
well-formedness. So the retained display drops nothing, the output is
well-formed, and $n = n_{\mathrm{in}} n_{\mathrm{out}}$. For $k$: the display
has $n_{\mathrm{out}} (n_{\mathrm{in}} - k_{\mathrm{in}})$ inner rows and
$m_X^{O} + m_Z^{O}$ lifted rows, all independent, so
$k = n_{\mathrm{in}} n_{\mathrm{out}} - n_{\mathrm{out}} (n_{\mathrm{in}} - k_{\mathrm{in}}) - m_X^{O} - m_Z^{O} = N - m_X^{O} - m_Z^{O} = k_O$,
with $N = n_{\mathrm{out}} k_{\mathrm{in}}$ the outer qubit count. ∎ Evidence:
the tests compare the constructor with the tower built by
`machine/experiments/tower_sweep.py` row for row.

**Distances.** No constructor computes or asserts a distance. A constructed
state's ledger starts at $[0, +\infty)$ in every sector and for the full
distance; a lower endpoint rises only through a supplied bound with a
source, and an upper endpoint only through a witness validated in the
state (`JUDGMENT_LAYER.md` §2g, §2c; `DistanceLedger.for_constructed`). This
is the explicit-hypothesis discipline the 2026-11-10 disposition asked for:
the hypotheses are inputs, recorded with their source and never validated
(`OBL-PRICED-INPUT-SEMANTICS`). For `L-HGP` the classical distances are the
natural source of such a bound, through the hypergraph-product distance
theorem of Tillich and Zémor (2014); that theorem is a citation a consumer
may name as the source of a supplied bound, not a cell of this calculus, and
its sector orientation is not verified here. For `A-CONCAT` the tower price
provider of `JUDGMENT_LAYER.md` §2a supplies deletion and exposure prices of
the constructed state from level data.

**What this does not settle.** The five constructors that had no typed
inputs on this date, which §4.35 covers since; a closed form for $k$ of the lifted product; and any distance formula. The
Lean mechanization is partial. `lean/CodeCalculus/Term.lean`
and `Eval.lean` carry the four productions and their `EvalExpr` rules, with
the state updates in `Constructors.lean`; `A-CONCAT` takes its
representatives explicitly there, and algebra exponents are natural
numbers. Proved in Lean: the retained-display claim above
(`wf_constructedState`), $n$ for the four, the pairwise even overlap of
the natural rows for all four, and $k$ as $n$ minus the displayed row
counts on a well-formed output (`stateK_of_wf`). The overlap is
`hgp_naturalOrthogonal` for every pair of matrices,
`lift_naturalOrthogonal` and `twoblock_naturalOrthogonal` for every list
of cyclic orders and every algebra input, and `concat_naturalOrthogonal`
for well-formed factors and typed blocks and representatives
(`lean/CodeCalculus/ConstructorOverlap.lean`). Every
evaluation of the four therefore yields a well-formed state with no
hypothesis (`evalExpr_hgp_wf`, `evalExpr_lift_wf`, `evalExpr_twoblock_wf`,
`evalExpr_concat_wf`). The two group-algebra proofs do not use the typing
premises of their rules. For $k$: the $k$ of every
constructed state is $n$ minus the ranks of the natural rows of the two
sectors, with no hypothesis (`stateK_constructedState`,
`lean/CodeCalculus/ConstructorRank.lean`); the closed form
$k = 2(\ell - \operatorname{rank}[L(a) \mid L(b)])$ of `L-GROUP-ALGEBRA`
is proved for every list of cyclic orders and every pair of algebra
elements, again without the typing premises (`twoblockState_k_closed`,
`ConstructorRankTyped.lean`); and the `A-CONCAT` display retains every
natural row for well-formed factors and typed blocks and representatives
(`concatState_rows_length`, `lean/CodeCalculus/ConcatRetention.lean`), so $k = k_O$ holds there with no further hypothesis
(`concatState_k_closed`). The independence of the natural rows of one
sector (`vecIndep_concat`) is the argument above made explicit. The
overlap parities with the representatives of the opposite sector, taken
copy by copy, vanish on every inner row of the sector and send the lift of
an outer row to its vector over the block labels, so a vanishing
combination has a vanishing combination of outer rows, and its outer
coefficients are zero by I2 of the outer state. What is left is a
vanishing combination of inner rows. Its projection onto one copy is a
combination of the inner rows of that copy, and its coefficients are zero
by I2 of the inner state. Not proved in the audited modules as a proof from definitions: the closed
form for $k$ of `L-HGP`. Its statement in `lean/extra/ClosedK.lean` rests
on the two rank axioms `hgp_rankX` and `hgp_rankZ` (the arithmetic
`hgp_arith` is proved); those axioms are accepted as
`proposed (classical)` assumptions (see `AXIOMS.md`). It stays a hand
derivation of this section.
`OBL-WELL-FORMEDNESS-PRESERVATION` are discharged by this section for the
four admitted constructors; §4.35 discharges them for the other five. ∎

## 4.35 The five later constructors: output well-formedness and the parameter bookkeeping (`OBL-WELL-FORMEDNESS-PRESERVATION`, constructor instances)

Dated hand derivation, 2026-11-11. Evidence, not a
machine-checked proof. It covers the five constructors admitted as
`transition-defined` on this date (`A-PRODUCT`, `A-DOUBLE`, `L-BALANCED`,
`L-TANNER`, `L-TILE`; §2 cards). Each lists natural rows and displays their
retained display, so by the claim of §4.34 the output is well-formed as
soon as the natural rows of the two sectors have pairwise even overlap,
and $n$ is the number of labels of the card. What remains per constructor
is that overlap, which is derived for `A-PRODUCT` and `L-BALANCED` and is
an applicability premise for `A-DOUBLE`, `L-TANNER`, and `L-TILE`, and the
bookkeeping of $k$.

**`A-PRODUCT`.** Read a well-formed factor $F$ as the chain complex
$F_2 \to F_1 \to F_0$ over $\mathbb{F}_2$, with $F_2$ spanned by the
displayed $Z$-rows, $F_1$ by the qubits, and $F_0$ by the displayed
$X$-rows. The map $\partial_2^F$ sends a $Z$-row to the sum of the qubits of
its support, and $\partial_1^F$ sends a qubit to the sum of the $X$-rows that
contain it. Then $\partial_1^F \partial_2^F$ sends a $Z$-row $z$ to the sum
over the $X$-rows $x$ of the overlap parity of $x$ and $z$, which is $0$ by
I1. The tensor product $T = A \otimes B$ has
$T_d = \bigoplus_{p + q = d} A_p \otimes B_q$ and differential
$\partial(u \otimes v) = \partial u \otimes v + u \otimes \partial v$, and
$\partial \partial (u \otimes v) = 2 (\partial u \otimes \partial v) = 0$
over $\mathbb{F}_2$. The card's qubits are the basis of $T_2$ in the order
$A_2 \otimes B_0$, $A_1 \otimes B_1$, $A_0 \otimes B_2$; its natural
$X$-rows are indexed by the basis of $T_1$ in the order $A_1 \otimes B_0$,
$A_0 \otimes B_1$, the row of a basis element $c$ being the set of basis
elements $t$ of $T_2$ with $c$ in $\partial t$; and its natural $Z$-rows
are indexed by the basis of $T_3$ in the order $A_2 \otimes B_1$,
$A_1 \otimes B_2$, the row of $e$ being the support of $\partial e$.
Unfolding $\partial$ on each of the four index families gives the supports
of the card. The overlap parity of the $X$-row of $c$ and the $Z$-row of
$e$ is the coefficient of $c$ in $\partial \partial e$, which is $0$. Hence
the output is well-formed, with
$n = \dim T_2 = m_Z^A m_X^B + n_A n_B + m_X^A m_Z^B$.

For $k$, write $h_d(C)$ for the dimension of the degree-$d$ homology of a
finite complex $C$ over $\mathbb{F}_2$. The retained display spans the
natural row spaces, so
$k = n - \mathrm{rank}(\partial_2^T) - \mathrm{rank}(\partial_3^T) = h_2(T)$.
The Künneth formula over a field gives
$h_2(T) = h_2(A) h_0(B) + h_1(A) h_1(B) + h_0(A) h_2(B)$. A derivation in
this setting: a finite complex over a field is a direct sum of complexes
of two kinds, a single copy of the field with zero differential and two
copies in adjacent degrees joined by the identity (in each degree choose a
complement of the cycles, and inside the cycles a complement of the
boundaries); the tensor product distributes over direct sums; the product
of two summands of the first kind is of the first kind, in the sum of the
two degrees; and a product with a summand of the second kind has zero
homology, because it is two copies of the other factor joined by the
identity. Counting the summands of the first kind gives the formula. For a
well-formed factor $F$, $h_2(F) = \dim \ker \partial_2^F = 0$ because the
displayed $Z$-rows are independent (I2), $h_0(F) = m_X^F - \mathrm{rank}(\partial_1^F) = 0$
because the displayed $X$-rows are independent, and $h_1(F) = k_F$. So
$k = k_A k_B$. ∎

*Dependence on the display.* Replacing the display of a factor by another
display of the same code is an invertible change of basis of $F_2$ and of
$F_0$ that commutes with the differentials. It induces an isomorphism of
the product complexes, which acts on the summands $A_2 \otimes B_0$ and
$A_0 \otimes B_2$ of $T_2$ by an invertible linear map that is not a
permutation of the basis in general. So $n$ and $k$ do not depend on the
display, while the output code is determined only up to that linear map,
and its distances may depend on the display. This is the dependence on
retained-presentation data recorded at `TAXONOMY.md` §2.13, and it is the
reason the card types the inputs as presented states. Evidence:
`machine/test_constructors.py` checks $n$, $k = k_A k_B$, and the number of
dropped rows on products of the $[[4, 2, 2]]$ and Steane codes, where the
retained display drops rows.

**`A-DOUBLE`.** The commutation of the natural rows is the applicability
premise of the card, so an evaluation has natural rows with pairwise even
overlap, and the output is well-formed with $n = 2 n_C$ by §4.34. The
premise is decidable row pair by row pair. For two displayed rows $r$ and
$r'$ of $C$ and a common qubit $q$, write $\epsilon(q) \in \{0, 1\}$ for the
parity of the number of the two sets $w(r)$ and $w(r')$ that contain $q$.
The rows $(r, t)$ and $(r', t')$ meet exactly at the common qubits $q$ with
$\epsilon(q) = t + t' \bmod 2$, each on one sheet. Without `conjugate`, the
premise is that for every $X$-row $r$ and $Z$-row $r'$ the two counts
$|\{q : \epsilon(q) = 0\}|$ and $|\{q : \epsilon(q) = 1\}|$ are even; their
sum is even by I1 for $C$, so the premise is that the second is even for
every such pair. Under `conjugate`, rows of one sheet keep or swap sectors
together and rows of different sheets of one input sector have opposite
sectors, so the premise is that $|\{q : \epsilon(q) = 0\}|$ is even for
every pair of opposite input sectors and $|\{q : \epsilon(q) = 1\}|$ is even
for every pair of equal input sectors. For the empty wiring $\epsilon = 0$
and both hold; the natural rows are then the display of $C$ on sheet $0$
and, on sheet $1$, the display of $C$ or of its sector swap, on disjoint
qubits, so nothing is dropped and $k = 2 k_C$. For a general wiring $k$ is
the rank bookkeeping of the output. ∎

*The factorization question stays open.* `TAXONOMY.md` §2.16 records the
free $\mathbb{Z}_2$ cover of a two-block code as evidence that the
$n' = 2n$ shape factors through a cover constructor. That cover is the
double of the *natural* rows of the base under the wiring that twists an
incidence when the first exponent wraps. `A-DOUBLE` doubles the *displayed*
rows. The two agree when the natural rows of the base are independent, and
when they are dependent the cover also carries the lifts of the rows the
retained display dropped, so the double's row spaces lie strictly inside
the cover's and its $k$ is larger. `machine/test_constructors.py` records
one instance of each case. So the cover constructor is `L-GROUP-ALGEBRA`
with the larger group, not an instance of this card, and whether
`A-DOUBLE` factors through `A-CONCAT` or a cover constructor under the
§3.8 criteria is not settled here.

**`L-BALANCED`.** Let $P_2 \to P_1 \to P_0$ be the complex of
`hgp(H₁, H₂)`: $P_1$ is spanned by the qubits, $P_0$ by the pairs $(a, j)$,
$P_2$ by the pairs $(i, b)$, $\partial_2 (i, b)$ is the sum of the qubits of
the natural $Z$-row $\zeta(i, b)$, and $\partial_1$ sends a qubit to the sum
of the pairs $(a, j)$ whose natural $X$-row $\xi(a, j)$ contains it, with
$\partial_1 \partial_2 = 0$ by §4.34. The action $g (x, y) = (g x, g^{-1} y)$
permutes each of the three bases. It commutes with both differentials:
by the `L-HGP` card, membership of a qubit in $\xi(a, j)$ or in
$\zeta(i, b)$ is an entry of $H_1$ or of $H_2$ together with an equality of
indices, both of which the action preserves, because $H_1$ is equivariant
under $g$ and $H_2$ under $g^{-1}$. For a space $V$ with a permuted basis,
let $V_G$ be the quotient of $V$ by the span of the elements $v + g v$; the
orbits form a basis of $V_G$, a basis element mapping to its orbit. A
linear map that commutes with the action descends to the quotients, and
the composite of the descended maps is the descent of the composite. So
$\bar\partial_1 \bar\partial_2 = 0$ on $(P_2)_G \to (P_1)_G \to (P_0)_G$.
The card's natural $Z$-row of an orbit is the support of $\bar\partial_2$
of that orbit, computed on its least pair, and the card's natural $X$-row
of an orbit $c$ is the set of qubit orbits $o$ with $c$ in
$\bar\partial_1 o$, computed on the least pair of $o$; both are independent
of the representative because the maps descend. The overlap parity of the
$X$-row of $c$ and the $Z$-row of $e$ is the coefficient of $c$ in
$\bar\partial_1 \bar\partial_2 e$, which is $0$. Hence the output is
well-formed, and $n$ is the number of orbits on the pairs of column indices
plus the number on the pairs of row indices. When the action on both
families of pairs is free, $n = (n_1 n_2 + m_1 m_2) / |G|$. Over the trivial
group every orbit is a single pair, the orders of the card are the index
orders of the `L-HGP` card, and the rows are the natural rows of
`hgp(H₁, H₂)`. No closed form for $k$ is claimed. ∎ Evidence: the tests
compare the trivial-group balanced product with the hypergraph product
state for state, and on two cyclic repetition matrices of length $L$ with
the cyclic shift acting on both they find $n = 2L$ and the $k$ of
`twoblock` over $\mathbb{Z}_L$ with $a = b = 1 + x$.

The construction is the balanced product named at `TAXONOMY.md` §3.4,
restricted to two-term factors and finite abelian groups. No source
derivation is reproduced or relied on: the well-formedness argument above
is self-contained. Over $\mathbb{F}_2$
the quotient $V_G$ is taken as defined above for every action; for an
action that is not free, an orbit sum can vanish in the descended maps,
and the output is still a well-formed state.

**`L-TANNER`.** The commutation of the natural rows is the applicability
premise, so the output is well-formed with the $n$ of the input by §4.34.
A sufficient condition for the premise covers the tensor local codes of
quantum Tanner constructions. Let $C_A \subseteq \mathbb{F}_2^{\Delta_A}$
and $C_B \subseteq \mathbb{F}_2^{\Delta_B}$ be classical codes, let
$w_X = w_Z = \Delta_A \Delta_B$ with positions read as a grid of pairs
$(\alpha, \beta)$, let the rows of $\Lambda_Z$ span $C_A \otimes C_B$, and
let the rows of $\Lambda_X$ span $C_A^{\perp} \otimes C_B^{\perp}$. Suppose
that for every vertex $u$ of the $X$ class and $v$ of the $Z$ class the
qubits common to the two embeddings are either none, or a full grid line
of both: the positions $(\alpha, \beta)$ with one fixed $\alpha$ in both
embeddings, matched at equal $\beta$, or the positions with one fixed
$\beta$ in both, matched at equal $\alpha$. On a line with fixed $\alpha$,
a codeword of $C_A \otimes C_B$ restricts to a codeword of $C_B$ and a
codeword of $C_A^{\perp} \otimes C_B^{\perp}$ to a codeword of
$C_B^{\perp}$, so the two restrictions have even overlap; likewise with
$C_A$ on a line with fixed $\beta$. So every natural $X$-row and natural
$Z$-row have even overlap, and the premise holds. The condition is
sufficient and is not a premise of the card: the card checks the overlap
itself. $k$ is the rank bookkeeping of the output. ∎ Evidence: the tests
build the $[[18, 2, 3]]$ toric code from weight-four local checks on stars
and faces.

**`L-TILE`.** The commutation of the natural rows is the applicability
premise, so the output is well-formed by §4.34, and $n$ is the number of
site classes by construction. The support rule of the card is the image of
the local row under the map that sends a local qubit to its site class,
taken over $\mathbb{F}_2$: a class that receives an even number of the
row's qubits is not in the support. A check imposed by two placements, or a
row whose image is empty, lies in the span of the rows kept before it and
is dropped by the retained display. $k$ is the rank bookkeeping of the
output. ∎ Evidence: the tests assemble the $[[9, 1, 3]]$ rotated surface
code from four tiles and eight placements, remove a boundary check, and
identify the sites of two copies of a four-qubit tile.

**Distances.** As for the four constructors of §4.34: no constructor
computes or asserts a distance, a constructed state's ledger starts at
$[0, +\infty)$, and endpoints move only on supplied, sourced bounds and
validated witnesses (`JUDGMENT_LAYER.md` §2g). Distance statements for
balanced products, quantum Tanner codes, and tensor products exist in the
literature under expansion or other hypotheses; none is a cell here, and
none of those hypotheses is an input of a transition.

**What this does not settle.** A closed form for $k$ of `L-BALANCED`,
`L-TANNER`, `L-TILE`, or a twisted `A-DOUBLE`; nonabelian group actions;
product structures other than the CSS tensor product; local codes that
vary from vertex to vertex; the factorization question of `TAXONOMY.md`
§2.16; and any distance formula. The Lean mechanization is
partial. `lean/CodeCalculus/Term.lean` and `Eval.lean` carry the five
productions and their `EvalExpr` rules, with the state updates in
`Constructors.lean`; a wiring is a list keyed by displayed identifier, and
the orbits of `L-BALANCED` are computed from the group elements. Proved in
Lean (`ConstructorAssembly.lean`): $n$ for the five; the pairwise even
overlap for `A-PRODUCT` on every pair of well-formed factors, so its
output well-formedness holds with no hypothesis (`evalExpr_product_wf`);
and output well-formedness for `A-DOUBLE`, `L-TANNER`, and `L-TILE`, whose
rules carry the overlap as a premise. Also proved (`ConstructorRank.lean`): $k = 2 k_C$ for the empty wiring of `A-DOUBLE`,
for every factor with a repeat-free namespace and both values of the
conjugation flag (`doubleState_empty_k`). Also proved (`BalancedOverlap.lean`): the pairwise even overlap for `L-BALANCED` on
every typed input (`balanced_naturalOrthogonal`), so its output
well-formedness holds with no hypothesis (`evalExpr_balanced_wellFormed`).
The proof is the argument above in counting form. The action of an
exponent tuple composes and inverts, the matrices are invariant under it,
and the least pair of an orbit is the same for every pair of the orbit.
For an orbit $c$ of the pairs $(a, j)$ and a pair $(i, b)$, the left
qubits and the right qubits each contribute to the overlap the number of
pairs $(a, j)$ in $c$ with $H_1[a, i] = 1$ and $H_2[b, j] = 1$, so the
overlap is even. For $k$ of `L-BALANCED`, `L-TANNER`, and `L-TILE`
(`ConstructorRankNatural.lean`), the rank bookkeeping is stated against
the inputs: $k$ is $n$ minus the ranks of the two matrices of natural
rows, written out row by row (`balancedState_k_closed`,
`tannerState_k_closed`, `tileState_k_closed`). These are instances of
`stateK_constructedState` and are not formulas in the parameters of the
inputs; no such formula is claimed above. Not proved in Lean:
$k = k_A k_B$ for `A-PRODUCT`, whose statement in
`lean/extra/ClosedK.lean` rests on the two rank axioms `product_rankX` and
`product_rankZ` (the arithmetic `product_arith` is proved);
those axioms are accepted as `proposed (classical)` assumptions (see
`AXIOMS.md`); the agreement of
`L-BALANCED` over the trivial group with `L-HGP` beyond one instance; and
the sufficient condition for the commutation premise of `L-TANNER`. Those
stay hand derivations of this section. The constructor instances of
`OBL-WELL-FORMEDNESS-PRESERVATION` are discharged by this section for the
five constructors of this date. ∎

## 4.36 `L-NESTED-CSS`: output well-formedness and the parameter bookkeeping (`OBL-WELL-FORMEDNESS-PRESERVATION`, constructor instance)

Dated hand derivation, 2026-11-13. Evidence, not a
machine-checked proof. It covers `L-NESTED-CSS`, admitted as
`transition-defined` on this date (§2 card).

**Setting.** Let $n \ge 1$ and let $H_X$ and $H_Z$ be binary matrices with
$n$ columns. Write $C_X = \ker H_X$ and $C_Z = \ker H_Z$ for the two
classical codes of length $n$ they check. For a subspace $C$ of
$\mathbb{F}_2^{n}$ write $C^{\perp}$ for its dual, the vectors with even
overlap with every element of $C$, so that $C_X^{\perp}$ is the row space
of $H_X$ and $C_Z^{\perp}$ is the row space of $H_Z$. For a set $V$ of
vectors write $\mathrm{wt}(V)$ for the least weight of an element of $V$,
with $\mathrm{wt}(\emptyset) = +\infty$, and write
$d(C) = \mathrm{wt}(C \setminus \{0\})$ for the minimum distance of a code
$C$. The natural rows of the card are the rows of $H_X$ as $X$-rows and the
rows of $H_Z$ as $Z$-rows.

**The premise is the nesting.** Every row of $H_X$ has even overlap with
every row of $H_Z$ exactly when the row space of $H_Z$ lies in the kernel
of $H_X$, that is, when $C_Z^{\perp} \subseteq C_X$. Taking duals, this is
the same as $C_X^{\perp} \subseteq C_Z$. The premise is decided by
one overlap parity for each pair of a row of $H_X$ and a row of $H_Z$.

**Well-formedness and $n$.** Under the premise the natural rows of the two
sectors have pairwise even overlap, so by the claim of §4.34 the retained
display is a well-formed state on the labels $0, \ldots, n - 1$, and $n$
is the common number of columns.

**The count $k$.** The retained display of a sector spans the natural row
space of that sector (§4.34), so the $X$ rank of the output is
$\mathrm{rank}(H_X) = \dim C_X^{\perp}$ and the $Z$ rank is
$\mathrm{rank}(H_Z) = \dim C_Z^{\perp}$. Hence

$$
k = n - \mathrm{rank}(H_X) - \mathrm{rank}(H_Z) = \dim C_X - \dim C_Z^{\perp} = \dim C_Z - \dim C_X^{\perp},
$$

the dimension of the quotient $C_X / C_Z^{\perp}$, which the nesting makes
a quotient of spaces. ∎

**The sector distances, derived and not admitted as cells.** An $X$-logical
of the output, in the sense of `JUDGMENT_LAYER.md` §2c, is a support with
even overlap with every displayed $Z$-row that lies outside the span of the
displayed $X$-rows. The displayed $Z$-rows span $C_Z^{\perp}$ and the
displayed $X$-rows span $C_X^{\perp}$, so the $X$-logicals are the elements
of $C_Z \setminus C_X^{\perp}$, and likewise the $Z$-logicals are the
elements of $C_X \setminus C_Z^{\perp}$. Therefore

$$
d_X = \mathrm{wt}(C_Z \setminus C_X^{\perp}) \ge d(C_Z), \qquad d_Z = \mathrm{wt}(C_X \setminus C_Z^{\perp}) \ge d(C_X).
$$

Each inequality holds because the set on the left of it is a subset of the
nonzero codewords, and each can be strict, when every codeword of least
weight lies in the dual of the other code. These are statements about the
constructed state. No cell carries them: the constructor computes no
classical distance, and the ledger of the output starts at $[0, +\infty)$
like that of every constructor (`JUDGMENT_LAYER.md` §2g). What the
derivation licenses is the naming of a classical minimum distance as the
source of a supplied lower bound, $d(C_Z)$ for $d_X$ and $d(C_X)$ for
$d_Z$. The supplied value itself is not validated.

**Relation to `L-TANNER`.** The expression
$\mathrm{tanner}(n; H_X, H_Z; \iota, \iota)$, with $\iota$ the one-entry
list whose embedding is $(0, \ldots, n - 1)$, lists the same natural rows
in the same order under the same premise, so it has a derivation exactly
when $\mathrm{nested}(H_X, H_Z)$ has one and evaluates to the same state.
The production therefore constructs no state that the admitted expressions
did not already construct. In the other direction the constructor is
generic: a well-formed state on the labels $0, \ldots, n - 1$ whose
identifiers are minted canonically with the $X$-rows first is the value of
$\mathrm{nested}$ on the two matrices of its own display, with no row
dropped, provided each sector displays at least one row.

**What this does not settle.** Any distance cell, and the validation of a
classical distance. Codes given by generator matrices or as abstract
subspaces: the signature of `CONSTRUCTOR_SIGNATURES.md` is
narrowed to parity-check matrices. Whether a production that is an
instance of `L-TANNER` should stay a separate production or become a
derived form is not decided here. The Lean mechanization is partial.
`lean/CodeCalculus/Term.lean` and `Eval.lean` carry the production and its
`EvalExpr` rule, with the state update in `Constructors.lean`. Proved in
Lean (`ConstructorAssembly.lean`): $n$ (`evalExpr_nested_n`) and output
well-formedness (`evalExpr_nested_wf`), the rule carrying the overlap as a
premise. Checked by the kernel on the Steane instance only
(`ConstructorInstances.lean`): agreement with the consumer's state and
equality with the `L-TANNER` expression above. Not in Lean: the closed
form for $k$ read on the classical codes, the two distance inequalities,
and the equality with `L-TANNER` on every input. Evidence: `machine/test_constructors.py`
builds the $[[7, 1, 3]]$ Steane code from the Hamming check matrix, checks
$k$ and both displayed formulas for the sector distances against the
exact-distance oracle on 60 seeded nested pairs (on some of which a sector
distance exceeds the classical minimum distance), checks equality with the
`L-TANNER` expression above on 20 seeded pairs, and rebuilds a
hypergraph-product state from its own display. Agreement is evidence that
the derivation is transcribed as stated, not a proof. The constructor
instance of `OBL-WELL-FORMEDNESS-PRESERVATION` is discharged by this
section for `L-NESTED-CSS`. ∎

## 4.37 Gate-realization judgment rows: codespace preservation and the equal-syndrome weight floor

Dated hand derivation, 2026-11-18. Evidence, not a
machine-checked proof. Source statements: Nelson, Danageozian, Cao, Economou,
and Barnes, *From Syndromes to Computation: A General Framework for Logical
Operations in Quantum Error-Correcting Codes*, arXiv 2610.17612v1 (Theorem 1
and Corollaries 2 and 3), re-derived here for a CSS display so that no cell
rests on the source's appendix proofs. The judgment cells are recorded in
[`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2 and §2h.

**Setting.** Let $C$ be a well-formed state on $n = |Q|$ qubits. Each
displayed row is a sector $\sigma \in \{X, Z\}$ and a support $S \subseteq Q$,
denoting the Pauli operator that applies $\sigma$ on $S$. Write
$\mathcal{S}(C)$ for the stabilizer group these operators generate and
$\mathcal{V}(C)$ for the codespace, the common $+1$ eigenspace of the
displayed rows. For bit vectors $a, b \in \mathbb{F}_2^Q$, write $X(a)$ for
the product of Pauli $X$ over the support of $a$ and $Z(b)$ for the product
of Pauli $Z$ over the support of $b$. Every Pauli operator on $Q$ with a
fourth-root-of-unity phase is $i^t X(a) Z(b)$ for a unique triple
$(t, a, b)$ with $t \in \{0, 1, 2, 3\}$.

**Lemma 1 (stabilizer membership on a CSS display).** *The operator
$i^t X(a) Z(b)$ lies in $\mathcal{S}(C)$ iff $t = 0$, $a \in X$, and
$b \in Z$.*

*Derivation.* The displayed rows commute pairwise by I1, so any product of
displayed rows can be ordered with the $X$-rows first and the $Z$-rows
second. The $X$-rows multiply to $X(a)$ with $a \in X$ the $\mathbb{F}_2$-sum
of their supports, the $Z$-rows to $Z(b)$ with $b \in Z$ likewise, and no
phase factor arises in the product $X(a) Z(b)$. Conversely, each such
$X(a) Z(b)$ with $a \in X$ and $b \in Z$ is a product of displayed rows.
$\square$

In particular $-I \notin \mathcal{S}(C)$, so $\mathcal{V}(C) \neq 0$, and the
phase of any product of displayed CSS rows is determined by `(sector, support)`
without an independent per-row sign field.

**Lemma 2 (fixing the codespace).** *A Pauli operator $P$ with a phase
satisfies $P\psi = \psi$ for every $\psi \in \mathcal{V}(C)$ iff
$P \in \mathcal{S}(C)$.*

*Derivation.* Every element of $\mathcal{S}(C)$ fixes $\mathcal{V}(C)$ by
definition. Conversely, let
$\Pi = \lvert\mathcal{S}(C)\rvert^{-1} \sum_{s \in \mathcal{S}(C)} s$ be the
orthogonal projector onto $\mathcal{V}(C) \neq 0$. From $P\Pi = \Pi$,
$\mathrm{Tr}(P\Pi) = \mathrm{Tr}(\Pi) > 0$, so $\mathrm{Tr}(Ps) \neq 0$ for
some $s \in \mathcal{S}(C)$. A Pauli operator with nonzero trace is a scalar
multiple of the identity, so $P = c s^{-1}$ for a scalar $c$, and $c = 1$
because both $P$ and $s^{-1}$ fix a nonzero vector in $\mathcal{V}(C)$.
$\square$

**Gates and the codespace-preservation predicate $\mathsf{preserves}_U(C)$.**
A *gate* $U$ is specified by a finite list of pairwise commuting Hermitian
Pauli operators $G_1, \dots, G_q$ on $Q$ (the *generators*), signs
$\epsilon_j \in \{+1, -1\}$, and angles $\theta_j \ge 0$, denoting the
unitary

$$
U = \prod_{j=1}^{q} \exp(i\epsilon_j \theta_j G_j).
$$

A gate is an operator parameter of the assertion language, not state data,
and leaves $C = (Q, X, Z, \mathsf{pres}, \mathsf{used})$ unchanged; no
operation identifier is minted for a logical gate
([`TAXONOMY.md`](TAXONOMY.md) §3.8). The predicate $\mathsf{preserves}_U(C)$
holds when $U$ maps $\mathcal{V}(C)$ into itself. Because $\mathcal{V}(C)$
is determined by $\mathcal{S}(C) = \langle X, Z \rangle$, the carrier of
$\mathsf{preserves}_U$ is `span`.

**Lemma 3 (preservation at $\theta_j = \pi/4$).** *Let $\theta_j = \pi/4$ for
all $1 \le j \le q$. For a displayed row $g$, let
$J(g) = \{j \in \{1,\dots,q\} : G_j \text{ anticommutes with } g\}$ and*

$$
V_g = \prod_{j \in J(g)} i\epsilon_j G_j.
$$

*Then $U^\dagger g U = g V_g$, and $\mathsf{preserves}_U(C)$ holds iff
$V_g \in \mathcal{S}(C)$ for every displayed row $g$.*

*Derivation.*
1. For a single rotation $R = \exp(i\epsilon(\pi/4) G)$, if $G$ commutes with
 $g$ then $R^\dagger g R = g$; if $G$ anticommutes with $g$ then
 $g R = R^\dagger g$, so
 $R^\dagger g R = g R^2 = g \exp(i\epsilon(\pi/2) G) = g(i\epsilon G)$.
2. Because $G_1, \dots, G_q$ commute pairwise, each rotation commutes with
 every factor $i\epsilon_j G_j$. Conjugating $g$ by the rotations in turn
 and applying step 1 at each step gives $U^\dagger g U = g V_g$.
3. $\mathsf{preserves}_U(C)$ holds iff $g U\psi = U\psi$ for every displayed
 row $g$ and every $\psi \in \mathcal{V}(C)$, which by step 2 and
 $U^\dagger g U = g V_g$ is equivalent to $g V_g \psi = \psi$. Since
 $g\psi = \psi$ and $g^2 = I$, this is $V_g \psi = \psi$ for all
 $\psi \in \mathcal{V}(C)$. Because $V_g$ is a Pauli operator with a phase,
 Lemma 2 gives $V_g \in \mathcal{S}(C)$. $\square$

By Lemma 1, the condition $V_g \in \mathcal{S}(C)$ at angle $\pi/4$ is
decidable from the display in polynomial time: two $\mathbb{F}_2$
span-membership checks and one phase check ($t = 0$) per displayed row.

**Carry derivations for $\mathsf{preserves}_U$ across the kernel.**

- *`C-SKIP`.* The state and its codespace are unchanged, so
 $\mathsf{preserves}_U(C)$ carries unchanged.
- *`C-ADD-CHECK` adding row $s$, with child $C'$ and
 $\mathsf{preserves}_U(C)$.* The child codespace is
 $\mathcal{V}(C') = \{\psi \in \mathcal{V}(C) : s\psi = \psi\}$.
 1. *Commuting generators, any angle.* If every $G_j$ commutes with $s$,
 then $U$ commutes with $s$. For $\psi \in \mathcal{V}(C')$,
 $U\psi \in \mathcal{V}(C)$ by $\mathsf{preserves}_U(C)$ and
 $s U\psi = U s\psi = U\psi$, so $U\psi \in \mathcal{V}(C')$ and
 $\mathsf{preserves}_U(C')$ holds at every angle.
 2. *All angles $\pi/4$.* By Lemma 3 applied to $C'$,
 $\mathsf{preserves}_U(C')$ holds iff $V_g \in \mathcal{S}(C')$ for every
 displayed row $g$ of $C'$. The displayed rows of $C'$ are those of $C$
 together with $s$. For every displayed row $g$ of $C$, Lemma 3 on $C$
 gives $V_g \in \mathcal{S}(C) \subseteq \mathcal{S}(C')$. Thus
 $\mathsf{preserves}_U(C')$ holds iff $V_s \in \mathcal{S}(C')$, a single
 stabilizer-membership check at the added row $s$. (When every $G_j$
 commutes with $s$, $J(s) = \varnothing$ and $V_s = I \in \mathcal{S}(C')$,
 recovering branch 1 at $\pi/4$.)
 3. *Anticommuting generator at an angle $\neq \pi/4$, and addressability.*
 When some $G_j$ anticommutes with $s$ and some angle is not $\pi/4$,
 codespace preservation depends on the eigenvalues of zero-syndrome
 logical operators in a chosen frame; addressability (that $U$ acts on
 chosen logical qubits) and the logical action of an accepted gate
 likewise require a logical frame. Because no judgment rule reads the
 eigenvalues of the future-$\Pi$ logical-witness field
 ([`STATE_MODEL.md`](STATE_MODEL.md) §1a), these cases remain
 `not yet defined`.
- *`C-DELETE-CHECK` (refutation of carry).* On $Q = \{0, 1\}$ with displayed
 rows $X_0 X_1$ and $Z_0 Z_1$, take $G_1 = X_0$, $G_2 = X_1$ with signs
 $\epsilon_1 = +1$, $\epsilon_2 = -1$ at angle $\pi/4$. The row $Z_0 Z_1$
 anticommutes with both generators, so
 $V_{Z_0 Z_1} = (i X_0)(-i X_1) = X_0 X_1 \in \mathcal{S}(C)$, while
 $X_0 X_1$ commutes with both ($V_{X_0 X_1} = I \in \mathcal{S}(C)$); hence
 $\mathsf{preserves}_U(C)$ holds. Deleting $X_0 X_1$ produces $C'$ with
 $\mathcal{S}(C') = \{I, Z_0 Z_1\}$, so
 $V_{Z_0 Z_1} = X_0 X_1 \notin \mathcal{S}(C')$ and
 $\mathsf{preserves}_U(C')$ is false. Thus $\mathsf{preserves}_U$ does not
 carry across `C-DELETE-CHECK` (at $\pi/4$, Lemma 3 re-evaluated over the
 child's remaining rows decides the child directly).
- *`C-DIRECT-SUM`.* Let $\mathsf{preserves}_U(A)$ hold for a gate $U$ whose
 generators are supported on $Q_A$ (acting as the identity on $Q_B$). Because
 $\mathcal{V}(A \oplus B) = \mathcal{V}(A) \otimes \mathcal{V}(B)$ on the
 disjoint union $Q_A \sqcup Q_B$, the operator $U \otimes I_{Q_B}$ maps
 $\mathcal{V}(A \oplus B)$ into itself, so $\mathsf{preserves}_U(A \oplus B)$
 holds.
- *`C-SEQUENCE`.* Composes step by step from the per-primitive cells above.
 $\square$

**Lemma 4 (equal-syndrome generator weight floor).** *Call a family of
pairwise commuting Hermitian Pauli generators $G_1, \dots, G_q$ ($q \ge 2$)
equal-syndrome on $C$ when all members have one common nonempty syndrome on
the displayed rows of $C$, and nontrivial on $C$ when some product $G_1 G_j$
lies outside $\mathcal{S}(C)$ up to sign. Write
$w_{\max} = \max_{1 \le j \le q} \mathrm{wt}(G_j)$ and let $\omega(C)$ be the
least $w_{\max}$ over nontrivial equal-syndrome families on $C$ ($+\infty$ if
none exists). Then at every well-formed state $C$,*

$$
\omega(C) \ge \lceil d(C)/2 \rceil.
$$

*Derivation.* Take $j$ such that $L = G_1 G_j$ is not in $\mathcal{S}(C)$ up
to sign, and write $L = i^t X(a) Z(b)$. Because $G_1$ and $G_j$ have the same
syndrome on every displayed row, $L$ commutes with every displayed row: $a$
has even overlap with every displayed $Z$-row and $b$ has even overlap with
every displayed $X$-row. By Lemma 1, since $L$ is not in $\mathcal{S}(C)$ up
to sign, either $a \notin X$ or $b \notin Z$. In the first case $a$ is an
$X$-logical of $C$, so $\lvert a\rvert \ge d_X(C) \ge d(C)$; in the second
case $b$ is a $Z$-logical of $C$, so $\lvert b\rvert \ge d_Z(C) \ge d(C)$.
Hence $\mathrm{wt}(L) = \lvert a \cup b\rvert \ge \max(\lvert a\rvert, \lvert b\rvert) \ge d(C)$.
By subadditivity of Pauli weight under multiplication,
$\mathrm{wt}(L) \le \mathrm{wt}(G_1) + \mathrm{wt}(G_j) \le 2 w_{\max}$, so
$w_{\max} \ge \lceil d(C)/2 \rceil$. Taking the minimum over all nontrivial
equal-syndrome families on $C$ gives $\omega(C) \ge \lceil d(C)/2 \rceil$
(including when $k = 0$ and $d(C) = +\infty$, where no nontrivial
equal-syndrome family exists and $\omega(C) = +\infty$). $\square$

**Transport by weakening (and refutation of parent-value substitution).**
If the full-distance interval at state $C$ has sound lower endpoint
$\ell = L_d \le d(C)$, then because $\ell \mapsto \lceil \ell/2 \rceil$ is
nondecreasing on $\mathbb{N} \cup \{+\infty\}$, Lemma 4 implies
$\omega(C) \ge \lceil L_d/2 \rceil$. This bound is re-read at each state from
that state's carried lower endpoint $L_d$: it is unchanged across `C-SKIP`,
does not decrease across `C-ADD-CHECK` ($L_d' \ge L_d$), recomputes from
$\min(L_d^A, L_d^B)$ across `C-DIRECT-SUM`, and weakens to
$\lceil L_d'/2 \rceil$ across `C-DELETE-CHECK` (where $L_d'$ resets to $0$
unpriced or moves to $\min(L_d, w_{\mathrm{del}}, w_{\mathrm{exp}})$ priced).

The parent's value of the floor cannot be substituted into the child across
`C-DELETE-CHECK`. On the nine-qubit Shor code ($Q = \{0,\dots,8\}$, $Z$-rows
$\{0,1\},\{1,2\},\{3,4\},\{4,5\},\{6,7\},\{7,8\}$, $X$-rows
$\{0,1,2,3,4,5\},\{3,4,5,6,7,8\}$), $d(C) = 3$ and the floor is
$\lceil 3/2 \rceil = 2$. Deleting the first $X$-row $\{0,1,2,3,4,5\}$ produces
a child $C'$ in which $G_1 = Z_3$ and $G_2 = Z_6$ both anticommute with the
sole remaining $X$-row $\{3,4,5,6,7,8\}$ and commute with every $Z$-row, while
$G_1 G_2 = Z_3 Z_6$ lies outside $\mathcal{S}(C')$ up to sign. Thus
$\{Z_3, Z_6\}$ is a nontrivial equal-syndrome family on $C'$ with
$w_{\max} = 1 < 2$, matching the child's own weakened floor
$\lceil d(C')/2 \rceil = \lceil 1/2 \rceil = 1$.

**Evidence.** `machine/experiments/gate_realization_rows.py` and
`machine/test_gate_realization_rows.py` check Lemmas 1, 3, and 4 and the
`C-ADD-CHECK` and `C-DELETE-CHECK` cells against a state-vector rotation
oracle and an exact-distance oracle across the two named counterexamples and a
seeded sweep (seed 452). Agreement is evidence that the derivations are
transcribed as stated, not a proof. ∎

## 4.38 Family-level one-shot level-map transport: block-length lower bound

Dated 2026-11-18. For a seed $C$ satisfying Hypotheses 102--103 and a sheet
count $m \ge 2$, the finite hollowed-tensor complex $\bar\Gamma(C)$ of
Definition 116 (Eq. (249)) has qubit layer
$Q(\Gamma) = \bigoplus_x Y^x_1 \oplus \bigoplus_q Y^q_0$.
Each $Y^q_0$ is the 0-cells of $K^q \otimes V + G^q \otimes R$; since
$G^q$ has no edges, $K^q = \mathrm{cone}\,G^q$ contributes the apex $q$
tensored with the $m$ vertices of $V$, i.e. $m$ cells for the apex, plus
$m (|\{z \succ q\}|)$ cells from $G^q \otimes R$'s vertex--edge
incidence, so $Y^q_0$ contributes at least $m(1 + |\delta q|)$ qubits.
Summing over $q \in Q(C)$ gives at least $m \cdot n(C)$ qubits from the
$q$-layers alone, and any $x$-check contributes the additional cells
$Y^x_1$ (the 1-cells $xq, qz$ tensored with $V$ and the edges $qz$ tensored
with $R$). Hence $n(\bar\Gamma(C)) > m \cdot n(C)$ for every nonempty seed.
This is a finite cell count from Definitions 104, 106, 111 and 116; it is
not a distance or family-closure claim, and it says nothing about the tower
cost scaling. $\square$

## 4.39 Logical-sector quotient transport for `C-DIRECT-SUM`, `C-DELETE-CHECK`, and `C-ADD-CHECK`

Dated hand derivation, 2026-11-18. Evidence, not a machine-checked
proof; Lean currently builds no logical quotient (`the status note`, Gate 2).
Establishes the quotient-level logical-sector effects of the five kernel
operations (`C-SKIP` is identity; `C-SEQUENCE` composes step-wise) for
[`CLAIMS.md`](CLAIMS.md) §5 and the property inventory.

**Setting.** Let $C = (Q, X, Z, \mathsf{pres}, \mathsf{used})$ be a well-formed
phase-insensitive CSS state (I1–I5) on finite qubit namespace $Q$ with
$n = \lvert Q\rvert$. By I1, $X = \langle \mathit{rows}_X\rangle \subseteq \mathbb{F}_2^Q$,
$Z = \langle \mathit{rows}_Z\rangle \subseteq \mathbb{F}_2^Q$, and $X \perp Z$
(so $X \subseteq Z^\perp$ and $Z \subseteq X^\perp$ under the binary dot product
$u \cdot v = \lvert u \cap v\rvert \bmod 2$ on $\mathbb{F}_2^Q$). Write the
logical-sector quotient spaces over $\mathbb{F}_2$ as

$$
\mathcal{L}_X(C) = Z^\perp / X, \qquad \mathcal{L}_Z(C) = X^\perp / Z.
$$

**Lemma (orthogonality over $\mathbb{F}_2^Q$).** *For every subspace
$W \subseteq \mathbb{F}_2^Q$, $\dim W^\perp = n - \dim W$ and
$(W^\perp)^\perp = W$. Consequently
$\dim \mathcal{L}_X(C) = \dim \mathcal{L}_Z(C) = k(C) = n - \dim X - \dim Z$.*

*Derivation.* The map $\Phi : \mathbb{F}_2^Q \to (\mathbb{F}_2^Q)^*$ given by
$\Phi(u)(v) = u \cdot v$ is linear and has identity matrix in the standard basis
$\{e_q : q \in Q\}$, hence is an isomorphism. Restriction
$\mathrm{res}_W : (\mathbb{F}_2^Q)^* \to W^*$ is surjective because any linear
functional on a basis of $W$ extends by $0$ on a complementary basis of
$\mathbb{F}_2^Q$. Since $W^\perp = \ker(\mathrm{res}_W \circ \Phi)$,
rank–nullity yields $\dim W^\perp = n - \dim W^* = n - \dim W$. By symmetry of
the dot product, $W \subseteq (W^\perp)^\perp$, and
$\dim((W^\perp)^\perp) = n - (n - \dim W) = \dim W$, so $(W^\perp)^\perp = W$.
(No $X \cap Z = \{0\}$ assumption is used; the identity holds over $\mathbb{F}_2$
including isotropic subspaces and when $k(C) = 0$ or $n = 0$.) Finally, since
$X \subseteq Z^\perp$, $\dim(Z^\perp / X) = (n - \dim Z) - \dim X = k(C)$, and
symmetrically $\dim(X^\perp / Z) = k(C)$. $\square$

**1. Direct sum (`C-DIRECT-SUM`).** Let $C_A, C_B$ be well-formed with
$Q_A \cap Q_B = \varnothing$ and $\mathsf{used}_A \cap \mathsf{used}_B = \varnothing$,
and let $C = C_A \oplus C_B$ on $Q = Q_A \sqcup Q_B$. In
$\mathbb{F}_2^Q = \mathbb{F}_2^{Q_A} \oplus \mathbb{F}_2^{Q_B}$ we have
$X = X_A \oplus X_B$, $Z = Z_A \oplus Z_B$, and by block-disjointness of the dot
product $Z^\perp = Z_A^\perp \oplus Z_B^\perp$ and
$X^\perp = X_A^\perp \oplus X_B^\perp$ (§4.4). Define
$\phi_X : \mathcal{L}_X(C_A) \oplus \mathcal{L}_X(C_B) \to \mathcal{L}_X(C)$ by
$\phi_X(u_A + X_A, u_B + X_B) = (u_A, u_B) + (X_A \oplus X_B)$.
- *Well-defined and linear:* if $u_A' - u_A \in X_A$ and $u_B' - u_B \in X_B$,
 then $(u_A', u_B') - (u_A, u_B) \in X_A \oplus X_B = X$; linearity is
 componentwise.
- *Surjective:* every $u \in Z^\perp = Z_A^\perp \oplus Z_B^\perp$ splits as
 $(u_A, u_B)$ with $u_A \in Z_A^\perp$, $u_B \in Z_B^\perp$, and
 $\phi_X(u_A + X_A, u_B + X_B) = u + X$.
- *Injective:* $(u_A, u_B) \in X_A \oplus X_B \iff u_A \in X_A \land u_B \in X_B$.

Hence $\mathcal{L}_X(C_A \oplus C_B) \cong \mathcal{L}_X(C_A) \oplus \mathcal{L}_X(C_B)$,
and symmetrically
$\mathcal{L}_Z(C_A \oplus C_B) \cong \mathcal{L}_Z(C_A) \oplus \mathcal{L}_Z(C_B)$.
$\square$

**2. Stabilizer deletion (`C-DELETE-CHECK`).** Let `delete_r` remove a displayed
$X$-row $r \in \mathit{rows}_X$ from $C$ (the $Z$-row case is symmetric by
exchanging $X \leftrightarrow Z$). By I1 and I2, $r \notin X' := \langle \mathit{rows}_X \setminus \{r\}\rangle$,
$X = X' \oplus \langle r\rangle$, and $Z' = Z$. Hence
$X' \subsetneq X \subseteq Z^\perp$ and $Z \subseteq X^\perp \subsetneq X'^\perp$.

- *Same sector ($\mathcal{L}_X$).* The inclusion $X' \hookrightarrow X$ induces
 a canonical surjective $\mathbb{F}_2$-linear projection
 $\pi_X : \mathcal{L}_X(C') = Z^\perp / X' \twoheadrightarrow Z^\perp / X = \mathcal{L}_X(C)$,
 $u + X' \mapsto u + X$, with kernel
 $\ker(\pi_X) = X / X' = \{0 + X',\, r + X'\} \cong \mathbb{F}_2$, giving the
 short exact sequence
 $$
 0 \longrightarrow X / X' \longrightarrow \mathcal{L}_X(C') \xrightarrow{\;\pi_X\;} \mathcal{L}_X(C) \longrightarrow 0.
 $$
 Every parent class $u + X \in \mathcal{L}_X(C)$ splits into two child classes
 $u + X'$ and $(u + r) + X'$ whose vector union is $u + X$. In particular, the
 trivial parent class $0 + X$ splits into $0 + X'$ and the **newly admitted
 (promoted) $X$-logical class** $r + X' = X \setminus X'$, which is nonzero in
 $\mathcal{L}_X(C')$ because $r \in X \subseteq Z^\perp$ and $r \notin X'$.
 The canonical quotient map is the backward projection $\pi_X$, which has no
 canonical section $\mathcal{L}_X(C) \to \mathcal{L}_X(C')$.
- *Opposite sector ($\mathcal{L}_Z$).* The inclusion
 $X^\perp \hookrightarrow X'^\perp$ induces a canonical injective
 $\mathbb{F}_2$-linear transport map
 $\iota_Z : \mathcal{L}_Z(C) = X^\perp / Z \hookrightarrow X'^\perp / Z = \mathcal{L}_Z(C')$,
 $v + Z \mapsto v + Z$. Define $\ell_r : X'^\perp \to \mathbb{F}_2$ by
 $\ell_r(v) = v \cdot r$. Because $Z \subseteq X^\perp \subseteq \ker(\ell_r)$,
 $\ell_r$ descends to a well-defined linear functional
 $\bar\ell_r : \mathcal{L}_Z(C') \to \mathbb{F}_2$, $\bar\ell_r(v + Z) = v \cdot r$,
 with $\ker(\bar\ell_r) = ((X' + \langle r\rangle)^\perp) / Z = X^\perp / Z = \mathrm{im}(\iota_Z)$.
 By the Lemma, $(X'^\perp)^\perp = X'$; since $r \notin X'$, there exists
 $v_0 \in X'^\perp$ with $v_0 \cdot r = 1$. Hence $\bar\ell_r$ is
 surjective (its value at $v_0 + Z$ is $1$; such a $v_0$ cannot lie in $Z$,
 as $Z \perp X$ and $r \in X$), giving the short exact sequence
 $$
 0 \longrightarrow \mathcal{L}_Z(C) \xrightarrow{\;\iota_Z\;} \mathcal{L}_Z(C') \xrightarrow{\;\bar\ell_r\;} \mathbb{F}_2 \longrightarrow 0.
 $$
 Parent $Z$-logical classes embed injectively without merging as the surviving
 subspace $\mathrm{im}(\iota_Z) = \ker(\bar\ell_r)$, and the **newly admitted
 (exposed) $Z$-logical classes** are precisely the affine hyperplane
 $\bar\ell_r^{-1}(1) = (X'^\perp \setminus X^\perp) / Z = \{v_0 + v + Z : v + Z \in \mathcal{L}_Z(C)\}$
 of $2^{k(C)}$ classes anticommuting with $r$ while commuting with $X'$.
 Together, $(r + X', v_0 + Z)$ satisfies $r \cdot v_0 = 1$ and forms a
 conjugate logical pair for the added logical qubit ($k(C') = k(C) + 1$).

This derivation settles the quotient-level logical-sector characterization
(including the $k = 0$ case exhibited by fixture `W12`); it derives no
unpriced post-deletion distance lower bound or equality, which remains
`unavailable` (`JUDGMENT_LAYER.md` §2, §3). $\square$

**3. Stabilizer addition (`C-ADD-CHECK`).** Let `addStab_{r:X}` add an $X$-row
$r \in \mathbb{F}_2^Q$ satisfying the `C-ADD-CHECK` premises $r \in Z^\perp$
and $r \notin X$ (the $Z$-row case is symmetric). Then
$X' = X \oplus \langle r\rangle \subseteq Z^\perp$, $Z' = Z$, and
$Z \subseteq X'^\perp \subsetneq X^\perp$; moreover $r + X$ is a nonzero class
in $\mathcal{L}_X(C)$, so $k(C) \ge 1$ and $k(C') = k(C) - 1 \ge 0$. Reversing
the roles of $(X', X)$ in Part 2 yields the dual exact sequences:

- *Same sector ($\mathcal{L}_X$):* canonical surjection
 $\pi_X : \mathcal{L}_X(C) \twoheadrightarrow \mathcal{L}_X(C')$,
 $u + X \mapsto u + X'$, with $\ker(\pi_X) = X' / X = \{0 + X,\, r + X\} \cong \mathbb{F}_2$:
 $$
 0 \longrightarrow X' / X \longrightarrow \mathcal{L}_X(C) \xrightarrow{\;\pi_X\;} \mathcal{L}_X(C') \longrightarrow 0.
 $$
 The parent class $r + X$ is **absorbed** into the stabilizer group, and each
 surviving pair $\{u + X, (u + r) + X\}$ merges into a single child class
 $u + X' \in \mathcal{L}_X(C')$.
- *Opposite sector ($\mathcal{L}_Z$):* canonical injection
 $\iota_Z : \mathcal{L}_Z(C') \hookrightarrow \mathcal{L}_Z(C)$ with
 surjective anticommutation functional $\bar\ell_r(v + Z) = v \cdot r$
 (surjective since $r \notin X = (X^\perp)^\perp$):
 $$
 0 \longrightarrow \mathcal{L}_Z(C') \xrightarrow{\;\iota_Z\;} \mathcal{L}_Z(C) \xrightarrow{\;\bar\ell_r\;} \mathbb{F}_2 \longrightarrow 0.
 $$
 Surviving classes are $\ker(\bar\ell_r) = X'^\perp / Z = \mathcal{L}_Z(C')$
 (those commuting with $r$), and the **removed (killed) classes** are the
 affine hyperplane $\bar\ell_r^{-1}(1) = (X^\perp \setminus X'^\perp) / Z$ of
 $2^{k(C)-1}$ parent $Z$-classes anticommuting with $r$.

Exact post-addition distance values remain `open`; strict improvement,
sector-aware gauging, and direct-sum extinction remain conditional cells
(`JUDGMENT_LAYER.md` §2a). $\square$

## 4.40 Metatheorem re-discharge for `stdCSS-3` and kernel rung-6 promotion

Dated hand derivation and re-discharge audit, 2026-11-18. Evidence,
not a machine-checked proof; Gates 2–7 remain unchecked and rung 7
(`mechanized`) remains open.

Per [`VERSIONING.md`](VERSIONING.md) §4, every release bump creates a
**re-discharge obligation** for every metatheorem scoped to the operation set:
each affected metatheorem must be re-established against the expanded operation
set, either by extending its proof or by restricting its statement explicitly,
before its `discharged-through` field advances. Between `stdCSS-1` (the five
kernel primitives) and `stdCSS-3` (including the 2026-11-18 `v0.3.0` candidate
axis-3 additions), the calculus changed in four places:

1. **Equality and capacity:** $\equiv$ added the $Q_1 = Q_2$ clause
 (2026-10-29, `STATE_MODEL.md` §2), and every minting rule added
 the H-4 finite 70,000-name capacity premise (2026-10-31 / 2026-11-11, §2 `C-ADD-CHECK`).
2. **`stdCSS-2` transitions (axis 2):** `E-GRAFT` and the six Gate 6 CSS-level
 conditional cells (`P-REBASE`, `E-LOCAL-HADAMARD` at $T \in \{Q, \varnothing\}$,
 `E-PEEL`, `E-PUNCTURE`, `E-EXTEND`, and binary `E-GLUE`).
3. **`stdCSS-3` constructors (axis 2):** ten `transition-defined` expression
 constructors (`L-HGP`, `L-LIFTED`, `L-GROUP-ALGEBRA`, `A-CONCAT`,
 `A-PRODUCT`, `A-DOUBLE`, `L-BALANCED`, `L-TANNER`, `L-TILE`,
 `L-NESTED-CSS`, §4.34–§4.36), carrying no distance rule (`JUDGMENT_LAYER.md`
 §2g).
4. **Axis-3 judgment additions:** derived properties $w$, $r$ (§4.21), $\kappa$
 (§4.22); generator-referencing claim $\mathsf{gen}_i$ (`JUDGMENT_LAYER.md`
 §4, §4.11); `E-PEEL` price cells (§4.28); heuristic statuses `probabilistic`
  and `certificate-checked` (`CLAIMS.md`); gate-realization
 rows $\mathsf{preserves}_U$ and $\omega$ weakening (§2h, §4.37);
 `A-QUOTIENT` monomial-quotient conditional slot (§2i;
 `A-QUOTIENT` remains `taxonomy-only`); and conditional family-level one-shot
 level-map transport (§2j, §4.38; no single-state evaluation or
 operation ID).

Each metatheorem in [`OBLIGATIONS.md`](OBLIGATIONS.md) — together with
`OBL-WELL-FORMEDNESS-PRESERVATION`, which quantifies over all admitted
operations — is audited below. Every entry is either **discharged** across
`stdCSS-3` or **explicitly restricted** to a stated fragment and discharged on
that fragment through `stdCSS-3`:

1. **`OBL-WELL-FORMEDNESS-PRESERVATION`** *(discharged through `stdCSS-3` for
 all admitted operations and constructors; explicitly restricted away from
 unadmitted candidates).* Kernel five (§4.7), `E-GRAFT` (§4.12), six Gate 6
 CSS cells (§4.26–§4.31), and all ten `stdCSS-3` constructors (§4.34–§4.36)
 each have dated hand derivations preserving I1–I5 (and ambient containment in
 $\mathbb{F}_2^{Q'}$). H-4 capacity restricts the domain of minting rules to
 states with enough unused identifiers; it never alters output invariants.
 Unadmitted candidates (`A-QUOTIENT`, `E-SPLIT`, `X-*`, `pullback`,
 `pushout`) remain explicitly outside this scope (`open`).
2. **`OBL-PRIMITIVE-DETERMINISM`** *(discharged through `stdCSS-3` as
 single-valuedness on fixed presentations; $\equiv$-input invariance
 explicitly restricted).* On a fixed encoded input state and explicit term
 data, every transition and constructor of `stdCSS-3` is a deterministic
 function of its input and term: kernel five (§4.8, re-evidenced for $Q$
 2026-10-29), `E-GRAFT` (§4.12, explicit chain $\vec r$), six Gate 6 cells
 (§4.26–§4.31), and all ten `stdCSS-3` constructors (§4.34–§4.36, with
 `A-CONCAT` representatives explicit or canonically defaulted from
 `tower_level_data`); capacity exhaustion (H-4) produces `no_derivation`, not
 multiple outputs. Lean's `eval_unique` and `denoteExpr_eval` (`Eval.lean`)
 match this single-valuedness across all mechanized commands and expressions.
 *Explicit restriction:* invariance of the output modulo $\equiv$ under
 row-order permutations of the input state holds for the five kernel
 primitives, `E-GRAFT`, `E-LOCAL-HADAMARD`, `E-PEEL`, `E-PUNCTURE`,
 `E-EXTEND`, `E-GLUE`, and the classical/algebraic `L-*` constructors, and is
 **restricted away from** display-order-reading operations (`P-REBASE`,
 `A-PRODUCT`, `A-DOUBLE`, `A-CONCAT`), whose matrix indexing, qubit/retention
 order, or factor-row concatenation in display order depends on the concrete
 display list order. For the six Gate 6 cells `E-GRAFT`,
 `E-LOCAL-HADAMARD`, `E-PEEL`, `E-PUNCTURE`, `E-EXTEND`, and `E-GLUE`,
 invariance follows from a common argument: each reads input rows by
 identifier or as a set and mints any new identifiers canonically from
 `used`, so a row-order permutation of the input leaves the output row set
 and the minted names unchanged (§4.26–§4.31).
3. **`OBL-SKIP-IDENTITY`** *(discharged through `stdCSS-3` for all admitted
 commands).* §4.6's proof uses only the `C-SKIP` and `C-SEQUENCE` rules and
 the Framing Lemma (no `Eval` premise or semantic output field reads `steps`).
 Every command admitted in `stdCSS-2` (`E-GRAFT`, `P-REBASE`,
 `E-LOCAL-HADAMARD`, `E-PEEL`, `E-PUNCTURE`, `E-EXTEND`) obeys
 `STATE_MODEL.md` §5 (`steps` is read by no `Eval` premise or judgment), and
 `stdCSS-3` introduces no new command production. Thus §4.6 holds verbatim
 for every command $m$ of `stdCSS-3`.
4. **`OBL-SEQUENCE-ASSOCIATIVITY`** *(discharged through `stdCSS-3` for all
 admitted commands).* §4.8's associativity proof uses only inversion of the
 `C-SEQUENCE` rule and is parametric in the command language; §1a's
 denotational adequacy ($\llbracket m\rrbracket(S) = \mathsf{some}\ S' \iff
 \mathrm{Eval}(m, S, S')$) depends only on single-valuedness of `Eval`,
 discharged for all `stdCSS-3` commands in item 2 above.
5. **`OBL-DIRECT-SUM-LAWS`** *(discharged through `stdCSS-3`).* The state model
 $C = (Q, X, Z, \mathsf{pres}, \mathsf{used})$, equality $\equiv$ (including
 $Q$, re-evidenced 2026-10-29), and the `C-DIRECT-SUM` rule are unchanged
 across `stdCSS-1`–`stdCSS-3`. Every `stdCSS-3` expression constructor yields
 a well-formed presented CSS state on this model (§4.34–§4.36), so
 associativity and commutativity at $\equiv$ apply to any disjoint pair or
 triple of evaluated expressions. The 2026-11-18 axis-3 span properties
 ($\mathsf{preserves}_U$, $\omega$) respect qubit relabeling $\approx$
 (transporting $U$'s support by $\sigma$ for $\mathsf{preserves}_U$, and by
 weight-invariance of $\sigma$ for $\omega$).
6. **`OBL-ORDER-INDEPENDENT-DELETION`** *(explicitly restricted to pure
 `C-DELETE-CHECK` / `C-SEQUENCE` batches; discharged through `stdCSS-3` on
 that scope).* The statement explicitly excludes interleaved presentation or
 extension commands. Because deletion neither mints identifiers nor changes
 $Q$, neither the $Q$ clause in $\equiv$ nor H-4 capacity alters §4.15's
 proof; the fixed-reference-set annotation-transport clause is likewise
 unaffected.
7. **`OBL-CROSS-SECTOR-PERMUTATION`** *(explicitly restricted to opposite-sector
 kernel check commands `C-DELETE-CHECK` and `C-ADD-CHECK` under `C-SEQUENCE`;
 discharged through `stdCSS-3` on that scope).* Excluded from `E-GRAFT` and
 Gate 6 commands (which change $Q$, swap sectors, or mint multiple rows).
 Under H-4 capacity on the kernel fragment: `Delete`/`Delete` mints nothing;
 `Delete`/`Add` mints one identifier (since `Delete` leaves `used` unchanged,
 capacity holds in both orders or fails in both, yielding Case 4 when
 exhausted); `Add`/`Add` mints two identifiers (if fewer than two unused
 identifiers remain, both orders fail at the second step, yielding Case 4;
 otherwise §4.10's Case 2/Case 4 analysis holds unchanged). Thus the
 four-case partition and side condition $\Pi$ stand verbatim.
8. **`OBL-FIXED-NAMESPACE-REACHABILITY`** *(explicitly restricted to
 fixed-namespace kernel `C-DELETE-CHECK` / `C-ADD-CHECK` / `C-SEQUENCE` paths
 up to canonical identifier allocation; discharged through `stdCSS-3` on that
 scope under H-4 capacity).* Excludes $n$-changing `E-*` commands and
 extended-state models. Under H-4 capacity (§4.17), the
 all-deletions-first path mints $\dim X_1 + \dim Z_1 \le \lvert Q\rvert$
 identifiers and exists whenever at least that many identifiers remain unused
 in the 70,000-name enumeration.
9. **`OBL-PRESENTATION-CONJUGATION`** *(explicitly restricted to the five
 kernel primitives and `E-GRAFT`; discharged through `stdCSS-3` on that
 scope).* §4.25 proves transported-command congruence for all five kernel
 operations and `E-GRAFT`. Because a qubit relabeling $\sigma$ leaves `used`
 untouched, the H-4 capacity premise is relabeling-invariant, so §4.25 stands
 unchanged. Explicitly restricted away from `P-REBASE`, the other five Gate 6
 cells, and the ten `stdCSS-3` expression constructors (which emit fresh
 canonical namespaces $\{0, \dots, n-1\}$ or read input display order).
10. **`OBL-DERIVED-TERM-FACTORIZATION`** *(explicitly restricted to derived
 commands over the five kernel primitives for a fixed ordered elementary
 expansion; discharged through `stdCSS-3` on that scope).* `E-GRAFT` and the
 Gate 6 commands are admitted as primitive conditional transitions, not
 derived commands (`CLAIMS.md`, `P-REBASE` card), and the ten `stdCSS-3`
 constructors are expression constructors. On the kernel scope, H-4 capacity
 makes a fixed ordered expansion applicable iff capacity suffices for its
 additions, leaving §4.23 unchanged.
11. **`OBL-CERTIFICATE-PATH-KEYING`** *(discharged through `stdCSS-3` for
 per-state keying $(C, P, \sigma)$ and syntax-directed route-scoping; the
 three Gate 5 design questions of §4.24 remain open).* `stdCSS-3` admitted
  `certificate-checked` for per-state atomic judgments (`CLAIMS.md`) using this exact keying (`CertificateChecker.lean`), and none of
 the `stdCSS-3` or 2026-11-18 axis-3 additions adds a distance-computing rule
 or an operation-contract certificate variant.
12. **`OBL-JUDGMENT-SOUNDNESS`** *(discharged by hand derivation through
 `stdCSS-3` for the unconditional L3 inventory; explicitly restricted away
 from conditional priced/certificate/honest-layout cells, §2j family-level
 transport, and unadmitted candidates).* For every unconditional L3 rule
 currently in the signature, the instantiation base is backed by a dated hand
 derivation:
 - kernel five across all unconditional carry-table rows ($n, k, w, r, \kappa,
 d_X, d_Z, d, \mathsf{preserves}_U, \omega$, output well-formedness,
 logical-sector quotients, and $\mathsf{gen}_i$: §4.1–§4.7, §4.11,
 §4.21–§4.22, §4.37, §4.39);
 - `E-GRAFT` and the five unary Gate 6 commands for structural/WF rows and
 $\mathsf{gen}_i$ (§4.11–§4.12, §4.21–§4.22, §4.26–§4.30);
 - `E-GLUE` and the ten `stdCSS-3` expression constructors for structural/WF
 rows, plus `E-GLUE`'s §4.31/§4.33 unpriced distance lower bound (§4.31,
 §4.33–§4.36; constructors carry no distance rule, §2g).
 The order and weakening rules (`TRANSITIVITY`, `MIN-ORDER`, ambient order
 theory on $\mathbb{N} \cup \{+\infty\}$, and monotone weakening §7.2.6 /
 §4.37) are sound over $\mathbb{N} \cup \{+\infty\}$. *Explicit
 restrictions:* (a) conditional priced cells, seam certificates, and honest
 merged/supplied layout premises remain conditional on consumer-supplied
 hypotheses (`OBL-PRICED-INPUT-SEMANTICS`, `OBL-PRICED-INTERVAL-SOUNDNESS`,
 `OBL-GATE6-CSS-EXTENSIONS`); (b) family-level one-shot level-map transport
 (`JUDGMENT_LAYER.md` §2j) has no single-state evaluation and rests on
 imported framework hypotheses; (c) `A-QUOTIENT` (`JUDGMENT_LAYER.md` §2i)
 is an existence record only (`taxonomy-only`); and (d) full Lean
 mechanization over the expanded inventory landed in
 `lean/CodeCalculus/ExpandedSoundness.lean`, and
 Gate 5 remains unchecked.
13. **`OBL-JUDGMENT-TRANSPORT`** *(discharged through `stdCSS-3` for
 single-state command sequences; explicitly restricted away from mixed
 opposite-polarity distance chains and future-$\Pi$ certificate mutation).*
 The positive half composes all structural properties ($n, k, w, r, \kappa,
 \mathsf{preserves}_U$, $\omega$ weakening, output well-formedness),
 single-polarity distance chains, and surviving $\mathsf{gen}_i$ claims
 across sequences of kernel, `E-GRAFT`, and unary Gate 6 commands, with
 `stdCSS-3` expression constructors entering at chain position $0$ via the
 input-display source rule (§4.11, §4.21–§4.22, §4.37). The `W13` refusal
 half and the seam condition on chains of single steps cover deletion, graft,
 peel, puncture, and rebase (§4.11; mechanized in `Transport.lean` and
 `SeamChains.lean`). *Explicit restrictions:* mixed opposite-polarity
 exact-quantity distance chains remain `open` in L3; future-$\Pi$
 certificate context mutation is not part of `Eval`; binary `E-GLUE` and
 expression constructors occur only in expression position $e$, not in
 command sequences $m_1; m_2$; and every `W13` refutation is relative to the
 recorded L3 inventory (F7 second cost).
14. **`OBL-PRICED-INTERVAL-SOUNDNESS`** *(explicitly restricted to the core
 §8.3 consumer transformer slice; discharged through `stdCSS-3` on that
 scope).* Covers `C-SKIP`, `C-ADD-CHECK`, `C-DELETE-CHECK`, `E-GRAFT`,
 `C-DIRECT-SUM`, and `C-SEQUENCE` (§4.13). The six Gate 6 cells are governed
 separately by `OBL-GATE6-CSS-EXTENSIONS` (§4.32, including the 2026-11-10
 `E-PEEL` price cells of §4.28); the ten `stdCSS-3` constructors carry no
 distance rule and initialize ledgers at $[0, +\infty)$ (§2g, trivially
 sound); and the 2026-11-18 axis-3 additions (§2h–§2j) modify no distance
 interval endpoint.

**Consequence for kernel rung 6 (`contract-proved`).** Together with §4.1–§4.11,
§4.13–§4.19, §4.21–§4.25, §4.37, and §4.39, every transition, applicability
condition, exact state/context update, unconditional theorem-level judgment,
conditional carry cell (with stated hypotheses), and scoped metatheorem
re-discharge for the five kernel operations (`C-SKIP`, `C-DIRECT-SUM`,
`C-DELETE-CHECK`, `C-ADD-CHECK`, `C-SEQUENCE`) now carries a dated hand
derivation in this repository. This satisfies the `spec/CLAIMS.md` definition
of rung 6 (`contract-proved`). It does **not** establish rung 7 (`mechanized`),
does **not** ratify Gates 2–7, and does **not** promote any claim in the
`AUTHORITY.md` §B4 review-disposition sense without independent review and
maintainer confirmation. $\square$

## 4.41 `L-MAPPING-CONE`: output well-formedness and the parameter bookkeeping (`OBL-WELL-FORMEDNESS-PRESERVATION`, constructor instance)

Dated hand derivation, 2026-11-18. Evidence, not a
machine-checked proof. It covers `L-MAPPING-CONE`, admitted as
`transition-defined` on this date (§2 card).

**Setting.** Let $\partial_A$ be an $a_1 \times a_0$ binary matrix,
$\partial_B$ a $b_1 \times b_0$ matrix, $f_1$ an $a_1 \times b_1$
matrix, and $f_0$ an $a_0 \times b_0$ matrix, satisfying the chain-map
premise $\partial_B f_1 = f_0 \partial_A$. The matrices are read as
linear maps $\partial_A \colon A_1 \to A_0$, $\partial_B \colon B_1 \to B_0$,
$f_1 \colon A_1 \to B_1$, and $f_0 \colon A_0 \to B_0$, with $A$ and $B$
two-term complexes. The cone has $C_2 = A_1$, $C_1 = A_0 \oplus B_1$, and
$C_0 = B_0$, with $\delta_2(a_1) = (\partial_A a_1, f_1 a_1)$ and
$\delta_1(a_0, b_1) = f_0 a_0 + \partial_B b_1$.

**Well-formedness and $n$.** The premise gives $\delta_1 \delta_2 = 0$, so
the natural $Z$-rows (one per basis element of $A_1$, the support of
$\delta_2$) and the natural $X$-rows (one per basis element of $B_0$, the
corresponding row of $\delta_1$) have pairwise even overlap. (The chain-map
premise is equivalent to this overlap: the $(j,r)$ entry of
$f_0\partial_A+\partial_Bf_1$ is the overlap of $Z$-row $j$ with $X$-row $r$.
The Lean rule takes the commutation side, `naturalCommuteBool` of the natural
rows, as its premise.) Hence, by the claim of §4.34, the retained display
is a well-formed state on the labels $0, \ldots, a_0 + b_1 - 1$, and
$n = \dim A_0 + \dim B_1 = a_0 + b_1$. The first $a_0$ labels are the
basis of $A_0$ and the remaining $b_1$ labels the basis of $B_1$.

**The count $k$.** The retained display of a sector spans the natural row
space of that sector (§4.34), so $k$ is rank bookkeeping over the
constructed display. Write $Z(A)=\ker\partial_A$, $Z(B)=\ker\partial_B$,
and let $\bar f_0\colon A_0/\operatorname{im}\partial_A \to
B_0/\operatorname{im}\partial_B$ be the map induced by $f_0$ (well-defined
by the premise). Let $\pi$ send the class of a cycle $(a_0,b_1)$ to the
class of $a_0$ in $A_0/\operatorname{im}\partial_A$, and $\iota$ send
$b\in Z(B)$ to the class of $(0,b)$. Then $\pi$ is well-defined with
image $\ker\bar f_0$, $\ker\pi=\operatorname{im}\iota$, and
$\iota(b)=0$ iff $b\in f_1(Z(A))$. Hence the space of classes has
dimension $\dim\operatorname{im}\iota+\dim\ker\bar f_0$, with
$\operatorname{im}\iota\cong Z(B)/f_1(Z(A))$, giving

$$
k = \dim Z(B) - \dim f_1(Z(A)) + \dim \ker \bar f_0.
$$

**The sector distances (conditional, not cells).** A nonzero class is of
exactly one of two kinds: either its image under $\pi$ is nonzero, with
representative $(a_0,b_1)$ satisfying $a_0\notin\operatorname{im}\partial_A$;
or it is $\iota(b)$ for some $b\in Z(B)\setminus f_1(Z(A))$. Define

$$
D_A=\min\{\lVert a_0\rVert+\lVert b_1\rVert :
 f_0a_0=\partial_Bb_1,\ a_0\notin\operatorname{im}\partial_A\},
$$

$$
D_B=\min\{\lVert\partial_Aa_1\rVert+\lVert f_1a_1+b\rVert :
 a_1\in A_1,\ b\in Z(B)\setminus f_1(Z(A))\},
$$

each $+\infty$ when empty. Then

$$
d_Z(C(f)) = \min(D_B, D_A).
$$

The constructor computes no distance.
The ledger starts at $[0, +\infty)$. A consumer that supplies sourced
lower bounds $\ell_B \le D_B$ and $\ell_A \le D_A$ obtains the lower
endpoint $\min(\ell_B, \ell_A)$, and $\ell_B$ alone when $\bar f_0$ is
injective (decidable by rank). Upper endpoints come from validated
witnesses in $B$ (§3.2). The other sector is the same statement for the
transposed input (§3.3). No distance value is asserted by the transition.

**What this does not settle.** Validation of supplied bounds or of
exhaustive minimum-weight-class enumerations; weighted norms on the factors;
cones of maps between longer complexes. The Lean mechanization is partial.
`lean/CodeCalculus/Term.lean` and `Eval.lean` carry the production and its
`EvalExpr` rule, with the state update in `Constructors.lean`. Proved in
Lean (`ConstructorAssembly.lean`): $n$ (`evalExpr_cone_n`), output
well-formedness (`evalExpr_cone_wf`), and the rank statement
`evalExpr_cone_k` (an instance of `stateK_constructedState`), the rule
carrying the commutation of the natural rows as its premise (equivalent to
the chain-map premise, not yet mechanized). Not in Lean: the closed form
for $k$ read on the complexes, the conditional distance cells, and the
transposed duality. Evidence: `machine/test_mapping_cone.py` pins two
instances and the premise refusal; `machine/test_constructor_lean.py` pins
the Lean production. Agreement is evidence that the derivation is
transcribed as stated, not a proof. The constructor instance of
`OBL-WELL-FORMEDNESS-PRESERVATION` is discharged by this section for
`L-MAPPING-CONE`. $\square$


## 4.42 CSS-preserving column CNOT/SWAP transformation

Dated hand derivation, 2026-11-18. Evidence, not a machine-checked proof.

**Setting.** Let $C$ be a well-formed CSS state on qubits $Q$ with $n=|Q|$,
check matrices $H_X, H_Z \in \mathbb{F}_2^{m_X \times n}, \mathbb{F}_2^{m_Z \times n}$.
Let $U \in \mathrm{GL}(n,2)$. Define $C' = \mathrm{cnotSwap}_U(C)$ by

$$
 H_X' = H_X U^{-1}, \qquad H_Z' = H_Z U^{\mathsf{T}},
$$

with the same qubit set $Q$ and the same identifiers (no minting). The
orthogonality premise is preserved:

$$
 H_X' (H_Z')^{\mathsf{T}} = H_X U^{-1} U H_Z^{\mathsf{T}} = H_X H_Z^{\mathsf{T}} = 0.
$$

**Identifier retention (agreement with `P-REBASE`, §4.26).** No row is added or
removed and no generator is renamed: each displayed row keeps its identifier,
and only its support vector changes. This differs from `P-REBASE`, which
mints fresh identifiers because it replaces a sector's display by new basis
vectors $V_\tau M$; here the display set is the same set of rows, so no
minting occurs and `used` is unchanged. The capacity premise (H-4) is
therefore vacuously satisfied. `pres` keeps its qubit namespace, sector
labels, and identifier set; only the supports of the displayed rows are
rewritten. Carried witnesses are **not** automatically valid: a parent-valid
logical witness is a subset of $Q$ whose membership in the normalizer depends
on the row spans, and those spans change under $U$; the witness's support must
be transported by the appropriate sector map and revalidated in the child before
it can tighten an endpoint. The consumer drops or revalidates witnesses rather
than carrying them blindly. $\square$

**Output well-formedness.** I1 carries: orthogonality is shown above. I2
carries: multiplication by the invertible matrix $U^{-1}$ (respectively
$U^{\mathsf{T}}$) preserves linear independence of the displayed rows in each
sector. I3 carries: no identifiers are minted or retired, and `used` is
unchanged, so injectivity and non-reuse are untouched. I4 carries: every
displayed row keeps its sector label, and the rewritten row spans the same
sector's (transformed) space. I5 carries: provenance records are append-only
and no identifier is reused or removed from `used`. Hence $C'$ is a
well-formed CSS display (`OBL-WELL-FORMEDNESS-PRESERVATION`). $\square$

**Parameter bookkeeping.** $n' = n$ and $k' = n - \mathrm{rank}(H_X') -
\mathrm{rank}(H_Z') = n - \mathrm{rank}(H_X) - \mathrm{rank}(H_Z) = k$,
since multiplication by an invertible matrix preserves rank. The interaction
radius and the maximum row weight are recomputed on the image display; no
monotonicity claim is made. $\square$

**Distance.** The two sectors transform by different matrices. A $Z$-type
logical (a vector $z$ with $H_X z = 0$) maps to $U z$ in $C'$, because
$H_X' (U z) = H_X U^{-1} U z = H_X z = 0$. An $X$-type logical (a vector
$x$ with $H_Z x = 0$) maps to $U^{-\mathsf{T}} x$, because
$H_Z' (U^{-\mathsf{T}} x) = H_Z U^{\mathsf{T}} U^{-\mathsf{T}} x = H_Z x = 0$.
Define the four matrix norms

$$
\begin{aligned}
\rho_Z &= \max_{j} \mathrm{wt}(\text{column } j \text{ of } U), \\
\rho_Z^- &= \max_{j} \mathrm{wt}(\text{column } j \text{ of } U^{-1}), \\
\rho_X &= \max_{j} \mathrm{wt}(\text{column } j \text{ of } U^{-\mathsf{T}})
 = \max_{i} \mathrm{wt}(\text{row } i \text{ of } U^{-1}), \\
\rho_X^- &= \max_{j} \mathrm{wt}(\text{column } j \text{ of } U^{\mathsf{T}})
 = \max_{i} \mathrm{wt}(\text{row } i \text{ of } U).
\end{aligned}
$$

For the $Z$ sector, the map is $U$, so
$\mathrm{wt}(U z) \le \rho_Z \, \mathrm{wt}(z)$ and
$\mathrm{wt}(z) \le \rho_Z^- \, \mathrm{wt}(U z)$; hence

$$
\lceil d_Z / \rho_Z^- \rceil \le d_Z' \le \rho_Z \, d_Z .
$$

For the $X$ sector, the map is $U^{-\mathsf{T}}$, so the same argument with
$\rho_X, \rho_X^-$ gives

$$
\lceil d_X / \rho_X^- \rceil \le d_X' \le \rho_X \, d_X .
$$

No equality is claimed; the universal equality tail stays open. $\square$

**Hamming-weight non-invariance.** For general $U$, $\mathrm{wt}(H_X' \text{ row})$
need not equal $\mathrm{wt}(H_X \text{ row})$; a single column CNOT can
increase it. No generic CNOT layer is modelled as zero-price. $\square$

## 4.43 Nullary, base, and interface constructors: output well-formedness and parameters (`OBL-WELL-FORMEDNESS-PRESERVATION`)

Dated hand derivation, 2026-11-19. Evidence, not a
machine-checked proof. It covers `L-EMPTY`, `L-FREE`, `A-PULLBACK`, and
`A-PUSHOUT`, admitted as `transition-defined` expression constructors on this
date (§2 cards).

**`L-EMPTY` (`empty`) and `L-FREE` (`free(Q)`).** For any finite set
$Q \subset \mathbb{N}$ of distinct nonnegative integers stored in strictly
increasing order, `free(Q)` produces $C = (Q, \varnothing, \varnothing, [], \varnothing)$
(and `empty` is the $Q = \varnothing$ case). Because `rows` and `used` are
empty, I1 ($X \perp Z$, with $X = Z = \{0\}$), I2 (displayed independence), I3
(identifier discipline), I4 (sector typing), I5 (`ValidProvenance`), and
ambient containment hold vacuously; $Q$ is duplicate-free and strictly
increasing by typing. Thus the output is well-formed (`wf_emptyState` /
`wf_freeState` in Lean). Parameters: $n = |Q|$, $\dim X = \dim Z = 0$, so
$k = |Q|$; $w = 0$; Tanner components $\kappa = |Q|$ (every qubit is an
isolated vertex with no check vertices); $r = 0$ under any supplied honest
layout on $Q$.

*Semantic distances (not automatic §2g ledger rules).* When $Q = \varnothing$
(`empty` or `free(∅)`), $k = 0$ and no $\sigma$-logical exists in either sector,
so $d_X = d_Z = d = +\infty$. When $Q \neq \varnothing$, $X = Z = \{0\}$ and
every singleton $\{q\}$ ($q \in Q$) has even overlap with $\varnothing$ and lies
outside $\{0\}$, so $\{q\}$ is a weight-$1$ logical in both sectors; since $0$ is
not a logical, $d_X = d_Z = d = 1$. Under `JUDGMENT_LAYER.md` §2g,
`DistanceLedger.for_constructed` starts at $[0, +\infty)$ unless a sourced
lower bound or validated witness (such as $\{q\}$ for $Q \neq \varnothing$)
is supplied.

**`A-PULLBACK` (`pullback(e₁, e₂, e_I; φ₁, φ₂)`).** Let $C_1, C_2, I$ be
well-formed CSS states and $\phi_i : Q_i \to Q_I$ ($i = 1, 2$) be total qubit
maps. Each natural row of the card is a subset of $\{0, \dots, n - 1\}$ paired
with a sector $\sigma \in \{X, Z\}$, where $n = |Q_1 \times_{Q_I} Q_2|$. Under
the applicability premise that the natural rows of the two sectors have
pairwise even overlap, the retained-display theorem of §4.34 (`wf_constructedState`
in Lean) implies that the retained display with canonically minted identifiers
from empty `used` satisfies I1–I5 and ambient containment on $\{0, \dots, n-1\}$.
Notice that even when $n = 0$ (empty fiber product), the supports are all
$\varnothing \subseteq \varnothing$ and the output is well-formed (`emptyState 0`
with zero rows retained, or empty display). Parameters: $n = |Q_1 \times_{Q_I} Q_2|$
exact; $k = n - \dim X - \dim Z$ by rank bookkeeping over the retained display;
$w, \kappa, r$ recomputed over the constructed display (§2d.5, §2g).
*Set-level equalizers:* for parallel maps $f, g : C_1 \rightrightarrows I$,
taking $C_2 = C_1$, $\phi_1 = f$, and $\phi_2 = g$ restricts to the equalizer
subspace $\{q_1 \in Q_1 : f(q_1) = g(q_1)\}$ on the diagonal pairs, so
set-level equalizers factor through `A-PULLBACK`, as the disposition above notes.

**`A-PUSHOUT` (`pushout(e₁, e₂, e_S; ψ₁, ψ₂)`).** Let $C_1, C_2, S$ be
well-formed CSS states and $\psi_i : Q_S \to Q_i$ ($i = 1, 2$) be total qubit
maps. The quotient $Q_1 \sqcup_{Q_S} Q_2$ has $n$ equivalence classes relabeled
$0, \dots, n - 1$. Each natural row of the card is a subset of $\{0, \dots, n - 1\}$
paired with a sector $\sigma \in \{X, Z\}$. Under the applicability premise that
the natural rows of the two sectors have pairwise even overlap, §4.34
(`wf_constructedState` in Lean) implies that the retained display with
canonically minted identifiers from empty `used` satisfies I1–I5 and ambient
containment. Parameters: $n = |Q_1 \sqcup_{Q_S} Q_2|$ exact;
$k = n - \dim X - \dim Z$ by rank bookkeeping over the retained display;
$w, \kappa, r$ recomputed over the constructed display (§2d.5, §2g).
*Two-code set-level coequalizers:* identifying pairs $(q_1, q_2)$
witnessed by $Q_S$ via $\psi_1, \psi_2$ is the pushout construction itself.

**Distance cells.** Neither `A-PULLBACK` nor `A-PUSHOUT` carries an automatic
distance rule: the naive pullback lower bound $d(A \times_C B) \ge \min(d_A, d_B)$
is `false` (`the left-in-papers note` §6.3), and a general pushout along a
nontrivial shared subcode $S \neq 0$ can drop distance (`the left-in-papers note`
claims 3.5, 4.1), so factor minima do not carry unconditionally. Both ledgers
start at $[0, +\infty)$ per `JUDGMENT_LAYER.md` §2g.

The constructor instances of `OBL-WELL-FORMEDNESS-PRESERVATION` are discharged
by this section for `L-EMPTY`, `L-FREE`, `A-PULLBACK`, and `A-PUSHOUT`. ∎



## Disposition (2026-11-10)

The following were accepted for work in v0.2 and are not discharged by this
disposition:

- **Re-exposure hardness in constrained splits**: landed
 2026-11-11 as §4.33 and `OBL-GLUE-RE-EXPOSURE`: under the
 admitted `E-GLUE` no class is re-exposed, so the quantity is $+\infty$
 there and the polynomiality question does not arise; the NP-hardness
 boundary stays recorded against shared-interface splits, which the
 calculus does not admit.
- **Distance-increasing constructor admission**: `L-HGP`,
 `L-LIFTED`, `L-BALANCED`, `L-GROUP-ALGEBRA`, `L-TANNER`, `L-TILE`,
 `A-CONCAT`, `A-PRODUCT`, `A-DOUBLE` as typed constructors with explicit
 distance hypotheses; typed signatures already recorded in
 `CONSTRUCTOR_SIGNATURES.md`. Partially landed 2026-11-11: `L-HGP`, `L-LIFTED`, `L-GROUP-ALGEBRA`, and `A-CONCAT` have
 expression productions (`TERM_LANGUAGE.md` §2), §2 cards, and the §4.34
 derivation, at `transition-defined`. Landed in full 2026-11-11: `L-BALANCED`, `L-TANNER`, `L-TILE`, `A-PRODUCT`, and `A-DOUBLE` have
 productions, §2 cards, and the §4.35 derivation, at `transition-defined`.
- **Gluing promotion**: promote `E-GLUE` from conditional
 lower-bound connector to a licensed connected-code composition with
 seam-certificate equality, once the logical-witness prerequisite lands.
- **Sector-swap exploitation**: consumer support for
 `E-LOCAL-HADAMARD` (`T=Q`) targeting, plus a derived cell if needed.

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
2026-10-20); its Lean forms `judgment_soundness` / `judgment_soundness_of_term`
(`lean/CodeCalculus/TermSoundness.lean`, over the `Nat`-valued sentinel
reading) and `ext_judgment_soundness` (`lean/CodeCalculus/ExpandedSoundness.lean`, over `ExtNat`) are stated for a well-formed evaluation chain, with
the `k` cells discharged via `ranksFit_of_wf` and the distance cells taking
`MeasureMonotone` (discharged for the exact sector distance in
`judgment_soundness_exact` / `extMeasureLaws_exact`); and promoted
remains a review disposition. The obligations themselves
are tracked in [`OBLIGATIONS.md`](OBLIGATIONS.md); it is their ledger, and this
section does not restate it.
