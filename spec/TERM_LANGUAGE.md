# Term Language

**Status:** normative. The syntax of what can be written, and what cannot.

---

## 1. Two syntactic categories

State expressions and commands are separate. They are never composed as if both
were functions.

$$
e \;::=\; S \;\mid\; e_1 \oplus e_2 \;\mid\; \mathrm{glue}(e_1, e_2; \vec u)
$$

where $\mathrm{glue}(e_1, e_2; \vec u)$ (`E-GLUE`, binary-only expression
constructor decided 2026-11-18; no unary command production)
combines two disjoint state expressions with an ordered list $\vec u$ of
typed seam checks $(\tau_i, \mathrm{supp}_i)$ (`OPERATIONAL_SEMANTICS.md` §4.31).

and, since 2026-11-11, the four admitted typed constructors
extend the expressions by

$$
e ::= \mathrm{hgp}(H_1, H_2) \mid \mathrm{lift}_G(A, B) \mid \mathrm{twoblock}_G(a, b) \mid \mathrm{concat}(e_O, e_I; \vec B)
$$

where $H_1$ and $H_2$ are binary matrices, $G$ is a finite group given either
by its abelian cyclic orders or (since 2026-11-22) by an explicit multiplication
table or permutation-generator presentation, $A$ and $B$ are matrices and $a$
and $b$ elements of the group algebra $\mathbb{F}_2[G]$, and $\vec B$ is a block
partition of the outer state's qubits (`OPERATIONAL_SEMANTICS.md` §2 cards).

Since 2026-11-11 the other five accepted constructors extend
the expressions by

$$
e ::= \mathrm{product}(e_A, e_B) \mid \mathrm{double}_{w,s}(e) \mid \mathrm{balanced}_G(H_1, \alpha_1; H_2, \alpha_2) \mid \mathrm{tanner}(n; \Lambda_X, \Lambda_Z; \iota_X, \iota_Z) \mid \mathrm{tile}(\tau; \alpha; \beta)
$$

The typed inputs are finite objects, defined on the cards of
`OPERATIONAL_SEMANTICS.md` §2. In `product`, $e_A$ and $e_B$ are state
expressions. In `double`, $w$ is a wiring map from the displayed row
identifiers of the value of $e$ to subsets of their supports and $s$ is an
optional sector-duality flag. In `balanced`, $G$ is a finite group given by its
abelian cyclic orders or (since 2026-11-22) by an explicit multiplication table
or permutation-generator presentation, $H_1$ and $H_2$ are binary matrices, and
$\alpha_1$ (a right action on $H_1$) and $\alpha_2$ (a left action on $H_2$) are
equivariant actions of $G$ on their row and column indices by permutations. In `tanner`, $n$ is a qubit count, $\Lambda_X$ and
$\Lambda_Z$ are binary matrices of local checks, and $\iota_X$ and $\iota_Z$
are lists of vertex embeddings. In `tile`, $\tau$ is a list of tiles,
$\alpha$ a list of placements on sites, and $\beta$ the boundary rules (site
identifications and removed checks).

Since 2026-11-13 the expressions also include

$$
e ::= \mathrm{nested}(H_X, H_Z)
$$

where $H_X$ and $H_Z$ are binary matrices with the same number of columns,
the parity-check matrices of two classical codes of one length
(`OPERATIONAL_SEMANTICS.md` §2 card).

Since 2026-11-19 the expressions also include the nullary and
qubit-set base constructors and the two interface constructors

$$
e ::= \mathrm{empty} \mid \mathrm{free}(Q) \mid \mathrm{pullback}(e_1, e_2, e_I; \phi_1, \phi_2) \mid \mathrm{pushout}(e_1, e_2, e_S; \psi_1, \psi_2)
$$

where $Q \subset \mathbb{N}$ is a finite set of distinct qubit labels,
$\phi_i : Q_i \to Q_I$ are CSS code morphisms from the values of $e_1, e_2$
to the value of $e_I$, and $\psi_i : Q_S \to Q_i$ are CSS code morphisms
from the value of $e_S$ to the values of $e_1, e_2$ (`OPERATIONAL_SEMANTICS.md`
§2 cards).

Since 2026-11-22 the expressions also include the pair-partition relative-permutation
constructor and its explicit size-scaling specialization

$$
e ::= \mathrm{pair\_partition}(p; B_X, B_Z) \mid \mathrm{pp\_scale}(e; P)
$$

where in `pair_partition` $p \ge 1$ is a lift size and $B_X, B_Z$ are block matrices
of affine permutation descriptors $(a, b) \in \mathbb{Z}_p^\times \times \mathbb{Z}_p$
with an even block-column count $L \ge 2$ (`OPERATIONAL_SEMANTICS.md` §2 card, §4.46),
and in `pp_scale` $e$ is a state expression whose value is a PP-presented CSS code and
$P \ge 2$ is a target lift size (`OPERATIONAL_SEMANTICS.md` §2 card, §4.47,
`OBL-PP-SCALE`). The PP-parameter bundle (pair partition, Smith-normal-form data,
fixed shift vector) is constructor-side data, not part of $C = (Q, X, Z, \mathsf{pres}, \mathsf{used})$.

$$
m \;::=\; \mathrm{skip}
\;\mid\; \mathrm{delete}_r
\;\mid\; \mathrm{addStab}_r
\;\mid\; \mathrm{graft}_{q,\tau;\vec r}
\;\mid\; \mathrm{peel}_{q,\tau;r}
\;\mid\; \mathrm{puncture}_q
\;\mid\; \mathrm{extend}_{\Delta;\vec u}
\;\mid\; \mathrm{hadamard}_T
\;\mid\; \mathrm{rebase}_{\tau;M}
\;\mid\; \mathrm{cnotSwap}_U
\;\mid\; m_1; m_2
$$

A **closed construction term** is $m\triangleright e$: evaluate the state
expression $e$, then execute command $m$ against the result. The base expression
$S$ denotes a presented phase-insensitive CSS state.

So $e$ always denotes a state and $m$ denotes a *partial* state transformer.
`C-DIRECT-SUM` is an expression constructor, **not** a command.

## 2. Kernel and admitted construction extension

| Taxonomy ID | Kind | Production | Notation |
| --- | --- | --- | --- |
| `C-SKIP` | command | $m ::= \mathrm{skip}$ | `skip` |
| `C-DIRECT-SUM` | expression-constructor | $e ::= e_1\oplus e_2$ | `e₁ ⊕ e₂` |
| `E-GLUE` | expression-constructor | $e ::= \mathrm{glue}(e_1, e_2; \vec u)$ | `glue(e₁, e₂; [(τ₁,u₁),…])` — binary-only (decided 2026-11-18; no unary command production) |
| `C-DELETE-CHECK` | command | $m ::= \mathrm{delete}_r$ | `delete_r` |
| `C-ADD-CHECK` | command | $m ::= \mathrm{addStab}_r$ | `addStab_r` |
| `E-GRAFT` | command | $m ::= \mathrm{graft}_{q,\tau;\vec r}$ | `graft(q, τ; [r₁,…,rₘ])` |
| `E-PEEL` | command | $m ::= \mathrm{peel}_{q,\tau;r}$ | `peel(q, τ; r)` |
| `E-PUNCTURE` | command | $m ::= \mathrm{puncture}_q$ | `puncture(q)` |
| `E-EXTEND` | command | $m ::= \mathrm{extend}_{\Delta;\vec u}$ | `extend(Δ; [(τ₁,u₁),…])` |
| `E-LOCAL-HADAMARD` | command | $m ::= \mathrm{hadamard}_T$ | `hadamard(T)` — admitted for $T=Q$ or $T=\varnothing$ |
| `P-REBASE` | command | $m ::= \mathrm{rebase}_{\tau;M}$ | `rebase(τ; M)`, $M\in\mathrm{GL}(m,2)$ |
| `C-COLUMN-CNOT` | command | $m ::= \mathrm{cnotSwap}_U$ | `cnotSwap(U)`, $U\in\mathrm{GL}(Q,2)$ (admitted 2026-11-18) |
| `L-HGP` | expression-constructor | $e ::= \mathrm{hgp}(H_1,H_2)$ | `hgp(H₁, H₂)`, two binary matrices (admitted 2026-11-11) |
| `L-LIFTED` | expression-constructor | $e ::= \mathrm{lift}_G(A,B)$ | `lift_G(A, B)`, $G$ a finite group (abelian by cyclic orders, or nonabelian via an explicit multiplication table / permutation generators), $A$ and $B$ matrices over $\mathbb{F}_2[G]$ (admitted 2026-11-11; generalized 2026-11-22) |
| `L-GROUP-ALGEBRA` | expression-constructor | $e ::= \mathrm{twoblock}_G(a,b)$ | `twoblock_G(a, b)`, $a, b \in \mathbb{F}_2[G]$ for a finite group $G$ (abelian or nonabelian, with explicit left/right regular representations) (admitted 2026-11-11; generalized 2026-11-22) |
| `A-CONCAT` | expression-constructor | $e ::= \mathrm{concat}(e_O, e_I; \vec B)$ | `concat(e_O, e_I; blocks)`, CSS outer and inner factors with a block partition (admitted 2026-11-11) |
| `A-PRODUCT` | expression-constructor | $e ::= \mathrm{product}(e_A, e_B)$ | `product(e_A, e_B)`, the CSS tensor product of two well-formed CSS states (admitted 2026-11-11) |
| `A-DOUBLE` | expression-constructor | $e ::= \mathrm{double}_{w,s}(e)$ | `double(e; wiring[, conjugate])`, the two-sheet cover under a wiring map; no derivation unless the lifted rows commute (admitted 2026-11-11) |
| `L-BALANCED` | expression-constructor | $e ::= \mathrm{balanced}_G(H_1,\alpha_1;H_2,\alpha_2)$ | `balanced_G(H₁, α₁; H₂, α₂)`, binary matrices equivariant under permutation actions of a finite group (abelian or nonabelian, with explicit left/right actions) (admitted 2026-11-11; generalized 2026-11-22) |
| `L-TANNER` | expression-constructor | $e ::= \mathrm{tanner}(n;\Lambda_X,\Lambda_Z;\iota_X,\iota_Z)$ | `tanner(n; Λ_X, Λ_Z; ι_X, ι_Z)`, local checks on the two vertex classes of an incidence structure; no derivation unless the local checks of the two classes commute (admitted 2026-11-11) |
| `L-TILE` | expression-constructor | $e ::= \mathrm{tile}(\tau;\alpha;\beta)$ | `tile(tiles; placements; boundary rules)`; no derivation unless the placed rows of the two sectors commute (admitted 2026-11-11) |
| `L-NESTED-CSS` | expression-constructor | $e ::= \mathrm{nested}(H_X,H_Z)$ | `nested(H_X, H_Z)`, two binary parity-check matrices with equally many columns; no derivation unless every row of the one has even overlap with every row of the other (admitted 2026-11-13) |
| `L-MAPPING-CONE` | expression-constructor | $e ::= \mathrm{cone}(\partial_A,\partial_B,f_1,f_0)$ | `cone(∂_A, ∂_B, f_1, f_0)`, four binary matrices with the chain-map premise $\partial_B f_1 = f_0 \partial_A$; no derivation unless the premise holds (admitted 2026-11-18) |
| `L-EMPTY` | expression-constructor | $e ::= \mathrm{empty}$ | `empty`, the 0-qubit CSS code with empty display and empty `used` (admitted 2026-11-19) |
| `L-FREE` | expression-constructor | $e ::= \mathrm{free}(Q)$ | `free(Q)`, the check-free CSS code on a finite qubit-label set $Q \subset \mathbb{N}$ (admitted 2026-11-19) |
| `A-PULLBACK` | expression-constructor | $e ::= \mathrm{pullback}(e_1, e_2, e_I; \phi_1, \phi_2)$ | `pullback(e₁, e₂, e_I; φ₁, φ₂)`, fiber product along CSS code morphisms $\phi_i : C_i \to I$; no derivation unless $\phi_i$ are CSS code morphisms and the pulled-back rows commute (admitted 2026-11-19) |
| `A-PUSHOUT` | expression-constructor | $e ::= \mathrm{pushout}(e_1, e_2, e_S; \psi_1, \psi_2)$ | `pushout(e₁, e₂, e_S; ψ₁, ψ₂)`, amalgamated sum along CSS code morphisms $\psi_i : S \to C_i$; no derivation unless $\psi_i$ are CSS code morphisms and the pushed-forward rows commute (admitted 2026-11-19)
| `L-PAIR-PARTITION` | expression-constructor | $e ::= \mathrm{pair\_partition}(p; B_X, B_Z)$ | `pair_partition(p; B_X, B_Z)`, paired affine/circulant permutation block matrices over lift size $p \ge 1$ with even column count $L \ge 2$; no derivation unless the paired relative affine maps match on each block-row pair so the natural rows commute (admitted 2026-11-22) |
| `PP-SCALE` | expression-constructor | $e ::= \mathrm{pp\_scale}(e; P)$ | `pp_scale(e; P)`, explicit extension of a PP-presented CSS code $e$ to target lift size $P \ge 2$; no derivation unless the input is PP-presented with unit slopes, the PP conditions and SNF reproduction check pass, $k' > 0$, and the generated rows commute (promoted 2026-11-22) |

| `C-SEQUENCE` | command | $m ::= m_1;m_2$ | `m₁ ; m₂` |
| `P-RELABEL` | presentation-operation | **none** | — |

`E-GRAFT` is an in-scope conditional construction transition. Its syntax names
the qubit $q$, spliced sector $\tau$, and ordered list of displayed row IDs;
that list must contain exactly the selected-sector rows touching $q$. Distance
prices are judgment inputs, not command arguments or state fields.

`E-PEEL`, `E-PUNCTURE`, `E-EXTEND`, `E-LOCAL-HADAMARD` (the $T=Q$
sector-swap instance only) and `P-REBASE` were added as commands on
2026-10-23, under the same decision that admitted their conditional cells
(`JUDGMENT_LAYER.md` §2f); their transitions are typed at
`OPERATIONAL_SEMANTICS.md` §2 and their sound admission — the Gate 6
extensions' soundness obligation — is discharged under the stated hypotheses
(`OBL-GATE6-CSS-EXTENSIONS`, §4.32). Distances carry no command argument for any of
these: every conditional distance hypothesis remains a judgment input. The
general split-subset instance of the local Hadamard
($\varnothing\subsetneq T\subsetneq Q$) is **not** a command: the term
`hadamard(T)` is admitted for $T=Q$ (the sector exchange of the whole
display) and for $T=\varnothing$ (the identity); it is inapplicable for any
other $T$ (`OPERATIONAL_SEMANTICS.md` §2, §4.27). A $T$ that lists a label
twice is **malformed** rather than inapplicable: a list with repeats does not
name a subset, so there is no reading of it as one.

`E-GLUE` remains **binary-only, with no unary command production** (dated
maintainer decision 2026-11-18): gluing combines two disjoint
factor states rather than transforming a single presented state, so it sits in
the expression grammar as the binary state-expression constructor
$e ::= \mathrm{glue}(e_1, e_2; \vec u)$ beside $\oplus$ (§1, §2; admitted
evaluator transition at `OPERATIONAL_SEMANTICS.md` §4.31). `EvalExpr` evaluates
both factors to presented states first (`StateExpr.glue` / `EvalExpr.glue` in
`lean/CodeCalculus/Term.lean` and `Eval.lean`); on well-formed factors this is
proved equivalent to the closed term
`⟨glueCommand seams, directSum (base A) (base B)⟩`
(`evalExpr_glue_iff_evalTerm_glueCommand` in `lean/CodeCalculus/GlueExtraction.lean`)
and matches `Eval(glue(C_A, C_B; seam checks), C)` in `machine/semantics.json`.
Both future-$\Pi$ fields (`STATE_MODEL.md` §1a) are defined outside the state,
and the §2e/§2f conditional cell remains conditional on its seam-certificate
hypothesis. `P-RELABEL` has **no** grammar production; it is a congruence
to be proved, not a command.

`P-REBASE` is admitted as a command expressing a full basis change of one
sector's row space. It is a different thing from the retained-presentation data
shape of the same name, which is a signature field of a later-layer constructor.

Other `E-*` moves need support/interface predicates,
`A-*` and `L-*` constructors need typed classical, algebraic, graph or cellulation
inputs, and `X-*` needs an extended state model.

## 3. Well-formed terms

- $\mathrm{delete}_a\triangleright S$
- $(\mathrm{delete}_a;\mathrm{addStab}_b)\triangleright S$
- $m\triangleright (S\oplus T)$
- $m\triangleright \mathrm{glue}(S, T; [(X, \{0, 2\})])$
- $\mathrm{graft}_{q,X;[a_1,a_2]}\triangleright S$
- $\mathrm{peel}_{q,Z;a}\triangleright S$
- $\mathrm{puncture}_a\triangleright S$
- $\mathrm{extend}_{\{5\};\,(X,\{1,5\})}\triangleright S$
- $\mathrm{hadamard}_{Q}\triangleright S$
- $\mathrm{rebase}_{X;M}\triangleright S$ with $M\in\mathrm{GL}(m_X,2)$
- $\mathrm{skip}\triangleright S$
- $\mathrm{delete}_a\triangleright \mathrm{hgp}(H_1,H_2)$ (a constructed state in expression position)
- $m\triangleright \mathrm{concat}(S, T; \vec B)$

## 4. Malformed — rejected by the grammar alone

| Term | Why |
| --- | --- |
| $S\triangleright S$ | a state in command position; $\triangleright$'s left side is a command |
| $\mathrm{delete}_a\triangleright \mathrm{skip}$ | a command in expression position; $e$ never contains commands |
| $(\mathrm{delete}_a\triangleright S);m$ | a closed term is not a command; `;` composes commands only |
| $(m\triangleright S)\oplus(m'\triangleright T)$ | $\oplus$ combines state expressions, not terms |
| $m_1;m_2\triangleright (e_1;e_2)$ | `;` is undefined on state expressions |
| $\mathrm{hgp}(S, H)$ | a state in matrix position; the constructor's inputs are binary matrices, not expressions |

## 5. Well-typed but inapplicable is a third thing

$\mathrm{delete}_a\triangleright S$ is a **well-typed term with no
evaluation derivation** when $a$ is not displayed in $S$. This is not
malformation and not `false`; it is `no_derivation`, and *absence of derivation
is part of the semantics, not a failure of it*.

The three are distinct outcomes and the fixture suite keeps them distinct.

## 6. Notation

Sequencing is conventional left-to-right: $m_1;m_2$ executes $m_1$ first, and
the second command's applicability is checked against the **intermediate** state,
not the original.

Two presentations are equivalent only when a finite qubit relabeling transports
qubits, displayed rows, generator identifiers, and sector labels. Direct sum is a
separate matter: it is associative and commutative as literal equality of labeled
states on unordered presentations, with disjointness premises — a metatheorem
discharged at `OBL-DIRECT-SUM-LAWS` (`OPERATIONAL_SEMANTICS.md` §4.8,
re-evidenced 2026-10-29 and re-discharged through `stdCSS-3` at §4.40), not
assumed.

## 7. What this document does not do

It gives the syntax only. Whether a well-typed term has an evaluation
derivation, and what state it yields, is
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md). What the calculus can
*claim* about the resulting state is
[`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md).

**Disposition (2026-11-10) and admission (2026-11-11).** Distance-increasing constructor admission was accepted as a v0.2
disposition. On 2026-11-11 four of the nine constructors gained expression
productions (§1, §2): `L-HGP`, `L-LIFTED`, `L-GROUP-ALGEBRA`, and `A-CONCAT`,
whose typed inputs are finite constructive data and whose output
well-formedness is derived at `OPERATIONAL_SEMANTICS.md` §4.34; they are
`transition-defined` and carry no distance rule (`JUDGMENT_LAYER.md` §2g).
They are expressions, not commands, because they build a state from data
rather than transform a presented state.

**Admission of the other five (2026-11-11).** `L-BALANCED`,
`L-TANNER`, `L-TILE`, `A-PRODUCT`, and `A-DOUBLE` gained expression
productions (§1, §2) once their typed inputs were defined as finite
objects: permutation actions of a finite abelian group with an
equivariance condition; local check matrices with vertex embeddings; tiles,
placements, site identifications, and removed checks; two presented CSS
states under the CSS tensor product; and a wiring map on the displayed
incidences with an optional sector-duality flag. They are
`transition-defined`, their output well-formedness is derived at
`OPERATIONAL_SEMANTICS.md` §4.35, and they carry no distance rule
(`JUDGMENT_LAYER.md` §2g). Three of them (`A-DOUBLE`, `L-TANNER`, `L-TILE`)
have an applicability premise that the natural rows of the two sectors
commute; a failed premise is a no-derivation, not a malformed input. The
realizations narrow the signatures of
`CONSTRUCTOR_SIGNATURES.md`: `A-PRODUCT` admits the CSS
tensor product only, `L-BALANCED` finite abelian groups only, `L-TANNER`
one local code per vertex class, and `A-DOUBLE` the two-sheet cover of the
displayed incidences only.

**Admission of `L-NESTED-CSS` (2026-11-13).** `L-NESTED-CSS`
gained the expression production `nested(H_X, H_Z)` (§1, §2). Its typed
input is two binary parity-check matrices with equally many columns, and
its applicability premise is that every row of the one has even overlap
with every row of the other, which is the nesting of the two classical
codes; a failed premise is a no-derivation. It is `transition-defined`,
its output well-formedness is derived at `OPERATIONAL_SEMANTICS.md` §4.36,
and it carries no distance rule (`JUDGMENT_LAYER.md` §2g). The realization
narrows the signature of `CONSTRUCTOR_SIGNATURES.md` to
codes given by parity-check matrices. The production constructs no state
that `tanner` does not already construct (§4.36).

**Admission of `L-EMPTY`, `L-FREE`, `A-PULLBACK`, and `A-PUSHOUT` (2026-11-19).**
The two base constructors (`empty` and `free(Q)`) and the two interface
constructors (`pullback(e₁, e₂, e_I; φ₁, φ₂)` and `pushout(e₁, e₂, e_S; ψ₁, ψ₂)`)
gained expression productions (§1, §2). A CSS code morphism is a qubit map
whose $\mathbb{F}_2$-pushforward sends every displayed row into the target
code's same-sector row space; for `pullback` and `pushout`, morphism
preservation and pairwise even overlap of the constructed natural rows are
decidable applicability premises whose failure is a no-derivation. All four
are `transition-defined`, their output well-formedness is derived at
`OPERATIONAL_SEMANTICS.md` §4.43, and they carry no automatic distance rule in
`JUDGMENT_LAYER.md` §2g. The Kan-extension candidate remains refused.

**Generalization of `L-LIFTED`, `L-GROUP-ALGEBRA`, and `L-BALANCED` to finite nonabelian groups (2026-11-22).**
On 2026-11-22 the group input $G$ of `lift_G(A, B)`, `twoblock_G(a, b)`, and
`balanced_G(H_1, \alpha_1; H_2, \alpha_2)` was generalized from finite abelian
groups by cyclic orders to arbitrary finite groups (abelian by cyclic orders, or
nonabelian via an explicit multiplication table or permutation-generator
presentation), with explicit left and right regular representations $L(x), R(y)$,
antipode involution $g \mapsto g^{-1}$, and right/left permutation actions
$\alpha_1, \alpha_2$ (`OPERATIONAL_SEMANTICS.md` §2 cards, §4.44;
`OBL-NONABELIAN-GROUP-INPUTS`). Abelian cyclic-order inputs are preserved
conservatively ($R(y) = L(y)$ when $G$ is abelian). Conditional distance
lower-bound cells and consumer-side factor-to-child witness lifting for
`L-HGP`, `L-NESTED-CSS`, `A-CONCAT`, `A-PRODUCT`, and `A-DOUBLE` are recorded in
`OPERATIONAL_SEMANTICS.md` §4.45 and `JUDGMENT_LAYER.md` §2g.1
(`OBL-CONDITIONAL-CONSTRUCTOR-CELLS`).

**Admission of `L-PAIR-PARTITION` and promotion of `PP-SCALE` (2026-11-22).**
The pair-partition relative-permutation constructor `pair_partition(p; B_X, B_Z)`
and the explicit size-scaling specialization `pp_scale(e; P)` gained expression
productions (§1, §2). Both are `transition-defined` (`OPERATIONAL_SEMANTICS.md`
§2 cards, §4.46–§4.47; `OBL-PP-SCALE`): `L-PAIR-PARTITION` assembles $X$ and $Z$
parity checks from paired circulant/affine permutation blocks over lift size
$p \ge 1$ under the relative-affine pair-partition premise, while `PP-SCALE`
evaluates the Smith-normal-form slope/shift parametrization of a PP-presented
code $C_0$ at target size $P \ge 2$ on a fresh namespace with identifiers
canonically minted disjoint from $\mathsf{used}_0$ and applicability premise
$k' > 0$. Neither computes a distance (`JUDGMENT_LAYER.md` §2g, §2l).


## 8. Contexts

Gate 1 asks for a grammar of states, contexts, elementary moves, and sequential
terms. States, moves, and sequential terms are given above (§1–§4). **Contexts
are not a separate syntactic category in the MVP**, and that is deliberate: a
state in this calculus is always a *presented* CSS state, and its presentation
(the `pres` field: displayed generators, identifiers, sector labels, qubit
namespace) together with support and interface data *is* the context. No MVP
move constructs or manipulates a context independently of a state, so there is
no standalone context term; presentation equivalence (`P-RELABEL`) is a
congruence over the whole state, not a constructor. Support and interface data
are future-$\Pi$ data and are not MVP state data
([`STATE_MODEL.md`](STATE_MODEL.md) §1). Evaluation contexts (holes) are
likewise absent: the partial big-step relation evaluates closed terms
$m\triangleright e$ directly, so no reduction-context syntax is required. The
context grammar is therefore the presentation carried by $S$, and it travels
with the state under `P-RELABEL`.

## 9. Gate 1 artifact

This document is the Gate 1 artifact: it gives the grammar of states (§1, $e$),
elementary moves (§1, $m$; §2), sequential terms (§1, $m_1;m_2$ and
$m\triangleright e$), and contexts (§8). Gate 1 is ratified; Gates 2–7 remain
unchecked and are out of this artifact's scope.
