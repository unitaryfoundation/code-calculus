# Term Language

**Status:** normative. The syntax of what can be written, and what cannot.

---

## 1. Two syntactic categories

State expressions and commands are separate. They are never composed as if both
were functions.

$$
e \;::=\; S \;\mid\; e_1 \oplus e_2
$$

and, since 2026-11-11 (issue #330), the four admitted typed constructors
extend the expressions by

$$
e ::= \mathrm{hgp}(H_1, H_2) \mid \mathrm{lift}_G(A, B) \mid \mathrm{twoblock}_G(a, b) \mid \mathrm{concat}(e_O, e_I; \vec B)
$$

where $H_1$ and $H_2$ are binary matrices, $G$ is a finite abelian group given
by its cyclic orders, $A$ and $B$ are matrices and $a$ and $b$ elements of the
group algebra $\mathbb{F}_2[G]$, and $\vec B$ is a block partition of the outer
state's qubits (`OPERATIONAL_SEMANTICS.md` §2 cards).

Since 2026-11-11 (issue #369) the other five accepted constructors extend
the expressions by

$$
e ::= \mathrm{product}(e_A, e_B) \mid \mathrm{double}_{w,s}(e) \mid \mathrm{balanced}_G(H_1, \alpha_1; H_2, \alpha_2) \mid \mathrm{tanner}(n; \Lambda_X, \Lambda_Z; \iota_X, \iota_Z) \mid \mathrm{tile}(\tau; \alpha; \beta)
$$

The typed inputs are finite objects, defined on the cards of
`OPERATIONAL_SEMANTICS.md` §2. In `product`, $e_A$ and $e_B$ are state
expressions. In `double`, $w$ is a wiring map from the displayed row
identifiers of the value of $e$ to subsets of their supports and $s$ is an
optional sector-duality flag. In `balanced`, $G$ is a finite abelian group
given by its cyclic orders, $H_1$ and $H_2$ are binary matrices, and
$\alpha_1$ and $\alpha_2$ are actions of $G$ on their row and column indices
by permutations. In `tanner`, $n$ is a qubit count, $\Lambda_X$ and
$\Lambda_Z$ are binary matrices of local checks, and $\iota_X$ and $\iota_Z$
are lists of vertex embeddings. In `tile`, $\tau$ is a list of tiles,
$\alpha$ a list of placements on sites, and $\beta$ the boundary rules (site
identifications and removed checks).

Since 2026-11-13 (issue #445) the expressions also include

$$
e ::= \mathrm{nested}(H_X, H_Z)
$$

where $H_X$ and $H_Z$ are binary matrices with the same number of columns,
the parity-check matrices of two classical codes of one length
(`OPERATIONAL_SEMANTICS.md` §2 card).

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
| `C-DELETE-CHECK` | command | $m ::= \mathrm{delete}_r$ | `delete_r` |
| `C-ADD-CHECK` | command | $m ::= \mathrm{addStab}_r$ | `addStab_r` |
| `E-GRAFT` | command | $m ::= \mathrm{graft}_{q,\tau;\vec r}$ | `graft(q, τ; [r₁,…,rₘ])` |
| `E-PEEL` | command | $m ::= \mathrm{peel}_{q,\tau;r}$ | `peel(q, τ; r)` |
| `E-PUNCTURE` | command | $m ::= \mathrm{puncture}_q$ | `puncture(q)` |
| `E-EXTEND` | command | $m ::= \mathrm{extend}_{\Delta;\vec u}$ | `extend(Δ; [(τ₁,u₁),…])` |
| `E-LOCAL-HADAMARD` | command | $m ::= \mathrm{hadamard}_T$ | `hadamard(T)` — admitted for $T=Q$ or $T=\varnothing$ |
| `P-REBASE` | command | $m ::= \mathrm{rebase}_{\tau;M}$ | `rebase(τ; M)`, $M\in\mathrm{GL}(m,2)$ |
| `L-HGP` | expression-constructor | $e ::= \mathrm{hgp}(H_1,H_2)$ | `hgp(H₁, H₂)`, two binary matrices (admitted 2026-11-11, issue #330) |
| `L-LIFTED` | expression-constructor | $e ::= \mathrm{lift}_G(A,B)$ | `lift_G(A, B)`, $G$ a finite abelian group by cyclic orders, $A$ and $B$ matrices over $\mathbb{F}_2[G]$ (admitted 2026-11-11) |
| `L-GROUP-ALGEBRA` | expression-constructor | $e ::= \mathrm{twoblock}_G(a,b)$ | `twoblock_G(a, b)`, $a, b \in \mathbb{F}_2[G]$ (admitted 2026-11-11) |
| `A-CONCAT` | expression-constructor | $e ::= \mathrm{concat}(e_O, e_I; \vec B)$ | `concat(e_O, e_I; blocks)`, CSS outer and inner factors with a block partition (admitted 2026-11-11) |
| `A-PRODUCT` | expression-constructor | $e ::= \mathrm{product}(e_A, e_B)$ | `product(e_A, e_B)`, the CSS tensor product of two well-formed CSS states (admitted 2026-11-11, issue #369) |
| `A-DOUBLE` | expression-constructor | $e ::= \mathrm{double}_{w,s}(e)$ | `double(e; wiring[, conjugate])`, the two-sheet cover under a wiring map; no derivation unless the lifted rows commute (admitted 2026-11-11, issue #369) |
| `L-BALANCED` | expression-constructor | $e ::= \mathrm{balanced}_G(H_1,\alpha_1;H_2,\alpha_2)$ | `balanced_G(H₁, α₁; H₂, α₂)`, binary matrices equivariant under permutation actions of a finite abelian group (admitted 2026-11-11, issue #369) |
| `L-TANNER` | expression-constructor | $e ::= \mathrm{tanner}(n;\Lambda_X,\Lambda_Z;\iota_X,\iota_Z)$ | `tanner(n; Λ_X, Λ_Z; ι_X, ι_Z)`, local checks on the two vertex classes of an incidence structure; no derivation unless the local checks of the two classes commute (admitted 2026-11-11, issue #369) |
| `L-TILE` | expression-constructor | $e ::= \mathrm{tile}(\tau;\alpha;\beta)$ | `tile(tiles; placements; boundary rules)`; no derivation unless the placed rows of the two sectors commute (admitted 2026-11-11, issue #369) |
| `L-NESTED-CSS` | expression-constructor | $e ::= \mathrm{nested}(H_X,H_Z)$ | `nested(H_X, H_Z)`, two binary parity-check matrices with equally many columns; no derivation unless every row of the one has even overlap with every row of the other (admitted 2026-11-13, issue #445) |
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

`E-GLUE` has **no unary grammar production**: gluing is a binary state
operation rather than a command over a single presented state, but an evaluator
transition is now admitted (§4.31) that combines two disjoint factor states and
consumes the §2e seam certificate. The Lean mechanization renders this binary
transition as a state-expression constructor `glue(e₁, e₂; seams)` beside
`⊕`, so `EvalExpr` evaluates both factors to presented states first; on
closed terms this is the same transition as `Eval(glue(C_A, C_B; seam checks), C)`
(`semantics.json`). The §2f conditional cell and the
logical-witness prerequisite (`TAXONOMY.md` §2.10, still `not-yet-defined`)
remain as stated. `P-RELABEL` has **no** grammar production; it is a congruence
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
states on unordered presentations, with disjointness premises — a claim recorded
**`open`** at `OBL-DIRECT-SUM-LAWS`, not assumed.

## 7. What this document does not do

It gives the syntax only. Whether a well-typed term has an evaluation
derivation, and what state it yields, is
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md). What the calculus can
*claim* about the resulting state is
[`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md).

**Disposition (2026-11-10, issue #315 C1) and admission (2026-11-11, issue
#330).** Distance-increasing constructor admission was accepted as a v0.2
disposition. On 2026-11-11 four of the nine constructors gained expression
productions (§1, §2): `L-HGP`, `L-LIFTED`, `L-GROUP-ALGEBRA`, and `A-CONCAT`,
whose typed inputs are finite constructive data and whose output
well-formedness is derived at `OPERATIONAL_SEMANTICS.md` §4.34; they are
`transition-defined` and carry no distance rule (`JUDGMENT_LAYER.md` §2g).
They are expressions, not commands, because they build a state from data
rather than transform a presented state.

**Admission of the other five (2026-11-11, issue #369).** `L-BALANCED`,
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
`archive/notes/CONSTRUCTOR_SIGNATURES.md`: `A-PRODUCT` admits the CSS
tensor product only, `L-BALANCED` finite abelian groups only, `L-TANNER`
one local code per vertex class, and `A-DOUBLE` the two-sheet cover of the
displayed incidences only.

**Admission of `L-NESTED-CSS` (2026-11-13, issue #445).** `L-NESTED-CSS`
gained the expression production `nested(H_X, H_Z)` (§1, §2). Its typed
input is two binary parity-check matrices with equally many columns, and
its applicability premise is that every row of the one has even overlap
with every row of the other, which is the nesting of the two classical
codes; a failed premise is a no-derivation. It is `transition-defined`,
its output well-formedness is derived at `OPERATIONAL_SEMANTICS.md` §4.36,
and it carries no distance rule (`JUDGMENT_LAYER.md` §2g). The realization
narrows the signature of `archive/notes/CONSTRUCTOR_SIGNATURES.md` to
codes given by parity-check matrices. The production constructs no state
that `tanner` does not already construct (§4.36).

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
