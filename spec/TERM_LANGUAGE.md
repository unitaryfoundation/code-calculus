# Term Language

**Status:** normative. The syntax of what can be written, and what cannot.

---

## 1. Two syntactic categories

State expressions and commands are separate. They are never composed as if both
were functions.

$$
e \;::=\; S \;\mid\; e_1 \oplus e_2
$$

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
consumes the §2e seam certificate. The §2f conditional cell and the
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

## 4. Malformed — rejected by the grammar alone

| Term | Why |
| --- | --- |
| $S\triangleright S$ | a state in command position; $\triangleright$'s left side is a command |
| $\mathrm{delete}_a\triangleright \mathrm{skip}$ | a command in expression position; $e$ never contains commands |
| $(\mathrm{delete}_a\triangleright S);m$ | a closed term is not a command; `;` composes commands only |
| $(m\triangleright S)\oplus(m'\triangleright T)$ | $\oplus$ combines state expressions, not terms |
| $m_1;m_2\triangleright (e_1;e_2)$ | `;` is undefined on state expressions |

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
