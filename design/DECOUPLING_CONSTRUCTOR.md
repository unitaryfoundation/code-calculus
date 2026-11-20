# Decoupling of translation-invariant CSS codes: a candidate formulation

**Status:** non-normative design note. It proposes how the
decoupling of [`ROADMAP.md`](ROADMAP.md), *Decoupling of translation-invariant
CSS codes*, could be stated against this state model, and derives the cells
that formulation would carry. Nothing here is admitted: `spec/` is unchanged,
no taxonomy identifier is minted, and no constructor or cell is added.
Promotion needs a dated maintainer decision (ROADMAP §3). The derivations are
hand derivations in this note. They are not machine-checked and not reviewed.
The machine-side certificate check lives in
`machine/experiments/translation_invariant_decoupling.py`, with tests in
`machine/test_translation_invariant_decoupling.py`.

**Source.** He, Wang, Song, and Gu, *Toric codes all the way down: decoupling
translation-invariant topological CSS codes in higher dimensions*, arXiv
2610.40592. ROADMAP recorded v2. The version read for this note, on
2026-11-13, is v3 (10 November 2026), from its HTML rendering and in part
only: the representation of a code by polynomial matrices, the action of a
circuit on them, the ancilla and coarse-graining lemmas, and the definition
of the higher-form toric codes were read in full. The statement of the main
theorem, the definitions of the SUM and SWAP gates, and the worked example
were read in the abstract or in summary only. This note uses nothing from
the second group: it cites the decoupling criterion as the source's claim
and derives none of it.

## 1. The recommendation

The roadmap entry and sketch a constructor

```text
(C : TranslationInvariantCSSCode; L : Superlattice) -> StackOfHigherFormToricCodes
```

with the source's criterion (translations act trivially on every layer and
the gluing vanishes) as its admission hypothesis. This note recommends a
different shape: a **certificate-checked relation** between two presented
states. The input is the code, the target stack, and a circuit. The
transition checks, by finite linear algebra on the torus, that the circuit
maps the one display onto the other.

The reasons are the calculus's own.

1. A constructor of the sketched type would have to run the source's
 algorithm, and its correctness would rest on a theorem whose proof is not
 in this repository. A checked certificate rests on nothing: if the check
 passes, the two states are related as stated, whoever produced the
 circuit.
2. The criterion is a statement about modules over a Laurent polynomial
 ring. It is not decidable from a presented state, and trusting it as a
 hypothesis would make it a priced input with no price to check. With a
 certificate the criterion is not an input. It becomes the source's
 account of when a certificate exists.
3. The roadmap entry already calls the circuit the evidence for the move
 and not a calculus rule. The certificate form takes that literally.

The typed data of §2 is needed in either shape, and §2 and §3 can be read as
the definition of the input type alone.

## 2. The typed input

Fix a dimension $D\ge 1$ and periods $L_1,\dots,L_D\ge 1$. Let $G$ be the
product of the cyclic groups of orders $L_1,\dots,L_D$, and let $R$ be its
group algebra over $\mathbb{F}_2$. An element of $R$ is a finite set of
exponent tuples, which is the encoding the `L-LIFTED` input already uses for
group-algebra elements. For $f\in R$, write $\bar f$ for its *antipode*, the
element whose exponents are the negatives of those of $f$. For a matrix $H$
over $R$, write $H^{\dagger}$ for the transpose with the antipode applied to
each entry.

A **translation-invariant CSS input** is a tuple $(L, q, H_X, H_Z)$: the
periods $L$, a number $q\ge 1$ of *sites* per cell, and matrices $H_X$ and
$H_Z$ over $R$ with $q$ columns each, subject to the premise

$$
 H_X H_Z^{\dagger}=0 .
$$

This is the source's representation restricted to a finite torus and to
qubits. The state model is the qubit one, so odd primes are out of scope.

**The presented state.** The qubits are the pairs $(g,a)$ of a cell $g\in G$
and a site $a<q$, in a fixed order. For each row $i$ of $H_X$ and each cell
$g$ there is one $X$-row with support

$$
 \{(g-\alpha,a) : \alpha\in (H_X)_{ia}\},
$$

and the $Z$-rows are formed from $H_Z$ in the same way. The premise is
exactly the pairwise even overlap of the rows of the two sectors, which I1
requires. Independence of the rows is not implied. The admitted typed
constructors meet the same situation by retaining an independent spanning
subset of their natural rows.

This is the translation-invariance data the roadmap entry says the state
model lacks. It does not have to enter the state: it is constructor input,
of the same kind as the inputs of `L-LIFTED` and `L-GROUP-ALGEBRA`, and the
state it produces is an ordinary presented state.

**Targets.** For $1\le j\le D-1$ the $j$-form toric code is the input with
one site per $j$-subset of the directions, $H_X=\partial_j$, and
$H_Z^{\dagger}=\partial_{j+1}$, where $\partial_k$ is the Koszul differential
on the elements $x_i+1$ (the source's definition, with signs dropped over
$\mathbb{F}_2$). A *stack* is a direct sum of such inputs on one torus.
An *ancilla* is an extra site stabilized by a single-qubit $X$ or a
single-qubit $Z$ in every cell.

**Coarse-graining.** For factors $m_i$ dividing $L_i$, the input can be read
on the superlattice with $m_i$ cells per new cell in direction $i$: the
periods become $L_i/m_i$, each site becomes $\prod_i m_i$ sites, and each
entry of a matrix becomes the matrix of multiplication by it. The presented
state is the same up to a relabelling of qubits. Coarse-graining is therefore
not a transition. It changes which circuits count as translation-invariant.

## 3. Circuits and the check

A **gate** is $\mathrm{SUM}(c,t,f)$ for sites $c\ne t$ and $f\in R$, or
$\mathrm{SWAP}(a,b)$. The gate $\mathrm{SUM}(c,t,f)$ stands for the matrix
$U=I+f\,e_te_c^{T}$ over $R$, which is its own inverse, and acts on the
matrices by

$$
 H_Z\mapsto H_ZU^{\dagger},\qquad H_X\mapsto H_XU^{-1},
$$

which is the matrix form of the action the source states for a
translation-invariant circuit that preserves the CSS form: $Z(v)$ goes to
$Z(Uv)$ and $X(u)$ to $X((U^{\dagger})^{-1}u)$. On the torus it is the set of controlled-NOT gates
with control $(g+\alpha,t)$ and target $(g,c)$ over all cells $g$ and all
$\alpha\in f$. These commute with each other, since no qubit is both a
control and a target. A **circuit** is a list of gates.

**The certificate check.** Given an input $C$, numbers of ancilla sites, a
circuit, and a target input $T$ on the same torus with the same number of
sites as $C$ with its ancillas, the check accepts when

1. the premise of §2 holds for $C$, and
2. applying the circuit's controlled-NOT and swap gates to the display of
 $C$ with its ancillas gives, in each sector, rows with the same span as
 the rows of $T$.

Both conditions are finite. The check does not use the polynomial action
above: it applies the gates to the display.

## 4. Candidate cells

Let the check accept, with $C^{+}$ the input $C$ with its ancillas and $T$
the target. A circuit of controlled-NOT and swap gates is an invertible
linear map $A$ on $X$-supports and the map $A^{-T}$ on $Z$-supports. Write
$\rho_X$ for the largest weight of the image of a single-qubit $X$ under the
circuit, $\rho_Z$ for the same with $Z$, and $\rho_X^{-}$ and $\rho_Z^{-}$
for the same quantities for the reversed circuit.

| Property | Candidate cell | Evidence in this note |
| --- | --- | --- |
| $n$ | $n(T)=n(C)+a\,|G|$ for $a$ ancilla sites, exact | §4.1 |
| $k$ | $k(T)=k(C)$, exact | §4.1 |
| $d_X$ | $\lceil d_X(C)/\rho_X^{-}\rceil\le d_X(T)\le\rho_X\,d_X(C)$ | §4.2 |
| $d_Z$ | $\lceil d_Z(C)/\rho_Z^{-}\rceil\le d_Z(T)\le\rho_Z\,d_Z(C)$ | §4.2 |
| $w$, Tanner components, $r$ | no cell: recomputed on the target display | none needed |

The distance cells are a window and not an equality. §5 pins a certificate
that takes a code of $X$ distance $1$ to a target of $X$ distance $2$. This
agrees with the roadmap's standing condition that a layer of controlled-NOT
gates is not modelled as zero-price. The source makes no distance statement
in the text read, and these cells do not come from it.

### 4.1 Dimension counts

An ancilla adds one qubit and one independent row per cell, so it changes
$n$ by $|G|$ per ancilla site and leaves $k$ unchanged. The circuit is a
bijection on qubits' operators that maps the span of each sector's rows of
$C^{+}$ onto the span of the corresponding rows of $T$, by condition 2, so
the two sector ranks are equal and $k(T)=k(C^{+})=k(C)$. $\square$

### 4.2 Distances

*Ancillas.* Let the ancilla qubit carry the row $X$. A $Z$-sector logical
has even overlap with that row, so it avoids the ancilla. An $X$-sector
logical can be multiplied by the row to avoid it without gaining weight. In
both sectors the logicals of least weight are those of $C$, and their
classes are unchanged, so $d_X(C^{+})=d_X(C)$ and $d_Z(C^{+})=d_Z(C)$. The
case of the row $Z$ is the same with the sectors exchanged.

*The circuit.* The map $A$ takes the span of the $X$-rows of $C^{+}$ onto
that of $T$, and since $A^{-T}$ does the same for the $Z$-rows, it takes the
vectors with even overlap with every $Z$-row of $C^{+}$ onto those of $T$.
So $A$ is a bijection from the $X$-sector logicals of $C^{+}$ to those of
$T$. The image of a vector of weight $v$ is a sum of $v$ images of single
qubits, so it has weight at most $\rho_Xv$. Applying this to a logical of
least weight gives $d_X(T)\le\rho_X\,d_X(C^{+})$, and applying it to the
reversed circuit gives $d_X(C^{+})\le\rho_X^{-}\,d_X(T)$. The $Z$ sector is
the same with $A^{-T}$. $\square$

## 5. Evidence

`machine/experiments/translation_invariant_decoupling.py` implements §2 and
§3 for qubits and `machine/test_translation_invariant_decoupling.py` pins
the following.

- The two-dimensional toric code from the Koszul differential has $k=2$ and
 $d_X=d_Z=\min(L_1,L_2)$ on the tori $2\times2$, $3\times2$, and
 $3\times3$. The $j$-form code in dimension $D$ has $\binom{D}{j}$ logical
 qubits on the four tori tried with $D=3$ and $D=4$.
- Coarse-graining gives the same display up to the stated relabelling on
 three instances.
- The polynomial action of a circuit and its gate-by-gate action on the
 display agree, on a torus where the antipode is not the identity.
- On a sweep of 30 codes built by applying a random circuit to a toric code
 with one ancilla per cell, the check accepts the reversed circuit, refuses
 it with one gate appended, and the exhaustive distances fall inside the
 windows of §4. The instance of §4 with a changed distance is pinned
 separately.
- `Code` validates the typed input signature $(L, q, H_X, H_Z)$, and
 `check_decoupling` explicitly refuses non-`Code` inputs lacking
 translation-invariance data, non-commuting inputs or targets, shape
 mismatches, and malformed circuits while recording the input and target
 signatures on accepted records.

The sweep certifies only codes whose decoupling is known by construction.
It exercises the check and the cells. It is not a test of the source's
theorem or algorithm, neither of which is implemented. Agreement is
evidence that the derivations are transcribed as stated, not a proof
(AGENTS.md). The authors' code repositories were not examined.

## 6. What a decision would have to settle

1. **Constructor or relation.** §1 recommends the certificate-checked
 relation. If the maintainer prefers the constructor of the roadmap entry,
 §2 still defines its input type, and the criterion would be a trusted
 hypothesis with a source.
2. **Where the input type lives.** The input of §2 could be admitted on its
 own as an `L-` constructor of presented states (a translation-invariant
 code from its polynomial matrices), independently of decoupling. That is
 the smaller admission and the decoupling relation needs it first.
3. **The relation is not specific to decoupling.** The check of §3 relates
 any two inputs by a circuit, and the target being a stack is one use.
 This overlaps the presentation-transform judgments of , and the
 two should be decided together.
4. **Dependent rows.** The display of §2 can have dependent rows, as on any
 torus for the toric code. The admitted constructors retain an independent
 spanning subset, and the same step would be needed here.
5. **Scope.** Qubits only. The infinite-lattice statements of the source,
 including its topological condition and its criterion, are outside what a
 presented state can express.

## 7. Completion note (2026-11-14)

The candidate formulation of is complete at the documentation
level: a typed input (§2), a certificate check (§3), candidate cells (§4),
and evidence (§5, 14 tests passing in
`machine/test_translation_invariant_decoupling.py`). The admission decision
of 2026-11-14 admitted the decoupling entry into the
`stdCSS-3` / `v0.2.0` candidate scope; conditions, hypotheses, and proof
obligations are preserved. The source's theorem and algorithm are not
implemented; the check is a certificate check that rests on finite linear
algebra only (§3). Promotion to an admitted constructor (taxonomy ID,
grammar production, spec card, machine and Lean counterparts) is separate
follow-up work, and the five questions of §6 remain open for the decision.

No claim is made that a code decouples: the decoupling criterion stays the
source's account of when a certificate exists (§1, §3).
