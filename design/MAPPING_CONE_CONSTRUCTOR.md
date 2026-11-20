# Mapping-cone constructor: a candidate formulation and an audit

**Status:** non-normative design note. This note formulates the mapping cone of a
chain map as a typed constructor candidate, derives the judgment cells it would
carry, and audits two prerequisites before any admission to [`spec/`](../spec/):
the candidate distance formula and the identification of the cone with a strict
pushout. Nothing here is admitted: `spec/` is unchanged, no taxonomy identifier
is minted, and no constructor or cell is added. Promotion requires a formal
admission decision ([`ROADMAP.md`](ROADMAP.md) §2). The derivations below are
hand derivations and are not machine-checked.

Because the companion source paper (*code-deformation*) was not available when
this note was written, the audit below checks the recorded formula directly
from first principles and derives every statement it uses rather than relying on
external proofs.

## 1. The typed input and the constructed state

All vector spaces are over $\mathbb{F}_2$ with fixed bases, and the *weight*
$\lVert v\rVert$ of a vector is the number of its nonzero coordinates.

A **cone input** is four matrices: $\partial_A\colon A_1\to A_0$,
$\partial_B\colon B_1\to B_0$, $f_1\colon A_1\to B_1$, and
$f_0\colon A_0\to B_0$, subject to the premise

$$
 \partial_B f_1 = f_0\,\partial_A .
$$

So $A$ and $B$ are two-term complexes, which is the data of two classical
parity-check matrices, and $f=(f_1,f_0)$ is a chain map between them. This
is the roadmap's condition that the rule take the chain map as an explicit
input. It is a finite object of the same kind as the inputs of `L-HGP`.

The **cone** $C(f)$ is the three-term complex with $C_2=A_1$,
$C_1=A_0\oplus B_1$, and $C_0=B_0$, and differentials

$$
 \delta_2(a_1)=(\partial_Aa_1,\ f_1a_1),\qquad
 \delta_1(a_0,b_1)=f_0a_0+\partial_Bb_1 .
$$

The premise gives $\delta_1\delta_2=0$. The constructed state has one qubit
per basis element of $C_1$, so $n=\dim A_0+\dim B_1$, one natural $Z$-row
$\delta_2(e)$ per basis element $e$ of $A_1$, and one natural $X$-row per
basis element of $B_0$, the corresponding row of the matrix of $\delta_1$.
The rows of the two sectors have pairwise even overlap exactly because
$\delta_1\delta_2=0$. As for the admitted typed constructors, the natural
rows can be dependent and a display would retain an independent spanning
subset.

With the sector convention of `machine/oracle.py`, $d_Z$ is the least weight
of a *cycle* (a vector of $\ker\delta_1$) that is not a *boundary* (a vector
of the image of $\delta_2$), and $d_X$ is the same for the transposed
complex.

## 2. The classes of the cone

Write $Z(A)=\ker\partial_A$ and $Z(B)=\ker\partial_B$, and let
$\bar f_0\colon A_0/\operatorname{im}\partial_A\to
B_0/\operatorname{im}\partial_B$ be the map $f_0$ induces, which is
well-defined by the premise.

**Lemma 1.** Let $\pi$ send the class of a cycle $(a_0,b_1)$ to the class of
$a_0$ in $A_0/\operatorname{im}\partial_A$, and let $\iota$ send
$b\in Z(B)$ to the class of the cycle $(0,b)$. Then

1. $\pi$ is well-defined on classes, and its image is $\ker\bar f_0$;
2. the kernel of $\pi$ is the image of $\iota$;
3. $\iota(b)=0$ iff $b\in f_1(Z(A))$, and the representatives of $\iota(b)$
 are exactly the vectors $(\partial_Aa_1,\ b+f_1a_1)$ for $a_1\in A_1$.

*Derivation.*

1. A boundary $(\partial_Aa_1,f_1a_1)$ has first component in
 $\operatorname{im}\partial_A$, so $\pi$ is well-defined. If $(a_0,b_1)$
 is a cycle then $f_0a_0=\partial_Bb_1$, so the class of $a_0$ is in
 $\ker\bar f_0$. Conversely, if $f_0a_0=\partial_Bb_1$ for some $b_1$ then
 $(a_0,b_1)$ is a cycle.
2. If $a_0=\partial_Aa_1$, adding the boundary $\delta_2(a_1)$ to
 $(a_0,b_1)$ gives a cycle $(0,b)$, and $\delta_1(0,b)=\partial_Bb=0$.
 Conversely $\pi(\iota(b))=0$.
3. The representatives of a class are the sums of one representative with
 the boundaries, which gives the stated form. The class is zero iff
 $(0,b)=(\partial_Aa_1,f_1a_1)$ for some $a_1$, that is iff $b=f_1a_1$
 with $a_1\in Z(A)$. $\square$

Lemma 1 is the part of the long exact sequence of the cone that the cells
use, derived here so that exactness is not imported.

## 3. Candidate cells

| Property | Candidate cell | Evidence in this note |
| --- | --- | --- |
| $n$ | $\dim A_0+\dim B_1$, exact | §1 |
| $k$ | $\dim Z(B)-\dim f_1(Z(A))+\dim\ker\bar f_0$, exact | Lemma 1 |
| $d_Z$ | $\min(D_B,D_A)$, the two terms defined below; no value is computed by the rule | §3.1 |
| $d_Z$, upper endpoint | a cycle of $B$ outside $f_1(Z(A))$ is a validated witness | §3.2 |
| $d_Z$, lower endpoint | $\min(\ell_B,\ell_A)$ for supplied, sourced bounds $\ell_B\le D_B$ and $\ell_A\le D_A$, and $\ell_B$ alone when $\bar f_0$ is injective | §3.1 |
| $d_X$ | the cells of $d_Z$ for the transposed input | §3.3 |
| $w$, Tanner components, $r$ | no cell: recomputed on the constructed display | none needed |

*The count $k$.* By Lemma 1 the space of classes has dimension
$\dim\operatorname{im}\iota+\dim\ker\bar f_0$, and
$\operatorname{im}\iota\cong Z(B)/f_1(Z(A))$.

### 3.1 The split of the distance

By Lemma 1 a nonzero class is of exactly one of two kinds. Either its image
under $\pi$ is nonzero, and then every representative $(a_0,b_1)$ has
$a_0\notin\operatorname{im}\partial_A$. Or it is $\iota(b)$ for some
$b\in Z(B)\setminus f_1(Z(A))$. Define

$$
 D_A=\min\{\lVert a_0\rVert+\lVert b_1\rVert :
 f_0a_0=\partial_Bb_1,\ a_0\notin\operatorname{im}\partial_A\},
$$

$$
 D_B=\min\{\lVert\partial_Aa_1\rVert+\lVert f_1a_1+b\rVert :
 a_1\in A_1,\ b\in Z(B)\setminus f_1(Z(A))\},
$$

each read as $+\infty$ when its set is empty. Then
$d_Z(C(f))=\min(D_B,D_A)$.

Both terms are minima over exponentially many vectors, so the split is not a
way to compute a distance, and no rule would. Its use is as a conditional
price in the sense of [`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md)
§2a: a consumer that supplies sourced lower bounds on the two terms gets a
lower endpoint, and the constructor checks only the decidable side
condition. Whether $\bar f_0$ is injective is decidable by rank, and when it
is, $D_A=+\infty$ and one bound suffices.

### 3.2 Bounds from the factors

Taking $a_1=0$ in $D_B$ gives $D_B\le\min\{\lVert b\rVert :
b\in Z(B)\setminus f_1(Z(A))\}$, and each such $b$ gives the cycle $(0,b)$
of the cone, which is a witness that can be validated in the constructed
state. Dropping the term $\lVert b_1\rVert$ in $D_A$ gives
$D_A\ge\min\{\lVert a_0\rVert : a_0\notin\operatorname{im}\partial_A,\
f_0a_0\in\operatorname{im}\partial_B\}$. Both right-hand sides are distances
of smaller objects and would be supplied, not computed.

### 3.3 The other sector

The transposed input has $\partial_B^{T}$ in the place of $\partial_A$,
$\partial_A^{T}$ in the place of $\partial_B$, $f_0^{T}$ in the place of
$f_1$, and $f_1^{T}$ in the place of $f_0$. It satisfies the premise, since
transposing $\partial_Bf_1=f_0\partial_A$ gives
$f_1^{T}\partial_B^{T}=\partial_A^{T}f_0^{T}$. Its cone has the same qubits
with the two blocks exchanged, and its natural $Z$-rows are the natural
$X$-rows of $C(f)$. So $d_X(C(f))$ is $d_Z$ of the cone of the transposed
input, and §3.1 and §3.2 apply to it.

## 4. Audit of the candidate distance formula

The candidate distance formula recorded in the roadmap literature summary reads:

$$
 d(C(f))=\min_{[b_1]\notin\operatorname{im}f_*}
 \lVert d_Aa_1\rVert+\lVert f_1(a_1)+b_1\rVert .
$$

Read against §3.1, the right-hand side is $D_B$. Three findings follow.

1. **It is one term of one sector.** It equals $d_Z(C(f))$ iff
 $D_B\le D_A$. That holds when $\bar f_0$ is injective, and it fails in
 general: for $A$ the complex $0\to\mathbb{F}_2$, $B$ the complex
 $\mathbb{F}_2^2\to\mathbb{F}_2$ with both basis vectors sent to $1$, and
 $f_0=0$, the generator of $A_0$ is a cycle of weight $1$ on its own, and
 $D_B=2$. The line as recorded states no such hypothesis. If the paper
 states one, the record should carry it.
2. **It says nothing about $d_X$.** The left-hand side is written $d$. The
 other sector is the same statement for the transposed map (§3.3), with
 its own two terms.
3. **It is a characterization, not a price.** The minimum ranges over all
 $a_1$ and all admissible $b_1$. As a provider it yields only what §3.1
 and §3.2 state: a conditional lower endpoint from supplied bounds and
 upper witnesses from $B$.

The roadmap entry says a rule must take *compatible weights* as explicit
inputs. This note could not determine from the repository what the paper
means by that. The reading adopted in §3 is that the inputs are the bounds
$\ell_B$ and $\ell_A$ with their sources. If the paper means weighted norms
on the factors, the cells would have to be restated for them.

## 5. Audit of the strict-pushout identification

Let $\operatorname{Cone}(\mathrm{id}_A)$ be the cone of the identity of $A$,
with degree-one part $A_0\oplus A_1$, and let $A\to
\operatorname{Cone}(\mathrm{id}_A)$ be the inclusion of the second summand.
The strict pushout of $B\leftarrow A\to\operatorname{Cone}(\mathrm{id}_A)$
has degree-one part

$$
 P_1=(B_1\oplus A_0\oplus A_1)\,/\,\{(f_1a,\ 0,\ a) : a\in A_1\}.
$$

**As complexes the identification holds.** The map
$\varphi(b_1,a_0,a_1)=(a_0,\ b_1+f_1a_1)$ is onto $C_1$, its kernel is the
subspace of relations, and with the corresponding maps in degrees $2$ and
$0$ it commutes with the differentials: in degree $2$ the pushout sends
$a_1$ to the class of $(0,\partial_Aa_1,a_1)$, whose image under $\varphi$
is $\delta_2(a_1)$, and in degree $0$ the two composites agree by the
premise. So $n$, $k$, and the classes of §2 can be read from either
description.

**As normed complexes it does not.** The pushout has no preferred basis. If
it is given the quotient norm, the weight of a class being the least weight
of a representative in $B_1\oplus A_0\oplus A_1$, then the class of the cone
vector $(a_0,b_1)$ has norm
$\lVert a_0\rVert+\min_a(\lVert b_1+f_1a\rVert+\lVert a\rVert)$, which is at
most its weight in the cone and can be smaller. Take $A$ the complex
$\mathbb{F}_2\to\mathbb{F}_2^2$ with the generator sent to $11$, $B$ the
complex $\mathbb{F}_2^2\to\mathbb{F}_2$ with both basis vectors sent to $1$,
$f_1$ sending the generator to $11$, and $f_0$ sending both basis vectors
to $1$. The cone is the code with rows $XXXX$ and $ZZZZ$, with $d_Z=2$. The
cycle $(0,11)$ has weight $2$, and its class has quotient norm $1$ through
the representative with $b_1=0$ and $a_1$ the generator. Under the quotient
norm the least norm of a cycle that is not a boundary is $1$.

The distance of the constructed code is the Hamming weight in the basis of
$C_1=A_0\oplus B_1$, because those basis elements are the qubits. A rule
must therefore fix the cone presentation of §1. A statement that transports
a distance bound through the pushout description is not sound unless it
says which norm it uses, and the quotient norm is the wrong one.

## 6. Evidence

[`machine/experiments/mapping_cone.py`](../machine/experiments/mapping_cone.py)
builds the cone from the four matrices and checks by enumeration: the count $k$
against the rank count, the split of §3.1, the injective case, the two bounds
of §3.2, the duality of §3.3, the identification of §5 as complexes, and that
the quotient norm never exceeds the weight. At seed 449 over 600 random inputs
with every dimension at most $3$ there is no disagreement. Of the 403 inputs
with $k>0$, the recorded formula equals $d_Z$ on 256 and differs on 147, and
the quotient-norm distance is smaller than $d_Z$ on 3.
[`machine/test_mapping_cone.py`](../machine/test_mapping_cone.py) pins the two
instances of §4 and §5. Agreement is empirical evidence that the derivations are
transcribed as stated, not a proof.

## 7. Open questions and prototype status

### Open questions for admission

1. **Hypothesis on the distance formula.** Whether the source paper states the
   injectivity hypothesis under which $D_B$ equals $d_Z$, and which sector it
   addresses.
2. **Compatible weights (§4).** Clarifying whether the source's "compatible
   weights" are the sourced lower bounds $\ell_A, \ell_B$ used in §3 or weighted
   norms on the factors.
3. **Shape of the input.** This note takes two-term complexes, which give a CSS
   code directly. Cones of maps between longer complexes require a choice of
   which degree carries the qubits and are not covered.
4. **Relation to the admitted constructors.** For $f=0$ the cone is a code
   with its $Z$-rows on one block and its $X$-rows on the other. Whether the
   cone should be a new `L-` constructor or a parameter of an existing one
   remains open.
5. **Dependent rows.** As for the admitted constructors, the display would
   retain an independent spanning subset of the natural rows.

### Machine prototype

The mapping-cone candidate is implemented on the consumer side in
[`machine/experiments/mapping_cone.py`](../machine/experiments/mapping_cone.py)
(re-exported by [`machine/mapping_cone.py`](../machine/mapping_cone.py) and
[`machine/entrypoints.py`](../machine/entrypoints.py)):

- `chain_map_input` and `compatible_weights` record the chain-map matrices,
  dimensions, and sourced bounds $\ell_A, \ell_B$, combined by
  `mapping_cone_constructor`.
- `pushout_audit` records that the strict-pushout identification holds as
  complexes and fails for the quotient norm.
- `induced_metric` records that the code's distance is the Hamming weight in
  the cone basis $C_1 = A_0 \oplus B_1$, not the quotient norm.
- `no_exactness_beyond_source` records that the candidate formula is one term
  ($D_B$) of one sector's distance and that no exact-distance claim is made.

No `spec/` change, taxonomy identifier, grammar production, or spec card is
added; promotion to an admitted constructor remains candidate work.
