# Structured constructor signatures — Gate 7 candidates

**Status:** design note, 2026-10-28 . Non-normative: it records
shapes for later admission work and admits no constructor, changes no claim
status, and adds no grammar production. Owner of the ladder positions is
[`ROADMAP.md`](ROADMAP.md) §2; the contract-index rows are in
[`spec/CLAIMS.md`](../spec/CLAIMS.md).

**Scope.** The fifteen Gate 7 candidate constructors named in
[`ROADMAP.md`](ROADMAP.md) §2: `A-PRODUCT`, `A-CONCAT`, `A-DOUBLE`,
`A-QUOTIENT`, `L-HGP`, `L-LIFTED`, `L-NESTED-CSS`, `L-TILE`, `L-TANNER`,
`L-BALANCED`, `L-GROUP-ALGEBRA`, `X-SYMPLECTIC-DOUBLE`,
`X-SYMPLECTIC-HALVE`, `X-SUBSYSTEM`, `X-GAUGE-FIX`. `X-LOCAL-CLIFFORD`
is not constructor-shaped and is excluded (it is a conjugation, recorded at
[`spec/TAXONOMY.md`](../spec/TAXONOMY.md) §4.4). All fifteen remain at
rung 1 (`taxonomy-only`).

---

## 1. Reading convention

A signature is written in operadic form

\[
\mathsf{ID} : (x_1 : T_1,\;\dots,\;x_r : T_r) \;\to\; T_{\mathrm{out}},
\]

followed by three blocks:

- **Inputs** — for each \(x_i\), its type and whether it is *constructive* or
 *axiomatic*.
- **Incurred obligations** — the proof obligations the constructor would have to
 discharge if it were admitted (well-formedness, orthogonality, rank/dimension
 bookkeeping, distance hypotheses, judgment transport).
- **Notes** — factorization questions, open questions, and the Gate 6/7
 dependencies that remain.

**Constructive input.** A finite, checkable object: a CSS code state, a matrix,
a chain complex, a graph, a wiring map, an involution, a cellulation, or an
algebra element. Its well-formedness is decidable by linear algebra or
combinatorics; the constructor's conditions are proof obligations *over* that
data, not assumptions about it.

**Axiomatic input.** A property or existence hypothesis the calculus records
but does not verify: a distance lower bound, a family-closure claim, an
exhaustive minimum-weight-class enumeration, the existence of a typed
involution satisfying a predicate, or any consumer-supplied price. The consumer
records the source of such an input and never validates it (priced hypotheses
are inputs, not computed facts; `OBL-PRICED-INPUT-SEMANTICS`,
`JUDGMENT_LAYER.md` §2c).

**Common incurred obligations (every constructor below).** The output must be a
well-formed CSS code (invariants I1–I5) where the output lives in the ordinary
CSS model; \(X \perp Z\); displayed rows independent and spanning; every
parameter effect stated with its hypotheses; the later-layer instance of
`OBL-WELL-FORMEDNESS-PRESERVATION`; and, if property judgments are claimed,
`OBL-JUDGMENT-TRANSPORT`. None of these is discharged by this note.

---

## 2. Algebraic code-level constructors

### `A-PRODUCT`

\[
\mathsf{A\text{-} PRODUCT} : (A,B : \mathsf{ChainComplex}\mid\mathsf{CSSCode};\;
\mu : \mathsf{ProductStructure};\;
\rho : \mathsf{RetainedDisplay})
\;\to\; \mathsf{CSSCode}
\]

- **Inputs.**
 - \(A, B\) — constructive: chain complexes (or CSS states read as
 two-term complexes).
 - \(\mu\) — constructive: grading, boundary maps, and tensor/mapping-cone
 data of the product.
 - \(\rho\) — constructive: retained-presentation data of `P-REBASE` shape
 selecting which rows survive (repair (a), `TAXONOMY.md` §2.13).
- **Incurred obligations.** Product differential squares to zero; \(X\perp Z\)
 for the product; output well-formed with an independent display; row-count
 effects are functions of the retained display \(\rho\), not of code invariants;
 judgment transport inherits that dependence; distance effects are
 constructor-specific and remain `proposed`, not `established`.
- **Notes.** The CSS-tensor-product instance is not `C-DIRECT-SUM`: the factor
 qubit sets are indexed by pairs rather than placed on disjoint namespaces,
 and \(k\) multiplies. The retained-display dependence is the well-formedness
 clash of `TAXONOMY.md` §2.13. No generic distance rule.

### `A-CONCAT`

\[
\mathsf{A\text{-} CONCAT} : (O : \mathsf{CSSCode};\;
I : \mathsf{CSSCode}\mid\mathsf{StabilizerCode};\;
E : \mathsf{EncodingMap};\;
L : \mathsf{LogicalReps})
\;\to\; \mathsf{CSSCode}
\]

- **Inputs.**
 - \(O\) — constructive: outer CSS code.
 - \(I\) — constructive when it is a CSS state; an open question whether a
 non-CSS stabilizer inner is admissible (challenge board entries
 `(challenge entry)`, `(challenge entry)`, `(challenge entry)`). If admitted,
 \(I\) would be an extended-state input and this signature splits.
 - \(E\) — constructive: block interfaces and encoding maps.
 - \(L\) — constructive: chosen logical representatives for lifting.
- **Incurred obligations.** CSS compatibility of the composite; independence of
 lifted checks; block lengths and logical dimensions multiply; check-weight
 effect (max of inner weight and outer weight times representative weight)
 is a description of the lift, not a priced bound; distance effects require
 hypotheses (axiomatic if claimed); well-formedness of the output display.
- **Notes.** `A-CONCAT` is a price provider only via tower factorization
 (`JUDGMENT_LAYER.md` §2a); the constructor itself remains `taxonomy-only`.
 Non-CSS inner inputs are unresolved and must not be assumed.

### `A-DOUBLE`

\[
\mathsf{A\text{-} DOUBLE} : (C : \mathsf{CSSCode};\;
w : \mathsf{WiringMap};\;
s : \mathsf{SectorDualityChoice}\ \text{(optional)})
\;\to\; \mathsf{CSSCode}
\]

- **Inputs.**
 - \(C\) — constructive.
 - \(w\) — constructive: an explicit identification map on two copies of the
 qubit namespace.
 - \(s\) — constructive when supplied: the sector-duality choice for
 conjugate-copy variants.
- **Incurred obligations.** \(n' = 2n\); resulting rows independent and
 \(X\perp Z\); \(k\) and both distances constructor-specific (no generic
 distance rule); factorization through `A-CONCAT` (fixed two-qubit inner
 code), a cover/lift constructor, or `E-LOCAL-HADAMARD` is an open question
 under the §3.8 criteria.
- **Notes.** The free-\(\mathbb{Z}_2\) BB cover in the challenge kit is
 evidence for the cover-constructor reading, not for a dedicated primitive.
 A family name alone is not an operation.

### `A-QUOTIENT`

\[
\mathsf{A\text{-} QUOTIENT} : (V : \mathsf{StabilizerSpace}\mid\mathsf{Subspace};\;
q : \mathsf{QuotientMap};\;
e : \mathsf{EmbeddingData})
\;\to\; \mathsf{CSSCode}
\]

- **Inputs.**
 - \(V\) — constructive: typed stabilizer spaces or subspaces.
 - \(q\) — constructive: the quotient map.
 - \(e\) — constructive: kernel, embedding, and retained quotient data.
- **Incurred obligations.** \(q\) must preserve or explicitly account for CSS
 orthogonality, qubit support, and independence; rank and kernel effects
 stated; no generic distance rule; output well-formedness. Distance claims, if
 made, carry axiomatic hypotheses.
- **Notes.** "Take a subspace" is not a sufficient description; the map and
 induced CSS structure must be typed.

---

## 3. Lower-level constructors

### `L-NESTED-CSS`

\[
\mathsf{L\text{-} NESTED\text{-} CSS} : (X : \mathsf{ClassicalCode};\;
Z : \mathsf{ClassicalCode})
\;\to\; \mathsf{CSSCode}
\]

- **Inputs.** \(X, Z\) — constructive: classical linear spaces or parity-check
 matrices satisfying the nesting/orthogonality relation.
- **Incurred obligations.** \(X \perp Z\) in the CSS sense; chosen presentation
 defined; \(n,k\) follow from classical dimensions; distances require separate
 classical-code hypotheses (axiomatic if a distance claim is made).
- **Notes.** Self-orthogonal Steane/Hamming/Reed–Muller-derived codes belong
 here. Not necessarily a composition of two quantum codes.

### `L-HGP`

\[
\mathsf{L\text{-} HGP} : (C_1, C_2 : \mathsf{ClassicalCode})
\;\to\; \mathsf{CSSCode}
\]

- **Inputs.** \(C_1, C_2\) — constructive: typed classical codes or
 parity-check complexes.
- **Incurred obligations.** Matrix dimensions, tensor-factor ordering, and the
 product differential explicit; for \(H_i \in \mathbb{F}_2^{m_i \times n_i}\)
 in the standard parity-check convention the usual qubit count is
 \(n_1 n_2 + m_1 m_2\) (other conventions must state object ordering);
 distances require hypotheses (axiomatic).
- **Notes.** A genuine construction, not an operation on two already-formed CSS
 states unless the calculus defines that typed interface.

### `L-LIFTED`

\[
\mathsf{L\text{-} LIFTED} : (B : \mathsf{BaseMatrix}\mid\mathsf{ChainMap};\;
\mathcal{A} : \mathsf{Algebra};\;
\ell : \mathsf{LiftAction})
\;\to\; \mathsf{CSSCode}
\]

- **Inputs.** \(B, \mathcal{A}, \ell\) — constructive: base matrices/chain
 maps, the specified group or lift algebra, and the lift action.
- **Incurred obligations.** Coefficient algebra, involution/transpose convention,
 lift action, and orthogonality proof specified; degree and rank bounds are
 constructor-specific hypotheses; distances require hypotheses (axiomatic).
- **Notes.** Normal-subgroup lifts are specializations, not automatically a new
 primitive.

### `L-BALANCED`

\[
\mathsf{L\text{-} BALANCED} : (F_1, F_2 : \mathsf{LiftedFactor};\;
G : \mathsf{GroupAction};\;
q : \mathsf{QuotientRelation})
\;\to\; \mathsf{CSSCode}
\]

- **Inputs.** \(F_1, F_2, G, q\) — constructive.
- **Incurred obligations.** Group action, quotient relation, and induced check
 maps explicit; counts typically differ from an unconstrained lifted product
 because the quotient changes qubit and check counts; distances require
 hypotheses.
- **Notes.** The quotient is part of the typed input, not an implicit
 normalization.

### `L-GROUP-ALGEBRA`

\[
\mathsf{L\text{-} GROUP\text{-} ALGEBRA} : (a, b : \mathsf{AlgebraElement};\;
R : \mathsf{Representation})
\;\to\; \mathsf{CSSCode}
\]

- **Inputs.** \(a, b, R\) — constructive: algebra elements and a specified
 regular or coset representation.
- **Incurred obligations.** The exact representation convention must prove
 \(H_X H_Z^{\mathsf T} = 0\); nonabelian transpose/inversion conventions
 cannot remain implicit; block length, check degree, and rank depend on the
 algebra and representation; distances require hypotheses.
- **Notes.** Generalized bicycle, bivariate bicycle, multivariate bicycle,
 quadricycle, and related families are specializations or parameterizations of
 this constructor, not unrelated primitives.

### `L-TANNER`

\[
\mathsf{L\text{-} TANNER} : (\lambda : \mathsf{LocalCode};\;
\Gamma : \mathsf{TypedGraph};\;
\iota : \mathsf{EmbeddingData})
\;\to\; \mathsf{CSSCode}
\]

- **Inputs.** \(\lambda, \Gamma, \iota\) — constructive: local classical or
 CSS codes, a typed graph or group action, and local-to-global embeddings.
- **Incurred obligations.** Incidence maps, embeddings, and cross-partition
 commutation explicit; parameter effects depend on graph size, local
 dimensions, expansion, and boundary conventions; expansion/distance
 hypotheses are axiomatic if a distance claim is made.
- **Notes.** A Tanner construction is a code constructor even when described
 informally as composing local codes.

### `L-TILE`

\[
\mathsf{L\text{-} TILE} : (\tau : \mathsf{LocalTileSet};\;
\beta : \mathsf{BoundaryRules};\;
\alpha : \mathsf{Cellulation})
\;\to\; \mathsf{CSSCode}
\]

- **Inputs.** \(\tau, \beta, \alpha\) — constructive.
- **Incurred obligations.** Boundary identifications, retained/removed checks,
 and interface orthogonality specified; parameter effects depend on tile
 count, boundary type, identifications, and local rank relations; splitting
 the assembly requires tile and boundary provenance.
- **Notes.** "Packing" is not enough; the assembly must define the global
 stabilizer code.

---

## 4. Extended-state constructors

These require the Gate 6 extended-state layer (`X-SYMPLECTIC-DOUBLE` /
`X-SYMPLECTIC-HALVE` decision) before they can be admitted. At the CSS layer
their inputs are axiomatic existence hypotheses rather than checkable data.

### `X-SYMPLECTIC-DOUBLE`

\[
\mathsf{X\text{-} SYMPLECTIC\text{-} DOUBLE} :
(S : \mathsf{StabilizerCode}) \;\to\; \mathsf{CSSCode}
\]

- **Inputs.** \(S\) — constructive within the extended model: a general
 stabilizer code on \(n\) qubits presented by a symplectic check matrix
 \(H = (A \mid B)\) with \(AB^{\mathsf T}+BA^{\mathsf T}=0\).
- **Incurred obligations.** Input commuting condition; output CSS by
 construction (\(H_X'=(A\mid B)\), \(H_Z'=(B\mid A)\) on \(2n\) qubits);
 \(n'=2n,\ k'=2k,\ d \le d' \le 2d\) are candidate effects pending
 derivation; CSS-model well-formedness of the doubled output.
- **Notes.** Doubling lives outside the ordinary-CSS model in general; this
 record is deferred, not conditioned, into the CSS layer. Distinct from
 `A-DOUBLE`.

### `X-SYMPLECTIC-HALVE`

\[
\mathsf{X\text{-} SYMPLECTIC\text{-} HALVE} :
(C : \mathsf{CSSCode};\;
\pi : \mathsf{Involution})
\;\to\; \mathsf{StabilizerCode}
\]

- **Inputs.**
 - \(C\) — constructive: a CSS code on \(2n\) qubits.
 - \(\pi\) — constructive data when supplied: a fixed-point-free qubit
 involution with \(\pi(S_X)=S_Z\). Its *existence* for a given \(C\) is a
 decidable linear-algebra property and is currently a `not yet defined`
 judgment slot (axiomatic at the CSS layer).
- **Incurred obligations.** \(\pi\) fixed-point-free and exchanges the sector
 row spaces; folded checks commute from parent CSS orthogonality;
 \(n'=n/2,\ k'=k/2,\ \lceil d/2\rceil \le d' \le d\); output is not
 representable in the ordinary-CSS model.
- **Notes.** Inverse of `X-SYMPLECTIC-DOUBLE` on doubled outputs.

### `X-SUBSYSTEM`

\[
\mathsf{X\text{-} SUBSYSTEM} :
(G : \mathsf{GaugeData};\;
S : \mathsf{CenterData};\;
L : \mathsf{LogicalData})
\;\to\; \mathsf{SubsystemCode}
\]

- **Inputs.** \(G, S, L\) — constructive within the extended model (gauge
 generators, stabilizer centers, bare/dressed logical data); at the CSS layer
 they are axiomatic existence hypotheses because the extended state model is
 not admitted.
- **Incurred obligations.** Gauge/stabilizer-center relations; bare and
 dressed logical distances distinguished; subsystem-code well-formedness.
- **Notes.** Requires subsystem-code states and update rules for gauge groups
 and stabilizer centers (`TAXONOMY.md` §4.2).

### `X-GAUGE-FIX`

\[
\mathsf{X\text{-} GAUGE\text{-} FIX} :
(E : \mathsf{ExtendedState};\;
g : \mathsf{GaugeGeneratorChoice})
\;\to\; \mathsf{ExtendedState}\mid\mathsf{CSSCode}
\]

- **Inputs.** \(E, g\) — constructive within the extended model; axiomatic at
 the CSS layer.
- **Incurred obligations.** Gauge fixing reduces to adding \(L_g^X\) to the
 stabilizer subset only after gauge operators are admitted to the state
 (external support, `TAXONOMY.md` §4.1); purity/CSS-preservation condition
 must be checked; distance judgments distinguish bare and dressed distance.
- **Notes.** Should not be represented as ordinary `C-ADD-CHECK` until gauge
 generators are part of the state.

---

## 5. Common consequences recorded

- No constructor above is admitted; none has a grammar production; all remain at
 rung 1 (`taxonomy-only`).
- Inputs classified *constructive* are finite data whose well-formedness is
 decidable; inputs classified *axiomatic* are hypotheses the calculus records
 and does not validate.
- Distance, closure, and enumeration claims attached to any constructor are
 conditional on externally justified hypotheses and never become `proved` by
 this note.
- Promotion above rung 1 requires a dated maintainer decision in
 a dated maintainer decision plus the stated hypotheses and
 proof/evidence obligations being met.
