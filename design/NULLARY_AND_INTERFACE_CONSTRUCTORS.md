# Nullary and interface constructors

**Status:** non-normative design note. This note documents the design rationale,
well-formedness conditions, and distance boundaries for the nullary, qubit-set,
and interface expression constructors (`L-EMPTY`, `L-FREE`, `A-PULLBACK`, and
`A-PUSHOUT`), as well as the refusal of a Kan-extension constructor. These four
constructors are admitted at `transition-defined` in
[`spec/TERM_LANGUAGE.md`](../spec/TERM_LANGUAGE.md) §1–§2,
[`spec/OPERATIONAL_SEMANTICS.md`](../spec/OPERATIONAL_SEMANTICS.md) §2 and
§4.43, and [`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md) §2g and
§2d.5, with consumer support in
[`machine/constructors.py`](../machine/constructors.py) and Lean
well-formedness theorems in
[`lean/CodeCalculus/ConstructorInstances.lean`](../lean/CodeCalculus/ConstructorInstances.lean).
Where this note and `spec/` touch the same ground, `spec/` wins.

---

## 1. Reading convention

Signatures follow the operadic form described in
[`CONSTRUCTOR_SIGNATURES.md`](CONSTRUCTOR_SIGNATURES.md). Inputs are either
*constructive* (finite, checkable objects) or *axiomatic* (supplied,
unvalidated hypotheses). Every constructor incurs the common obligations of
well-formed output (invariants I1–I5 and ambient containment), $X \perp Z$,
independent display, property-inventory cells for $n$, $k$, $w$, Tanner
connectivity $\kappa$, and interaction radius $r$ (under a supplied honest
layout), plus `OBL-WELL-FORMEDNESS-PRESERVATION` and `OBL-JUDGMENT-TRANSPORT`
where property judgments are claimed.

**Semantic distance vs. consumer ledger (`JUDGMENT_LAYER.md` §2g).**
Under [`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md) §2g, constructed
states initialize their consumer distance intervals at $[0, +\infty)$ in every
sector and for the full distance; a lower endpoint rises only through a
supplied bound with source provenance (or an explicitly admitted semantic rule),
and an upper endpoint tightens only through a validated logical witness (§2c).
Where a base-set constructor has an exact semantic distance fixed by definition
of the empty check set ($+\infty$ at $k = 0$, or $1$ at $k = |Q| \ge 1$), both
the exact semantic distance of the state and the §2g consumer-ledger rule are
stated separately below so the two are never conflated.

---

## 2. Empty and qubit-set base constructors

### `L-EMPTY` (`empty` — strictly nullary)

$$
\mathsf{empty} : \;\to\; \mathsf{CSSCode}
$$

- **Inputs.** None (0-ary).
- **State.** $Q = \varnothing$, empty display (`rows = []`, so
  $X = Z = \{0\} \subseteq \mathbb{F}_2^{\varnothing}$), empty `used`.
- **Well-formedness.** Invariants I1–I5 and ambient containment hold vacuously;
  canonical mint is vacuous; equality and `used` are trivial. In Lean,
  `emptyState 0` in [`lean/CodeCalculus/Constructors.lean`](../lean/CodeCalculus/Constructors.lean)
  is proved well-formed by `wf_emptyState 0`
  ([`lean/CodeCalculus/ConstructorWellFormedness.lean`](../lean/CodeCalculus/ConstructorWellFormedness.lean)).
- **Property and judgment cells.**
  - $n = 0$, exact; $k = 0$, exact.
  - $w = 0$ (empty display), Tanner components $\kappa = 0$ (empty Tanner
    graph), interaction radius $r = 0$ relative to any supplied honest layout
    on $\varnothing$ ([`spec/REPRESENTATION.md`](../spec/REPRESENTATION.md)
    §3; [`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md) §2d.1).
  - *Semantic distance vs. §2g ledger:* because $k = 0$, no logical operator
    exists in either sector, so the exact semantic distances are
    $d_X = d_Z = d = +\infty$. Under §2g, `DistanceLedger.for_constructed`
    starts at $[0, +\infty)$; no finite witness exists, and raising the lower
    endpoint to $+\infty$ requires either a sourced input or an explicitly
    admitted semantic rule.
- **Status.** Admitted at `transition-defined` (`L-EMPTY`).

### `L-FREE` (`free(Q)` — qubit-set base constructor)

$$
\mathsf{free} : (Q : \mathsf{QubitSet}) \;\to\; \mathsf{CSSCode}
$$

- **Inputs.** $Q$ — constructive: a finite set of qubit labels
  ($Q \subset \mathbb{N}$). Because `free` takes $Q$ as an input, it is **not**
  strictly nullary (it is unary in `QubitSet`, and 0-ary only in the sense of
  taking zero input `CSSCode`s; `free(∅)` coincides with `empty`).
- **State.** The supplied $Q$, empty display (`rows = []`, so
  $X = Z = \{0\} \subseteq \mathbb{F}_2^Q$), empty `used`.
- **Well-formedness.** CSS orthogonality (I1), displayed independence (I2),
  identifier discipline (I3), sector typing (I4), provenance (I5), and ambient
  containment hold vacuously over an empty row list; canonical mint is vacuous.
  In Lean, `emptyState n` (for contiguous labels $Q = \{0, \dots, n - 1\}$) is
  proved well-formed by `wf_emptyState n`
  ([`lean/CodeCalculus/ConstructorWellFormedness.lean`](../lean/CodeCalculus/ConstructorWellFormedness.lean)).
- **Property and judgment cells.**
  - $n = |Q|$, exact; $k = |Q|$, exact.
  - $w = 0$ (empty display), Tanner components $\kappa = |Q|$ (isolated
    qubit vertices with no check vertices), interaction radius $r = 0$
    relative to any supplied honest layout on $Q$
    ([`spec/REPRESENTATION.md`](../spec/REPRESENTATION.md) §3).
  - *Semantic distance vs. §2g ledger:*
    - When $Q = \varnothing$, `free(∅) ≡ empty` with $n = 0$, $k = 0$, and
      semantic $d_X = d_Z = d = +\infty$.
    - When $Q \neq \varnothing$ ($|Q| \ge 1$), every singleton $\{q\}$ ($q \in
      Q$) is a weight-$1$ logical in both sectors (there are $|Q|$ such
      weight-$1$ logicals), so the exact semantic distances are
      $d_X = d_Z = d = 1$. Under §2g alone, `DistanceLedger.for_constructed`
      starts at $[0, +\infty)$ and validating any singleton witness $\{q\}$
      tightens both sector upper endpoints and the full upper endpoint to $1$.
- **Status.** Admitted at `transition-defined` (`L-FREE`).

---

## 3. Interface constructors

### `A-PULLBACK` (`pullback(e₁, e₂, e_I; φ₁, φ₂)` — fiber product)

$$
\mathsf{pullback} : (C_1, C_2, I : \mathsf{CSSCode};\;
\phi_1 : C_1 \to I,\; \phi_2 : C_2 \to I) \;\to\; \mathsf{CSSCode}
$$

- **Inputs.** $C_1, C_2, I$ — constructive: presented CSS states (with $I$
  explicitly bound as the shared interface code). $\phi_1 : C_1 \to I$ and
  $\phi_2 : C_2 \to I$ — typed morphisms of CSS codes. Set-level equalizers
  (common subcode / intersection of parallel maps $C_1 \rightrightarrows I$)
  fold into this constructor.
- **State.** Output qubits are the fiber product $Q_1 \times_{Q_I} Q_2$ indexed
  canonically over pairs; output $X$- and $Z$-rows are pulled back from the
  input displays and retained to an independent spanning subset with
  canonically minted identifiers from empty `used`.
- **Well-formedness.** Interface compatibility and CSS orthogonality
  ($X \perp Z$ of the constructed output rows) are **decidable** applicability
  premises checked over the finite constructive inputs
  ([`spec/OPERATIONAL_SEMANTICS.md`](../spec/OPERATIONAL_SEMANTICS.md) §4.43).
- **Property and judgment cells.** $n = |Q_1 \times_{Q_I} Q_2|$ exact; $k$ by
  rank bookkeeping over the retained display; $w$, $\kappa$, and $r$ (under a
  supplied honest layout) recomputed exactly over the constructed display per
  §2g. Constructed distances start at $[0, +\infty)$ per §2g and move only via
  a sourced lower bound or validated witness. In particular, the naive pullback
  lower bound $d(A \times_C B) \ge \min(d_A, d_B)$ is **false** in general, so
  no uncertified factor-minimum lower bound carries.
- **Status.** Admitted at `transition-defined` (`A-PULLBACK`).

### `A-PUSHOUT` (`pushout(e₁, e₂, e_S; ψ₁, ψ₂)` — amalgamated sum)

$$
\mathsf{pushout} : (C_1, C_2, S : \mathsf{CSSCode};\;
\psi_1 : S \to C_1,\; \psi_2 : S \to C_2) \;\to\; \mathsf{CSSCode}
$$

- **Inputs.** $C_1, C_2, S$ — constructive: presented CSS states (with $S$
  explicitly bound as the shared interface/subcode). $\psi_1 : S \to C_1$ and
  $\psi_2 : S \to C_2$ — typed CSS code morphisms identifying qubits and
  compatible stabilizer data along $S$. Two-code set-level coequalizers fold
  here, while single-code self-zipping coequalizers fold into `A-QUOTIENT`
  ([`spec/TAXONOMY.md`](../spec/TAXONOMY.md) §2.15).
- **State.** Generalized amalgamation identifying $Q_1$ and $Q_2$ along the
  shared subcode $S$ (the pushout $Q_1 \sqcup_{Q_S} Q_2$), with amalgamated
  output rows retained to an independent display with canonically minted
  identifiers from empty `used`. Unlike `E-GLUE`, which forms a disjoint union
  $Q_A \sqcup Q_B$ with added planar seam checks, `pushout` identifies shared
  qubits and checks directly.
- **Well-formedness.** Seam compatibility and interface orthogonality
  ($X \perp Z$ after identification along $S$) are **decidable** checkable
  premises ([`spec/OPERATIONAL_SEMANTICS.md`](../spec/OPERATIONAL_SEMANTICS.md)
  §4.43).
- **Property and judgment cells.** $n = |Q_1 \sqcup_{Q_S} Q_2|$ exact; $k$ by
  rank bookkeeping over the retained display; $w$, $\kappa$, and $r$ (under a
  supplied honest layout) recomputed exactly over the constructed display per
  §2g. Constructed distances start at $[0, +\infty)$ per §2g and rise only via
  a supplied sourced bound or validated seam certificate. Unlike `E-GLUE`'s
  disjoint-factor planar seam, a general pushout along a nontrivial shared
  subcode $S \neq 0$ **can drop distance**, so factor minima do **not** carry
  unconditionally without a certificate or explicit hypothesis.
- **Status.** Admitted at `transition-defined` (`A-PUSHOUT`).

### Refusal of Kan extension

A meta-level Kan-extension candidate was evaluated and **refused** as a state
constructor because it states neither a finite state update on
$C = (Q, X, Z, \mathsf{pres}, \mathsf{used})$ nor a concrete promotion
criterion. No taxonomy identifier or grammar production is assigned to it.
