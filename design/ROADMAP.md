# Roadmap

**Role:** non-normative design note. This document indexes every operation,
constructor, and judgment extension on the calculus's admission ladder
([`spec/CLAIMS.md`](../spec/CLAIMS.md) §1), showing what is already admitted,
what is staged as a candidate, and what is deferred. Where this note and
[`spec/`](../spec/) disagree, `spec/` wins.

---

## The admission ladder

Restated from [`spec/CLAIMS.md`](../spec/CLAIMS.md) §1:

```text
taxonomy-only → syntax-candidate → transition-defined → state-sound
  → contract-stated → contract-proved → mechanized
```

A candidate or planned transition is not an admitted calculus rule until it
lands in [`spec/`](../spec/).

---

## 1. The kernel (rung 6 — `contract-proved`)

All five kernel operations are at rung 6 (`contract-proved`), backed by typed
transitions, complete applicability premises, exact state/context updates,
conditional carry cells, and hand derivations in
[`spec/OPERATIONAL_SEMANTICS.md`](../spec/OPERATIONAL_SEMANTICS.md) §4
(including quotient-level logical-sector exact sequences in §4.39 and
`stdCSS-3` re-discharge records in §4.40).

| Operation | Rung | Transition & applicability | State/context update & carry cells | Derivations |
| --- | --- | --- | --- | --- |
| `C-SKIP` | 6 — `contract-proved` | `m ::= skip`; no premises ([`spec/OPERATIONAL_SEMANTICS.md`](../spec/OPERATIONAL_SEMANTICS.md) §1–§2) | Identity on $Q$, display, and `used`; all carry cells unconditional identity ([`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md) §2, §2b, §2d.5, §2h) | §4.6–§4.8, §4.11, §4.13, §4.21–§4.22, §4.37, §4.40 |
| `C-DIRECT-SUM` | 6 — `contract-proved` | `e ::= e₁ ⊕ e₂`; $Q_A \cap Q_B = \varnothing$, $\mathsf{used}_A \cap \mathsf{used}_B = \varnothing$ (§2) | Disjoint union of $Q$, display, `used` (no mint); exact `min` distance & structural cells; conditional honest merged layout for $r$ (§2d.3, §2d.5) and `OBL-FRAME-LAW` (§4.9) | §4.4, §4.7–§4.9, §4.11, §4.13, §4.21–§4.22, §4.37, §4.39, §4.40 |
| `C-DELETE-CHECK` | 6 — `contract-proved` | `m ::= delete_r`; `DisplayedGenerator` + `Independent` (§2) | Removes $r$, retires ID in `used`; non-increase upper bound `[proved]`, unpriced exact `unavailable`; conditional full-distance price $d' = \min(d, w_{\mathrm{del}}, w_{\mathrm{exp}})$ (§2a–§2c) | §4.1, §4.5, §4.7–§4.11, §4.13, §4.15–§4.19, §4.21–§4.22, §4.37, §4.39, §4.40 |
| `C-ADD-CHECK` | 6 — `contract-proved` | `m ::= addStab_r`; $\mathrm{supp}(r) \subseteq Q$ (`W22`), opposite-sector commutation, same-sector independence, H-4 capacity (§2) | Appends $r$ with canonical mint in `used`; nondecrease lower bound `[proved]`, exact `open`; three conditional cells (§2a–§2c): strict improvement, sector-aware gauging, direct-sum extinction | §4.2–§4.3, §4.7–§4.11, §4.13, §4.16–§4.19, §4.21–§4.22, §4.37, §4.39, §4.40 |
| `C-SEQUENCE` | 6 — `contract-proved` | `m ::= m₁ ; m₂`; left-to-right composition of premises (`W10`, §1–§2) | Intermediate state feeds $m_2$; structural persistence & single-polarity composition `[proved]` (§4.11; `W13` `unavailable`); conditional step-wise interval composition (`OBL-PRICED-INTERVAL-SOUNDNESS`, §4.13) | §4.6–§4.8, §4.10–§4.11, §4.13, §4.15, §4.17, §4.21–§4.23, §4.37, §4.40 |

Rung 6 records hand-derivation evidence (`proved`). Full machine-checked
soundness (rung 7 — `mechanized`) remains open, and Gate 7 remains unchecked
([`spec/GATES.md`](../spec/GATES.md)).

---

## 2. Admitted extensions and expression constructors

### Conditional CSS extensions and `P-REBASE`

These operations have defined transitions and conditional carry cells in
[`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md) §2f (with `E-GRAFT` at
§2a–§2c). Each carries only when the consumer supplies the stated hypotheses;
otherwise distance cells remain `unavailable` or `not yet defined`. Interval
transformer soundness under these hypotheses (`OBL-GATE6-CSS-EXTENSIONS`) is
discharged by hand derivation in §4.32 and mechanized conditionally in
[`lean/CodeCalculus/Gate6Soundness.lean`](../lean/CodeCalculus/Gate6Soundness.lean).

| Entry | Rung | Notes |
| --- | --- | --- |
| `E-GLUE` | 5 — `contract-stated` | Binary-only expression constructor `glue(e₁, e₂; seams)` ([`spec/TERM_LANGUAGE.md`](../spec/TERM_LANGUAGE.md) §1–§2). Both witness fields are defined ([`spec/STATE_MODEL.md`](../spec/STATE_MODEL.md) §1a; [`WitnessFields.lean`](../lean/CodeCalculus/WitnessFields.lean)). Algebraic extraction and family-level `AdmissibleSeam` soundness are mechanized across `ExactGlue*.lean`, `LogicalWitness.lean`, `AdmissibleSeamFamily.lean`, `Gate6Exact.lean`, and `GlueExtraction.lean`; the remaining geometric step (planar move words $\to$ `AdmissibleSeam`) is recorded in [`ADMISSIBLE_SEAM_FAMILY.md`](ADMISSIBLE_SEAM_FAMILY.md). |
| `E-GRAFT` | 3 — `transition-defined` | Conditional construction extension; `OBL-GRAFT-TRANSITION-SOUNDNESS`, `OBL-PRICED-INTERVAL-SOUNDNESS`, and `OBL-PRICED-INPUT-SEMANTICS` discharged by hand derivation (§4.12–§4.14). |
| `E-PEEL`, `E-PUNCTURE` | 3 — `transition-defined` | Typed transitions and carry/refutation derivations in [`spec/OPERATIONAL_SEMANTICS.md`](../spec/OPERATIONAL_SEMANTICS.md) §4.28–§4.29; exact peel relations mechanized in [`ExactPeel.lean`](../lean/CodeCalculus/ExactPeel.lean). |
| `E-EXTEND` | 3 — `transition-defined` | Patch growth / breeding (§4.30). |
| `E-LOCAL-HADAMARD` | 3 — `transition-defined` | Sector swap on $T = Q$ (§4.27); involution and conjugation laws mechanized in [`DualityAdjunction.lean`](../lean/CodeCalculus/DualityAdjunction.lean). |
| `P-REBASE` | 3 — `transition-defined` | Presentation rebasing `rebase(τ; M)` (§4.26, discharging `OBL-REBASE-GENERATION`); rank preservation mechanized in [`RebaseRankSector.lean`](../lean/CodeCalculus/RebaseRankSector.lean). |

### Expression constructors (rung 3 — `transition-defined`)

All expression constructors below are admitted at rung 3 with productions in
[`spec/TERM_LANGUAGE.md`](../spec/TERM_LANGUAGE.md) §1–§2, cards in
[`spec/OPERATIONAL_SEMANTICS.md`](../spec/OPERATIONAL_SEMANTICS.md) §2, and
default distance intervals $[0, +\infty)$ per
[`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md) §2g (no automatic
distance lower-bound rules):

- **`stdCSS-3` construction family:** `L-HGP`, `L-LIFTED` (finite abelian
  groups), `L-GROUP-ALGEBRA` (two-block over a finite abelian group),
  `A-CONCAT` (CSS factors), `L-BALANCED`, `L-TANNER`, `L-TILE`, `A-PRODUCT`
  (CSS tensor product), `A-DOUBLE` (two-sheet cover), and `L-NESTED-CSS`
  ([`spec/OPERATIONAL_SEMANTICS.md`](../spec/OPERATIONAL_SEMANTICS.md)
  §4.34–§4.36; consumer support in [`machine/constructors.py`](../machine/constructors.py);
  Lean well-formedness and rank bookkeeping in [`lean/CodeCalculus/`](../lean/CodeCalculus/)
  and [`AXIOMS.md`](../AXIOMS.md)).
- **Nullary and interface constructors:** `L-EMPTY`, `L-FREE`, `A-PULLBACK`,
  and `A-PUSHOUT` ([`spec/OPERATIONAL_SEMANTICS.md`](../spec/OPERATIONAL_SEMANTICS.md)
  §4.43; [`NULLARY_AND_INTERFACE_CONSTRUCTORS.md`](NULLARY_AND_INTERFACE_CONSTRUCTORS.md)).

### Gate-realization and family-level judgment rows

- **Gate-realization rows ([`GATE_REALIZATION_ROWS.md`](GATE_REALIZATION_ROWS.md)):**
  Codespace preservation $\mathsf{preserves}_U(C)$ on CSS displays and the
  equal-syndrome generator weight floor $\omega(C) \ge \lceil d(C)/2 \rceil$
  (carried by weakening as $\lceil L_d / 2 \rceil$) are admitted in
  [`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md) §2, §2h, and §7.1–§7.4
  and derived in §4.37. Because CSS displays determine the phase $(-i)^m$ of
  any product of $X$- and $Z$-rows sharing $m$ qubits, phase-insensitivity of
  the CSS state model does not block CSS gate-preservation checks. Logical-gate
  addressability, logical action, and the non-$\pi/4$ anticommuting
  `C-ADD-CHECK` branch remain `not yet defined`.
- **Conditional family-level level-map transport:** Yuan's one-shot
  hollowed-tensor level map is recorded in
  [`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md) §2j ($k' = k$
  conditional on Lemma 118, $n$ inflation beyond $m \cdot n$ per tower level,
  and an upper ceiling on region-graph failure probability), with amplified
  distance lower bounds remaining `unavailable`.

---

## 3. Deferred and candidate work

### Deferred CSS-layer operations (rung 1 — `taxonomy-only`)

| Entry | Blocked by | Promotion criterion |
| --- | --- | --- |
| `P-RELABEL` | No grammar production; `OBL-PRESENTATION-CONJUGATION` out of scope | Admitting relabeling as ordinary syntax and discharging `OBL-PRESENTATION-CONJUGATION`. |
| `E-SPLIT` | Merge/split routing outside current scope | Formal admission decision with typed transition, premises, and carry cells. |
| `A-QUOTIENT` | No grammar production (`spec/JUDGMENT_LAYER.md` §2i records the conditional monomial-quotient transfer-theorem slot only) | Typed quotient map/embedding syntax, well-formedness derivation, and distance/parameter cells. |

### Extended-state (non-CSS) layer (rung 1 — `taxonomy-only`, deferred)

The extended-state layer requires a two-sorted state model (general stabilizer
codes presented by symplectic check matrices with per-row signs alongside CSS
codes). It is outside the current `C = (Q, X, Z, pres, used)` scope. A
consumer-side prototype lives in
[`machine/symplectic_calculus.py`](../machine/symplectic_calculus.py), which
admits no calculus rules.

| Entry | Role and promotion prerequisite |
| --- | --- |
| `X-SYMPLECTIC-DOUBLE` | General stabilizer $\to$ CSS ($n'=2n$, $k'=2k$, $d \le d' \le 2d$). Requires two-sorted state model. |
| `X-SYMPLECTIC-HALVE` | CSS $\to$ general stabilizer via fixed-point-free involution $\pi$ with $\pi(S_X) = S_Z$ ($n'=n/2$, $k'=k/2$, $\lceil d/2\rceil \le d' \le d$). |
| `X-LOCAL-CLIFFORD` | General local Clifford conjugation (CSS-preserving single-qubit instance is `E-LOCAL-HADAMARD`). |
| `X-DRESSED-QUOTIENT` | Commuting-projector dressed quotient from higher-form/cup-polynomial backgrounds. |
| `X-SUBSYSTEM`, `X-GAUGE-FIX` | Subsystem and gauge-fixing extensions. |
| `X-WEIGHT-REDUCTION` | 3-local subsystem weight reduction via layer codes. |

### Other candidate constructions and judgment extensions

These candidates are tracked in design notes and consumer experiments; none is
admitted to [`spec/`](../spec/) without a formal promotion decision:

| Candidate | Summary & current status |
| --- | --- |
| **Mapping-cone constructor** | Formulated and audited in [`MAPPING_CONE_CONSTRUCTOR.md`](MAPPING_CONE_CONSTRUCTOR.md) with consumer prototype in [`machine/experiments/mapping_cone.py`](../machine/experiments/mapping_cone.py). Needs resolution of distance-formula hypotheses and `L-` placement. |
| **Decoupling of translation-invariant CSS codes** | Formulated in [`DECOUPLING_CONSTRUCTOR.md`](DECOUPLING_CONSTRUCTOR.md) as a certificate-checked SUM/SWAP circuit relation with prototype in [`machine/experiments/translation_invariant_decoupling.py`](../machine/experiments/translation_invariant_decoupling.py). Requires translation-invariance data outside the core state model. |
| **Multi-band patch count** | Construction metadata prototype in [`machine/experiments/multi_band_patch_count.py`](../machine/experiments/multi_band_patch_count.py); physical check-structure reconstruction from geometry remains open. |
| **Positive composition criteria & insufficiency** | Baseline seam certificate and no-go obstruction are in [`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md) §2e; richer interface classification and boundary-signature certificates remain candidate extensions. |
| **CNOT-disguised direct sums & depth-one equality** | Conditional presentation-transform judgment candidates; must preserve Hamming-weight non-invariance under general Clifford conjugation. |
| **Hole punch (`E-PUNCTURE` pricing)** | Full hole price remains `unavailable` in [`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md) §2f pending acceptance of a strict-interior lower bound. |
| **Graphlike exposure & arbitrary-$k_{\mathrm{in}}$ tower pricing** | Price-provider extensions documented in [`DERIVED_RELATIONS.md`](DERIVED_RELATIONS.md) §2a and §3a; column-weight-three hardness stays out of the graphlike provider. |

### Evaluator and Lean mechanization status

- **Evaluator ([`machine/`](../machine/)):** [`machine/priced_calculus.py`](../machine/priced_calculus.py)
  executes the admitted subset and passes pinned state and judgment conformance
  harnesses in CI. Adding new admitted transitions requires wiring them through
  the evaluator with fixtures.
- **Formalization ([`lean/`](../lean/)):** The Lean 4 development covers the
  presented state, identifier enumeration, presentation equality $\equiv$,
  invariants I1–I5, `EvalExpr`/`Eval`, interval ledger, `Transport.lean`,
  `Gate6Soundness.lean`, `Gate6Exact.lean`, `GlueExtraction.lean`,
  `DualityAdjunction.lean`, and constructor well-formedness/rank theorems.
  Discharging the four classical rank axioms in [`AXIOMS.md`](../AXIOMS.md) and
  completing full soundness across all extensions remain open.

---

## 4. Promotion and pull rules

- **Promotion rule:** Every roadmap entry must state a concrete promotion
  criterion (typed signature, applicability premises, well-formedness and
  judgment derivations); entries without a concrete criterion are dropped
  rather than parked.
- **Release pull rule:** At each release boundary ([`spec/VERSIONING.md`](../spec/VERSIONING.md)),
  entries whose promotion criteria are now satisfied are reviewed for promotion,
  with accepted changes recorded in [`CHANGELOG.md`](../CHANGELOG.md).
