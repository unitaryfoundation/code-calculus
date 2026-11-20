# Scope and stopping point

**Role:** non-normative design note. This note states the project's research
question, its explicit stopping point, and what it intentionally leaves out of
scope. The calculus's formal rules live in [`spec/`](../spec/), which is
authoritative wherever this note and `spec/` touch the same ground.

---

## 1. The research question

**What is a sound calculus of code transformations?**

Concretely, the project studies an object with four parts:

1. **States** — a typed description of a CSS code together with its
   presentation, so that "which generator" is a well-formed question.
2. **Transformations as terms** — a typed term language whose closed terms
   denote transformation sequences rather than imperative procedures.
3. **Operational semantics** — a partial big-step relation; absence of a
   derivation is part of the semantics, not an error.
4. **Judgment layer** — for each property in the signature and each
   transformation, a determination of whether that property carries, does not
   carry, is conditional on supplied hypotheses, or is `unavailable` /
   `not yet defined`, scoped per evaluation rather than per state.

The central metatheoretic property is:

> **Soundness.** Every derivable judgment is true of the state or evaluation the
> term denotes.

The aim is not to compute code distances. It is to make **which facts survive
which transformation, and what each step is permitted to assume**, syntactic
objects that can be checked rather than re-argued.

## 2. Deliberate incompleteness

The calculus is **intended to be sound and deliberately incomplete**. A class of
properties—such as exact deletion-distance lower bounds without external
pricing—is recorded as `unavailable` (withheld by design commitment) rather than
silently omitted or approximated.

In particular, the calculus distinguishes four outcomes in
[`spec/CLAIMS.md`](../spec/CLAIMS.md): `false`, `not derivable`,
`unavailable`, and `not yet defined`. Collapsing these is a common source of
overclaim in code-construction work; keeping them distinct makes the calculus's
limits auditable.

Named soundness obligations have dated hand derivations in
[`spec/OPERATIONAL_SEMANTICS.md`](../spec/OPERATIONAL_SEMANTICS.md) §4, while
the Lean mechanization under [`lean/`](../lean/) covers a growing subset and
does not yet establish full soundness of the entire calculus.

## 3. In scope (the stopping point)

| Component | Scope |
| --- | --- |
| **Transformations** | The five kernel operations (`C-SKIP`, `C-DIRECT-SUM`, `C-DELETE-CHECK`, `C-ADD-CHECK`, `C-SEQUENCE`); conditional cells for `E-GRAFT`, priced `C-DELETE-CHECK`, and `C-ADD-CHECK` (strict improvement, sector-aware gauging, direct-sum extinction); the CSS-level Gate 6 extensions (`E-GLUE`, `E-PUNCTURE`, `E-PEEL`, `E-EXTEND`, `E-LOCAL-HADAMARD`, `P-REBASE`) as conditional cells requiring consumer-supplied hypotheses; and the `transition-defined` expression constructors (`L-HGP`, `L-LIFTED`, `L-GROUP-ALGEBRA`, `A-CONCAT`, `L-BALANCED`, `L-TANNER`, `L-TILE`, `A-PRODUCT`, `A-DOUBLE`, `L-NESTED-CSS`, plus `L-EMPTY`, `L-FREE`, `A-PULLBACK`, `A-PUSHOUT`). |
| **Properties** | $n$, $k$, $d_X$, $d_Z$, $d$, maximum stabilizer weight $w$, interaction radius $r$ (relative to a supplied layout), Tanner connectivity $\kappa$ of displayed rows, and the gate-realization properties ($\mathsf{preserves}_U$ and equal-syndrome weight floor $\omega$). |
| **Per-cell judgments** | For each operation and property: `carries`, `does not carry`, `not yet defined`, or `conditional` (scoped per evaluation), plus the conditional family-level one-shot level-map transport rule ([`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md) §2j). |
| **Mechanization** | Lean 4 formalization of the state model, operational semantics, hand derivations, and soundness metatheorem under [`lean/`](../lean/). |
| **Consumption** | The discovery-facing consumer prototype under [`machine/`](../machine/): evaluator, interval ledger, certify/prune/re-measure loop, qLDPC adapter, and planner. Supplied lower bounds, prices, and enumerations remain trusted inputs. |

**Deliverable criterion.** The stopping point is reached when every in-scope
cell is stated and transcribed, every in-scope obligation is discharged or shown
not to hold, and the consumer decides targets from transported intervals
whenever they suffice—requesting re-measurement only when they do not. Executing
the consumer is empirical evidence of utility, not a proof of soundness.

**Family-level boundary.** The conditional family-level transport rule for
Yuan's one-shot hollowed-tensor level map ([`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md)
§2j) records $k' = k$ (conditional on Lemma 118), $n$ inflation beyond $m \cdot n$
per tower level, and an upper ceiling on region-graph failure probability.
General family closure, family-level completeness, and amplified distance lower
bounds (`unavailable`) remain out of scope.

**Price-provider boundary.** Concatenation-tower factorization (`A-CONCAT`) is
also used as a source of deletion and exposure prices for `C-DELETE-CHECK`,
separate from its `transition-defined` expression constructor.

## 4. Out of scope, with reasons

| Excluded | Reason |
| --- | --- |
| **Non-CSS extended-state layer** (`X-SYMPLECTIC-DOUBLE`, `X-SYMPLECTIC-HALVE`, `X-LOCAL-CLIFFORD`, etc.) | Requires a two-sorted state model with phase/sign tracking; the core state model stays `C = (Q, X, Z, pres, used)`. |
| **Family closure and completeness** | The calculus does not aim to be complete or to close over arbitrary code families; `unavailable` commitments are part of the design. |
| **Code lineage** | Recorded by the downstream consumer rather than by the calculus state; the calculus is responsible only for property propagation. |
| **Verified per-state certificates** | The consumer records provenance for supplied hypotheses and bounds, but does not independently validate external exact prices or minimum-weight enumerations. |
| **Downstream search control** | Learned budget allocation and heuristic decision models live downstream of the consumer interface, not inside the calculus. |

## 5. Obligation ledger and non-transport

The full obligation inventory and current discharge statuses live in
[`spec/OBLIGATIONS.md`](../spec/OBLIGATIONS.md), and the proof-gate status lives
in [`spec/GATES.md`](../spec/GATES.md).

One structural boundary is worth highlighting here: **non-transport under
deletion (`W13`)**. When a claim references a deleted generator, the judgment
transport rule's schema condition fails to fire, so no derivation closes. Absence
of a derivation serves as the machine-checkable witness for non-transport. This
establishes a *refutation* ("no derivation closes in the current rule set"), not
a universal impossibility theorem ("no derivation can ever close under any
future extension").

## 6. What this note does not do

This note decides no proof gate, discharges no obligation, and changes no claim
status. It does not claim that the calculus is complete or fully machine-checked,
nor that the executable consumer or its challenge replay proves any theorem.
