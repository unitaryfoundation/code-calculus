# Expressibility of non-transport under generator deletion

**Role:** non-normative design note. This note explains why the non-transport
requirement under generator deletion (`W13` in
[`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md)) is witnessed by the
*absence of a derivation* rather than by a separate negative-conclusion rule.
The normative rules live in [`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md),
which is authoritative wherever this note and `spec/` touch the same ground.

---

## 1. The asymmetry in judgment transport

The judgment-transport obligation
([`OBL-JUDGMENT-TRANSPORT`](../spec/OBLIGATIONS.md)) has two halves:

1. **Positive transport:** a claim mentioning only invariant fields transports
   across sequential composition (`C-SEQUENCE`).
2. **Non-transport (`W13`):** any claim referring to a deleted generator is
   *not* transported, scoped **per evaluation** rather than per state.

At the rule level, these two halves have different syntactic shapes:

| Half | Condition | Rule mechanism |
| --- | --- | --- |
| **Positive transport** | $\mathit{Fields}(\text{claim}) \subseteq \mathit{InvariantFields} \Rightarrow \text{transports}$ | Syntactic schema condition on the rule |
| **Non-transport (`W13`)** | $\mathit{Deleted}(\text{eval}) \cap \mathit{Refs}(\text{claim}) \neq \varnothing \Rightarrow \neg\,\text{transports}$ | No rule concludes a negative |

No rule in the judgment layer reads a claim's reference set to *conclude* that
something does not transport. Stating a positive rule that concludes
$\neg\,\text{transports}$ would require extending the assertion language with
explicit reference-set fields on every claim schema and adding negative-conclusion
rules.

## 2. Absence of derivation as the witness

Transport is already a derivability property: sequential composition composes
claims only when their syntactic schema conditions are satisfied. A claim
referencing a deleted generator fails that schema condition, so **no derivation
closes**. Non-transport is therefore witnessed structurally by the derivation
search failing to close—a machine-checkable, per-evaluation fact—without
needing a negative-conclusion rule.

In this respect, the negative half uses the exact same mechanism as the positive
half, observed in the opposite direction:

- Under a **procedural-only** reading, non-transport would be merely a policy
  statement documented on the `C-SEQUENCE` card (`Underivability`) and policed
  by manual review.
- Under a **negative-rule** reading, the assertion language would be extended
  with reference sets and negative-transport rules.
- Under the **absence-of-derivation** reading adopted by the calculus, the
  `Underivability` field documents a structural property of the rule system
  itself: the calculus declines to derive transported claims for deleted
  generators because the schema condition fails to fire.

## 3. Scope and limits of the refutation witness

Two boundaries govern how "the calculus refuses to derive" claims should be
read:

1. **Refutation, not a universal impossibility theorem.** Absence of derivation
   establishes *"no derivation closes for this evaluation in the current rule
   set"*, not *"no derivation can close under any future extension"*. A later
   release adding a new rule could close a gap that today's refutation reports.
2. **Decidability is instance-specific.** A failing search is a valid witness
   only when the search is guaranteed to terminate. Here it terminates because
   the schema conditions and finite field memberships are decidable, though
   termination must be argued for the concrete rule set rather than assumed in
   general.

The normative `W13` rules and their Lean mechanization are recorded in
[`spec/JUDGMENT_LAYER.md`](../spec/JUDGMENT_LAYER.md) and
[`lean/CodeCalculus/Transport.lean`](../lean/CodeCalculus/Transport.lean).
