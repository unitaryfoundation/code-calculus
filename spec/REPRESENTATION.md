# Representation

**Status:** normative. This document fixes *how a code is concretely written
down*. It is the foundation for `machine/` and the executable evaluator, and
the premise on which the ranking arguments in
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §3 rest.

The abstract state model is unchanged and is stated in
[`STATE_MODEL.md`](STATE_MODEL.md).

---

## 1. The choice, and why

A code is a pair of **sparse supports** — lists of qubit indices — over a finite
index set. This is the representation already in production at
`qldpc-challenge`, where a code is

```json
"checks": {
 "X": [[0,4,5,7,8,9], [0,1,5,6,8,9], [1,2,5,6,7,9], ...],
 "Z": [[0,1,2,3,5,6], [1,2,3,4,6,7], ...]
}
```

Three reasons:

1. **It is readable by a person.** A stabilizer is the list of qubits it acts
 on: `[0,4,5,7,8,9]` says *exactly* what the operator is. A bitstring of the
 same row (`1000101111`) says the same thing and is read by nobody.
2. **It is already validated.** `qldpc-challenge` ships
 an archived internal note against this encoding and runs GF(2) helpers over
 it. Adopting it inherits a tested schema instead of inventing one.
3. **GF(2) arithmetic falls out of it.** Combination is symmetric difference of
 sets; membership and independence are rank questions over the incidence
 matrix the supports induce.

QECLean and LeanQEC represent stabilizers **symplectically**, as matrices. That
is Lean-idiomatic and is a reasonable *internal* implementation, but it is not
human-readable and is not the interface. **One external representation; the
representation a machine uses internally is its own business.** The
specification is backend-neutral.

## 2. The encoding

```json
{
 "Q": [0,1,2,3,4,5,6,7,8,9],
 "rows": [
 {"id": "a_1", "sector": "X", "support": [0,4,5,7,8,9]},
 {"id": "a_2", "sector": "X", "support": [0,1,5,6,8,9]},
 {"id": "b_1", "sector": "Z", "support": [0,1,2,3,5,6]}
 ],
 "used": ["a_1","a_2","b_1"]
}
```

| Element | Encodes | Rule |
| --- | --- | --- |
| `Q` | the qubit namespace | finite set of naturals; `n = \|Q\|` |
| `rows` | the display | unordered; each entry carries `id`, `sector`, `support` |
| `support` | one stabilizer | list of qubits, **strictly increasing**, no repeats, **every qubit in `Q`** |
| `used` | every identifier ever minted | live ∪ retired |

Three choices inside this are worth naming:

- **`Q` is an explicit set, not the range `0..n-1`.** `C-DIRECT-SUM` requires
 *disjoint* qubit namespaces, and explicit index sets let the constructor be a
 plain union with no relabelling: `A` on `{0..9}` and `B` on `{10..19}` give a
 code on `{0..19}` with A's supports and B's supports unchanged. A contiguous
 convention would force a reindexing step that the calculus does not have a
 command for.
- **Sector is a field, not an array position.** `qldpc-challenge` infers the
 sector from which list a check sits in. The calculus keeps it explicit
 ([`STATE_MODEL.md`](STATE_MODEL.md) I4) so that a malformed state is
 representable and can be *rejected*, rather than unrepresentable and silently
 coerced.
- **Rows are unordered.** State identity does not depend on row order or
 layout. Two encodings differing only in row order are the same state.

## 3. Derived, not stored

Three quantities the encoding may carry but the calculus does **not** treat as
state:

- **`n = |Q|`.** Computed from `Q`.
- **`k = n - dim(rows_X) - dim(rows_Z)`.** Computed by GF(2) rank over the
 display, where `dim` is the rank of the row space (I1 makes the display
 spanning, so rank of the display *is* rank of the row space).
- **`w = max{wt(r) : r in rows}`** (0 if the display is empty). Computed from
 the displayed rows as the maximum support size (weight) of a displayed check
 in either sector. Like `n` and `k`, it is a derived property, not a state
 field and not a declared value: it is not minted, not part of identity, and
 not transported by `used`. It joins the property inventory
 ([`CLAIMS.md`](CLAIMS.md)) as an exact, carried property under every
 primitive. The consumer-supplied minima
 `w_del`, `w_exp`, `w_re` are a different quantity and remain judgment inputs.
- **`r = max{diam_lambda(s) : s in rows}`** (0 if the display is empty), where
 `diam_lambda(s)` is the largest Euclidean distance between two points of a
 displayed row's support in a supplied layout `lambda`. It is a derived
 property of the display **relative to the layout**, in the same sense as `w`
 is a derived property of the display: computed, never stored, never a search.
 It joins the property inventory as an exact, carried property under every
 primitive. Unlike `n`, `k` and `w`, it
 is a function of the *pair* (state, layout), so a state with no layout has
 no radius; the layout is ledger data and is not carried by this encoding.

`qldpc-challenge` declares `n` and `k` as fields. In this encoding they are
**redundant declared values that must agree with the computed ones** — a
consistency check on import, not a source of truth. Disagreement is a malformed
input, and malformed input is one of the outcomes the evaluator reports, not a
value it adopts. `w` is not declared by the challenge encoding and is never
recomputed from anything but the display.

This matters for the deletion and addition laws. The `k` effects are recorded
`proved` on the basis of rank arithmetic over the display, which is only because
I1 makes the display spanning. The `w` effects are recorded `proved` on the
basis of the trivial max over the displayed rows: deletion can only lower or
preserve it, addition gives `max(old, added)`, direct sum gives
`max(w_A, w_B)`, and graft is computable from the post-graft display. See §5.

## 4. What the representation does not carry

- **Phases.** The model is phase-insensitive (FD1). A support is a binary row;
 $Y$-type behaviour arises from $X\cap Z\neq\varnothing$, never from an
 explicit phase.
- **Distance, and any metric.** `d_X`, `d_Z`, `d` are not state fields. Exact
 distance is a minimum-weight-codeword problem and is never silently
 recalculated by a transition. The consumer keeps a separate interval ledger
 and transports only the bounds licensed by
 [`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md): for example, an addition carries a
 lower bound while current logical witnesses are revalidated; an unpriced
 deletion resets the lower endpoint to zero and carries only surviving
 witnesses; a supplied, cited exact deletion price can tighten the interval
 conditionally. Input witnesses support upper bounds only. Exact-distance
 searches and lower-bound evidence are explicit external inputs, not part of
 the state or automatic transition semantics.
- **The future $\Pi$ fields.** Interfaces, boundaries, metrics, logical
 witnesses, certificates, constructor inputs, inversion data. None are MVP
 data ([`STATE_MODEL.md`](STATE_MODEL.md) §1).
- **The layout.** The geometric placement of the qubits is not carried by this
 encoding either, but for a different reason: it is **ledger data**, supplied
 per code and held beside the state, not a field of it. The interaction radius
 is read off the display *relative to* that ledger data
 ([`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2d), and two states differing only
 in their layout are the same state.

## 5. Spanning is assumed, not checked

**Decision:** an evaluator operating on this
representation **assumes** that the displayed rows span their row space, and
**does not** compute rank to verify it.

The basis is I1: `$X = ⟨rows_X⟩$` is *definitional* — the row space **is** the
span of the display, not a property of the display). Under that reading an independent-display check is not needed for
soundness, because there is no gap between "the display" and "the row space".

**The cost of the decision, stated.** The evaluator is sound **on spanning
displays**, and this is part of its contract. Handed a non-spanning
independent display, it will compute a `k` that does not correspond to a code
and will report transformations whose premises were decided against the wrong
row space. That is a silent wrong answer, not an error.

Checking is available — rank arithmetic over the incidence matrix is the same
computation the derivation uses — and would convert this from an assumption into
a precondition. It is **not** done in the MVP, because I1 makes it redundant and
because a redundant check costs time on every evaluation.

## 6. Well-formedness as a decidable predicate

I1–I5 become checks. `Independent` is I2; orthogonality is I1; identifier
discipline is I3; sector typing is I4; and every element of a `support` lies in
`Q` — the ambient containment of [`STATE_MODEL.md`](STATE_MODEL.md) §1. All are
decidable by finite GF(2) arithmetic over the incidence matrix, or by the
encoding itself.

A state failing any of them is **malformed** — rejected by the encoding alone,
with no evaluation attempted. This is one of the outcomes the fixture suite
already enumerates (`mvp_fixtures.json`, category `state-malformed`).

## 7. Formalization status: a Lean development exists, and it is not a certificate

**A Lean 4 development of the presented state exists, under `lean/`.** It
carries the state record, the canonical mint and its two theorems, the
presentation equality ≡, a list-level well-formedness predicate, the term
language, the transition relation with its derived denotation, and scoped
slices of the derivation layer. What it covers at a given date, the
hypotheses each theorem takes, and the trust basis it rests on are recorded
once, at [`../lean/README.md`](../lean/README.md); per-obligation progress is
recorded under *Intended mechanization status* in
[`OBLIGATIONS.md`](OBLIGATIONS.md). No artifact may describe a hand
derivation as mechanized because a Lean module exists: a theorem counts only
with its hypotheses stated.

The distinction is deliberate and load-bearing. The project's deliverable is the
runnable evaluator; a proof assistant formalizing the same semantics is a later
certificate. Recording the development's scope, rather than leaving its
status unstated, is what keeps a clean architecture from reading as a verified
one. The development is authorized work, and its substrate choice is recorded in
[`README.md`](../README.md).

This also fixes the standard the machine layer is written to: `machine/` is a
transcription of `spec/` precise enough that a formalization can be built from it
without re-deriving the semantics from prose. That standard holds whether or not
the formalization is built soon, because re-tightening a transcription after an
implementation exists costs more than getting it right first.

## 8. What this document does not do

It does not define the commands, the transition relation, or the judgments —
those are [`TERM_LANGUAGE.md`](TERM_LANGUAGE.md),
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) and
[`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md). It admits no operation of its own:
`P-REBASE` and the other Gate 6 commands are admitted by
[`TERM_LANGUAGE.md`](TERM_LANGUAGE.md) §2 and
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §2, not by this
document, which describes how a *displayed CSS state* is written down. The
obligation this presentation layer was said to defer
(`OBL-REBASE-GENERATION`) is discharged at [`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4.26.

It claims no soundness. It fixes an encoding, and the soundness theorem is owed.
