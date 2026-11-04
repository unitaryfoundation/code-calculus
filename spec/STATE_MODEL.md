# State Model

**Status:** normative. What a state *is*, and which invariant governs each field.

This document is the authority for **what the state is**. It is unchanged by the
representation decision in [`REPRESENTATION.md`](REPRESENTATION.md), which fixes
how a state is written down rather than what it is.

---

## 1. The state

$$
C = (Q,\, X,\, Z,\, \mathsf{pres},\, \mathsf{used})
$$

| Field | Meaning |
| --- | --- |
| $Q$ | finite physical-qubit namespace |
| $X$ | $X$-type row space |
| $Z$ | $Z$-type row space |
| $\mathsf{pres}$ | the presentation: displayed generators, their identifiers, sector labels, and the qubit namespace |
| $\mathsf{used}$ | every identifier ever minted on this state — live ∪ retired |

**The row spaces live in $\mathbb{F}_2^Q$.** $X$ and $Z$ are subspaces of
$\mathbb{F}_2^Q$, and every displayed row $r$ has
$\mathrm{supp}(r)\subseteq Q$. This is typing, part of what makes the
state a code on $Q$: without it a row whose support leaves $Q$ satisfies every
invariant I1–I5 while its row space is not a subspace of $\mathbb{F}_2^Q$.

`used` is **semantic**, not provenance. It is read by the canonical mint, by
state equality, and by the direct-sum disjointness premise.

Everything the future $\Pi$ will carry — interfaces, support ownership,
boundaries, metrics, logical witnesses, certificates, constructor inputs,
inversion data — is **not MVP state data**. Consumer-supplied hypotheses for
conditional carry cells (minima, minimum-weight-class enumerations, exposure
minima) are **judgment inputs**, not state fields: they are not part of state
identity, not minted, and not transported by `used`.

The executable consumer's distance intervals, logical witnesses, target, and
decision (`certify`, `prune`, or `re-measure`) are also **ledger data**, separate
from $C$. They do not alter equality or the calculus state. The consumer checks
that a witness is currently logical; it does not validate a supplied lower
bound, exact price, or exhaustive enumeration claim.

## 2. Equality

$$
C_1 \equiv C_2 \iff Q_1 = Q_2 \;\wedge\; \text{identical labeled rows} \;\wedge\; \text{identical } \mathsf{used}.
$$

Three consequences that are easy to get wrong:

- **The namespace is part of identity.** Two well-formed states with the same
 labeled rows and the same `used` set on different namespaces are different
 codes: they differ in $n$, in $k$, and in which additions apply. They are
 not equal.
- **`used` is part of identity.** A state reached by a delete/add loop is *not*
 equal to its origin even when the row space is restored, because `used` grew.
- **Row order is not.** Displayed rows form finite **unordered** sets, and $Q$
 is a set. Two states differing only in row order, in the order $Q$ is
 written, or in matrix layout are equal.

## 3. The invariants

- **Derived property $w$.** The max stabilizer weight
 $w=\max\{\mathrm{wt}(r):r\in\mathit{rows}\}$ (0 if the display is empty) is a
 derived property of the display, not a state field: it is not minted, not part
 of identity, and not transported by `used`. It joins the property inventory
 (`spec/CLAIMS.md`) as an exact, carried property under every primitive.

- **Derived property $r$ (interaction radius).** The interaction radius
 $r=\max\{\mathrm{diam}_\lambda(s):s\in\mathit{rows}\}$ (0 if the display is
 empty) is a derived property of the display **relative to a layout**
 $\lambda$: the largest Euclidean diameter of a displayed row's support. Like
 $w$ it is not minted, not part of identity, and not transported by `used`;
 and like $w$ it is an exact, carried property under every primitive. It
 differs from $w$ in one respect: it is a function of the *pair* (state,
 layout), so a state with no layout has no radius. The layout is **ledger
 data** — supplied per code, held beside the state, not part of it — and not a
 $\Pi$ field, so admitting the radius does not change the state model or the
 equality relation.

- **Derived quantity $\kappa$ (Tanner components).** The number of connected
 components of the combined X+Z Tanner graph of the displayed rows is a derived
 property of the display, like $w$: computed, never minted, not part of
 identity, and not transported by `used`. It is carried exactly under every
 primitive. It is display-relative, so it is not part of the equality relation.
 See `spec/VOCABULARY.md`.

- **I1 — `WellFormedCSS`.** With $X=\langle \mathit{rows\_X}\rangle$ and
 $Z=\langle \mathit{rows\_Z}\rangle$: $X\perp Z$. Nontrivial $X\cap Z$ is
 permitted (`spec/VOCABULARY.md`, *Standard CSS state*).

 The span clause is definitional: the row space *is* the span of the display.
 It is not a property of the display that could be checked.

- **I2 — displayed independence.** Each displayed row is not in the span of the
 other displayed rows of its sector; equivalently the deletion precondition
 `Independent(r; pres)` holds for every displayed $r$.

- **I3 — identifier discipline.** `id` is injective on live rows, and an
 identifier of a retired row is **never reused**. Fresh identifiers are minted
 **canonically**: the first element of a fixed enumeration of the identifier
 namespace not in `used`. There is therefore **no fresh-name choice anywhere**,
 and every MVP primitive is deterministic outright.

 The fixed enumeration of the identifier namespace is, in order: seven blocks
 of 10000 identifiers each, named `a`, `b`, `c`, `d`, `e`, `p`, `q`
 (`a1`..`a10000`, then `b1`..`b10000`, and so on through `q1`..`q10000`).
 This enumeration is normative: `machine/priced_calculus.py` and
 `lean/CodeCalculus/State.lean` transcribe it, and any change to its order or
 block size is a release-level change.

- **I4 — sector typing.** Every displayed row carries exactly one sector label,
 matching the row space it spans.

- **I5 — `ValidProvenance`.** Provenance records are append-only and refer only
 to identifiers live or retired at the recorded step.

I1 and I2 are carried by the ranking arguments in
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §3 and by the
well-formedness obligation; I3 by the partial-inverse laws.

## 4. Update ownership

| Command | $Q$ | `rows_X` / `rows_Z` | `id` | `used` |
| --- | --- | --- | --- | --- |
| `C-SKIP` | — | — | — | appends a `skip` record |
| `C-DIRECT-SUM` | disjoint union | concatenate | plain union of disjoint id sets | union of summand sets |
| `C-DELETE-CHECK` | unchanged | remove $r$ | retire $r$ | **$r$ stays in `used`** |
| `C-ADD-CHECK` | unchanged | append $r$ | mint canonically | add the mint |
| `E-GRAFT` | remove $q$ | replace selected touching-row chain by adjacent products; shorten opposite-sector rows at $q$ | retire selected rows; mint products canonically | retain retired IDs and add minted IDs |
| `P-REBASE` | unchanged | replace the selected sector's display by $\mathrm{GL}(m,2)$ mixes; opposite sector untouched | retire selected rows; mint mixes canonically | retain retired IDs and add minted IDs |
| `E-LOCAL-HADAMARD` | unchanged | swap the sector label of every displayed row | none | unchanged |
| `E-PEEL` | remove $q$ | retire the unique selected row touching $q$; shorten opposite-sector rows at $q$ | retire the selected row | unchanged (retired ID retained) |
| `E-PUNCTURE` | remove $q$ | delete every displayed row touching $q$ in both sectors | retire deleted rows | unchanged (retired IDs retained) |
| `E-EXTEND` | add $\Delta$ | append canonically minted rows over $Q\cup\Delta$; factor rows unchanged | mint one identifier per addition | retain old used and add minted IDs |
| `E-GLUE` | union $Q_A\cup Q_B$ | factor rows followed by one minted row per admissible seam check | mint one identifier per seam check | union of the factors' used sets plus minted IDs |
| `C-SEQUENCE` | composed | composed | composed | union, in order |

`C-DIRECT-SUM` requires the summands' **qubit namespaces to be disjoint and
their `used` sets to be disjoint**; it unions both. Identifier collision makes
the constructor inapplicable exactly as qubit-namespace collision does.

The per-command cards, with their context-update rows, remain in
[`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §2.

## 5. Provenance is inert

`steps` records one entry per executed command — operation ID, affected
generator identifiers, identifiers minted or retired, and the bijection for
`P-RELABEL`. It is **read by nothing except `ValidProvenance`**: no `Eval`
premise and no judgment reads it.

That was correct for the original aim and remains correct here. A pipeline
records code ancestry itself; the calculus's obligation is only to be correct
about property propagation. Making `steps` load-bearing would be a different
project.

## 6. What this document does not do

It does not define how a state is written down — that is
[`REPRESENTATION.md`](REPRESENTATION.md). It does not define the commands
([`TERM_LANGUAGE.md`](TERM_LANGUAGE.md)) or the transition relation
([`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md)). It admits no
taxonomy-only operation and defines no future $\Pi$ *state* field; admitted
consumer-supplied judgment inputs are specified in
[`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2a.

It does not claim any invariant is *checked*. Under the MVP's assume-spanning
decision ([`REPRESENTATION.md`](REPRESENTATION.md) §5) an evaluator trusts I1's
span clause — definitional, so not checkable — and verifies I1's orthogonality
clause together with I2–I5.
