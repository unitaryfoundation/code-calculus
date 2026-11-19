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

**Logical-witness field (future-$\Pi$, defined 2026-11-11, issue #332).**
The field is a finite set $\mathsf{log}\subseteq \mathcal{P}(Q)\times\{X,Z\}
\times \{\pm 1\}$ of *logical representatives*: each entry is a support
$S\subseteq Q$, a sector $\sigma$, and an eigenvalue $\varepsilon\in\{\pm1\}$,
such that $S$ commutes with every row of the opposite sector and is not in
the same-sector span (i.e. $S$ is a logical of sector $\sigma$ in the sense
of `JUDGMENT_LAYER.md` §2c), with at most one representative per logical
class. It is **not** added to $C=(Q,X,Z,\mathsf{pres},\mathsf{used})$: it
remains future-$\Pi$ data, outside MVP state identity, not minted, and not
read by equality or by any kernel transition. Its role is to carry, under
`E-GLUE`, the survival statement of §4.31: a factor representative
$(S,\sigma,\varepsilon)$ survives the seam iff $S$ commutes with every $X$
seam check (when $\sigma=Z$) or every $Z$ seam check (when $\sigma=X$) and
is not absorbed into the glued same-sector span; surviving representatives
are the glued code's logicals, and the equality
$d_\sigma(Q)=\min(d_\sigma(C_A),d_\sigma(C_B))$ holds for sector $\sigma$
exactly when a representative of weight $\min(d_\sigma(C_A),d_\sigma(C_B))$
survives. The field's transport under `E-GLUE` is therefore survival of
factor representatives across the seam, which is the content Theorem 4 /
claim 7.4 of *composition-distance* records. The field does not enter the
consumer. It is mechanized as a definition outside `CodeState`, with its
`E-GLUE` transport, in `lean/CodeCalculus/LogicalWitness.lean` (issue #439):
the transported field is the set of factor representatives that survive, it
is sound, and for factor fields that hold a least-weight representative of
every class the equality of sector $\sigma$ holds exactly when the
transported field holds a representative of weight
$\min(d_\sigma(C_A),d_\sigma(C_B))$. The transport does not preserve the
condition of at most one representative per class: two surviving factor
representatives can represent one class of the glued state
(`glueLog_not_onePerClass`), so a transport that keeps the condition must
also discard duplicates. The transport of §1a does, and the definition of
§1a supersedes this paragraph as the definition of the field (issue #440).

**Boundary/edge-label field (future-$\Pi$, defined 2026-11-12, issue #366).**
The field is a finite set $\mathsf{bd}\subseteq \mathcal{P}(Q)\times
\{X,Z\}\times \mathbb{N}$ of *boundary supports*: each entry is a support
$S\subseteq Q$ (a boundary segment), a sector $\sigma$, and an index $i$
naming a logical operator of sector $\sigma$ whose support is carried by $S$,
with at most one entry per (segment, sector, operator) and with segments
partitioning the boundary of the patch. A segment may carry labels in both
sectors (the Steane edge supports both $\overline{X}$ and $\overline{Z}$),
and the index is required once a patch has $k>1$. It is **not** added to
$C=(Q,X,Z,\mathsf{pres},\mathsf{used})$: it remains future-$\Pi$ data,
outside MVP state identity, not minted, and not read by equality or by any
kernel transition. Its role is to type the geometric uses of moves such as
`E-LOCAL-HADAMARD` (conjugating along a boundary edge exchanges the sector
component of each label that edge supports) and to gate multi-port merges
through the edge-count conditions of `TAXONOMY.md` §2.10. Under `E-GLUE`,
a factor label $(S,\sigma,i)$ is carried unchanged when $S\subseteq Q_A$
or $S\subseteq Q_B$ (segments contained in a factor); a segment meeting the
seam is refined by the seam checks, and a label crosses the seam only when
the logical representative it names survives it, so boundary transport is
the restriction of the logical-witness survival statement of §4.31 to
boundary supports and the two fields are coupled. `E-LOCAL-HADAMARD` applied
along an edge exchanges the sector component of every label on that edge.
The field does not enter the consumer. The definition of §1a supersedes
this paragraph as the definition of the field (issue #440). It differs
from the sketch in three places, each stated there: a label stores a
representative, the partition of the boundary is replaced by a condition
on segments, and a factor label is carried under `E-GLUE` only when its
representative survives.

The executable consumer's distance intervals, logical witnesses, target, and
decision (`certify`, `prune`, or `re-measure`) are also **ledger data**, separate
from $C$. They do not alter equality or the calculus state. The consumer checks
that a witness is currently logical; it does not validate a supplied lower
bound, exact price, or exhaustive enumeration claim.

## 1a. The logical-witness and boundary-label fields: definition and transport

Defined 2026-11-13 (issue #440). Both fields are future-$\Pi$ data. They are
not part of $C=(Q,X,Z,\mathsf{pres},\mathsf{used})$, not read by equality,
not minted, and not read by any transition or judgment rule, and the
consumer does not carry them. This section fixes what each field is, when
it is well formed on a state, and how it is transported along every
admitted transition. Admitting either field as state data would change
state identity and is not done here.

**Further future-$\Pi$ fields (issue #453).** No additional field beyond the
logical-witness field above and the boundary/edge-label field (#366) is
admitted as state data. Any further field is sketch refinement only (a
minor, axis-3 change) unless a use and a dated maintainer decision admit it
as state data, which would be a new calculus line (major). This disposition
is recorded at `design/ROADMAP.md` and
`diary/2026-11-14-admit-v030-candidate-constructors-judgments-issues-446-453.md`.

**Notation.** Fix a state $C$ with qubit set $Q$, a sector $\sigma$, and
the other sector $\tau$. A *$\sigma$-vector* is a subset of $Q$ read as a
product of $\sigma$ operators. It is a *$\sigma$-logical* of $C$ when it has
even overlap with every displayed $\tau$-row and lies outside the span of
the displayed $\sigma$-rows ([`JUDGMENT_LAYER.md`](JUDGMENT_LAYER.md) §2c).
Two $\sigma$-vectors are in the same *class* of $C$ when their sum lies in
the span of the displayed $\sigma$-rows.

**The logical-witness field.** A *representative* is a triple
$(v,\sigma,\varepsilon)$ of a $\sigma$-vector $v$, a sector $\sigma$, and an
eigenvalue $\varepsilon\in\{\pm1\}$. The field $\mathsf{log}$ is a finite
list of representatives. It is *well formed* on $C$ when

- **(W1)** every entry $(v,\sigma,\varepsilon)$ has $v$ a $\sigma$-logical of
  $C$, and
- **(W2)** no two entries of one sector are in the same class of $C$.

Two further properties are named and are not required. The field is
*complete* in $\sigma$ when every class of $\sigma$-logicals of $C$ has an
entry, and *tight* when every entry has the least weight of its class. The
order of the list is used only to break ties in the transport. The
eigenvalue is carried and is read by nothing in this section.

**Transport of the logical-witness field.** A transition to a child state
$C'$ supplies a list of *candidates*, representatives on the qubits of
$C'$, by the table below. The transported field is obtained in two steps.
First, the candidates that are not logicals of $C'$ are discarded. Second,
of the remaining candidates one of least weight is kept for each class of
$C'$, the earliest in the list among those of equal weight. For every list
of candidates:

1. the transported field is well formed on $C'$, and
2. every candidate that is a logical of $C'$ has an entry of its class in
   the transported field, of no larger weight.

So the transport loses no class that a candidate represents and no minimum
weight among the candidates. It does not preserve completeness or
tightness: the child can have a class that no candidate represents, and a
class can have a representative lighter than every candidate. Both
statements are machine-checked for arbitrary candidates
(`transportLog_sound`, `transportLog_onePerClass`, `transportLog_keeps` in
`lean/CodeCalculus/WitnessFields.lean`).

**Candidates per transition.** Where the last column gives no derivation,
nothing is claimed beyond statements 1 and 2.

| Transition | Candidates | What is derived |
| --- | --- | --- |
| `C-SKIP` | the entries of the field | the field is unchanged |
| `C-DELETE-CHECK` | the entries of the field | the field is unchanged, by (a) below; it is not complete afterwards, since the child has one more logical qubit |
| `C-ADD-CHECK`, added row $r$ | the entries of the field | an entry of the sector of $r$ survives when it stays outside the enlarged span, an entry of the other sector when it has even overlap with $r$; two entries whose sum is $r$ modulo the old span merge into the lighter |
| `C-DIRECT-SUM` | the entries of both fields, extended by zero | every entry survives and no two merge, by (b) below |
| `C-SEQUENCE` | by composition | by composition |
| `P-REBASE` | the entries of the field | the field is unchanged: the spans of both sectors are unchanged |
| `E-LOCAL-HADAMARD`, $T=Q$ | the entries of the field with the sector exchanged | every entry survives and no two merge: the two row spans are exchanged with the sectors |
| `E-LOCAL-HADAMARD`, $T=\varnothing$ | the entries of the field | the field is unchanged |
| `E-GLUE` | the entries of both fields, extended by zero | the survival criterion of [`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4.31; machine-checked as stated below |
| `E-EXTEND` | the entries of the field, extended by zero on the added qubits | none |
| `E-PEEL`, `E-PUNCTURE`, `E-GRAFT`, removed qubit $q$ | the entries whose vector does not contain $q$, on the remaining qubits | none; an entry whose vector contains $q$ is not a candidate |
| every typed constructor | none | the field of a constructed state is empty |

(a) *Deletion.* Deleting a displayed row of sector $\rho$ leaves the span
of the other sector unchanged and makes the span of sector $\rho$ smaller.
A $\rho$-logical of the parent still has even overlap with every displayed
row of the other sector and still lies outside the span of the displayed
$\rho$-rows. A logical of the other sector has one constraint fewer to meet
and its span is unchanged. Two vectors whose sum lay outside a span have
their sum outside a smaller span. So every entry survives and the classes
of the entries stay distinct. ∎

(b) *Direct sum.* The direct sum is the `E-GLUE` state with no seam check.
By Claim 2 of [`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §4.33
with no seam check, the classes of the sum are the pairs of factor classes,
none is absorbed, and an entry of a factor extended by zero represents the
pair of its class and the zero class. Distinct nonzero pairs are distinct
classes. ∎

The derivations (a) and (b) and the rows for `C-SKIP`, `P-REBASE`, and
`E-LOCAL-HADAMARD` are hand derivations and are not machine-checked. For
`E-GLUE` the instance is `glueField`. For well-formed factor fields it
holds an entry of weight $\min(d_\sigma(C_A),d_\sigma(C_B))$ exactly when
some surviving factor entry has that weight
(`carriesMin_glueField_iff`), so the statements of
`lean/CodeCalculus/LogicalWitness.lean` about the equality
$d_\sigma(C)=\min(d_\sigma(C_A),d_\sigma(C_B))$ hold for this transport.

**The boundary-label field.** A *label* is a triple $(S,\rho,i)$ of a
*segment* $S\subseteq Q$, a representative $\rho=(v,\sigma,\varepsilon)$,
and an index $i\in\mathbb{N}$. The field $\mathsf{bd}$ is a finite list of
labels. It is well formed on $C$ when

- **(B1)** for every label the vector $v$ of its representative is a
  $\sigma$-logical of $C$ and $v\subseteq S$, and
- **(B2)** any two segments are equal or disjoint.

The triple $(S,\sigma,i)$ of the 2026-11-12 sketch is the segment, the
sector of the representative, and the index. The representative is added
because an index alone names no class of $C$, and because the sketch's
condition that the segment carries the operator is the existence of a
representative of its class inside the segment, which the label now
stores. The sketch's condition that the segments partition the boundary of
the patch is not expressible, since a state has no geometry. (B2) replaces
it, and the boundary is read as the union of the segments. A segment may
carry labels of both sectors. The index is a name: no rule relates it to a
position in $\mathsf{log}$, and uniqueness of the label for a given
segment, sector, and index is not required here.

**Transport of the boundary-label field.** A transition supplies candidate
labels as it supplies candidate representatives: the segment and the
vector of the representative are carried by the same map on qubits
(unchanged, extended by zero, or restricted to the remaining qubits, with
a label whose representative contains a removed qubit not a candidate),
and `E-LOCAL-HADAMARD` with $T=Q$ exchanges the sector of every
representative. The transported field is the list of candidates that
satisfy (B1) on $C'$. It satisfies (B1) by construction. It satisfies (B2)
for every transition of the table, since each map on qubits sends equal
segments to equal segments and disjoint segments to disjoint segments.

*Coupling.* Every transported label names a class that the logical-witness
field transported from the labels' representatives also holds, with an
entry no heavier than the label's representative
(`transportBd_names_class`). Under `E-GLUE` a factor label is transported
exactly when its representative survives the seam
(`bdLabel_extendA_valid_iff`, `bdLabel_extendB_valid_iff`). The sketch says
a label whose segment lies in one factor is carried unchanged. Factor
namespaces are disjoint, so every factor segment lies in one factor, and
the reading fixed here is that such a label is carried only when its
representative survives.

**What is not defined.** A refinement of a segment by seam checks: no
operation here splits a segment. The edge-count conditions of
[`TAXONOMY.md`](TAXONOMY.md) §2.10 for multi-port merges: they need a
count of segments per port, and no port is defined. Any reading of the
eigenvalue. Any rule that reads either field. Candidates for a logical
that contains a removed qubit, which would need a choice of equivalent
representative avoiding the qubit.

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
 block size is a release-level change. Because it is finite, minting is
 partial: a command that would mint when every identifier is already in
 `used` is inapplicable (the capacity premise of the minting cards,
 [`OPERATIONAL_SEMANTICS.md`](OPERATIONAL_SEMANTICS.md) §2; H-4, decided
 2026-10-31, carried by `machine/` and, since 2026-11-11, by `lean/`).

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
| `L-HGP` | fresh $\{0,\ldots,n-1\}$, $n=n_1n_2+m_1m_2$ | the retained display of the natural product rows (§4.34) | mint canonically from the empty used set, $X$-rows first | the minted IDs |
| `L-LIFTED` | fresh, $n=|G|(n_An_B+m_Am_B)$ | the retained display of the lifted product rows | mint canonically from the empty used set | the minted IDs |
| `L-GROUP-ALGEBRA` | fresh, $n=2|G|$ | the retained display of the two-block rows | mint canonically from the empty used set | the minted IDs |
| `A-CONCAT` | fresh, $n=n_{\mathrm{in}}n_{\mathrm{out}}$ | the inner rows on every copy, then the lifted outer rows (nothing dropped) | mint canonically from the empty used set | the minted IDs |
| `A-PRODUCT` | fresh, $n=m_Z^Am_X^B+n_An_B+m_X^Am_Z^B$ | the retained display of the tensor-product rows (§4.35) | mint canonically from the empty used set | the minted IDs |
| `A-DOUBLE` | fresh, $n=2n_C$ | the retained display of the two lifts of each displayed row | mint canonically from the empty used set | the minted IDs |
| `L-BALANCED` | fresh, one label per orbit | the retained display of the descended product rows | mint canonically from the empty used set | the minted IDs |
| `L-TANNER` | fresh, the supplied $n$ | the retained display of the local rows at every vertex | mint canonically from the empty used set | the minted IDs |
| `L-TILE` | fresh, one label per site class | the retained display of the placed tile rows | mint canonically from the empty used set | the minted IDs |
| `L-NESTED-CSS` | fresh, one label per column | the retained display of the rows of the two parity-check matrices (§4.36) | mint canonically from the empty used set, $X$-rows first | the minted IDs |
| `L-EMPTY` | $\varnothing$ | empty (`rows = []`) | none | $\varnothing$ |
| `L-FREE` | the supplied finite $Q \subset \mathbb{N}$ (sorted) | empty (`rows = []`) | none | $\varnothing$ |
| `A-PULLBACK` | fresh $0,\ldots,n-1$, $n=|Q_1\times_{Q_I} Q_2|$ | the retained display of the pulled-back rows of $C_1$ then $C_2$ (§4.43) | mint canonically from the empty used set | the minted IDs |
| `A-PUSHOUT` | fresh $0,\ldots,n-1$, $n=|Q_1\sqcup_{Q_S} Q_2|$ | the retained display of the pushed-forward rows of $C_1$ then $C_2$ (§4.43) | mint canonically from the empty used set | the minted IDs |
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
