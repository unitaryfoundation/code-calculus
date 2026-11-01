# Scope and stopping point

**Status:** maintainer decision record. This note is the canonical statement of
scope. It decides no gate and discharges no obligation.

**Role:** public scope note. The calculus itself is stated in `spec/`, one
authority per topic. Where this note and `spec/` touch the same ground, `spec/`
wins.

This note does not modify any existing artifact; it is standalone. Where it and
a prior record differ, this note is the later statement of scope and the
earlier record is the statement of detail.

## 1. The research question

**What is a sound calculus of code transformations?**

Concretely, an object with four parts:

1. **States** — a typed description of a code together with the presentation it
   carries, so that "which generator" is a well-formed question.
2. **Transformations as terms** — a typed term language whose closed terms denote
   transformation sequences, not a library of procedures.
3. **An operational semantics** — a partial big-step relation; absence of a
   derivation is part of the semantics, not a failure of it.
4. **A judgment layer** — for each property in the signature, and for each
   transformation, a determination of whether that property carries, does not
   carry, or is not yet defined, scoped per evaluation, not per state.

And the theorem that makes it a formal-methods artifact rather than a tool:

> **Soundness.** Every derivable judgment is true of the state or evaluation the
> term denotes.

The aim is not to compute distances. It is to make which facts survive which
transformation, and what each step is permitted to assume, a syntactic object
that can be checked rather than re-argued.

## 2. What "sound" means here, and why the calculus is deliberately incomplete

The calculus is intended to be sound and deliberately incomplete. This is a
design position, not an established result: a class of property is recorded
`unavailable` — withheld by design commitment — rather than left unstated or
silently omitted. The bar is that the calculus never claims more than it can
back. The named soundness obligations are discharged by dated hand derivation
in `spec/OPERATIONAL_SEMANTICS.md` §4; soundness of the calculus as a
machine-checked theorem is not established.

Incompleteness is the ordinary condition of formal verification. The discipline
that makes it auditable is the contribution: `unavailable` is distinguished from
`false`, from `not derivable`, and from `not yet defined`, per claim and in a
stated scope. A calculus that quietly dropped what it could not derive would be
less useful and less honest.

**Consequence, stated plainly:** the calculus will not be complete, and no
artifact may describe it as aiming at completeness in the MVP. The
`unavailable` commitments are part of the design, not gaps awaiting closure.

## 3. Stopping point — in scope

| | |
| --- | --- |
| **Transformations** | The five kernel primitives, plus conditional cells for `C-DELETE-CHECK` with a supplied full-distance price, `E-GRAFT`, the `C-ADD-CHECK` judgment inputs, and the Gate 6 CSS-level extensions admitted as conditional cells: `E-GLUE`, `E-PUNCTURE`, `E-PEEL`, patch growth/breeding (`E-EXTEND`), `E-LOCAL-HADAMARD`, and presentation rebasing. Each carries only when the consumer supplies the stated hypothesis; otherwise `unavailable` or `not yet defined`. The non-CSS extended-state layer remains out of scope. |
| **Properties** | Exactly those the property inventory carries: $n$, $k$, $d_X$, $d_Z$, $d$, $w$ (max stabilizer weight), $r$ (interaction radius, relative to a supplied layout), and Tanner connectivity of the displayed rows. |
| **Per cell** | For each (primitive or admitted construction move × property): carries / does not carry / not yet defined / conditional, scoped per evaluation. |
| **Mechanization** | The hand derivations re-derived in a proof assistant, plus the soundness metatheorem. |
| **Consumption** | The discovery-facing interface built, not merely documented: evaluator, interval ledger, certify/prune/re-measure loop, qLDPC adapter, and a consumer-side planner in `machine/`. Supplied lower bounds, prices, and enumerations remain trusted inputs. |

**"Done" is:** every in-scope cell stated and transcribed; every in-scope
obligation discharged or proved not to hold; the consumer takes a target
decision from transported intervals whenever they suffice, and asks for
re-measurement only when they do not. Executing the transcription is not a
proof that the judgments are sound; the soundness obligations remain part of the
research deliverable.

**Price-provider boundary.** `A-CONCAT` tower factorization is admitted only as
a source of deletion/exposure prices. It is not an `A-CONCAT` state constructor
or term production in this scope.

This is the project's first and principal deliverable. Later layers — Gate 6
extensions, Gate 7 constructors, family closure — are real work with real value,
but they are not this project's stopping point and are not owed by it.

## 4. Out of scope, with the reason

| Excluded | Reason |
| --- | --- |
| Non-CSS extended-state layer and Gate 6 moves beyond the admitted CSS-level cells | The CSS-level subset is admitted as conditional cells; their sound admission is discharged under the stated hypotheses, and they remain `unavailable` or `not yet defined` without consumer-supplied hypotheses. The extended-state layer needs its own scope decision. |
| Gate 7 constructors and family closure / completeness | Same. |
| Code lineage | Recorded by the built consumer, not by the calculus. The calculus's obligation is only to be correct about property propagation. |
| Certificates, `certificate-checked` | The consumer records conditional hypothesis sources, but does not validate exact prices or minimum-weight-class enumerations; verified per-state certificates remain outside this scope. |
| Negative-space investigation | The reachability obligation stays in scope, but its discharge is a later exercise, once the calculus exists to investigate. |
| Discovery architecture, harness, search control | Now in scope: the consumer is a deliverable, not a scenario. |
| A published novelty claim | See the consequences below. |

## 5. The obligation set under this scope

The baseline scope contains seventeen obligations: thirteen attach to the
five-primitive kernel and are in scope; one is discharged and twelve remain.
The priced-construction decision adds three open obligations:
`OBL-GRAFT-TRANSITION-SOUNDNESS`, `OBL-PRICED-INTERVAL-SOUNDNESS`, and
`OBL-PRICED-INPUT-SEMANTICS`. Do not report the baseline count as the full
current obligation count. Four baseline obligations remain deferred with the
reasons recorded.

**In scope:** `SKIP-IDENTITY` (discharged), `JUDGMENT-SOUNDNESS`,
`WELL-FORMEDNESS-PRESERVATION`, `PRIMITIVE-DETERMINISM`,
`SEQUENCE-ASSOCIATIVITY`, `JUDGMENT-TRANSPORT`, `DIRECT-SUM-LAWS`, `FRAME-LAW`,
`ORDER-INDEPENDENT-DELETION` (discharged), `CROSS-SECTOR-PERMUTATION`,
`PARTIAL-INVERSE-LAWS`, `ROW-REPLACEMENT-FACTOR` (discharged for the loop; its
`P-REBASE` residual is `REBASE-GENERATION`), `FIXED-NAMESPACE-REACHABILITY`
(discharged), and `OBL-GATE6-CSS-EXTENSIONS` (discharged; cells remain
conditional).

**Out of scope:** `PRESENTATION-CONJUGATION` (attaches only to `P-RELABEL` /
`P-REBASE`, neither an MVP primitive); `DERIVED-TERM-FACTORIZATION` (future
derived commands); `CERTIFICATE-PATH-KEYING` (no MVP operation);
`REBASE-GENERATION` (attaches to `P-REBASE`, and its status is `not yet
defined` rather than `open`).

**The straddle is split.** `ROW-REPLACEMENT-FACTOR` had three claims of two
polarities: two computable over the five primitives (the delete/add loop applies
and restores the row space; it is not a presentation identity), and one
quantifying over `P-REBASE`. The third is not stateable — `P-REBASE` has no
grammar production, so it has no cases to take cases of. It is now
`REBASE-GENERATION`, status `not yet defined`, deferred to the Gate 6 admission
decision (P-REBASE admitted as a conditional cell; `REBASE-GENERATION` remains
`not yet defined` pending its contract row).

The cut falls between "core moves generate the basis-change group" (a statement
about `C-DELETE-CHECK` / `C-ADD-CHECK`, retained) and "therefore `P-REBASE`
does" (a statement about `P-REBASE`, deferred). The MVP half kept the original
obligation name, so existing citations remain correct. `REBASE-GENERATION` is
`not yet defined`, not `open`: there is nothing to evidence about a statement
that cannot be written.

## 6. Consequences

Measured against all seventeen obligations, the project reads as barely begun:
one discharged. Measured against the thirteen the scope actually requires, it is
roughly three-quarters built at the design layer, with twelve proofs
outstanding. The larger number was measuring against obligations never in the
frame. This is the historical five-primitive baseline; the three priced
obligations were additional and are discharged.

The research question's binding constraint was the "does not carry" half of
judgment transport. The third option is adopted: absence of derivation is the
witness. The `W13` half needs no rule concluding a negative; a claim
referencing a deleted generator fails the schema condition, so no derivation
closes, and that is the machine-checkable witness. No release bump, and no gate
re-plan.

Two costs travel with it: it re-reads D2 (non-transport becomes a consequence
of the logic's shape where D2 recorded it as a registry commitment — weaker
than reversing it, but owed a dated note either way), and it establishes a
refutation, not a theorem — no derivation closes, not no derivation can close.
A later release adding a rule could close a gap that today's refutation reports,
and no artifact may imply otherwise. The decidability argument for the
refutation's termination is also owed.

This supersedes the F7 note's original Reading I recommendation, which rested
on the narrower aim recorded above.

## 7. Related records

- `spec/` is the authority for the mechanics this scope describes; the proposal
  keeps its framing.
- Earlier planning notes and cheat sheets are archived or superseded by
  `README.md` and `spec/`.
- Earlier context-field and operation-semantics notes are superseded in favour of
  `spec/STATE_MODEL.md`, `spec/OPERATIONAL_SEMANTICS.md`, and
  `spec/CLAIMS.md`.
- The word "lineage" is used by `spec/VOCABULARY.md` for model version history.
  The code-ancestry sense is the consumer's and is out of scope here, so no
  renaming is required, but the collision should stay flagged if the word is ever
  adopted.

## 8. What this note does not do

It decides no gate, discharges no obligation, and changes no claim status. It
does not claim the calculus is complete, sound, or mechanized — none of those
is yet established. The baseline scope had one obligation discharged and twelve
remaining; the priced-construction decision adds three open obligations, with no
discharges.

It records the stopping point; individual dispositions and obligation closures
are recorded in the artifacts that carry them, not here. It does not claim that
the priced consumer or its challenge replay proves any theorem.
