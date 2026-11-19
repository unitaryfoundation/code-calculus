# Scope and stopping point (updated 2026-10-19)

**Status:** maintainer decision record. Adopted 2026-10-11 (MathysRennela). This
note states the project's research question, its explicit stopping point, and the
obligation set that follows. It is **the canonical statement of scope**, and it
decides no gate and discharges no obligation.

**Role:** public design note. It does not state the calculus — that is
`spec/`, one authority per topic, adopted the same day under the
same decision. Where this note and `spec/` touch the same ground, `spec/` wins
and this one explains why.

**Relationship to other records.** This note does not modify any existing
artifact; it is standalone, and §7 lists what it bears on so the wiring can be
done deliberately rather than incidentally. Where it and a prior record differ,
this note is the later statement of scope and the earlier record is the
statement of detail.

---

## 1. The research question

**What is a sound calculus of code transformations?**

Concretely, an object with four parts:

1. **States** — a typed description of a code together with the presentation
   it carries, so that "which generator" is a well-formed question.
2. **Transformations as terms** — a typed term language whose closed terms denote
   transformation sequences, not a library of procedures.
3. **An operational semantics** — a partial big-step relation; absence of a
   derivation is part of the semantics, not a failure of it.
4. **A judgment layer** — for each property in the signature, and for each
   transformation, a determination of **whether that property carries, does not
   carry, or is not yet defined** — scoped per evaluation, not per state.

And the theorem that makes it a formal-methods artifact rather than a tool:

> **Soundness.** Every derivable judgment is true of the state or evaluation the
> term denotes.

The aim is not to compute distances. It is to make **which facts survive which
transformation, and what each step is permitted to assume**, a syntactic object
that can be checked rather than re-argued.

## 2. What "sound" means here, and why the calculus is deliberately incomplete

The calculus is **intended to be sound and deliberately incomplete**. This is a
design position, not an established result: a class of property is recorded
`unavailable` — withheld by design commitment — rather than left unstated or
silently omitted. The bar is that the calculus **never claims more than it can
back**. The named soundness obligations are discharged by dated hand derivation
in `spec/OPERATIONAL_SEMANTICS.md` §4;
soundness of the calculus as a machine-checked theorem is not established.

Incompleteness is the ordinary condition of formal verification, and the
discipline that makes it auditable is the contribution: `unavailable` is
distinguished from `false`, from `not derivable`, and from `not yet defined`,
per claim and in a stated scope. A calculus that quietly dropped what it could
not derive would be less useful and less honest.

**Consequence, stated plainly:** the calculus will not be complete, and no
artifact may describe it as aiming at completeness in the MVP. The
`unavailable` commitments are part of the design, not gaps awaiting closure.

## 3. Stopping point — in scope

| | |
| --- | --- |
| **Transformations** | the five kernel primitives, plus conditional cells for `C-DELETE-CHECK` with a supplied full-distance price, `E-GRAFT`, the `C-ADD-CHECK` judgment inputs (strict improvement under an exhaustive minimum-weight-class hypothesis; sector-aware gauging price; direct-sum extinction on a stack parent), and the Gate 6 CSS-level extensions admitted 2026-10-23 as conditional cells: `E-GLUE`, `E-PUNCTURE`, `E-PEEL`, patch growth/breeding (`E-EXTEND`), `E-LOCAL-HADAMARD`, and presentation rebasing. Each carries only when the consumer supplies the stated hypothesis; otherwise `unavailable`/`not yet defined`. The non-CSS extended-state layer remains out of scope |
| **Properties** | exactly those the property inventory carries: $n$, $k$, $d_X$, $d_Z$, $d$, $w$ (max stabilizer weight), $r$ (interaction radius, relative to a supplied layout), and Tanner connectivity of the displayed rows (issue #64 disposition 2026-10-23) |
| **Per cell** | for each (primitive or admitted construction move × property): **carries / does not carry / not yet defined / conditional**, scoped per evaluation; plus the `v0.3.0` conditional family-level one-shot level-map transport rule (`spec/JUDGMENT_LAYER.md` §2j, issue #541) |
| **Mechanization** | the hand derivations re-derived in a proof assistant, plus the soundness metatheorem |
| **Consumption** | the discovery-facing interface **built, not merely documented**: evaluator, interval ledger, certify/prune/re-measure loop, qLDPC adapter, and a consumer-side planner (in `machine/`, decided 2026-10-24). Supplied lower bounds, prices, and enumerations remain trusted inputs. |

**Family-level extension (2026-11-18, issue #541, `v0.3.0`).** The stopping point
is extended solely to admit a conditional family-level transport rule for
Yuan's one-shot hollowed-tensor level map (`spec/JUDGMENT_LAYER.md` §2j): $k' = k$
conditional on Lemma 118, $n$ inflated beyond $m \cdot n$ per tower level,
and the Theorem 81 / Remark 39 transport bound scoped as an **upper ceiling** on
RG failure probability. Family closure, family-level completeness, and amplified
distance lower bounds (`unavailable`) remain outside the scope.

**"Done" is:** every in-scope cell stated and transcribed; every in-scope
obligation discharged or proved not to hold; the consumer takes a target
decision from transported intervals whenever they suffice, and asks for
re-measurement only when they do not. Executing the transcription is not a proof
that the judgments are sound; the soundness obligations remain part of the
research deliverable.

**Price-provider boundary (2026-10-19).** `A-CONCAT` tower factorization is
admitted only as a source of deletion/exposure prices. It is not an `A-CONCAT`
state constructor or term production in this scope.

This is the project's **first and principal deliverable**. Later layers — Gate 6
extensions, Gate 7 constructors, family closure — are real work with real value,
but they are **not** this project's stopping point and are not owed by it.

## 4. Out of scope, with the reason

| Excluded | Reason |
| --- | --- |
| Non-CSS extended-state layer (`X-SYMPLECTIC-DOUBLE`/`HALVE`) and Gate 6 moves beyond the admitted CSS-level cells | the CSS-level subset is admitted as conditional cells (see §3); their sound admission is discharged under the stated hypotheses (`OBL-GATE6-CSS-EXTENSIONS`, §4.32, 2026-10-28), and they remain `unavailable`/`not yet defined` without consumer-supplied hypotheses. The extended-state layer is refused for `v0.3.0` (issue #545, 2026-11-18); the state model stays `C=(Q,X,Z,pres,used)` |
| Gate 7 constructors (`A-PRODUCT`, `L-`, `X-`) and family closure / completeness | same; since 2026-11-11 (issue #330) four constructors (`L-HGP`, `L-LIFTED`, `L-GROUP-ALGEBRA`, `A-CONCAT`) are admitted as `transition-defined` expression constructors under the v0.2 candidate, outside the stopping point and carrying no distance rule, since issue #369 the other five accepted constructors (`L-BALANCED`, `L-TANNER`, `L-TILE`, `A-PRODUCT`, `A-DOUBLE`) are admitted on the same terms, and `L-NESTED-CSS` since issue #445; since 2026-11-18 (issue #541) only the conditional family-level transport rule of `spec/JUDGMENT_LAYER.md` §2j enters `v0.3.0`, while general family closure / completeness and amplified distance lower bounds remain excluded |
| **Code lineage** | recorded by the **built** consumer, not by the calculus. The calculus's obligation is only to be correct about property propagation. |
| Certificates, `certificate-checked` | the consumer records conditional hypothesis sources, but does not validate exact prices or minimum-weight-class enumerations; verified per-state certificates remain outside this scope |
| Negative-space *investigation* | the reachability obligation stays **in** scope (§5) but its discharge is a later exercise, once the calculus exists to investigate |
| Discovery architecture, harness, search control | **now in scope**: the consumer is a deliverable, not a scenario. Learned budget allocation / decision models are **downstream** of the consumer, not part of the calculus or its consumer; see `an internal note` |
| A published novelty claim | see §6 |

## 5. The obligation set under this scope

The baseline count below records the original five-primitive scope:
**thirteen of seventeen attach to those primitives and are in scope; one is
discharged, twelve remain.** The 2026-10-19 construction-calculus decision adds
three open obligations (`OBL-GRAFT-TRANSITION-SOUNDNESS`,
`OBL-PRICED-INTERVAL-SOUNDNESS`, and `OBL-PRICED-INPUT-SEMANTICS`). Do not report
the baseline count as the full current obligation count. Four baseline
obligations remain deferred with the reasons recorded.

**In scope** — `SKIP-IDENTITY` *(discharged 2026-10-11)*, `JUDGMENT-SOUNDNESS`,
`WELL-FORMEDNESS-PRESERVATION`, `PRIMITIVE-DETERMINISM`,
`SEQUENCE-ASSOCIATIVITY`, `JUDGMENT-TRANSPORT`, `DIRECT-SUM-LAWS`, `FRAME-LAW`,
`ORDER-INDEPENDENT-DELETION` *(discharged, §4.15)*, `CROSS-SECTOR-PERMUTATION`,
`PARTIAL-INVERSE-LAWS`, `ROW-REPLACEMENT-FACTOR` *(discharged for the loop,
§4.16 and §4.18; its `P-REBASE` residual is `REBASE-GENERATION`, discharged
§4.26, below)*,
`FIXED-NAMESPACE-REACHABILITY` *(discharged, §4.17)*, and `OBL-GATE6-CSS-EXTENSIONS`
*(discharged 2026-10-28, §4.32; cells remain conditional)*.

**Out of scope** — `PRESENTATION-CONJUGATION` (attaches only to `P-RELABEL` /
`P-REBASE`, neither an MVP primitive); `DERIVED-TERM-FACTORIZATION` (future
derived commands); `CERTIFICATE-PATH-KEYING` (no MVP operation);
`REBASE-GENERATION` (minted 2026-10-11 on the split below; attaches to
`P-REBASE`, and its status is `not yet defined` rather than `open`).

**Decided 2026-10-11 — the straddle is split.** `ROW-REPLACEMENT-FACTOR` had
three claims of two polarities: two computable over the five primitives (the
delete/add loop applies and restores the row space; it is *not* a presentation
identity), and one quantifying over `P-REBASE`. The third is **not stateable** —
`P-REBASE` has no grammar production, so it has no cases to take cases of. It
is now `REBASE-GENERATION`, status `not yet defined`, deferred to the Gate 6
admission decision, taken 2026-10-23 (P-REBASE admitted as a conditional cell;
`REBASE-GENERATION` remains `not yet defined` pending its contract row).

The cut falls between *"core moves generate the basis-change group"* (a
statement about `C-DELETE-CHECK` / `C-ADD-CHECK`, retained) and *"therefore
`P-REBASE` does"* (a statement about `P-REBASE`, deferred). **The MVP half kept
the original obligation name**, so every one of its 28 existing citations remains
correct and none was rewritten. `REBASE-GENERATION` is `not yet defined`, not
`open`: there is nothing to evidence about a statement that cannot be written.

**Baseline in-scope count after the split: unchanged at thirteen, one discharged,
twelve remaining.** The later construction-calculus decision adds the three
open obligations listed above; it does not discharge or rewrite the baseline
obligations.

## 6. Two consequences worth recording

**The original in-scope count reframes progress.** Measured against all seventeen
obligations the project reads as barely begun — one discharged. Measured against
the thirteen the scope actually requires, it is roughly three-quarters built at
the design layer, with twelve proofs outstanding. The larger number was
measuring against obligations never in the frame. This is the historical
five-primitive baseline; the three issue #21 obligations were additional and
are discharged (`OBL-GRAFT-TRANSITION-SOUNDNESS` §4.12,
`OBL-PRICED-INTERVAL-SOUNDNESS` §4.13, `OBL-PRICED-INPUT-SEMANTICS` §4.14).

**As of 2026-10-11**, the research question's binding constraint was the
"does not carry" half of judgment transport; its disposition remains recorded
below. The 2026-10-19 scope change adds open obligations for graft transition
soundness, interval transport, and the semantics of trusted price inputs. The
consumer demonstrates a concrete use path but closes none of those obligations.

**Dispositioned 2026-10-11: the third is adopted** — *absence of derivation is
the witness*. The `W13` half needs no rule concluding a negative; a claim
referencing a deleted generator fails the schema condition, so no derivation
closes, and that is the machine-checkable witness. No release bump, and no gate
re-plan.

Two costs travel with it and are recorded in
`EXPRESSIBILITY.md`
§6: it **re-reads D2** (non-transport becomes a consequence of the logic's shape
where D2 recorded it as a registry commitment — weaker than reversing it, but
owed a dated note either way), and it establishes a **refutation, not a theorem**
— *no derivation closes*, not *no derivation can close*. A later release adding a
rule could close a gap that today's refutation reports, and no artifact may
imply otherwise. The decidability argument for the refutation's termination is
also owed.

This supersedes the F7 note's original Reading I recommendation, which rested on
the narrower aim recorded in §7 below.

## 7. What this bears on

Recorded for deliberate wiring, not edited by this note.

- The queue dispositions **D-2, D-4, D-5, D-7, D-8** are all Gate 6/7
  admissions and become *deferred by scope* — dispositions with a reason, rather
  than open rows implying work the scope does not owe. The queue itself is
  superseded: `an internal note`.
- **D-9** (required-citation rows) is bibliographic hygiene. Decided
  2026-11-14 (issue #442): not owed by a project whose deliverable is a
  calculus and a soundness theorem; citations stay inline at claims, and the
  `PRIOR_ART.md` §12 list remains a review aid rather than a release
  gate. No axis change.
- The statement of **aim** in the co-author briefing
  (`an internal note`)
  and in the proposal's framing describes one worked instance (distance bounds)
  of the general mechanism in §1. That is a faithful reading of what has been
  built, but it is narrower than the research question, and the difference should
  be made explicit rather than left for a reader to infer.
- The word **"lineage"** is used by `VOCABULARY.md` for model
  version history. The code-ancestry sense is the consumer's and is out of scope
  here, so no renaming is required — but the collision should stay flagged if the
  word is ever adopted.

**Wiring done 2026-10-11 (the same decision).** `spec/` now exists and is the
authority for the mechanics this scope describes; the proposal keeps its framing;
the co-author briefing and `MVP_CHEATSHEET.md` are archived as superseded by
[`README.md`](README.md) and `spec/`; `CONTEXT_FIELD_INVENTORY.md`,
`OPERATION_SEMANTICS.md` and `SEMANTIC_CONTRACT.md` are archived in favour of
`spec/STATE_MODEL.md`,
`spec/OPERATIONAL_SEMANTICS.md` and
`spec/CLAIMS.md`.

**Wiring updated 2026-10-20 (issue #24).** `w` (max stabilizer weight) joins the
property inventory as an exact, derived, carried property: `spec/STATE_MODEL.md`
§3 (derived property, not a state field), `spec/JUDGMENT_LAYER.md` §2 (carry
row), `spec/CLAIMS.md` (property inventory row), `spec/REPRESENTATION.md` §3
(derived, not stored), and `machine/priced_calculus.py` (`CodeState.w()`).
The consumer-supplied minima `w_del`, `w_exp`, `w_re` remain judgment inputs.

**Wiring updated 2026-10-22 (issue #62).** $r$ (interaction radius) joins the
property inventory as an exact, derived, carried property, on the `w` pattern
with one difference: it is derived *relative to a layout*, which is **ledger
data** -- supplied per code, held beside the state, not part of it -- so the
state model and the equality relation are unchanged. `spec/STATE_MODEL.md` 3,
`spec/JUDGMENT_LAYER.md` 2 (carry row) and 2d (the layout's evolution, the
honesty conditions, and the locality-class verdict), `spec/CLAIMS.md`
(inventory row), `spec/REPRESENTATION.md` 3 and 4,
`spec/OPERATIONAL_SEMANTICS.md` 4.19 (the dated derivation, including the
graft's factor-of-two bound), and `spec/VOCABULARY.md` (the terms *layout*,
*interaction radius*, *locality class*). The locality class is **not** a
property: it is a consumer-side verdict computed from the transported radius
against consumer-supplied caps.

**Wiring updated 2026-10-19.** The admission ladder is indexed in
[`ROADMAP.md`](ROADMAP.md), and the conditional `E-GRAFT` transition is
listed in `spec/CLAIMS.md` and
`spec/TAXONOMY.md`. Tower factorization is indexed only
as a price provider, not as a constructor.

## 8. What this note does not do

It decides no gate, discharges no obligation, and changes no claim status. It
does not claim the calculus is complete, sound, or mechanized — **none of those
is yet established**. The 2026-10-11 five-primitive baseline had one obligation
discharged and twelve remaining; the priced-construction decision adds three
open obligations, with no discharges.

It records the **stopping point**; individual dispositions and obligation
closures are recorded in the artifacts that carry them, not here. It does not
claim that the priced consumer or its challenge replay proves any theorem.
