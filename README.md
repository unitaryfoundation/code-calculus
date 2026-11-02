# code-calculus

[![Supported By-Unitary Foundation](https://img.shields.io/badge/Supported%20By-Unitary%20Foundation-FFFF00.svg)](https://unitary.foundation)
[![License](https://img.shields.io/github/license/unitaryfoundation/code-calculus.svg)](https://github.com/unitaryfoundation/code-calculus/blob/main/LICENSE)
[![Validation](https://github.com/unitaryfoundation/code-calculus/actions/workflows/ci.yml/badge.svg)](https://github.com/unitaryfoundation/code-calculus/actions/workflows/ci.yml)
[![Lean](https://github.com/unitaryfoundation/code-calculus/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/unitaryfoundation/code-calculus/actions/workflows/lean_action_ci.yml)
[![Contributor Covenant](https://img.shields.io/badge/Contributor%20Covenant-2.1-4baaaa.svg)](https://github.com/unitaryfoundation/code-calculus/blob/main/CODE_OF_CONDUCT.md)

> A formal calculus of transformations on CSS quantum error-correcting codes.

**code-calculus** is a research artifact (Apache 2.0) that treats code
transformations as a typed language rather than as a library of procedures. It
specifies:

- a **state model** for a presented CSS code,
- a **term language** whose closed terms denote transformation sequences,
- a **partial operational semantics** (absence of a derivation is part of the
  semantics, not a failure),
- a **judgment layer** that records, for each property and each transformation,
  whether that property carries, does not carry, is not yet defined, or is
  deliberately withheld (`unavailable`).

Alongside the specification there is an executable consumer
(`machine/priced_calculus.py`) that propagates distance **intervals** through
construction steps and asks for re-measurement only when the current bounds
cannot decide a target. It is evidence about whether the interface is useful; it
does not establish the calculus's soundness theorem.

**Status.** Gate 0 and Gate 1 are ratified; Gates 2–7 are unchecked. The
calculus is intended to be sound and deliberately incomplete. No soundness
claim is machine-proved in full: the named obligations have dated hand
derivations in `spec/OPERATIONAL_SEMANTICS.md` §4, and the Lean development
under `lean/` is partial. See `SCOPE.md` and `spec/GATES.md`.

---

## What is a CSS code?

A **CSS (Calderbank–Shor–Steane) code** is a quantum error-correcting code
defined by two families of commuting Pauli checks, one **X-type** and one
**Z-type**, acting on a finite set of physical qubits. Its headline parameters
are:

- **n** — number of physical qubits,
- **k** — number of logical qubits (`k = n − rank(X) − rank(Z)`),
- **d** — distance, the minimum weight of a logical operator (and its
  X/Z-sector variants `d_X`, `d_Z`).

The calculus is **phase-insensitive**: it records supports and row spaces, not
stabilizer phases. It also tracks derived, display-relative quantities such as
the maximum stabilizer weight **w**, the interaction radius **r** (relative to a
supplied layout), and Tanner connectivity of the displayed rows. Distance is
never a state field and is never silently recomputed by a transition — see
[Distance is opaque](#distance-is-opaque).

## Why this exists

The aim is not to compute distances. It is to make two things **syntactic
objects that can be checked rather than re-argued**:

1. **which facts survive which transformation** (and which do not), and
2. **what each step is permitted to assume**.

In particular the calculus distinguishes four different kinds of "no": a
proposition can be **false**, **not derivable**, **unavailable** (withheld by
design commitment), or **not yet defined** (outside the current assertion
language). Collapsing these is the usual source of overclaim in code-construction
work, and the calculus refuses to do it.

## A first look

A state is a presented CSS code:

```json
{
 "Q": [0,1,2,3,4,5,6,7,8,9],
 "rows": [
   {"id": "a_1", "sector": "X", "support": [0,4,5,7,8,9]},
   {"id": "a_2", "sector": "X", "support": [0,1,5,6,8,9]},
   {"id": "b_1", "sector": "Z", "support": [0,1,2,3,5,6]}
 ],
 "used": ["a_1", "a_2", "b_1"]
}
```

`Q` is the qubit namespace; `rows` is the displayed generator set (unordered);
`used` is every identifier ever minted on this state. The row spaces `X` and
`Z` are the spans of the displayed rows. See `spec/REPRESENTATION.md`.

A transformation is a term, not a procedure. The grammar has two categories:

```
e ::= S | e₁ ⊕ e₂            (state expressions)
m ::= skip | delete_r | addStab_r | graft(q, τ; [r₁,…]) | … | m₁ ; m₂
```

A **closed construction term** is `m ▷ e`: evaluate the state expression `e`,
then execute command `m`. For example

```
(delete_a ; addStab_b) ▷ S
```

deletes generator `a` and then adds generator `b`. `C-DIRECT-SUM` (`⊕`) is an
expression constructor, not a command: it combines two already-formed codes on
disjoint qubit namespaces.

Three outcomes are kept distinct, and the fixture suite keeps them distinct:

- **malformed** — rejected by the grammar or the encoding alone;
- **no derivation** — a well-typed term whose premises do not hold for this
  state (e.g. `delete_a ▷ S` when `a` is not displayed in `S`). This is not
  an error; absence of a derivation is part of the semantics;
- **a result state** — the term evaluates.

## Core concepts

### State

A state is `C = (Q, X, Z, pres, used)`:

| Field | Meaning |
| --- | --- |
| `Q` | finite physical-qubit namespace |
| `X`, `Z` | X- and Z-type row spaces (`X⊥Z`) |
| `pres` | the presentation: displayed generators, identifiers, sector labels |
| `used` | every identifier ever minted (live ∪ retired) |

`used` is **semantic**, not provenance: it participates in state equality and in
the canonical mint. Two states with the same rows but different `used` sets are
different states. Rows are unordered; row order is not identity. See
`spec/STATE_MODEL.md`.

### Operational semantics

The semantics is a **partial big-step relation** `Eval(m, e) = C'`. It is
partial by design: a term with no applicable rule simply has no derivation.
Evaluation contexts (holes) are absent because the relation evaluates closed
terms directly. The rules for the kernel and the in-scope construction moves are
in `spec/OPERATIONAL_SEMANTICS.md` §2.

### Judgment layer

For each property and each transformation, the calculus records one of
**carries**, **does not carry**, **not yet defined**, or **unavailable**, scoped
per evaluation. The carry table for the five kernel primitives:

| Property | `C-SKIP` | `C-DIRECT-SUM` | `C-DELETE-CHECK` | `C-ADD-CHECK` | `C-SEQUENCE` |
| --- | --- | --- | --- | --- | --- |
| `n` | carries, `n'=n` | `n = n_A+n_B` | carries | carries | carries |
| `k` | carries | `k = k_A+k_B` | `k'=k+1` | `k'=k-1` | carries |
| `w` (max weight) | carries | `max(w_A,w_B)` | `≤ w` (exact) | `max(w, wt(r))` | carries |
| Tanner connectivity | carries | always disconnected | can drop | cannot drop | composition |
| `r` (radius) | carries | `max(r_A,r_B)` | `≤ r` (exact) | `max(...)` | composition |
| `d_X`, `d_Z`, `d` | carries | `min` of factors | upper bound `≤`; exact unavailable | lower bound; strict improvement conditional | composition (open) |

`C-DIRECT-SUM` is exact but **terminal for connected codes**: the two blocks
share no qubit, so the Tanner graph is disconnected and no calculus move
reconnects them.

Three claims do not carry unconditionally:

| Claim | Status | Why |
| --- | --- | --- |
| A claim referencing a **deleted generator** | `unavailable` | judgment transport is per-evaluation, not per-state (`W13`) |
| A **row-referencing certificate** through delete→add | `unavailable` | information-losing at the context level, even when the row space is restored |
| **Strict improvement** of distance under addition | `conditional` | carries `d' ≥ d+1` only with a supplied minimum-weight-class enumeration |

Everything outside the table (certificates, interface/metric/logical-witness
judgments, support-sensitive predicates under rebasing, circuit/DEM/realization
predicates) is **not yet defined**. See `spec/JUDGMENT_LAYER.md`.

### Distance is opaque

`d_X`, `d_Z`, `d` are **not** state fields and **not** functions of the row
space. No rule computes an exact distance from a state update; exact distance is
a minimum-weight-codeword problem. Transitions transport only the bounds the
semantics licenses (for example, deletion gives an upper bound; unpriced
deletion resets the lower endpoint to 0). Input witnesses support upper bounds
only. This is a ratified design position (`spec/VOCABULARY.md`, *Opaque
distance term*), not an implementation gap.

### Priced construction moves

Beyond the five kernel primitives, the calculus admits **conditional cells** that
carry only when the consumer supplies a stated hypothesis:

| Move | Carries when | Hypothesis (consumer-supplied) |
| --- | --- | --- |
| `C-DELETE-CHECK` (priced) | exact `d' = min(d, w_del, w_exp)` | minima `w_del`, `w_exp` over promoted/exposed sets |
| `E-GRAFT` | sector-wise bounds | exposure minimum in the non-spliced sector + coverage condition |
| `C-ADD-CHECK` (strict improvement) | `d' ≥ d+1` | exact old `d` + exhaustive minimum-weight-class enumeration |
| `C-ADD-CHECK` (sector gauging) | raised sector lower bound | sector minima `w_X`, `w_Z` |
| `C-ADD-CHECK` (direct-sum extinction) | `d' = d_B` | trusted factor distance `d_B` + structural side conditions |
| `E-GRAFT` (radius) | exact radius | none — radius is computable |
| `A-CONCAT` towers | deletion/exposure price input | tower structure; price provider, not a constructor |

Without the hypothesis the corresponding cell is `unavailable`, not a guess. The
consumer checks that inputs are present and records their evidence reference; it
does **not** establish their truth. See `spec/JUDGMENT_LAYER.md` §2a.

## What is tracked

The property signature is fixed and small:

- `n`, `k` — dimensions,
- `d_X`, `d_Z`, `d` — distances (opaque; transported as bounds),
- `w` — maximum stabilizer weight (derived, exact, carried),
- `r` — interaction radius relative to a supplied layout (derived, exact,
  carried; a state with no layout has no radius),
- Tanner connectivity of the displayed rows (derived, exact, carried).

Consumer-supplied hypotheses (`w_del`, `w_exp`, `w_X`, `w_Z`, exposure minima,
enumerations, trusted factor distances) are **judgment inputs**, not state
fields: they are not part of state identity, not minted, and not transported by
`used`.

## Status

- **Gates:** Gate 0 (taxonomy-to-syntax) and Gate 1 (formal syntax) are
  ratified. Gates 2–7 are unchecked. See `spec/GATES.md`.
- **Obligations:** every obligation in scope has a dated hand derivation in
  `spec/OPERATIONAL_SEMANTICS.md` §4; the ledger is `spec/OBLIGATIONS.md`.
  Machine-checked soundness is **not** claimed. `OBL-JUDGMENT-SOUNDNESS` is
  `proved` by hand derivation; its Lean form is stated for a well-formed
  evaluation chain with evaluation assumed, and the `k` and distance cells enter
  as hypotheses.
- **Mechanization:** `lean/` is partial and certifies only the theorems it
  states (`lean/README.md`). The build is expected to be green on `main`.
- **Scope:** the stopping point is `SCOPE.md`. The calculus is deliberately
  incomplete: `unavailable` is withheld by design commitment, and no artifact
  describes the MVP as aiming at completeness.

## Repository layout

Four layers. One authority per topic: the same fact is not stated twice.

| Layer | Holds | Authority |
| --- | --- | --- |
| `spec/` | Normative calculus: representation, state model, term language, operational semantics, judgment layer, claims, obligations | Wins every disagreement |
| `machine/` | `state.json`, `semantics.json`, `consumer.json`, executable interval consumer, fixtures, pinned replay | Derived; where it disagrees with prose, prose wins and the transcription is fixed |
| `lean/` | Partial Lean 4 mechanization | Certifies only the theorems it states |
| root | Framing and process: `README.md`, `AGENTS.md`, `AUTHORITY.md`, `SCOPE.md`, `CHANGELOG.md`, `CONTRIBUTING.md` | Process only |

`CHANGELOG.md` is the dated record of what was decided, when, and why. Root
also holds `spec/VOCABULARY.md`, `spec/CLAIMS.md`, `spec/VERSIONING.md`, and
`spec/TAXONOMY.md`.

## Running and reproducing

Python 3.12 or newer.

```sh
python -m pip install -r machine/requirements.txt
sh scripts/lint_docs.sh
python -m pytest -q machine/
python3 machine/fixture_conformance.py
```

Lean (toolchain pinned in `lean/lean-toolchain`):

```sh
cd lean && lake build
```

The pinned qLDPC replay additionally needs the challenge repository at a pinned
commit; see `machine/README.md`.

## Where to read next (humans)

- **Start with the calculus:** `spec/REPRESENTATION.md` (how a code is written
  down) → `spec/STATE_MODEL.md` → `spec/TERM_LANGUAGE.md` →
  `spec/OPERATIONAL_SEMANTICS.md` → `spec/JUDGMENT_LAYER.md`.
- **Then reference:** `spec/CLAIMS.md` (admission schema and evidence
  vocabulary), `spec/OBLIGATIONS.md` (the obligation ledger),
  `spec/GATES.md` (proof gates and non-goals), `spec/TAXONOMY.md` (operation
  inventory), `spec/VERSIONING.md`.
- **The consumer:** `machine/README.md` and `machine/priced_calculus.py`.
- **The mechanization:** `lean/README.md`.
- **Scope and stopping point:** `SCOPE.md`.

Agents should read `AGENTS.md` first (read order, hard rules, what to grep).

## Non-goals

No complete move set, no target family, no completeness theorem, no inferability
claim, no unconditional exact deletion distance, no circuit realizations, no
DEM-level distance equality, no software code generator beyond the admitted
consumer, and no load-bearing category theory. The executable consumer is a
discovery aid whose hypotheses remain explicit and whose traces do not prove
soundness. See `spec/VERSIONING.md`.

## Provenance

Seeded from an earlier proposal draft; this copy is the living document. The
formal-design packages FD0–FD7 are closed, and their artifacts are superseded by
`spec/`. The proposal, an archived internal note, and an in-preparation
manuscript are not shipped here; the calculus is stated so that its normative
content does not depend on them (`REFERENCES.md`).

## Contributing

See `CONTRIBUTING.md` for the contribution process and `CODE_OF_CONDUCT.md` for
community standards. Mathematical claims (a theorem that does not hold, a
derivation error) are reported as normal issues, not security issues — see
`SECURITY.md`. Decisions belong in pull requests or `CHANGELOG.md`, not
amended into the artifact they concern.

## License

Apache 2.0 — see `LICENSE`.