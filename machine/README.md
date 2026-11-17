# Machine (derived transcription and executable consumer)

This directory holds the **derived** side of the repository: a transcription of
the normative specification into machine-readable form, plus the executable
interval consumer, fixtures, and pinned replay. It is **not** normative — where
it disagrees with [`../spec/`](../spec/), the prose wins and this directory is
fixed (`AGENTS.md` *Precedence*).

No soundness claim is established here. `priced_calculus.py` evaluates the
implemented transition subset and propagates distance intervals without
searching for exact distance; its traces are evidence about the interface, not
proofs.

## Layout

- `state.json`, `semantics.json` — transcription of `spec/STATE_MODEL.md`,
  `spec/REPRESENTATION.md`, `spec/TERM_LANGUAGE.md`, and
  `spec/OPERATIONAL_SEMANTICS.md`; `semantics.json` also carries the layout
  cells of `spec/JUDGMENT_LAYER.md` §2d.5 under `layout_cells` (how the
  layout travels with each transition, the radius direction, and the honesty
  verdict).
- `consumer.json` — transcription of the interval consumer contract
  (`spec/JUDGMENT_LAYER.md` §§2a–2f, 5).
- `operation_registry.json` — derived index of `spec/TAXONOMY.md` and
  `spec/CLAIMS.md`.
- `priced_calculus.py` — compatibility shim re-exporting the focused modules below (issue #378).
- `state.py`, `intervals.py`, `layout.py`, `connectivity.py`, `tower_prices.py`, `constructors.py`, `sequence.py`, `entrypoints.py` — the executable interval consumer, split by concern (issue #378). `priced_calculus.py` remains the documented implementation path for `semantics.json` / `consumer.json`.
- `symplectic_calculus.py`: machine-side companion for general (non-CSS)
  stabilizer codes: the symplectic state, the move set (`SYM-SKIP`,
  `SYM-DELETE-CHECK`, `SYM-ADD-CHECK`, `SYM-DIRECT-SUM`, and the cross-layer
  `X-SYMPLECTIC-DOUBLE` and `X-SYMPLECTIC-HALVE`), and the Pauli-distance
  ledger (issues #294 and #305). Not an admitted calculus layer: the
  extended-state layer is a Gate 6 decision that has not been taken, and the
  companion interval rules are maintained in the development notes
  (`symplectic_move_set_2026-11-10.md`).
- `planner.py`, `certificates.py` — consumer-side planning and certificate
  helpers. Bounded searches (the planner's sector-targeted search and the
  strict-improvement enumeration fallback) attach a `heuristic_outcome`
  record in the admitted `probabilistic` claim shape (`spec/CLAIMS.md`,
  *Admission*, issue #329): a claim about the search that moves no ledger
  endpoint. `certificates.py` also translates a state and a kill certificate
  into Lean source for the mechanized checker
  (`lean/CodeCalculus/CertificateChecker.lean`, issue #371);
  `experiments/certificate_lean_instances.py` regenerates
  `lean/CodeCalculus/CertificateInstances.lean`, and
  `test_certificate_lean.py` pins the committed file to the generator. The
  translation is untrusted and the Python checker stays the prototype:
  `certificate-checked` attaches to the theorems `lake build` accepts.
  The planner enumerates removals (deletion, peel, puncture),
  screens them, transports the carried ledger, and ranks the survivors;
  `bounded_support_search` (issue #347) is its recorded-budget search over
  supports: a child's supports are enumerated by weight under `budget` and
  `max_weight` (defaults `DEFAULT_SUPPORT_BUDGET`,
  `DEFAULT_SUPPORT_MAX_WEIGHT`), a witness found is handed to the ledger's
  own transport as a post-step observation, and a sector without one is
  recorded as "no survivor found up to weight `w`" with no lower endpoint
  raised. `plan(..., support_search=...)` runs it on every surviving child;
  `tighten_ledger_with_search` runs it on one state.
  Sector-swap exploitation (issue #346) is
  `sector_swap_exploitation` in `priced_calculus.py`, which applies
  `E-LOCAL-HADAMARD` at `T=Q` when the carried ledger says the other sector
  is the stronger one for the target and records the reason and the
  full-distance invariance; `plan(..., sector_swap=True)` offers it as a
  candidate and `bounded_sector_search` applies it first.
- `constructors.py` (`priced_calculus.construct`): evaluates the nine typed
  constructors admitted 2026-11-11 (`L-HGP`, `L-LIFTED`, `L-GROUP-ALGEBRA`,
  `A-CONCAT`, issue #330; `L-BALANCED`, `L-TANNER`, `L-TILE`, `A-PRODUCT`,
  `A-DOUBLE`, issue #369, the last three with a commutation premise whose
  failure is `NoDerivation`) and `L-NESTED-CSS` (2026-11-13, issue #445, with
  the same kind of premise) and `DistanceLedger.for_constructed` starts their
  ledgers at $[0, +\infty)$ with sourced lower bounds only.
  `experiments/constructor_lean_instances.py` regenerates
  `lean/CodeCalculus/ConstructorInstances.lean`, where the kernel checks
  that the Lean state updates equal `construct`'s states on one or two
  instances per constructor (issue #370); `test_constructor_lean.py` pins
  the committed file to the generator and checks that every admitted
  constructor has a Lean production, rule, and instance.
- `oracle.py` — **oracle only.** Small-`n` exhaustive exact-distance utility for
  verification/audit; never imported by the consumer or planner. Explicit
  `n` ceiling (`ORACLE_N_CEILING`).
- `fixture_conformance.py` — full fixture-conformance evaluator.
- `lean_fixture_coverage.py` — record-by-record conformance against the Lean
  transcription.
- `fixtures/`: `mvp_fixtures.json` (the state-level fixture surface),
  `qldpc_10_2_3_b.json`, and `symplectic_fixtures.json` (the symplectic
  move set's records, replayed by the symplectic harness; not part of the
  acceptance surface).
- `experiments/`: the priced-conformance harness
  (`priced_conformance_harness.py`), the symplectic-conformance harness
  (`symplectic_conformance_harness.py`, with the exhaustive Pauli-distance
  oracle), the layout-conformance harness
  (`layout_conformance_harness.py`: random states and layouts, every
  transition transited, each layout cell's direction, formula, and honesty
  claim checked exactly, and the consumer's own layout transport compared
  against the cells), the exact-distance oracle and challenge replay
  (`issue21_challenge_replay.py`), the column-splitting reduction for the
  exposure price (`weight3_split_reduction.py`: builds the weight-three split
  of a parent and compares exhaustive exposure prices, issue #326), the
  tower price sweep (`tower_sweep.py`: builds concatenation towers from small
  inner codes and compares `tower_deletion_prices` with exhaustive
  enumeration, issue #327), the `E-GLUE` class-pair check
  (`glue_class_pairs.py`: enumerates glued logicals for re-exposed classes
  and compares the class-pair distance formula with the oracle, issue #328),
  layout/graft surveys, and recorded reports.
- `test_*.py` — the test suite run by CI (`python -m pytest -q machine/`).
- `requirements.txt` — Python dependencies.

## Run and validate

Python 3.12.

```sh
python -m pip install -r machine/requirements.txt
python -m pytest -q machine/
python3 machine/fixture_conformance.py
python3 machine/experiments/priced_conformance_harness.py
python3 machine/experiments/symplectic_conformance_harness.py
python3 machine/experiments/layout_conformance_harness.py
```

From the repository root, the documentation lint also checks that every rule
transcribed in `consumer.json` and `semantics.json` carries a `source` resolving
to a `spec/` section naming its operation:

```sh
sh scripts/lint_docs.sh
```

The pinned qLDPC replay additionally needs the challenge repository at a
pinned commit (see [`../README.md`](../README.md)).

## Authority

- [`../spec/`](../spec/) is the source of truth; this directory is derived.
- [`../AGENTS.md`](../AGENTS.md) states the hard rules, including that priced
  hypotheses are inputs rather than computed facts, and that the consumer
  checks input shape, not truth.
- [`../spec/GATES.md`](../spec/GATES.md) and
  [`../spec/VERSIONING.md`](../spec/VERSIONING.md) state the proof gates,
  explicit non-goals, and release scope for the calculus and this consumer.