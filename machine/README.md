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
- `priced_calculus.py` — compatibility shim re-exporting the focused modules below.
- `state.py`, `intervals.py`, `layout.py`, `connectivity.py`, `tower_prices.py`, `constructors.py`, `sequence.py`, `entrypoints.py` — the executable interval consumer, split by concern. `priced_calculus.py` remains the documented implementation path for `semantics.json` / `consumer.json`.
- `layout_provider.py` — consumer-side layout provider (issue #666). It
 synthesizes an honest planar layout from a state's displayed Tanner graph
 in three stages: a spectral or classical-MDS embedding, a rank-preserving
 packing onto an integer grid with at most `layers` qubits per site, and a
 deterministic move/swap refinement of `(r^2, sum of squared row
 diameters)`. It reports the exact radius, the locality class, and a
 rectilinear total grid distance `W` as ledger metadata. It is ledger-only:
 it never alters a state, it refuses to replace a document's existing
 layout unless asked, and it writes no `contributed_by` credit of its own.
 The layout is a witness with no optimality claim
 (`spec/JUDGMENT_LAYER.md` §2d.5). Run it as
 `python3 -m machine.layout_provider entry.json out.json --layers 1`.
- `symplectic_calculus.py`: machine-side companion for general (non-CSS)
 stabilizer codes: the symplectic state, the move set (`SYM-SKIP`,
 `SYM-DELETE-CHECK`, `SYM-ADD-CHECK`, `SYM-DIRECT-SUM`, and the cross-layer
 `X-SYMPLECTIC-DOUBLE` and `X-SYMPLECTIC-HALVE`), and the Pauli-distance
 ledger. Not an admitted calculus layer: Gate 6 was ratified on 2026-11-19
 with the extended-state layer refused (`spec/GATES.md`), and the companion
 interval rules are kept in the development repository, not in the
 public tree.
- `planner.py`, `certificates.py` — consumer-side planning and certificate
 helpers. Bounded searches (the planner's sector-targeted search and the
 strict-improvement enumeration fallback) attach a `heuristic_outcome`
 record in the admitted `probabilistic` claim shape (`spec/CLAIMS.md`,
 *Admission*): a claim about the search that moves no ledger
 endpoint. `certificates.py` also translates a state and a kill certificate
 into Lean source for the mechanized checker
 (`lean/CodeCalculus/CertificateChecker.lean`);
 `experiments/certificate_lean_instances.py` regenerates
 `lean/CodeCalculus/CertificateInstances.lean`, and
 `test_certificate_lean.py` pins the committed file to the generator. The
 translation is untrusted and the Python checker stays the prototype:
 `certificate-checked` attaches to the theorems `lake build` accepts.
 A second format, the pruning tree
 (`build_sector_lower_bound_tree_certificate`,
 `check_sector_lower_bound_tree_certificate`, `lean_tree_instance_block`),
 covers the vectors below the bound by classes, so its size follows the
 search and not the ball: about 4,500 nodes against 174,437 vectors for
 the bound 6 on the 30-qubit instance. It uses no code symmetry.
 `ingestion.py` translates an external matrix presentation into a Lean
 `CodeState` under the contract of `spec/REPRESENTATION.md` §9: the
 canonical row order, the binding hash (`checks_sha256`, the one
 qldpc-challenge computes), the Lean block with its kernel-checked binding
 theorem, and `binding_failures`, which re-derives the hash from the Lean
 source. `experiments/code_state_lean_instances.py` regenerates
 `lean/CodeCalculus/IngestedInstances.lean`, prints a module for one
 presentation with `--presentation FILE --name NAME`, and checks the
 committed bindings with `--verify`; `test_code_state_lean.py` pins all
 three.
 The planner enumerates removals (deletion, peel, puncture),
 screens them, transports the carried ledger, and ranks the survivors;
 `bounded_support_search` is its recorded-budget search over
 supports: a child's supports are enumerated by weight under `budget` and
 `max_weight` (defaults `DEFAULT_SUPPORT_BUDGET`,
 `DEFAULT_SUPPORT_MAX_WEIGHT`), a witness found is handed to the ledger's
 own transport as a post-step observation, and a sector without one is
 recorded as "no survivor found up to weight `w`" with no lower endpoint
 raised. `plan(..., support_search=...)` runs it on every surviving child;
 `tighten_ledger_with_search` runs it on one state.
 Sector-swap exploitation is
 `sector_swap_exploitation` in `priced_calculus.py`, which applies
 `E-LOCAL-HADAMARD` at `T=Q` when the carried ledger says the other sector
 is the stronger one for the target and records the reason and the
 full-distance invariance; `plan(..., sector_swap=True)` offers it as a
 candidate and `bounded_sector_search` applies it first.
- **Applicability diagnostics (issues #592, qldpc-challenge #7116):** `bounded_sector_search`
  always returns an `"applicability"` record (also fillable in place via
  `diagnostics=new_applicability_record()`). It reports, per move family,
  `enabled`, `enumerated`, and the first stage that rejected each candidate
  (`apply_fail`, `bare_qubit`, `disconnected`, `derive_fail`, `min_upper`,
  `deep_refuted`, `screened`, `dominated`, `over_budget`, `survived`,
  `improving`). `plan()` fills the same record
  inline, so accounting costs one increment per drop rather than a second
  replay. A family with `enabled: false` (e.g. `P-REBASE` by default) was
  never tested — distinct from one that failed. This is search control: it
  moves no ledger endpoint and discharges no obligation.
  Each family also carries `refusals`, which counts its `apply_fail` drops by
  the premise `apply_operation` named (row identifiers erased).
- **Parent-level applicability report (issue #592):**
  `move_applicability_report(state, weight_cap=None)` answers, for one parent
  and no ledger, why each move family does or does not give a usable child.
  It tries the whole candidate domain of `C-DELETE-CHECK`, `E-PEEL`,
  `E-PUNCTURE`, `E-GRAFT`, `P-REBASE`, and `E-EXTEND`, where the planner's
  enumerators skip candidates they can see will fail. Each candidate is
  counted once: under `refusals` by the failed premise, under `screens` when
  the child has a bare qubit, another validated weight-1 logical
  (`weight_one_logicals`, so the child has distance 1), a disconnected Tanner
  graph, or a check weight above `weight_cap`, or as `usable`. `blocking`
  names the most frequent reason when nothing is usable, and `parent` holds
  the per-sector column-weight histogram a peel depends on.
  `experiments/applicability_report.py ENTRY.json [--weight-cap W]` prints
  the report as a table. Search control only: no endpoint moves.
- **Objective-aware search (qldpc-challenge #7116):** `bounded_sector_search(...,
  objective=...)` selects the axis on which a candidate counts as improving:
  `"distance"` (default, the carried sector interval), `"weight"` (maximum
  displayed check weight), `"n"`, `"k"`, a dict with `axis` and optional
  `targets` (e.g. a missing-n set), or a callable. `plan` orders candidates
  by the same objective so a weight/n-improving child is seen within the
  budget. The distance objective cannot see a weight or n gain, so campaigns
  targeting those axes must pass the matching objective explicitly.
- **Presentation and constructor separation:** a sector swap is a presentation
  symmetry (§4.27) and is returned under `"presentation_candidates"`, never in
  `"improving"`. `constructor_specs=...` evaluates typed constructors through
  `constructor_candidates()`, filters them by the same objective, and returns
  each with a `structural_profile` (`connected`, `blocks`, `block_sizes`) from
  `constructors.py`; that profile mirrors the gate's direct-sum screen before
  a child is staged. A constructed ledger still starts at `[0, +inf)` with no
  automatic distance rule. `_extend_candidates` now checks the commutation
  and independence premises before yielding single-qubit additions, removing
  candidates that could only fail `apply_operation`.
- `constructors.py` (`priced_calculus.construct`): evaluates the nine typed
 constructors admitted 2026-11-11 (`L-HGP`, `L-LIFTED`, `L-GROUP-ALGEBRA`,
 `A-CONCAT`; `L-BALANCED`, `L-TANNER`, `L-TILE`, `A-PRODUCT`,
 `A-DOUBLE`, the last three with a commutation premise whose
 failure is `NoDerivation`) and `L-NESTED-CSS` (2026-11-13, with
 the same kind of premise) and `DistanceLedger.for_constructed` starts their
 ledgers at $[0, +\infty)$ with sourced lower bounds only.
 `experiments/constructor_lean_instances.py` regenerates
 `lean/CodeCalculus/ConstructorInstances.lean`, where the kernel checks
 that the Lean state updates equal `construct`'s states on one or two
 instances per constructor; `test_constructor_lean.py` pins
 the committed file to the generator and checks that every admitted
 constructor has a Lean production, rule, and instance.
- `oracle.py` — **oracle only.** Small-`n` exhaustive exact-distance utility for
 verification/audit; never imported by the consumer or planner. Explicit
 `n` ceiling (`ORACLE_N_CEILING`).
- `fixture_conformance.py` — full fixture-conformance evaluator.
- `lean_fixture_coverage.py` — record-by-record conformance against the Lean
 transcription. It reports which fixtures Lean transcribes (all but `W24`),
 and compares each transcribed Lean state, read as text, with the JSON state
 it names; it exits non-zero on a mismatch.
- `fixtures/`: `mvp_fixtures.json` (the state-level fixture surface),
 `qldpc_10_2_3_b.json`, and `symplectic_fixtures.json` (the symplectic
 move set's records, replayed by the symplectic harness; not part of the
 acceptance surface).
- `experiments/`: the priced-conformance harness
 (`priced_conformance_harness.py`), the asserted discovery-loop stress battery
 (`stress_campaign.py`, issue #577 — four quadrants covering oracle import
 hygiene, all 17 admitted constructors + Pareto/domination brute-force +
 small-`n` oracle differential, medium-`n` pinned gate differential with
 operational prune precision and re-measure rate, invariant fuzzing,
 adversarial inputs, and an `n = 100–120` scale ladder; per-quadrant
 wall-clock budgets are advisory metrics rather than consumer-invariant
 violations; committed baseline recorded at
 `experiments/stress_campaign_report.json` (whitelisted in `.gitignore`);
 PR CI runs fast smoke-sized trials in `test_stress_campaign.py` and the full
 battery runs weekly in `.github/workflows/weekly.yml`; empirical
 falsification only, never a proof),
 the symplectic-conformance harness
 (`symplectic_conformance_harness.py`, with the exhaustive Pauli-distance
 oracle), the layout-conformance harness
 (`layout_conformance_harness.py`: random states and layouts, every
 transition transited, each layout cell's direction, formula, and honesty
 claim checked exactly, and the consumer's own layout transport compared
 against the cells), the exact-distance oracle and challenge replay
 (`issue21_challenge_replay.py`), the column-splitting reduction for the
 exposure price (`weight3_split_reduction.py`: builds the weight-three split
 of a parent and compares exhaustive exposure prices), the
 tower price sweep (`tower_sweep.py`: builds concatenation towers from small
 inner codes and compares `tower_deletion_prices` with exhaustive
 enumeration), the `E-GLUE` class-pair check
 (`glue_class_pairs.py`: enumerates glued logicals for re-exposed classes
 and compares the class-pair distance formula with the oracle),
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

The pinned qLDPC replay and the full discovery-loop stress battery additionally
need the challenge repository at a pinned commit (see [`../README.md`](../README.md));
the offline quadrants of `stress_campaign.py` run without a challenge checkout
(pass `--ci` for the minimal PR CI smoke trial counts):

```sh
python3 machine/experiments/stress_campaign.py --quick
```

## Authority

- [`../spec/`](../spec/) is the source of truth; this directory is derived.
- [`../AGENTS.md`](../AGENTS.md) states the hard rules, including that priced
 hypotheses are inputs rather than computed facts, and that the consumer
 checks input shape, not truth.
- [`../spec/GATES.md`](../spec/GATES.md) and
 [`../spec/VERSIONING.md`](../spec/VERSIONING.md) state the proof gates,
 explicit non-goals, and release scope for the calculus and this consumer.