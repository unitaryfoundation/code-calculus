# Changelog

All notable changes to this project are documented here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [Unreleased]

## [0.3.0] - 2026-11-19

### Added
- **Gate-realization judgment rows (axis 3):** the operator-indexed codespace-preservation
  predicate `preserves_U(C)` on CSS displays with its `C-ADD-CHECK` carry cell and
  kernel rows, plus the equal-syndrome generator weight floor `ω(C) ≥ ⌈d(C)/2⌉`
  carried by weakening (`spec/JUDGMENT_LAYER.md` §2, §2h, §7.1–§7.4;
  `spec/OPERATIONAL_SEMANTICS.md` §4.37).
- **`A-QUOTIENT` monomial-quotient specialization:** conditional transfer-theorem
  record (`spec/JUDGMENT_LAYER.md` §2i, `spec/TAXONOMY.md` §2.15); remains
  `taxonomy-only` at rung 1.
- **Conditional family-level one-shot level-map transport:** Yuan hollowed-tensor
  level map admitted as judgment vocabulary (`spec/JUDGMENT_LAYER.md` §2j,
  `spec/CLAIMS.md`); no new property or operator.
- **Positive composition criteria, CNOT-disguised direct sums, depth-one
  equality, multi-band patch count, mapping-cone/chain-map constructor,
  decoupling of translation-invariant CSS codes:** admitted as conditional
  judgment rows (`spec/OPERATIONAL_SEMANTICS.md` §4.37–§4.42).
- **New admitted constructors:** `L-EMPTY`, `L-FREE`, `A-PULLBACK`, `A-PUSHOUT`
  (nullary/interface constructors) and the CSS-preserving column CNOT/SWAP
  transformation, all `transition-defined` (`spec/TERM_LANGUAGE.md` §1–§2,
  `spec/OPERATIONAL_SEMANTICS.md` §4.43, `spec/JUDGMENT_LAYER.md` §2g/§2d.5).
- **Sector-split deletion price cells for `C-DELETE-CHECK`:** deleted-sector
  `d'_τ = min(d_τ, w_del)`, opposite sector `d'_{τ̄} = min(d_{τ̄}, w_exp)`,
  full distance `d' = min(d, w_del, w_exp)` (`spec/JUDGMENT_LAYER.md`).
- **`E-SPLIT` transition:** stated as a candidate proposal
  (`spec/OPERATIONAL_SEMANTICS.md`).
- **`E-GLUE` mechanization and binary-only decision:** `glue(e_1, e_2; u⃗)`
  production recorded in `spec/TERM_LANGUAGE.md` §1–§2; `E-GLUE` advances to
  rung 5 (`contract-stated`) with the extracted derivation mechanized
  (`lean/CodeCalculus/GlueExtraction.lean`).
- **Annotated-term soundness mechanization and W13 Gate 6 rows:** completed
  with identifier-level refusals and Trace/StepChain seam discharge.
- **Kernel five promoted to rung 6 (`contract-proved`):** backed by dated hand
  derivations including quotient-level logical-sector exact sequences (§4.39)
  and the `stdCSS-3` metatheorem re-discharge ledger (§4.40); all
  `discharged-through` values advanced to `stdCSS-3`.
- **Machine-side:** sector-targeted deletion/peel search
  (`bounded_sector_search`), multi-objective candidate ranking, multi-band
  patch count as construction metadata, constructor support in
  `machine/constructors.py` and Lean (`Constructors.lean`,
  `ConstructorAssembly.lean`, `ConstructorInstances.lean`, `Eval.lean`).

### Changed
- `spec/VERSIONING.md`: current development release advanced to `stdCSS-3` /
  `v0.3.0`; new release row appended (discharged-through advanced).
- `spec/CLAIMS.md`: kernel five at rung 6; `E-GLUE` at rung 5; new
  constructor and judgment-row admissions recorded.
- `machine/operation_registry.json`, `machine/semantics.json`, `machine/state.json`:
  updated for new constructors and cells.
- Lean toolchain and axiom audit hygiene (continued).

### Notes
- Gates 0–6 are ratified; Gate 7 remains unchecked by design.
- `discharged-through` values advanced to `stdCSS-3` (`spec/OPERATIONAL_SEMANTICS.md` §4.40); re-discharge
  obligations scoped to named fragments remain open where recorded.
- **Lean mechanization scope:** determinism of `EvalExpr` for the newly
  admitted `A-PULLBACK` and `A-PUSHOUT` constructors is now discharged
  (`evalExpr_unique`, `lean/CodeCalculus/ExpandedSoundness.lean`); the
  module is in the axiom audit (`AxiomAudit.lean`), which reports
  5,972 constants, 43 on `Classical.choice`, and no `sorryAx`. Every other
  audited constant remains free of `sorryAx`. This closes the determinism gap
  for those constructors; it is a mechanization fact, not a soundness
  claim, and does not affect the executable consumer.

## [0.2.0] - 2026-11-17

### Added
- **Ten distance-increasing expression constructors (`stdCSS-3`):** admitted
  `L-HGP`, `L-LIFTED`, `L-GROUP-ALGEBRA`, `A-CONCAT`, `L-BALANCED`,
  `L-TANNER`, `L-TILE`, `A-PRODUCT`, `A-DOUBLE`, and `L-NESTED-CSS` at
  `transition-defined` (`spec/TERM_LANGUAGE.md` §1–§2,
  `spec/OPERATIONAL_SEMANTICS.md` §2 and §4.34–§4.36,
  `spec/JUDGMENT_LAYER.md` §2g, `machine/constructors.py`).
- **Lean constructor well-formedness, overlaps, and $k$ bookkeeping:**
  mechanized output well-formedness and $n$ for all ten admitted constructors
  (`Constructors.lean`, `ConstructorWellFormedness.lean`,
  `ConstructorOrthogonality.lean`, `ConstructorOverlap.lean`,
  `BalancedOverlap.lean`, `ConstructorAssembly.lean`,
  `ConstructorInstances.lean`), same-sector independence and full display
  retention with $k = k_O$ for `A-CONCAT` (`ConcatRetention.lean`), closed $k$
  forms for `L-GROUP-ALGEBRA` and empty-wiring `A-DOUBLE` plus natural-row rank
  bookkeeping for `L-BALANCED`, `L-TANNER`, and `L-TILE`
  (`ConstructorRank.lean`, `ConstructorRankTyped.lean`,
  `ConstructorRankNatural.lean`), and combining arithmetic (`hgp_arith`,
  `product_arith`) for `L-HGP` and `A-PRODUCT` (`lean/extra/ClosedK.lean`), with
  the four rank axioms recorded in `AXIOMS.md`.
- **`E-GLUE` promotion, seam-certificate extraction, and future-$\Pi$ fields:**
  promoted `E-GLUE` to `transition-defined` in `spec/CLAIMS.md`; defined the
  logical-witness and boundary/edge-label fields (`spec/STATE_MODEL.md` §1/§1a);
  derived the glued sector-distance class-pair formula and discharged
  `OBL-GLUE-RE-EXPOSURE` (`spec/OPERATIONAL_SEMANTICS.md` §4.31, §4.33); and
  mechanized exact-distance glue lower bounds, class-pair bijection, witness
  survival, field transport, and the admissible-seam family guarantee
  (`ExactGlue.lean`, `ExactGluePairs.lean`, `ExactGlueDistance.lean`,
  `ExactGlueSurvival.lean`, `LogicalWitness.lean`, `WitnessFields.lean`,
  `AdmissibleSeamFamily.lean`).
- **Peeling/puncturing prices and exact-distance Gate 6 soundness:** added two
  `E-PEEL` distance price cells (`w_avoid`, `w_expose`) over sharpened unpriced
  carries and recorded the `E-PUNCTURE` reduction (`spec/JUDGMENT_LAYER.md`
  §2a–§2c, `spec/OPERATIONAL_SEMANTICS.md` §4.28–§4.29); mechanized the §4.28
  peel relations and `exactDist_k0` (`ExactPeel.lean`), the §4.13 graft
  relations (`ExactGraft.lean`), direct-sum and namespace-permutation exact
  distance laws (`ExactDirectSum.lean`, `ExactPermute.lean`), and
  `gate6_interval_soundness_exact` (`Gate6Exact.lean`).
- **Closed-term judgment soundness and `W13` seam transport:** mechanized
  `judgment_soundness_of_term` (`TermSoundness.lean`) over the evaluation trace
  of a closed term, the derivation-level `W13` half for generator-referencing
  claims (`Ann.gen`) across kernel, `E-GRAFT`, and Gate 6 steps
  (`Transport.lean`), and the seam condition across chains of single steps
  (`SeamChains.lean`).
- **Mechanized kill-certificate checker and heuristic outcome vocabulary:**
  admitted the `certificate-checked` evidence status for per-state atomic
  judgments and the `probabilistic` claim shape for heuristic search outcomes
  (`spec/CLAIMS.md`, `spec/VERSIONING.md`); mechanized `checkCertificate_sound`
  and per-state instances (`CertificateChecker.lean`,
  `CertificateInstances.lean`).
- **Layout-transfer cells and conformance harnesses:** added layout-transfer
  judgment cells (`spec/JUDGMENT_LAYER.md` §2d.5, `machine/semantics.json`
  `layout_cells`) and `layout_conformance_harness.py`, alongside the non-CSS
  companion `machine/symplectic_calculus.py` and
  `symplectic_conformance_harness.py`.
- **Consumer search and planning:** added bounded support search, sector-swap
  exploitation via `E-LOCAL-HADAMARD` (`T=Q`), multi-objective (Pareto)
  candidate ranking, and multi-level concatenation tower sweeps (`k_in > 1`).

### Changed
- Updated `spec/VERSIONING.md` to `stdCSS-3` / `v0.2.0` (`discharged-through`
  values not advanced).
- Modularized `machine/priced_calculus.py` into focused modules (`state.py`,
  `intervals.py`, `layout.py`, `connectivity.py`, `tower_prices.py`,
  `constructors.py`, `sequence.py`, `entrypoints.py`) while keeping
  `priced_calculus.py` as the compatibility entry point.
- Upgraded the Lean toolchain to `leanprover/lean4:v4.35.0` and hardened
  `AxiomAudit.lean` and `scripts/lint_docs.sh`.

## [0.1.0] - 2026-11-01

### Added
- Initial public release of the CSS code calculus (`stdCSS-2`): the executable
  consumer prototype (`machine/`), the normative specification (`spec/`), and
  the Lean mechanization (`lean/`).
- Apache 2.0 license and community files (`CONTRIBUTING.md`,
  `CODE_OF_CONDUCT.md`, `SECURITY.md`).
- Run and reproduction instructions in `README.md`.
- Four-axis release pin for `v0.1.0` in `spec/VERSIONING.md`.
