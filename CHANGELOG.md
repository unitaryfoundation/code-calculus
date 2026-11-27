# Changelog

All notable changes to this project are documented here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [Unreleased]

## [0.3.2] - 2026-11-26

### Added
- **Consumer-side layout provider for the interaction radius:** `machine/layout_provider.py` synthesizes an honest planar layout from a state's displayed Tanner graph (spectral or classical-MDS embedding, rank-preserving packing onto an integer grid, and deterministic refinement of `(r^2, sum of squared diameters)`), reporting exact radius, locality class, and rectilinear total grid distance `W` as ledger metadata without altering state or replacing an existing layout (`spec/JUDGMENT_LAYER.md` §2d.5, `machine/test_layout_provider.py`).
- **`E-EXTEND` distance-loss cell:** for `E-EXTEND` with new qubits, the hypothesis `extend_distance_loss` (`loss_X` and/or `loss_Z`, non-negative integers, with an evidence reference) is read as `d'_tau >= d_tau - loss_tau` and sets sector `tau`'s lower endpoint to `max(0, L_tau - loss_tau)` instead of 0. It is refused when no qubits are added, when the parent has no `tau`-logical, and when a child witness contradicts it; the consumer checks shape only (`spec/JUDGMENT_LAYER.md` §2a, `spec/OPERATIONAL_SEMANTICS.md` §4.30, new obligation `OBL-EXTEND-DISTANCE-LOSS`). Consumer: `machine/intervals.py`, tested in `machine/test_extend_distance_loss.py`. Patch-level `stdCSS-3` inventory (`spec/VERSIONING.md` §5.3), covered by hand derivation only; there is no Lean counterpart.
- **Coset inputs for `L-LIFTED`:** the production `lift_{G;H}(A, B)` takes a subgroup `H <= G` by generators. Blocks are indexed by the left cosets `G/H`, `A` acts by the left action and `B`, whose terms must lie in `N_G(H)`, by the right action; a term outside the normalizer is malformed. `n = [G:H] * (n_A n_B + m_A m_B)`, and with `H` trivial the output is the regular lift row for row (`spec/OPERATIONAL_SEMANTICS.md` §2 card and §4.49, new obligation `OBL-COSET-LIFT-INPUTS`). Consumer: `lifted_product(..., subgroup=...)` and the `subgroup` key of `construct`, tested in `machine/test_constructors.py` and `machine/test_family_closure.py`. Patch-level `stdCSS-3` inventory (`spec/VERSIONING.md` §5.3), covered by hand derivation only; there is no Lean counterpart.
- **Frame-reading gate-realization predicates and any-angle `C-ADD-CHECK` cell (`stdCSS-3` / `v0.3.2`, axis 3):** four operator- and frame-indexed predicates on CSS displays (`preserves_U(C | F)`, `phase_U(C | F) = z`, `image_U(C; e) ≡ P`, `addresses_U(C; F, A)`) reading the logical-witness field `log` as a supplied frame (`spec/STATE_MODEL.md` §1a *Eigenvalue reading*, `spec/JUDGMENT_LAYER.md` §2/§2h Rows C–F/§7.1–§7.4, `spec/CLAIMS.md`, hand derivations in `spec/OPERATIONAL_SEMANTICS.md` §4.37 Lemmas 5–11), together with the frame-free `C-ADD-CHECK` cell (Corollary 7.1), all decided by exact rational arithmetic for rational angles $\theta_j \in \pi\mathbb{Q}$ (other angles `not yet defined`), `machine/consumer.json` transcription, and state-vector oracle harness and tests (`machine/experiments/gate_realization_rows.py`, `machine/test_gate_realization_rows.py`). Folded into `stdCSS-3` / `v0.3.2` by maintainer decision (`spec/VERSIONING.md` §5.3); no operation ID is minted, `C = (Q, X, Z, pres, used)` is unchanged, and the §4 metatheorem re-discharge audit against Rows C–F remains owed (`spec/OBLIGATIONS.md`).
- **`E-SPLIT` separating deletion:** the command production `split(Q_A; R)` admitted at `transition-defined`, derived over `C-DELETE-CHECK` and `C-SEQUENCE` (`spec/OPERATIONAL_SEMANTICS.md` §4.48), with a conditional block-interval cell, consumer support, and Lean `SplitCommand.lean`. The two-state projection reading is refused. Patch-level `stdCSS-3` inventory (`spec/VERSIONING.md` §5.3).
- **Split-subset `E-LOCAL-HADAMARD`:** `hadamard(T)` now applies to every $T\subseteq Q$ along which both row spaces split, not only $T=Q$ and $T=\varnothing$ (`spec/OPERATIONAL_SEMANTICS.md` §2 card, §4.27(b)). Mixed rows are re-presented by a deterministic selection that uses the existing canonical mint. The full distance carries exactly; the sector distances follow the $T$-split decomposition and are bounded below by $d$, not exchanged. Consumer: `CodeState.local_hadamard` and its interval transport, tested against the exhaustive oracle (`machine/test_split_hadamard.py`). Lean: `Eval.hadamardSplit`, with well-formedness, $k'=k$ and capacity as checked premises. `lean/CodeCalculus/SplitHadamard.lean` proves $d'=d$ and $d_\sigma'\ge d$ for the exact distance, and the Lean ledger carries them (`splitLedger`); the factor-code closed forms of the sector distances are hand-derived. Patch-level `stdCSS-3` inventory (`spec/VERSIONING.md` §5.3).
- **Gate 7 decision matrices and completeness obligation:** recorded the typed-input decision matrix, family-closure matrix, and scoped non-circular completeness feasibility decision (`spec/TAXONOMY.md`), opening `OBL-ELEMENTARY-COMPLETENESS` at status `open` (`spec/OBLIGATIONS.md`, recorded in `stdCSS-3` / `v0.3.2`).
- **Lean mechanization of `C-COLUMN-CNOT` and retirement of the §5.2 transitional clause:** added `Command.cnotSwap`, `Eval.cnotSwap`, and `lean/CodeCalculus/ColumnCnot.lean` and completed the §4.2 instance-contract record for the `v0.3.x` inventory (`spec/VERSIONING.md` §5.2, `spec/OBLIGATIONS.md`).
- **Asserted discovery-loop stress battery:** `machine/experiments/stress_campaign.py` asserts oracle import hygiene, four quadrants, and an `n = 100–120` scale ladder, and exits non-zero on an unexpected violation. Wall-clock budgets are advisory. It is empirical evidence that can falsify a rule and never confirms soundness.
- **Formal certificates for challenge entries:** `machine/experiments/formal_cert_from_challenge.py` turns a qldpc-challenge entry into a Lean module whose theorem `<name>_certified` binds the entry and states each sector's bound, builds it, checks its axioms, and prints the `certs/<slug>.json` payload once the module is committed. `export_challenge_certificate` (`machine/certificates.py`) builds and checks the payload; `machine/experiments/benchmark_formal_cert.py` measures generation and build time, and `lean/README.md` documents the workflow and the size limits. Nothing is admitted; the payload asserts what its named theorem states.
- **Blocking reasons in campaign records:** each `run_campaign` record carries the step's applicability record, with children pruned by their verdict counted and named as the blocker, and `bounded_sector_search` counts a refused candidate once, under its premise. Search control only.
- **Candidate future-Π field sketches in Lean:** `lean/CodeCalculus/FuturePiFields.lean` mechanizes two non-state sketch-refinement candidates outside `CodeState` — `ConstructionRecord` (`Option ClosedTerm` with command and constructor transport soundness) and `LogicalFrame` (paired `X`/`Z` logical representatives with canonical symplectic duality, automatic `OnePerClass` projection to `LogField`, and transport soundness across kernel and Gate 6 transitions). `spec/TAXONOMY.md` §2.6 (`E-PEEL`, *Conditions*) aligns its context wording with `OPERATIONAL_SEMANTICS.md` §4.28. Neither field is admitted to `spec/STATE_MODEL.md` §1a and the state model is unchanged.
- **Symplectic inner inputs for `A-CONCAT`, refusal decision:** `machine/experiments/concat_symplectic_inner.py` builds the composite of a CSS outer code and a symplectic inner code and decides whether its stabilizer group is CSS; symplectic inner inputs are refused by dated maintainer decision (`A-CONCAT` takes `stdCSS` states only, `spec/TAXONOMY.md` §2.14). Nothing is admitted.
- **Pruning-tree distance certificates:** a second certificate format for per-state sector distance lower bounds, which covers the vectors below the bound by classes instead of listing them (`machine/certificates.py`, `spec/CLAIMS.md` *Mechanized checker*). `checkPruneCertificate` in `lean/CodeCalculus/CertificateChecker.lean` is proved to imply the bound for the exact sector distance. `CertificateInstances.lean` proves both sector distances of a 30-qubit cyclic two-block code equal to 6 from trees of about 4,500 nodes, against 174,437 vectors for the kill list. No code symmetry is used.
- **External code ingestion:** a contract for translating a matrix presentation into a `CodeState` (`spec/REPRESENTATION.md` §9: canonical row order, the ingested state, and the binding hash, which is the `checks_sha256` of qldpc-challenge), a generator (`machine/ingestion.py`, `machine/experiments/code_state_lean_instances.py`), a Lean binding predicate with its soundness theorems (`lean/CodeCalculus/Ingestion.lean`), and two ingested instances with kernel-checked bindings and exact sector distances (`lean/CodeCalculus/IngestedInstances.lean`). Lean does not compute the hash; the comparison is made outside Lean.
- **Lean replays of the supplementary fixtures `W25` to `W29`:** the five are transcribed in `lean/CodeCalculus/Fixtures.lean` and replayed by the kernel: the two malformed states are refused, the direct sum with a shared live identifier has no derivation, the two deletion terms evaluate to the recorded states, and the `W25` kill certificate is accepted on the parent state and rejected on the child, whose exact `X`-distance is below the certified bound. `W24` is the one fixture Lean does not transcribe.
- **Transcription check:** `machine/lean_fixture_coverage.py` compares each hand-typed Lean fixture state with the JSON state it names and exits non-zero on a mismatch.
- **Counting bounds, local-rank bound, disjoint-views closed form, and no-go theorems for `k` of `L-TANNER` and `L-TILE` in Lean:** `k` is at least `n` minus the number of natural rows of the two sectors (`tannerState_k_ge`, `tileState_k_ge`), with equality iff the natural rows of each sector are independent (`tannerState_k_of_indep`, `tileState_k_of_indep`, `tannerState_k_eq_counting_iff`, `tileState_k_eq_counting_iff`). For `L-TANNER`, `tannerState_k_ge_localRank` gives the local-code rank bound `n <= k + |V_X| * rank(L_X) + |V_Z| * rank(L_Z)` (no weaker than `tannerState_k_ge`, and tighter when a sector with a view has redundant local checks), with exact equality on vertex-disjoint views (`tannerState_k_of_disjoint_views`). Formal no-go theorems prove that no function of `(n, L_X, L_Z, |V_X|, |V_Z|)` equals `stateK` across all valid `L-TANNER` evaluations (`tanner_k_not_determined_by_params`) and no function of the tile list, qubit count, placement count, and two kept-row counts equals `stateK` across all valid `L-TILE` evaluations (`tile_k_not_determined_by_params`).
- **Move applicability report:** `move_applicability_report` in `machine/planner.py` says, for one parent, which premise refuses each candidate of `C-DELETE-CHECK`, `E-PEEL`, `E-PUNCTURE`, `E-GRAFT`, `P-REBASE`, and `E-EXTEND`, and which screen (bare qubit, validated weight-1 logical, disconnected, check weight above a cap) removes each child that derives. `machine/experiments/applicability_report.py` prints it for a challenge entry. The search record of `bounded_sector_search` and `plan` now counts `apply_fail` drops by failed premise under `refusals`. Search control only; no ledger endpoint moves.

### Changed
- **Gate 7 ratified for `stdCSS-3` (2026-11-26):** typed inputs stay production arguments, family closure stays a code-level fact entering no judgment cell, and no completeness theorem is claimed; `OBL-ELEMENTARY-COMPLETENESS` stays `open` (recorded in `stdCSS-3` / `v0.3.2`, `spec/GATES.md` *Gate 7*). `spec/OBLIGATIONS.md` and `spec/CLAIMS.md` record that no `discharged-through` value or claim rung moves. No soundness claim is made.
- **Versioning by shape and inventory (`spec/VERSIONING.md` §3, §4.1, §4.2, §5, §8):** the calculus ordinal changes only when an interface changes (a grammar sort or production form, a judgment form or assertion predicate, an evidence status or claim shape, a metatheorem, or state equality). A new command, constructor, widened input domain, or cell in an existing format is a patch-level instance, admitted with its local obligations under the new instance contract. The software MINOR is the ordinal from `v0.4.0` on, PATCH covers everything else, and the bump is computed from the merged changes. The staged-admission rule is removed. Everything published in `v0.3.0`, `v0.3.1`, and `v0.3.2` is recorded as `stdCSS-3`, with a `stdCSS-3` / `v0.3.2` row appended in §5.
- **Additive shape changes may be folded (`spec/VERSIONING.md` §3, §4.1, §6, §8):** a shape change that adds an interface and changes none may ship under the current ordinal by dated maintainer decision, with a fold record (row, why additive, evidence, metatheorems not yet covering it, audit owed). State-model changes, new grammar sorts or production forms, and changes to an existing metatheorem's statement are never folded. A folded interface is covered by no `discharged-through` value until a disposition names it, and from `v0.3.2` on the tag, not the ordinal, fixes the assertion language.
- **The four rank axioms are theorems:** `hgp_rankX`, `hgp_rankZ`, `product_rankX`, and `product_rankZ`, the ranks of the natural check matrices of `L-HGP` and `A-PRODUCT`, are proved in the audited module `lean/CodeCalculus/ClosedK.lean` with their statements unchanged, so the closed forms `hgpState_k_closed` and `productState_k_closed` rest on no assumption. New audited modules supply the linear algebra over mask lists: rank and nullity for an additive map (`RankNullity.lean`), the rank of a family of tensors (`TensorRank.lean`), row rank equals column rank and the rank of the two-block tensor family (`HgpRank.lean`), and the rank of the natural rows of a tensor product of two complexes (`ProductRank.lean`). `lean/extra/ClosedK.lean` holds no declaration, `AXIOMS.md` records no accepted assumption, and `scripts/lint_docs.sh` fails if a module under `lean/` declares an axiom.
- **Exact canonical state key without full permutation enumeration:** `_canonical_state_key` in `machine/planner.py` partitions qubits by label-independent signatures and skips interchangeable classes, preserving exact key equivalence while avoiding full permutation enumeration.
- **`A-CONCAT` retention export:** exported `combineRows_take_drop` and pinned the `A-CONCAT` retention theorems in `lean/CodeCalculus/ConcatRetention.lean` and `machine/test_constructor_lean.py`.
- **Consumer hardening, diagnostics, and spec/JSON alignment:** hardened consumer soundness and input boundaries, fixed planner constructor screening and `E-LOCAL-HADAMARD` diagnostics, and reconciled spec derivations and JSON transcriptions.

### Notes
- **Version label (maintainer decision, 2026-11-26):** ships as `v0.3.2` (`stdCSS-3`), appending the `stdCSS-3` / `v0.3.2` row in `spec/VERSIONING.md` §5 and folding the frame-reading gate-realization predicates and `OBL-ELEMENTARY-COMPLETENESS` (status `open`) into `stdCSS-3` / `v0.3.2` as additive shape changes under the fold clause of `spec/VERSIONING.md` §4.1, each with its fold record in §5.3.
- Gates 0–7 are ratified (Gate 7 for `stdCSS-3`, 2026-11-26). `OBL-ELEMENTARY-COMPLETENESS` stays `open`, no completeness theorem is claimed, and the §4 metatheorem re-discharge audit against Rows C–F remains owed (Rows C–F stand on the dated hand derivations of `spec/OPERATIONAL_SEMANTICS.md` §4.37 Lemmas 5–11 and are not mechanized). No soundness claim is made by this release.

## [0.3.1] - 2026-11-23

### Added
- **`L-PAIR-PARTITION` constructor (axis 2):** admitted as a `transition-defined` expression constructor with production `pair_partition(p; B_X, B_Z)` — the relative-permutation (CPM-PP / APM-PP) construction of Okada–Kasai v4 Thm 4. Dated hand derivation in `spec/OPERATIONAL_SEMANTICS.md` §4.46 (paired relative-affine orthogonality, output well-formedness, parameter bookkeeping, and the CPM-PP `(J+1)!` versus APM-PP distance-ceiling distinction); update-ownership and judgment rows in `spec/STATE_MODEL.md`, `spec/JUDGMENT_LAYER.md`, and `spec/CLAIMS.md`; machine implementation (`pair_partition_code`, `construct`, transcription entries) and Lean mechanization (`StateExpr.pairPartition`, `evalExpr_pairPartition_wf`, kernel-checked CPM-PP/APM-PP instances).
- **`PP-SCALE` promoted to rung 3 (`transition-defined`, axis 2):** the Kasai 2026 explicit-extension scaling of pair-partition codes, with production `pp_scale(e; P)`, Smith-normal-form slope/shift derivation (`spec/OPERATIONAL_SEMANTICS.md` §4.47), conditional per-state interval cell and conjectural family-level structural ceiling (`spec/JUDGMENT_LAYER.md` §2l), the new `OBL-PP-SCALE` obligation, and machine/Lean support. The earlier rung-1 (`taxonomy-only`) specialization record is retained as history.
- **Nonabelian finite-group inputs (axis 2):** `L-LIFTED`, `L-GROUP-ALGEBRA`, and `L-BALANCED` generalized from finite abelian groups given by cyclic orders to arbitrary finite groups presented by cyclic order, multiplication table, or permutation generators. Left and right regular representations $L(x)$ and $R(y)$ commute over $\mathbb{F}_2$, and $R(y) = L(y)$ entrywise in the abelian case, so the extension is conservative on the abelian fragment. The abelian $k$ closed form is refuted for nonabelian inputs by an explicit $D_4$ instance (`spec/OPERATIONAL_SEMANTICS.md` §4.44). Machine group presentations and Lean overlap/well-formedness theorems included.
- **Conditional constructor distance cells and witness lifting (axis 3):** five conditional lower-bound cells (`L-HGP`, `L-NESTED-CSS`, `A-CONCAT`, `A-PRODUCT`, `A-DOUBLE`) and five deterministic factor-to-child lifting procedures (`lift_hgp_witnesses`, `lift_nested_witnesses`, `lift_concat_witnesses`, `lift_product_witnesses`, `lift_double_witnesses`), recorded in `spec/JUDGMENT_LAYER.md` §2g.1 and derived in §4.45. `DistanceLedger.for_constructed` now consumes `constructor_cell` inputs, records `status: "conditional"` entries with named `source`, validates supplied/lifted witnesses, tightens upper endpoints, and refuses when a lower endpoint exceeds a validated witness weight. Lean `LedgerSound` proofs in `PricedInterval.lean`.
- **Prior-art records (documentation):** Wang commuting-check gauging (arXiv:2611.12236v1) and Kasai, *Increasing Quantum LDPC Code Distance through Explicit Extensions* (arXiv submit/8406448), with the `PP-SCALE` specialization record in `spec/TAXONOMY.md` §3.8.
- **Consumer applicability diagnostics:** `bounded_sector_search` reports per-move-family `enabled`, `enumerated` and first-drop-reason counts, so a campaign can tell an inapplicable move from one the search never tried.
- **Objective-aware search:** `objective=` selects distance, check weight, n, k, an axis/targets dict, or a callable; weight/n campaigns no longer measure the distance interval.
- **Constructor screening and separation:** typed `constructor_specs` enter the same objective-filtered pool, each with a `structural_profile` flagging direct sums; sector swaps are reported as presentation-only candidates, never as improvements.
- **Consumer stop/budget reporting:** `bounded_sector_search` reports why it stopped (`budget-exhausted`, `frontier-exhausted`, or `max-depth-reached`) and how much budget it declined. `run_campaign` termination records carry a `stop_reason` (`no-survivor`, `operation-failed`, or `step-limit-reached`). This is descriptive reporting only, with no verdict, ledger endpoint, or stopping-behaviour change. The pinned replay reports an experiment-only exact-distance decision gap alongside its existing experiment-only comparisons.
- **Lean productions for the multiplication-table presentation of nonabelian group inputs:** `StateExpr.liftTable`, `twoblockTable`, and `balancedTable`, with typing checks in `lean/CodeCalculus/CayleyTables.lean`, well-formedness of every evaluation, `n`, and kernel-checked `S_3` instances against the consumer. The permutation-generator presentation has no production of its own.
- **Consumer stress/campaign harness:** `machine/experiments/stress_v031_campaign.py` exercises the v0.3.1 feature surface (pair partition, `PP-SCALE`, nonabelian inputs, conditional constructor cells and witness lifting, objective-aware search, applicability diagnostics, constructor screening) and runs small constructor-seeded campaigns. It asserts its results: it exits non-zero on any unexpected error, crash, or failed check. A candidate is reported as certified only when its full-distance lower endpoint reaches the target; unresolved (`re-measure`) candidates are not counted as improvements.

### Changed
- `spec/VERSIONING.md`: dated notes of 2026-11-19 and 2026-11-22 recording the above as `v0.4.0`-target new-admission scope; the §8 staged-admission rule under which this patch ships; a 2026-11-23 §5.1 note staging the consumer capabilities of this patch on the `v0.4.0` row; no new calculus release row appended and no `discharged-through` value advanced by this patch.
- `spec/TAXONOMY.md`, `spec/TERM_LANGUAGE.md`, `spec/STATE_MODEL.md`, `spec/OPERATIONAL_SEMANTICS.md`, `spec/JUDGMENT_LAYER.md`, `spec/CLAIMS.md`, `spec/OBLIGATIONS.md`: new operation cards, grammar productions, update-ownership rows, hand derivations §4.44–§4.47, judgment cells, claim rows, and obligations (`OBL-PP-SCALE`, `OBL-NONABELIAN-GROUP-INPUTS`, `OBL-CONDITIONAL-CONSTRUCTOR-CELLS`).
- Machine: `machine/constructors.py`, `machine/intervals.py`, `machine/consumer.json`, `machine/operation_registry.json`, `machine/semantics.json`, `machine/state.json`, and the consumer search/decision surfaces (`machine/planner.py`, `machine/entrypoints.py`, `machine/oracle.py`) — new constructors, conditional cells, transcription entries, and search/stop reporting; unit and conformance coverage extended.
- Lean: `Term.lean`, `Constructors.lean`, `Eval.lean`, `ConstructorOverlap.lean`, `BalancedOverlap.lean`, `ConstructorAssembly.lean`, `ConstructorInstances.lean`, `PricedInterval.lean`, `ExpandedSoundness.lean`, `CayleyGroups.lean`, `CayleyTables.lean` extended; no new `sorry` and no change to the accepted axiom set.
- **`PP-SCALE` status-row alignment and mechanical review fixes:** stale-text alignment in `spec/TAXONOMY.md` and `spec/VERSIONING.md` and dead-code removal in `machine/intervals.py` and `machine/test_constructors.py`; no rule, premise, claim status, or obligation status moves.

### Fixed
- **Consumer decision rule reads the interval only:** `DistanceLedger.decide` returns `prune` when the upper endpoint is finite and below the target, replacing a deep-witness gate that appears in no spec, transcription, or Lean counterpart; the ledger no longer invents confidence labels, and `has_deep_witness` moved to `DistanceLedger`.
- **Lean `L-PAIR-PARTITION` rule carries the pair-partition premise of its card:** the typed rule now requires that within every block-row pair each relative affine map occurs an even number of times, and `EvalExpr.ppScale` reads the same predicate; `sixMaps_no_derivation` records a commuting-rows input with no pair partition that the card and the consumer refuse and the old rule admitted.
- **Consumer input boundaries:** nine defensive fixes surfaced by a code-quality stress test (sourced lower bounds, shape validation, no planner oracle, narrow exception handling, strict support labels), with regression tests.

### Notes
- **Version label (maintainer decision, 2026-11-23):** the changes above are new-admission, axis-2, and axis-3 content staged for `v0.4.0` by dated notes in `spec/VERSIONING.md` (2026-11-19 and 2026-11-22). The maintainer kept the `v0.3.1` label. `spec/VERSIONING.md` §8 now states the rule that allows a PATCH to carry staged admissions: the row append and ordinal bump fall due at the next MINOR. No §5 release row is appended and `discharged-through` values remain at `stdCSS-3`. The re-discharge obligations of §4 apply at the next MINOR release audit, which is `v0.4.0` (`stdCSS-4`).
- Gates 0–6 are ratified; Gate 7 remains unchecked by design. The new constructors are `transition-defined`; conditional distance cells are priced hypotheses, not proved bounds. No soundness claim is made by this release.
- Validation on the release commit: `sh scripts/lint_docs.sh`; `pytest machine/` under Python 3.12; fixture conformance (26 fixtures, no mismatches); the priced, symplectic and layout conformance harnesses; `lake build` (64 jobs); and the asserted stress harness, which reports zero errors, crashes, and failed checks. CI on `origin/main` was green before this release commit.

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
