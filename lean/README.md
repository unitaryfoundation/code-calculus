# Lean development

This directory contains a partial Lean 4 mechanization of the code-calculus.
It certifies only the theorems it states; it does not establish soundness of
the whole calculus. See the repository `README.md` and `spec/GATES.md` for
what is and is not claimed.

## Building

Toolchain is pinned in `lean-toolchain`. From this directory:

```sh
lake build
```

## Layout

- `CodeCalculus.lean` — top-level module that imports everything below.
- `CodeCalculus/` — one module per concern:
  - `ChoiceFree.lean`: restatements of core-library facts whose library
    proofs depend on `Classical.choice`, proved without it.
  - `State.lean` — presented code state, equality, canonical mint.
  - `Term.lean` / `Eval.lean` — term language and big-step evaluation
    (`StateExpr.glue` / `EvalExpr.glue` render the binary `E-GLUE`
    transition; see `spec/TERM_LANGUAGE.md` §2). `StateExpr.hgp`, `lift`,
    `twoblock`, and `concat` are the four typed constructors admitted
    2026-11-11, with rules `EvalExpr.hgp`, `lift`, `twoblock`, and `concat`
    (issue #370). `StateExpr.product`, `double`, `balanced`, `tanner`, and
    `tile` are the five admitted the same day by issue #369, with rules of
    the same names (issue #407).
  - `Constructors.lean`: the state updates of the nine typed constructors,
    as the retained display of their natural rows (`constructedState`,
    `hgpState`, `liftState`, `twoblockState`, `concatState`,
    `productState`, `doubleState`, `balancedState`, `tannerState`,
    `tileState`).
  - `ConstructorWellFormedness.lean`: the retained display is a sequence of
    additions, so natural rows with pairwise even overlap give a
    well-formed state (`wf_constructedState`); `n` for the four.
  - `ConstructorOrthogonality.lean`: the overlap for `L-HGP`, proved for
    every input (`hgp_naturalOrthogonal`, `evalExpr_hgp_wf`);
    `stateK_of_wf`.
  - `ConstructorOverlap.lean`: the overlap for `L-LIFTED`,
    `L-GROUP-ALGEBRA`, and `A-CONCAT` (issue #482):
    `lift_naturalOrthogonal` and `twoblock_naturalOrthogonal` for every
    group and every algebra input, and `concat_naturalOrthogonal` for
    well-formed factors and typed blocks and representatives. Their
    well-formedness theorems (`evalExpr_lift_wf`, `evalExpr_twoblock_wf`,
    `evalExpr_concat_wf`) take no hypothesis.
  - `ConstructorRank.lean`: `k` of a constructed state from the natural
    rows, with no hypothesis (`stateK_constructedState`); the rank lemmas
    for mask lists it rests on; and `k = 2 k_C` for `A-DOUBLE` with the
    empty wiring (`doubleState_empty_k`, issue #483).
  - `ConstructorRankTyped.lean`: `k = 2(ℓ - rank[L(a) | L(b)])` for
    `L-GROUP-ALGEBRA` on every input (`twoblockState_k_closed`), and
    `k = k_O` for `A-CONCAT` under the hypothesis that the display retains
    every natural row (`concatState_k_of_retention`). The closed forms for
    `L-HGP` and `A-PRODUCT` are not proved.
  - `ConcatRetention.lean`: the `A-CONCAT` display retains every natural
    row (`concatState_rows_length`), so `k = k_O` (`concatState_k_closed`,
    `evalExpr_concat_k`), for well-formed factors and typed blocks and
    representatives (issue #505). It rests on the independence of the
    natural rows of each sector (`vecIndep_concat`), on the independence of
    the displayed rows of a well-formed state (`vecIndep_sectorRows`), and
    on the general statement that a constructed state with independent
    natural rows displays all of them
    (`constructedState_rows_length_of_indep`).
  - `BalancedOverlap.lean`: the pairwise even overlap for `L-BALANCED` on
    every typed input (`balanced_naturalOrthogonal`), so every evaluation
    yields a well-formed state with no hypothesis
    (`evalExpr_balanced_wellFormed`, issue #501). It carries the group
    action of exponent tuples (`actF`, `actF_gadd`, `actF_gneg`), the
    invariance of an equivariant matrix (`matEntry_actF`), and the least
    pair of an orbit (`pairRep_mem`, `pairRep_act`).
  - `ConstructorRankNatural.lean`: `k` of `L-BALANCED`, `L-TANNER`, and
    `L-TILE` as `n` minus the ranks of the two matrices of natural rows
    (`balancedState_k_closed`, `tannerState_k_closed`,
    `tileState_k_closed`, issue #501). These are instances of
    `stateK_constructedState`, not formulas in the input parameters.
  - `SplitCommand.lean`: the separating deletion of
    `design/E_SPLIT_PROPOSAL.md` (issue #546) as the sequence of deletions
    `splitCommand`, with no constructor added and no operation admitted. Its
    applicability on a well-formed state (`eval_splitCommand_iff`),
    `k' = k + |R|` (`stateK_of_eval_split`), the non-increase of each sector
    distance (`exactDistanceExt_split_le`), the separation of the child
    (`separated_deleteAll`), and the inverse law against `E-GLUE` up to the
    growth of `used` (`deleteAll_glueState_rows`, `deleteAll_glueState_used`).
  - `ConstructorAssembly.lean`: the five constructors of issue #369. The
    overlap for `A-PRODUCT`, proved for every pair of well-formed factors
    (`product_naturalOrthogonal`, `evalExpr_product_wf`); well-formedness
    for `A-DOUBLE`, `L-TANNER`, and `L-TILE` from the commutation premise
    of their rules; the well-formedness theorem of `L-BALANCED`, which
    takes the overlap as a hypothesis (the overlap is proved in
    `BalancedOverlap.lean`); `n` for the five. Also
    `L-NESTED-CSS` (issue #445): well-formedness from the premise of its
    rule (`evalExpr_nested_wf`) and `n` (`evalExpr_nested_n`).
    `L-MAPPING-CONE` (issue #569): well-formedness from the premise of its
    rule (`evalExpr_cone_wf`) and `n` (`evalExpr_cone_n`), plus the rank
    statement `evalExpr_cone_k`.
  - `ConstructorInstances.lean`: generated by
    `machine/experiments/constructor_lean_instances.py`. Instances of the
    eleven constructors whose Lean states equal the consumer's, by kernel
    `decide`, and `nested_steane_eq_tanner`, the equality of the
    `L-NESTED-CSS` and `L-TANNER` states on the Steane instance.
  - `Invariants.lean` / `WellFormedness.lean` — well-formedness (I1–I5).
  - `Soundness.lean` — annotated-judgment soundness metatheorem.
  - `TermSoundness.lean` — the metatheorem over the evaluation of a closed
    term: `Trace` is the chain a command unfolds through, one state per
    primitive step, and `judgment_soundness_of_term` needs no chain
    hypothesis (issue #425).
  - `ExpandedSoundness.lean` — annotated-term soundness over the expanded
    operation set: the models predicate `ExtModels` / `TermModels` over
    `ExtNat = ℕ ∪ {+∞}`, the metatheorems `ext_judgment_soundness` and its
    `_exact`, `_exact_uncertified`, and `_exact_admissible` instances, seam-
    certificate equality retained as `SeamCertSound` with the `AdmissibleSeam`
    discharge, and three worked closed-term derivations (issue #533). It is the
    expanded-system counterpart of `Soundness.lean` / `TermSoundness.lean`;
    the two derivation systems are documented in their headers.
  - `Transport.lean` — judgment transport through sequences, including the
    W13 refutation shape and its derivation-level instance for the
    generator-referencing claim `Ann.gen` (issue #340), with the
    input-display source rule, the graft rows, and the seam condition for
    transporting the source rule through a sequence (issue #368), and the
    Gate 6 rows `genExtend`, `genExtendMint`, `genPeel`, `genPuncture`,
    `genHadamard`, `genRebase`, and `genRebaseMint` with refusals
    `not_derivable_gen_of_peeled`, `not_derivable_gen_of_punctured`,
    `not_derivable_gen_of_punctured_id`, and `not_derivable_gen_of_rebased`,
    plus worked instances for all five Gate 6 commands (issues #424, #534).
  - `SeamChains.lean` — the seam condition on every chain of single
    (non-sequence) steps and every command `Trace`: at every position the
    claim of every displayed row is derivable (`derives_gen_of_displayed`),
    so `SeamRowsDerived` holds on every `StepChain` (`seamRowsDerived_of_stepChain`,
    `seamRowsDerived_of_prefix_stepChain`, `stepChain_append`) and on every
    command evaluation trace (`Trace.stepChain`, `seamRowsDerived_of_trace`,
    `Derives.shift_gen_of_trace`, `derives_gen_iff_displayed_of_trace`), with
    a worked three-step Gate 6 seam chain (issues #424, #489, #534).
  - `PricedInterval.lean` — priced interval transport.
  - `Gate6Soundness.lean`: the Gate 6 interval transformers of
    `spec/OPERATIONAL_SEMANTICS.md` §4.32, their soundness and monotonicity
    conditional on the per-cell distance relations (for `E-PEEL`, the three
    §4.28 relations and the two price cells of issue #331 through `Hyp`),
    `E-GLUE` as a closed term, and the rebase and Hadamard relations for the
    exact distance. Audited by `AxiomAudit.lean` since 2026-11-10.
  - `ExactPeel.lean`: the three §4.28 peel relations for the exact distance
    (`exactDist_peel_relations`, `peel_transformer_sound_exact`) and the
    `k = 0` reading `hk0` (`exactDist_k0`: a well-formed state with no
    logical qubit has no logical operator), issue #338. The positional
    vector operations `dropAt`, `insertAt`, and `entryAt` live here.
  - `Gate6Exact.lean`: `gate6_interval_soundness` instantiated with the
    exact distance (`gate6_interval_soundness_exact`, with no distance
    hypothesis since issue #367), and the `glueLedger` transformer on the
    `E-GLUE` constructor's update (`glue_state_transformer_sound`,
    `glue_expr_sound`, `glue_expr_sound_exact`), issue #339. The glue
    statement keeps the seam certificate's equality and the factors'
    well-formedness as premises. The closed-term reading of `E-GLUE` has
    the same instance (`glue_transformer_sound_at`,
    `glue_transformer_sound_exact`, `glue_term_sound_exact`), issue #406.
  - `ExactDirectSum.lean`: the direct-sum law for the exact distance on
    disjoint namespaces (`exactDist_directSumState`), issue #367.
  - `ExactPermute.lean`: the exact distance does not depend on the order of
    the namespace (`exactDist_perm`), issue #367.
  - `ExactGraft.lean`: the two unpriced §4.13 graft relations for the exact
    distance (`exactDist_graft_relations`), issue #367.
  - `DualityAdjunction.lean`: the classical `puncture ⊣ shorten` Galois
    connections (`zeroExtend_adj_shorten`, `puncture_adj_pullDrop`), the
    antitone dual-code Galois connection (`sub_dualCode_iff_symm`), the
    pointwise duality identity $P_i(C)^\perp = S_i(C^\perp)$
    (`dualCode_puncture_iff_shorten_dualCode`,
    `puncture_dualCode_sub_dualCode_shorten`), and the sector-swap
    involution and conjugation laws $H(m_\sigma(C)) = m_{\bar\sigma}(H(C))$
    across the kernel and Gate 6 state updates (`swapState_deleteState`,
    `swapState_addState`, `swapState_directSumState`, `swapState_glueState`,
    `swapState_peelState`, `swapState_punctureState`,
    `swapState_hadamardState`, `swapState_rebaseState`,
    `swapState_extendState`, `swapState_graftState`), issue #518.
  - `ExactGlue.lean`: Claim 1 of §4.33 for the glued state (`glue_claim1`),
    the lower bound `glue_exactDistance_ge_min`, and two lemmas toward
    Claim 2 (`phi_well_defined`, `seam_checks_commute_split`), issue #366.
  - `ExactGluePairs.lean`: steps 3 and 4 of Claim 2 of §4.33 on
    representatives, issue #395. `glue_normalizer_iff` reads the
    normalizer of the glued state as the pairs in `GlueK`,
    `glue_stabilizer_iff` reads its stabilizer as the pairs in `GlueW`, and
    `glueW_subset_glueK`, `glueK_xor`, `glue_class_eq_iff`, and
    `glue_logical_iff` give the bijection between the logical classes of
    the glued state and the classes of `GlueK` modulo `GlueW`. No quotient
    type is built.
  - `ExactGlueDistance.lean`: step 5 of Claim 2 of §4.33, issue #396.
    `classWeight` is the least weight of a representative of a class
    (`classWeight_attained`, `classWeight_congr`, `classWeight_of_span`).
    `glue_exactDistance?_eq_some_iff` and `glue_exactDistance?_eq_none_iff`
    state the class-pair distance formula for `exactDistance?` of a
    well-formed glued state: the distance is the least sum of two class
    weights over the pairs in `GlueK` outside `GlueW`, and `none` when
    there is no such pair.
  - `ExactGlueSurvival.lean`: the survival statement of §4.31 and §4.33,
    issue #397. `SurvivesA` and `SurvivesB` say that a factor logical,
    extended by zero, is a logical of the glued state. `survivesA_iff` and
    `survivesB_iff` are the criterion (even overlap with every seam check
    of the opposite sector, and not spanned by the glued rows of its own
    sector), `survivesA_congr` and `survivesB_congr` show survival depends
    only on the factor class, `glue_exactDistance_eq_min_of_survivesA` and
    its `B` form are the instance-wise equality, and
    `glue_survivor_of_min_logical` is its converse. No statement says that
    a seam certificate guarantees a survivor.
  - `LogicalWitness.lean`: the logical-witness field of
    `spec/STATE_MODEL.md` §1 as a definition outside `CodeState`, and its
    transport under `E-GLUE`, issue #439. `glueLog` keeps the factor
    entries that survive (`mem_glueLog_iff_survives`) and is sound
    (`glueLog_sound`). `glueExact_iff_carriesMin` proves that, for sound,
    complete, and tight factor fields, the glued state has a logical of
    weight `min (d_σ a) (d_σ b)` iff the transported field has an entry of
    that weight, and `family_glueExact_iff` is the same statement over an
    arbitrary family of glues. `glueLog_not_onePerClass` and
    `glueLog_empty_instance` pin a glue whose transport holds two entries
    of one class and the §4.33 counterexample, whose transport is empty. No
    statement says that the admissible seams of §2e form a family on which
    a minimum-weight entry is carried.
  - `WitnessFields.lean`: the two future-`Π` fields of
    `spec/STATE_MODEL.md` §1a and their transport, issue #440.
    `transportLog` keeps the candidates that are logicals of the child, one
    of least weight per class; it is sound (`transportLog_sound`), has one
    entry per class (`transportLog_onePerClass`), and loses no class and no
    minimum among the candidates (`transportLog_keeps`). `glueField` is the
    `E-GLUE` instance and `carriesMin_glueField_iff` relates it to
    `glueLog`. `BdLabel` and `transportBd` are the boundary-label field,
    `transportBd_names_class` couples the two fields, and
    `bdLabel_extendA_valid_iff` and its `B` form show that a factor label
    crosses a seam exactly when its representative survives. The candidate
    lists of the other transitions and the hand derivations of §1a are not
    mechanized.
  - `AdmissibleSeamFamily.lean`: the admissible-seam family guarantee for
    `E-GLUE` (`spec/OPERATIONAL_SEMANTICS.md` §4.31, `design/ADMISSIBLE_SEAM_FAMILY.md`,
    issue #439): `AdmissibleSeam` and `HasMinLogical` package survival of
    minimum-weight factor representatives across the seam, `admissible_carriesMin`
    derives `CarriesMin`, and `admissible_family_exactDistance_eq_min` derives
    the family-level `exactDistance` equality.
  - `GlueExtraction.lean`: completion of the CSS-level algebraic mechanization
    of `E-GLUE` (`spec/OPERATIONAL_SEMANTICS.md` §4.31, §4.33, issue #536):
    `evalExpr_glue_iff_evalTerm_glueCommand`, `wf_glueState_of_eval_glueCommand`,
    and `stateK_glueState_add_seams` (equivalence of `EvalExpr.glue` with
    `glueCommand`, deriving output well-formedness and `k` drop);
    `reExposedVectors_eq_nil`, `wRe?_eq_none`, `glue_exactDistance?_ge_min`, and
    `glue_theorem4_lower_bound` ($w_{\mathrm{re},\sigma} = +\infty$ and the
    Theorem 4 / claim 7.4 bound in `Option Nat`); `phiSeam_congr`,
    `phiSeam_linear`, `glue_exactDistance?_ge_add_of_no_pure_survivor`, and
    `glue_universal_min_equality_false` (Claim 2 Step 1, Consequence (iii), and
    issue #398 refutation); and `admissibleSeam_exactDistance?_eq_min`,
    `admissible_carriesMin_glueField`, `admissible_family_glueField_exact`,
    `glue_expr_sound_exact_of_admissible`, and
    `glue_term_sound_exact_of_admissible` (`Option Nat` / `glueField` /
    `Gate6Exact` end-to-end discharge from `AdmissibleSeam`). The geometric
    implication from planar move-word equality `w(c_A) = w(c_B)` to
    `AdmissibleSeam` remains outside the CSS state model.
  - `CertificateChecker.lean`: the mechanized certificate checker of issue
    #371. `checkCertificate` accepts a kill certificate for a sector
    distance lower bound; `checkCertificate_sound`,
    `certificate_lower_bound` (and its `ExtNat` and `Nat` readings), and
    `certificate_equality` prove that acceptance implies the bound, and with
    a checked witness the exact value, for the exact distance.
  - `CertificateInstances.lean`: generated by
    `machine/experiments/certificate_lean_instances.py`. Per-state theorems
    for the `W3` result state and the pinned `[[10,2,3]]` parent, with every
    acceptance premise discharged by kernel `decide`.
  - `ExactDistance.lean`: exact sector distance over F₂, in `Nat` with the
    sentinel `|Q| + 1`, in `Option Nat` (`exactDistance?`, `none` for `+∞`),
    and in the S2 domain `ExtNat` (`exactDistanceExt`), with the sentinel
    proved exact and its order proved faithful on a common namespace.
  - `KernelObligations.lean` — kernel obligation lemmas (determinism,
    associativity, direct-sum laws, frame law, cross-sector permutation,
    partial-inverse clauses).
  - `RanksFit.lean` — the dimension bound behind deletion/addition k-cells.
  - `GraftWellFormedness.lean` — well-formedness for E-GRAFT.
  - `Rebase*.lean` — presentation-rebase rank preservation.
  - `Fixtures.lean` / `FixtureReplay.lean` / `FixtureEvalReplay.lean` —
    fixture transcription and replay checks.
  - `WellFormedBool.lean` — boolean well-formedness helpers.
  - `Property.lean`, `Judgment.lean`, `Interval.lean`, `Refinement.lean`,
    `MaskRank.lean`, `MixSupport.lean` — supporting definitions.
  - `AxiomAudit.lean`: build-time check of the trust basis below.
- `CodeCalculus.lean` is the entry point imported by `lake build`.

## Extra modules

`lean/extra/` holds modules that are **not** part of the default `lake build`
target and are **not** covered by `AxiomAudit.lean`:

- `ClosedK.lean`: closed forms for `stateK` of `L-HGP` and `A-PRODUCT`
  (issue #483), derived from the four rank axioms recorded in `AXIOMS.md`
  (`hgp_rankX`, `hgp_rankZ`, `product_rankX`, `product_rankZ`); the
  arithmetic that combines the ranks is proved.
- `Retention.lean`: no declaration. The `A-CONCAT` retention statement it
  held as an axiom is proved in `CodeCalculus/ConcatRetention.lean`
  (issue #505). The file remains so that `lake build Retention` names a
  target.

Build them explicitly with `lake build ClosedK Retention`. Neither CI nor
the audit covers them, so a broken statement there will not fail the
default build.

## Status

Mechanization is partial and ongoing. Modules marked with `sorry` are
incomplete; the build is expected to be green (`0 sorry` on `main`), and
`CodeCalculus/AxiomAudit.lean` fails the build on a `sorry`. Gate 0
(record completeness) and Gate 1 (formal syntax) are ratified; Gates 2–7 are
unchecked. See `spec/GATES.md`.

## Trust basis

The development is not uniformly kernel-checked, and the axioms it rests on
are recorded here. `CodeCalculus/AxiomAudit.lean` checks the three statements
below when the library is built, so `lake build` fails if one of them stops
holding; its summary line lists the constants that depend on
`Classical.choice`.

- `Classical.choice` is confined to the noncomputable denotation. The only
  constants whose axioms include it are `denoteExpr` and `denote`
  (`CodeCalculus/Eval.lean`, both `open Classical`), their generated
  auxiliaries, and the theorems stated about them (`denote_eval`,
  `denote_some_eval`, `eval_denote`, `denoteExpr_eval`,
  `denoteExpr_some_eval`, `eval_denoteExpr`, and `denote_seq_assoc`). Every
  other theorem depends on `propext` and `Quot.sound` at most. The
  core-library facts whose library proofs are classical are restated with
  choice-free proofs in `CodeCalculus/ChoiceFree.lean`, and the identifier
  enumeration is rendered and parsed as `List Char` (`identifierCharsAt?`,
  `rankOfChars?`), because every `String` inspection in Lean core depends on
  `Classical.choice` through UTF-8 decoding.
- `native_decide` is used at one site, `rankOf_identifierAt`
  (`CodeCalculus/State.lean`), which therefore depends on the per-theorem
  axiom `rankOf_identifierAt._native.native_decide.ax_1_1`: the statement is
  checked by the Lean compiler, not by the kernel. The v0.1 decision (issue
  #195, 2026-10-28) accepts this site. The fixture replays
  (`FixtureReplay.lean`, `FixtureEvalReplay.lean`) are kernel `decide`
  throughout.
- No constant depends on `sorryAx`.

Certificates (issue #371): the theorems of `CertificateInstances.lean` rest
on the kernel and on the definition of the exact distance. The certificate
producer and the generator that writes that module are Python and are not
trusted; a wrong certificate or a wrong translation fails `by decide` or
yields a true theorem about a different state term. That a state term is the
intended state is checked by reading (`spec/CLAIMS.md`, *Mechanized
checker*).

Capacity (H-4, issue #296, 2026-11-11): the five minting rules (`Eval.add`,
`Eval.graft`, `Eval.rebase`, `Eval.extend`, `EvalExpr.glue`) carry a capacity
premise over the finite enumeration (`MintsWithinCapacity`, `totalIdentifiers`
in `CodeCalculus/Eval.lean` and `State.lean`), so a transition that would mint
past the 70,000 names has no derivation, matching the Python consumer's
refusal; `eval_used_within_capacity` shows that evaluation never mints an
identifier outside the enumeration. `canonicalMint` itself stays total over
`Nat`; the refusal lives in the rules.

This is a qualification, not an evidence status: the evidence vocabulary of
`spec/CLAIMS.md` has no slot for it, and the obligation ledger keeps its
statuses and cites this section.
