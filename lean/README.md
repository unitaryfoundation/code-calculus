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
 2026-11-11, with rules `EvalExpr.hgp`, `lift`, `twoblock`, and `concat`. `StateExpr.product`, `double`, `balanced`, `tanner`, and
 `tile` are the five admitted the same day, with rules of
 the same names. `StateExpr.liftTable`, `twoblockTable`, and
 `balancedTable` are the productions of `L-LIFTED`, `L-GROUP-ALGEBRA`,
 and `L-BALANCED` with the group given by its multiplication table
 (`spec/OPERATIONAL_SEMANTICS.md` §4.44), with rules of the same names.
 - `Constructors.lean`: the state updates of the nine typed constructors,
 as the retained display of their natural rows (`constructedState`,
 `hgpState`, `liftState`, `twoblockState`, `concatState`,
 `productState`, `doubleState`, `balancedState`, `tannerState`,
 `tileState`).
 - `CayleyGroups.lean`: the definitions of the three group constructors
 over an arbitrary finite group: the structure `FiniteGroup`, the left
 and right regular rows, the right and left actions, and the states
 `cayleyTwoblockState`, `cayleyLiftState`, and `cayleyBalancedState`.
 Definitions only. They sit ahead of `Eval.lean` so that the evaluation
 relation can name them.
 - `CayleyTables.lean`: a group as raw data. `tableGroupTyped` is the
 typing check of a multiplication table (nonempty and square with
 entries in range, a two-sided identity, two-sided inverses,
 associativity), `tableGroup` the `FiniteGroup` of a table that passes
 it, and `tableLiftState`, `tableTwoblockState`, and
 `tableBalancedState` the states of the three table productions. The
 actions of `balancedTable` are one permutation per group element
 (`tableRightActionTyped`, `tableLeftActionTyped`,
 `tableEquivariantTyped`). A group given by permutation generators has
 no production: it is the table `gensTable d gens`, which the table
 productions carry. No theorem says that `gensTable` is the table of the
 generated group, and the extension of an action from the generators to
 the group is not transcribed.
 - `ConstructorWellFormedness.lean`: the retained display is a sequence of
 additions, so natural rows with pairwise even overlap give a
 well-formed state (`wf_constructedState`); `n` for the four.
 - `ConstructorOrthogonality.lean`: the overlap for `L-HGP`, proved for
 every input (`hgp_naturalOrthogonal`, `evalExpr_hgp_wf`);
 `stateK_of_wf`.
 - `ConstructorOverlap.lean`: the overlap for `L-LIFTED`,
 `L-GROUP-ALGEBRA`, and `A-CONCAT`:
 `lift_naturalOrthogonal` and `twoblock_naturalOrthogonal` for every
 group and every algebra input, and `concat_naturalOrthogonal` for
 well-formed factors and typed blocks and representatives. Their
 well-formedness theorems (`evalExpr_lift_wf`, `evalExpr_twoblock_wf`,
 `evalExpr_concat_wf`) take no hypothesis. The same over an arbitrary
 finite group (`cayleyLift_naturalOrthogonal`,
 `cayleyTwoblock_naturalOrthogonal`), so every evaluation of a table
 production yields a well-formed state (`evalExpr_liftTable_wf`,
 `evalExpr_twoblockTable_wf`), with `n` (`evalExpr_liftTable_n`,
 `evalExpr_twoblockTable_n`).
 - `ConstructorRank.lean`: `k` of a constructed state from the natural
 rows, with no hypothesis (`stateK_constructedState`); the rank lemmas
 for mask lists it rests on; and `k = 2 k_C` for `A-DOUBLE` with the
 empty wiring (`doubleState_empty_k`).
 - `ConstructorRankTyped.lean`: `k = 2(ℓ - rank[L(a) | L(b)])` for
 `L-GROUP-ALGEBRA` on every input (`twoblockState_k_closed`), and
 `k = k_O` for `A-CONCAT` under the hypothesis that the display retains
 every natural row (`concatState_k_of_retention`). The closed forms for
 `L-HGP` and `A-PRODUCT` are proved in `ClosedK.lean`.
 - `ConcatRetention.lean`: the `A-CONCAT` display retains every natural
 row (`concatState_rows_length`), so `k = k_O` (`concatState_k_closed`,
 `evalExpr_concat_k`), for well-formed factors and typed blocks and
 representatives. It rests on the block-projection corollary
 (`combineRows_take_drop`, from `combineRows_map_additive` and
 `additive_blockAt`), on the inner and outer independence theorems
 (`vecIndep_concatInner`, `vecIndep_concat`), on the independence of
 the displayed rows of a well-formed state (`vecIndep_sectorRows`), and
 on the general statement that a constructed state with independent
 natural rows displays all of them
 (`constructedState_rows_length_of_indep`).
 - `BalancedOverlap.lean`: the pairwise even overlap for `L-BALANCED` on
 every typed input (`balanced_naturalOrthogonal`), so every evaluation
 yields a well-formed state with no hypothesis
 (`evalExpr_balanced_wellFormed`). It carries the group
 action of exponent tuples (`actF`, `actF_gadd`, `actF_gneg`), the
 invariance of an equivariant matrix (`matEntry_actF`), and the least
 pair of an orbit (`pairRep_mem`, `pairRep_act`). The same over an
 arbitrary finite group with a right and a left action
 (`cayleyBalanced_naturalOrthogonal`), so every evaluation of
 `balancedTable` yields a well-formed state
 (`evalExpr_balancedTable_wf`), with `n` (`evalExpr_balancedTable_n`).
 - `RankNullity.lean`: the rank is monotone in the span
 (`rankBitmasks_le_of_span`); rank and nullity for an additive map
 (`rank_nullity`); the combination of a mask list by a coefficient mask
 (`comb`) and a list spanning its kernel (`kerList`, `rank_kerList`).
 - `TensorRank.lean`: the tensor of two masks (`tens`), its bits and
 slices, and the rank of a family of tensors as the product of the ranks
 (`rank_tens`).
 - `HgpRank.lean`: row rank equals column rank (`rank_colMasks`), and the
 rank of the two-block tensor family `(A_s ⊗ e_t, e_s ⊗ D_t)`
 (`rank_hgRows`).
 - `MaskBlocks.lean`: masks of Boolean lists over index pairs as tensors
 with unit masks, and the two placements of a pair of blocks.
 - `ProductRank.lean`: the rank of the natural rows of a tensor product
 of two complexes (`rank_prodRows`), by counting the dependencies among
 the rows.
 - `ClosedK.lean`: the ranks of the natural matrices of `L-HGP`
 (`hgp_rankX`, `hgp_rankZ`) and of `A-PRODUCT` (`product_rankX`,
 `product_rankZ`), and the closed forms
 `k = k_1 k_2 + k_1ᵀ k_2ᵀ` (`hgpState_k_closed`, `evalExpr_hgp_k`) and
 `k = k_A k_B` (`productState_k_closed`, `evalExpr_product_k`). The four
 rank statements were axioms of `lean/extra/ClosedK.lean` until
 2026-11-24.
 - `ConstructorRankNatural.lean`: `k` of `L-BALANCED`, `L-TANNER`, and
 `L-TILE` as `n` minus the ranks of the two matrices of natural rows
 (`balancedState_k_closed`, `tannerState_k_closed`,
 `tileState_k_closed`). These are instances of
 `stateK_constructedState`, not formulas in the input parameters. For
 `L-TANNER` and `L-TILE`, the counting bound: `k` is at least `n` minus the
 number of natural rows (`tannerState_k_ge`, `tileState_k_ge`), with
 equality iff the natural rows of each sector are independent
 (`tannerState_k_of_indep`, `tileState_k_of_indep`,
 `tannerState_k_eq_counting_iff`, `tileState_k_eq_counting_iff`, and the
 `evalExpr_*` forms). For `L-TANNER`, the local-code rank bound
 (`tannerState_k_ge_localRank`, `evalExpr_tanner_k_ge_localRank` — no weaker
 than `tannerState_k_ge`, and tighter when a sector with a view has redundant
 local checks) and its exact closed form on vertex-disjoint views
 (`tannerState_k_of_disjoint_views`, `evalExpr_tanner_k_of_disjoint_views`).
 Finally, the formal no-go theorems (`tanner_k_not_determined_by_params`,
 `tile_k_not_determined_by_params`) proving that no function of
 `(n, L_X, L_Z, |V_X|, |V_Z|)` equals `stateK` on all valid `L-TANNER`
 evaluations and no function of the tile list, qubit count, placement count,
 and two kept-row counts equals `stateK` on all valid `L-TILE` evaluations
 (closed forms in richer invariants of the views or placements are not
 excluded).
 - `SplitCommand.lean`: the admitted `E-SPLIT` separating deletion
 (`Command.split` / `Eval.split` in `Term.lean` and `Eval.lean`, admitted
 2026-11-25, `spec/OPERATIONAL_SEMANTICS.md` §4.48) and its factorization into
 the deletion sequence `splitCommand` (`eval_split_iff_eval_splitCommand`).
 Covers applicability on a well-formed state (`eval_splitCommand_iff`),
 `k' = k + |R|` (`stateK_of_eval_split`, `stateK_of_eval_split_cmd`),
 non-increase of each sector distance (`exactDistanceExt_split_le`,
 `exactDistanceExt_split_cmd_le`), separation of the child
 (`separated_deleteAll`, `separated_of_eval_split`), the partial inverse law
 against `E-GLUE` up to the growth of `used` (`deleteAll_glueState_rows`,
 `deleteAll_glueState_used`, `eval_split_glueState`), the block-minimum
 decomposition (`exactDistanceExt_separated_eq_min`), the exact price
 decomposition (`exactDistanceExt_split_eq_min_price`), and the unpriced and
 `split_block_intervals`-priced interval transformers
 (`splitLedger_unpriced_sound`, `splitLedger_priced_sound`,
 `splitLedger_priced_monotone`). Well-formedness preservation (`wf_deleteAll`)
 lives in `WellFormedness.lean`; `Derives.genSplit` / `not_derivable_gen_of_split`
 and worked instances live in `Soundness.lean`, `Transport.lean`,
 `SeamChains.lean`, and `ExpandedSoundness.lean`; sector-swap conjugation
 (`swapState_deleteAll`) lives in `DualityAdjunction.lean`.
 - `ConstructorAssembly.lean`: the five constructors of. The
 overlap for `A-PRODUCT`, proved for every pair of well-formed factors
 (`product_naturalOrthogonal`, `evalExpr_product_wf`); well-formedness
 for `A-DOUBLE`, `L-TANNER`, and `L-TILE` from the commutation premise
 of their rules; the well-formedness theorem of `L-BALANCED`, which
 takes the overlap as a hypothesis (the overlap is proved in
 `BalancedOverlap.lean`); `n` for the five. Also
 `L-NESTED-CSS`: well-formedness from the premise of its
 rule (`evalExpr_nested_wf`) and `n` (`evalExpr_nested_n`).
 `L-MAPPING-CONE`: well-formedness from the premise of its
 rule (`evalExpr_cone_wf`) and `n` (`evalExpr_cone_n`), plus the rank
 statement `evalExpr_cone_k`.
 - `ConstructorInstances.lean`: generated by
 `machine/experiments/constructor_lean_instances.py`. Instances of the
 eleven constructors whose Lean states equal the consumer's, by kernel
 `decide`, and `nested_steane_eq_tanner`, the equality of the
 `L-NESTED-CSS` and `L-TANNER` states on the Steane instance. For the
 table productions: `twoblock_s3`, `lift_s3`, and `balanced_s3` over
 `S_3`, two inputs the consumer refuses that fail the Lean typing checks
 (`nonassociative_table_refused`, `balanced_s3_left_action_refused`),
 and `s3_gens_table`, the equality of `gensTable` with the consumer's
 table on two generators of `S_3`.
 - `Invariants.lean` / `WellFormedness.lean` — well-formedness (I1–I5).
 - `Soundness.lean` — annotated-judgment soundness metatheorem.
 - `TermSoundness.lean` — the metatheorem over the evaluation of a closed
 term: `Trace` is the chain a command unfolds through, one state per
 primitive step, and `judgment_soundness_of_term` needs no chain
 hypothesis.
 - `ExpandedSoundness.lean` — annotated-term soundness over the expanded
 operation set: the models predicate `ExtModels` / `TermModels` over
 `ExtNat = ℕ ∪ {+∞}`, the metatheorems `ext_judgment_soundness` and its
 `_exact`, `_exact_uncertified`, and `_exact_admissible` instances, seam-
 certificate equality retained as `SeamCertSound` with the `AdmissibleSeam`
 discharge, structural carry rows for `Command.cnotSwap` and all seventeen
 admitted `StateExpr` constructors (`instCnotSwap*`, `instCone*`,
 `instEmpty*`, `instFree*`, `instPullbackN`, `instPushoutN`,
 `instPairPartitionN`, `instPpScaleN`, `instLiftTableN`, `instTwoblockTableN`,
 `instBalancedTableN`), and worked closed-term derivations. For
 `Command.cnotSwap`, `Eval.cnotSwap` carries `EncodingWellFormed s'` as a
 premise, so `instCnotSwapWF` covers it through the well-formedness premise its
 transition carries (a premise restatement via `wf_of_eval_all`) and
 `eval_cnotSwap_k` relies on that premise; preservation of I1–I5 under an
 invertible column map `U` is hand-derived in `spec/OPERATIONAL_SEMANTICS.md`
 §4.42 and not mechanized. It is the
 expanded-system counterpart of `Soundness.lean` / `TermSoundness.lean`;
 the two derivation systems are documented in their headers.
 - `ColumnCnot.lean` — mechanization of `Command.cnotSwap` (`C-COLUMN-CNOT`,
 `spec/OPERATIONAL_SEMANTICS.md` §4.42; issue #657): identifier retention,
 determinism (`eval_cnotSwap_unique`), skip identity (`eval_cnotSwap_skip_left`,
 `eval_cnotSwap_skip_right`), sequence associativity (`eval_cnotSwap_seq_assoc`),
 positive CNOT/SWAP instances, singular/wrong-shape/wrong-size refusals (both
 malformed and singular matrices fail the single `cnotMatrix_ok` premise), and a
 worked `TermModels` derivation (`termModels_cnotSwap_example`). As with the
 non-rebase Gate 6 transitions, `Eval.cnotSwap` carries `EncodingWellFormed s'`
 as a premise, so `wf_of_eval_all` and `instCnotSwapWF` cover `Command.cnotSwap`
 through the well-formedness premise its transition carries (a premise
 restatement) and `eval_cnotSwap_k` relies on that premise; preservation of
 I1–I5 under invertible `U` remains the hand derivation of §4.42 and is not
 mechanized.
 - `Transport.lean` — judgment transport through sequences, including the
 W13 refutation shape and its derivation-level instance for the
 generator-referencing claim `Ann.gen`, with the
 input-display source rule, the graft rows, and the seam condition for
 transporting the source rule through a sequence, and the
 Gate 6 rows `genExtend`, `genExtendMint`, `genPeel`, `genPuncture`,
 `genHadamard`, `genRebase`, and `genRebaseMint` with refusals
 `not_derivable_gen_of_peeled`, `not_derivable_gen_of_punctured`,
 `not_derivable_gen_of_punctured_id`, and `not_derivable_gen_of_rebased`,
 plus worked instances for all five Gate 6 commands.
 - `SeamChains.lean` — the seam condition on every chain of single
 (non-sequence) steps and every command `Trace`: at every position the
 claim of every displayed row is derivable (`derives_gen_of_displayed`),
 so `SeamRowsDerived` holds on every `StepChain` (`seamRowsDerived_of_stepChain`,
 `seamRowsDerived_of_prefix_stepChain`, `stepChain_append`) and on every
 command evaluation trace (`Trace.stepChain`, `seamRowsDerived_of_trace`,
 `Derives.shift_gen_of_trace`, `derives_gen_iff_displayed_of_trace`), with
 a worked three-step Gate 6 seam chain.
 - `PricedInterval.lean` — priced interval transport.
 - `Gate6Soundness.lean`: the Gate 6 interval transformers of
 `spec/OPERATIONAL_SEMANTICS.md` §4.32, their soundness and monotonicity
 conditional on the per-cell distance relations (for `E-PEEL`, the three
 §4.28 relations and the two price cells through `Hyp`),
 `E-GLUE` as a closed term, and the rebase and Hadamard relations for the
 exact distance. Audited by `AxiomAudit.lean` since 2026-11-10.
 - `ExactPeel.lean`: the three §4.28 peel relations for the exact distance
 (`exactDist_peel_relations`, `peel_transformer_sound_exact`) and the
 `k = 0` reading `hk0` (`exactDist_k0`: a well-formed state with no
 logical qubit has no logical operator). The positional
 vector operations `dropAt`, `insertAt`, and `entryAt` live here.
 - `SplitHadamard.lean`: the split-subset `E-LOCAL-HADAMARD` (issue
 #571) for the exact distance. Each child sector distance is at least the
 parent's full distance (`exactDistance_split_ge`, needing no guard), and
 under the splitting guard the full distance is unchanged
 (`exactDistance_split_min`). Combined in `Option Nat` as
 `exactDist_splitHadamardState`, the `hsplit` premise of
 `gate6_interval_soundness`. The mechanized `splitLedger` transport floors
 each sector at `L.full.lower`, which is weaker than the consumer's
 `max(L.full.lower, min(ℓ_X, ℓ_Z))` (both are sound; the `min(ℓ_X, ℓ_Z)`
 floor is hand-derived in §4.27(b) and not mechanized in Lean). The proof
 rests on span facts about the canonical update, which reads rows in
 identifier order (`sortRowsByRank`) and is `≡`-input invariant
 (`splitHadamardState_equiv`): every child row is a piece of a parent row
 (`splitRow_origin`), every piece lies in the child span of its output
 sector (`piece_inSpan_child`), and the guard puts each inner piece in its
 own sector's span (`guard_inner`).
 - `Gate6Exact.lean`: `gate6_interval_soundness` instantiated with the
 exact distance (`gate6_interval_soundness_exact`, with no distance
 hypothesis), and the `glueLedger` transformer on the
 `E-GLUE` constructor's update (`glue_state_transformer_sound`,
 `glue_expr_sound`, `glue_expr_sound_exact`). The glue
 statement keeps the seam certificate's equality and the factors'
 well-formedness as premises. The closed-term reading of `E-GLUE` has
 the same instance (`glue_transformer_sound_at`,
 `glue_transformer_sound_exact`, `glue_term_sound_exact`).
 - `ExactDirectSum.lean`: the direct-sum law for the exact distance on
 disjoint namespaces (`exactDist_directSumState`).
 - `ExactPermute.lean`: the exact distance does not depend on the order of
 the namespace (`exactDist_perm`).
 - `ExactGraft.lean`: the two unpriced §4.13 graft relations for the exact
 distance (`exactDist_graft_relations`).
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
 `swapState_extendState`, `swapState_graftState`).
 - `ExactGlue.lean`: Claim 1 of §4.33 for the glued state (`glue_claim1`),
 the lower bound `glue_exactDistance_ge_min`, and two lemmas toward
 Claim 2 (`phi_well_defined`, `seam_checks_commute_split`).
 - `ExactGluePairs.lean`: steps 3 and 4 of Claim 2 of §4.33 on
 representatives. `glue_normalizer_iff` reads the
 normalizer of the glued state as the pairs in `GlueK`,
 `glue_stabilizer_iff` reads its stabilizer as the pairs in `GlueW`, and
 `glueW_subset_glueK`, `glueK_xor`, `glue_class_eq_iff`, and
 `glue_logical_iff` give the bijection between the logical classes of
 the glued state and the classes of `GlueK` modulo `GlueW`. No quotient
 type is built.
 - `ExactGlueDistance.lean`: step 5 of Claim 2 of §4.33.
 `classWeight` is the least weight of a representative of a class
 (`classWeight_attained`, `classWeight_congr`, `classWeight_of_span`).
 `glue_exactDistance?_eq_some_iff` and `glue_exactDistance?_eq_none_iff`
 state the class-pair distance formula for `exactDistance?` of a
 well-formed glued state: the distance is the least sum of two class
 weights over the pairs in `GlueK` outside `GlueW`, and `none` when
 there is no such pair.
 - `ExactGlueSurvival.lean`: the survival statement of §4.31 and §4.33. `SurvivesA` and `SurvivesB` say that a factor logical,
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
 transport under `E-GLUE`. `glueLog` keeps the factor
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
 `spec/STATE_MODEL.md` §1a and their transport.
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
 - `FuturePiFields.lean`: candidate sketch-refinement definitions and
 transport soundness proofs for the two proposed future-`Π` fields of
 `design/FUTURE_PI_FIELDS.md` (outside `CodeState`, not admitted to
 `spec/STATE_MODEL.md` §1a): `ConstructionRecord` (`Option ClosedTerm`,
 `constructionRecord_transportCmd_valid`,
 `constructionRecord_transportCmdPure_valid`, and constructor lifts
 `constructionRecord_directSum_valid`, `constructionRecord_glue_valid`,
 `constructionRecord_concat_valid`, `constructionRecord_product_valid`,
 `constructionRecord_double_valid`, `constructionRecord_ppScale_valid`)
 and `LogicalFrame` (`List FramePair` with canonical symplectic pairing
 `LogicalFrame.Dual`, automatic `LogField.OnePerClass` projection
 `frame_toLogField_onePerClass`, generic filter transport
 `transportFrame_wellFormed_of_dual`, and transition theorems
 `frame_wellFormed_deleteState`, `frame_wellFormed_addState`,
 `frame_wellFormed_rebaseState`, `frame_wellFormed_swapState`,
 `frame_wellFormed_directSumState`, `frame_wellFormed_glueState`, plus
 a kernel-checked `[[4, 2, 2]]` frame instance `frame422_wellFormed`).
 - `AdmissibleSeamFamily.lean`: the admissible-seam family guarantee for
 `E-GLUE` (`spec/OPERATIONAL_SEMANTICS.md` §4.31, `ADMISSIBLE_SEAM_FAMILY.md`): `AdmissibleSeam` and `HasMinLogical` package survival of
 minimum-weight factor representatives across the seam, `admissible_carriesMin`
 derives `CarriesMin`, and `admissible_family_exactDistance_eq_min` derives
 the family-level `exactDistance` equality.
 - `GlueExtraction.lean`: completion of the CSS-level algebraic mechanization
 of `E-GLUE` (`spec/OPERATIONAL_SEMANTICS.md` §4.31, §4.33):
 `evalExpr_glue_iff_evalTerm_glueCommand`, `wf_glueState_of_eval_glueCommand`,
 and `stateK_glueState_add_seams` (equivalence of `EvalExpr.glue` with
 `glueCommand`, deriving output well-formedness and `k` drop);
 `reExposedVectors_eq_nil`, `wRe?_eq_none`, `glue_exactDistance?_ge_min`, and
 `glue_theorem4_lower_bound` ($w_{\mathrm{re},\sigma} = +\infty$ and the
 Theorem 4 / claim 7.4 bound in `Option Nat`); `phiSeam_congr`,
 `phiSeam_linear`, `glue_exactDistance?_ge_add_of_no_pure_survivor`, and
 `glue_universal_min_equality_false` (Claim 2 Step 1, Consequence (iii), and its refutation); and `admissibleSeam_exactDistance?_eq_min`,
 `admissible_carriesMin_glueField`, `admissible_family_glueField_exact`,
 `glue_expr_sound_exact_of_admissible`, and
 `glue_term_sound_exact_of_admissible` (`Option Nat` / `glueField` /
 `Gate6Exact` end-to-end discharge from `AdmissibleSeam`). The geometric
 implication from planar move-word equality `w(c_A) = w(c_B)` to
 `AdmissibleSeam` remains outside the CSS state model.
 - `CertificateChecker.lean`: the mechanized certificate checker. `checkCertificate` accepts a kill certificate for a sector
 distance lower bound; `checkCertificate_sound`,
 `certificate_lower_bound` (and its `ExtNat` and `Nat` readings), and
 `certificate_equality` prove that acceptance implies the bound, and with
 a checked witness the exact value, for the exact distance.
 `checkPruneCertificate` accepts a pruning-tree certificate, which covers
 the vectors of weight below the bound by classes and is walked once;
 `checkPrune_sound`, `checkPruneCertificate_sound`, and the
 `pruneCertificate_` theorems prove the same four conclusions for it.
 - `CertificateInstances.lean`: generated by
 `machine/experiments/certificate_lean_instances.py`. Per-state theorems
 for the `W3` result state and the pinned `[[10,2,3]]` parent, with every
 acceptance premise discharged by kernel `decide`, and for a cyclic
 two-block code on 30 qubits, whose two sector distances are proved equal
 to 6 from pruning-tree certificates by `decide +kernel`. That term is
 not proved well-formed, because the kernel evaluation of `wellFormedBool`
 on it is too slow.
 - `Ingestion.lean`: external code ingestion (`spec/REPRESENTATION.md` §9).
 `presentationBinds` is the computable statement that a state is an
 ingestion of a matrix presentation; `presentationBinds_Q`,
 `presentationBinds_retained`, and `presentationBinds_span` read off that
 the qubits are `0, …, n − 1`, that every row of the state is a presented
 row, and that every presented row is in the span of the state's rows.
 - `IngestedInstances.lean`: generated by
 `machine/experiments/code_state_lean_instances.py`. The pinned
 `[[10,2,3]]` entry and a redundant presentation of the `[[8,2,2]]` toric
 code, each with its presentation literal, recorded binding hash,
 `_binds` theorem by kernel `decide`, and exact sector distances from
 checked certificates.
 - `ExactDistance.lean`: exact sector distance over F₂, in `Nat` with the
 sentinel `|Q| + 1`, in `Option Nat` (`exactDistance?`, `none` for `+∞`),
 and in the domain `ExtNat` (`exactDistanceExt`), with the sentinel
 proved exact and its order proved faithful on a common namespace.
 - `KernelObligations.lean` — kernel obligation lemmas (determinism,
 associativity, direct-sum laws, frame law, cross-sector permutation,
 partial-inverse clauses).
 - `RanksFit.lean` — the dimension bound behind deletion/addition k-cells.
 - `GraftWellFormedness.lean` — well-formedness for E-GRAFT.
 - `Rebase*.lean` — presentation-rebase rank preservation.
 - `Fixtures.lean` / `FixtureReplay.lean` / `FixtureEvalReplay.lean` —
 fixture transcription and replay checks. Every fixture of
 `machine/fixtures/mvp_fixtures.json` is transcribed except `W24`, a
 119-qubit state whose well-formedness the Boolean test cannot decide in
 the kernel: its independence check enumerates the coefficient vectors of
 a 46-row sector. `machine/lean_fixture_coverage.py` reports the coverage
 and compares the transcribed states with the JSON.
 - `WellFormedBool.lean` — boolean well-formedness helpers.
 - `Property.lean`, `Judgment.lean`, `Interval.lean`, `Refinement.lean`,
 `MaskRank.lean`, `MixSupport.lean` — supporting definitions.
 - `AxiomAudit.lean`: build-time check of the trust basis below.
- `CodeCalculus.lean` is the entry point imported by `lake build`.

## External code ingestion

A code written outside this repository as a pair of check matrices is brought
into Lean under the contract of `spec/REPRESENTATION.md` §9.

```sh
python3 machine/experiments/code_state_lean_instances.py \
    --presentation entry.json --name my_code > CodeCalculus/MyCode.lean
```

The input is a document of the shape `CodeState.from_challenge` accepts (`n`,
`k`, `checks.X`, `checks.Z`). The output defines `my_code_presentation`,
`my_code_checks_sha256`, the state `my_code`, and the theorems
`my_code_wellFormed` and `my_code_binds`. Certificates for the state are
added with `lean_instance_block` of `machine/certificates.py`, as
`IngestedInstances.lean` does.

- The translation is untrusted. `my_code_binds` is checked by the kernel, so a
  state whose rows are not rows of the presentation, or whose row spaces
  differ from it, does not build.
- Lean does not compute the binding hash. `binding_failures` in
  `machine/ingestion.py` reads the presentation literal back out of the Lean
  source, hashes it, and compares it with the recorded string and with the
  hash and `n` of the source document. For the committed instances this is
  `python3 machine/experiments/code_state_lean_instances.py --verify`, and
  `machine/test_code_state_lean.py` runs it. The hash is the `checks_sha256`
  of `qldpc-challenge`.
- Ingestion makes the state available. It proves nothing about distance. A
  lower bound needs a certificate, and `checkCertificate` enumerates every
  vector of weight below the bound, so kernel-checked bounds are practical
  only for small codes (about 20 qubits). Larger codes wait on a scalable
  certificate format (issue #574).

## Formal certificates for challenge entries

`machine/experiments/formal_cert_from_challenge.py` turns a qldpc-challenge
entry into a Lean module and, once that module is committed, into the
`certs/<slug>.json` payload of a `formal` certificate. Run it from the
repository root; it needs `lake` on the path. For `codes/10-2-3-b.json`,
with qldpc-challenge checked out beside this repository:

```sh
python3 machine/experiments/formal_cert_from_challenge.py \
    ../qldpc-challenge/codes/10-2-3-b.json --name qldpc_10_2_3_b
```

This ingests the entry, builds a pruning-tree certificate per sector at the
entry's witnessed values (`--sector X --bound B` pairs override them), and
writes `lean/CodeCalculus/FormalCerts/qldpc_10_2_3_b.lean`. The module holds
the ingestion block, the tree blocks, and one theorem,
`CodeCalculus.FormalCert_qldpc_10_2_3_b.qldpc_10_2_3_b_certified`: the
binding theorem conjoined with each sector's bound, or its exact distance
when the entry's witness has the bound's weight. The script checks the
module's binding hash against the entry, runs
`lake build CodeCalculus.FormalCerts.qldpc_10_2_3_b`, and refuses a theorem
that depends on an axiom other than `propext`, `Classical.choice` and
`Quot.sound`. The generated module is not imported by `CodeCalculus.lean`,
so `AxiomAudit.lean` does not cover it; this check is the audit. Progress
goes to stderr.

The payload names a commit that holds the theorem, so it is printed only
when the module at that commit is the one just generated. Commit the module
(on a branch of a public repository), then run again:

```sh
git add lean/CodeCalculus/FormalCerts/qldpc_10_2_3_b.lean
git commit -m "Formal certificate module for 10-2-3-b"
git push
python3 machine/experiments/formal_cert_from_challenge.py \
    ../qldpc-challenge/codes/10-2-3-b.json --name qldpc_10_2_3_b \
    --repo https://github.com/OWNER/REPO > ../qldpc-challenge/certs/10-2-3-b.json
```

`--repo` has no default: only the caller knows where the commit is
published. `--commit` defaults to `HEAD`. The payload's
`verification.replay` holds `repo`, `commit`, `theorem` (the
`_certified` theorem), `build`
(`cd lean && lake build CodeCalculus.FormalCerts.<name>`) and `toolchain`
(read from `lean/lean-toolchain` at the commit). There is no `mathlib`
field: the development uses the Lean core library only.
`verification.checks_sha256` is the hash of the entry's presentation, not of
the retained rows, so a redundant presentation binds to its entry. The
definition is generated from the entry, never transcribed. The payload is
exact when the least bound is the entry's `d` and partial otherwise; a run
with one `--sector` builds the module and prints no payload, since the board
takes no single-side bound. Then, in the qldpc-challenge checkout (its
command, which needs `jsonschema`):

```sh
python3 verify/check_certs.py
```

CI runs this workflow end to end on the board's `codes/10-2-3-b.json`:
`scripts/check_formal_cert_pipeline.sh` generates and builds the module,
pins it in a commit object no branch points at, and passes the payload
through `verify/check_certs.py` of a pinned qldpc-challenge commit in a
temporary tree. `machine/test_challenge_certificate.py` runs the same
checker on its payloads when `QLDPC_CHALLENGE_DIR` names a checkout, as
it does in CI.

The payload is built by `export_challenge_certificate` in
`machine/certificates.py`, which refuses a state that is not the entry's
ingestion, a missing sector, a certificate the prototype checker rejects, a
witness that is not a logical or is lighter than a proven bound or than
`d`, a partial bound outside `2 .. d - 1`, an exact payload without a
weight-`d` witness, and a `replay` or `checker` the schema does not allow.
It has no defaults for `replay`, `checker` or `solver`.

**Size limits** (`machine/ingestion.py`, measured by
`machine/experiments/benchmark_formal_cert.py` on an Apple-silicon laptop
with a warm build cache, lower bounds at the sector distance, no witness):

| code | n | retained rows per sector | bound | tree nodes | build (s) | build with `_wellFormed` (s) |
| --- | --- | --- | --- | --- | --- | --- |
| `10-2-3-b` | 10 | 4 | 3 | 86 | 0.9 | 1.4 |
| two-block, `Z_9` | 18 | 7 | 4 | 612 | 1.1 | 1.8 |
| two-block, `Z_12` | 24 | 8 | 2 | 98 | 4.1 | 2.8 |
| two-block, `Z_12` | 24 | 10 | 4 | 808 | 2.0 | fails |
| two-block, `Z_15` | 30 | 13 | 6 | 9,030 | 12.1 | fails |
| two-block, `Z_21` | 42 | 19 | 6 | 10,030 | 24.0 | fails |
| two-block, `Z_24` | 48 | 22 | 8 | 118,928 | stopped unfinished after > 10 min | not run |
Generation takes under 0.1 s for each. `<name>_wellFormed` is proved by
`decide`, which reaches Lean's maximum recursion depth at 10 retained rows;
the certified theorem does not use it, and the generator leaves it out above
`LEAN_WELL_FORMEDNESS_ROW_LIMIT = 8` rows (`--well-formedness always` keeps
it). The certificate theorems grow with the tree, which grows with the bound
and the number of qubits. The generator refuses entries above
`LEAN_GENERATION_QUBIT_LIMIT = 42` qubits, the largest size built here,
unless `--allow-large` is given; the 500-qubit board composites are far
outside it. Times are single runs.

## Extra modules

`lean/extra/` holds modules that are **not** part of the default `lake build`
target and are **not** covered by `AxiomAudit.lean`:

- `ClosedK.lean`: no declaration. The closed forms for `stateK` of `L-HGP`
 and `A-PRODUCT`, and the four rank statements it held as axioms, are
 proved in `CodeCalculus/ClosedK.lean`. The file remains so that
 `lake build ClosedK` names a target.
- `Retention.lean`: no declaration. The `A-CONCAT` retention statement it
 held as an axiom is proved in `CodeCalculus/ConcatRetention.lean`. The file remains so that `lake build Retention` names a
 target.

Build them explicitly with `lake build ClosedK Retention`. Neither CI nor
the audit covers them, so a broken statement there will not fail the
default build.

## Status

Mechanization is partial and ongoing. Modules marked with `sorry` are
incomplete; the build is expected to be green (`0 sorry` on `main`), and
`CodeCalculus/AxiomAudit.lean` fails the build on a `sorry`. Gates 0–6 are
ratified (2026-11-19); Gate 7 is ratified for `stdCSS-3` (2026-11-26). See
`spec/GATES.md`.

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
 checked by the Lean compiler, not by the kernel. The v0.1 decision (2026-10-28) accepts this site. The fixture replays
 (`FixtureReplay.lean`, `FixtureEvalReplay.lean`) are kernel `decide`
 throughout.
- No constant depends on `sorryAx`.

Certificates: the theorems of `CertificateInstances.lean` rest
on the kernel and on the definition of the exact distance. The certificate
producer and the generator that writes that module are Python and are not
trusted; a wrong certificate or a wrong translation fails `by decide` or
yields a true theorem about a different state term. The pruning-tree
instances use `decide +kernel`, which asks the kernel to evaluate the
checker directly and adds no axiom (`native_decide` is not used). That a state term is the
intended state is checked by reading (`spec/CLAIMS.md`, *Mechanized
checker*).

Capacity (H-4, 2026-11-11): the five minting rules (`Eval.add`,
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
