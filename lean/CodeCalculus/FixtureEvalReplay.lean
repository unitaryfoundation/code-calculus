import CodeCalculus.Eval
import CodeCalculus.Fixtures
import CodeCalculus.FixtureReplay
import CodeCalculus.WellFormedBool
import CodeCalculus.Soundness

/-!
# Fixture replays under `Eval` and `EvalExpr` (WP6)

`FixtureReplay.lean` decides `wellFormedBool` of the hand-typed fixture
states and nothing else, so a mistyped result state went unnoticed (the W5
and W7 results carried hard-coded identifiers instead of the minted rank;
review findings RG-8 and RC-3 of ). This module replays the
transitions themselves against `machine/fixtures/mvp_fixtures.json`:

- every `derivable` single-step or two-step fixture has a positive theorem
  `Eval term initial result` (or `EvalExpr` for the direct-sum pair fixture
  W14), with `result` the transcribed result state when the JSON records one
  and the transition's output otherwise;
- every `no_derivation` fixture has a negative theorem `¬ ∃ t, Eval term
  initial t`, closed on the premise the JSON names as failing (the pair
  fixtures W15 and W21 keep their negative theorems in `FixtureReplay.lean`);
- every transcribed state's well-formedness verdict is restated as the
  predicate `EncodingWellFormed` (or its negation), through `wellFormedBool_iff`
  and a kernel `decide` of the Boolean test, so this module does not inherit
  the `native_decide` axioms of `FixtureReplay.lean`.

Every proof here is kernel-checked: the decidable premises by `decide`, the
span premises through `inSpanRowsBool_iff` and `independentGeneratorBool_iff`
(`WellFormedBool.lean`), and the state equalities by `decide` on the derived
`DecidableEq CodeState`. No `native_decide`, no `sorry`.

The JSON names rows by example-local identifiers (`a1`, `b1`, `c1`); the
transcription uses their ranks in the pinned enumeration (`a1 = 0`, `a2 = 1`,
`b1 = 10000`, `a3 = 2`). W4's term `delete_{13}` names a non-displayed row by
its support; the replay deletes the non-displayed rank 2, which is the same
failing premise (`DisplayedGenerator`).
-/

namespace CodeCalculus

/-! ## The Boolean verdicts as the predicate -/

theorem fixture_W0_initial_wf : EncodingWellFormed fixture_W0_initial :=
  encodingWellFormed_of_bool (by decide)
theorem fixture_W3_initial_wf : EncodingWellFormed fixture_W3_initial :=
  encodingWellFormed_of_bool (by decide)
theorem fixture_W3_result_wf : EncodingWellFormed fixture_W3_result :=
  encodingWellFormed_of_bool (by decide)
theorem fixture_W4_initial_wf : EncodingWellFormed fixture_W4_initial :=
  encodingWellFormed_of_bool (by decide)
theorem fixture_W5_initial_wf : EncodingWellFormed fixture_W5_initial :=
  encodingWellFormed_of_bool (by decide)
theorem fixture_W5_result_wf : EncodingWellFormed fixture_W5_result :=
  encodingWellFormed_of_bool (by decide)
theorem fixture_W6_initial_wf : EncodingWellFormed fixture_W6_initial :=
  encodingWellFormed_of_bool (by decide)
theorem fixture_W7_initial_wf : EncodingWellFormed fixture_W7_initial :=
  encodingWellFormed_of_bool (by decide)
theorem fixture_W7_result_wf : EncodingWellFormed fixture_W7_result :=
  encodingWellFormed_of_bool (by decide)
theorem fixture_W8_initial_wf : EncodingWellFormed fixture_W8_initial :=
  encodingWellFormed_of_bool (by decide)
theorem fixture_W9_initial_wf : EncodingWellFormed fixture_W9_initial :=
  encodingWellFormed_of_bool (by decide)
theorem fixture_W9_result_wf : EncodingWellFormed fixture_W9_result :=
  encodingWellFormed_of_bool (by decide)
theorem fixture_W10_initial_wf : EncodingWellFormed fixture_W10_initial :=
  encodingWellFormed_of_bool (by decide)
theorem fixture_W11_initial_wf : EncodingWellFormed fixture_W11_initial :=
  encodingWellFormed_of_bool (by decide)
theorem fixture_W12_initial_wf : EncodingWellFormed fixture_W12_initial :=
  encodingWellFormed_of_bool (by decide)
theorem fixture_W13_initial_wf : EncodingWellFormed fixture_W13_initial :=
  encodingWellFormed_of_bool (by decide)
theorem fixture_W14_result_wf : EncodingWellFormed fixture_W14_result :=
  encodingWellFormed_of_bool (by decide)
theorem fixture_W16_initial_wf : EncodingWellFormed fixture_W16_initial :=
  encodingWellFormed_of_bool (by decide)
theorem fixture_W16_result_wf : EncodingWellFormed fixture_W16_result :=
  encodingWellFormed_of_bool (by decide)
theorem fixture_W22_initial_wf : EncodingWellFormed fixture_W22_initial :=
  encodingWellFormed_of_bool (by decide)
theorem fixture_W23_initial_wf : EncodingWellFormed fixture_W23_initial :=
  encodingWellFormed_of_bool (by decide)
theorem fixture_W23_result_wf : EncodingWellFormed fixture_W23_result :=
  encodingWellFormed_of_bool (by decide)
theorem fixture_W14_S_L_wf : EncodingWellFormed fixture_W14_S_L :=
  encodingWellFormed_of_bool (by decide)
theorem fixture_W14_S_R_wf : EncodingWellFormed fixture_W14_S_R :=
  encodingWellFormed_of_bool (by decide)
theorem fixture_W15_S_R_prime_wf : EncodingWellFormed fixture_W15_S_R_prime :=
  encodingWellFormed_of_bool (by decide)
theorem fixture_W21_S_R_double_prime_wf : EncodingWellFormed fixture_W21_S_R_double_prime :=
  encodingWellFormed_of_bool (by decide)

theorem fixture_W1_initial_not_wf : ¬ EncodingWellFormed fixture_W1_initial :=
  not_encodingWellFormed_of_bool (by decide)
theorem fixture_W2_initial_not_wf : ¬ EncodingWellFormed fixture_W2_initial :=
  not_encodingWellFormed_of_bool (by decide)
theorem malformed_dupQ_not_wf : ¬ EncodingWellFormed malformed_dupQ :=
  not_encodingWellFormed_of_bool (by decide)
theorem malformed_badSupport_not_wf : ¬ EncodingWellFormed malformed_badSupport :=
  not_encodingWellFormed_of_bool (by decide)
theorem malformed_dependent_not_wf : ¬ EncodingWellFormed malformed_dependent :=
  not_encodingWellFormed_of_bool (by decide)

/-! ## Helpers: decidability of the list-level premises, and the two span
premises through the bridge -/

/-- `DisplayedGenerator` is a bounded existential over the display. -/
instance (r : Nat) (s : CodeState) : Decidable (DisplayedGenerator r s) :=
  inferInstanceAs (Decidable (∃ row, row ∈ s.rows ∧ row.id = r))

/-- `supportSubset` is a bounded universal over the support. -/
instance (support Q : List Nat) : Decidable (supportSubset support Q) :=
  inferInstanceAs (Decidable (∀ q, q ∈ support → q ∈ Q))

/-- `DisjointList` is a bounded universal over the first list. -/
instance (xs ys : List Nat) : Decidable (DisjointList xs ys) :=
  inferInstanceAs (Decidable (∀ x, x ∈ xs → x ∉ ys))

/-- The addition premise `¬ inSpanRows …`, from the Boolean test. -/
theorem not_inSpanRows_of_bool {Q : List Nat} {rows : List Row} {v : List Bool}
    (h : inSpanRowsBool Q rows v = false) : ¬ inSpanRows Q rows v := by
  intro hs
  have := (inSpanRowsBool_iff Q rows v).mpr hs
  rw [h] at this
  exact Bool.false_ne_true this

/-- The addition premise fails: the row is in the span, from the Boolean test. -/
theorem inSpanRows_of_bool {Q : List Nat} {rows : List Row} {v : List Bool}
    (h : inSpanRowsBool Q rows v = true) : inSpanRows Q rows v :=
  (inSpanRowsBool_iff Q rows v).mp h

/-- The deletion premise `IndependentGenerator`, from the Boolean test. -/
theorem independentGenerator_of_bool {r : Nat} {s : CodeState}
    (h : independentGeneratorBool r s = true) : IndependentGenerator r s :=
  (independentGeneratorBool_iff r s).mp h

/-! ## Positive replays -/

/-- W3: `delete_{a1}` on W0 gives A1. -/
theorem fixture_W3_eval :
    Eval (Command.delete 0) fixture_W3_initial fixture_W3_result :=
  Eval.delete (by decide) (independentGenerator_of_bool (by decide)) (by decide)

/-- W5: `addStab` of the Z row `{1}` on A1 mints rank 2 and gives A2. -/
theorem fixture_W5_eval :
    Eval (Command.addStab Sector.Z [1]) fixture_W5_initial fixture_W5_result :=
  Eval.add (by decide) (by decide) (by decide) (by decide)
    (not_inSpanRows_of_bool (by decide)) (by decide)

/-- W7, first step: `delete_{a1}` on W0. -/
theorem fixture_W7_step1 :
    Eval (Command.delete 0) fixture_W7_initial (deleteState fixture_W7_initial 0) :=
  Eval.delete (by decide) (independentGenerator_of_bool (by decide)) rfl

/-- W7, second step: `addStab X {1,3}` on the intermediate state mints rank 2. -/
theorem fixture_W7_step2 :
    Eval (Command.addStab Sector.X [1, 3]) (deleteState fixture_W7_initial 0)
      fixture_W7_result :=
  Eval.add (by decide) (by decide) (by decide) (by decide)
    (not_inSpanRows_of_bool (by decide)) (by decide)

/-- W7: the row-replacement loop `delete_{a1}; addStab X {1,3}` on W0. -/
theorem fixture_W7_eval :
    Eval (Command.seq (Command.delete 0) (Command.addStab Sector.X [1, 3]))
      fixture_W7_initial fixture_W7_result :=
  Eval.seq fixture_W7_step1 fixture_W7_step2

/-- W9: `delete_{a2}; delete_{a1}` on W0, the second step checked against the
    intermediate state. -/
theorem fixture_W9_eval :
    Eval (Command.seq (Command.delete 1) (Command.delete 0))
      fixture_W9_initial fixture_W9_result :=
  Eval.seq
    (Eval.delete (by decide) (independentGenerator_of_bool (by decide)) rfl)
    (Eval.delete (by decide) (independentGenerator_of_bool (by decide)) (by decide))

/-- W12: `delete_{a1}` on W0 gives A1 (W3's result). -/
theorem fixture_W12_eval :
    Eval (Command.delete 0) fixture_W12_initial fixture_W3_result :=
  Eval.delete (by decide) (independentGenerator_of_bool (by decide)) (by decide)

/-- W16: the mixed-sector deletion set `delete_{a1}; delete_{b1}` on W0. -/
theorem fixture_W16_eval :
    Eval (Command.seq (Command.delete 0) (Command.delete 10000))
      fixture_W16_initial fixture_W16_result :=
  Eval.seq
    (Eval.delete (by decide) (independentGenerator_of_bool (by decide)) rfl)
    (Eval.delete (by decide) (independentGenerator_of_bool (by decide)) (by decide))

/-- W23: the single deletion of the small challenge code. -/
theorem fixture_W23_eval :
    Eval (Command.delete 0) fixture_W23_initial fixture_W23_result :=
  Eval.delete (by decide) (independentGenerator_of_bool (by decide)) (by decide)

/-- W14: the direct sum of the two summands is the transcribed result. -/
theorem fixture_W14_result_eq :
    directSumState fixture_W14_S_L fixture_W14_S_R = fixture_W14_result := by
  decide

theorem fixture_W14_evalExpr :
    EvalExpr (StateExpr.directSum (StateExpr.base fixture_W14_S_L)
      (StateExpr.base fixture_W14_S_R)) fixture_W14_result :=
  fixture_W14_result_eq ▸
    EvalExpr.directSum (by decide) (by decide) (EvalExpr.base _) (EvalExpr.base _)

/-! ## Negative replays -/

/-- W4: the row named is not displayed (`DisplayedGenerator` fails). -/
theorem fixture_W4_no_eval : ¬ ∃ t, Eval (Command.delete 2) fixture_W4_initial t := by
  rintro ⟨t, h⟩
  cases h with
  | delete hdisp _ _ => exact absurd hdisp (by decide)

/-- W6: the X row `{2,3}` is already displayed, so same-sector independence
    fails. -/
theorem fixture_W6_no_eval :
    ¬ ∃ t, Eval (Command.addStab Sector.X [2, 3]) fixture_W6_initial t := by
  rintro ⟨t, h⟩
  cases h with
  | add _ _ _ _ hspan _ => exact hspan (inSpanRows_of_bool (by decide))

/-- W6's variant: the X row `{1}` anticommutes with the Z row `{1,2,3}`. -/
theorem fixture_W6_variant_no_eval :
    ¬ ∃ t, Eval (Command.addStab Sector.X [1]) fixture_W0_initial t := by
  rintro ⟨t, h⟩
  cases h with
  | add _ _ _ hcomm _ _ => exact absurd hcomm (by decide)

/-- W8: the order `addStab Z {1}; delete_{a1}` fails at its first step, since
    `{1}` anticommutes with the X row `{1,2}` (the other order is W5's path
    after W3's). -/
theorem fixture_W8_no_eval :
    ¬ ∃ t, Eval (Command.seq (Command.addStab Sector.Z [1]) (Command.delete 0))
      fixture_W8_initial t := by
  rintro ⟨t, h⟩
  cases h with
  | seq h1 _ =>
      cases h1 with
      | add _ _ _ hcomm _ _ => exact absurd hcomm (by decide)

/-- W8's other order is derivable: `delete_{a1}; addStab Z {1}` reaches A2. -/
theorem fixture_W8_other_order_eval :
    Eval (Command.seq (Command.delete 0) (Command.addStab Sector.Z [1]))
      fixture_W8_initial fixture_W5_result :=
  Eval.seq
    (Eval.delete (by decide) (independentGenerator_of_bool (by decide)) rfl)
    (Eval.add (by decide) (by decide) (by decide) (by decide)
      (not_inSpanRows_of_bool (by decide)) (by decide))

/-- W10: `delete_{a1}; delete_{a1}` fails at the second step, against the
    intermediate state. -/
theorem fixture_W10_no_eval :
    ¬ ∃ t, Eval (Command.seq (Command.delete 0) (Command.delete 0)) fixture_W10_initial t := by
  rintro ⟨t, h⟩
  cases h with
  | seq h1 h2 =>
      cases h1 with
      | delete _ _ heq1 =>
          subst heq1
          cases h2 with
          | delete hdisp _ _ => exact absurd hdisp (by decide)

/-- W22: the support `{8}` leaves `Q = {1,2,3}`. -/
theorem fixture_W22_no_eval :
    ¬ ∃ t, Eval (Command.addStab Sector.X [8]) fixture_W22_initial t := by
  rintro ⟨t, h⟩
  cases h with
  | add hsub _ _ _ _ _ => exact absurd hsub (by decide)

/-! ## The two-step chains as `Chain`s, for the derivation layer -/

/-- W7's evaluation chain. -/
theorem fixture_W7_chain :
    Chain [fixture_W7_initial, deleteState fixture_W7_initial 0, fixture_W7_result] :=
  Chain.cons fixture_W7_step1 (Chain.cons fixture_W7_step2 (Chain.single _))

/-! ## Two-step `k` compositions by `TRANSITIVITY` alone ()

The `k` cells of deletion and addition are stated in an exact additive form
and in a truncated form (`Soundness.lean`, module note). `TRANSITIVITY`
composes two instantiation rows only through a shared middle term, so the
delete-then-add loop of W7 composes through `k_1 ∸ 1` and the add-then-delete
chain below through `k_1 + 1`. Both compositions are true of their chains by
`judgment_soundness_of_head`, from the input state's well-formedness alone. -/

/-- W7, delete then add: `k_2 = k_0`, from the truncated readings. -/
theorem fixture_W7_k_restored (dMeasure : Field → CodeState → Nat) :
    Derives dMeasure [fixture_W7_initial, deleteState fixture_W7_initial 0, fixture_W7_result]
      (Ann.eq (AExpr.atom ⟨2, Field.k⟩) (AExpr.atom ⟨0, Field.k⟩)) :=
  Derives.transit_eq_eq _ _ _
    (Derives.instAddKSub 1 Sector.X [1, 3] _ _ rfl rfl fixture_W7_step2)
    (Derives.eq_sym _ _ (Derives.instDeleteKSub 0 0 _ _ rfl rfl fixture_W7_step1))

theorem fixture_W7_k_restored_models (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) :
    Models dMeasure [fixture_W7_initial, deleteState fixture_W7_initial 0, fixture_W7_result]
      (Ann.eq (AExpr.atom ⟨2, Field.k⟩) (AExpr.atom ⟨0, Field.k⟩)) :=
  judgment_soundness_of_head dMeasure hmono _ fixture_W7_chain
    (fun s hs => by rw [← Option.some.inj hs]; exact fixture_W7_initial_wf) _
    (fixture_W7_k_restored dMeasure)

/-- Undoing W5: deleting the row W5 minted. -/
theorem fixture_W5_undo_step :
    Eval (Command.delete 2) fixture_W5_result (deleteState fixture_W5_result 2) :=
  Eval.delete (by decide) (independentGenerator_of_bool (by decide)) rfl

theorem addThenDelete_chain :
    Chain [fixture_W5_initial, fixture_W5_result, deleteState fixture_W5_result 2] :=
  Chain.cons fixture_W5_eval (Chain.cons fixture_W5_undo_step (Chain.single _))

/-- Add then delete: `k_2 = k_0`, from the exact additive readings. -/
theorem addThenDelete_k_restored (dMeasure : Field → CodeState → Nat) :
    Derives dMeasure [fixture_W5_initial, fixture_W5_result, deleteState fixture_W5_result 2]
      (Ann.eq (AExpr.atom ⟨2, Field.k⟩) (AExpr.atom ⟨0, Field.k⟩)) :=
  Derives.transit_eq_eq _ _ _
    (Derives.instDeleteK 1 2 _ _ rfl rfl fixture_W5_undo_step)
    (Derives.eq_sym _ _ (Derives.instAddK 0 Sector.Z [1] _ _ rfl rfl fixture_W5_eval))

theorem addThenDelete_k_restored_models (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) :
    Models dMeasure [fixture_W5_initial, fixture_W5_result, deleteState fixture_W5_result 2]
      (Ann.eq (AExpr.atom ⟨2, Field.k⟩) (AExpr.atom ⟨0, Field.k⟩)) :=
  judgment_soundness_of_head dMeasure hmono _ addThenDelete_chain
    (fun s hs => by rw [← Option.some.inj hs]; exact fixture_W5_initial_wf) _
    (addThenDelete_k_restored dMeasure)

end CodeCalculus
