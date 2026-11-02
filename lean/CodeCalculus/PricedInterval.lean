import CodeCalculus.State
import CodeCalculus.Term
import CodeCalculus.Eval
import CodeCalculus.Judgment
import CodeCalculus.GraftWellFormedness

namespace CodeCalculus

def minOpt : Option Nat → Option Nat → Option Nat
  | none, none => none
  | none, some b => some b
  | some a, none => some a
  | some a, some b => some (min a b)

def leOpt (a b : Option Nat) : Prop :=
  match a, b with
  | none, none => True
  | none, some _ => False
  | some _, none => True
  | some a, some b => a ≤ b

theorem leOpt_refl (a : Option Nat) : leOpt a a := by
  cases a <;> simp [leOpt]

theorem leOpt_trans {a b c : Option Nat} (h1 : leOpt a b) (h2 : leOpt b c) : leOpt a c := by
  cases a <;> cases b <;> cases c <;> simp [leOpt] at * <;> (try omega) <;> (try contradiction)

def Interval.contains (i : Interval) (d : Option Nat) : Prop :=
  leOpt i.lower d ∧ leOpt d i.upper

structure ExactDist where
  full : Option Nat
  x : Option Nat
  z : Option Nat

def LedgerSound (δ : ExactDist) (L : DistanceLedger) : Prop :=
  L.full.contains δ.full ∧ L.x.contains δ.x ∧ L.z.contains δ.z

structure Hyp where
  deletionPrice : Option (Nat × Nat) := none
  graftPrice : Option Nat := none

-- `propagateCmd` is the per-step transport. The `C-SEQUENCE`, `P-REBASE`,
-- `E-LOCAL-HADAMARD`, `E-PEEL`, `E-PUNCTURE` and `E-EXTEND` cases below are
-- *widened* transports (`[0, +∞]` or a carried reset): they are sound but
-- not exact, because exact transport for a composite step needs the
-- intermediate state and a price per sub-step. Composition is derived by
-- applying the per-step rule twice (see `priced_interval_soundness_seq`).
def propagateCmd (m : Command) (s s' : CodeState) (L : DistanceLedger) (H : Hyp) :
    DistanceLedger :=
  match m with
  | Command.skip => L
  | Command.delete r =>
      let base : DistanceLedger := { full := Interval.mk (some 0) L.full.upper, x := Interval.mk (some 0) L.x.upper, z := Interval.mk (some 0) L.z.upper }
      match H.deletionPrice with
      | none => base
      | some (wd, we) =>
          let p := min wd we
          { full := Interval.mk (minOpt L.full.lower (some p)) (minOpt L.full.upper (some p))
          , x := base.x
          , z := base.z }
  | Command.addStab sector support =>
      { full := Interval.mk L.full.lower none
      , x := Interval.mk L.x.lower none
      , z := Interval.mk L.z.lower none }
  | Command.graft q τ ids =>
      let splicedLow := if τ = Sector.X then L.x.lower else L.z.lower
      let otherUpper := if τ = Sector.X then L.z.upper else L.x.upper
      let otherLow := if τ = Sector.X then L.z.lower else L.x.lower
      let Lspliced := Interval.mk splicedLow none
      let Lother := Interval.mk (some 0) otherUpper
      let Lfull := Interval.mk (some 0) otherUpper
      let base : DistanceLedger := if τ = Sector.X
                  then { full := Lfull, x := Lspliced, z := Lother }
                  else { full := Lfull, x := Lother, z := Lspliced }
      match H.graftPrice with
      | none => base
      | some p =>
          let newOtherLow := minOpt otherLow (some p)
          let newOtherUpper := minOpt otherUpper (some p)
          let newOther := Interval.mk newOtherLow newOtherUpper
          let newFull := Interval.mk (minOpt L.full.lower (some p))
                                    (minOpt (some p) otherUpper)
          if τ = Sector.X
          then { full := newFull, x := Lspliced, z := newOther }
          else { full := newFull, x := newOther, z := Lspliced }
  | _ =>
      { full := Interval.mk (some 0) none
      , x := Interval.mk (some 0) none
      , z := Interval.mk (some 0) none }

def propagateCmdK (m : Command) (s s' : CodeState) (L : DistanceLedger) (H : Hyp) : DistanceLedger :=
  let out := propagateCmd m s s' L H
  if stateK s' = 0 then
    { full := Interval.mk none none, x := Interval.mk none none, z := Interval.mk none none }
  else out

theorem minOpt_monotone {a a' b b' : Option Nat}
    (ha : leOpt a a') (hb : leOpt b b') :
    leOpt (minOpt a b) (minOpt a' b') := by
  cases a <;> cases a' <;> cases b <;> cases b' <;>
    simp [minOpt, leOpt] at * <;> (try omega) <;> (try contradiction)

def HypTrue (δ : CodeState → ExactDist) (H : Hyp) :
    ∀ (m : Command) (s s' : CodeState), Prop
  | Command.delete _r, s, s' =>
      (∀ wd we, H.deletionPrice = some (wd, we) →
          (δ s').full = minOpt (δ s).full (some (min wd we)))
  | Command.graft q τ ids, s, s' =>
      (∀ p, H.graftPrice = some p →
          (if τ = Sector.X then (δ s').z = minOpt (δ s).z (some p)
           else (δ s').x = minOpt (δ s).x (some p)))
  | Command.addStab _sector support, _s, _s' =>
      True
  | _, _, _ => True

def directSumLedger (A B : DistanceLedger) : DistanceLedger :=
  { full := Interval.mk (minOpt A.full.lower B.full.lower) (minOpt A.full.upper B.full.upper)
  , x := Interval.mk (minOpt A.x.lower B.x.lower) (minOpt A.x.upper B.x.upper)
  , z := Interval.mk (minOpt A.z.lower B.z.lower) (minOpt A.z.upper B.z.upper) }

theorem directSum_sound (δ : CodeState → ExactDist)
    (hdirect : ∀ a b, δ (directSumState a b) =
        ExactDist.mk (minOpt (δ a).full (δ b).full)
                    (minOpt (δ a).x (δ b).x)
                    (minOpt (δ a).z (δ b).z))
    (A B : DistanceLedger) (sA sB : CodeState)
    (hA : LedgerSound (δ sA) A) (hB : LedgerSound (δ sB) B) :
    LedgerSound (δ (directSumState sA sB)) (directSumLedger A B) := by
  have hδ := hdirect sA sB
  rcases hA with ⟨hAf, hAx, hAz⟩
  rcases hB with ⟨hBf, hBx, hBz⟩
  constructor
  · have hδfull : (δ (directSumState sA sB)).full = minOpt (δ sA).full (δ sB).full :=
      congrArg ExactDist.full (hdirect sA sB)
    rw [hδfull]
    exact ⟨minOpt_monotone hAf.1 hBf.1, minOpt_monotone hAf.2 hBf.2⟩
  · constructor
    · have hδx : (δ (directSumState sA sB)).x = minOpt (δ sA).x (δ sB).x :=
        congrArg ExactDist.x (hdirect sA sB)
      rw [hδx]
      exact ⟨minOpt_monotone hAx.1 hBx.1, minOpt_monotone hAx.2 hBx.2⟩
    · have hδz : (δ (directSumState sA sB)).z = minOpt (δ sA).z (δ sB).z :=
        congrArg ExactDist.z (hdirect sA sB)
      rw [hδz]
      exact ⟨minOpt_monotone hAz.1 hBz.1, minOpt_monotone hAz.2 hBz.2⟩


@[simp] theorem leOpt_none (d : Option Nat) : leOpt d none := by cases d <;> simp [leOpt]

theorem some_zero_leOpt (d : Option Nat) : leOpt (some 0) d := by
  cases d <;> simp [leOpt] <;> omega



theorem minOpt_le_right (a b : Option Nat) : leOpt (minOpt a b) b := by
  cases a <;> cases b <;> simp [minOpt, leOpt] <;> omega

theorem minOpt_le_left (a b : Option Nat) : leOpt (minOpt a b) a := by
  cases a <;> cases b <;> simp [minOpt, leOpt] <;> omega

theorem leOpt_min (a b c : Option Nat) (hab : leOpt a b) (hac : leOpt a c) :
    leOpt a (minOpt b c) := by
  cases a <;> cases b <;> cases c <;> simp [leOpt, minOpt] at * <;> (try omega) <;> (try contradiction)

/-!
Gate 6 soundness (). `priced_interval_soundness` below is the
interval-transport statement over all admitted commands. For the five Gate 6
moves that have Lean transitions (`P-REBASE`, `E-PEEL`, `E-PUNCTURE`,
`E-EXTEND`, `E-LOCAL-HADAMARD`) their case in `propagateCmd` is the widened
`[0, +∞]` reset (the default `_` case), so this theorem proves soundness of
that reset, not the §4.32 transformers (identity for `P-REBASE`, sector swap
for `E-LOCAL-HADAMARD`, lower carry for `E-EXTEND` with `Δ = ∅`); those are
not implemented in Lean. The reset reading is §4.32's only for the three
refusals. Well-formedness preservation for these five moves is a premise of
their transitions, not a proof: `wf_of_eval` (`WellFormedness.lean`) returns
that premise (`hwf'`). `E-GLUE` has no `Eval` transition in Lean (no `glue`
constructor; `EvalExpr` has only `base` and `directSum`), so neither theorem
covers it. See `OBL-GATE6-CSS-EXTENSIONS` (`proved`,
`spec/OBLIGATIONS.md`) and `spec/OPERATIONAL_SEMANTICS.md` §4.32 for the
hand derivation; `hadamardState_stateK`, `stateK_swap`, and
`peelEval_Q_length` are facts about the transitions, not a soundness
discharge.

Well-formedness guard (review findings RC-4 and RG-10). The
`k = 0` hypothesis `hk0` and the three monotonicity hypotheses range over
well-formed states only, and the theorem takes `EncodingWellFormed` of the
input state, which `wf_of_eval_all` carries to the output and along a
sequence. Without the guard, `hk0` quantified over every `CodeState`: on an
ill-formed state `stateK` is a truncated subtraction and can be `0` while a
logical operator exists (`Q = {0,1}` with the X row `{0}` and the Z row
`{0}`), so the exact distance function did not satisfy the old hypothesis and
the theorem could not be instantiated with it. The spec's statement
(`OBL-PRICED-INTERVAL-SOUNDNESS`) is about well-formed states.
-/
theorem priced_interval_soundness
  (δ : CodeState → ExactDist)
  (hmin : ∀ s, (δ s).full = minOpt (δ s).x (δ s).z)
  (hk0 : ∀ s, EncodingWellFormed s → stateK s = 0 →
      (δ s).full = none ∧ (δ s).x = none ∧ (δ s).z = none)
  (hdelete : ∀ r s s', EncodingWellFormed s → Eval (Command.delete r) s s' →
      leOpt (δ s').full (δ s).full ∧ leOpt (δ s').x (δ s).x ∧ leOpt (δ s').z (δ s).z)
  (hadd : ∀ sector support s s', EncodingWellFormed s →
      Eval (Command.addStab sector support) s s' →
      leOpt (δ s).full (δ s').full ∧ leOpt (δ s).x (δ s').x ∧ leOpt (δ s).z (δ s').z)
  (hgraft : ∀ q τ ids s s', EncodingWellFormed s → Eval (Command.graft q τ ids) s s' →
      (if τ = Sector.X then leOpt (δ s).x (δ s').x else leOpt (δ s).z (δ s').z) ∧
      (if τ = Sector.X then leOpt (δ s').z (δ s).z else leOpt (δ s').x (δ s).x))
  (H : Hyp)
  : ∀ (L : DistanceLedger) (s s' : CodeState) (m : Command),
      EncodingWellFormed s →
      Eval m s s' →
      HypTrue δ H m s s' →
      LedgerSound (δ s) L →
      LedgerSound (δ s') (propagateCmdK m s s' L H) := by
  intro L s s' m hwf hEval hH hSound
  have hwf' : EncodingWellFormed s' := wf_of_eval_all hEval hwf
  by_cases hk : stateK s' = 0
  · have hδ0 := hk0 s' hwf' hk
    rcases hδ0 with ⟨hf, hx, hz⟩
    have hprop : propagateCmdK m s s' L H =
        { full := Interval.mk none none, x := Interval.mk none none, z := Interval.mk none none } := by
      simp [propagateCmdK, hk]
    rw [hprop]
    constructor
    · simp [Interval.contains, leOpt, hf]
    · constructor
      · simp [Interval.contains, leOpt, hx]
      · simp [Interval.contains, leOpt, hz]
  · have hnz : stateK s' ≠ 0 := hk
    have hprop : propagateCmdK m s s' L H = propagateCmd m s s' L H := by
      simp [propagateCmdK, hnz]
    rw [hprop]
    let he := hEval
    cases m with
    | skip =>
        cases hEval with
        | skip =>
            simp [propagateCmd]
            exact hSound
    | delete r =>
        cases hEval with
        | delete hr hind hs' =>
            rcases hdelete r s s' hwf he with ⟨hdf, hdx, hdz⟩
            rcases hSound with ⟨hLf, hLx, hLz⟩
            cases hp : H.deletionPrice with
            | none =>
                simp [propagateCmd, hp, Interval.contains]
                constructor
                · constructor
                  · exact some_zero_leOpt (δ s').full
                  · exact leOpt_trans hdf hLf.2
                · constructor
                  · constructor
                    · exact some_zero_leOpt (δ s').x
                    · exact leOpt_trans hdx hLx.2
                  · constructor
                    · exact some_zero_leOpt (δ s').z
                    · exact leOpt_trans hdz hLz.2
            | some pair =>
                rcases pair with ⟨wd, we⟩
                have hp' : H.deletionPrice = some (wd, we) := hp
                have heq : (δ s').full = minOpt (δ s).full (some (min wd we)) :=
                  hH wd we hp'
                let p := min wd we
                simp [propagateCmd, hp, Interval.contains]
                constructor
                · constructor
                  · have hlow : leOpt (minOpt L.full.lower (some p)) (δ s').full := by
                      rw [show (δ s').full = minOpt (δ s).full (some p) from heq]; exact minOpt_monotone hLf.1 (leOpt_refl (some p))
                    exact hlow
                  · have hup : leOpt (δ s').full (minOpt L.full.upper (some p)) := by
                      rw [show (δ s').full = minOpt (δ s).full (some p) from heq]; exact minOpt_monotone hLf.2 (leOpt_refl (some p))
                    exact hup
                · constructor
                  · constructor
                    · exact some_zero_leOpt (δ s').x
                    · exact leOpt_trans hdx hLx.2
                  · constructor
                    · exact some_zero_leOpt (δ s').z
                    · exact leOpt_trans hdz hLz.2
    | addStab sector support =>
        cases hEval with
        | add _ _ _ _ _ hs' =>
            rcases hadd sector support s s' hwf he with ⟨haf, hax, haz⟩
            rcases hSound with ⟨hLf, hLx, hLz⟩
            simp [propagateCmd, Interval.contains]
            constructor
            · constructor
              · exact leOpt_trans hLf.1 haf
              · exact leOpt_none (δ s').full
            · constructor
              · constructor
                · exact leOpt_trans hLx.1 hax
                · exact leOpt_none (δ s').x
              · constructor
                · exact leOpt_trans hLz.1 haz
                · exact leOpt_none (δ s').z
    | graft q τ ids =>
        cases hEval with
        | graft _ _ _ _ _ _ _ _ hs' =>
            rcases hgraft q τ ids s s' hwf he with ⟨hspliced, hnon⟩
            rcases hSound with ⟨hLf, hLx, hLz⟩
            cases hp : H.graftPrice with
            | none =>
                simp [propagateCmd, hp, Interval.contains]
                cases τ with
                | X =>
                  constructor
                  · constructor
                    · exact some_zero_leOpt (δ s').full
                    · -- full upper: δ'.full ≤ otherUpper (L.z.upper)
                      have hup1 : leOpt (δ s').full (δ s').z := by rw [hmin s']; exact minOpt_le_right (δ s').x (δ s').z
                      have hup2 : leOpt (δ s').z (δ s).z := hnon
                      have hup3 : leOpt (δ s).z L.z.upper := hLz.2
                      exact leOpt_trans (leOpt_trans hup1 hup2) hup3
                  · constructor
                    · constructor
                      · exact leOpt_trans hLx.1 hspliced
                      · exact leOpt_none (δ s').x
                    · constructor
                      · exact some_zero_leOpt (δ s').z
                      · exact leOpt_trans hnon hLz.2
                | Z =>
                  constructor
                  · constructor
                    · exact some_zero_leOpt (δ s').full
                    · have hup1 : leOpt (δ s').full (δ s').x := by rw [hmin s']; exact minOpt_le_left (δ s').x (δ s').z
                      have hup2 : leOpt (δ s').x (δ s).x := hnon
                      have hup3 : leOpt (δ s).x L.x.upper := hLx.2
                      exact leOpt_trans (leOpt_trans hup1 hup2) hup3
                  · constructor
                    · constructor
                      · exact some_zero_leOpt (δ s').x
                      · exact leOpt_trans hnon hLx.2
                    · constructor
                      · exact leOpt_trans hLz.1 hspliced
                      · exact leOpt_none (δ s').z
            | some p =>
                have hp' : H.graftPrice = some p := hp
                simp [propagateCmd, hp, Interval.contains]
                cases τ with
                | X =>
                  have heqX : (δ s').z = minOpt (δ s).z (some p) :=
                    Eq.mp (ite_eq_left (rfl : Sector.X = Sector.X)) (hH p hp')
                  constructor
                  · constructor
                    · -- full lower: min(L.full.lower, p) ≤ δ'.full
                      have hlowSpliced : leOpt (minOpt L.full.lower (some p)) (δ s').x := by
                        have h1 : leOpt (minOpt L.full.lower (some p)) L.full.lower :=
                          minOpt_le_left L.full.lower (some p)
                        have h2 : leOpt L.full.lower (δ s).full := hLf.1
                        have h3 : leOpt (δ s).full (δ s).x := by rw [hmin s]; exact minOpt_le_left (δ s).x (δ s).z
                        have h4 : leOpt (δ s).x (δ s').x := hspliced
                        exact leOpt_trans (leOpt_trans (leOpt_trans h1 h2) h3) h4
                      have hlowOther : leOpt (minOpt L.full.lower (some p)) (δ s').z := by
                        rw [heqX]
                        have hA : leOpt (minOpt L.full.lower (some p)) (δ s).z := by
                          have h1 : leOpt (minOpt L.full.lower (some p)) L.full.lower :=
                            minOpt_le_left L.full.lower (some p)
                          have h2 : leOpt L.full.lower (δ s).full := hLf.1
                          have h3 : leOpt (δ s).full (δ s).z := by rw [hmin s]; exact minOpt_le_right (δ s).x (δ s).z
                          exact leOpt_trans (leOpt_trans h1 h2) h3
                        have hB : leOpt (minOpt L.full.lower (some p)) (some p) :=
                          minOpt_le_right L.full.lower (some p)
                        exact leOpt_min (minOpt L.full.lower (some p)) (δ s).z (some p) hA hB
                      have hlow : leOpt (minOpt L.full.lower (some p)) (δ s').full := by
                        rw [hmin s']
                        exact leOpt_min (minOpt L.full.lower (some p)) (δ s').x (δ s').z hlowSpliced hlowOther
                      exact hlow
                    · -- full upper: δ'.full ≤ min(p, otherUpper=L.z.upper)
                      have hup1 : leOpt (δ s').full (δ s').z := by rw [hmin s']; exact minOpt_le_right (δ s').x (δ s').z
                      rw [heqX] at hup1
                      have hup2 : leOpt (minOpt (δ s).z (some p)) (some p) := minOpt_le_right (δ s).z (some p)
                      have hupZ : leOpt (δ s').z L.z.upper := by
                        rw [heqX]
                        have h1 : leOpt (minOpt (δ s).z (some p)) (δ s).z := minOpt_le_left (δ s).z (some p)
                        have h2 : leOpt (δ s).z L.z.upper := hLz.2
                        exact leOpt_trans h1 h2
                      have hupA : leOpt (δ s').z (some p) := by rw [heqX]; exact minOpt_le_right (δ s).z (some p)
                      have hup4 : leOpt (δ s').z (minOpt (some p) L.z.upper) := leOpt_min (δ s').z (some p) L.z.upper hupA hupZ
                      rw [heqX] at hup4
                      exact leOpt_trans hup1 hup4
                  · constructor
                    · constructor
                      · exact leOpt_trans hLx.1 hspliced
                      · exact leOpt_none (δ s').x
                    · constructor
                      · have hlow : leOpt (minOpt L.z.lower (some p)) (δ s').z := by
                          rw [heqX]; exact minOpt_monotone hLz.1 (leOpt_refl (some p))
                        exact hlow
                      · have hup : leOpt (δ s').z (minOpt L.z.upper (some p)) := by
                          rw [heqX]; exact minOpt_monotone hLz.2 (leOpt_refl (some p))
                        exact hup
                | Z =>
                  have heqZ : (δ s').x = minOpt (δ s).x (some p) :=
                    Eq.mp (ite_eq_right (by decide : Sector.Z ≠ Sector.X)) (hH p hp')
                  constructor
                  · constructor
                    · -- full lower: min(L.full.lower, p) ≤ δ'.full
                      have hlowSpliced : leOpt (minOpt L.full.lower (some p)) (δ s').z := by
                        have h1 : leOpt (minOpt L.full.lower (some p)) L.full.lower := minOpt_le_left L.full.lower (some p)
                        have h2 : leOpt L.full.lower (δ s).full := hLf.1
                        have h3 : leOpt (δ s).full (δ s).z := by rw [hmin s]; exact minOpt_le_right (δ s).x (δ s).z
                        have h4 : leOpt (δ s).z (δ s').z := hspliced
                        exact leOpt_trans (leOpt_trans (leOpt_trans h1 h2) h3) h4
                      have hlowOther : leOpt (minOpt L.full.lower (some p)) (δ s').x := by
                        rw [heqZ]
                        have hA : leOpt (minOpt L.full.lower (some p)) (δ s).x := by
                          have h1 : leOpt (minOpt L.full.lower (some p)) L.full.lower := minOpt_le_left L.full.lower (some p)
                          have h2 : leOpt L.full.lower (δ s).full := hLf.1
                          have h3 : leOpt (δ s).full (δ s).x := by rw [hmin s]; exact minOpt_le_left (δ s).x (δ s).z
                          exact leOpt_trans (leOpt_trans h1 h2) h3
                        have hB : leOpt (minOpt L.full.lower (some p)) (some p) := minOpt_le_right L.full.lower (some p)
                        exact leOpt_min (minOpt L.full.lower (some p)) (δ s).x (some p) hA hB
                      have hlow : leOpt (minOpt L.full.lower (some p)) (δ s').full := by
                        rw [hmin s']
                        exact leOpt_min (minOpt L.full.lower (some p)) (δ s').x (δ s').z hlowOther hlowSpliced
                      exact hlow
                    · -- full upper: δ'.full ≤ min(p, otherUpper=L.x.upper)
                      have hup1 : leOpt (δ s').full (δ s').x := by rw [hmin s']; exact minOpt_le_left (δ s').x (δ s').z
                      have hupA : leOpt (δ s').x (some p) := by rw [heqZ]; exact minOpt_le_right (δ s).x (some p)
                      have hupZ : leOpt (δ s').x L.x.upper := by
                        rw [heqZ]
                        have h1 : leOpt (minOpt (δ s).x (some p)) (δ s).x := minOpt_le_left (δ s).x (some p)
                        have h2 : leOpt (δ s).x L.x.upper := hLx.2
                        exact leOpt_trans h1 h2
                      have hup : leOpt (δ s').full (minOpt (some p) L.x.upper) := by
                        have hfull : leOpt (δ s').full (minOpt (some p) L.x.upper) :=
                          leOpt_trans hup1 (leOpt_min (δ s').x (some p) L.x.upper hupA hupZ)
                        exact hfull
                      exact hup
                  · constructor
                    · constructor
                      · have hlow : leOpt (minOpt L.x.lower (some p)) (δ s').x := by
                          rw [heqZ]; exact minOpt_monotone hLx.1 (leOpt_refl (some p))
                        exact hlow
                      · have hup : leOpt (δ s').x (minOpt L.x.upper (some p)) := by
                          rw [heqZ]; exact minOpt_monotone hLx.2 (leOpt_refl (some p))
                        exact hup
                    · constructor
                      · exact leOpt_trans hLz.1 hspliced
                      · exact leOpt_none (δ s').z

    | peel q τ r_id =>
        cases hEval with
        | peel _ _ _ _ _ _ =>
            simp [propagateCmd, Interval.contains]
            constructor
            · constructor
              · exact some_zero_leOpt (δ s').full
              · exact leOpt_none (δ s').full
            · constructor
              · constructor
                · exact some_zero_leOpt (δ s').x
                · exact leOpt_none (δ s').x
              · constructor
                · exact some_zero_leOpt (δ s').z
                · exact leOpt_none (δ s').z
    | puncture q =>
        cases hEval with
        | puncture _ _ _ =>
            simp [propagateCmd, Interval.contains]
            constructor
            · constructor
              · exact some_zero_leOpt (δ s').full
              · exact leOpt_none (δ s').full
            · constructor
              · constructor
                · exact some_zero_leOpt (δ s').x
                · exact leOpt_none (δ s').x
              · constructor
                · exact some_zero_leOpt (δ s').z
                · exact leOpt_none (δ s').z
    | extend delta adds =>
        cases hEval with
        | extend _ _ =>
            simp [propagateCmd, Interval.contains]
            constructor
            · constructor
              · exact some_zero_leOpt (δ s').full
              · exact leOpt_none (δ s').full
            · constructor
              · constructor
                · exact some_zero_leOpt (δ s').x
                · exact leOpt_none (δ s').x
              · constructor
                · exact some_zero_leOpt (δ s').z
                · exact leOpt_none (δ s').z
    | hadamard T =>
        cases hEval with
        | hadamard _ _ _ =>
            simp [propagateCmd, Interval.contains]
            constructor
            · constructor
              · exact some_zero_leOpt (δ s').full
              · exact leOpt_none (δ s').full
            · constructor
              · constructor
                · exact some_zero_leOpt (δ s').x
                · exact leOpt_none (δ s').x
              · constructor
                · exact some_zero_leOpt (δ s').z
                · exact leOpt_none (δ s').z
    | rebase sector matrix =>
        cases hEval with
        | rebase _ _ _ _ =>
            simp [propagateCmd, Interval.contains]
            constructor
            · constructor
              · exact some_zero_leOpt (δ s').full
              · exact leOpt_none (δ s').full
            · constructor
              · constructor
                · exact some_zero_leOpt (δ s').x
                · exact leOpt_none (δ s').x
              · constructor
                · exact some_zero_leOpt (δ s').z
                · exact leOpt_none (δ s').z
    | seq m1 m2 =>
        cases hEval with
        | seq _ _ =>
            simp [propagateCmd, Interval.contains]
            constructor
            · constructor
              · exact some_zero_leOpt (δ s').full
              · exact leOpt_none (δ s').full
            · constructor
              · constructor
                · exact some_zero_leOpt (δ s').x
                · exact leOpt_none (δ s').x
              · constructor
                · exact some_zero_leOpt (δ s').z
                · exact leOpt_none (δ s').z


theorem priced_interval_soundness_seq
  (δ : CodeState → ExactDist)
  (hmin : ∀ s, (δ s).full = minOpt (δ s).x (δ s).z)
  (hk0 : ∀ s, EncodingWellFormed s → stateK s = 0 →
      (δ s).full = none ∧ (δ s).x = none ∧ (δ s).z = none)
  (hdelete : ∀ r s s', EncodingWellFormed s → Eval (Command.delete r) s s' →
      leOpt (δ s').full (δ s).full ∧ leOpt (δ s').x (δ s).x ∧ leOpt (δ s').z (δ s).z)
  (hadd : ∀ sector support s s', EncodingWellFormed s →
      Eval (Command.addStab sector support) s s' →
      leOpt (δ s).full (δ s').full ∧ leOpt (δ s).x (δ s').x ∧ leOpt (δ s).z (δ s').z)
  (hgraft : ∀ q τ ids s s', EncodingWellFormed s → Eval (Command.graft q τ ids) s s' →
      (if τ = Sector.X then leOpt (δ s).x (δ s').x else leOpt (δ s).z (δ s').z) ∧
      (if τ = Sector.X then leOpt (δ s').z (δ s).z else leOpt (δ s').x (δ s).x))
  (H : Hyp)
  {s t u : CodeState} {m1 m2 : Command}
  (hwf : EncodingWellFormed s)
  (h1 : Eval m1 s t) (h2 : Eval m2 t u)
  (hH1 : HypTrue δ H m1 s t) (hH2 : HypTrue δ H m2 t u)
  (L : DistanceLedger) (hL : LedgerSound (δ s) L) :
  LedgerSound (δ u) (propagateCmdK m2 t u (propagateCmdK m1 s t L H) H) := by
  have hstep1 := priced_interval_soundness δ hmin hk0 hdelete hadd hgraft H L s t m1 hwf h1 hH1 hL
  exact priced_interval_soundness δ hmin hk0 hdelete hadd hgraft H (propagateCmdK m1 s t L H) t u
    m2 (wf_of_eval_all h1 hwf) h2 hH2 hstep1


/-! ### Monotonicity of the per-step transport (§8.4.2, §9.4)

`spec/JUDGMENT_LAYER.md` §8.4(2) requires every interval transformer to be
monotone in the precision order, and §9.4 lists the per-move lemmas;
`spec/OPERATIONAL_SEMANTICS.md` §4.32 closes the Gate 6 cells with the same
argument. The order below mirrors `AbsInterval.preciseLe` (the S2 schema,
`Interval.lean`) at the executable ledger: `a.refines b` reads "`a` is at
least as precise as `b`" — the smaller interval first. The soundness half is
`priced_interval_soundness` above; this is the monotone half, which is what
licenses tightening an input ledger before transporting it. No cell's
evidence status depends on this section (a transcription aid, as in
`Refinement.lean`). -/

/-- Precision order on an executable interval: `a.refines b` iff `a` is at
    least as precise as `b`, componentwise — the `leOpt` mirror of
    `AbsInterval.preciseLe`. -/
def Interval.refines (a b : Interval) : Prop :=
  leOpt b.lower a.lower ∧ leOpt a.upper b.upper

/-- Componentwise lift of the precision order to the ledger. -/
def DistanceLedger.refines (a b : DistanceLedger) : Prop :=
  a.full.refines b.full ∧ a.x.refines b.x ∧ a.z.refines b.z

theorem Interval.refines_refl (a : Interval) : a.refines a :=
  ⟨leOpt_refl a.lower, leOpt_refl a.upper⟩

theorem DistanceLedger.refines_refl (a : DistanceLedger) : a.refines a :=
  ⟨Interval.refines_refl a.full, Interval.refines_refl a.x, Interval.refines_refl a.z⟩

theorem Interval.refines_trans {a b c : Interval} (hab : a.refines b) (hbc : b.refines c) :
    a.refines c :=
  ⟨leOpt_trans hbc.1 hab.1, leOpt_trans hab.2 hbc.2⟩

theorem DistanceLedger.refines_trans {a b c : DistanceLedger} (hab : a.refines b)
    (hbc : b.refines c) : a.refines c :=
  ⟨Interval.refines_trans hab.1 hbc.1, Interval.refines_trans hab.2.1 hbc.2.1,
    Interval.refines_trans hab.2.2 hbc.2.2⟩

/-- Every per-step transformer is monotone in the precision order
    (`spec/JUDGMENT_LAYER.md` §8.4(2), §9.4): a tighter input ledger maps to
    a tighter output ledger. The wildcard cases below are the *widened*
    transports (`C-SEQUENCE`, `P-REBASE`, `E-LOCAL-HADAMARD`, `E-PEEL`,
    `E-PUNCTURE`, `E-EXTEND`): they ignore the input ledger and are therefore
    monotone as constants. They are strictly coarser than the §4.32
    transformers for `P-REBASE` (identity), `E-LOCAL-HADAMARD` (sector swap),
    and `E-EXTEND` with `Δ = ∅` (lower carry); for those, what is proved here
    is monotonicity of a constant map, not of §4.32's claim. -/
theorem propagateCmd_monotone (m : Command) (s s' : CodeState) (H : Hyp)
    (L1 L2 : DistanceLedger) (h : L1.refines L2) :
    (propagateCmd m s s' L1 H).refines (propagateCmd m s s' L2 H) := by
  cases m with
  | skip => exact h
  | delete r =>
      rcases h with ⟨hf, hx, hz⟩
      cases hp : H.deletionPrice with
      | none =>
          simp only [propagateCmd, hp, DistanceLedger.refines, Interval.refines]
          exact ⟨⟨leOpt_refl (some 0), hf.2⟩, ⟨leOpt_refl (some 0), hx.2⟩,
            ⟨leOpt_refl (some 0), hz.2⟩⟩
      | some pair =>
          rcases pair with ⟨wd, we⟩
          simp only [propagateCmd, hp, DistanceLedger.refines, Interval.refines]
          exact ⟨⟨minOpt_monotone hf.1 (leOpt_refl (some (min wd we))),
              minOpt_monotone hf.2 (leOpt_refl (some (min wd we)))⟩,
            ⟨leOpt_refl (some 0), hx.2⟩, ⟨leOpt_refl (some 0), hz.2⟩⟩
  | addStab sector support =>
      rcases h with ⟨hf, hx, hz⟩
      simp only [propagateCmd, DistanceLedger.refines, Interval.refines]
      exact ⟨⟨hf.1, leOpt_refl none⟩, ⟨hx.1, leOpt_refl none⟩,
        ⟨hz.1, leOpt_refl none⟩⟩
  | graft q τ ids =>
      rcases h with ⟨hf, hx, hz⟩
      cases hp : H.graftPrice with
      | none =>
          cases τ with
          | X =>
              simp only [propagateCmd, hp, DistanceLedger.refines, Interval.refines]
              exact ⟨⟨leOpt_refl (some 0), hz.2⟩, ⟨hx.1, leOpt_refl none⟩,
                ⟨leOpt_refl (some 0), hz.2⟩⟩
          | Z =>
              simp only [propagateCmd, hp, DistanceLedger.refines, Interval.refines]
              exact ⟨⟨leOpt_refl (some 0), hx.2⟩, ⟨leOpt_refl (some 0), hx.2⟩,
                ⟨hz.1, leOpt_refl none⟩⟩
      | some price =>
          cases τ with
          | X =>
              simp only [propagateCmd, hp, DistanceLedger.refines, Interval.refines]
              exact ⟨⟨minOpt_monotone hf.1 (leOpt_refl (some price)),
                  minOpt_monotone (leOpt_refl (some price)) hz.2⟩,
                ⟨hx.1, leOpt_refl none⟩,
                ⟨minOpt_monotone hz.1 (leOpt_refl (some price)),
                  minOpt_monotone hz.2 (leOpt_refl (some price))⟩⟩
          | Z =>
              simp only [propagateCmd, hp, DistanceLedger.refines, Interval.refines]
              exact ⟨⟨minOpt_monotone hf.1 (leOpt_refl (some price)),
                  minOpt_monotone (leOpt_refl (some price)) hx.2⟩,
                ⟨minOpt_monotone hx.1 (leOpt_refl (some price)),
                  minOpt_monotone hx.2 (leOpt_refl (some price))⟩,
                ⟨hz.1, leOpt_refl none⟩⟩
  | peel a b c => exact DistanceLedger.refines_refl _
  | puncture a => exact DistanceLedger.refines_refl _
  | extend a b => exact DistanceLedger.refines_refl _
  | hadamard a => exact DistanceLedger.refines_refl _
  | rebase a b => exact DistanceLedger.refines_refl _
  | seq m1 m2 => exact DistanceLedger.refines_refl _

/-- The same for the transported output including the `k = 0` collapse: the
    collapsed ledger is constant in the input, hence monotone. -/
theorem propagateCmdK_monotone (m : Command) (s s' : CodeState) (H : Hyp)
    (L1 L2 : DistanceLedger) (h : L1.refines L2) :
    (propagateCmdK m s s' L1 H).refines (propagateCmdK m s s' L2 H) := by
  by_cases hk : stateK s' = 0
  · have e1 : propagateCmdK m s s' L1 H =
        { full := Interval.mk none none, x := Interval.mk none none,
          z := Interval.mk none none } := by simp [propagateCmdK, hk]
    have e2 : propagateCmdK m s s' L2 H =
        { full := Interval.mk none none, x := Interval.mk none none,
          z := Interval.mk none none } := by simp [propagateCmdK, hk]
    rw [e1, e2]
    exact DistanceLedger.refines_refl _
  · have e1 : propagateCmdK m s s' L1 H = propagateCmd m s s' L1 H := by
      simp [propagateCmdK, hk]
    have e2 : propagateCmdK m s s' L2 H = propagateCmd m s s' L2 H := by
      simp [propagateCmdK, hk]
    rw [e1, e2]
    exact propagateCmd_monotone m s s' H L1 L2 h

/-- The `C-SEQUENCE` row of §9.4 at the executable layer: the two-step
    composite transport of `priced_interval_soundness_seq` is monotone in the
    input ledger. -/
theorem propagateCmdK_monotone_seq (m1 m2 : Command) (s t u : CodeState) (H : Hyp)
    (L1 L2 : DistanceLedger) (h : L1.refines L2) :
    (propagateCmdK m2 t u (propagateCmdK m1 s t L1 H) H).refines
      (propagateCmdK m2 t u (propagateCmdK m1 s t L2 H) H) :=
  propagateCmdK_monotone m2 t u H _ _ (propagateCmdK_monotone m1 s t H L1 L2 h)

end CodeCalculus
