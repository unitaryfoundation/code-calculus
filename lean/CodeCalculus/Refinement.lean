import CodeCalculus.State
import CodeCalculus.Interval

/-!
# The consumer refinement preorder (S3)

`spec/JUDGMENT_LAYER.md` §9. The preorder `LedgerState.refines` is the
componentwise precision order of S2's `AbsInterval.preciseLe`, lifted to the
product of the full-distance and two sector intervals. The `certify` and
`prune` verdicts of the §2b decision rule are monotone in this order:
refinement preserves both, and the two halves of the order match the two
verdicts.

This file is a transcription aid, not a proof-assistant result; it does not
establish soundness and no cell's evidence status depends on it.
-/

namespace CodeCalculus

/-! ## ExtNat order lemmas

`Interval.lean` declares the `LE ExtNat` instance but no order lemmas; they are
stated here to keep the S2 file's surface unchanged. -/

theorem ExtNat.le_refl (a : ExtNat) : a ≤ a := by
  cases a with
  | finite n => exact Nat.le_refl n
  | inf => trivial

theorem ExtNat.le_trans {a b c : ExtNat} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  cases a with
  | finite an =>
    cases b with
    | finite bn =>
      cases c with
      | finite cn => exact Nat.le_trans hab hbc
      | inf => trivial
    | inf =>
      cases c with
      | finite _ => exact absurd hbc (fun h => h)
      | inf => trivial
  | inf =>
    cases b with
    | finite _ => exact absurd hab (fun h => h)
    | inf =>
      cases c with
      | finite _ => exact absurd hbc (fun h => h)
      | inf => trivial

theorem ExtNat.le_inf (a : ExtNat) : a ≤ .inf := by
  cases a <;> trivial

theorem ExtNat.zero_le (a : ExtNat) : .finite 0 ≤ a := by
  cases a with
  | finite n => exact Nat.zero_le n
  | inf => trivial

instance (a b : ExtNat) : Decidable (a ≤ b) := by
  cases a with
  | finite an =>
    cases b with
    | finite bn => exact Nat.decLe an bn
    | inf => exact isTrue trivial
  | inf =>
    cases b with
    | finite _ => exact isFalse (fun h => h)
    | inf => exact isTrue trivial

/-! ## The preorder -/

/-- A consumer ledger state: the full-distance interval together with its two
    sector intervals (the reduced product of `JUDGMENT_LAYER` §8.8, held here
    as a plain triple — the product constraint is a side condition on the
    transformers, not on the order). -/
structure LedgerState where
  full : AbsInterval
  x : AbsInterval
  z : AbsInterval

/-- The consumer refinement preorder (`JUDGMENT_LAYER` §9.1, form (a)).
    `A refines B` (read "A is at least as informative as B") iff each axis's
    interval for `A` is at least as precise as `B`'s. -/
def LedgerState.refines (A B : LedgerState) : Prop :=
  A.full.preciseLe B.full ∧ A.x.preciseLe B.x ∧ A.z.preciseLe B.z

/-- The lower half of the preorder: `A`'s lower bounds are at least `B`'s. -/
def LedgerState.refinesLow (A B : LedgerState) : Prop :=
  B.full.L ≤ A.full.L ∧ B.x.L ≤ A.x.L ∧ B.z.L ≤ A.z.L

/-- The upper half of the preorder: `A`'s upper bounds are at most `B`'s. -/
def LedgerState.refinesUp (A B : LedgerState) : Prop :=
  A.full.U ≤ B.full.U ∧ A.x.U ≤ B.x.U ∧ A.z.U ≤ B.z.U

/-- The two halves decompose the preorder. -/
theorem refines_iff (A B : LedgerState) :
    A.refines B ↔ A.refinesLow B ∧ A.refinesUp B := by
  constructor
  · intro h
    rcases h with ⟨hf, hx, hz⟩
    rcases hf with ⟨hfl, hfu⟩
    rcases hx with ⟨hxl, hxu⟩
    rcases hz with ⟨hzl, hzu⟩
    exact ⟨⟨hfl, hxl, hzl⟩, ⟨hfu, hxu, hzu⟩⟩
  · intro h
    rcases h with ⟨⟨hfl, hxl, hzl⟩, ⟨hfu, hxu, hzu⟩⟩
    exact ⟨⟨hfl, hfu⟩, ⟨hxl, hxu⟩, ⟨hzl, hzu⟩⟩

/-- The preorder is reflexive. -/
theorem refines_refl (A : LedgerState) : A.refines A := by
  constructor
  · exact ⟨ExtNat.le_refl A.full.L, ExtNat.le_refl A.full.U⟩
  · constructor
    · exact ⟨ExtNat.le_refl A.x.L, ExtNat.le_refl A.x.U⟩
    · exact ⟨ExtNat.le_refl A.z.L, ExtNat.le_refl A.z.U⟩

/-- The preorder is transitive. -/
theorem refines_trans {A B C : LedgerState}
    (hab : A.refines B) (hbc : B.refines C) : A.refines C := by
  rcases hab with ⟨⟨hAfl, hAfu⟩, ⟨hAxl, hAxu⟩, ⟨hAzl, hAzu⟩⟩
  rcases hbc with ⟨⟨hBfl, hBfu⟩, ⟨hBxl, hBxu⟩, ⟨hBzl, hBzu⟩⟩
  exact ⟨⟨ExtNat.le_trans hBfl hAfl, ExtNat.le_trans hAfu hBfu⟩,
         ⟨ExtNat.le_trans hBxl hAxl, ExtNat.le_trans hAxu hBxu⟩,
         ⟨ExtNat.le_trans hBzl hAzl, ExtNat.le_trans hAzu hBzu⟩⟩

/-! ## Verdicts -/

/-- The three consumer verdicts of `spec/JUDGMENT_LAYER.md` §2b. Mirrors
    `machine/priced_calculus.py`'s `DistanceLedger.decide` return values. -/
inductive Verdict where
  | certify
  | remeasure
  | prune
  deriving Repr, BEq, DecidableEq

/-- `certify t` on interval `L`: the lower endpoint reaches the target. -/
def isCertify (L : AbsInterval) (t : ExtNat) : Prop := t ≤ L.L

/-- `prune t` on interval `L`: the upper endpoint is a strict upper bound
    below the target. Because `L.L ≤ L.U` holds by well-formedness,
    `¬ (t ≤ L.U)` already forces `¬ (t ≤ L.L)`; the two conditions in the §2b
    rule coincide for well-formed intervals. -/
def isPrune (L : AbsInterval) (t : ExtNat) : Prop := ¬ (t ≤ L.U)

/-- `certify` and `prune` are mutually exclusive on a well-formed interval. -/
theorem certify_not_prune (L : AbsInterval) (t : ExtNat)
    (hc : isCertify L t) : ¬ isPrune L t := by
  intro hp
  exact hp (ExtNat.le_trans hc L.le)

/-- The verdict of the §2b decision rule on the full distance. -/
def verdictAt (L : AbsInterval) (t : ExtNat) : Verdict :=
  if t ≤ L.L then .certify
  else if ¬ (t ≤ L.U) then .prune
  else .remeasure

theorem verdictAt_certify (L : AbsInterval) (t : ExtNat) (h : t ≤ L.L) :
    verdictAt L t = .certify := by
  unfold verdictAt
  rw [if_pos h]

theorem verdictAt_prune (L : AbsInterval) (t : ExtNat)
    (hL : ¬ (t ≤ L.L)) (hU : ¬ (t ≤ L.U)) :
    verdictAt L t = .prune := by
  unfold verdictAt
  rw [if_neg hL, if_pos hU]

theorem verdictAt_remeasure (L : AbsInterval) (t : ExtNat)
    (hL : ¬ (t ≤ L.L)) (hU : t ≤ L.U) :
    verdictAt L t = .remeasure := by
  unfold verdictAt
  have hU' : ¬ (¬ (t ≤ L.U)) := fun hn => hn hU
  rw [if_neg hL, if_neg hU']

/-! ## Verdict monotonicity -/

/-- `certify` is downward-closed under the lower half of the preorder: refining
    a certifying ledger preserves `certify` (`JUDGMENT_LAYER` §9.2, clause 1). -/
theorem certify_monotone_low {A B : LedgerState} {t : ExtNat}
    (h : A.refinesLow B)
    (hb : isCertify B.full t) :
    isCertify A.full t := by
  rcases h with ⟨hfl, _, _⟩
  exact ExtNat.le_trans hb hfl

/-- `prune` is downward-closed under the upper half of the preorder: refining a
    pruning ledger preserves `prune` (`JUDGMENT_LAYER` §9.2, clause 2). -/
theorem prune_monotone_up {A B : LedgerState} {t : ExtNat}
    (h : A.refinesUp B)
    (hb : isPrune B.full t) :
    isPrune A.full t := by
  rcases h with ⟨hfu, _, _⟩
  intro hA
  exact hb (ExtNat.le_trans hA hfu)

/-- Verdict monotonicity, `certify` half, in the combined order. -/
theorem verdict_monotone_certify {A B : LedgerState} {t : ExtNat}
    (h : A.refines B)
    (hb : verdictAt B.full t = .certify) :
    verdictAt A.full t = .certify := by
  rcases refines_iff A B |>.mp h with ⟨hlow, _⟩
  by_cases htB : t ≤ B.full.L
  · exact verdictAt_certify A.full t (certify_monotone_low hlow htB)
  · exfalso
    unfold verdictAt at hb
    rw [if_neg htB] at hb
    by_cases huB : ¬ (t ≤ B.full.U)
    · rw [if_pos huB] at hb
      cases hb
    · rw [if_neg huB] at hb
      cases hb

/-- Verdict monotonicity, `prune` half, in the combined order. -/
theorem verdict_monotone_prune {A B : LedgerState} {t : ExtNat}
    (h : A.refines B)
    (hb : verdictAt B.full t = .prune) :
    verdictAt A.full t = .prune := by
  rcases refines_iff A B |>.mp h with ⟨_, hup⟩
  by_cases htB : t ≤ B.full.L
  · exfalso
    unfold verdictAt at hb
    rw [if_pos htB] at hb
    cases hb
  · unfold verdictAt at hb
    rw [if_neg htB] at hb
    by_cases huB : ¬ (t ≤ B.full.U)
    · rw [if_pos huB] at hb
      have hnu : ¬ (t ≤ A.full.U) := by
        intro hA
        exact huB (ExtNat.le_trans hA hup.1)
      have hnl : ¬ (t ≤ A.full.L) := by
        intro hA
        exact hnu (ExtNat.le_trans (ExtNat.le_trans hA A.full.le) (ExtNat.le_refl _))
      exact verdictAt_prune A.full t hnl hnu
    · rw [if_neg huB] at hb
      cases hb

/-! ## Reference ledgers and the verdict derivation -/

/-- The reference ledger for `certify t`: `[t, +∞]`. Any ledger refining it
    has `L ≥ t` and hence certifies `t` (`JUDGMENT_LAYER` §9.3). -/
def certRef (t : ExtNat) : AbsInterval where
  L := t
  U := .inf
  le := ExtNat.le_inf t

/-- The reference ledger for `prune (n+1)`: `[0, n]`. -/
def pruneRef (n : Nat) : AbsInterval where
  L := .finite 0
  U := .finite n
  le := ExtNat.zero_le (.finite n)

/-- Verdict derivation, `certify` half: the full-distance ledger certifies `t`
    iff it refines `certRef t`. -/
theorem certify_iff_refines_certRef (L : AbsInterval) (t : ExtNat) :
    isCertify L t ↔ L.preciseLe (certRef t) := by
  constructor
  · intro h
    exact ⟨h, ExtNat.le_inf L.U⟩
  · intro h
    exact h.1

/-- Verdict derivation, `prune` half (finite `t = n+1`): the full-distance
    ledger prunes `t` iff it refines `pruneRef n`. -/
theorem prune_iff_refines_pruneRef (L : AbsInterval) (n : Nat) :
    isPrune L (.finite (n + 1)) ↔ L.preciseLe (pruneRef n) := by
  rcases L with ⟨LL, UL, Lle⟩
  cases UL with
  | inf =>
    constructor
    · intro h
      exact False.elim (h (by trivial))
    · intro h
      exact False.elim h.2
  | finite u =>
    constructor
    · intro h
      refine ⟨ExtNat.zero_le LL, ?_⟩
      show ExtNat.finite u ≤ ExtNat.finite n
      exact Nat.le_of_not_gt (fun hgt => h (Nat.succ_le_of_lt hgt))
    · intro h
      intro hle
      have hU' : u ≤ n := h.2
      have hle' : n + 1 ≤ u := hle
      omega

end CodeCalculus
