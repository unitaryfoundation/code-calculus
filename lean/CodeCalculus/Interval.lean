import CodeCalculus.State

/-! This file states the S2 schema only: the concrete/abstract domains, the
    concretization, the precision order, and the soundness/monotonicity/
    composition schema. It does not instantiate `Sound` or `Monotone` for any
    ledger transformer; `PricedInterval.propagateCmd`,
    `priced_interval_soundness`, and `propagateCmd_monotone` are the
    corresponding instances in `PricedInterval.lean`. The two meet lemmas are
    facts about `ExtNat`. -/

namespace CodeCalculus

/-- Extended natural: the concrete distance domain `D = N ∪ {+∞}`. -/
inductive ExtNat where
  | finite : Nat -> ExtNat
  | inf : ExtNat
  deriving Repr, BEq, DecidableEq

/-- Concrete order on the extended natural domain (the natural order). -/
def ExtNat.le : ExtNat -> ExtNat -> Prop
  | .finite a, .finite b => a <= b
  | .finite _, .inf => True
  | .inf, .finite _ => False
  | .inf, .inf => True

instance : LE ExtNat where
  le := ExtNat.le

/-- The meet (min) of two extended naturals, used for the disjunctive half
    `d = min(d_X, d_Z)`. -/
def ExtNat.min : ExtNat -> ExtNat -> ExtNat
  | .finite a, .finite b => .finite (Nat.min a b)
  | .finite a, .inf => .finite a
  | .inf, .finite b => .finite b
  | .inf, .inf => .inf

/-- An interval in the abstract domain. -/
structure AbsInterval where
  L : ExtNat
  U : ExtNat
  le : L <= U

/-- Concretization: the set of concrete distances contained in an interval. -/
def gamma (I : AbsInterval) (d : ExtNat) : Prop :=
  I.L <= d /\ d <= I.U

/-- Precision order on intervals: smaller interval = more precise. -/
def AbsInterval.preciseLe (a b : AbsInterval) : Prop :=
  b.L <= a.L /\ a.U <= b.U

/-- The top of the precision order: `[0, +∞]`. -/
def topInterval : AbsInterval where
  L := ExtNat.finite 0
  U := ExtNat.inf
  le := by
    show ExtNat.finite 0 <= ExtNat.inf
    trivial

/-- A transformer is sound for a concrete step relation when containment is
    preserved — the S2 schema's soundness half (JUDGMENT_LAYER §8.4.1). -/
def Sound (step : ExtNat -> ExtNat -> Prop) (F : AbsInterval -> AbsInterval) : Prop :=
  ∀ (a : AbsInterval) (d d' : ExtNat),
    gamma a d -> step d d' -> gamma (F a) d'

/-- A transformer is monotone in the precision order — the S2 schema's
    monotonicity half (JUDGMENT_LAYER §8.4.2), stated in `preciseLe`, never
    in the information order. -/
def Monotone (F : AbsInterval -> AbsInterval) : Prop :=
  ∀ (a b : AbsInterval), a.preciseLe b -> (F a).preciseLe (F b)

/-- Relational composition of two concrete step relations. -/
def StepComp (R S : ExtNat -> ExtNat -> Prop) : ExtNat -> ExtNat -> Prop :=
  fun d d' => ∃ mid, R d mid /\ S mid d'

/-- Composition theorem: sound and monotone transformers compose — the S2
    composition theorem (JUDGMENT_LAYER §8.5), the schema behind the
    `C-SEQUENCE` distance rows. -/
theorem compose_sound (R S : ExtNat -> ExtNat -> Prop)
    (F G : AbsInterval -> AbsInterval)
    (hF : Sound R F) (hG : Sound S G) :
    Sound (StepComp R S) (fun a => G (F a)) := by
  intro a d d' ha hstep
  rcases hstep with ⟨mid, hR, hS⟩
  have hmid : gamma (F a) mid := hF a d mid ha hR
  exact hG (F a) mid d' hmid hS

theorem compose_monotone (F G : AbsInterval -> AbsInterval)
    (mF : Monotone F) (mG : Monotone G) :
    Monotone (fun a => G (F a)) := by
  intro a b hab
  exact mG (F a) (F b) (mF a b hab)

/-- The full distance is at most either sector distance — the meet direction
    of the disjunctive half `d = min(d_X, d_Z)` (JUDGMENT_LAYER §8.8). -/
theorem ExtNat.min_le_left (a b : ExtNat) : ExtNat.min a b <= a := by
  cases a with
  | finite an =>
      cases b with
      | finite bn => exact Nat.min_le_left an bn
      | inf => exact Nat.le_refl an
  | inf =>
      cases b with
      | finite _ => trivial
      | inf => trivial

theorem ExtNat.min_le_right (a b : ExtNat) : ExtNat.min a b <= b := by
  cases a with
  | finite an =>
      cases b with
      | finite bn => exact Nat.min_le_right an bn
      | inf => trivial
  | inf =>
      cases b with
      | finite bn => exact Nat.le_refl bn
      | inf => trivial

end CodeCalculus
