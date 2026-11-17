import CodeCalculus.Soundness
import CodeCalculus.KernelObligations
import CodeCalculus.Fixtures
import CodeCalculus.Interval

/-!
# The exact distance as a concrete measure (issue #265, Route B of #230)

`judgment_soundness` (`Soundness.lean`) takes one hypothesis about the
distance measure, `MeasureMonotone dMeasure`, and Route A of issue #230
reduced it to `SpanMonotone`: on a fixed namespace, shrinking both sector
spans does not raise either sector distance. This module defines the exact
sector distance over `F₂` vectors and proves that it is span-monotone, so the
metatheorem holds for it with no measure hypothesis left
(`judgment_soundness_exact`).

The definition. For a state `s` with `n = s.Q.length`, a σ-logical is a
vector `v ∈ F₂^n` orthogonal to every displayed row of the opposite sector and
outside the `F₂`-span of the displayed σ-rows; `exactDistance σ s` is the least
Hamming weight of a σ-logical. When no σ-logical exists (every vector outside
the σ-span fails orthogonality, which is the `k = 0` case for a well-formed
state) the value is `n + 1`.

The `+∞` value (issue #310). The spec's distance domain is `ℕ ∪ {+∞}`
(`spec/JUDGMENT_LAYER.md` §8.1), and the development reads it in three ways:
`exactDistance?` in `Option Nat` with `none` for `+∞`, the reading of the
executable ledger (`PricedInterval.lean`); `exactDistanceExt` in the S2
concrete domain `ExtNat` (`Interval.lean`), through `ExtNat.ofOption`; and
`exactDistance` in `Nat`, which is the `Option` reading with the sentinel
`n + 1` as its default (`exactDistance_eq_getD`). The sentinel is exact: a
σ-logical has weight at most `n`, so `exactDistance σ s = n + 1` holds
exactly when there is no σ-logical (`exactDistance_eq_sentinel_iff`), and on
a common namespace length the `Nat` order of two sentinel readings is the
`ExtNat` order of the two distances (`exactDistance_le_iff_ext`). The `k`
cells and the `+∞` value are connected in `ExactPeel.lean`: a well-formed
state with `k = 0` has no logical (`exactDist_k0`, the `hk0` hypothesis of
`priced_interval_soundness`, issue #338).

The sentence-language measure `dMeasure : Field → CodeState → Nat` of
`Soundness.lean` stays `Nat`-valued by decision, recorded in that module's
note: its distance rows are monotonicity facts over one namespace, where the
sentinel order is the `ExtNat` order, and no row produces or needs a `+∞`
value; `exactMeasure` reads `exactDistance`, and the §4.3 and §4.5 laws are
restated in `ExtNat` below (`exactDistanceExt_delete_le`,
`exactDistanceExt_add_le`).

Everything is stated over vectors (`rowVector`, `inSpanRows`), not bitmasks,
because `SpanLE` is stated over vectors and the vector-to-mask bridge needs a
repeat-free namespace that `SpanMonotone` does not assume.

Opacity (D2) is preserved: `exactMeasure` is a definition used in a proof
about the metatheorem, not a rule that computes a distance, and no derivation
rule reads it. The definition is computable, so the sanity checks at the end
compare it by kernel `decide` with the hand-computed distances the fixtures
record.
-/

namespace CodeCalculus

/-! ## Overlap parity over `F₂` vectors -/

/-- The number of positions where both vectors are `true`. -/
def dotPar : List Bool → List Bool → Nat
  | x :: xs, y :: ys => (if x && y then 1 else 0) + dotPar xs ys
  | _, _ => 0

/-- Hamming weight. -/
def weight (v : List Bool) : Nat := v.count true

theorem dotPar_xorVec (v : List Bool) : ∀ (a b : List Bool), a.length = b.length →
    dotPar v (xorVec a b) % 2 = (dotPar v a + dotPar v b) % 2 := by
  induction v with
  | nil => intro a b _; simp [dotPar]
  | cons c cs ih =>
      intro a b hab
      cases a with
      | nil =>
          cases b with
          | nil => simp [xorVec, dotPar]
          | cons _ _ => cases hab
      | cons x xs =>
          cases b with
          | nil => simp at hab
          | cons y ys =>
              simp only [List.length_cons, Nat.add_right_cancel_iff] at hab
              have h := ih xs ys hab
              simp only [xorVec, dotPar]
              cases c <;> cases x <;> cases y <;> simp <;> omega

theorem dotPar_replicate_false (v : List Bool) : ∀ n : Nat,
    dotPar v (List.replicate n false) = 0 := by
  induction v with
  | nil => intro n; cases n <;> simp [dotPar]
  | cons c cs ih =>
      intro n
      cases n with
      | zero => simp [dotPar]
      | succ n => simp [List.replicate_succ, dotPar, ih]

/-- Orthogonality to every generator extends to every `F₂` combination. -/
theorem dotPar_combineRows_even (n : Nat) (v : List Bool) :
    ∀ (vs : List (List Bool)) (cs : List Bool),
      (∀ u ∈ vs, u.length = n) → (∀ u ∈ vs, dotPar v u % 2 = 0) →
      dotPar v (combineRows n vs cs) % 2 = 0 := by
  intro vs
  induction vs with
  | nil => intro cs _ _; simp [combineRows, dotPar_replicate_false]
  | cons u us ih =>
      intro cs hlen h
      cases cs with
      | nil => simp [combineRows, dotPar_replicate_false]
      | cons c cs' =>
          have hlen' : ∀ w ∈ us, w.length = n := fun w hw => hlen w (List.mem_cons_of_mem u hw)
          have h' : ∀ w ∈ us, dotPar v w % 2 = 0 := fun w hw => h w (List.mem_cons_of_mem u hw)
          cases c with
          | true =>
              show dotPar v (xorVec u (combineRows n us cs')) % 2 = 0
              rw [dotPar_xorVec v u _ (by rw [hlen u (List.mem_cons_self ..), combineRows_length n us cs' hlen'])]
              have h1 := h u (List.mem_cons_self ..)
              have h2 := ih cs' hlen' h'
              omega
          | false =>
              show dotPar v (combineRows n us cs') % 2 = 0
              exact ih cs' hlen' h'

/-- A vector orthogonal to every row is orthogonal to every vector of their span. -/
theorem dotPar_even_of_inSpanRows (Q : List Nat) (rows : List Row) (v w : List Bool)
    (hw : inSpanRows Q rows w) (h : ∀ r ∈ rows, dotPar v (rowVector Q r) % 2 = 0) :
    dotPar v w % 2 = 0 := by
  obtain ⟨cs, _, hcomb⟩ := hw
  rw [← hcomb]
  apply dotPar_combineRows_even Q.length v _ cs (rowVectors_length Q rows)
  intro u hu
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hu
  exact h r hr

/-! ## Logicals and the exact distance -/

/-- `v` is a σ-logical of `s`: orthogonal to every displayed row of the opposite
    sector and outside the span of the displayed σ-rows. -/
def isLogicalBool (s : CodeState) (σ : Sector) (v : List Bool) : Bool :=
  (sectorRows s (oppositeSector σ)).all (fun r => dotPar v (rowVector s.Q r) % 2 == 0) &&
  !inSpanRowsBool s.Q (sectorRows s σ) v

/-- The σ-logicals of `s`, as vectors of length `|Q|`. -/
def logicalVectors (s : CodeState) (σ : Sector) : List (List Bool) :=
  (allBoolLists s.Q.length).filter (isLogicalBool s σ)

/-- Minimum weight over a list of vectors, `init` for the empty list. -/
def minWeight (init : Nat) : List (List Bool) → Nat
  | [] => init
  | v :: vs => min (weight v) (minWeight init vs)

/-- The exact σ-distance of `s` in `Nat`; `s.Q.length + 1` is the value when
    there is no σ-logical, the sentinel for `+∞` (`exactDistance_eq_getD`,
    `exactDistance_eq_sentinel_iff`). -/
def exactDistance (σ : Sector) (s : CodeState) : Nat :=
  minWeight (s.Q.length + 1) (logicalVectors s σ)

/-- The exact distance as a measure for `judgment_soundness`: the two sector
    fields read `exactDistance`; `fieldValue` reads `n`, `k`, and `d` itself. -/
def exactMeasure : Field → CodeState → Nat
  | Field.dX, s => exactDistance Sector.X s
  | Field.dZ, s => exactDistance Sector.Z s
  | _, _ => 0

/-! ## Minimum-weight bookkeeping -/

theorem minWeight_le_init (init : Nat) : ∀ vs : List (List Bool), minWeight init vs ≤ init
  | [] => Nat.le_refl init
  | _ :: vs => Nat.le_trans (Nat.min_le_right _ _) (minWeight_le_init init vs)

theorem minWeight_le_of_mem (init : Nat) {v : List Bool} :
    ∀ vs : List (List Bool), v ∈ vs → minWeight init vs ≤ weight v
  | [], h => by simp at h
  | w :: vs, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact Nat.min_le_left _ _
      · exact Nat.le_trans (Nat.min_le_right _ _) (minWeight_le_of_mem init vs h')

theorem minWeight_attained (init : Nat) : ∀ vs : List (List Bool),
    minWeight init vs = init ∨ ∃ v ∈ vs, minWeight init vs = weight v
  | [] => Or.inl rfl
  | w :: vs => by
      show min (weight w) (minWeight init vs) = init ∨
        ∃ v ∈ w :: vs, min (weight w) (minWeight init vs) = weight v
      rcases Nat.le_total (weight w) (minWeight init vs) with hle | hge
      · exact Or.inr ⟨w, List.mem_cons_self .., Nat.min_eq_left hle⟩
      · rw [Nat.min_eq_right hge]
        rcases minWeight_attained init vs with h | ⟨v, hv, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨v, List.mem_cons_of_mem w hv, h⟩

/-- A larger set of candidates has a minimum no larger. -/
theorem minWeight_mono (init : Nat) (vs ws : List (List Bool)) (h : ∀ v ∈ vs, v ∈ ws) :
    minWeight init ws ≤ minWeight init vs := by
  rcases minWeight_attained init vs with hinit | ⟨v, hv, hval⟩
  · rw [hinit]; exact minWeight_le_init init ws
  · rw [hval]; exact minWeight_le_of_mem init ws (h v hv)

/-! ## The computable span test agrees with the span predicate -/

theorem exact_mem_allBoolLists : ∀ (n : Nat) (cs : List Bool),
    cs ∈ allBoolLists n ↔ cs.length = n
  | 0, cs => by
      simp only [allBoolLists, List.mem_singleton, List.length_eq_zero_iff]
  | n + 1, cs => by
      simp only [allBoolLists, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨bs, hbs, h⟩
        have hlen := (exact_mem_allBoolLists n bs).mp hbs
        rcases h with rfl | rfl <;> simp [hlen]
      · intro h
        cases cs with
        | nil => cases h
        | cons b bs =>
            refine ⟨bs, (exact_mem_allBoolLists n bs).mpr (by simpa using h), ?_⟩
            cases b <;> simp

theorem exact_inSpanRowsBool_iff (Q : List Nat) (rows : List Row) (target : List Bool) :
    inSpanRowsBool Q rows target = true ↔ inSpanRows Q rows target := by
  simp only [inSpanRowsBool, inSpanRows, List.any_eq_true, beq_iff_eq, exact_mem_allBoolLists]

/-! ## Monotonicity -/

/-- Shrinking both spans keeps every σ-logical a σ-logical. -/
theorem isLogical_mono (s t : CodeState) (σ : Sector) (hQ : t.Q = s.Q)
    (hσ : SpanLE s.Q (sectorRows t σ) (sectorRows s σ))
    (hopp : SpanLE s.Q (sectorRows t (oppositeSector σ)) (sectorRows s (oppositeSector σ)))
    (v : List Bool) (hv : isLogicalBool s σ v = true) : isLogicalBool t σ v = true := by
  unfold isLogicalBool at hv ⊢
  rw [Bool.and_eq_true, List.all_eq_true] at hv ⊢
  obtain ⟨horth, hspan⟩ := hv
  rw [hQ]
  refine ⟨?_, ?_⟩
  · intro r hr
    have hin : inSpanRows s.Q (sectorRows s (oppositeSector σ)) (rowVector s.Q r) :=
      hopp _ (inSpanRows_of_mem s.Q hr)
    have h0 : dotPar v (rowVector s.Q r) % 2 = 0 :=
      dotPar_even_of_inSpanRows s.Q _ v _ hin
        (fun r' hr' => Nat.eq_of_beq_eq_true (horth r' hr'))
    rw [h0]
    rfl
  · rw [Bool.not_eq_true'] at hspan ⊢
    cases hb : inSpanRowsBool s.Q (sectorRows t σ) v with
    | false => rfl
    | true =>
        exfalso
        have hin : inSpanRows s.Q (sectorRows s σ) v :=
          hσ v ((exact_inSpanRowsBool_iff _ _ _).mp hb)
        have := (exact_inSpanRowsBool_iff _ _ _).mpr hin
        rw [hspan] at this
        exact Bool.false_ne_true this

/-- The exact distance is span-monotone: the σ-logicals of `s` are σ-logicals
    of `t`, so the minimum over `t` is no larger. -/
theorem exactDistance_le_of_spanLE (s t : CodeState) (σ : Sector) (hQ : t.Q = s.Q)
    (hσ : SpanLE s.Q (sectorRows t σ) (sectorRows s σ))
    (hopp : SpanLE s.Q (sectorRows t (oppositeSector σ)) (sectorRows s (oppositeSector σ))) :
    exactDistance σ t ≤ exactDistance σ s := by
  unfold exactDistance
  rw [hQ]
  apply minWeight_mono
  intro v hv
  unfold logicalVectors at hv ⊢
  rw [List.mem_filter] at hv ⊢
  rw [hQ]
  exact ⟨hv.1, isLogical_mono s t σ hQ hσ hopp v hv.2⟩

theorem spanMonotone_exactMeasure : SpanMonotone exactMeasure := by
  intro s t hQ hX hZ
  exact ⟨exactDistance_le_of_spanLE s t Sector.X hQ hX hZ,
    exactDistance_le_of_spanLE s t Sector.Z hQ hZ hX⟩

/-- The hypothesis of `judgment_soundness`, discharged for the exact distance. -/
theorem measureMonotone_exactMeasure : MeasureMonotone exactMeasure :=
  measureMonotone_of_spanMonotone spanMonotone_exactMeasure

/-! ## The `+∞` value: the `Option Nat` and `ExtNat` readings (issue #310) -/

/-- Minimum weight over a list of vectors, `none` for the empty list. -/
def minWeight? : List (List Bool) → Option Nat
  | [] => none
  | v :: vs =>
      match minWeight? vs with
      | none => some (weight v)
      | some m => some (min (weight v) m)

theorem minWeight?_cons (v : List Bool) (vs : List (List Bool)) :
    minWeight? (v :: vs) = match minWeight? vs with
      | none => some (weight v)
      | some m => some (min (weight v) m) := rfl

theorem minWeight?_eq_none_iff (vs : List (List Bool)) : minWeight? vs = none ↔ vs = [] := by
  cases vs with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons v vs =>
      constructor
      · intro h
        rw [minWeight?_cons] at h
        split at h <;> cases h
      · intro h
        cases h

/-- `minWeight init` is the `Option` minimum met with `init`. -/
theorem minWeight_eq_minWeight? (init : Nat) : ∀ vs : List (List Bool),
    minWeight init vs = match minWeight? vs with
      | none => init
      | some m => min init m
  | [] => rfl
  | v :: vs => by
      show min (weight v) (minWeight init vs) = _
      rw [minWeight_eq_minWeight? init vs, minWeight?_cons]
      cases h : minWeight? vs with
      | none =>
          show min (weight v) init = min init (weight v)
          omega
      | some m =>
          show min (weight v) (min init m) = min init (min (weight v) m)
          omega

/-- The `Option` minimum is attained. -/
theorem minWeight?_attained : ∀ (vs : List (List Bool)) (m : Nat),
    minWeight? vs = some m → ∃ v ∈ vs, weight v = m
  | [], _, h => nomatch h
  | v :: vs, m, h => by
      rw [minWeight?_cons] at h
      split at h
      · exact ⟨v, List.mem_cons_self .., Option.some.inj h⟩
      · rename_i m' hm'
        have hm : min (weight v) m' = m := Option.some.inj h
        rcases Nat.le_total (weight v) m' with hle | hge
        · exact ⟨v, List.mem_cons_self .., (Nat.min_eq_left hle).symm.trans hm⟩
        · obtain ⟨w, hw, hwm⟩ := minWeight?_attained vs m' hm'
          exact ⟨w, List.mem_cons_of_mem v hw, hwm.trans ((Nat.min_eq_right hge).symm.trans hm)⟩

theorem weight_le_length (v : List Bool) : weight v ≤ v.length :=
  List.count_le_length ..

theorem length_of_mem_logicalVectors {s : CodeState} {σ : Sector} {v : List Bool}
    (h : v ∈ logicalVectors s σ) : v.length = s.Q.length := by
  unfold logicalVectors at h
  exact (exact_mem_allBoolLists _ _).mp (List.mem_filter.mp h).1

/-- The exact σ-distance of `s` in `Option Nat`: the least weight of a
    σ-logical, and `none` (`+∞`) when there is none. This is the reading of
    the executable ledger (`PricedInterval.lean`). -/
def exactDistance? (σ : Sector) (s : CodeState) : Option Nat :=
  minWeight? (logicalVectors s σ)

theorem exactDistance?_eq_none_iff (σ : Sector) (s : CodeState) :
    exactDistance? σ s = none ↔ logicalVectors s σ = [] :=
  minWeight?_eq_none_iff _

/-- A finite exact distance is at most the number of qubits. -/
theorem le_Q_length_of_exactDistance?_eq_some {σ : Sector} {s : CodeState} {d : Nat}
    (h : exactDistance? σ s = some d) : d ≤ s.Q.length := by
  obtain ⟨v, hv, hw⟩ := minWeight?_attained _ _ h
  rw [← hw, ← length_of_mem_logicalVectors hv]
  exact weight_le_length v

/-- The `Nat`-valued distance is the `Option` reading with the sentinel
    `|Q| + 1` as its default. -/
theorem exactDistance_eq_getD (σ : Sector) (s : CodeState) :
    exactDistance σ s = (exactDistance? σ s).getD (s.Q.length + 1) := by
  unfold exactDistance exactDistance?
  rw [minWeight_eq_minWeight?]
  cases h : minWeight? (logicalVectors s σ) with
  | none => rfl
  | some m =>
      show min (s.Q.length + 1) m = m
      exact Nat.min_eq_right (Nat.le_succ_of_le (le_Q_length_of_exactDistance?_eq_some h))

/-- The sentinel is exact: the `Nat`-valued distance is `|Q| + 1` exactly when
    there is no σ-logical. -/
theorem exactDistance_eq_sentinel_iff (σ : Sector) (s : CodeState) :
    exactDistance σ s = s.Q.length + 1 ↔ exactDistance? σ s = none := by
  rw [exactDistance_eq_getD]
  cases h : exactDistance? σ s with
  | none => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | some d =>
      have hd := le_Q_length_of_exactDistance?_eq_some h
      show d = s.Q.length + 1 ↔ some d = none
      exact ⟨fun hdn => absurd hdn (by omega), fun hc => nomatch hc⟩

/-- The exact σ-distance in the S2 concrete domain `ℕ ∪ {+∞}`
    (`Interval.lean`). -/
def exactDistanceExt (σ : Sector) (s : CodeState) : ExtNat :=
  ExtNat.ofOption (exactDistance? σ s)

/-- On a common namespace length, the `Nat` order of two sentinel readings is
    the `ExtNat` order of the two distances: a finite value is at most `|Q|`,
    below the sentinel. -/
theorem exactDistance_le_iff_ext {σ : Sector} {s t : CodeState}
    (hQ : t.Q.length = s.Q.length) :
    exactDistance σ t ≤ exactDistance σ s ↔ exactDistanceExt σ t ≤ exactDistanceExt σ s := by
  rw [exactDistance_eq_getD, exactDistance_eq_getD, hQ]
  unfold exactDistanceExt
  cases ht : exactDistance? σ t with
  | none =>
      cases hs : exactDistance? σ s with
      | none => exact ⟨fun _ => trivial, fun _ => Nat.le_refl _⟩
      | some d =>
          have hd := le_Q_length_of_exactDistance?_eq_some hs
          show s.Q.length + 1 ≤ d ↔ ExtNat.inf ≤ ExtNat.finite d
          exact ⟨fun h => absurd h (by omega), fun h => (h : False).elim⟩
  | some d =>
      have hd := le_Q_length_of_exactDistance?_eq_some ht
      cases hs : exactDistance? σ s with
      | none =>
          show d ≤ s.Q.length + 1 ↔ ExtNat.finite d ≤ ExtNat.inf
          exact ⟨fun _ => trivial, fun _ => by omega⟩
      | some e => exact Iff.rfl

/-- `exactDistance_le_of_spanLE` in the concrete domain. -/
theorem exactDistanceExt_le_of_spanLE (s t : CodeState) (σ : Sector) (hQ : t.Q = s.Q)
    (hσ : SpanLE s.Q (sectorRows t σ) (sectorRows s σ))
    (hopp : SpanLE s.Q (sectorRows t (oppositeSector σ)) (sectorRows s (oppositeSector σ))) :
    exactDistanceExt σ t ≤ exactDistanceExt σ s :=
  (exactDistance_le_iff_ext (by rw [hQ])).mp (exactDistance_le_of_spanLE s t σ hQ hσ hopp)

/-- The §4.5 law in `ℕ ∪ {+∞}`: deletion does not raise a sector distance. -/
theorem exactDistanceExt_delete_le {r : Nat} {s t : CodeState}
    (h : Eval (Command.delete r) s t) (σ : Sector) :
    exactDistanceExt σ t ≤ exactDistanceExt σ s := by
  have ht := eval_delete_eq h
  subst ht
  exact exactDistanceExt_le_of_spanLE s (deleteState s r) σ rfl
    (spanLE_of_sublist _ (sectorRows_deleteState_sublist s r σ))
    (spanLE_of_sublist _ (sectorRows_deleteState_sublist s r (oppositeSector σ)))

/-- The §4.3 law in `ℕ ∪ {+∞}`: addition does not lower a sector distance. -/
theorem exactDistanceExt_add_le {sector : Sector} {support : List Nat} {s t : CodeState}
    (h : Eval (Command.addStab sector support) s t) (σ : Sector) :
    exactDistanceExt σ s ≤ exactDistanceExt σ t := by
  have ht := eval_add_eq h
  subst ht
  exact exactDistanceExt_le_of_spanLE (addState s sector support) s σ rfl
    (spanLE_of_sublist _ (sectorRows_addState_sublist s sector support σ))
    (spanLE_of_sublist _ (sectorRows_addState_sublist s sector support (oppositeSector σ)))

/-- `judgment_soundness` for the exact distance: no measure hypothesis remains. -/
theorem judgment_soundness_exact (cs : List CodeState)
    (hctxt : WellFormedContext cs) (hchain : Chain cs) :
    ∀ a, Derives exactMeasure cs a → Models exactMeasure cs a :=
  judgment_soundness exactMeasure measureMonotone_exactMeasure cs hctxt hchain

/-- The same from the input state's well-formedness alone. -/
theorem judgment_soundness_of_head_exact (cs : List CodeState) (hchain : Chain cs)
    (hhead : ∀ s, cs.head? = some s → EncodingWellFormed s) :
    ∀ a, Derives exactMeasure cs a → Models exactMeasure cs a :=
  judgment_soundness_of_head exactMeasure measureMonotone_exactMeasure cs hchain hhead

/-! ## Sanity checks against the fixtures' hand-computed distances

`machine/fixtures/mvp_fixtures.json` records `d_X = d_Z = +∞` for W0 (`k = 0`),
`d_X = 2` and `d_Z = 1` for W3's result (the state `A1`), and `d_X = 1` and
`d_Z = 2` for W14's direct sum. W0's `+∞` is `exactDistance? = none`, whose
sentinel is `|Q| + 1 = 4`. These are checks that the definition is the
intended one, by kernel `decide`; they confirm nothing about the calculus. -/

theorem exactDistance?_W0_X : exactDistance? Sector.X fixture_W0_initial = none := by decide
theorem exactDistance?_W0_Z : exactDistance? Sector.Z fixture_W0_initial = none := by decide
theorem exactDistance_W0_X : exactDistance Sector.X fixture_W0_initial = 4 := by decide
theorem exactDistance_W0_Z : exactDistance Sector.Z fixture_W0_initial = 4 := by decide
theorem exactDistance?_W3_result_X : exactDistance? Sector.X fixture_W3_result = some 2 := by
  decide
theorem exactDistance?_W3_result_Z : exactDistance? Sector.Z fixture_W3_result = some 1 := by
  decide
theorem exactDistance_W3_result_X : exactDistance Sector.X fixture_W3_result = 2 := by decide
theorem exactDistance_W3_result_Z : exactDistance Sector.Z fixture_W3_result = 1 := by decide
theorem exactDistance_W14_result_X : exactDistance Sector.X fixture_W14_result = 1 := by decide
theorem exactDistance_W14_result_Z : exactDistance Sector.Z fixture_W14_result = 2 := by decide

/-- The deletion law on the W0 to A1 pair, read off the values: the deletion
    `delete_{a1}` takes both sector distances from `+∞` (`none`, sentinel `4`)
    to `2` and `1`, and neither rises. -/
theorem exactDistance_W3_delete_le :
    exactDistance Sector.X fixture_W3_result ≤ exactDistance Sector.X fixture_W0_initial ∧
    exactDistance Sector.Z fixture_W3_result ≤ exactDistance Sector.Z fixture_W0_initial := by
  decide

end CodeCalculus
