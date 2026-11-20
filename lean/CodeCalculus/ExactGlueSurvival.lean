import CodeCalculus.ExactGlueDistance

/-!
# `E-GLUE`: which factor logicals survive the seam

Mechanizes the survival statement of `spec/OPERATIONAL_SEMANTICS.md` §4.31
(*Instance-wise equality through a surviving witness*) and §4.33 (*What
follows*, item (ii)) for the glued state `C = glueState a b seams`.

A `σ`-logical `u` of the factor `a` survives the seam when its extension by
zero on the qubits of `b` is a `σ`-logical of `C` (`SurvivesA`); `SurvivesB`
is the same for the factor `b`.

* `survivesA_iff` and `survivesB_iff` are the survival criterion: a factor
  `σ`-logical survives iff it has even overlap with every seam check of the
  opposite sector and its extension is outside the span of the `σ`-rows of
  `C`.
* `survivesA_congr` and `survivesB_congr` show survival depends only on the
  factor class, so one representative decides it.
* `glue_exactDistance_le_of_survivesA` and its `B` form are the witness
  upper bound, and `glue_exactDistance_eq_min_of_survivesA` and its `B` form
  are the instance-wise equality: a survivor of weight
  `min (d_σ a) (d_σ b)` gives `d_σ C = min (d_σ a) (d_σ b)`.
* `glue_survivor_of_min_logical` is the converse: a `σ`-logical of `C` of
  weight `min (d_σ a) (d_σ b)` is the extension of a surviving factor
  logical of that weight.
-/

namespace CodeCalculus

/-! ### Zero vectors -/

theorem dotPar_replicate_false_left (n : Nat) (v : List Bool) :
    dotPar (List.replicate n false) v = 0 := by
  rw [dotPar_comm]
  exact dotPar_replicate_false v n

theorem inNormalizer_zero (s : CodeState) (σ : Sector) (n : Nat) :
    InNormalizer s σ (List.replicate n false) := by
  intro r _
  rw [dotPar_replicate_false_left]

theorem eq_replicate_false_of_weight_zero (v : List Bool) (h : weight v = 0) :
    v = List.replicate v.length false := by
  refine List.eq_replicate_iff.mpr ⟨rfl, fun b hb => ?_⟩
  cases b with
  | false => rfl
  | true => exact absurd hb (List.count_eq_zero.mp h)

/-! ### Survival -/

/-- A `σ`-logical `u` of the factor `a` survives the seam: its extension by
    zero on the qubits of `b` is a `σ`-logical of the glued state. -/
def SurvivesA (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (u : List Bool) : Prop :=
  u.length = a.Q.length ∧ isLogicalBool a σ u = true ∧
    isLogicalBool (glueState a b seams) σ (u ++ List.replicate b.Q.length false) = true

/-- A `σ`-logical `u` of the factor `b` survives the seam. -/
def SurvivesB (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (u : List Bool) : Prop :=
  u.length = b.Q.length ∧ isLogicalBool b σ u = true ∧
    isLogicalBool (glueState a b seams) σ (List.replicate a.Q.length false ++ u) = true

/-- The survival criterion for the factor `a`: a `σ`-logical of `a` survives
    iff it has even overlap with every seam check of the opposite sector and
    the `σ`-rows of the glued state do not span its extension. -/
theorem survivesA_iff (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (u : List Bool)
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (hu : u.length = a.Q.length) (hlog : isLogicalBool a σ u = true) :
    SurvivesA a b seams σ u ↔
      (∀ t ∈ seamSectorRows a b seams (oppositeSector σ),
        dotPar u (rowVector a.Q t) % 2 = 0) ∧
      ¬ inSpanRows (glueState a b seams).Q (sectorRows (glueState a b seams) σ)
        (u ++ List.replicate b.Q.length false) := by
  have hN : InNormalizer a σ u := ((isLogicalBool_iff_prop a σ u).mp hlog).1
  have hK : InNormalizer (glueState a b seams) σ (u ++ List.replicate b.Q.length false) ↔
      ∀ t ∈ seamSectorRows a b seams (oppositeSector σ),
        dotPar u (rowVector a.Q t) % 2 = 0 := by
    rw [glue_normalizer_iff a b seams σ u _ hQ hsupA hsupB hu]
    constructor
    · rintro ⟨_, _, hT⟩ t ht
      have h := hT t ht
      rw [dotPar_replicate_false_left, Nat.add_zero] at h
      exact h
    · intro hT
      refine ⟨hN, inNormalizer_zero b σ _, fun t ht => ?_⟩
      rw [dotPar_replicate_false_left, Nat.add_zero]
      exact hT t ht
  unfold SurvivesA
  rw [isLogicalBool_iff_prop (glueState a b seams)]
  constructor
  · rintro ⟨_, _, hn, hs⟩
    exact ⟨hK.mp hn, hs⟩
  · rintro ⟨hT, hs⟩
    exact ⟨hu, hlog, hK.mpr hT, hs⟩

/-- The survival criterion for the factor `b`. -/
theorem survivesB_iff (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (u : List Bool)
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (hu : u.length = b.Q.length) (hlog : isLogicalBool b σ u = true) :
    SurvivesB a b seams σ u ↔
      (∀ t ∈ seamSectorRows a b seams (oppositeSector σ),
        dotPar u (rowVector b.Q t) % 2 = 0) ∧
      ¬ inSpanRows (glueState a b seams).Q (sectorRows (glueState a b seams) σ)
        (List.replicate a.Q.length false ++ u) := by
  have hN : InNormalizer b σ u := ((isLogicalBool_iff_prop b σ u).mp hlog).1
  have hK : InNormalizer (glueState a b seams) σ (List.replicate a.Q.length false ++ u) ↔
      ∀ t ∈ seamSectorRows a b seams (oppositeSector σ),
        dotPar u (rowVector b.Q t) % 2 = 0 := by
    rw [glue_normalizer_iff a b seams σ _ u hQ hsupA hsupB (List.length_replicate ..)]
    constructor
    · rintro ⟨_, _, hT⟩ t ht
      have h := hT t ht
      rw [dotPar_replicate_false_left, Nat.zero_add] at h
      exact h
    · intro hT
      refine ⟨inNormalizer_zero a σ _, hN, fun t ht => ?_⟩
      rw [dotPar_replicate_false_left, Nat.zero_add]
      exact hT t ht
  unfold SurvivesB
  rw [isLogicalBool_iff_prop (glueState a b seams)]
  constructor
  · rintro ⟨_, _, hn, hs⟩
    exact ⟨hK.mp hn, hs⟩
  · rintro ⟨hT, hs⟩
    exact ⟨hu, hlog, hK.mpr hT, hs⟩

/-- Survival depends only on the class of the factor logical: every
    representative of the class of a survivor survives. -/
theorem survivesA_congr (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (u u' : List Bool)
    (hwfA : EncodingWellFormed a)
    (hwf : EncodingWellFormed (glueState a b seams))
    (hQ : DisjointList a.Q b.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (hu' : u' ∈ classVectors a σ u)
    (h : SurvivesA a b seams σ u) : SurvivesA a b seams σ u' := by
  obtain ⟨hu, hlogA, hlogC⟩ := h
  have hsupA := supports_subset_of_wf hwfA
  have hzl : (List.replicate b.Q.length false).length = b.Q.length := List.length_replicate ..
  have hKW := (glue_logical_iff a b seams σ u _ hQ hsupA hsupB hu hzl).mp hlogC
  have hKW' := glueKW_congr a b seams σ u _ u' _ hwf hQ hsupA hsupB hu hzl hu'
    (self_mem_classVectors b σ _ hzl) hKW
  have hul := ((mem_classVectors_iff a σ u u').mp hu').1
  exact ⟨hul, isLogicalBool_of_mem_classVectors hwfA σ u u' hu hlogA hu',
    (glue_logical_iff a b seams σ u' _ hQ hsupA hsupB hul hzl).mpr hKW'⟩

theorem survivesB_congr (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (u u' : List Bool)
    (hwfB : EncodingWellFormed b)
    (hwf : EncodingWellFormed (glueState a b seams))
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hu' : u' ∈ classVectors b σ u)
    (h : SurvivesB a b seams σ u) : SurvivesB a b seams σ u' := by
  obtain ⟨hu, hlogB, hlogC⟩ := h
  have hsupB := supports_subset_of_wf hwfB
  have hzl : (List.replicate a.Q.length false).length = a.Q.length := List.length_replicate ..
  have hKW := (glue_logical_iff a b seams σ _ u hQ hsupA hsupB hzl hu).mp hlogC
  have hKW' := glueKW_congr a b seams σ _ u _ u' hwf hQ hsupA hsupB hzl hu
    (self_mem_classVectors a σ _ hzl) hu' hKW
  have hul := ((mem_classVectors_iff b σ u u').mp hu').1
  exact ⟨hul, isLogicalBool_of_mem_classVectors hwfB σ u u' hu hlogB hu',
    (glue_logical_iff a b seams σ _ u' hQ hsupA hsupB hzl hul).mpr hKW'⟩

/-! ### The witness upper bound and the instance-wise equality -/

/-- A surviving logical of the factor `a` bounds the glued distance from
    above by its weight. -/
theorem glue_exactDistance_le_of_survivesA (a b : CodeState)
    (seams : List (Sector × List Nat)) (σ : Sector) (u : List Bool)
    (h : SurvivesA a b seams σ u) :
    exactDistance σ (glueState a b seams) ≤ weight u := by
  obtain ⟨hu, _, hlogC⟩ := h
  have hmem : u ++ List.replicate b.Q.length false ∈ logicalVectors (glueState a b seams) σ :=
    (mem_logicalVectors_iff _ σ _).mpr
      ⟨by rw [glueState_Q, List.length_append, List.length_append, hu, List.length_replicate],
        hlogC⟩
  have hle := minWeight_le_of_mem ((glueState a b seams).Q.length + 1) _ hmem
  rw [weight_append_eq, weight_replicate_false, Nat.add_zero] at hle
  exact hle

theorem glue_exactDistance_le_of_survivesB (a b : CodeState)
    (seams : List (Sector × List Nat)) (σ : Sector) (u : List Bool)
    (h : SurvivesB a b seams σ u) :
    exactDistance σ (glueState a b seams) ≤ weight u := by
  obtain ⟨hu, _, hlogC⟩ := h
  have hmem : List.replicate a.Q.length false ++ u ∈ logicalVectors (glueState a b seams) σ :=
    (mem_logicalVectors_iff _ σ _).mpr
      ⟨by rw [glueState_Q, List.length_append, List.length_append, hu, List.length_replicate],
        hlogC⟩
  have hle := minWeight_le_of_mem ((glueState a b seams).Q.length + 1) _ hmem
  rw [weight_append_eq, weight_replicate_false, Nat.zero_add] at hle
  exact hle

/-- The instance-wise equality of §4.31: a surviving logical of the factor
    `a` whose weight is the smaller factor distance closes the glued
    distance at that value. -/
theorem glue_exactDistance_eq_min_of_survivesA (a b : CodeState)
    (seams : List (Sector × List Nat)) (σ : Sector) (u : List Bool)
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (h : SurvivesA a b seams σ u)
    (hw : weight u = min (exactDistance σ a) (exactDistance σ b)) :
    exactDistance σ (glueState a b seams) = min (exactDistance σ a) (exactDistance σ b) :=
  Nat.le_antisymm (hw ▸ glue_exactDistance_le_of_survivesA a b seams σ u h)
    (glue_exactDistance_ge_min a b seams σ hQ hsupA hsupB)

theorem glue_exactDistance_eq_min_of_survivesB (a b : CodeState)
    (seams : List (Sector × List Nat)) (σ : Sector) (u : List Bool)
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (h : SurvivesB a b seams σ u)
    (hw : weight u = min (exactDistance σ a) (exactDistance σ b)) :
    exactDistance σ (glueState a b seams) = min (exactDistance σ a) (exactDistance σ b) :=
  Nat.le_antisymm (hw ▸ glue_exactDistance_le_of_survivesB a b seams σ u h)
    (glue_exactDistance_ge_min a b seams σ hQ hsupA hsupB)

/-- The converse: a `σ`-logical of the glued state whose weight is the
    smaller factor distance is the extension by zero of a surviving factor
    logical of that weight. -/
theorem glue_survivor_of_min_logical (a b : CodeState) (seams : List (Sector × List Nat))
    (σ : Sector) (v : List Bool)
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (hv : v ∈ logicalVectors (glueState a b seams) σ)
    (hw : weight v = min (exactDistance σ a) (exactDistance σ b)) :
    (∃ u, SurvivesA a b seams σ u ∧ weight u = weight v ∧
        v = u ++ List.replicate b.Q.length false) ∨
      (∃ u, SurvivesB a b seams σ u ∧ weight u = weight v ∧
        v = List.replicate a.Q.length false ++ u) := by
  have hvl := length_of_mem_logicalVectors hv
  have hlogC := ((mem_logicalVectors_iff _ σ v).mp hv).2
  have hvl' : v.length = a.Q.length + b.Q.length := by
    rw [hvl, glueState_Q, List.length_append]
  have hlA : (v.take a.Q.length).length = a.Q.length := by
    rw [List.length_take, hvl']
    exact Nat.min_eq_left (Nat.le_add_right _ _)
  have hlB : (v.drop a.Q.length).length = b.Q.length := by
    rw [List.length_drop, hvl', Nat.add_sub_cancel_left]
  have hsplit : v.take a.Q.length ++ v.drop a.Q.length = v := List.take_append_drop ..
  have hwsum : weight v = weight (v.take a.Q.length) + weight (v.drop a.Q.length) := by
    rw [← weight_append_eq, hsplit]
  have hmA : min (exactDistance σ a) (exactDistance σ b) ≤ exactDistance σ a :=
    Nat.min_le_left _ _
  have hmB : min (exactDistance σ a) (exactDistance σ b) ≤ exactDistance σ b :=
    Nat.min_le_right _ _
  rcases glue_claim1 a b seams σ v hQ hsupA hsupB hvl hlogC with hA | hB
  · left
    have hd := minWeight_le_of_mem (a.Q.length + 1) _
      ((mem_logicalVectors_iff a σ _).mpr ⟨hlA, hA⟩)
    have hd' : exactDistance σ a ≤ weight (v.take a.Q.length) := hd
    have hz : weight (v.drop a.Q.length) = 0 := by omega
    have hzero := eq_replicate_false_of_weight_zero _ hz
    rw [hlB] at hzero
    have hveq : v = v.take a.Q.length ++ List.replicate b.Q.length false := by
      rw [← hzero, hsplit]
    refine ⟨v.take a.Q.length, ⟨hlA, hA, ?_⟩, by omega, hveq⟩
    rw [← hveq]
    exact hlogC
  · right
    have hd := minWeight_le_of_mem (b.Q.length + 1) _
      ((mem_logicalVectors_iff b σ _).mpr ⟨hlB, hB⟩)
    have hd' : exactDistance σ b ≤ weight (v.drop a.Q.length) := hd
    have hz : weight (v.take a.Q.length) = 0 := by omega
    have hzero := eq_replicate_false_of_weight_zero _ hz
    rw [hlA] at hzero
    have hveq : v = List.replicate a.Q.length false ++ v.drop a.Q.length := by
      rw [← hzero, hsplit]
    refine ⟨v.drop a.Q.length, ⟨hlB, hB, ?_⟩, by omega, hveq⟩
    rw [← hveq]
    exact hlogC

end CodeCalculus
