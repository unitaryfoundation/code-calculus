import CodeCalculus.Eval
import CodeCalculus.ExactDistance
import CodeCalculus.ExactDirectSum

/-!
# `E-GLUE`: Claim 1 of the extracted derivation (issue #366)

Mechanizes Claim 1 of `spec/OPERATIONAL_SEMANTICS.md` §4.33: every
`σ`-logical of the glued state restricts to a `σ`-logical of at least one
factor. State-shape lemmas retained. Claim 2 remains follow-up.
-/ 

namespace CodeCalculus

theorem glueState_Q (a b : CodeState) (seams : List (Sector × List Nat)) :
    (glueState a b seams).Q = a.Q ++ b.Q := by
  rfl

theorem directSumState_Q (a b : CodeState) :
    (directSumState a b).Q = a.Q ++ b.Q := by
  rfl

theorem glueState_used_prefix (a b : CodeState) (seams : List (Sector × List Nat)) :
    (glueState a b seams).used = a.used ++ b.used ++ mintFresh (a.used ++ b.used) seams.length := by
  rfl

theorem inSpanRows_append (Q : List Nat) (rows extra : List Row) (v : List Bool)
    (h : inSpanRows Q rows v) : inSpanRows Q (rows ++ extra) v := by
  obtain ⟨cs, hlen, heq⟩ := h
  have hvlen : v.length = Q.length := by
    rw [← heq]
    exact combineRows_length Q.length (rows.map (rowVector Q)) cs
      (rowVectors_length Q rows)
  refine ⟨cs ++ List.replicate (extra.map (rowVector Q)).length false, ?_, ?_⟩
  · rw [List.length_append]; simp [hlen]
  · rw [List.map_append]
    rw [combineRows_append Q.length (rows.map (rowVector Q)) (extra.map (rowVector Q)) cs
      (List.replicate (extra.map (rowVector Q)).length false) (rowVectors_length Q rows)
      (rowVectors_length Q extra) (by simp [hlen, List.length_map])
      (by simp [List.length_replicate, List.length_map])]
    rw [heq]
    rw [combineRows_zero_coeffs Q.length (extra.map (rowVector Q))]
    rw [xorVec_replicate_false_right Q.length v hvlen]

theorem glue_claim1 (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (v : List Bool)
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (hvlen : v.length = (glueState a b seams).Q.length)
    (hlog : isLogicalBool (glueState a b seams) σ v = true) :
    isLogicalBool a σ (v.take a.Q.length) = true ∨
    isLogicalBool b σ (v.drop a.Q.length) = true := by
  let c := glueState a b seams
  let vA := v.take a.Q.length
  let vB := v.drop a.Q.length
  have hvsplit : v = vA ++ vB := (List.take_append_drop a.Q.length v).symm
  have hlA : vA.length = a.Q.length := by
    simp [vA, List.length_take, hvlen, glueState_Q]
  have hlB : vB.length = b.Q.length := by
    simp [vB, List.length_drop, hvlen, glueState_Q]
  have hlog' := (isLogicalBool_iff_prop c σ v).mp hlog
  rcases hlog' with ⟨horthC, hspanC⟩
  have orthA : ∀ r ∈ sectorRows a (oppositeSector σ),
      dotPar vA (rowVector a.Q r) % 2 = 0 := by
    intro r hr
    have hrC : r ∈ sectorRows c (oppositeSector σ) := by
      apply List.mem_filter.mpr
      refine ⟨?_, (List.mem_filter.mp hr).2⟩
      · dsimp [c, glueState]
        apply List.mem_append.mpr
        left
        apply List.mem_append.mpr
        left
        exact (List.mem_filter.mp hr).1
    have h := horthC r hrC
    have hsup : supportSubset r.support a.Q := hsupA r ((List.mem_filter.mp hr).1)
    have hrow : rowVector c.Q r = rowVector a.Q r ++ List.replicate b.Q.length false := by
      rw [glueState_Q a b seams, rowVector_append]
      have hd : rowVector b.Q r = List.replicate b.Q.length false := rowVector_eq_replicate_of_disjoint b.Q r
        (fun q hq => by
          intro hm
          have ha := hsup q hm
          exact (hQ q ha hq).elim)
      rw [hd]
    rw [hvsplit, hrow, dotPar_append_eq vA (rowVector a.Q r) vB (List.replicate b.Q.length false)
      (hlA.trans (rowVector_length a.Q r).symm)] at h
    have hrep : dotPar vB (List.replicate b.Q.length false) = 0 := by
      exact dotPar_replicate_false vB b.Q.length
    simpa [hrep] using h
  have orthB : ∀ r ∈ sectorRows b (oppositeSector σ),
      dotPar vB (rowVector b.Q r) % 2 = 0 := by
    intro r hr
    have hrC : r ∈ sectorRows c (oppositeSector σ) := by
      apply List.mem_filter.mpr
      refine ⟨?_, (List.mem_filter.mp hr).2⟩
      · dsimp [c, glueState]
        apply List.mem_append.mpr
        left
        apply List.mem_append.mpr
        right
        exact (List.mem_filter.mp hr).1
    have h := horthC r hrC
    have hsup : supportSubset r.support b.Q := hsupB r ((List.mem_filter.mp hr).1)
    have hrow : rowVector c.Q r =
        List.replicate a.Q.length false ++ rowVector b.Q r := by
      rw [glueState_Q a b seams, rowVector_append]
      have hd : rowVector a.Q r = List.replicate a.Q.length false := rowVector_eq_replicate_of_disjoint a.Q r
        (fun q hq => by
          intro hm
          have hb := hsup q hm
          exact (hQ q hq hb).elim)
      rw [hd]
    rw [hvsplit, hrow, dotPar_append_eq vA (List.replicate a.Q.length false) vB (rowVector b.Q r)
      (hlA.trans List.length_replicate.symm)] at h
    have hrep : dotPar vA (List.replicate a.Q.length false) = 0 := dotPar_replicate_false vA a.Q.length
    simpa [hrep] using h
  by_cases hbA : inSpanRowsBool a.Q (sectorRows a σ) vA = true
  · have hA : inSpanRows a.Q (sectorRows a σ) vA := (exact_inSpanRowsBool_iff a.Q (sectorRows a σ) vA).mp hbA
    by_cases hbB : inSpanRowsBool b.Q (sectorRows b σ) vB = true
    · have hB : inSpanRows b.Q (sectorRows b σ) vB := (exact_inSpanRowsBool_iff b.Q (sectorRows b σ) vB).mp hbB
      have hspanAB : inSpanRows (a.Q ++ b.Q) (sectorRows a σ ++ sectorRows b σ) (vA ++ vB) := by
        exact (inSpanRows_directSum_split a.Q b.Q (sectorRows a σ) (sectorRows b σ) vA vB
          (fun r hr q hq => by
            intro hm
            have ha := (hsupA r ((List.mem_filter.mp hr).1)) q hm
            exact (hQ q ha hq).elim)
          (fun r hr q hq => by
            intro hm
            have hb := (hsupB r ((List.mem_filter.mp hr).1)) q hm
            exact (hQ q hq hb).elim)
          hlA).mpr ⟨hA, hB⟩
      have hspanC' : inSpanRows c.Q (sectorRows c σ) v := by
        have h1 : inSpanRows c.Q (sectorRows a σ ++ sectorRows b σ) v := by
          rw [hvsplit]; simpa [c, glueState] using hspanAB
        let hextra := (glueState a b seams).rows.drop (a.rows.length + b.rows.length) |>.filter (fun r => r.sector = σ)
        have hdecomp : sectorRows c σ = sectorRows a σ ++ sectorRows b σ ++ hextra := by
          simp [sectorRows, c, glueState, List.filter_append, hextra]
        have h2 : inSpanRows c.Q (sectorRows a σ ++ sectorRows b σ ++ hextra) v := by
          have := inSpanRows_append c.Q (sectorRows a σ ++ sectorRows b σ) hextra v h1
          simpa [List.append_assoc] using this
        simpa [← hdecomp] using h2
      exact absurd hspanC' hspanC
    · have hB : ¬ inSpanRows b.Q (sectorRows b σ) vB := by
        intro h
        have := (exact_inSpanRowsBool_iff b.Q (sectorRows b σ) vB).mpr h
        rw [this] at hbB
        contradiction
      right
      exact (isLogicalBool_iff_prop b σ vB).mpr ⟨orthB, hB⟩
  · have hA : ¬ inSpanRows a.Q (sectorRows a σ) vA := by
      intro h
      have := (exact_inSpanRowsBool_iff a.Q (sectorRows a σ) vA).mpr h
      rw [this] at hbA
      contradiction
    left
    exact (isLogicalBool_iff_prop a σ vA).mpr ⟨orthA, hA⟩



/-- Helper: if every candidate has weight at least `m` and the init is at least
    `m`, then the minimum is at least `m`. -/
theorem minWeight_ge (init m : Nat) (vs : List (List Bool))
    (hinit : init ≥ m) (hall : ∀ v ∈ vs, weight v ≥ m) :
    minWeight init vs ≥ m := by
  match vs with
  | [] => exact hinit
  | v :: vs' =>
    have hv : weight v ≥ m := hall v (List.mem_cons_self ..)
    have hvs' : ∀ w ∈ vs', weight w ≥ m := fun w hw => hall w (List.mem_cons_of_mem v hw)
    simp [minWeight]
    rw [Nat.min_def]
    by_cases hle : weight v ≤ minWeight init vs'
    · rw [if_pos hle]
      exact hv
    · rw [if_neg hle]
      exact minWeight_ge init m vs' hinit hvs'

/-- **Lower bound.** Every `σ`-logical of the glued state has weight at least
    `min(d_σ(C_A), d_σ(C_B))`, so the glued exact distance is at least that
    minimum (the §4.31 repair's lower-endpoint half, mechanized from
    `glue_claim1`). -/
theorem glue_exactDistance_ge_min (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q) :
    min (exactDistance σ a) (exactDistance σ b) ≤ exactDistance σ (glueState a b seams) := by
  let c := glueState a b seams
  let m := min (exactDistance σ a) (exactDistance σ b)
  have hmA : m ≤ exactDistance σ a := Nat.min_le_left _ _
  have hmB : m ≤ exactDistance σ b := Nat.min_le_right _ _
  have hinit : m ≤ c.Q.length + 1 := by
    have hdA : exactDistance σ a ≤ a.Q.length + 1 := minWeight_le_init (a.Q.length + 1) (logicalVectors a σ)
    have : m ≤ a.Q.length + 1 := Nat.le_trans hmA hdA
    have hc : c.Q.length + 1 = a.Q.length + b.Q.length + 1 := by
      rw [glueState_Q a b seams]
      simp [List.length_append]
    rw [hc]
    exact Nat.le_trans this (by omega)
  have hall : ∀ v ∈ logicalVectors c σ, weight v ≥ m := by
    intro v hv
    have hvlen : v.length = c.Q.length := length_of_mem_logicalVectors hv
    have hlog : isLogicalBool c σ v = true := (mem_logicalVectors_iff c σ v).mp hv |>.2
    rcases glue_claim1 a b seams σ v hQ hsupA hsupB hvlen hlog with hA | hB
    · let vA := v.take a.Q.length
      have hvA_len : (v.take a.Q.length).length = a.Q.length := by
        simp [List.length_take, hvlen, c, glueState, glueState_Q, List.length_append]
      have hvA : vA ∈ logicalVectors a σ := by
        rw [mem_logicalVectors_iff a σ vA]
        refine ⟨hvA_len, hA⟩
      have hdA : exactDistance σ a ≤ weight vA := minWeight_le_of_mem (a.Q.length + 1) (logicalVectors a σ) hvA
      have hw : weight v = weight vA + weight (v.drop a.Q.length) := by
        have h1 := weight_append_eq vA (v.drop a.Q.length)
        rwa [List.take_append_drop a.Q.length v] at h1
      have : m ≤ weight vA := Nat.le_trans hmA hdA
      rw [hw]
      exact Nat.le_trans this (Nat.le_add_right (weight vA) (weight (v.drop a.Q.length)))
    · let vB := v.drop a.Q.length
      have hvB_len : (v.drop a.Q.length).length = b.Q.length := by
        simp [List.length_drop, hvlen, c, glueState, glueState_Q, List.length_append]
      have hvB : vB ∈ logicalVectors b σ := by
        rw [mem_logicalVectors_iff b σ vB]
        refine ⟨hvB_len, hB⟩
      have hdB : exactDistance σ b ≤ weight vB := minWeight_le_of_mem (b.Q.length + 1) (logicalVectors b σ) hvB
      have hw : weight v = weight (v.take a.Q.length) + weight vB := by
        have h1 := weight_append_eq (v.take a.Q.length) vB
        rwa [List.take_append_drop a.Q.length v] at h1
      have : m ≤ weight vB := Nat.le_trans hmB hdB
      rw [hw]
      exact Nat.le_trans this (Nat.le_add_left (weight vB) (weight (v.take a.Q.length)))
  have hres : minWeight (c.Q.length + 1) (logicalVectors c σ) ≥ m :=
    minWeight_ge (c.Q.length + 1) m (logicalVectors c σ) hinit hall
  show m ≤ exactDistance σ c
  unfold exactDistance
  exact hres


/-- Well-definedness of the `φ_t` functional of Claim 2: changing a
    representative of a factor class by a factor `σ`-row does not change
    `φ_t` modulo 2, provided that factor row commutes with the `τ`-seam. -/
theorem phi_well_defined (a r t : List Bool)
    (hlen : a.length = r.length) (hlenr : r.length = t.length)
    (hcomm : dotPar r t % 2 = 0) :
    dotPar (xorVec a r) t % 2 = dotPar a t % 2 := by
  rw [dotPar_comm (xorVec a r) t]
  have h1 := dotPar_xorVec t a r hlen
  have h2 : dotPar t r % 2 = 0 := by
    rw [dotPar_comm t r]
    exact hcomm
  have h3 : dotPar t a % 2 = dotPar a t % 2 := by
    rw [dotPar_comm a t]
  have h4 : (dotPar t a + dotPar t r) % 2 = dotPar t a % 2 := by
    rw [Nat.add_mod]
    rw [h2]
    simp
  rw [h1, h4, h3]

/-- The `W_σ ⊆ K_σ` half of Claim 2: a `σ`-seam check commutes with a
    `τ`-seam check iff the sum of the factor restrictions' parities is even. -/
theorem seam_checks_commute_split (a b : CodeState) (s t : Row)
    (hs : supportSubset s.support (a.Q ++ b.Q))
    (ht : supportSubset t.support (a.Q ++ b.Q)) :
    dotPar (rowVector (a.Q ++ b.Q) s) (rowVector (a.Q ++ b.Q) t) % 2 = 0 →
    (dotPar (rowVector a.Q s) (rowVector a.Q t) +
      dotPar (rowVector b.Q s) (rowVector b.Q t)) % 2 = 0 := by
  intro h
  rw [rowVector_append a.Q b.Q s, rowVector_append a.Q b.Q t] at h
  have hsplit := dotPar_append_eq (rowVector a.Q s) (rowVector a.Q t)
    (rowVector b.Q s) (rowVector b.Q t)
    ((rowVector_length a.Q s).trans (rowVector_length a.Q t).symm)
  simpa [hsplit] using h

end CodeCalculus
