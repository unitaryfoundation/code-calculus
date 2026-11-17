import CodeCalculus.ExactGluePairs

/-!
# `E-GLUE`: the class-pair distance formula (issue #396)

Mechanizes step 5 of Claim 2 of `spec/OPERATIONAL_SEMANTICS.md` §4.33: the
exact `σ`-distance of the glued state `C = glueState a b seams` is the least
value of `μ_A(α) + μ_B(β)` over the class pairs `(α, β)` in `K_σ` outside
`W_σ`, and it is `+∞` when there is no such pair.

As in `ExactGluePairs.lean`, a class is carried by a representative and no
quotient type is built.

* `classVectors s σ v` lists the vectors of the class of `v` modulo the span
  of the `σ`-rows of `s`, and `classWeight s σ v` is the least weight among
  them (`μ` of §4.33). `classWeight_attained` gives a representative of that
  weight, `classWeight_congr` shows the value depends only on the class, and
  `classWeight_of_span` is `μ(0) = 0`.
* `glueKW_congr` shows that membership of a pair in `K_σ` outside `W_σ`
  depends only on the two classes.
* `glue_exactDistance?_eq_some_iff` and `glue_exactDistance?_eq_none_iff`
  are the formula, stated for `exactDistance?` with `none` for `+∞`: the
  distance is `some d` iff `d` is attained by a pair in `K_σ` outside `W_σ`
  and is a lower bound for every such pair, and it is `none` iff no pair
  qualifies.
-/

namespace CodeCalculus

/-! ### Vector algebra -/

theorem xorVec_self_eq : ∀ v : List Bool, xorVec v v = List.replicate v.length false
  | [] => rfl
  | x :: xs => by
      rw [xorVec_cons, xorVec_self_eq xs, List.length_cons, List.replicate_succ]
      cases x <;> rfl

/-- `(u + v) + (v + w) = u + w` for vectors of one length. -/
theorem xorVec_chain (u v w : List Bool) (huv : u.length = v.length)
    (hvw : v.length = w.length) :
    xorVec (xorVec u v) (xorVec v w) = xorVec u w := by
  rw [xorVec_assoc u v (xorVec v w) huv ((xorVec_length v w hvw).symm),
    xorVec_cancel_left v w hvw]

/-! ### The class of a vector and its least weight -/

/-- The vectors on the qubits of `s` that differ from `v` by an element of
    the span of the `σ`-rows: the class of `v`. -/
def classVectors (s : CodeState) (σ : Sector) (v : List Bool) : List (List Bool) :=
  (allBoolLists s.Q.length).filter (fun u =>
    inSpanRowsBool s.Q (sectorRows s σ) (xorVec u v))

/-- The least weight of a representative of the class of `v` (`μ` of
    §4.33). The initial value `s.Q.length + 1` is never returned when `v` has
    length `s.Q.length`, because `v` is in its own class. -/
def classWeight (s : CodeState) (σ : Sector) (v : List Bool) : Nat :=
  minWeight (s.Q.length + 1) (classVectors s σ v)

theorem mem_classVectors_iff (s : CodeState) (σ : Sector) (v u : List Bool) :
    u ∈ classVectors s σ v ↔
      u.length = s.Q.length ∧ inSpanRows s.Q (sectorRows s σ) (xorVec u v) := by
  unfold classVectors
  rw [List.mem_filter, exact_mem_allBoolLists, exact_inSpanRowsBool_iff]

theorem self_mem_classVectors (s : CodeState) (σ : Sector) (v : List Bool)
    (hv : v.length = s.Q.length) : v ∈ classVectors s σ v := by
  rw [mem_classVectors_iff, xorVec_self_eq]
  refine ⟨hv, ?_⟩
  rw [hv]
  exact inSpanRows_zero s.Q (sectorRows s σ)

theorem classWeight_le_of_mem {s : CodeState} {σ : Sector} {v u : List Bool}
    (hu : u ∈ classVectors s σ v) : classWeight s σ v ≤ weight u :=
  minWeight_le_of_mem (s.Q.length + 1) _ hu

theorem classWeight_le_weight (s : CodeState) (σ : Sector) (v : List Bool)
    (hv : v.length = s.Q.length) : classWeight s σ v ≤ weight v :=
  classWeight_le_of_mem (self_mem_classVectors s σ v hv)

/-- The least weight of a class is the weight of one of its
    representatives. -/
theorem classWeight_attained (s : CodeState) (σ : Sector) (v : List Bool)
    (hv : v.length = s.Q.length) :
    ∃ u ∈ classVectors s σ v, weight u = classWeight s σ v := by
  rcases minWeight_attained (s.Q.length + 1) (classVectors s σ v) with h | h
  · have h1 := classWeight_le_weight s σ v hv
    have h2 := weight_le_length v
    unfold classWeight at h1
    omega
  · obtain ⟨u, hu, hw⟩ := h
    exact ⟨u, hu, hw.symm⟩

/-- Two vectors that differ by a span element have the same class. -/
theorem classVectors_of_span {s : CodeState} {σ : Sector} {v w u : List Bool}
    (hv : v.length = s.Q.length) (hw : w.length = s.Q.length)
    (hvw : inSpanRows s.Q (sectorRows s σ) (xorVec v w))
    (hu : u ∈ classVectors s σ v) : u ∈ classVectors s σ w := by
  rw [mem_classVectors_iff] at hu ⊢
  refine ⟨hu.1, ?_⟩
  have h := inSpanRows_xor s.Q (sectorRows s σ) hu.2 hvw
  rw [xorVec_chain u v w (hu.1.trans hv.symm) (hv.trans hw.symm)] at h
  exact h

/-- `μ` is well defined on classes. -/
theorem classWeight_congr (s : CodeState) (σ : Sector) (v w : List Bool)
    (hv : v.length = s.Q.length) (hw : w.length = s.Q.length)
    (hvw : inSpanRows s.Q (sectorRows s σ) (xorVec v w)) :
    classWeight s σ v = classWeight s σ w := by
  have hwv : inSpanRows s.Q (sectorRows s σ) (xorVec w v) := by
    rw [xorVec_comm]
    exact hvw
  obtain ⟨u1, hu1, hw1⟩ := classWeight_attained s σ v hv
  obtain ⟨u2, hu2, hw2⟩ := classWeight_attained s σ w hw
  have h1 := classWeight_le_of_mem (classVectors_of_span hv hw hvw hu1)
  have h2 := classWeight_le_of_mem (classVectors_of_span hw hv hwv hu2)
  omega

/-- `μ(0) = 0`: the class of a span element has least weight zero. -/
theorem classWeight_of_span (s : CodeState) (σ : Sector) (v : List Bool)
    (hv : inSpanRows s.Q (sectorRows s σ) v) : classWeight s σ v = 0 := by
  have hl := length_of_inSpanRows hv
  have hz : List.replicate s.Q.length false ∈ classVectors s σ v := by
    rw [mem_classVectors_iff, xorVec_replicate_false_left s.Q.length v hl]
    exact ⟨List.length_replicate .., hv⟩
  have h := classWeight_le_of_mem hz
  rw [weight_replicate_false] at h
  exact Nat.le_zero.mp h

/-! ### Logicals are stable under a change of representative -/

/-- Adding a span element of a well-formed state to a `σ`-logical gives a
    `σ`-logical. -/
theorem isLogicalBool_xor_span {s : CodeState} (hwf : EncodingWellFormed s) (σ : Sector)
    (v w : List Bool) (hv : v.length = s.Q.length)
    (hlog : isLogicalBool s σ v = true)
    (hw : inSpanRows s.Q (sectorRows s σ) w) :
    isLogicalBool s σ (xorVec v w) = true := by
  have hvw : v.length = w.length := hv.trans (length_of_inSpanRows hw).symm
  rw [isLogicalBool_iff_prop] at hlog ⊢
  refine ⟨inNormalizer_xor s σ v w hvw hlog.1 (inNormalizer_of_inSpanRows_wf hwf σ w hw), ?_⟩
  intro h
  have h1 := inSpanRows_xor s.Q (sectorRows s σ) h hw
  rw [xorVec_cancel_right v w hvw] at h1
  exact hlog.2 h1

/-- Every representative of the class of a `σ`-logical is a `σ`-logical. -/
theorem isLogicalBool_of_mem_classVectors {s : CodeState} (hwf : EncodingWellFormed s)
    (σ : Sector) (v u : List Bool) (hv : v.length = s.Q.length)
    (hlog : isLogicalBool s σ v = true) (hu : u ∈ classVectors s σ v) :
    isLogicalBool s σ u = true := by
  rw [mem_classVectors_iff] at hu
  have hvu : v.length = u.length := hv.trans hu.1.symm
  have h := isLogicalBool_xor_span hwf σ v (xorVec u v) hv hlog hu.2
  rw [xorVec_comm u v, xorVec_cancel_left v u hvu] at h
  exact h

/-- The exact distance of a well-formed state is at most the least weight of
    each of its logical classes. -/
theorem exactDistance_le_classWeight {s : CodeState} (hwf : EncodingWellFormed s)
    (σ : Sector) (v : List Bool) (hv : v.length = s.Q.length)
    (hlog : isLogicalBool s σ v = true) :
    exactDistance σ s ≤ classWeight s σ v := by
  obtain ⟨u, hu, hw⟩ := classWeight_attained s σ v hv
  rw [← hw]
  exact minWeight_le_of_mem (s.Q.length + 1) _
    ((mem_logicalVectors_iff s σ u).mpr
      ⟨((mem_classVectors_iff s σ v u).mp hu).1,
        isLogicalBool_of_mem_classVectors hwf σ v u hv hlog hu⟩)

/-! ### The formula -/

/-- Membership of a pair in `K_σ` outside `W_σ` depends only on the two
    factor classes. -/
theorem glueKW_congr (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (vA vB uA uB : List Bool)
    (hwf : EncodingWellFormed (glueState a b seams))
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (hlA : vA.length = a.Q.length) (hlB : vB.length = b.Q.length)
    (huA : uA ∈ classVectors a σ vA) (huB : uB ∈ classVectors b σ vB)
    (h : GlueK a b seams σ vA vB ∧ ¬ GlueW a b seams σ vA vB) :
    GlueK a b seams σ uA uB ∧ ¬ GlueW a b seams σ uA uB := by
  rw [mem_classVectors_iff] at huA huB
  have hvl : (vA ++ vB).length = (glueState a b seams).Q.length := by
    rw [glueState_Q, List.length_append, List.length_append, hlA, hlB]
  have hlog := (glue_logical_iff a b seams σ vA vB hQ hsupA hsupB hlA hlB).mpr h
  have hspan : inSpanRows (glueState a b seams).Q (sectorRows (glueState a b seams) σ)
      (xorVec uA vA ++ xorVec uB vB) :=
    (glue_stabilizer_iff a b seams σ _ _ hQ hsupA hsupB
      (length_of_inSpanRows huA.2) (length_of_inSpanRows huB.2)).mpr
      (glueW_of_factor_span a b seams σ _ _ huA.2 huB.2)
  have h1 := isLogicalBool_xor_span hwf σ (vA ++ vB) _ hvl hlog hspan
  rw [← xorVec_append uA vA uB vB (huA.1.trans hlA.symm), xorVec_comm (uA ++ uB) (vA ++ vB),
    xorVec_cancel_left (vA ++ vB) (uA ++ uB)
      (by rw [List.length_append, List.length_append, hlA, hlB, huA.1, huB.1])] at h1
  exact (glue_logical_iff a b seams σ uA uB hQ hsupA hsupB huA.1 huB.1).mp h1

/-- Each pair in `K_σ` outside `W_σ` bounds the glued distance from above by
    the sum of its two class weights. -/
theorem glue_exactDistance?_le_pair (a b : CodeState) (seams : List (Sector × List Nat))
    (σ : Sector) (vA vB : List Bool)
    (hwf : EncodingWellFormed (glueState a b seams))
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (hlA : vA.length = a.Q.length) (hlB : vB.length = b.Q.length)
    (h : GlueK a b seams σ vA vB ∧ ¬ GlueW a b seams σ vA vB) :
    ∃ m, exactDistance? σ (glueState a b seams) = some m ∧
      m ≤ classWeight a σ vA + classWeight b σ vB := by
  obtain ⟨uA, huA, hwA⟩ := classWeight_attained a σ vA hlA
  obtain ⟨uB, huB, hwB⟩ := classWeight_attained b σ vB hlB
  have hu := glueKW_congr a b seams σ vA vB uA uB hwf hQ hsupA hsupB hlA hlB huA huB h
  have hulA := ((mem_classVectors_iff a σ vA uA).mp huA).1
  have hulB := ((mem_classVectors_iff b σ vB uB).mp huB).1
  have hmem : uA ++ uB ∈ logicalVectors (glueState a b seams) σ :=
    (mem_logicalVectors_iff _ σ _).mpr
      ⟨by rw [glueState_Q, List.length_append, List.length_append, hulA, hulB],
        (glue_logical_iff a b seams σ uA uB hQ hsupA hsupB hulA hulB).mpr hu⟩
  obtain ⟨m, hm, hle⟩ := exactDistance?_le_of_mem hmem
  refine ⟨m, hm, ?_⟩
  rw [weight_append_eq, hwA, hwB] at hle
  exact hle

/-- A finite glued distance is the sum of the two class weights of some pair
    in `K_σ` outside `W_σ`. -/
theorem glue_exactDistance?_attained (a b : CodeState) (seams : List (Sector × List Nat))
    (σ : Sector) (d : Nat)
    (hwf : EncodingWellFormed (glueState a b seams))
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (hd : exactDistance? σ (glueState a b seams) = some d) :
    ∃ vA vB : List Bool, vA.length = a.Q.length ∧ vB.length = b.Q.length ∧
      (GlueK a b seams σ vA vB ∧ ¬ GlueW a b seams σ vA vB) ∧
      classWeight a σ vA + classWeight b σ vB = d := by
  obtain ⟨v, hv, hwv⟩ := minWeight?_attained _ _ hd
  have hvl : v.length = a.Q.length + b.Q.length := by
    rw [length_of_mem_logicalVectors hv, glueState_Q, List.length_append]
  have hlA : (v.take a.Q.length).length = a.Q.length := by
    rw [List.length_take, hvl]
    exact Nat.min_eq_left (Nat.le_add_right _ _)
  have hlB : (v.drop a.Q.length).length = b.Q.length := by
    rw [List.length_drop, hvl, Nat.add_sub_cancel_left]
  have hlog : isLogicalBool (glueState a b seams) σ
      (v.take a.Q.length ++ v.drop a.Q.length) = true := by
    rw [List.take_append_drop]
    exact ((mem_logicalVectors_iff _ σ v).mp hv).2
  have hKW := (glue_logical_iff a b seams σ _ _ hQ hsupA hsupB hlA hlB).mp hlog
  obtain ⟨m, hm, hle⟩ := glue_exactDistance?_le_pair a b seams σ _ _ hwf hQ hsupA hsupB
    hlA hlB hKW
  have hmd : m = d := Option.some.inj (hm.symm.trans hd)
  have h1 := classWeight_le_weight a σ _ hlA
  have h2 := classWeight_le_weight b σ _ hlB
  have h3 := weight_append_eq (v.take a.Q.length) (v.drop a.Q.length)
  rw [List.take_append_drop] at h3
  exact ⟨_, _, hlA, hlB, hKW, by omega⟩

/-- The class-pair distance formula, finite case: the glued `σ`-distance is
    `some d` iff `d` is the sum of the class weights of some pair in `K_σ`
    outside `W_σ` and no such pair has a smaller sum. -/
theorem glue_exactDistance?_eq_some_iff (a b : CodeState) (seams : List (Sector × List Nat))
    (σ : Sector) (d : Nat)
    (hwf : EncodingWellFormed (glueState a b seams))
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q) :
    exactDistance? σ (glueState a b seams) = some d ↔
      (∃ vA vB : List Bool, vA.length = a.Q.length ∧ vB.length = b.Q.length ∧
        (GlueK a b seams σ vA vB ∧ ¬ GlueW a b seams σ vA vB) ∧
        classWeight a σ vA + classWeight b σ vB = d) ∧
      (∀ vA vB : List Bool, vA.length = a.Q.length → vB.length = b.Q.length →
        GlueK a b seams σ vA vB ∧ ¬ GlueW a b seams σ vA vB →
        d ≤ classWeight a σ vA + classWeight b σ vB) := by
  constructor
  · intro hd
    refine ⟨glue_exactDistance?_attained a b seams σ d hwf hQ hsupA hsupB hd, ?_⟩
    intro vA vB hlA hlB hKW
    obtain ⟨m, hm, hle⟩ := glue_exactDistance?_le_pair a b seams σ vA vB hwf hQ hsupA hsupB
      hlA hlB hKW
    have hmd : m = d := Option.some.inj (hm.symm.trans hd)
    rw [← hmd]
    exact hle
  · rintro ⟨⟨vA, vB, hlA, hlB, hKW, hsum⟩, hmin⟩
    obtain ⟨m, hm, hle⟩ := glue_exactDistance?_le_pair a b seams σ vA vB hwf hQ hsupA hsupB
      hlA hlB hKW
    obtain ⟨wA, wB, hwA, hwB, hKW', hsum'⟩ :=
      glue_exactDistance?_attained a b seams σ m hwf hQ hsupA hsupB hm
    have h1 := hmin wA wB hwA hwB hKW'
    have hmd : m = d := by omega
    rw [hm, hmd]

/-- The class-pair distance formula, infinite case: the glued state has no
    `σ`-logical iff no pair lies in `K_σ` outside `W_σ`. -/
theorem glue_exactDistance?_eq_none_iff (a b : CodeState) (seams : List (Sector × List Nat))
    (σ : Sector)
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q) :
    exactDistance? σ (glueState a b seams) = none ↔
      ∀ vA vB : List Bool, vA.length = a.Q.length → vB.length = b.Q.length →
        ¬ (GlueK a b seams σ vA vB ∧ ¬ GlueW a b seams σ vA vB) := by
  rw [exactDistance?_eq_none_iff]
  constructor
  · intro hnil vA vB hlA hlB hKW
    have hmem : vA ++ vB ∈ logicalVectors (glueState a b seams) σ :=
      (mem_logicalVectors_iff _ σ _).mpr
        ⟨by rw [glueState_Q, List.length_append, List.length_append, hlA, hlB],
          (glue_logical_iff a b seams σ vA vB hQ hsupA hsupB hlA hlB).mpr hKW⟩
    rw [hnil] at hmem
    exact absurd hmem (List.not_mem_nil)
  · intro h
    cases hl : logicalVectors (glueState a b seams) σ with
    | nil => rfl
    | cons v vs =>
        have hv : v ∈ logicalVectors (glueState a b seams) σ := by
          rw [hl]
          exact List.mem_cons_self ..
        have hvl : v.length = a.Q.length + b.Q.length := by
          rw [length_of_mem_logicalVectors hv, glueState_Q, List.length_append]
        have hlA : (v.take a.Q.length).length = a.Q.length := by
          rw [List.length_take, hvl]
          exact Nat.min_eq_left (Nat.le_add_right _ _)
        have hlB : (v.drop a.Q.length).length = b.Q.length := by
          rw [List.length_drop, hvl, Nat.add_sub_cancel_left]
        have hlog : isLogicalBool (glueState a b seams) σ
            (v.take a.Q.length ++ v.drop a.Q.length) = true := by
          rw [List.take_append_drop]
          exact ((mem_logicalVectors_iff _ σ v).mp hv).2
        exact absurd ((glue_logical_iff a b seams σ _ _ hQ hsupA hsupB hlA hlB).mp hlog)
          (h _ _ hlA hlB)

end CodeCalculus
