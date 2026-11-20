import CodeCalculus.ExactGlue
import CodeCalculus.ExactPeel

/-!
# `E-GLUE`: the normalizer and the stabilizer of the glued state as pairs

Mechanizes steps 3 and 4 of Claim 2 of `spec/OPERATIONAL_SEMANTICS.md` §4.33
for the glued state `C = glueState a b seams`. A vector on the glued namespace
is written as a pair `(vA, vB)` of its restrictions to the two factors, so
`vA ++ vB` is the vector itself.

No quotient type is built. The class of a vector is carried by a
representative, and the two subgroups of the spec are predicates on pairs of
representatives:

* `GlueK a b seams σ vA vB` reads "the class pair of `(vA, vB)` lies in
  `K_σ`": both restrictions are in their factor's `σ`-normalizer and every
  `τ`-seam check has `φ_t = 0` on the pair.
* `GlueW a b seams σ vA vB` reads "the class pair of `(vA, vB)` lies in
  `W_σ`": some combination of the `σ`-seam checks has the same class pair.

The results are `glue_normalizer_iff` (step 3: `N_σ(C)` is the pairs in
`K_σ`, which also gives surjectivity of the class map onto `K_σ`),
`glue_stabilizer_iff` (step 4: `S_σ(C)` is the pairs in `W_σ`),
`glueW_subset_glueK` (`W_σ ⊆ K_σ`), `glueK_xor` (closure of `K_σ` under
addition), `glue_class_eq_iff` (two vectors have the same class in `L_σ(C)`
iff their pairs differ by an element of `W_σ`), and `glue_logical_iff` (the
`σ`-logicals of `C` are the pairs in `K_σ` outside `W_σ`). Together these are
the content of `L_σ(C) ≅ K_σ / W_σ` on representatives. The weight formula
of step 5 is not part of this module.
-/

namespace CodeCalculus

/-- The seam rows of the glued state: the rows `glueState` appends after the
    factor rows. -/
def glueSeamRows (a b : CodeState) (seams : List (Sector × List Nat)) : List Row :=
  (seams.zip (mintFresh (a.used ++ b.used) seams.length)).map (fun (si, id) =>
    ({ id := id, sector := si.1, support := si.2 } : Row))

/-- The seam rows of one sector (`T_σ` of §4.33). -/
def seamSectorRows (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector) :
    List Row :=
  (glueSeamRows a b seams).filter (fun r => r.sector = σ)

theorem glueState_rows (a b : CodeState) (seams : List (Sector × List Nat)) :
    (glueState a b seams).rows = a.rows ++ b.rows ++ glueSeamRows a b seams := rfl

/-- The `σ`-rows of the glued state are the factor `σ`-rows followed by the
    `σ`-seam rows. -/
theorem glue_sectorRows (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector) :
    sectorRows (glueState a b seams) σ =
      sectorRows a σ ++ sectorRows b σ ++ seamSectorRows a b seams σ := by
  unfold sectorRows seamSectorRows
  rw [glueState_rows, List.filter_append, List.filter_append]

/-- The `σ`-normalizer of a state (`N_σ` of §4.33): even overlap with every
    displayed row of the opposite sector. -/
def InNormalizer (s : CodeState) (σ : Sector) (v : List Bool) : Prop :=
  ∀ r ∈ sectorRows s (oppositeSector σ), dotPar v (rowVector s.Q r) % 2 = 0

/-- `K_σ` on representatives: both restrictions are factor normalizer
    elements and every `τ`-seam check has `φ_t = 0` on the pair. -/
def GlueK (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (vA vB : List Bool) : Prop :=
  InNormalizer a σ vA ∧ InNormalizer b σ vB ∧
    ∀ t ∈ seamSectorRows a b seams (oppositeSector σ),
      (dotPar vA (rowVector a.Q t) + dotPar vB (rowVector b.Q t)) % 2 = 0

/-- `W_σ` on representatives: some combination `wA ++ wB` of the `σ`-seam
    checks has the class pair of `(vA, vB)`, that is, differs from it by a
    factor stabilizer in each factor. -/
def GlueW (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (vA vB : List Bool) : Prop :=
  ∃ wA wB : List Bool, wA.length = a.Q.length ∧ wB.length = b.Q.length ∧
    inSpanRows (a.Q ++ b.Q) (seamSectorRows a b seams σ) (wA ++ wB) ∧
    inSpanRows a.Q (sectorRows a σ) (xorVec vA wA) ∧
    inSpanRows b.Q (sectorRows b σ) (xorVec vB wB)

/-! ### Overlap parities against the rows of the glued state -/

theorem dotPar_glue_split (QA QB : List Nat) (vA vB : List Bool) (r : Row)
    (hlA : vA.length = QA.length) :
    dotPar (vA ++ vB) (rowVector (QA ++ QB) r) =
      dotPar vA (rowVector QA r) + dotPar vB (rowVector QB r) := by
  rw [rowVector_append]
  exact dotPar_append_eq vA (rowVector QA r) vB (rowVector QB r)
    (hlA.trans (rowVector_length QA r).symm)

theorem dotPar_glue_left (QA QB : List Nat) (vA vB : List Bool) (r : Row)
    (hlA : vA.length = QA.length) (hr : ∀ q ∈ QB, q ∉ r.support) :
    dotPar (vA ++ vB) (rowVector (QA ++ QB) r) = dotPar vA (rowVector QA r) := by
  rw [dotPar_glue_split QA QB vA vB r hlA, rowVector_eq_replicate_of_disjoint QB r hr,
    dotPar_replicate_false, Nat.add_zero]

theorem dotPar_glue_right (QA QB : List Nat) (vA vB : List Bool) (r : Row)
    (hlA : vA.length = QA.length) (hr : ∀ q ∈ QA, q ∉ r.support) :
    dotPar (vA ++ vB) (rowVector (QA ++ QB) r) = dotPar vB (rowVector QB r) := by
  rw [dotPar_glue_split QA QB vA vB r hlA, rowVector_eq_replicate_of_disjoint QA r hr,
    dotPar_replicate_false, Nat.zero_add]

theorem factorA_misses_B {a b : CodeState} (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q) (σ : Sector) :
    ∀ r ∈ sectorRows a σ, ∀ q ∈ b.Q, q ∉ r.support :=
  fun r hr q hq hm => hQ q (hsupA r (List.mem_filter.mp hr).1 q hm) hq

theorem factorB_misses_A {a b : CodeState} (hQ : DisjointList a.Q b.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q) (σ : Sector) :
    ∀ r ∈ sectorRows b σ, ∀ q ∈ a.Q, q ∉ r.support :=
  fun r hr q hq hm => hQ q hq (hsupB r (List.mem_filter.mp hr).1 q hm)

/-! ### Step 3: the normalizer as pairs -/

/-- Step 3 of Claim 2: a vector on the glued namespace is in `N_σ(C)` iff its
    pair of restrictions is in `K_σ`. Read right to left, every pair in `K_σ`
    is the pair of a normalizer element, so the class map is onto `K_σ`. -/
theorem glue_normalizer_iff (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (vA vB : List Bool)
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (hlA : vA.length = a.Q.length) :
    InNormalizer (glueState a b seams) σ (vA ++ vB) ↔ GlueK a b seams σ vA vB := by
  unfold InNormalizer GlueK InNormalizer
  rw [glue_sectorRows]
  show (∀ r ∈ sectorRows a (oppositeSector σ) ++ sectorRows b (oppositeSector σ) ++
      seamSectorRows a b seams (oppositeSector σ),
      dotPar (vA ++ vB) (rowVector (a.Q ++ b.Q) r) % 2 = 0) ↔ _
  constructor
  · intro h
    refine ⟨fun r hr => ?_, fun r hr => ?_, fun t ht => ?_⟩
    · have h1 := h r (List.mem_append_left _ (List.mem_append_left _ hr))
      rw [dotPar_glue_left a.Q b.Q vA vB r hlA (factorA_misses_B hQ hsupA _ r hr)] at h1
      exact h1
    · have h1 := h r (List.mem_append_left _ (List.mem_append_right _ hr))
      rw [dotPar_glue_right a.Q b.Q vA vB r hlA (factorB_misses_A hQ hsupB _ r hr)] at h1
      exact h1
    · have h1 := h t (List.mem_append_right _ ht)
      rw [dotPar_glue_split a.Q b.Q vA vB t hlA] at h1
      exact h1
  · rintro ⟨hA, hB, hT⟩ r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · rw [dotPar_glue_left a.Q b.Q vA vB r hlA (factorA_misses_B hQ hsupA _ r hr)]
        exact hA r hr
      · rw [dotPar_glue_right a.Q b.Q vA vB r hlA (factorB_misses_A hQ hsupB _ r hr)]
        exact hB r hr
    · rw [dotPar_glue_split a.Q b.Q vA vB r hlA]
      exact hT r hr

/-! ### Span membership over an appended row list -/

/-- A vector is in the span of `rows1 ++ rows2` iff it differs from an element
    of the span of `rows2` by an element of the span of `rows1`. -/
theorem inSpanRows_append_iff (Q : List Nat) (rows1 rows2 : List Row) (v : List Bool)
    (hv : v.length = Q.length) :
    inSpanRows Q (rows1 ++ rows2) v ↔
      ∃ w, inSpanRows Q rows2 w ∧ inSpanRows Q rows1 (xorVec v w) := by
  constructor
  · rintro ⟨cs, hlen, heq⟩
    rw [List.length_append] at hlen
    have h1 : (cs.take rows1.length).length = (rows1.map (rowVector Q)).length := by
      rw [List.length_take, List.length_map]
      exact Nat.min_eq_left (by rw [hlen]; exact Nat.le_add_right _ _)
    have h2 : (cs.drop rows1.length).length = (rows2.map (rowVector Q)).length := by
      rw [List.length_drop, List.length_map, hlen, Nat.add_sub_cancel_left]
    have hsplit := combineRows_append Q.length (rows1.map (rowVector Q))
      (rows2.map (rowVector Q)) (cs.take rows1.length) (cs.drop rows1.length)
      (rowVectors_length Q rows1) (rowVectors_length Q rows2) h1 h2
    rw [List.take_append_drop, ← List.map_append, heq] at hsplit
    have hu : inSpanRows Q rows1
        (combineRows Q.length (rows1.map (rowVector Q)) (cs.take rows1.length)) :=
      ⟨_, by rw [h1, List.length_map], rfl⟩
    have hw : inSpanRows Q rows2
        (combineRows Q.length (rows2.map (rowVector Q)) (cs.drop rows1.length)) :=
      ⟨_, by rw [h2, List.length_map], rfl⟩
    refine ⟨_, hw, ?_⟩
    rw [hsplit, xorVec_cancel_right _ _
      ((length_of_inSpanRows hu).trans (length_of_inSpanRows hw).symm)]
    exact hu
  · rintro ⟨w, ⟨c2, hc2, hw⟩, ⟨c1, hc1, hu⟩⟩
    have hwl : w.length = Q.length := length_of_inSpanRows ⟨c2, hc2, hw⟩
    refine ⟨c1 ++ c2, by rw [List.length_append, List.length_append, hc1, hc2], ?_⟩
    rw [List.map_append, combineRows_append Q.length (rows1.map (rowVector Q))
      (rows2.map (rowVector Q)) c1 c2 (rowVectors_length Q rows1) (rowVectors_length Q rows2)
      (by rw [hc1, List.length_map]) (by rw [hc2, List.length_map]), hu, hw]
    exact xorVec_cancel_right v w (hv.trans hwl.symm)

/-! ### Step 4: the stabilizer as pairs -/

/-- Step 4 of Claim 2: a vector on the glued namespace is in `S_σ(C)` iff its
    pair of restrictions is in `W_σ`. -/
theorem glue_stabilizer_iff (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (vA vB : List Bool)
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (hlA : vA.length = a.Q.length) (hlB : vB.length = b.Q.length) :
    inSpanRows (glueState a b seams).Q (sectorRows (glueState a b seams) σ) (vA ++ vB) ↔
      GlueW a b seams σ vA vB := by
  rw [glue_sectorRows]
  show inSpanRows (a.Q ++ b.Q) _ (vA ++ vB) ↔ _
  have hvl : (vA ++ vB).length = (a.Q ++ b.Q).length := by
    rw [List.length_append, List.length_append, hlA, hlB]
  rw [inSpanRows_append_iff (a.Q ++ b.Q) _ _ (vA ++ vB) hvl]
  unfold GlueW
  constructor
  · rintro ⟨w, hw, hu⟩
    have hwl : w.length = a.Q.length + b.Q.length := by
      rw [length_of_inSpanRows hw, List.length_append]
    have htl : (w.take a.Q.length).length = a.Q.length := by
      rw [List.length_take, hwl]
      exact Nat.min_eq_left (Nat.le_add_right _ _)
    have hdl : (w.drop a.Q.length).length = b.Q.length := by
      rw [List.length_drop, hwl, Nat.add_sub_cancel_left]
    have hws : w = w.take a.Q.length ++ w.drop a.Q.length :=
      (List.take_append_drop a.Q.length w).symm
    refine ⟨w.take a.Q.length, w.drop a.Q.length, htl, hdl, ?_, ?_⟩
    · rw [← hws]
      exact hw
    · rw [hws, xorVec_append vA (w.take a.Q.length) vB (w.drop a.Q.length)
        (hlA.trans htl.symm)] at hu
      exact (inSpanRows_directSum_split a.Q b.Q (sectorRows a σ) (sectorRows b σ) _ _
        (factorA_misses_B hQ hsupA σ) (factorB_misses_A hQ hsupB σ)
        ((xorVec_length vA _ (hlA.trans htl.symm)).trans hlA)).mp hu
  · rintro ⟨wA, wB, hwA, hwB, hw, huA, huB⟩
    refine ⟨wA ++ wB, hw, ?_⟩
    rw [xorVec_append vA wA vB wB (hlA.trans hwA.symm)]
    exact (inSpanRows_directSum_split a.Q b.Q (sectorRows a σ) (sectorRows b σ) _ _
      (factorA_misses_B hQ hsupA σ) (factorB_misses_A hQ hsupB σ)
      ((xorVec_length vA wA (hlA.trans hwA.symm)).trans hlA)).mpr ⟨huA, huB⟩

/-- The kernel of the class map lies in `W_σ`: a pair of factor stabilizers
    is the pair of the zero combination of the `σ`-seam checks. -/
theorem glueW_of_factor_span (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (vA vB : List Bool)
    (hA : inSpanRows a.Q (sectorRows a σ) vA) (hB : inSpanRows b.Q (sectorRows b σ) vB) :
    GlueW a b seams σ vA vB := by
  refine ⟨List.replicate a.Q.length false, List.replicate b.Q.length false,
    List.length_replicate .., List.length_replicate .., ?_, ?_, ?_⟩
  · have h := inSpanRows_zero (a.Q ++ b.Q) (seamSectorRows a b seams σ)
    rw [List.length_append, ← List.replicate_append_replicate] at h
    exact h
  · rw [xorVec_replicate_false_right a.Q.length vA (length_of_inSpanRows hA)]
    exact hA
  · rw [xorVec_replicate_false_right b.Q.length vB (length_of_inSpanRows hB)]
    exact hB

/-! ### `W_σ ⊆ K_σ`, closure of `K_σ`, and the induced class statements -/

theorem inNormalizer_of_inSpanRows (s : CodeState) (σ : Sector) (v : List Bool)
    (hcomm : ∀ r ∈ sectorRows s σ, ∀ t ∈ sectorRows s (oppositeSector σ),
      dotPar (rowVector s.Q t) (rowVector s.Q r) % 2 = 0)
    (hv : inSpanRows s.Q (sectorRows s σ) v) : InNormalizer s σ v := by
  intro t ht
  rw [dotPar_comm]
  exact dotPar_even_of_inSpanRows s.Q (sectorRows s σ) (rowVector s.Q t) v hv
    (fun r hr => hcomm r hr t ht)

/-- In a well-formed state the span of the `σ`-rows lies in the
    `σ`-normalizer. -/
theorem inNormalizer_of_inSpanRows_wf {s : CodeState} (hwf : EncodingWellFormed s)
    (σ : Sector) (v : List Bool) (hv : inSpanRows s.Q (sectorRows s σ) v) :
    InNormalizer s σ v := by
  refine inNormalizer_of_inSpanRows s σ v (fun r hr t ht => ?_) hv
  have hrs := List.mem_filter.mp hr
  have hts := List.mem_filter.mp ht
  exact dotPar_rowVector_even_of_wf hwf hts.1 hrs.1 (by
    have h1 : t.sector = oppositeSector σ := of_decide_eq_true hts.2
    have h2 : r.sector = σ := of_decide_eq_true hrs.2
    rw [h2, h1, oppositeSector_involutive])

/-- `W_σ ⊆ K_σ` for a well-formed glued state: the pairs the `σ`-seam absorbs
    commute with the `τ`-seam and restrict to factor normalizer elements. -/
theorem glueW_subset_glueK (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (vA vB : List Bool)
    (hwf : EncodingWellFormed (glueState a b seams))
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (hlA : vA.length = a.Q.length) (hlB : vB.length = b.Q.length)
    (h : GlueW a b seams σ vA vB) : GlueK a b seams σ vA vB :=
  (glue_normalizer_iff a b seams σ vA vB hQ hsupA hsupB hlA).mp
    (inNormalizer_of_inSpanRows_wf hwf σ (vA ++ vB)
      ((glue_stabilizer_iff a b seams σ vA vB hQ hsupA hsupB hlA hlB).mpr h))

theorem dotPar_xorVec_left (u w r : List Bool) (h : u.length = w.length) :
    dotPar (xorVec u w) r % 2 = (dotPar u r + dotPar w r) % 2 := by
  rw [dotPar_comm (xorVec u w) r, dotPar_comm u r, dotPar_comm w r]
  exact dotPar_xorVec r u w h

theorem even_add_of_even {x y z : Nat} (hz : z % 2 = (x + y) % 2)
    (hx : x % 2 = 0) (hy : y % 2 = 0) : z % 2 = 0 := by
  rw [hz, Nat.add_mod, hx, hy]

theorem inNormalizer_xor (s : CodeState) (σ : Sector) (u w : List Bool)
    (h : u.length = w.length) (hu : InNormalizer s σ u) (hw : InNormalizer s σ w) :
    InNormalizer s σ (xorVec u w) :=
  fun r hr => even_add_of_even (dotPar_xorVec_left u w _ h) (hu r hr) (hw r hr)

/-- `K_σ` is closed under addition of pairs. -/
theorem glueK_xor (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (uA uB wA wB : List Bool)
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (huA : uA.length = a.Q.length) (huB : uB.length = b.Q.length)
    (hwA : wA.length = a.Q.length) (hwB : wB.length = b.Q.length)
    (hu : GlueK a b seams σ uA uB) (hw : GlueK a b seams σ wA wB) :
    GlueK a b seams σ (xorVec uA wA) (xorVec uB wB) := by
  have hxl : (xorVec uA wA).length = a.Q.length :=
    (xorVec_length uA wA (huA.trans hwA.symm)).trans huA
  rw [← glue_normalizer_iff a b seams σ _ _ hQ hsupA hsupB hxl,
    ← xorVec_append uA wA uB wB (huA.trans hwA.symm)]
  exact inNormalizer_xor _ σ _ _
    (by rw [List.length_append, List.length_append, huA, huB, hwA, hwB])
    ((glue_normalizer_iff a b seams σ uA uB hQ hsupA hsupB huA).mpr hu)
    ((glue_normalizer_iff a b seams σ wA wB hQ hsupA hsupB hwA).mpr hw)

/-- Two vectors on the glued namespace have the same class modulo `S_σ(C)`
    iff their pairs differ by an element of `W_σ`. With
    `glue_normalizer_iff` this is the statement that the class map induces a
    bijection from `L_σ(C)` onto `K_σ / W_σ`. -/
theorem glue_class_eq_iff (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (uA uB wA wB : List Bool)
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (huA : uA.length = a.Q.length) (huB : uB.length = b.Q.length)
    (hwA : wA.length = a.Q.length) (hwB : wB.length = b.Q.length) :
    inSpanRows (glueState a b seams).Q (sectorRows (glueState a b seams) σ)
        (xorVec (uA ++ uB) (wA ++ wB)) ↔
      GlueW a b seams σ (xorVec uA wA) (xorVec uB wB) := by
  rw [xorVec_append uA wA uB wB (huA.trans hwA.symm)]
  exact glue_stabilizer_iff a b seams σ _ _ hQ hsupA hsupB
    ((xorVec_length uA wA (huA.trans hwA.symm)).trans huA)
    ((xorVec_length uB wB (huB.trans hwB.symm)).trans huB)

/-- The `σ`-logicals of the glued state are the pairs in `K_σ` outside
    `W_σ`. -/
theorem glue_logical_iff (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (vA vB : List Bool)
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (hlA : vA.length = a.Q.length) (hlB : vB.length = b.Q.length) :
    isLogicalBool (glueState a b seams) σ (vA ++ vB) = true ↔
      GlueK a b seams σ vA vB ∧ ¬ GlueW a b seams σ vA vB := by
  rw [isLogicalBool_iff_prop,
    ← glue_normalizer_iff a b seams σ vA vB hQ hsupA hsupB hlA,
    ← glue_stabilizer_iff a b seams σ vA vB hQ hsupA hsupB hlA hlB]
  exact Iff.rfl

end CodeCalculus
