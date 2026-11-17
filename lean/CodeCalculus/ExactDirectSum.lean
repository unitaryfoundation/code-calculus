import CodeCalculus.ExactPeel

/-!
# The direct-sum law for the exact distance (issue #367)

For two states on disjoint namespaces whose rows are supported on their own
namespaces, each exact sector distance of the direct sum is the minimum of
the two summands' (`exactDistance?_directSum`), and so is the full distance
(`exactDist_directSumState`). This is the §4.2 law
`d_σ(A ⊕ B) = min(d_σ(A), d_σ(B))` for the measure `exactDist`, which
`glue_expr_sound_exact` took as the hypothesis `hdirect`.

A vector over `Q_A ++ Q_B` is a pair `v_A ++ v_B`. It is orthogonal to the
opposite-sector rows of the sum exactly when each part is orthogonal to its
summand's rows, and it lies in the span of the sum's σ-rows exactly when
each part lies in its summand's span. So a logical of a summand, padded
with zeros, is a logical of the sum of the same weight, and a logical of the
sum has a part that is a logical of its summand, of no larger weight.

The law is stated under the two hypotheses it needs, disjoint namespaces and
rows supported on their own namespace. It is false without them, so it is
not available in the unconditional form `∀ a b` that `directSum_sound`
takes for an uninterpreted measure.
-/

namespace CodeCalculus

/-! ## Vectors over an appended namespace -/

theorem dotPar_append_eq : ∀ (a b c d : List Bool), a.length = b.length →
    dotPar (a ++ c) (b ++ d) = dotPar a b + dotPar c d
  | [], [], c, d, _ => by
      rw [List.nil_append, List.nil_append, dotPar_nil_left, Nat.zero_add]
  | x :: a, y :: b, c, d, h => by
      rw [List.cons_append, List.cons_append, dotPar_cons, dotPar_cons,
        dotPar_append_eq a b c d (Nat.succ.inj h)]
      omega
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h

theorem weight_append_eq : ∀ (a b : List Bool), weight (a ++ b) = weight a + weight b
  | [], b => by
      rw [List.nil_append]
      show weight b = 0 + weight b
      omega
  | x :: a, b => by
      rw [List.cons_append, weight_cons, weight_cons, weight_append_eq a b]
      omega

theorem weight_replicate_false : ∀ n : Nat, weight (List.replicate n false) = 0
  | 0 => rfl
  | n + 1 => by
      rw [List.replicate_succ, weight_cons, weight_replicate_false n]
      rfl

theorem leOpt_antisymm {a b : Option Nat} (h1 : leOpt a b) (h2 : leOpt b a) : a = b := by
  cases a <;> cases b <;> simp [leOpt] at * <;> omega

theorem minOpt_interchange (a b c d : Option Nat) :
    minOpt (minOpt a b) (minOpt c d) = minOpt (minOpt a c) (minOpt b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp [minOpt] <;> omega

/-- The Prop reading of `isLogicalBool`. -/
theorem isLogicalBool_iff_prop (s : CodeState) (σ : Sector) (v : List Bool) :
    isLogicalBool s σ v = true ↔
      (∀ r ∈ sectorRows s (oppositeSector σ), dotPar v (rowVector s.Q r) % 2 = 0) ∧
        ¬ inSpanRows s.Q (sectorRows s σ) v := by
  unfold isLogicalBool
  rw [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', ← exact_inSpanRowsBool_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun r hr => Nat.eq_of_beq_eq_true (h1 r hr), ?_⟩
    rw [h2]
    exact Bool.false_ne_true
  · rintro ⟨h1, h2⟩
    refine ⟨fun r hr => ?_, ?_⟩
    · rw [h1 r hr]
      rfl
    · cases hb : inSpanRowsBool s.Q (sectorRows s σ) v with
      | false => rfl
      | true => exact absurd hb h2

/-- Span membership over a direct sum splits into the two blocks. -/
theorem inSpanRows_directSum_split (QA QB : List Nat) (rowsA rowsB : List Row)
    (vA vB : List Bool)
    (hA : ∀ r ∈ rowsA, ∀ q ∈ QB, q ∉ r.support)
    (hB : ∀ r ∈ rowsB, ∀ q ∈ QA, q ∉ r.support)
    (hlA : vA.length = QA.length) :
    inSpanRows (QA ++ QB) (rowsA ++ rowsB) (vA ++ vB) ↔
      inSpanRows QA rowsA vA ∧ inSpanRows QB rowsB vB := by
  have hmapA : rowsA.map (rowVector (QA ++ QB)) =
      (rowsA.map (rowVector QA)).map (fun v => v ++ List.replicate QB.length false) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro r hr
    show rowVector (QA ++ QB) r = rowVector QA r ++ List.replicate QB.length false
    rw [rowVector_append, rowVector_eq_replicate_of_disjoint QB r (hA r hr)]
  have hmapB : rowsB.map (rowVector (QA ++ QB)) =
      (rowsB.map (rowVector QB)).map (fun v => List.replicate QA.length false ++ v) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro r hr
    show rowVector (QA ++ QB) r = List.replicate QA.length false ++ rowVector QB r
    rw [rowVector_append, rowVector_eq_replicate_of_disjoint QA r (hB r hr)]
  have hvA : ∀ v ∈ rowsA.map (rowVector QA), v.length = QA.length := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨r, _, rfl⟩
    exact rowVector_length QA r
  have hvB : ∀ v ∈ rowsB.map (rowVector QB), v.length = QB.length := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨r, _, rfl⟩
    exact rowVector_length QB r
  unfold inSpanRows
  rw [List.map_append, hmapA, hmapB]
  simp only [List.length_append]
  constructor
  · rintro ⟨cs, hlen, heq⟩
    have h1 : (cs.take rowsA.length).length = (rowsA.map (rowVector QA)).length := by
      rw [List.length_take, List.length_map]
      omega
    have h2 : (cs.drop rowsA.length).length = (rowsB.map (rowVector QB)).length := by
      rw [List.length_drop, List.length_map]
      omega
    rw [← List.take_append_drop rowsA.length cs,
      combineRows_split QA.length QB.length _ _ _ _ hvA hvB h1 h2] at heq
    have hl : (combineRows QA.length (rowsA.map (rowVector QA))
        (cs.take rowsA.length)).length = vA.length := by
      rw [combineRows_length _ _ _ hvA, hlA]
    have hsplit := List.append_inj heq hl
    refine ⟨⟨cs.take rowsA.length, ?_, hsplit.1⟩, ⟨cs.drop rowsA.length, ?_, hsplit.2⟩⟩
    · rw [h1, List.length_map]
    · rw [h2, List.length_map]
  · rintro ⟨⟨csA, hlenA, heqA⟩, ⟨csB, hlenB, heqB⟩⟩
    have h1 : csA.length = (rowsA.map (rowVector QA)).length := by
      rw [List.length_map]
      exact hlenA
    have h2 : csB.length = (rowsB.map (rowVector QB)).length := by
      rw [List.length_map]
      exact hlenB
    refine ⟨csA ++ csB, ?_, ?_⟩
    · rw [List.length_append, hlenA, hlenB]
    · rw [combineRows_split QA.length QB.length _ _ _ _ hvA hvB h1 h2, heqA, heqB]

/-! ## Logicals of a direct sum -/

/-- The hypotheses of the direct-sum law: disjoint namespaces, and rows
    supported on their own namespace. -/
structure DirectSumCtx (A B : CodeState) : Prop where
  hQ : DisjointList A.Q B.Q
  hsupA : ∀ row ∈ A.rows, supportSubset row.support A.Q
  hsupB : ∀ row ∈ B.rows, supportSubset row.support B.Q

namespace DirectSumCtx

variable {A B : CodeState}

theorem ofWellFormed (hQ : DisjointList A.Q B.Q) (hA : EncodingWellFormed A)
    (hB : EncodingWellFormed B) : DirectSumCtx A B := by
  refine ⟨hQ, ?_, ?_⟩
  · intro row hrow q hq
    have h := List.all_eq_true.mp (List.all_eq_true.mp hA.2.2.2.1 row hrow) q hq
    exact List.contains_iff_mem.mp h
  · intro row hrow q hq
    have h := List.all_eq_true.mp (List.all_eq_true.mp hB.2.2.2.1 row hrow) q hq
    exact List.contains_iff_mem.mp h

theorem missA (C : DirectSumCtx A B) (τ : Sector) :
    ∀ r ∈ sectorRows A τ, ∀ q ∈ B.Q, q ∉ r.support := by
  intro r hr q hq hmem
  exact C.hQ q (C.hsupA r (List.mem_filter.mp hr).1 q hmem) hq

theorem missB (C : DirectSumCtx A B) (τ : Sector) :
    ∀ r ∈ sectorRows B τ, ∀ q ∈ A.Q, q ∉ r.support := by
  intro r hr q hq hmem
  exact C.hQ q hq (C.hsupB r (List.mem_filter.mp hr).1 q hmem)

/-- Orthogonality to the sum's rows of one sector splits into the blocks. -/
theorem orth_iff (C : DirectSumCtx A B) (τ : Sector) (vA vB : List Bool)
    (hlA : vA.length = A.Q.length) :
    (∀ r ∈ sectorRows (directSumState A B) τ,
        dotPar (vA ++ vB) (rowVector (directSumState A B).Q r) % 2 = 0) ↔
      (∀ r ∈ sectorRows A τ, dotPar vA (rowVector A.Q r) % 2 = 0) ∧
        (∀ r ∈ sectorRows B τ, dotPar vB (rowVector B.Q r) % 2 = 0) := by
  have keyA : ∀ r ∈ sectorRows A τ,
      dotPar (vA ++ vB) (rowVector (A.Q ++ B.Q) r) = dotPar vA (rowVector A.Q r) := by
    intro r hr
    rw [rowVector_append, rowVector_eq_replicate_of_disjoint B.Q r (C.missA τ r hr),
      dotPar_append_eq _ _ _ _ (by rw [hlA, rowVector_length]), dotPar_replicate_false,
      Nat.add_zero]
  have keyB : ∀ r ∈ sectorRows B τ,
      dotPar (vA ++ vB) (rowVector (A.Q ++ B.Q) r) = dotPar vB (rowVector B.Q r) := by
    intro r hr
    rw [rowVector_append, rowVector_eq_replicate_of_disjoint A.Q r (C.missB τ r hr),
      dotPar_append_eq _ _ _ _ (by rw [hlA, List.length_replicate]), dotPar_replicate_false,
      Nat.zero_add]
  rw [sectorRows_directSum]
  show (∀ r ∈ sectorRows A τ ++ sectorRows B τ,
      dotPar (vA ++ vB) (rowVector (A.Q ++ B.Q) r) % 2 = 0) ↔ _
  constructor
  · intro h
    exact ⟨fun r hr => by rw [← keyA r hr]; exact h r (List.mem_append_left _ hr),
      fun r hr => by rw [← keyB r hr]; exact h r (List.mem_append_right _ hr)⟩
  · rintro ⟨hA, hB⟩ r hr
    rcases List.mem_append.mp hr with h | h
    · rw [keyA r h]; exact hA r h
    · rw [keyB r h]; exact hB r h

/-- A vector over the sum's namespace is a logical of the sum exactly when
    both parts are orthogonal to their summand's opposite rows and one of
    them is outside its summand's span. -/
theorem isLogical_iff (C : DirectSumCtx A B) (σ : Sector) (vA vB : List Bool)
    (hlA : vA.length = A.Q.length) :
    isLogicalBool (directSumState A B) σ (vA ++ vB) = true ↔
      ((∀ r ∈ sectorRows A (oppositeSector σ), dotPar vA (rowVector A.Q r) % 2 = 0) ∧
        (∀ r ∈ sectorRows B (oppositeSector σ), dotPar vB (rowVector B.Q r) % 2 = 0)) ∧
      ¬ (inSpanRows A.Q (sectorRows A σ) vA ∧ inSpanRows B.Q (sectorRows B σ) vB) := by
  rw [isLogicalBool_iff_prop, C.orth_iff (oppositeSector σ) vA vB hlA, sectorRows_directSum]
  show _ ∧ ¬ inSpanRows (A.Q ++ B.Q) (sectorRows A σ ++ sectorRows B σ) (vA ++ vB) ↔ _
  rw [inSpanRows_directSum_split A.Q B.Q _ _ vA vB (C.missA σ) (C.missB σ) hlA]

end DirectSumCtx

theorem inSpanRows_zero (Q : List Nat) (rows : List Row) :
    inSpanRows Q rows (List.replicate Q.length false) :=
  ⟨List.replicate rows.length false, List.length_replicate ..,
    by
      have h := combineRows_zero_coeffs Q.length (rows.map (rowVector Q))
      rw [List.length_map] at h
      exact h⟩

/-! ## The law -/

/-- `d_σ(A ⊕ B) = min(d_σ(A), d_σ(B))` for the exact distance. -/
theorem exactDistance?_directSum {A B : CodeState} (C : DirectSumCtx A B) (σ : Sector) :
    exactDistance? σ (directSumState A B) =
      minOpt (exactDistance? σ A) (exactDistance? σ B) := by
  have hSQ : (directSumState A B).Q.length = A.Q.length + B.Q.length := List.length_append ..
  apply leOpt_antisymm
  · apply leOpt_min
    · apply leOpt_exactDistance?_of_map
      intro vA hvA
      obtain ⟨hlen, hlog⟩ := (mem_logicalVectors_iff _ _ _).mp hvA
      obtain ⟨horth, hspan⟩ := (isLogicalBool_iff_prop _ _ _).mp hlog
      refine ⟨vA ++ List.replicate B.Q.length false, ?_, ?_⟩
      · rw [mem_logicalVectors_iff]
        refine ⟨by rw [List.length_append, List.length_replicate, hlen, hSQ], ?_⟩
        rw [C.isLogical_iff σ _ _ hlen]
        exact ⟨⟨horth, fun r _ => by rw [dotPar_comm, dotPar_replicate_false]⟩,
          fun h => hspan h.1⟩
      · rw [weight_append_eq, weight_replicate_false, Nat.add_zero]
        exact Nat.le_refl _
    · apply leOpt_exactDistance?_of_map
      intro vB hvB
      obtain ⟨hlen, hlog⟩ := (mem_logicalVectors_iff _ _ _).mp hvB
      obtain ⟨horth, hspan⟩ := (isLogicalBool_iff_prop _ _ _).mp hlog
      refine ⟨List.replicate A.Q.length false ++ vB, ?_, ?_⟩
      · rw [mem_logicalVectors_iff]
        refine ⟨by rw [List.length_append, List.length_replicate, hlen, hSQ], ?_⟩
        rw [C.isLogical_iff σ _ _ (List.length_replicate ..)]
        exact ⟨⟨fun r _ => by rw [dotPar_comm, dotPar_replicate_false], horth⟩,
          fun h => hspan h.2⟩
      · rw [weight_append_eq, weight_replicate_false, Nat.zero_add]
        exact Nat.le_refl _
  · cases hS : exactDistance? σ (directSumState A B) with
    | none => exact leOpt_none _
    | some m =>
        obtain ⟨v, hv, hw⟩ := minWeight?_attained _ m hS
        obtain ⟨hlen, hlog⟩ := (mem_logicalVectors_iff _ _ _).mp hv
        have hsplit : v = v.take A.Q.length ++ v.drop A.Q.length :=
          (List.take_append_drop _ _).symm
        have hlA : (v.take A.Q.length).length = A.Q.length := by
          rw [List.length_take, hlen, hSQ]
          omega
        have hlB : (v.drop A.Q.length).length = B.Q.length := by
          rw [List.length_drop, hlen, hSQ]
          omega
        rw [hsplit, C.isLogical_iff σ _ _ hlA] at hlog
        obtain ⟨⟨horthA, horthB⟩, hnot⟩ := hlog
        have hwsplit : weight v =
            weight (v.take A.Q.length) + weight (v.drop A.Q.length) := by
          rw [← weight_append_eq, ← hsplit]
        have hdec : inSpanRows A.Q (sectorRows A σ) (v.take A.Q.length) ∨
            ¬ inSpanRows A.Q (sectorRows A σ) (v.take A.Q.length) := by
          cases hb : inSpanRowsBool A.Q (sectorRows A σ) (v.take A.Q.length) with
          | true => exact Or.inl ((exact_inSpanRowsBool_iff _ _ _).mp hb)
          | false =>
              refine Or.inr (fun h => ?_)
              rw [(exact_inSpanRowsBool_iff _ _ _).mpr h] at hb
              exact Bool.noConfusion hb
        rcases hdec with hin | hout
        · have hB : v.drop A.Q.length ∈ logicalVectors B σ := by
            rw [mem_logicalVectors_iff]
            exact ⟨hlB, (isLogicalBool_iff_prop _ _ _).mpr ⟨horthB, fun h => hnot ⟨hin, h⟩⟩⟩
          obtain ⟨mb, hmb, hle⟩ := exactDistance?_le_of_mem hB
          rw [hmb]
          have hbm : leOpt (some mb) (some m) := by
            show mb ≤ m
            omega
          exact leOpt_trans (minOpt_le_right _ _) hbm
        · have hA : v.take A.Q.length ∈ logicalVectors A σ := by
            rw [mem_logicalVectors_iff]
            exact ⟨hlA, (isLogicalBool_iff_prop _ _ _).mpr ⟨horthA, hout⟩⟩
          obtain ⟨ma, hma, hle⟩ := exactDistance?_le_of_mem hA
          rw [hma]
          have ham : leOpt (some ma) (some m) := by
            show ma ≤ m
            omega
          exact leOpt_trans (minOpt_le_left _ _) ham

/-- The §4.2 direct-sum law for `exactDist`: each sector distance and the
    full distance of the sum are the minima of the summands'. -/
theorem exactDist_directSumState {A B : CodeState} (C : DirectSumCtx A B) :
    exactDist (directSumState A B) =
      ExactDist.mk (minOpt (exactDist A).full (exactDist B).full)
        (minOpt (exactDist A).x (exactDist B).x)
        (minOpt (exactDist A).z (exactDist B).z) := by
  have hx : exactDistOpt Sector.X (directSumState A B) =
      minOpt (exactDistOpt Sector.X A) (exactDistOpt Sector.X B) := by
    rw [exactDistOpt_eq_exactDistance?, exactDistOpt_eq_exactDistance?,
      exactDistOpt_eq_exactDistance?]
    exact exactDistance?_directSum C Sector.X
  have hz : exactDistOpt Sector.Z (directSumState A B) =
      minOpt (exactDistOpt Sector.Z A) (exactDistOpt Sector.Z B) := by
    rw [exactDistOpt_eq_exactDistance?, exactDistOpt_eq_exactDistance?,
      exactDistOpt_eq_exactDistance?]
    exact exactDistance?_directSum C Sector.Z
  unfold exactDist
  rw [hx, hz, minOpt_interchange]

end CodeCalculus
