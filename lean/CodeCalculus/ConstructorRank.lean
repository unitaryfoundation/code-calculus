import CodeCalculus.ConstructorWellFormedness
import CodeCalculus.RanksFit

/-!
# Logical counts of the typed constructors

`stateK` of a constructed state is read from the retained display. This
module shows that it can be read from the natural rows instead
(`stateK_constructedState`): the retained rows of a sector span what the
natural rows of that sector span, so the two greedy ranks agree. No
well-formedness hypothesis is used.

The rank lemmas it rests on are stated for mask lists: rank is additive
over two lists whose spans meet in zero (`rankBitmasks_append_of_disjoint`),
and an additive map with no kernel on the span preserves it
(`rankBitmasks_map`).

On top of that it proves the closed form of `spec/OPERATIONAL_SEMANTICS.md`
§4.35 for `A-DOUBLE` with the empty wiring, `k = 2 k_C`
(`doubleState_empty_k`). `ConstructorRankTyped.lean` holds the closed form
for `L-GROUP-ALGEBRA` and the count for `A-CONCAT`.
-/

namespace CodeCalculus

/-! ## Rank lemmas for mask lists -/

/-- The greedy basis of a mask list. -/
def basisOf (xs : List Nat) : List Nat := xs.foldl insertBasis []

theorem basisOf_indep (xs : List Nat) : independentMasks (basisOf xs) :=
  independentMasks_pivotDistinct _ (foldl_insertBasis_pivotDistinct xs [] pivotDistinct_nil)

theorem basisOf_span (xs : List Nat) (v : Nat) :
    inSpanMasks (basisOf xs) v ↔ inSpanMasks xs v :=
  spanEq_foldl_insertBasis_nil xs v

theorem rankBitmasks_eq_basisOf_length (xs : List Nat) :
    rankBitmasks xs = (basisOf xs).length := rfl

/-- An independent mask list has greedy rank equal to its length. -/
theorem rankBitmasks_of_indep {xs : List Nat} (h : independentMasks xs) :
    rankBitmasks xs = xs.length :=
  rankBitmasks_eq_length_of_prefix_indep xs (not_inSpan_of_independent h)

/-- The greedy rank is the length of any independent list with the same span. -/
theorem rankBitmasks_eq_of_basis {xs B : List Nat} (hB : independentMasks B)
    (hspan : ∀ v, inSpanMasks B v ↔ inSpanMasks xs v) : rankBitmasks xs = B.length := by
  rw [← rankBitmasks_eq_of_span_eq hspan, rankBitmasks_of_indep hB]

/-- Two mask lists, each inside the span of the other, have the same span. -/
theorem span_eq_of_mem {xs ys : List Nat} (h1 : ∀ x, x ∈ xs → inSpanMasks ys x)
    (h2 : ∀ y, y ∈ ys → inSpanMasks xs y) (v : Nat) :
    inSpanMasks xs v ↔ inSpanMasks ys v :=
  ⟨fun h => inSpanMasks_trans h1 h, fun h => inSpanMasks_trans h2 h⟩

/-- The span of a concatenation is the sum of the spans. -/
theorem inSpanMasks_append_iff (xs ys : List Nat) (v : Nat) :
    inSpanMasks (xs ++ ys) v ↔
      ∃ a b, inSpanMasks xs a ∧ inSpanMasks ys b ∧ v = a ^^^ b := by
  constructor
  · rintro ⟨cs, hlen, h01, hval⟩
    rw [List.length_append] at hlen
    refine ⟨combineMasks xs (cs.take xs.length), combineMasks ys (cs.drop xs.length),
      ⟨cs.take xs.length, ?_, fun c hc => h01 c (List.mem_of_mem_take hc), rfl⟩,
      ⟨cs.drop xs.length, ?_, fun c hc => h01 c (List.mem_of_mem_drop hc), rfl⟩, ?_⟩
    · rw [List.length_take]; omega
    · rw [List.length_drop]; omega
    · rw [← combineMasks_append xs ys _ _ (by rw [List.length_take]; omega),
        List.take_append_drop, hval]
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact inSpanMasks_xor (inSpanMasks_append_right ha) (inSpanMasks_append_left hb)

/-- Rank is additive over two lists whose spans meet in zero. -/
theorem rankBitmasks_append_of_disjoint (xs ys : List Nat)
    (hdis : ∀ a b, inSpanMasks xs a → inSpanMasks ys b → a ^^^ b = 0 → a = 0) :
    rankBitmasks (xs ++ ys) = rankBitmasks xs + rankBitmasks ys := by
  have hspan : ∀ v, inSpanMasks (basisOf xs ++ basisOf ys) v ↔ inSpanMasks (xs ++ ys) v := by
    intro v
    rw [inSpanMasks_append_iff, inSpanMasks_append_iff]
    constructor
    · rintro ⟨a, b, ha, hb, rfl⟩
      exact ⟨a, b, (basisOf_span xs a).mp ha, (basisOf_span ys b).mp hb, rfl⟩
    · rintro ⟨a, b, ha, hb, rfl⟩
      exact ⟨a, b, (basisOf_span xs a).mpr ha, (basisOf_span ys b).mpr hb, rfl⟩
  have hind : independentMasks (basisOf xs ++ basisOf ys) := by
    intro cs hlen h01 hval
    rw [List.length_append] at hlen
    have hl1 : (cs.take (basisOf xs).length).length = (basisOf xs).length := by
      rw [List.length_take]; omega
    have hl2 : (cs.drop (basisOf xs).length).length = (basisOf ys).length := by
      rw [List.length_drop]; omega
    have h01a : ∀ c ∈ cs.take (basisOf xs).length, c = 0 ∨ c = 1 :=
      fun c hc => h01 c (List.mem_of_mem_take hc)
    have h01b : ∀ c ∈ cs.drop (basisOf xs).length, c = 0 ∨ c = 1 :=
      fun c hc => h01 c (List.mem_of_mem_drop hc)
    have hsplit : combineMasks (basisOf xs) (cs.take (basisOf xs).length) ^^^
        combineMasks (basisOf ys) (cs.drop (basisOf xs).length) = 0 := by
      rw [← combineMasks_append _ _ _ _ hl1, List.take_append_drop, hval]
    have ha0 := hdis _ _
      ((basisOf_span xs _).mp ⟨_, hl1, h01a, rfl⟩)
      ((basisOf_span ys _).mp ⟨_, hl2, h01b, rfl⟩) hsplit
    have hb0 : combineMasks (basisOf ys) (cs.drop (basisOf xs).length) = 0 := by
      rw [ha0, Nat.zero_xor] at hsplit
      exact hsplit
    have hz1 := basisOf_indep xs _ hl1 h01a ha0
    have hz2 := basisOf_indep ys _ hl2 h01b hb0
    intro c hc
    rw [← List.take_append_drop (basisOf xs).length cs] at hc
    rcases List.mem_append.mp hc with h | h
    · exact hz1 c h
    · exact hz2 c h
  rw [rankBitmasks_eq_of_basis hind hspan, List.length_append,
    rankBitmasks_eq_basisOf_length, rankBitmasks_eq_basisOf_length]

/-- An additive map sends combinations to combinations. -/
theorem combineMasks_map_additive (f : Nat → Nat) (hadd : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    (h0 : f 0 = 0) : ∀ (xs cs : List Nat),
      combineMasks (xs.map f) cs = f (combineMasks xs cs)
  | [], cs => by simp only [List.map_nil, combineMasks_nil, h0]
  | _ :: _, [] => by
      show (0 : Nat) = f 0
      rw [h0]
  | m :: ms, c :: cs => by
      show (if c = 1 then f m else 0) ^^^ combineMasks (ms.map f) cs =
        f ((if c = 1 then m else 0) ^^^ combineMasks ms cs)
      rw [combineMasks_map_additive f hadd h0 ms cs, hadd]
      cases Nat.decEq c 1 with
      | isTrue h => simp only [h, ↓reduceIte]
      | isFalse h => simp only [h, ↓reduceIte, h0]

theorem additive_zero (f : Nat → Nat) (hadd : ∀ a b, f (a ^^^ b) = f a ^^^ f b) : f 0 = 0 := by
  have h := hadd 0 0
  rw [Nat.xor_self, Nat.xor_self] at h
  exact h

/-- The span of the image under an additive map is the image of the span. -/
theorem inSpanMasks_map_additive_iff (f : Nat → Nat) (hadd : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    (xs : List Nat) (v : Nat) :
    inSpanMasks (xs.map f) v ↔ ∃ a, inSpanMasks xs a ∧ v = f a := by
  have h0 := additive_zero f hadd
  constructor
  · rintro ⟨cs, hlen, h01, hval⟩
    rw [List.length_map] at hlen
    exact ⟨combineMasks xs cs, ⟨cs, hlen, h01, rfl⟩, by
      rw [← combineMasks_map_additive f hadd h0, hval]⟩
  · rintro ⟨a, ⟨cs, hlen, h01, hval⟩, rfl⟩
    exact ⟨cs, by rw [List.length_map]; exact hlen, h01, by
      rw [combineMasks_map_additive f hadd h0, hval]⟩

/-- An additive map with no kernel on the span preserves the rank. -/
theorem rankBitmasks_map (f : Nat → Nat) (hadd : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    (xs : List Nat) (hinj : ∀ a, inSpanMasks xs a → f a = 0 → a = 0) :
    rankBitmasks (xs.map f) = rankBitmasks xs := by
  have h0 := additive_zero f hadd
  have hind : independentMasks ((basisOf xs).map f) := by
    intro cs hlen h01 hval
    rw [List.length_map] at hlen
    rw [combineMasks_map_additive f hadd h0] at hval
    exact basisOf_indep xs cs hlen h01
      (hinj _ ((basisOf_span xs _).mp ⟨cs, hlen, h01, rfl⟩) hval)
  have hspan : ∀ v, inSpanMasks ((basisOf xs).map f) v ↔ inSpanMasks (xs.map f) v := by
    intro v
    rw [inSpanMasks_map_additive_iff f hadd, inSpanMasks_map_additive_iff f hadd]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, (basisOf_span xs a).mp ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, (basisOf_span xs a).mpr ha, rfl⟩
  rw [rankBitmasks_eq_of_basis hind hspan, List.length_map, rankBitmasks_eq_basisOf_length]

/-- A bit that is clear in every generator is clear on the span. -/
theorem testBit_false_of_inSpan {xs : List Nat} {a : Nat} {j : Nat}
    (h : ∀ x ∈ xs, x.testBit j = false) (ha : inSpanMasks xs a) : a.testBit j = false := by
  obtain ⟨cs, _, _, rfl⟩ := ha
  exact combineMasks_testBit_false xs cs j h

/-! ## The shift by `n` bits -/

theorem shiftLeft_xor (n a b : Nat) : (a ^^^ b) <<< n = (a <<< n) ^^^ (b <<< n) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_shiftLeft, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft,
    Nat.testBit_shiftLeft]
  cases decide (j ≥ n) <;> rfl

theorem eq_zero_of_shiftLeft_eq_zero (n a : Nat) (h : a <<< n = 0) : a = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  have h1 : (a <<< n).testBit (j + n) = false := by rw [h, testBit_zero_all]
  rw [Nat.testBit_shiftLeft, Nat.add_sub_cancel] at h1
  have h2 : decide (j + n ≥ n) = true := decide_eq_true (Nat.le_add_left n j)
  rw [h2, Bool.true_and] at h1
  rw [h1, testBit_zero_all]

/-- Rank is additive over a list below `2 ^ n` and a list shifted by `n`. -/
theorem rankBitmasks_append_shift (n : Nat) (xs ys : List Nat)
    (hxs : ∀ x ∈ xs, ∀ j, n ≤ j → x.testBit j = false) :
    rankBitmasks (xs ++ ys.map (· <<< n)) = rankBitmasks xs + rankBitmasks ys := by
  rw [rankBitmasks_append_of_disjoint, rankBitmasks_map (· <<< n) (shiftLeft_xor n) ys
    (fun a _ h => eq_zero_of_shiftLeft_eq_zero n a h)]
  intro a b ha hb hab
  obtain ⟨b', _, rfl⟩ := (inSpanMasks_map_additive_iff (· <<< n) (shiftLeft_xor n) ys b).mp hb
  have heq : a = b' <<< n := by
    have h := congrArg (· ^^^ (b' <<< n)) hab
    simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] at h
    exact h
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_zero_all]
  cases Nat.lt_or_ge j n with
  | inl hlt =>
      rw [heq, Nat.testBit_shiftLeft]
      have : decide (j ≥ n) = false := decide_eq_false (Nat.not_le.mpr hlt)
      rw [this, Bool.false_and]
  | inr hge => exact testBit_false_of_inSpan (fun x hx => hxs x hx j hge) ha

/-! ## `stateK` from the natural rows -/

/-- The mask of a support over the labels `0, …, n - 1`. -/
def natMask (n : Nat) (sup : List Nat) : Nat := maskOfSupport (List.range n) sup

/-- The mask of a vector over the labels `0, …, n - 1`. -/
def vecMask (n : Nat) (v : List Bool) : Nat := natMask n (supportOfVector n v)

/-- The masks of the natural rows of one sector. -/
def naturalMasks (n : Nat) (vs : List (Sector × List Bool)) (σ : Sector) : List Nat :=
  (vs.filter (fun x => x.1 = σ)).map (fun x => vecMask n x.2)

theorem sectorRows_addState_same (s : CodeState) (sec : Sector) (sup : List Nat) :
    sectorRows (addState s sec sup) sec = sectorRows s sec ++ [addRow s sec sup] := by
  unfold sectorRows
  rw [addState_rows, List.filter_append]
  have : [addRow s sec sup].filter (fun r => r.sector = sec) = [addRow s sec sup] := by
    rw [List.filter_cons_of_pos (by exact decide_eq_true rfl), List.filter_nil]
  rw [this]

theorem sectorRows_addState_other (s : CodeState) (sec σ : Sector) (sup : List Nat)
    (h : sec ≠ σ) : sectorRows (addState s sec sup) σ = sectorRows s σ := by
  unfold sectorRows
  rw [addState_rows, List.filter_append]
  have : [addRow s sec sup].filter (fun r => r.sector = σ) = [] := by
    rw [List.filter_cons_of_neg (by
      rw [Bool.not_eq_true]; exact decide_eq_false h), List.filter_nil]
  rw [this, List.append_nil]

/-- Along the retained display, the rows of a sector span what the rows
    displayed at the start and the natural rows processed since then span. -/
theorem span_foldl_retainStep (n : Nat) (σ : Sector) :
    ∀ (l : List (Sector × List Nat)) (s : CodeState), s.Q = List.range n → ∀ v,
      inSpanMasks ((sectorRows (l.foldl retainStep s) σ).map (rowBitmask (List.range n))) v ↔
      inSpanMasks ((sectorRows s σ).map (rowBitmask (List.range n)) ++
        (l.filter (fun x => x.1 = σ)).map (fun x => natMask n x.2)) v
  | [], s, _, v => by
      rw [List.foldl_nil, List.filter_nil, List.map_nil, List.append_nil]
  | x :: l, s, hQ, v => by
      rw [List.foldl_cons]
      have hQ' : (retainStep s x).Q = List.range n := by rw [retainStep_Q, hQ]
      rw [span_foldl_retainStep n σ l (retainStep s x) hQ' v]
      cases hb : inSpanRowsBool s.Q (s.rows.filter (fun r => r.sector = x.1))
          (s.Q.map (fun q => x.2.contains q)) with
      | true =>
          have hstep : retainStep s x = s := by
            unfold retainStep
            rw [hb]
            rfl
          rw [hstep]
          cases Decidable.em (x.1 = σ) with
          | inl hσ =>
              rw [List.filter_cons_of_pos (by exact decide_eq_true hσ), List.map_cons]
              have hin : inSpanMasks ((sectorRows s σ).map (rowBitmask (List.range n)))
                  (natMask n x.2) := by
                have h1 : inSpanRows s.Q (sectorRows s x.1)
                    (rowVector s.Q (addRow s x.1 x.2)) :=
                  (inSpanRowsBool_iff _ _ _).mp hb
                have h2 := (inSpanRows_iff_inSpanMasks s.Q (by rw [hQ]; exact nodup_range n)
                  _ _).mp h1
                rw [hQ, hσ] at h2
                exact h2
              apply span_eq_of_mem
              · intro m hm
                rcases List.mem_append.mp hm with h | h
                · exact inSpanMasks_of_mem (List.mem_append_left _ h)
                · exact inSpanMasks_of_mem
                    (List.mem_append_right _ (List.mem_cons_of_mem _ h))
              · intro m hm
                rcases List.mem_append.mp hm with h | h
                · exact inSpanMasks_of_mem (List.mem_append_left _ h)
                · rcases List.mem_cons.mp h with h | h
                  · rw [h]
                    exact inSpanMasks_append_right hin
                  · exact inSpanMasks_of_mem (List.mem_append_right _ h)
          | inr hσ =>
              rw [List.filter_cons_of_neg (by
                rw [Bool.not_eq_true]; exact decide_eq_false hσ)]
      | false =>
          have hstep : retainStep s x = addState s x.1 x.2 := by
            unfold retainStep
            rw [hb]
            rfl
          rw [hstep]
          cases Decidable.em (x.1 = σ) with
          | inl hσ =>
              rw [List.filter_cons_of_pos (by exact decide_eq_true hσ), List.map_cons,
                ← hσ, sectorRows_addState_same, List.map_append, List.append_assoc]
              rfl
          | inr hσ =>
              rw [List.filter_cons_of_neg (by
                rw [Bool.not_eq_true]; exact decide_eq_false hσ),
                sectorRows_addState_other s x.1 σ x.2 hσ]

theorem filter_naturalRows (n : Nat) (vs : List (Sector × List Bool)) (σ : Sector) :
    ((naturalRows n vs).filter (fun x => x.1 = σ)).map (fun x => natMask n x.2) =
      naturalMasks n vs σ := by
  unfold naturalRows naturalMasks
  induction vs with
  | nil => rfl
  | cons x vs ih =>
      rw [List.map_cons]
      cases Decidable.em (x.1 = σ) with
      | inl h =>
          rw [List.filter_cons_of_pos (by exact decide_eq_true h),
            List.filter_cons_of_pos (by exact decide_eq_true h), List.map_cons, List.map_cons, ih]
          rfl
      | inr h =>
          rw [List.filter_cons_of_neg (by rw [Bool.not_eq_true]; exact decide_eq_false h),
            List.filter_cons_of_neg (by rw [Bool.not_eq_true]; exact decide_eq_false h), ih]

/-- The rank of a sector of a constructed state is the rank of the natural
    rows of that sector. -/
theorem sectorRank_constructedState (n : Nat) (vs : List (Sector × List Bool)) (σ : Sector) :
    sectorRank (constructedState n vs).Q (constructedState n vs).rows σ =
      rankBitmasks (naturalMasks n vs σ) := by
  rw [constructedState_Q]
  unfold sectorRank
  apply rankBitmasks_eq_of_span_eq
  intro v
  have h := span_foldl_retainStep n σ (naturalRows n vs) (emptyState n) rfl v
  rw [filter_naturalRows] at h
  exact h

/-- `k` of a constructed state, read from the natural rows. -/
theorem stateK_constructedState (n : Nat) (vs : List (Sector × List Bool)) :
    stateK (constructedState n vs) =
      n - rankBitmasks (naturalMasks n vs Sector.X) -
        rankBitmasks (naturalMasks n vs Sector.Z) := by
  unfold stateK
  rw [sectorRank_constructedState, sectorRank_constructedState, constructedState_Q,
    List.length_range]

/-! ## Masks of vectors -/

theorem testBit_natMask (n : Nat) (sup : List Nat) (i : Nat) :
    (natMask n sup).testBit i = qubitBit (List.range n) sup i :=
  testBit_rowBitmask (List.range n) (nodup_range n) ⟨0, Sector.X, sup⟩ i

/-- Bit `i` of the mask of a vector is entry `i` of the vector, for `i < n`. -/
theorem testBit_vecMask (n : Nat) (v : List Bool) (i : Nat) :
    (vecMask n v).testBit i = (decide (i < n) && v.getD i false) := by
  unfold vecMask
  rw [testBit_natMask]
  unfold qubitBit
  cases Nat.lt_or_ge i n with
  | inl hlt =>
      rw [List.getElem?_range hlt, decide_eq_true hlt, Bool.true_and]
      show (supportOfVector n v).contains i = v.getD i false
      rw [Bool.eq_iff_iff, List.contains_iff_mem]
      unfold supportOfVector
      rw [List.mem_filter, List.mem_range]
      exact ⟨fun h => h.2, fun h => ⟨hlt, h⟩⟩
  | inr hge =>
      rw [List.getElem?_eq_none (by rw [List.length_range]; exact hge),
        decide_eq_false (Nat.not_lt.mpr hge), Bool.false_and]

theorem getD_rowVector (Q : List Nat) (r : Row) (i : Nat) :
    (rowVector Q r).getD i false = qubitBit Q r.support i := by
  unfold rowVector qubitBit
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases Q[i]? <;> rfl

theorem getD_map_false (Q : List Nat) (i : Nat) :
    (Q.map (fun _ => false)).getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases Q[i]? <;> rfl

theorem qubitBit_high (Q sup : List Nat) (i : Nat) (h : Q.length ≤ i) :
    qubitBit Q sup i = false := by
  unfold qubitBit
  rw [List.getElem?_eq_none h]

/-- The mask of a row vector followed by a zero block is the row's mask. -/
theorem vecMask_row_zero (Q : List Nat) (hQ : Q.Nodup) (r : Row) :
    vecMask (2 * Q.length) (rowVector Q r ++ Q.map (fun _ => false)) = rowBitmask Q r := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_vecMask, testBit_rowBitmask Q hQ]
  have hlen : (rowVector Q r).length = Q.length := by unfold rowVector; rw [List.length_map]
  cases Nat.lt_or_ge i Q.length with
  | inl hlt =>
      rw [decide_eq_true (show i < 2 * Q.length by omega), Bool.true_and,
        List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hlen]; exact hlt),
        ← List.getD_eq_getElem?_getD, getD_rowVector]
  | inr hge =>
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen]; exact hge),
        ← List.getD_eq_getElem?_getD, getD_map_false, Bool.and_false, qubitBit_high Q _ i hge]

/-- The mask of a zero block followed by a row vector is the row's mask
    shifted by the block length. -/
theorem vecMask_zero_row (Q : List Nat) (hQ : Q.Nodup) (r : Row) :
    vecMask (2 * Q.length) (Q.map (fun _ => false) ++ rowVector Q r) =
      rowBitmask Q r <<< Q.length := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_vecMask, Nat.testBit_shiftLeft, testBit_rowBitmask Q hQ]
  have hlen : (Q.map (fun _ => false)).length = Q.length := by rw [List.length_map]
  cases Nat.lt_or_ge i Q.length with
  | inl hlt =>
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hlen]; exact hlt),
        ← List.getD_eq_getElem?_getD, getD_map_false, Bool.and_false,
        decide_eq_false (show ¬ i ≥ Q.length by omega), Bool.false_and]
  | inr hge =>
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen]; exact hge),
        ← List.getD_eq_getElem?_getD, getD_rowVector, hlen, decide_eq_true hge, Bool.true_and]
      cases Nat.lt_or_ge i (2 * Q.length) with
      | inl h2 => rw [decide_eq_true h2, Bool.true_and]
      | inr h2 =>
          rw [qubitBit_high Q _ _ (show Q.length ≤ i - Q.length by omega), Bool.and_false]

/-! ## `A-DOUBLE` with the empty wiring -/

/-- The sector of the sheet-1 copy of a row. -/
def doubleSector (conj : Bool) (σ : Sector) : Sector :=
  if conj then oppositeSector σ else σ

theorem doubleSector_eq_iff (conj : Bool) (σ τ : Sector) :
    doubleSector conj σ = τ ↔ σ = doubleSector conj τ := by
  cases conj <;> cases σ <;> cases τ <;> decide

/-- With the empty wiring, the natural rows are each row on sheet 0 and then
    on sheet 1. -/
theorem doubleVectors_empty (C : CodeState) (conj : Bool) :
    doubleVectors C [] conj = C.rows.flatMap (fun r =>
      [(r.sector, rowVector C.Q r ++ C.Q.map (fun _ => false)),
       (doubleSector conj r.sector, C.Q.map (fun _ => false) ++ rowVector C.Q r)]) := by
  unfold doubleVectors
  congr 1
  funext r
  cases conj <;> cases hs : r.sector <;>
    simp [doubleTwisted, rowVector, doubleSector, oppositeSector]

/-- The masks of the natural rows of one sector: the factor's rows of that
    sector, and the shifted rows of the sector that sheet 1 sends to it. -/
theorem mem_naturalMasks_double (C : CodeState) (hQ : C.Q.Nodup) (conj : Bool) (σ : Sector)
    (m : Nat) :
    m ∈ naturalMasks (doubleQubits C) (doubleVectors C [] conj) σ ↔
      m ∈ (sectorRows C σ).map (rowBitmask C.Q) ++
        ((sectorRows C (doubleSector conj σ)).map (rowBitmask C.Q)).map (· <<< C.Q.length) := by
  unfold naturalMasks doubleQubits sectorRows
  rw [doubleVectors_empty]
  simp only [List.mem_map, List.mem_filter, List.mem_flatMap, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq]
  constructor
  · rintro ⟨x, ⟨⟨r, hr, hx | hx⟩, hσ⟩, rfl⟩
    · subst hx
      exact Or.inl ⟨r, ⟨hr, hσ⟩, (vecMask_row_zero C.Q hQ r).symm⟩
    · subst hx
      exact Or.inr ⟨_, ⟨r, ⟨hr, (doubleSector_eq_iff conj _ _).mp hσ⟩, rfl⟩,
        (vecMask_zero_row C.Q hQ r).symm⟩
  · rintro (⟨r, ⟨hr, hσ⟩, rfl⟩ | ⟨_, ⟨r, ⟨hr, hσ⟩, rfl⟩, rfl⟩)
    · exact ⟨_, ⟨⟨r, hr, Or.inl rfl⟩, hσ⟩, vecMask_row_zero C.Q hQ r⟩
    · exact ⟨_, ⟨⟨r, hr, Or.inr rfl⟩, (doubleSector_eq_iff conj _ _).mpr hσ⟩,
        vecMask_zero_row C.Q hQ r⟩

/-- The rank of a sector of the double: the factor's rank in that sector plus
    its rank in the sector that sheet 1 sends to it. -/
theorem rank_naturalMasks_double (C : CodeState) (hQ : C.Q.Nodup) (conj : Bool) (σ : Sector) :
    rankBitmasks (naturalMasks (doubleQubits C) (doubleVectors C [] conj) σ) =
      sectorRank C.Q C.rows σ + sectorRank C.Q C.rows (doubleSector conj σ) := by
  have hspan := span_eq_of_mem
    (fun x hx => inSpanMasks_of_mem ((mem_naturalMasks_double C hQ conj σ x).mp hx))
    (fun y hy => inSpanMasks_of_mem ((mem_naturalMasks_double C hQ conj σ y).mpr hy))
  rw [rankBitmasks_eq_of_span_eq hspan, rankBitmasks_append_shift]
  · rfl
  · intro x hx j hj
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hx
    exact rowBitmask_testBit_high C.Q hQ r j hj

/-- §4.35: with the empty wiring, `k = 2 k_C`. Only a repeat-free namespace
    is used. The overlap condition of the `A-DOUBLE` rule is not needed: the
    count is a count of ranks. -/
theorem doubleState_empty_k (C : CodeState) (conj : Bool) (hQ : C.Q.Nodup) :
    stateK (doubleState C [] conj) = 2 * stateK C := by
  unfold doubleState
  rw [stateK_constructedState, rank_naturalMasks_double C hQ, rank_naturalMasks_double C hQ]
  unfold stateK doubleQubits
  cases conj
  · show 2 * C.Q.length - (sectorRank C.Q C.rows Sector.X + sectorRank C.Q C.rows Sector.X) -
      (sectorRank C.Q C.rows Sector.Z + sectorRank C.Q C.rows Sector.Z) = _
    omega
  · show 2 * C.Q.length - (sectorRank C.Q C.rows Sector.X + sectorRank C.Q C.rows Sector.Z) -
      (sectorRank C.Q C.rows Sector.Z + sectorRank C.Q C.rows Sector.X) = _
    omega

/-- The same for a well-formed factor. -/
theorem doubleState_empty_k_closed (C : CodeState) (conj : Bool)
    (hC : EncodingWellFormed C) :
    stateK (doubleState C [] conj) = 2 * stateK C :=
  doubleState_empty_k C conj hC.1

/-- `A-DOUBLE` with the empty wiring: the evaluated state has `k = 2 k_C`,
    for any factor expression. -/
theorem evalExpr_double_empty_k {e : StateExpr} {conj : Bool} {s : CodeState}
    (h : EvalExpr (StateExpr.double e [] conj) s) :
    ∃ sC, EvalExpr e sC ∧ stateK s = 2 * stateK sC := by
  cases h with
  | double hC _ _ _ hEvalC => exact ⟨_, hEvalC, doubleState_empty_k_closed _ conj hC⟩

end CodeCalculus
