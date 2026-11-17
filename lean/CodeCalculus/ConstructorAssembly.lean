import CodeCalculus.ConstructorOrthogonality

/-!
# Well-formedness and `n` for the five constructors of issue #369 (issue #407)

The per-constructor half of `spec/OPERATIONAL_SEMANTICS.md` §4.35, for the
state updates `productState`, `doubleState`, `balancedState`, `tannerState`,
and `tileState` of `Constructors.lean`.

* `A-DOUBLE`, `L-TANNER`, `L-TILE`: the pairwise even overlap of the natural
  rows is a premise of the rule, so every evaluation yields a well-formed
  state (`evalExpr_double_wf`, `evalExpr_tanner_wf`, `evalExpr_tile_wf`),
  with no further hypothesis.
* `A-PRODUCT`, `L-BALANCED`: the overlap is not a premise of the rule.
  For `A-PRODUCT` it is proved below for every pair of well-formed factors
  (`product_naturalOrthogonal`, `evalExpr_product_wf`). For `L-BALANCED`
  this module proves well-formedness from the overlap as a hypothesis
  (`evalExpr_balanced_wf`), and `BalancedOverlap.lean` proves the overlap
  for every typed input (`balanced_naturalOrthogonal`), so every evaluation
  yields a well-formed state (`evalExpr_balanced_wellFormed`).
* `n`: the qubit count of each card (`evalExpr_product_n`,
  `evalExpr_double_n`, `evalExpr_balanced_n`, `evalExpr_tanner_n`,
  `evalExpr_tile_n`).
* `k`: no closed form is mechanized. On a well-formed output `k` is the rank
  bookkeeping of `stateK_of_wf`.
-/

namespace CodeCalculus

/-- The overlap test of the rules gives the overlap hypothesis of the
    retained-display theorem. -/
theorem naturalOrthogonal_of_commuteBool {rows : List (Sector × List Nat)}
    (h : naturalCommuteBool rows = true) : NaturalOrthogonal rows := by
  intro x hx y hy hsec
  unfold naturalCommuteBool at h
  rw [List.all_eq_true] at h
  have hx' := h x hx
  rw [List.all_eq_true] at hx'
  have hy' := hx' y hy
  rw [Bool.or_eq_true] at hy'
  rcases hy' with hsame | heven
  · have hxy : x.1 = y.1 := of_decide_eq_true hsame
    rw [hsec] at hxy
    cases hs : x.1 with
    | X => rw [hs] at hxy; cases hxy
    | Z => rw [hs] at hxy; cases hxy
  · exact Nat.eq_of_beq_eq_true heven

/-! ## `A-PRODUCT`: the natural rows have pairwise even overlap -/

theorem filter_length_zero {α : Type} (p : α → Bool) (hp : ∀ x, p x = false) :
    ∀ L : List α, (L.filter p).length = 0
  | [] => rfl
  | x :: L => by
      rw [List.filter_cons_of_neg (by rw [hp x]; exact Bool.false_ne_true)]
      exact filter_length_zero p hp L

/-- The pairs `(a, b)` of one row with first coordinate `i`. -/
theorem filter_row_fst (a i : Nat) (F : Nat → Bool) : ∀ L : List Nat,
    ((L.map (fun b => (a, b))).filter
      (fun p : Nat × Nat => decide (p.1 = i) && F p.2)).length =
      if a = i then (L.filter F).length else 0
  | [] => by split <;> rfl
  | b :: L => by
      have ih := filter_row_fst a i F L
      rw [List.map_cons, List.filter_cons, List.filter_cons]
      rcases Decidable.em (a = i) with h | h
      · rw [if_pos h] at ih ⊢
        show List.length (if (decide (a = i) && F b) = true then _ else _) = _
        rw [decide_eq_true h, Bool.true_and]
        cases F b with
        | true => rw [if_pos rfl, if_pos rfl, List.length_cons, List.length_cons, ih]
        | false => rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, ih]
      · rw [if_neg h] at ih ⊢
        show List.length (if (decide (a = i) && F b) = true then _ else _) = _
        rw [decide_eq_false h, Bool.false_and, if_neg Bool.false_ne_true, ih]

/-- The pairs with first coordinate `i`. -/
theorem filter_pairs_fst (n i : Nat) (F : Nat → Bool) : ∀ l : List Nat, l.Nodup →
    ((l.flatMap (fun a => (List.range n).map (fun b => (a, b)))).filter
      (fun p : Nat × Nat => decide (p.1 = i) && F p.2)).length =
      if i ∈ l then ((List.range n).filter F).length else 0
  | [], _ => by rw [if_neg List.not_mem_nil]; rfl
  | a :: l, h => by
      rw [List.nodup_cons] at h
      rw [List.flatMap_cons, List.filter_append, List.length_append, filter_row_fst,
        filter_pairs_fst n i F l h.2]
      rcases Decidable.em (a = i) with hai | hai
      · subst hai
        rw [if_pos rfl, if_neg h.1, if_pos (List.mem_cons_self ..), Nat.add_zero]
      · rw [if_neg hai]
        rcases Decidable.em (i ∈ l) with hil | hil
        · rw [if_pos hil, if_pos (List.mem_cons_of_mem a hil), Nat.zero_add]
        · rw [if_neg hil, if_neg (fun hm => by
            rcases List.mem_cons.mp hm with h1 | h1
            · exact hai h1.symm
            · exact hil h1)]

/-- The pairs `(a, b)` of one row with second coordinate `j`. -/
theorem filter_row_snd (a j : Nat) (F : Nat → Bool) (L : List Nat) (hnd : L.Nodup)
    (hj : j ∈ L) :
    ((L.map (fun b => (a, b))).filter
      (fun p : Nat × Nat => decide (p.2 = j) && F p.1)).length = if F a then 1 else 0 := by
  rw [List.filter_map, List.length_map]
  exact filter_point_length j (F a) L hnd hj

/-- The pairs with second coordinate `j`. -/
theorem filter_pairs_snd (n j : Nat) (F : Nat → Bool) (hj : j < n) : ∀ l : List Nat,
    ((l.flatMap (fun a => (List.range n).map (fun b => (a, b)))).filter
      (fun p : Nat × Nat => decide (p.2 = j) && F p.1)).length = (l.filter F).length
  | [] => rfl
  | a :: l => by
      rw [List.flatMap_cons, List.filter_append, List.length_append,
        filter_row_snd a j F _ (nodup_range_cf n) (List.mem_range.mpr hj),
        filter_pairs_snd n j F hj l, List.filter_cons]
      cases F a with
      | true => rw [if_pos rfl, if_pos rfl, List.length_cons, Nat.add_comm]
      | false => rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, Nat.zero_add]

/-- The overlap of two rows given block by block over three lists. -/
theorem dotPar_three {α β γ : Type} (L1 : List α) (L2 : List β) (L3 : List γ)
    (f f' : α → Bool) (g g' : β → Bool) (h h' : γ → Bool) :
    dotPar (L1.map f ++ L2.map g ++ L3.map h) (L1.map f' ++ L2.map g' ++ L3.map h') =
      (L1.filter (fun x => f x && f' x)).length + (L2.filter (fun x => g x && g' x)).length +
        (L3.filter (fun x => h x && h' x)).length := by
  rw [dotPar_append _ _ _ _ (by
      rw [List.length_append, List.length_append, List.length_map, List.length_map,
        List.length_map, List.length_map]),
    dotPar_append _ _ _ _ (by rw [List.length_map, List.length_map]),
    dotPar_map_map_gen, dotPar_map_map_gen, dotPar_map_map_gen]

/-- Two conditions that single out the pair `(c₁, c₂)`, the second
    coordinate tested first. -/
theorem point_pred_snd_fst (c1 c2 : Nat) (U V : Nat → Bool) :
    (fun p : Nat × Nat => (decide (p.2 = c2) && U p.1) && (decide (p.1 = c1) && V p.2)) =
      (fun p => decide (p = (c1, c2)) && (U c1 && V c2)) := by
  funext p
  obtain ⟨a, b⟩ := p
  rcases Decidable.em (b = c2) with h2 | h2
  · rcases Decidable.em (a = c1) with h1 | h1
    · subst h1; subst h2
      rw [decide_eq_true rfl, decide_eq_true rfl, decide_eq_true rfl]
      rfl
    · rw [decide_eq_false h1, decide_eq_false (fun h => h1 (Prod.mk.inj h).1)]
      rw [Bool.false_and, Bool.and_false, Bool.false_and]
  · rw [decide_eq_false h2, decide_eq_false (fun h => h2 (Prod.mk.inj h).2)]
    rw [Bool.false_and, Bool.false_and, Bool.false_and]

/-- The same, the first coordinate tested first. -/
theorem point_pred_fst_snd (c1 c2 : Nat) (U V : Nat → Bool) :
    (fun p : Nat × Nat => (decide (p.1 = c1) && V p.2) && (decide (p.2 = c2) && U p.1)) =
      (fun p => decide (p = (c1, c2)) && (V c2 && U c1)) := by
  funext p
  obtain ⟨a, b⟩ := p
  rcases Decidable.em (a = c1) with h1 | h1
  · rcases Decidable.em (b = c2) with h2 | h2
    · subst h1; subst h2
      rw [decide_eq_true rfl, decide_eq_true rfl, decide_eq_true rfl]
      rfl
    · rw [decide_eq_false h2, decide_eq_false (fun h => h2 (Prod.mk.inj h).2)]
      rw [Bool.false_and, Bool.and_false, Bool.false_and]
  · rw [decide_eq_false h1, decide_eq_false (fun h => h1 (Prod.mk.inj h).1)]
    rw [Bool.false_and, Bool.false_and, Bool.false_and]

/-- Two tests of the first coordinate against `i` and `i'`. -/
theorem fst_pred (i i' : Nat) (U V : Nat → Bool) :
    (fun p : Nat × Nat => (decide (p.1 = i) && U p.2) && (decide (p.1 = i') && V p.2)) =
      (fun p => decide (p.1 = i) && (decide (i = i') && (U p.2 && V p.2))) := by
  funext p
  obtain ⟨a, b⟩ := p
  show ((decide (a = i) && U b) && (decide (a = i') && V b)) =
    (decide (a = i) && (decide (i = i') && (U b && V b)))
  rcases Decidable.em (a = i) with h | h
  · subst h
    rw [decide_eq_true rfl, Bool.true_and, Bool.true_and]
    cases decide (a = i') <;> cases U b <;> rfl
  · rw [decide_eq_false h, Bool.false_and, Bool.false_and, Bool.false_and]

/-- Two tests of the second coordinate against `j` and `j'`. -/
theorem snd_pred (j j' : Nat) (U V : Nat → Bool) :
    (fun p : Nat × Nat => (decide (p.2 = j) && U p.1) && (decide (p.2 = j') && V p.1)) =
      (fun p => decide (p.2 = j) && (decide (j = j') && (U p.1 && V p.1))) := by
  funext p
  obtain ⟨a, b⟩ := p
  show ((decide (b = j) && U a) && (decide (b = j') && V a)) =
    (decide (b = j) && (decide (j = j') && (U a && V a)))
  rcases Decidable.em (b = j) with h | h
  · subst h
    rw [decide_eq_true rfl, Bool.true_and, Bool.true_and]
    cases decide (b = j') <;> cases U a <;> rfl
  · rw [decide_eq_false h, Bool.false_and, Bool.false_and, Bool.false_and]

/-- The even overlap of the rows of two matrices over `n` columns. -/
def MatricesCommute (n : Nat) (MX MZ : List (List Bool)) : Prop :=
  ∀ x z, x < MX.length → z < MZ.length →
    ((List.range n).filter (fun i => matEntry MX x i && matEntry MZ z i)).length % 2 = 0

section ProductOverlap

variable (na nb : Nat) (AX AZ BX BZ : List (List Bool))

/-- The rows `(i, x)` and `(z, j)` meet at the label `(z, x)` and at the
    label `(i, j)`, each exactly when `z` contains `i` and `x` contains
    `j`. -/
theorem product_overlap_X1_Z1 (ix zj : Nat × Nat)
    (hix : ix ∈ indexPairs na BX.length) (hzj : zj ∈ indexPairs AZ.length nb) :
    dotPar (productX1 na nb AX AZ BX BZ ix) (productZ1 na nb AX AZ BX BZ zj) % 2 = 0 := by
  obtain ⟨i, x⟩ := ix
  obtain ⟨z, j⟩ := zj
  have hix' := mem_indexPairs.mp hix
  have hzj' := mem_indexPairs.mp hzj
  unfold productX1 productZ1
  rw [dotPar_three,
    point_pred_snd_fst z x (fun a => matEntry AZ a i) (fun b => matEntry BX b j),
    point_pred_fst_snd i j (fun a => matEntry AZ z a) (fun b => matEntry BX x b),
    filter_point_length (z, x) _ _ (nodup_indexPairs _ _)
      (mem_indexPairs.mpr ⟨hzj'.1, hix'.2⟩),
    filter_point_length (i, j) _ _ (nodup_indexPairs _ _)
      (mem_indexPairs.mpr ⟨hix'.1, hzj'.2⟩),
    filter_length_zero _ (fun _ => Bool.and_false _)]
  cases matEntry AZ z i <;> cases matEntry BX x j <;> rfl

/-- The rows `(x, j)` and `(i, z)` meet at the label `(i, j)` and at the
    label `(x, z)`, each exactly when `x` contains `i` and `z` contains
    `j`. -/
theorem product_overlap_X2_Z2 (xj iz : Nat × Nat)
    (hxj : xj ∈ indexPairs AX.length nb) (hiz : iz ∈ indexPairs na BZ.length) :
    dotPar (productX2 na nb AX AZ BX BZ xj) (productZ2 na nb AX AZ BX BZ iz) % 2 = 0 := by
  obtain ⟨x, j⟩ := xj
  obtain ⟨i, z⟩ := iz
  have hxj' := mem_indexPairs.mp hxj
  have hiz' := mem_indexPairs.mp hiz
  unfold productX2 productZ2
  rw [dotPar_three,
    point_pred_snd_fst i j (fun a => matEntry AX x a) (fun b => matEntry BZ z b),
    point_pred_fst_snd x z (fun a => matEntry AX a i) (fun b => matEntry BZ b j),
    filter_point_length (i, j) _ _ (nodup_indexPairs _ _)
      (mem_indexPairs.mpr ⟨hiz'.1, hxj'.2⟩),
    filter_point_length (x, z) _ _ (nodup_indexPairs _ _)
      (mem_indexPairs.mpr ⟨hxj'.1, hiz'.2⟩),
    filter_length_zero _ (fun _ => Bool.false_and _)]
  cases matEntry AX x i <;> cases matEntry BZ z j <;> rfl

/-- The rows `(i, x)` and `(i', z)` meet only on the labels `(i, j)`, and
    only when `i = i'`, in the overlap of the rows `x` and `z` of `B`. -/
theorem product_overlap_X1_Z2 (hB : MatricesCommute nb BX BZ) (ix iz : Nat × Nat)
    (hix : ix ∈ indexPairs na BX.length) (hiz : iz ∈ indexPairs na BZ.length) :
    dotPar (productX1 na nb AX AZ BX BZ ix) (productZ2 na nb AX AZ BX BZ iz) % 2 = 0 := by
  obtain ⟨i, x⟩ := ix
  obtain ⟨i', z⟩ := iz
  have hix' := mem_indexPairs.mp hix
  have hiz' := mem_indexPairs.mp hiz
  unfold productX1 productZ2
  rw [dotPar_three, filter_length_zero _ (fun _ => Bool.and_false _),
    filter_length_zero (fun _ : Nat × Nat => false && _) (fun _ => Bool.false_and _),
    fst_pred i i' (fun b => matEntry BX x b) (fun b => matEntry BZ z b)]
  rcases Decidable.em (i = i') with h | h
  · rw [decide_eq_true h]
    unfold indexPairs
    rw [filter_pairs_fst nb i (fun b => true && (matEntry BX x b && matEntry BZ z b)) _
      (nodup_range_cf _), if_pos (List.mem_range.mpr hix'.1), Nat.zero_add, Nat.add_zero]
    exact hB x z hix'.2 hiz'.2
  · rw [decide_eq_false h,
      filter_length_zero _ (fun p => by rw [Bool.false_and, Bool.and_false])]

/-- The rows `(x, j)` and `(z, j')` meet only on the labels `(i, j)`, and
    only when `j = j'`, in the overlap of the rows `x` and `z` of `A`. -/
theorem product_overlap_X2_Z1 (hA : MatricesCommute na AX AZ) (xj zj : Nat × Nat)
    (hxj : xj ∈ indexPairs AX.length nb) (hzj : zj ∈ indexPairs AZ.length nb) :
    dotPar (productX2 na nb AX AZ BX BZ xj) (productZ1 na nb AX AZ BX BZ zj) % 2 = 0 := by
  obtain ⟨x, j⟩ := xj
  obtain ⟨z, j'⟩ := zj
  have hxj' := mem_indexPairs.mp hxj
  have hzj' := mem_indexPairs.mp hzj
  unfold productX2 productZ1
  rw [dotPar_three, filter_length_zero _ (fun _ => Bool.false_and _),
    filter_length_zero (fun p : Nat × Nat => (decide (p.1 = x) && matEntry BZ p.2 j) && false)
      (fun _ => Bool.and_false _),
    snd_pred j j' (fun a => matEntry AX x a) (fun a => matEntry AZ z a)]
  rcases Decidable.em (j = j') with h | h
  · rw [decide_eq_true h]
    unfold indexPairs
    rw [filter_pairs_snd nb j (fun a => true && (matEntry AX x a && matEntry AZ z a))
      hxj'.2, Nat.zero_add, Nat.add_zero]
    exact hA x z hxj'.1 hzj'.1
  · rw [decide_eq_false h,
      filter_length_zero _ (fun p => by rw [Bool.false_and, Bool.and_false])]

theorem length_productXVectors :
    ∀ v ∈ productXVectors na nb AX AZ BX BZ,
      v.length = AZ.length * BX.length + na * nb + AX.length * BZ.length := by
  intro v hv
  unfold productXVectors at hv
  rcases List.mem_append.mp hv with h | h
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp h
    unfold productX1
    rw [List.length_append, List.length_append, List.length_map, List.length_map,
      List.length_map, length_indexPairs, length_indexPairs, length_indexPairs]
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp h
    unfold productX2
    rw [List.length_append, List.length_append, List.length_map, List.length_map,
      List.length_map, length_indexPairs, length_indexPairs, length_indexPairs]

theorem length_productZVectors :
    ∀ v ∈ productZVectors na nb AX AZ BX BZ,
      v.length = AZ.length * BX.length + na * nb + AX.length * BZ.length := by
  intro v hv
  unfold productZVectors at hv
  rcases List.mem_append.mp hv with h | h
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp h
    unfold productZ1
    rw [List.length_append, List.length_append, List.length_map, List.length_map,
      List.length_map, length_indexPairs, length_indexPairs, length_indexPairs]
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp h
    unfold productZ2
    rw [List.length_append, List.length_append, List.length_map, List.length_map,
      List.length_map, length_indexPairs, length_indexPairs, length_indexPairs]

/-- Every natural `X`-row has even overlap with every natural `Z`-row when
    the rows of each factor do. -/
theorem product_cross (hA : MatricesCommute na AX AZ) (hB : MatricesCommute nb BX BZ) :
    ∀ vx ∈ productXVectors na nb AX AZ BX BZ, ∀ vz ∈ productZVectors na nb AX AZ BX BZ,
      dotPar vx vz % 2 = 0 := by
  intro vx hvx vz hvz
  unfold productXVectors at hvx
  unfold productZVectors at hvz
  rcases List.mem_append.mp hvx with h1 | h2
  · obtain ⟨ix, hix, rfl⟩ := List.mem_map.mp h1
    rcases List.mem_append.mp hvz with k1 | k2
    · obtain ⟨zj, hzj, rfl⟩ := List.mem_map.mp k1
      exact product_overlap_X1_Z1 na nb AX AZ BX BZ ix zj hix hzj
    · obtain ⟨iz, hiz, rfl⟩ := List.mem_map.mp k2
      exact product_overlap_X1_Z2 na nb AX AZ BX BZ hB ix iz hix hiz
  · obtain ⟨xj, hxj, rfl⟩ := List.mem_map.mp h2
    rcases List.mem_append.mp hvz with k1 | k2
    · obtain ⟨zj, hzj, rfl⟩ := List.mem_map.mp k1
      exact product_overlap_X2_Z1 na nb AX AZ BX BZ hA xj zj hxj hzj
    · obtain ⟨iz, hiz, rfl⟩ := List.mem_map.mp k2
      exact product_overlap_X2_Z2 na nb AX AZ BX BZ xj iz hxj hiz

end ProductOverlap

/-- Natural rows given as `X`-vectors and then `Z`-vectors of length `n`
    have pairwise even overlap across the sectors when every `X`-vector has
    even overlap with every `Z`-vector. -/
theorem naturalOrthogonal_of_cross (n : Nat) (XV ZV : List (List Bool))
    (hX : ∀ v ∈ XV, v.length = n) (hZ : ∀ v ∈ ZV, v.length = n)
    (hcross : ∀ vx ∈ XV, ∀ vz ∈ ZV, dotPar vx vz % 2 = 0) :
    NaturalOrthogonal (naturalRows n
      (XV.map (fun v => (Sector.X, v)) ++ ZV.map (fun v => (Sector.Z, v)))) := by
  intro x hx y hy hsec
  unfold naturalRows at hx hy
  obtain ⟨vx, hvx, rfl⟩ := List.mem_map.mp hx
  obtain ⟨vy, hvy, rfl⟩ := List.mem_map.mp hy
  rcases List.mem_append.mp hvx with h1 | h2
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h1
    rcases List.mem_append.mp hvy with k1 | k2
    · obtain ⟨w, _, rfl⟩ := List.mem_map.mp k1
      cases hsec
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp k2
      show supportIntersectionSize (supportOfVector n u) (supportOfVector n w) % 2 = 0
      rw [overlap_supportOfVector n u w (hX u hu) (hZ w hw)]
      exact hcross u hu w hw
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h2
    rcases List.mem_append.mp hvy with k1 | k2
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp k1
      show supportIntersectionSize (supportOfVector n u) (supportOfVector n w) % 2 = 0
      rw [overlap_supportOfVector n u w (hZ u hu) (hX w hw), dotPar_comm]
      exact hcross w hw u hu
    · obtain ⟨w, _, rfl⟩ := List.mem_map.mp k2
      cases hsec

/-- The displayed rows of the two sectors of a well-formed state, as
    matrices, have pairwise even overlap. -/
theorem sectorMatrix_commute (s : CodeState) (hwf : EncodingWellFormed s) :
    MatricesCommute s.Q.length (sectorMatrix s Sector.X) (sectorMatrix s Sector.Z) := by
  intro x z hx hz
  have hmemX : (sectorMatrix s Sector.X).getD x [] ∈ sectorMatrix s Sector.X := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx]
    exact List.getElem_mem hx
  have hmemZ : (sectorMatrix s Sector.Z).getD z [] ∈ sectorMatrix s Sector.Z := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hz]
    exact List.getElem_mem hz
  unfold sectorMatrix at hmemX hmemZ
  obtain ⟨rx, hrx, hvx⟩ := List.mem_map.mp hmemX
  obtain ⟨rz, hrz, hvz⟩ := List.mem_map.mp hmemZ
  have hrx' := List.mem_filter.mp hrx
  have hrz' := List.mem_filter.mp hrz
  have hsx : rx.sector = Sector.X := of_decide_eq_true hrx'.2
  have hsz : rz.sector = Sector.Z := of_decide_eq_true hrz'.2
  show ((List.range s.Q.length).filter (fun i =>
    ((sectorMatrix s Sector.X).getD x []).getD i false &&
      ((sectorMatrix s Sector.Z).getD z []).getD i false)).length % 2 = 0
  unfold sectorMatrix
  rw [← hvx, ← hvz, ← dotPar_map_map_gen]
  have hlx : s.Q.length = (rowVector s.Q rx).length := (rowVector_length s.Q rx).symm
  have hlz : s.Q.length = (rowVector s.Q rz).length := (rowVector_length s.Q rz).symm
  have h1 : (List.range s.Q.length).map (fun i => (rowVector s.Q rx).getD i false) =
      rowVector s.Q rx := by
    rw [hlx]
    exact map_getD_range _
  have h2 : (List.range s.Q.length).map (fun i => (rowVector s.Q rz).getD i false) =
      rowVector s.Q rz := by
    rw [hlz]
    exact map_getD_range _
  rw [h1, h2]
  exact dotPar_rowVector_even_of_wf hwf hrx'.1 hrz'.1 (by rw [hsz, hsx]; rfl)

/-- §4.35 for `A-PRODUCT`: the natural rows of the product of two
    well-formed states have pairwise even overlap across the sectors. -/
theorem product_naturalOrthogonal (A B : CodeState) (hA : EncodingWellFormed A)
    (hB : EncodingWellFormed B) :
    NaturalOrthogonal (naturalRows (productQubits A B) (productVectors A B)) :=
  naturalOrthogonal_of_cross _ _ _
    (length_productXVectors _ _ _ _ _ _) (length_productZVectors _ _ _ _ _ _)
    (product_cross _ _ _ _ _ _ (sectorMatrix_commute A hA) (sectorMatrix_commute B hB))

/-- The output of `A-PRODUCT` on two well-formed states is well-formed. -/
theorem wf_productState (A B : CodeState) (hA : EncodingWellFormed A)
    (hB : EncodingWellFormed B) : EncodingWellFormed (productState A B) :=
  wf_constructedState _ _ (product_naturalOrthogonal A B hA hB)

/-! ## Well-formedness -/

/-- `A-DOUBLE`: every evaluation yields a well-formed state. -/
theorem evalExpr_double_wf {e : StateExpr} {wiring : List (Nat × List Nat)} {conj : Bool}
    {s : CodeState} (h : EvalExpr (StateExpr.double e wiring conj) s) :
    EncodingWellFormed s := by
  cases h with
  | double _ _ hcomm _ _ =>
      exact wf_constructedState _ _ (naturalOrthogonal_of_commuteBool hcomm)

/-- `L-TANNER`: every evaluation yields a well-formed state. -/
theorem evalExpr_tanner_wf {n : Nat} {LX LZ : List (List Bool)}
    {viewsX viewsZ : List (List Nat)} {s : CodeState}
    (h : EvalExpr (StateExpr.tanner n LX LZ viewsX viewsZ) s) : EncodingWellFormed s := by
  cases h with
  | tanner _ hcomm _ =>
      exact wf_constructedState _ _ (naturalOrthogonal_of_commuteBool hcomm)

/-- `L-TILE`: every evaluation yields a well-formed state. -/
theorem evalExpr_tile_wf {tiles : List (Nat × List (List Nat) × List (List Nat))}
    {placements : List (Nat × List Nat)} {idents : List (Nat × Nat)}
    {removed : List (Nat × Sector × Nat)} {s : CodeState}
    (h : EvalExpr (StateExpr.tile tiles placements idents removed) s) :
    EncodingWellFormed s := by
  cases h with
  | tile _ hcomm _ =>
      exact wf_constructedState _ _ (naturalOrthogonal_of_commuteBool hcomm)

/-- `A-PRODUCT`: every evaluation at two factor states yields a well-formed
    state. -/
theorem evalExpr_product_wf {sA sB : CodeState} {s : CodeState}
    (h : EvalExpr (StateExpr.product (StateExpr.base sA) (StateExpr.base sB)) s) :
    EncodingWellFormed s := by
  cases h with
  | product hwfA hwfB _ hA hB =>
      cases hA
      cases hB
      exact wf_constructedState _ _ (product_naturalOrthogonal sA sB hwfA hwfB)

/-- `L-BALANCED`: well-formed output from the pairwise even overlap of the
    natural rows. -/
theorem evalExpr_balanced_wf {orders : List Nat} {H1 H2 : List (List Bool)}
    {rows1 cols1 rows2 cols2 : List (List Nat)} {s : CodeState}
    (h : EvalExpr (StateExpr.balanced orders H1 rows1 cols1 H2 rows2 cols2) s)
    (horth : NaturalOrthogonal
      (naturalRows (balancedQubits orders H1 rows1 cols1 H2 rows2 cols2)
        (balancedVectors orders H1 rows1 cols1 H2 rows2 cols2))) :
    EncodingWellFormed s := by
  cases h
  exact wf_constructedState _ _ horth

/-! ## The `n` of each card -/

/-- The `n` of an evaluation of `product(e_A, e_B)` at factor states `sA`
    and `sB`: `m_Z^A m_X^B + n_A n_B + m_X^A m_Z^B`. -/
theorem evalExpr_product_n {sA sB : CodeState} {s : CodeState}
    (h : EvalExpr (StateExpr.product (StateExpr.base sA) (StateExpr.base sB)) s) :
    s.Q.length =
      (sectorRows sA Sector.Z).length * (sectorRows sB Sector.X).length +
        sA.Q.length * sB.Q.length +
        (sectorRows sA Sector.X).length * (sectorRows sB Sector.Z).length := by
  cases h with
  | product _ _ _ hA hB =>
      cases hA
      cases hB
      show (constructedState _ _).Q.length = _
      rw [constructedState_n]
      unfold productQubits sectorMatrix sectorRows
      rw [List.length_map, List.length_map, List.length_map, List.length_map]

/-- The `n` of an evaluation of `double_{w,s}(C)`: `2 n_C`. -/
theorem evalExpr_double_n {sC : CodeState} {wiring : List (Nat × List Nat)} {conj : Bool}
    {s : CodeState} (h : EvalExpr (StateExpr.double (StateExpr.base sC) wiring conj) s) :
    s.Q.length = 2 * sC.Q.length := by
  cases h with
  | double _ _ _ _ hC =>
      cases hC
      exact constructedState_n _ _

/-- The `n` of an evaluation of `balanced_G(H₁, α₁; H₂, α₂)`: the number of
    orbits of the pairs of column indices plus the number of orbits of the
    pairs of row indices. -/
theorem evalExpr_balanced_n {orders : List Nat} {H1 H2 : List (List Bool)}
    {rows1 cols1 rows2 cols2 : List (List Nat)} {s : CodeState}
    (h : EvalExpr (StateExpr.balanced orders H1 rows1 cols1 H2 rows2 cols2) s) :
    s.Q.length =
      (orbitReps orders cols1 cols2 (matCols H1) (matCols H2)).length +
        (orbitReps orders rows1 rows2 H1.length H2.length).length := by
  cases h
  exact constructedState_n _ _

/-- The `n` of an evaluation of `tanner(n; Λ_X, Λ_Z; ι_X, ι_Z)`. -/
theorem evalExpr_tanner_n {n : Nat} {LX LZ : List (List Bool)}
    {viewsX viewsZ : List (List Nat)} {s : CodeState}
    (h : EvalExpr (StateExpr.tanner n LX LZ viewsX viewsZ) s) : s.Q.length = n := by
  cases h
  exact constructedState_n _ _

/-- The `n` of an evaluation of `tile(τ; α; β)`: the number of site
    classes. -/
theorem evalExpr_tile_n {tiles : List (Nat × List (List Nat) × List (List Nat))}
    {placements : List (Nat × List Nat)} {idents : List (Nat × Nat)}
    {removed : List (Nat × Sector × Nat)} {s : CodeState}
    (h : EvalExpr (StateExpr.tile tiles placements idents removed) s) :
    s.Q.length = (tileClasses placements idents).length := by
  cases h
  exact constructedState_n _ _

/-- `L-NESTED-CSS`: every evaluation yields a well-formed state. -/
theorem evalExpr_nested_wf {HX HZ : List (List Bool)} {s : CodeState}
    (h : EvalExpr (StateExpr.nested HX HZ) s) : EncodingWellFormed s := by
  cases h with
  | nested _ hcomm _ =>
      exact wf_constructedState _ _ (naturalOrthogonal_of_commuteBool hcomm)

/-- The `n` of an evaluation of `nested(H_X, H_Z)`: the number of columns. -/
theorem evalExpr_nested_n {HX HZ : List (List Bool)} {s : CodeState}
    (h : EvalExpr (StateExpr.nested HX HZ) s) : s.Q.length = matCols HX := by
  cases h
  exact constructedState_n _ _

end CodeCalculus
