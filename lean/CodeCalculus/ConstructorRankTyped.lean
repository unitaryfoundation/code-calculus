import CodeCalculus.ConstructorRank
import CodeCalculus.ConstructorOverlap

/-!
# Closed forms for `k` of `L-GROUP-ALGEBRA` and `A-CONCAT` (issue #483)

`twoblockState_k_closed`: `k = 2(ℓ - rank[L(a) | L(b)])`, for every list of
cyclic orders and every pair of algebra elements. The `Z`-rows
`[L(b*) | L(a*)]` are the `X`-rows `[L(a) | L(b)]` with the two blocks
exchanged and the group elements negated, on the rows and on the columns, so
the two sectors have the same rank.

`concatState_k_of_retention`: `k = k_O` for `A-CONCAT`, under the hypothesis
that the display retains every natural row. That hypothesis is the
independence of the natural rows of each sector (issue #484), which is not
proved here.

The closed form for `L-HGP` is proved in `lean/extra/ClosedK.lean` from
the rank axioms `hgp_rankX`, `hgp_rankZ`, and `hgp_arith`; the closed
form for `A-PRODUCT` is proved there from `product_rankX`, `product_rankZ`,
and `product_arith`. Both need the rank of a tensor-product matrix, which
the mask-list rank lemmas of `ConstructorRank.lean` do not give.
-/

namespace CodeCalculus

/-! ## Positions in a list -/

/-- The first position of `a` in `l`, the length of `l` when absent. -/
def posOf {α : Type} [DecidableEq α] (a : α) : List α → Nat
  | [] => 0
  | x :: xs => if x = a then 0 else posOf a xs + 1

theorem posOf_lt {α : Type} [DecidableEq α] (a : α) : ∀ (l : List α), a ∈ l →
    posOf a l < l.length
  | [], h => nomatch h
  | x :: xs, h => by
      unfold posOf
      split
      · exact Nat.succ_pos _
      · rename_i hne
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hne
        · exact Nat.succ_lt_succ (posOf_lt a xs h)

theorem getD_posOf {α : Type} [DecidableEq α] (a d : α) : ∀ (l : List α), a ∈ l →
    l.getD (posOf a l) d = a
  | [], h => nomatch h
  | x :: xs, h => by
      unfold posOf
      split
      · rename_i heq
        exact heq
      · rename_i hne
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hne
        · exact getD_posOf a d xs h

theorem posOf_getD {α : Type} [DecidableEq α] (d : α) : ∀ (l : List α), l.Nodup →
    ∀ i, i < l.length → posOf (l.getD i d) l = i
  | [], _, _, h => nomatch h
  | x :: xs, hnd, 0, _ => by
      show (if x = x then 0 else _) = 0
      split
      · rfl
      · rename_i h
        exact absurd rfl h
  | x :: xs, hnd, i + 1, h => by
      have hnd' := List.nodup_cons.mp hnd
      have hi : i < xs.length := Nat.lt_of_succ_lt_succ h
      show (if x = xs.getD i d then 0 else posOf (xs.getD i d) xs + 1) = i + 1
      have hne : ¬ x = xs.getD i d := fun heq => hnd'.1 (heq ▸ getD_mem d xs i hi)
      split
      · rename_i h
        exact absurd h hne
      · rw [posOf_getD d xs hnd'.2 i hi]

/-! ## Negation in the group -/

/-- `-x` modulo `o`, written with `subm`. -/
def negm (o x : Nat) : Nat := subm o (subm o x x) x

theorem negm_eq {o x : Nat} (hx : x < o) : negm o x = if x = 0 then 0 else o - x := by
  unfold negm
  have h0 : subm o x x = 0 := by
    rw [subm_eq hx hx]
    split <;> omega
  rw [h0, subm_eq (by omega) hx]
  split <;> split <;> omega

theorem negm_lt {o x : Nat} (hx : x < o) : negm o x < o := by
  rw [negm_eq hx]
  split <;> omega

theorem negm_negm {o x : Nat} (hx : x < o) : negm o (negm o x) = x := by
  rw [negm_eq (negm_lt hx), negm_eq hx]
  split <;> split <;> omega

theorem subm_negm_negm {o x y : Nat} (hx : x < o) (hy : y < o) :
    subm o (negm o x) (negm o y) = subm o y x := by
  rw [subm_eq (negm_lt hx) (negm_lt hy), subm_eq hy hx, negm_eq hx, negm_eq hy]
  split <;> split <;> split <;> split <;> omega

/-- The inverse of a group element, written with `groupSub`. -/
def gneg (os g : List Nat) : List Nat := groupSub os (groupSub os g g) g

theorem gneg_cons (o : Nat) (os : List Nat) (x : Nat) (xs : List Nat) :
    gneg (o :: os) (x :: xs) = negm o x :: gneg os xs := rfl

theorem inGroup_gneg (os g : List Nat) (hg : InGroup os g) : InGroup os (gneg os g) :=
  inGroup_sub os _ g (inGroup_sub os g g hg hg) hg

theorem gneg_gneg : ∀ (os g : List Nat), InGroup os g → gneg os (gneg os g) = g
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | o :: os, x :: xs, h => by
      rw [gneg_cons, gneg_cons, negm_negm h.1, gneg_gneg os xs h.2]

theorem groupSub_gneg_gneg : ∀ (os u v : List Nat), InGroup os u → InGroup os v →
    groupSub os (gneg os u) (gneg os v) = groupSub os v u
  | [], [], [], _, _ => rfl
  | [], [], _ :: _, _, h => nomatch h
  | [], _ :: _, _, h, _ => nomatch h
  | _ :: _, [], _, h, _ => nomatch h
  | _ :: _, _ :: _, [], _, h => nomatch h
  | o :: os, x :: xs, y :: ys, hu, hv => by
      rw [gneg_cons, gneg_cons, groupSub_cons, groupSub_cons, subm_negm_negm hu.1 hv.1,
        groupSub_gneg_gneg os xs ys hu.2 hv.2]

/-! ## Masks from boolean rows -/

/-- Turn a row of booleans into the bitmask used by `rankBitmasks`. -/
def boolsToMask : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * boolsToMask bs

theorem testBit_boolsToMask : ∀ (v : List Bool) (i : Nat),
    (boolsToMask v).testBit i = v.getD i false
  | [], i => by
      show (0 : Nat).testBit i = false
      exact testBit_zero_all i
  | b :: bs, 0 => by
      show ((if b then 1 else 0) + 2 * boolsToMask bs).testBit 0 = b
      rw [Nat.testBit_zero]
      cases b
      · show decide ((0 + 2 * boolsToMask bs) % 2 = 1) = false
        exact decide_eq_false (by omega)
      · show decide ((1 + 2 * boolsToMask bs) % 2 = 1) = true
        exact decide_eq_true (by omega)
  | b :: bs, i + 1 => by
      show ((if b then 1 else 0) + 2 * boolsToMask bs).testBit (i + 1) = bs.getD i false
      rw [Nat.testBit_succ, ← testBit_boolsToMask bs i]
      congr 1
      cases b
      · show (0 + 2 * boolsToMask bs) / 2 = boolsToMask bs
        omega
      · show (1 + 2 * boolsToMask bs) / 2 = boolsToMask bs
        omega

/-- On a vector of length `n`, the mask over `0, …, n - 1` is `boolsToMask`. -/
theorem vecMask_eq_boolsToMask (n : Nat) (v : List Bool) (h : v.length = n) :
    vecMask n v = boolsToMask v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_vecMask, testBit_boolsToMask]
  cases Nat.lt_or_ge i n with
  | inl hlt => rw [decide_eq_true hlt, Bool.true_and]
  | inr hge =>
      rw [decide_eq_false (Nat.not_lt.mpr hge), Bool.false_and, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by rw [h]; exact hge)]
      rfl

/-! ## Natural masks of two tagged families -/

theorem filter_tagged_same {α : Type} (σ : Sector) (F : α → List Bool) : ∀ L : List α,
    (L.map (fun h => (σ, F h))).filter (fun x => x.1 = σ) = L.map (fun h => (σ, F h))
  | [] => rfl
  | x :: L => by
      rw [List.map_cons, List.filter_cons_of_pos (by exact decide_eq_true rfl),
        filter_tagged_same σ F L]

theorem filter_tagged_other {α : Type} (σ τ : Sector) (hne : σ ≠ τ) (F : α → List Bool) :
    ∀ L : List α, (L.map (fun h => (σ, F h))).filter (fun x => x.1 = τ) = []
  | [] => rfl
  | x :: L => by
      rw [List.map_cons, List.filter_cons_of_neg (by
        rw [Bool.not_eq_true]; exact decide_eq_false hne), filter_tagged_other σ τ hne F L]

/-- The natural masks of `X`-rows followed by `Z`-rows, sector by sector. -/
theorem naturalMasks_XZ {α β : Type} (n : Nat) (F : α → List Bool) (G : β → List Bool)
    (L : List α) (M : List β) :
    naturalMasks n (L.map (fun h => (Sector.X, F h)) ++ M.map (fun h => (Sector.Z, G h)))
        Sector.X = L.map (fun h => vecMask n (F h)) ∧
    naturalMasks n (L.map (fun h => (Sector.X, F h)) ++ M.map (fun h => (Sector.Z, G h)))
        Sector.Z = M.map (fun h => vecMask n (G h)) := by
  unfold naturalMasks
  rw [List.filter_append, List.filter_append, filter_tagged_same, filter_tagged_same,
    filter_tagged_other Sector.Z Sector.X (by decide),
    filter_tagged_other Sector.X Sector.Z (by decide), List.append_nil, List.nil_append,
    List.map_map, List.map_map]
  exact ⟨rfl, rfl⟩

/-! ## `L-GROUP-ALGEBRA` -/

theorem getD_append_lt (u w : List Bool) (i : Nat) (h : i < u.length) :
    (u ++ w).getD i false = u.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

theorem getD_append_ge (u w : List Bool) (i : Nat) (h : u.length ≤ i) :
    (u ++ w).getD i false = w.getD (i - u.length) false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h, ← List.getD_eq_getElem?_getD]

theorem getD_regRow (os : List Nat) (x : List (List Nat)) (h : List Nat) (i : Nat)
    (hi : i < (groupElements os).length) :
    (regRow os x h).getD i false =
      algCoeff os x (groupSub os h ((groupElements os).getD i [])) := by
  unfold regRow
  exact getD_map_lt _ [] false (groupElements os) i hi

theorem gneg_mem (os g : List Nat) (hg : g ∈ groupElements os) :
    gneg os g ∈ groupElements os :=
  (mem_groupElements os _).mpr (inGroup_gneg os g ((mem_groupElements os g).mp hg))

/-- The column permutation: exchange the two blocks and negate the group
    element. -/
def swapNegIdx (os : List Nat) (i : Nat) : Nat :=
  if i < (groupElements os).length then
    (groupElements os).length +
      posOf (gneg os ((groupElements os).getD i [])) (groupElements os)
  else posOf (gneg os ((groupElements os).getD (i - (groupElements os).length) []))
    (groupElements os)

theorem swapNegIdx_lt (os : List Nat) (i : Nat) (hi : i < (groupElements os).length) :
    swapNegIdx os i = (groupElements os).length +
      posOf (gneg os ((groupElements os).getD i [])) (groupElements os) := by
  unfold swapNegIdx
  split
  · rfl
  · rename_i h
    exact absurd hi h

theorem swapNegIdx_ge (os : List Nat) (i : Nat) (hi : (groupElements os).length ≤ i) :
    swapNegIdx os i =
      posOf (gneg os ((groupElements os).getD (i - (groupElements os).length) []))
        (groupElements os) := by
  unfold swapNegIdx
  split
  · rename_i h
    exact absurd h (Nat.not_lt.mpr hi)
  · rfl

/-- The column permutation on masks over the `2ℓ` labels. -/
def swapNeg (os : List Nat) (m : Nat) : Nat :=
  vecMask (2 * (groupElements os).length)
    ((List.range (2 * (groupElements os).length)).map (fun i => m.testBit (swapNegIdx os i)))

theorem testBit_swapNeg (os : List Nat) (m i : Nat) :
    (swapNeg os m).testBit i =
      (decide (i < 2 * (groupElements os).length) && m.testBit (swapNegIdx os i)) := by
  unfold swapNeg
  rw [testBit_vecMask]
  cases Nat.lt_or_ge i (2 * (groupElements os).length) with
  | inl hlt =>
      rw [getD_map_lt _ 0 false _ i (by rw [List.length_range]; exact hlt),
        List.getD_eq_getElem?_getD, List.getElem?_range hlt]
      rfl
  | inr hge => rw [decide_eq_false (Nat.not_lt.mpr hge), Bool.false_and, Bool.false_and]

theorem swapNeg_xor (os : List Nat) (a b : Nat) :
    swapNeg os (a ^^^ b) = swapNeg os a ^^^ swapNeg os b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_swapNeg, Nat.testBit_xor, Nat.testBit_xor, testBit_swapNeg, testBit_swapNeg]
  cases decide (i < 2 * (groupElements os).length) <;> rfl

/-- Every label below `2ℓ` is the image of a label below `2ℓ`. -/
theorem swapNegIdx_surj (os : List Nat) (j : Nat) (hj : j < 2 * (groupElements os).length) :
    ∃ i, i < 2 * (groupElements os).length ∧ swapNegIdx os i = j := by
  have hnd := nodup_groupElements os
  cases Nat.lt_or_ge j (groupElements os).length with
  | inl hlt =>
      have hg := getD_mem [] (groupElements os) j hlt
      have hp := posOf_lt _ _ (gneg_mem os _ hg)
      refine ⟨(groupElements os).length +
        posOf (gneg os ((groupElements os).getD j [])) (groupElements os), by omega, ?_⟩
      rw [swapNegIdx_ge os _ (by omega), Nat.add_sub_cancel_left,
        getD_posOf _ [] _ (gneg_mem os _ hg),
        gneg_gneg os _ ((mem_groupElements os _).mp hg), posOf_getD [] _ hnd j hlt]
  | inr hge =>
      have hlt : j - (groupElements os).length < (groupElements os).length := by omega
      have hg := getD_mem [] (groupElements os) _ hlt
      have hp := posOf_lt _ _ (gneg_mem os _ hg)
      refine ⟨posOf (gneg os ((groupElements os).getD (j - (groupElements os).length) []))
        (groupElements os), by omega, ?_⟩
      rw [swapNegIdx_lt os _ hp, getD_posOf _ [] _ (gneg_mem os _ hg),
        gneg_gneg os _ ((mem_groupElements os _).mp hg), posOf_getD [] _ hnd _ hlt]
      omega

theorem eq_zero_of_swapNeg_eq_zero (os : List Nat) (m : Nat)
    (hhigh : ∀ j, 2 * (groupElements os).length ≤ j → m.testBit j = false)
    (h : swapNeg os m = 0) : m = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_zero_all]
  cases Nat.lt_or_ge j (2 * (groupElements os).length) with
  | inl hlt =>
      obtain ⟨i, hi, rfl⟩ := swapNegIdx_surj os j hlt
      have hb : (swapNeg os m).testBit i = false := by rw [h, testBit_zero_all]
      rw [testBit_swapNeg, decide_eq_true hi, Bool.true_and] at hb
      exact hb
  | inr hge => exact hhigh j hge

/-- The `Z`-row at `h` is the `X`-row at `-h` under the column permutation. -/
theorem twoblock_Z_eq_swapNeg (os : List Nat) (a b : List (List Nat)) (h : List Nat)
    (hh : h ∈ groupElements os) :
    vecMask (2 * (groupElements os).length)
        (regRow os (algInv os b) h ++ regRow os (algInv os a) h) =
      swapNeg os (vecMask (2 * (groupElements os).length)
        (regRow os a (gneg os h) ++ regRow os b (gneg os h))) := by
  have hhG := (mem_groupElements os h).mp hh
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_vecMask, testBit_swapNeg, testBit_vecMask]
  cases Nat.lt_or_ge i (2 * (groupElements os).length) with
  | inr hge => rw [decide_eq_false (Nat.not_lt.mpr hge), Bool.false_and, Bool.false_and]
  | inl hlt =>
      rw [decide_eq_true hlt, Bool.true_and, Bool.true_and]
      cases Nat.lt_or_ge i (groupElements os).length with
      | inl hi =>
          have hg := getD_mem [] (groupElements os) i hi
          have hgG := (mem_groupElements os _).mp hg
          have hp := posOf_lt _ _ (gneg_mem os _ hg)
          have hidx : swapNegIdx os i = (groupElements os).length +
              posOf (gneg os ((groupElements os).getD i [])) (groupElements os) :=
            swapNegIdx_lt os i hi
          rw [hidx, decide_eq_true (show _ < 2 * (groupElements os).length by omega),
            Bool.true_and,
            getD_append_lt _ _ i (by rw [length_regRow]; exact hi),
            getD_append_ge _ _ _ (by rw [length_regRow]; omega),
            length_regRow, Nat.add_sub_cancel_left,
            getD_regRow os _ h i hi, getD_regRow os _ _ _ hp,
            getD_posOf _ [] _ (gneg_mem os _ hg),
            algCoeff_inv os b h _ hhG hgG, groupSub_gneg_gneg os h _ hhG hgG]
      | inr hi =>
          have hi' : i - (groupElements os).length < (groupElements os).length := by omega
          have hg := getD_mem [] (groupElements os) _ hi'
          have hgG := (mem_groupElements os _).mp hg
          have hp := posOf_lt _ _ (gneg_mem os _ hg)
          have hidx : swapNegIdx os i =
              posOf (gneg os ((groupElements os).getD (i - (groupElements os).length) []))
                (groupElements os) :=
            swapNegIdx_ge os i hi
          rw [hidx, decide_eq_true (show _ < 2 * (groupElements os).length by omega),
            Bool.true_and,
            getD_append_ge _ _ i (by rw [length_regRow]; exact hi),
            getD_append_lt _ _ _ (by rw [length_regRow]; exact hp),
            length_regRow,
            getD_regRow os _ h _ hi', getD_regRow os _ _ _ hp,
            getD_posOf _ [] _ (gneg_mem os _ hg),
            algCoeff_inv os a h _ hhG hgG, groupSub_gneg_gneg os h _ hhG hgG]

/-- The two sectors of `twoblock_G(a, b)` have the same rank. -/
theorem twoblock_rank_Z (os : List Nat) (a b : List (List Nat)) :
    rankBitmasks ((groupElements os).map (fun h => vecMask (2 * (groupElements os).length)
        (regRow os (algInv os b) h ++ regRow os (algInv os a) h))) =
      rankBitmasks ((groupElements os).map (fun h => vecMask (2 * (groupElements os).length)
        (regRow os a h ++ regRow os b h))) := by
  have hspan := span_eq_of_mem
    (xs := (groupElements os).map (fun h => vecMask (2 * (groupElements os).length)
        (regRow os (algInv os b) h ++ regRow os (algInv os a) h)))
    (ys := ((groupElements os).map (fun h => vecMask (2 * (groupElements os).length)
        (regRow os a h ++ regRow os b h))).map (swapNeg os))
    (by
      intro z hz
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hz
      rw [twoblock_Z_eq_swapNeg os a b h hh]
      exact inSpanMasks_of_mem (List.mem_map.mpr ⟨_,
        List.mem_map.mpr ⟨gneg os h, gneg_mem os h hh, rfl⟩, rfl⟩))
    (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
      have hA := twoblock_Z_eq_swapNeg os a b (gneg os h) (gneg_mem os h hh)
      rw [gneg_gneg os h ((mem_groupElements os h).mp hh)] at hA
      rw [← hA]
      exact inSpanMasks_of_mem (List.mem_map.mpr ⟨gneg os h, gneg_mem os h hh, rfl⟩))
  rw [rankBitmasks_eq_of_span_eq hspan, rankBitmasks_map (swapNeg os) (swapNeg_xor os)]
  intro m hm hzero
  refine eq_zero_of_swapNeg_eq_zero os m (fun j hj => ?_) hzero
  refine testBit_false_of_inSpan (fun x hx => ?_) hm
  obtain ⟨h, _, rfl⟩ := List.mem_map.mp hx
  rw [testBit_vecMask, decide_eq_false (Nat.not_lt.mpr hj), Bool.false_and]

/-- The row bitmask of one natural row of `twoblock_G(a, b)`. -/
def twoblockRowMask (orders : List Nat) (a b : List (List Nat)) (h : List Nat) : Nat :=
  boolsToMask (regRow orders a h ++ regRow orders b h)

theorem twoblockVectors_eq (os : List Nat) (a b : List (List Nat)) :
    twoblockVectors os a b =
      (groupElements os).map (fun h => (Sector.X, regRow os a h ++ regRow os b h)) ++
      (groupElements os).map (fun h => (Sector.Z,
        regRow os (algInv os b) h ++ regRow os (algInv os a) h)) := rfl

/-- §4.34: `k = 2(ℓ - rank[L(a) | L(b)])`, for every list of cyclic orders
    and every pair of algebra elements. No typing premise is used. -/
theorem twoblockState_k_closed (orders : List Nat) (a b : List (List Nat)) :
    stateK (twoblockState orders a b) =
      2 * ((groupElements orders).length -
        rankBitmasks ((groupElements orders).map (twoblockRowMask orders a b))) := by
  unfold twoblockState
  rw [stateK_constructedState, twoblockVectors_eq]
  obtain ⟨hX, hZ⟩ := naturalMasks_XZ (twoblockQubits orders)
    (fun h => regRow orders a h ++ regRow orders b h)
    (fun h => regRow orders (algInv orders b) h ++ regRow orders (algInv orders a) h)
    (groupElements orders) (groupElements orders)
  rw [hX, hZ]
  unfold twoblockQubits
  rw [twoblock_rank_Z]
  have hmask : (groupElements orders).map (fun h => vecMask (2 * (groupElements orders).length)
      (regRow orders a h ++ regRow orders b h)) =
      (groupElements orders).map (twoblockRowMask orders a b) :=
    List.map_congr_left (fun h _ => vecMask_eq_boolsToMask _ _ (by
      rw [List.length_append, length_regRow, length_regRow]; omega))
  rw [hmask]
  omega

/-- `L-GROUP-ALGEBRA`: the evaluated state has `k = 2(ℓ - rank[L(a) | L(b)])`. -/
theorem evalExpr_twoblock_k {orders : List Nat} {a b : List (List Nat)} {s : CodeState}
    (h : EvalExpr (StateExpr.twoblock orders a b) s) :
    stateK s =
      2 * ((groupElements orders).length -
        rankBitmasks ((groupElements orders).map (twoblockRowMask orders a b))) := by
  cases h with
  | twoblock _ _ _ _ => exact twoblockState_k_closed orders a b

/-! ## `A-CONCAT`, conditional on the display retaining every natural row -/

theorem length_sectorRows_add (s : CodeState) :
    (sectorRows s Sector.X).length + (sectorRows s Sector.Z).length = s.rows.length := by
  unfold sectorRows
  induction s.rows with
  | nil => rfl
  | cons r rs ih =>
      cases hs : r.sector with
      | X =>
          rw [List.filter_cons_of_pos (by rw [hs]; exact decide_eq_true rfl),
            List.filter_cons_of_neg (by rw [hs]; decide), List.length_cons, List.length_cons]
          omega
      | Z =>
          rw [List.filter_cons_of_neg (by rw [hs]; decide),
            List.filter_cons_of_pos (by rw [hs]; exact decide_eq_true rfl),
            List.length_cons, List.length_cons]
          omega

/-- On a well-formed state, `k` is `n` minus the number of displayed rows. -/
theorem stateK_of_wf_rows (s : CodeState) (hwf : EncodingWellFormed s) :
    stateK s = s.Q.length - s.rows.length := by
  rw [stateK_of_wf s hwf, ← length_sectorRows_add s]
  omega

theorem length_flatMap_map {α β γ : Type} (F : α → β → γ) (M : List β) : ∀ L : List α,
    (L.flatMap (fun j => M.map (F j))).length = L.length * M.length
  | [] => by rw [List.flatMap_nil, List.length_nil, List.length_nil, Nat.zero_mul]
  | x :: L => by
      rw [List.flatMap_cons, List.length_append, List.length_map, length_flatMap_map F M L,
        List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem length_flatten_const {α : Type} (k : Nat) : ∀ L : List (List α),
    (∀ B ∈ L, B.length = k) → L.flatten.length = L.length * k
  | [], _ => by rw [List.flatten_nil, List.length_nil, List.length_nil, Nat.zero_mul]
  | B :: L, h => by
      rw [List.flatten_cons, List.length_append, h B (List.mem_cons_self ..),
        length_flatten_const k L (fun B' hB' => h B' (List.mem_cons_of_mem _ hB')),
        List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- The number of natural rows of `concat`: every inner row on every copy,
    and every outer row. -/
theorem length_concatVectors (O I : CodeState) (blocks repsX repsZ : List (List Nat)) :
    (concatVectors O I blocks repsX repsZ).length =
      blocks.length * I.rows.length + O.rows.length := by
  rw [concatVectors_eq, List.length_append, List.length_map,
    length_flatMap_map (fun j r => (r.sector, concatInner I blocks.length j r)),
    List.length_range]

/-- §4.34, the count for `A-CONCAT`: when the display retains every natural
    row, `k = k_O`. The hypothesis is the statement that the natural rows of
    each sector are independent, which this module does not prove. -/
theorem concatState_k_of_retention (O I : CodeState) (blocks repsX repsZ : List (List Nat))
    (hO : EncodingWellFormed O) (hI : EncodingWellFormed I)
    (hty : concatTyped O I blocks repsX repsZ = true)
    (hret : (concatState O I blocks repsX repsZ).rows.length =
      (concatVectors O I blocks repsX repsZ).length) :
    stateK (concatState O I blocks repsX repsZ) = stateK O := by
  have hwf := wf_concatState O I blocks repsX repsZ hO hI hty
  rw [stateK_of_wf_rows _ hwf, stateK_of_wf_rows O hO, hret, concatState_n,
    length_concatVectors]
  simp only [concatTyped, Bool.and_eq_true] at hty
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, t3⟩, t4⟩, t5⟩, t6⟩, t7⟩, _⟩, _⟩, _⟩, _⟩ := hty
  have hn : I.Q.length = I.rows.length + repsX.length := Nat.eq_of_beq_eq_true t3
  have hB : ∀ B ∈ blocks, B.length = repsX.length :=
    fun B hBm => Nat.eq_of_beq_eq_true (List.all_eq_true.mp t4 B hBm)
  have hnd : blocks.flatten.Nodup := of_decide_eq_true t5
  have hsub1 : ∀ q ∈ blocks.flatten, q ∈ O.Q :=
    fun q hq => List.contains_iff_mem.mp (List.all_eq_true.mp t6 q hq)
  have hsub2 : ∀ q ∈ O.Q, q ∈ blocks.flatten :=
    fun q hq => List.contains_iff_mem.mp (List.all_eq_true.mp t7 q hq)
  have hlen : blocks.length * repsX.length = O.Q.length := by
    rw [← length_flatten_const repsX.length blocks hB]
    exact Nat.le_antisymm (length_le_of_nodup_subset_gen _ _ hnd hO.1 hsub1)
      (length_le_of_nodup_subset_gen _ _ hO.1 hnd hsub2)
  rw [hn, Nat.mul_comm, Nat.mul_add, hlen]
  omega

end CodeCalculus
