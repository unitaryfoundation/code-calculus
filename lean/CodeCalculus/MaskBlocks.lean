import CodeCalculus.HgpRank

/-!
# Masks of lists over index pairs, and block layouts

Bit-level identifications used by the closed forms for `k` of `L-HGP` and
`A-PRODUCT`: the mask of a Boolean list over `indexPairs` is a
`maskFn`, the natural rows are tensors with unit masks, and the two
placements of a pair of blocks are `HgLayout`s.
-/

namespace CodeCalculus

/-! ## Masks of lists over index pairs -/

theorem below_boolsToMask (v : List Bool) : Below v.length (boolsToMask v) := by
  intro j hj
  rw [testBit_boolsToMask, List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]
  rfl

theorem boolsToMask_append (u w : List Bool) :
    boolsToMask (u ++ w) = boolsToMask u ^^^ (boolsToMask w <<< u.length) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft, testBit_boolsToMask, testBit_boolsToMask,
    testBit_boolsToMask]
  rcases Nat.lt_or_ge i u.length with h | h
  · rw [getD_append_lt u w i h, decide_eq_false (Nat.not_le_of_lt h), Bool.false_and,
      Bool.xor_false]
  · rw [getD_append_ge u w i h, decide_eq_true h, Bool.true_and,
      List.getD_eq_getElem?_getD (l := u), List.getElem?_eq_none h]
    exact (Bool.false_xor _).symm

theorem indexPairs_succ (m n : Nat) :
    indexPairs (m + 1) n = indexPairs m n ++ (List.range n).map (fun b => (m, b)) := by
  unfold indexPairs
  rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem getElem?_indexPairs : ∀ (m n k : Nat), k < m * n →
    (indexPairs m n)[k]? = some (k / n, k % n)
  | 0, n, k, h => by
      rw [Nat.zero_mul] at h
      exact absurd h (Nat.not_lt_zero k)
  | m + 1, n, k, h => by
      rw [indexPairs_succ]
      rw [Nat.succ_mul] at h
      rcases Nat.lt_or_ge k (m * n) with hk | hk
      · rw [List.getElem?_append_left (by rw [length_indexPairs]; exact hk)]
        exact getElem?_indexPairs m n k hk
      · have hlt : k - m * n < n := by omega
        have hk' : m * n + (k - m * n) = k := by omega
        have hd := mul_add_div m n (k - m * n) hlt
        have hm := mul_add_mod m n (k - m * n) hlt
        rw [hk'] at hd hm
        rw [List.getElem?_append_right (by rw [length_indexPairs]; exact hk),
          length_indexPairs, List.getElem?_map, List.getElem?_range hlt, hd, hm]
        rfl

theorem boolsToMask_map_indexPairs (m n : Nat) (f : Nat × Nat → Bool) :
    boolsToMask ((indexPairs m n).map f) = maskFn (m * n) (fun k => f (k / n, k % n)) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_boolsToMask, testBit_maskFn, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases Nat.lt_or_ge k (m * n) with h | h
  · rw [getElem?_indexPairs m n k h, decide_eq_true h]
    rfl
  · rw [List.getElem?_eq_none (by rw [length_indexPairs]; exact h),
      decide_eq_false (Nat.not_lt_of_le h)]
    rfl

theorem decide_eq_swap (a b : Nat) : decide (a = b) = decide (b = a) := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · rw [decide_eq_false (Nat.ne_of_lt h), decide_eq_false (Nat.ne_of_gt h)]
  · rw [decide_eq_true h, decide_eq_true h.symm]
  · rw [decide_eq_false (Nat.ne_of_gt h), decide_eq_false (Nat.ne_of_lt h)]

/-- The mask of the tensor of `x` with a unit mask. -/
theorem maskFn_tens_unit_right (p q j x : Nat) (hj : j < q) :
    maskFn (p * q) (fun k => decide (k % q = j) && x.testBit (k / q)) =
      tens p q x (2 ^ j) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_maskFn, testBit_tens p q x (2 ^ j) k (below_two_pow hj), Nat.testBit_two_pow,
    decide_eq_swap j (k % q), Bool.and_comm (decide (k % q = j))]

/-- The mask of the tensor of a unit mask with `y`. -/
theorem maskFn_tens_unit_left (p q i y : Nat) (hy : Below q y) :
    maskFn (p * q) (fun k => decide (k / q = i) && y.testBit (k % q)) =
      tens p q (2 ^ i) y := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_maskFn, testBit_tens p q (2 ^ i) y k hy, Nat.testBit_two_pow,
    decide_eq_swap i (k / q)]

/-! ## Rows and columns of a binary matrix as masks -/

theorem getD_map_boolsToMask : ∀ (H : List (List Bool)) (a : Nat),
    (H.map boolsToMask).getD a 0 = boolsToMask (H.getD a [])
  | [], a => by
      rw [List.map_nil, List.getD_nil, List.getD_nil]
      rfl
  | r :: H, 0 => by rw [List.map_cons, List.getD_cons_zero, List.getD_cons_zero]
  | r :: H, a + 1 => by
      rw [List.map_cons, List.getD_cons_succ, List.getD_cons_succ]
      exact getD_map_boolsToMask H a

theorem testBit_rowMask (H : List (List Bool)) (a i : Nat) :
    ((H.map boolsToMask).getD a 0).testBit i = matEntry H a i := by
  rw [getD_map_boolsToMask, testBit_boolsToMask]
  rfl

theorem testBit_colMask_rows (H : List (List Bool)) (j b : Nat) :
    (colMask (H.map boolsToMask) j).testBit b = matEntry H b j := by
  rw [testBit_colMask, testBit_rowMask]

theorem below_colMask (R : List Nat) (j : Nat) : Below R.length (colMask R j) := by
  intro i hi
  rw [testBit_colMask, List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  exact Nat.zero_testBit j

theorem length_colMasks (n : Nat) (R : List Nat) : (colMasks n R).length = n := by
  unfold colMasks
  rw [List.length_map, List.length_range]

theorem below_colMasks (n : Nat) (R : List Nat) : ∀ c ∈ colMasks n R, Below R.length c := by
  intro c hc
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
  exact below_colMask R j

/-! ## The two layouts of the blocks -/

theorem shiftLeft_mod_two_pow (y n : Nat) : (y <<< n) % 2 ^ n = 0 := by
  apply eq_zero_of_testBit
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  rcases Nat.lt_or_ge i n with h | h
  · rw [decide_eq_false (Nat.not_le_of_lt h), Bool.false_and, Bool.and_false]
  · rw [decide_eq_false (Nat.not_lt_of_le h), Bool.false_and]

theorem shiftRight_eq_zero_of_below {y n : Nat} (h : Below n y) : y >>> n = 0 := by
  apply eq_zero_of_testBit
  intro i
  rw [Nat.testBit_shiftRight]
  exact h _ (Nat.le_add_right _ _)

theorem below_mono {n m x : Nat} (h : n ≤ m) (hx : Below n x) : Below m x :=
  fun j hj => hx j (Nat.le_trans h hj)

theorem below_shiftLeft {n y : Nat} (m : Nat) (h : Below n y) : Below (m + n) (y <<< m) := by
  intro j hj
  rw [Nat.testBit_shiftLeft]
  rcases Nat.lt_or_ge j m with h1 | h1
  · rw [decide_eq_false (Nat.not_le_of_lt h1), Bool.false_and]
  · rw [h (j - m) (by omega), Bool.and_false]

/-- The first block in the low positions, the second above it. -/
theorem hgLayout_low (S T p q : Nat) :
    HgLayout id (· <<< (p * T)) (· % 2 ^ (p * T)) S T p q where
  lam_xor := fun _ _ => rfl
  rho_xor := fun a b => shiftLeft_xor (p * T) a b
  phi_xor := fun _ _ => Nat.xor_mod_two_pow
  phi_lam := fun x hx => Nat.mod_eq_of_lt (Nat.lt_pow_two_of_testBit x hx)
  phi_rho := fun y _ => shiftLeft_mod_two_pow y (p * T)
  rho_inj := fun y hy => eq_zero_of_shiftLeft_eq_zero (p * T) y hy

/-- The second block in the low positions, the first above it. -/
theorem hgLayout_high (S T p q : Nat) :
    HgLayout (· <<< (S * q)) id (· >>> (S * q)) S T p q where
  lam_xor := fun a b => shiftLeft_xor (S * q) a b
  rho_xor := fun _ _ => rfl
  phi_xor := fun _ _ => Nat.shiftRight_xor_distrib
  phi_lam := fun x _ => Nat.shiftLeft_shiftRight x (S * q)
  phi_rho := fun _ hy => shiftRight_eq_zero_of_below hy
  rho_inj := fun _ hy => hy

end CodeCalculus
