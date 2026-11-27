import CodeCalculus.MaskBlocks

/-!
# The rank of the natural rows of a tensor product of two complexes

`rank_prodRows` computes the rank of a family of two kinds of rows over a
middle block of `a * b` positions. A row of the first kind,
indexed by `(i, x)`, carries the tensor of the unit mask `i` with `Q_x` in
the middle block. A row of the second kind, indexed by `(x, j)`, carries
the tensor of `P_x` with the unit mask `j`. Each row also carries an extra
part outside the middle block. When `P` and `Q` are independent and the
extra parts cancel on the combinations that cancel in the middle block,
the rank is `a * |Q| + |P| * b - |P| * |Q|`.

The natural `X`-rows and the natural `Z`-rows of `A-PRODUCT` are two
instances.
-/

namespace CodeCalculus

/-! ## More on combinations -/

theorem comb_sel (xs : List Nat) (b : Bool) (c : Nat) :
    comb xs (sel b c) = sel b (comb xs c) := by
  cases b
  · exact comb_zero xs
  · rfl

theorem comb_snoc : ∀ (xs : List Nat) (c y : Nat),
    comb (xs ++ [c]) y = comb xs y ^^^ sel (y.testBit xs.length) c
  | [], c, y => by
      show sel (y.testBit 0) c ^^^ 0 = 0 ^^^ sel (y.testBit 0) c
      rw [Nat.xor_zero, Nat.zero_xor]
  | x :: xs, c, y => by
      show sel (y.testBit 0) x ^^^ comb (xs ++ [c]) (y >>> 1) =
        (sel (y.testBit 0) x ^^^ comb xs (y >>> 1)) ^^^ sel (y.testBit (xs.length + 1)) c
      rw [comb_snoc xs c (y >>> 1), Nat.testBit_shiftRight, Nat.xor_assoc, Nat.add_comm 1]

theorem comb_append_aux : ∀ (xs ys : List Nat) (c1 c2 : Nat), Below xs.length c1 →
    comb (xs ++ ys) (c1 ^^^ (c2 <<< xs.length)) = comb xs c1 ^^^ comb ys c2
  | [], ys, c1, c2, h => by
      rw [eq_zero_of_below_zero h]
      show comb ys (0 ^^^ (c2 <<< 0)) = 0 ^^^ comb ys c2
      rw [Nat.zero_xor, Nat.zero_xor, Nat.shiftLeft_zero]
  | x :: xs, ys, c1, c2, h => by
      show sel ((c1 ^^^ (c2 <<< (xs.length + 1))).testBit 0) x ^^^
          comb (xs ++ ys) ((c1 ^^^ (c2 <<< (xs.length + 1))) >>> 1) =
        (sel (c1.testBit 0) x ^^^ comb xs (c1 >>> 1)) ^^^ comb ys c2
      have hb : (c2 <<< (xs.length + 1)).testBit 0 = false := by
        rw [Nat.testBit_shiftLeft, decide_eq_false (by omega), Bool.false_and]
      have hs : (c2 <<< (xs.length + 1)) >>> 1 = c2 <<< xs.length := by
        rw [Nat.shiftLeft_add, Nat.shiftLeft_shiftRight]
      have hbelow : Below xs.length (c1 >>> 1) := by
        intro j hj
        rw [Nat.testBit_shiftRight]
        exact h (1 + j) (by show xs.length + 1 ≤ 1 + j; omega)
      rw [Nat.testBit_xor, hb, Bool.xor_false, Nat.shiftRight_xor_distrib, hs,
        comb_append_aux xs ys (c1 >>> 1) c2 hbelow, Nat.xor_assoc]

/-- The combination of an append by a coefficient mask in two parts. -/
theorem comb_append (n : Nat) (xs ys : List Nat) (c1 c2 : Nat) (hlen : xs.length = n)
    (h : Below n c1) : comb (xs ++ ys) (c1 ^^^ (c2 <<< n)) = comb xs c1 ^^^ comb ys c2 := by
  subst hlen
  exact comb_append_aux xs ys c1 c2 h

theorem comb_unitMasks : ∀ (n y : Nat), Below n y → comb (unitMasks n) y = y
  | 0, y, h => by
      rw [eq_zero_of_below_zero h]
      rfl
  | n + 1, y, h => by
      have hbelow : Below n (y >>> 1) := by
        intro j hj
        rw [Nat.testBit_shiftRight]
        exact h (1 + j) (by omega)
      rw [unitMasks_succ]
      show sel (y.testBit 0) 1 ^^^ comb ((unitMasks n).map (· <<< 1)) (y >>> 1) = y
      rw [comb_map_additive (· <<< 1) (shiftLeft_xor 1), comb_unitMasks n (y >>> 1) hbelow]
      exact (eq_sel_xor_shift y).symm

/-- The combination of the values of an additive map at the unit masks. -/
theorem comb_map_units (f : Nat → Nat) (hadd : ∀ a b, f (a ^^^ b) = f a ^^^ f b) (n y : Nat)
    (h : Below n y) : comb ((List.range n).map (fun i => f (2 ^ i))) y = f y := by
  have e : (List.range n).map (fun i => f (2 ^ i)) = (unitMasks n).map f := by
    unfold unitMasks
    rw [List.map_map]
    rfl
  rw [e, comb_map_additive f hadd, comb_unitMasks n y h]

theorem getD_map_range_lt {α : Type} (n : Nat) (f : Nat → α) (d : α) (i : Nat) (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

theorem indexPairs_cons (S T : Nat) :
    indexPairs (S + 1) T = (List.range T).map (fun t => (0, t)) ++
      (indexPairs S T).map (fun st => (st.1 + 1, st.2)) := by
  unfold indexPairs
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.map_flatMap]
  have e : (fun a => List.map (fun st : Nat × Nat => (st.1 + 1, st.2))
        (List.map (fun b => (a, b)) (List.range T))) =
      (fun a => List.map (fun b => (Nat.succ a, b)) (List.range T)) :=
    funext (fun a => by rw [List.map_map]; rfl)
  rw [e]

/-- The combination of a family over index pairs by the tensor of a
    coefficient mask with a unit mask. -/
theorem comb_indexPairs_right (T t : Nat) (ht : t < T) :
    ∀ (S : Nat) (g : Nat × Nat → Nat) (y : Nat),
      comb ((indexPairs S T).map g) (tens S T y (2 ^ t)) =
        comb ((List.range S).map (fun s => g (s, t))) y
  | 0, _, _ => rfl
  | S + 1, g, y => by
      rw [indexPairs_cons, List.map_append, List.map_map, List.map_map]
      show comb (_ ++ _) (sel (y.testBit 0) (2 ^ t) ^^^ (tens S T (y >>> 1) (2 ^ t) <<< T)) = _
      rw [comb_append T _ _ _ _ (by rw [List.length_map, List.length_range])
          (below_sel _ (below_two_pow ht)), comb_sel,
        comb_two_pow _ t (by rw [List.length_map, List.length_range]; exact ht),
        getD_map_range_lt T _ 0 t ht, comb_indexPairs_right T t ht S _ (y >>> 1),
        List.range_succ_eq_map, List.map_cons, List.map_map]
      rfl

/-- The combination of a family over index pairs by the tensor of a unit
    mask with a coefficient mask. -/
theorem comb_indexPairs_left (T z : Nat) (hz : Below T z) :
    ∀ (S : Nat) (g : Nat × Nat → Nat) (s : Nat), s < S →
      comb ((indexPairs S T).map g) (tens S T (2 ^ s) z) =
        comb ((List.range T).map (fun t => g (s, t))) z
  | 0, _, s, h => absurd h (Nat.not_lt_zero s)
  | S + 1, g, 0, _ => by
      rw [indexPairs_cons, List.map_append, List.map_map, List.map_map]
      show comb (_ ++ _) (sel ((2 ^ 0).testBit 0) z ^^^ (tens S T (2 ^ 0 >>> 1) z <<< T)) = _
      have h1 : (2 ^ 0 : Nat).testBit 0 = true := by decide
      have h2 : (2 ^ 0 : Nat) >>> 1 = 0 := by decide
      rw [h1, h2, tens_zero_left, sel_true,
        comb_append T _ _ _ _ (by rw [List.length_map, List.length_range]) hz, comb_zero,
        Nat.xor_zero]
      rfl
  | S + 1, g, s + 1, h => by
      rw [indexPairs_cons, List.map_append, List.map_map, List.map_map]
      show comb (_ ++ _)
        (sel ((2 ^ (s + 1)).testBit 0) z ^^^ (tens S T (2 ^ (s + 1) >>> 1) z <<< T)) = _
      have h1 : (2 ^ (s + 1) : Nat).testBit 0 = false := by
        rw [Nat.testBit_two_pow]
        exact decide_eq_false (Nat.succ_ne_zero s)
      rw [h1, two_pow_succ_shiftRight, sel_false,
        comb_append T _ _ 0 _ (by rw [List.length_map, List.length_range]) (below_zero T),
        comb_zero, Nat.zero_xor, comb_indexPairs_left T z hz S _ s (Nat.lt_of_succ_lt_succ h)]
      rfl

/-! ## Columns of appended lists and of families over index pairs -/

theorem colMask_append (xs ys : List Nat) (k : Nat) :
    colMask (xs ++ ys) k = colMask xs k ^^^ (colMask ys k <<< xs.length) := by
  unfold colMask
  rw [List.map_append, boolsToMask_append, List.length_map]

theorem colMask_map_indexPairs (S T : Nat) (g : Nat × Nat → Nat) (k : Nat) :
    colMask ((indexPairs S T).map g) k =
      maskFn (S * T) (fun r => (g (r / T, r % T)).testBit k) := by
  unfold colMask
  rw [List.map_map, boolsToMask_map_indexPairs]
  rfl

/-! ## Rank lemmas -/

theorem rankBitmasks_map_le_additive (f : Nat → Nat) (hadd : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    (L : List Nat) : rankBitmasks (L.map f) ≤ rankBitmasks L := by
  have h1 : rankBitmasks (L.map f) ≤ rankBitmasks ((basisOf L).map f) := by
    apply rankBitmasks_le_of_span
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact (inSpanMasks_map_additive_iff f hadd (basisOf L) _).mpr
      ⟨x, (basisOf_span L x).mpr (inSpanMasks_of_mem hx), rfl⟩
  have h2 := rankBitmasks_le_length ((basisOf L).map f)
  rw [List.length_map] at h2
  exact Nat.le_trans h1 h2

theorem rankBitmasks_append_comm (xs ys : List Nat) :
    rankBitmasks (xs ++ ys) = rankBitmasks (ys ++ xs) := by
  apply rankBitmasks_eq_of_span_eq
  apply span_eq_of_mem
  · intro x hx
    apply inSpanMasks_of_mem
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_append_right _ h
    · exact List.mem_append_left _ h
  · intro x hx
    apply inSpanMasks_of_mem
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_append_right _ h
    · exact List.mem_append_left _ h

/-! ## Combinations of columns and the parity form -/

theorem dotCount_succ (n a b : Nat) :
    dotCount (n + 1) a b = dotCount n a b + (if a.testBit n && b.testBit n then 1 else 0) := by
  unfold dotCount
  rw [List.range_succ, List.filter_append, List.length_append]
  congr 1
  cases h : (a.testBit n && b.testBit n) with
  | false =>
      rw [List.filter_cons_of_neg (p := fun i => a.testBit i && b.testBit i)
        (by rw [h]; exact Bool.false_ne_true)]
      rfl
  | true =>
      rw [List.filter_cons_of_pos (p := fun i => a.testBit i && b.testBit i) h]
      rfl

theorem parity_step (d : Nat) (b : Bool) :
    decide ((d + (if b then 1 else 0)) % 2 = 1) = (decide (d % 2 = 1) ^^ b) := by
  cases b
  · show decide ((d + 0) % 2 = 1) = (decide (d % 2 = 1) ^^ false)
    rw [Nat.add_zero, Bool.xor_false]
  · show decide ((d + 1) % 2 = 1) = (decide (d % 2 = 1) ^^ true)
    rcases Nat.mod_two_eq_zero_or_one d with h | h
    · rw [decide_eq_true (show (d + 1) % 2 = 1 by omega),
        decide_eq_false (show ¬ d % 2 = 1 by omega)]
      rfl
    · rw [decide_eq_false (show ¬ (d + 1) % 2 = 1 by omega), decide_eq_true h]
      rfl

theorem colMasks_succ (n : Nat) (R : List Nat) :
    colMasks (n + 1) R = colMasks n R ++ [colMask R n] := by
  unfold colMasks
  rw [List.range_succ, List.map_append]
  rfl

/-- Bit `z` of the combination of the columns of `R` by `y` is the parity
    of the overlap of member `z` of `R` with `y`. -/
theorem testBit_comb_colMasks (R : List Nat) (y : Nat) : ∀ (n z : Nat),
    (comb (colMasks n R) y).testBit z = decide (dotCount n (R.getD z 0) y % 2 = 1)
  | 0, z => by
      show (0 : Nat).testBit z = _
      rw [Nat.zero_testBit]
      rfl
  | n + 1, z => by
      rw [colMasks_succ, comb_snoc, Nat.testBit_xor, testBit_comb_colMasks R y n z,
        length_colMasks, testBit_sel, testBit_colMask, dotCount_succ, parity_step,
        Bool.and_comm]

/-- A mask with even overlap with every member of `R` has zero combination
    of the columns of `R`. -/
theorem comb_colMasks_eq_zero (n : Nat) (R : List Nat) (y : Nat)
    (h : ∀ z, z < R.length → dotCount n (R.getD z 0) y % 2 = 0) :
    comb (colMasks n R) y = 0 := by
  apply eq_zero_of_testBit
  intro z
  rw [testBit_comb_colMasks]
  rcases Nat.lt_or_ge z R.length with hz | hz
  · exact decide_eq_false (by rw [h z hz]; decide)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hz]
    show decide (dotCount n 0 y % 2 = 1) = false
    rw [dotCount_zero_left]
    rfl

/-! ## The two kinds of rows -/

/-- The rows `(i, x)`: an extra part and the tensor of the unit mask `i`
    with `Q_x` in the middle block. -/
def prodRows1 (mu : Nat → Nat) (E1 : Nat → Nat → Nat) (a b : Nat) (Q : List Nat) : List Nat :=
  (indexPairs a Q.length).map
    (fun ix => E1 ix.1 ix.2 ^^^ mu (tens a b (2 ^ ix.1) (Q.getD ix.2 0)))

/-- The rows `(x, j)`: an extra part and the tensor of `P_x` with the unit
    mask `j` in the middle block. -/
def prodRows2 (mu : Nat → Nat) (E2 : Nat → Nat → Nat) (a b : Nat) (P : List Nat) : List Nat :=
  (indexPairs P.length b).map
    (fun xj => E2 xj.1 xj.2 ^^^ mu (tens a b (P.getD xj.1 0) (2 ^ xj.2)))

/-- The middle blocks of the rows of the first kind. -/
def prodMids1 (a b : Nat) (Q : List Nat) : List Nat :=
  (indexPairs a Q.length).map (fun ix => tens a b (2 ^ ix.1) (Q.getD ix.2 0))

/-- The middle blocks of the rows of the second kind. -/
def prodMids2 (a b : Nat) (P : List Nat) : List Nat :=
  (indexPairs P.length b).map (fun xj => tens a b (P.getD xj.1 0) (2 ^ xj.2))

/-- The hypotheses of `rank_prodRows`: `mu` places the middle block, `phi`
    reads it back and kills the extra parts, `P` and `Q` are independent,
    and the extra parts cancel on the combination indexed by `(x', x)`. -/
structure ProdData (mu phi : Nat → Nat) (E1 E2 : Nat → Nat → Nat) (a b : Nat)
    (P Q : List Nat) : Prop where
  mu_xor : ∀ x y, mu (x ^^^ y) = mu x ^^^ mu y
  phi_xor : ∀ x y, phi (x ^^^ y) = phi x ^^^ phi y
  phi_mu : ∀ x, Below (a * b) x → phi (mu x) = x
  phi_E1 : ∀ i x, x < Q.length → phi (E1 i x) = 0
  phi_E2 : ∀ x j, j < b → phi (E2 x j) = 0
  indepP : independentMasks P
  indepQ : independentMasks Q
  belowP : ∀ p ∈ P, Below a p
  belowQ : ∀ q ∈ Q, Below b q
  dep : ∀ x' x, x' < P.length → x < Q.length →
    comb ((List.range a).map (fun i => E1 i x)) (P.getD x' 0) ^^^
      comb ((List.range b).map (fun j => E2 x' j)) (Q.getD x 0) = 0

theorem colMask_prodMids1 (a b : Nat) (Q : List Nat) (hQ : ∀ q ∈ Q, Below b q) (i' j : Nat)
    (hi' : i' < a) (hj : j < b) :
    colMask (prodMids1 a b Q) (i' * b + j) = tens a Q.length (2 ^ i') (colMask Q j) := by
  unfold prodMids1
  rw [colMask_map_indexPairs, ← maskFn_tens_unit_left a Q.length i' _ (below_colMask Q j)]
  congr 1
  funext r
  show (tens a b (2 ^ (r / Q.length)) (Q.getD (r % Q.length) 0)).testBit (i' * b + j) =
    (decide (r / Q.length = i') && (colMask Q j).testBit (r % Q.length))
  rw [testBit_tens a b _ _ _ (below_getD hQ _), decide_eq_true (mul_add_lt i' a b j hi' hj),
    mul_add_div i' b j hj, mul_add_mod i' b j hj, Bool.true_and, Nat.testBit_two_pow,
    testBit_colMask]

theorem colMask_prodMids2 (a b : Nat) (P : List Nat) (i' j : Nat) (hi' : i' < a)
    (hj : j < b) :
    colMask (prodMids2 a b P) (i' * b + j) = tens P.length b (colMask P i') (2 ^ j) := by
  have hb : 0 < b := Nat.lt_of_le_of_lt (Nat.zero_le j) hj
  unfold prodMids2
  rw [colMask_map_indexPairs, ← maskFn_tens_unit_right P.length b j _ hj]
  congr 1
  funext r
  show (tens a b (P.getD (r / b) 0) (2 ^ (r % b))).testBit (i' * b + j) =
    (decide (r % b = j) && (colMask P i').testBit (r / b))
  rw [testBit_tens a b _ _ _ (below_two_pow (Nat.mod_lt r hb)),
    decide_eq_true (mul_add_lt i' a b j hi' hj), mul_add_div i' b j hj, mul_add_mod i' b j hj,
    Bool.true_and, Nat.testBit_two_pow, testBit_colMask, Bool.and_comm]

theorem length_prodMids1 (a b : Nat) (Q : List Nat) :
    (prodMids1 a b Q).length = a * Q.length := by
  unfold prodMids1
  rw [List.length_map, length_indexPairs]

theorem length_prodRows1 (mu : Nat → Nat) (E1 : Nat → Nat → Nat) (a b : Nat) (Q : List Nat) :
    (prodRows1 mu E1 a b Q).length = a * Q.length := by
  unfold prodRows1
  rw [List.length_map, length_indexPairs]

theorem length_prodRows2 (mu : Nat → Nat) (E2 : Nat → Nat → Nat) (a b : Nat) (P : List Nat) :
    (prodRows2 mu E2 a b P).length = P.length * b := by
  unfold prodRows2
  rw [List.length_map, length_indexPairs]

theorem prod_arith (a b u w : Nat) (h : u ≤ a) :
    u * b + (a - u) * w = a * w + u * b - u * w := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Nat.add_sub_cancel_left, Nat.add_mul]
  omega

/-- The rank of the middle blocks, by row rank equals column rank and the
    two-block tensor family. -/
theorem rank_prodMids (a b : Nat) (P Q : List Nat) (hP : independentMasks P)
    (hQ : independentMasks Q) (hPb : ∀ p ∈ P, Below a p) (hQb : ∀ q ∈ Q, Below b q) :
    rankBitmasks (prodMids1 a b Q ++ prodMids2 a b P) =
      a * Q.length + P.length * b - P.length * Q.length := by
  have hu : P.length ≤ a := by
    rw [← rankBitmasks_of_indep hP]
    exact rankBitmasks_le_of_high_bits_false P a hPb
  have hbelow : ∀ r ∈ prodMids1 a b Q ++ prodMids2 a b P, Below (a * b) r := by
    intro r hr
    rcases List.mem_append.mp hr with h | h
    · obtain ⟨ix, _, rfl⟩ := List.mem_map.mp h
      exact below_tens a b _ _ (below_getD hQb _)
    · obtain ⟨xj, hxj, rfl⟩ := List.mem_map.mp h
      obtain ⟨_, hj⟩ := (mem_indexPairs (a := xj.1) (b := xj.2)).mp hxj
      exact below_tens a b _ _ (below_two_pow hj)
  have key : ∀ i' j, i' < a → j < b →
      colMask (prodMids1 a b Q ++ prodMids2 a b P) (i' * b + j) =
        hgTerm (· <<< (a * Q.length)) id a b P.length Q.length (colMasks a P) (colMasks b Q)
          j (2 ^ i') := by
    intro i' j hi' hj
    unfold hgTerm
    rw [colMask_append, colMask_prodMids1 a b Q hQb i' j hi' hj,
      colMask_prodMids2 a b P i' j hi' hj, length_prodMids1,
      comb_two_pow _ i' (by rw [length_colMasks]; exact hi'), getD_colMasks,
      ite_eq_left_of_eq_true _ _ (eq_true hi'), getD_colMasks,
      ite_eq_left_of_eq_true _ _ (eq_true hj), Nat.xor_comm]
    rfl
  have hspan : rankBitmasks (colMasks (a * b) (prodMids1 a b Q ++ prodMids2 a b P)) =
      rankBitmasks (hgRows (· <<< (a * Q.length)) id a b P.length Q.length (colMasks a P)
        (colMasks b Q)) := by
    apply rankBitmasks_eq_of_span_eq
    apply span_eq_of_mem
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      have hk' := List.mem_range.mp hk
      have hb : 0 < b := by
        rcases Nat.eq_zero_or_pos b with h0 | h0
        · rw [h0, Nat.mul_zero] at hk'
          exact absurd hk' (Nat.not_lt_zero k)
        · exact h0
      have hd : k / b < a := (Nat.div_lt_iff_lt_mul hb).mpr hk'
      have e := key (k / b) (k % b) hd (Nat.mod_lt k hb)
      rw [Nat.div_add_mod'] at e
      rw [e]
      apply inSpanMasks_of_mem
      exact List.mem_map.mpr ⟨(k / b, k % b), mem_indexPairs.mpr ⟨hd, Nat.mod_lt k hb⟩, rfl⟩
    · intro x hx
      obtain ⟨st, hst, rfl⟩ := List.mem_map.mp hx
      obtain ⟨hs, ht⟩ := (mem_indexPairs (a := st.1) (b := st.2)).mp hst
      apply inSpanMasks_of_mem
      exact List.mem_map.mpr ⟨st.1 * b + st.2, List.mem_range.mpr (mul_add_lt _ _ _ _ hs ht),
        key st.1 st.2 hs ht⟩
  rw [← rank_colMasks (a * b) _ hbelow, hspan,
    rank_hgRows (hgLayout_high a b P.length Q.length) (colMasks a P) (colMasks b Q)
      (length_colMasks _ _) (length_colMasks _ _) (below_colMasks a P) (below_colMasks b Q),
    rank_colMasks a P hPb, rank_colMasks b Q hQb, rankBitmasks_of_indep hP,
    rankBitmasks_of_indep hQ]
  exact prod_arith a b P.length Q.length hu

section Product

variable {mu phi : Nat → Nat} {E1 E2 : Nat → Nat → Nat} {a b : Nat} {P Q : List Nat}

theorem map_phi_prodRows (h : ProdData mu phi E1 E2 a b P Q) :
    (prodRows1 mu E1 a b Q ++ prodRows2 mu E2 a b P).map phi =
      prodMids1 a b Q ++ prodMids2 a b P := by
  rw [List.map_append]
  congr 1
  · unfold prodRows1 prodMids1
    rw [List.map_map]
    apply List.map_congr_left
    intro ix hix
    obtain ⟨i, x⟩ := ix
    obtain ⟨_, hx⟩ := mem_indexPairs.mp hix
    show phi (E1 i x ^^^ mu (tens a b (2 ^ i) (Q.getD x 0))) = tens a b (2 ^ i) (Q.getD x 0)
    rw [h.phi_xor, h.phi_E1 i x hx, h.phi_mu _ (below_tens a b _ _ (below_getD h.belowQ x)),
      Nat.zero_xor]
  · unfold prodRows2 prodMids2
    rw [List.map_map]
    apply List.map_congr_left
    intro xj hxj
    obtain ⟨x, j⟩ := xj
    obtain ⟨_, hj⟩ := mem_indexPairs.mp hxj
    show phi (E2 x j ^^^ mu (tens a b (P.getD x 0) (2 ^ j))) = tens a b (P.getD x 0) (2 ^ j)
    rw [h.phi_xor, h.phi_E2 x j hj, h.phi_mu _ (below_tens a b _ _ (below_two_pow hj)),
      Nat.zero_xor]

/-- The combination indexed by `(x', x)` of the rows is zero. -/
theorem comb_prodRows_dep (h : ProdData mu phi E1 E2 a b P Q) (x' x : Nat)
    (hx' : x' < P.length) (hx : x < Q.length) :
    comb (prodRows1 mu E1 a b Q ++ prodRows2 mu E2 a b P)
      (hgTerm id (· <<< (a * Q.length)) P.length Q.length a b P Q x (2 ^ x')) = 0 := by
  unfold hgTerm
  show comb (prodRows1 mu E1 a b Q ++ prodRows2 mu E2 a b P)
    (tens a Q.length (comb P (2 ^ x')) (2 ^ x) ^^^
      (tens P.length b (2 ^ x') (Q.getD x 0) <<< (a * Q.length))) = 0
  rw [comb_two_pow P x' hx',
    comb_append (a * Q.length) _ _ _ _ (length_prodRows1 mu E1 a b Q)
      (below_tens a Q.length _ _ (below_two_pow hx))]
  unfold prodRows1 prodRows2
  rw [comb_indexPairs_right Q.length x hx a _ _,
    comb_indexPairs_left b _ (below_getD h.belowQ x) P.length _ x' hx']
  show comb ((List.range a).map
        (fun i => E1 i x ^^^ mu (tens a b (2 ^ i) (Q.getD x 0)))) (P.getD x' 0) ^^^
      comb ((List.range b).map
        (fun j => E2 x' j ^^^ mu (tens a b (P.getD x' 0) (2 ^ j)))) (Q.getD x 0) = 0
  rw [comb_map_xor, comb_map_xor,
    comb_map_units (fun y => mu (tens a b y (Q.getD x 0)))
      (fun y z => by
        show mu (tens a b (y ^^^ z) _) = _
        rw [tens_xor_left, h.mu_xor]) a _ (below_getD h.belowP x'),
    comb_map_units (fun y => mu (tens a b (P.getD x' 0) y))
      (fun y z => by
        show mu (tens a b _ (y ^^^ z)) = _
        rw [tens_xor_right, h.mu_xor]) b _ (below_getD h.belowQ x),
    xor_interchange, Nat.xor_self, Nat.xor_zero]
  exact h.dep x' x hx' hx

/-- The rank of the two kinds of rows. -/
theorem rank_prodRows (h : ProdData mu phi E1 E2 a b P Q) :
    rankBitmasks (prodRows1 mu E1 a b Q ++ prodRows2 mu E2 a b P) =
      a * Q.length + P.length * b - P.length * Q.length := by
  have hlen : (prodRows1 mu E1 a b Q ++ prodRows2 mu E2 a b P).length =
      a * Q.length + P.length * b := by
    rw [List.length_append, length_prodRows1, length_prodRows2]
  -- the dependencies have rank `|P| * |Q|`
  have hK : rankBitmasks (hgRows id (· <<< (a * Q.length)) P.length Q.length a b P Q) =
      P.length * Q.length := by
    rw [rank_hgRows (hgLayout_low P.length Q.length a b) P Q rfl rfl h.belowP h.belowQ,
      rankBitmasks_of_indep h.indepP, Nat.sub_self, Nat.zero_mul, Nat.add_zero]
  have hsub : ∀ k ∈ hgRows id (· <<< (a * Q.length)) P.length Q.length a b P Q,
      inSpanMasks (kerList (prodRows1 mu E1 a b Q ++ prodRows2 mu E2 a b P)) k := by
    intro k hk
    obtain ⟨st, hst, rfl⟩ := List.mem_map.mp hk
    obtain ⟨hx', hx⟩ := (mem_indexPairs (a := st.1) (b := st.2)).mp hst
    apply inSpan_kerList
    · rw [hlen]
      unfold hgTerm
      exact below_xor
        (below_mono (Nat.le_add_right _ _) (below_tens a Q.length _ _ (below_two_pow hx)))
        (below_shiftLeft (a * Q.length) (below_tens P.length b _ _ (below_getD h.belowQ st.2)))
    · exact comb_prodRows_dep h st.1 st.2 hx' hx
  have h3 := rankBitmasks_le_of_span hsub
  rw [hK] at h3
  have h4 := rank_kerList (prodRows1 mu E1 a b Q ++ prodRows2 mu E2 a b P)
  rw [hlen] at h4
  have h5 := rankBitmasks_map_le_additive phi h.phi_xor (prodRows1 mu E1 a b Q ++ prodRows2 mu E2 a b P)
  rw [map_phi_prodRows h, rank_prodMids a b P Q h.indepP h.indepQ h.belowP h.belowQ] at h5
  omega

end Product

end CodeCalculus
