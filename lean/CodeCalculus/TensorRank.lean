import CodeCalculus.RankNullity

/-!
# Tensor products of masks and their rank

`tens p q a b` is the mask over the positions `i * q + j`, for `i < p` and
`j < q`, whose bit `i * q + j` is the conjunction of bit `i` of `a` and bit
`j` of `b`. The module proves that the rank of a family of tensors is the
product of the ranks (`rank_tens`), which the closed forms for `k` of
`L-HGP` and `A-PRODUCT` use.
-/

namespace CodeCalculus

/-! ## Masks from a bit function -/

/-- The mask below `2 ^ n` whose bit `i` is `f i`. -/
def maskFn (n : Nat) (f : Nat → Bool) : Nat := boolsToMask ((List.range n).map f)

theorem getD_map_range (n : Nat) (f : Nat → Bool) (i : Nat) :
    ((List.range n).map f).getD i false = (decide (i < n) && f i) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases Nat.lt_or_ge i n with h | h
  · rw [List.getElem?_range h, decide_eq_true h]
    rfl
  · rw [List.getElem?_eq_none (by rw [List.length_range]; exact h),
      decide_eq_false (Nat.not_lt_of_le h)]
    rfl

theorem testBit_maskFn (n : Nat) (f : Nat → Bool) (i : Nat) :
    (maskFn n f).testBit i = (decide (i < n) && f i) := by
  unfold maskFn
  rw [testBit_boolsToMask, getD_map_range]

theorem maskFn_xor (n : Nat) (f g : Nat → Bool) :
    maskFn n (fun i => f i ^^ g i) = maskFn n f ^^^ maskFn n g := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, testBit_maskFn, testBit_maskFn, testBit_maskFn]
  cases decide (i < n) <;> cases f i <;> cases g i <;> rfl

theorem below_maskFn (n : Nat) (f : Nat → Bool) : Below n (maskFn n f) := by
  intro j hj
  rw [testBit_maskFn, decide_eq_false (Nat.not_lt_of_le hj)]
  rfl

theorem maskFn_false (n : Nat) : maskFn n (fun _ => false) = 0 := by
  apply eq_zero_of_testBit
  intro i
  rw [testBit_maskFn, Bool.and_false]

/-! ## Index arithmetic -/

theorem mul_add_div (i q j : Nat) (hj : j < q) : (i * q + j) / q = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right j i (Nat.lt_of_le_of_lt (Nat.zero_le j) hj),
    Nat.div_eq_of_lt hj, Nat.zero_add]

theorem mul_add_mod (i q j : Nat) (hj : j < q) : (i * q + j) % q = j := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

theorem mul_add_lt (i p q j : Nat) (hi : i < p) (hj : j < q) : i * q + j < p * q := by
  have h1 : (i + 1) * q ≤ p * q := Nat.mul_le_mul_right q hi
  rw [Nat.succ_mul] at h1
  omega

/-! ## The tensor of two masks -/

/-- The tensor of `a`, read over `p` positions, and `b`, read over `q`. -/
def tens : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | p + 1, q, a, b => sel (a.testBit 0) b ^^^ (tens p q (a >>> 1) b <<< q)

theorem tens_xor_left : ∀ (p q a a' b : Nat),
    tens p q (a ^^^ a') b = tens p q a b ^^^ tens p q a' b
  | 0, _, _, _, _ => (Nat.xor_self 0).symm
  | p + 1, q, a, a', b => by
      show sel ((a ^^^ a').testBit 0) b ^^^ (tens p q ((a ^^^ a') >>> 1) b <<< q) =
        (sel (a.testBit 0) b ^^^ (tens p q (a >>> 1) b <<< q)) ^^^
          (sel (a'.testBit 0) b ^^^ (tens p q (a' >>> 1) b <<< q))
      rw [Nat.testBit_xor, sel_xor_bool, Nat.shiftRight_xor_distrib, tens_xor_left p,
        shiftLeft_xor, xor_interchange]

theorem tens_xor_right : ∀ (p q a b b' : Nat),
    tens p q a (b ^^^ b') = tens p q a b ^^^ tens p q a b'
  | 0, _, _, _, _ => (Nat.xor_self 0).symm
  | p + 1, q, a, b, b' => by
      show sel (a.testBit 0) (b ^^^ b') ^^^ (tens p q (a >>> 1) (b ^^^ b') <<< q) =
        (sel (a.testBit 0) b ^^^ (tens p q (a >>> 1) b <<< q)) ^^^
          (sel (a.testBit 0) b' ^^^ (tens p q (a >>> 1) b' <<< q))
      rw [sel_xor_val, tens_xor_right p, shiftLeft_xor, xor_interchange]

theorem tens_zero_right (p q a : Nat) : tens p q a 0 = 0 :=
  additive_zero (tens p q a) (tens_xor_right p q a)

theorem tens_zero_left (p q b : Nat) : tens p q 0 b = 0 :=
  additive_zero (fun a => tens p q a b) (fun a a' => tens_xor_left p q a a' b)

/-- The bits of a tensor. -/
theorem testBit_tens : ∀ (p q a b k : Nat), Below q b →
    (tens p q a b).testBit k =
      (decide (k < p * q) && (a.testBit (k / q) && b.testBit (k % q)))
  | 0, q, a, b, k, _ => by
      show (0 : Nat).testBit k = _
      rw [Nat.zero_testBit, Nat.zero_mul, decide_eq_false (Nat.not_lt_zero k)]
      rfl
  | p + 1, q, a, b, k, hb => by
      show (sel (a.testBit 0) b ^^^ (tens p q (a >>> 1) b <<< q)).testBit k = _
      rw [Nat.testBit_xor, testBit_sel, Nat.testBit_shiftLeft,
        testBit_tens p q (a >>> 1) b (k - q) hb, Nat.testBit_shiftRight]
      rcases Nat.lt_or_ge k q with hk | hqk
      · have hlt : k < (p + 1) * q := by
          rw [Nat.succ_mul]
          exact Nat.lt_of_lt_of_le hk (Nat.le_add_left q (p * q))
        rw [decide_eq_false (Nat.not_le_of_lt hk), Bool.false_and, Bool.xor_false,
          Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk, decide_eq_true hlt, Bool.true_and]
      · rw [hb k hqk, Bool.and_false, Bool.false_xor, decide_eq_true hqk, Bool.true_and]
        rcases Nat.eq_zero_or_pos q with h0 | hq
        · subst h0
          rw [hb _ (Nat.zero_le _), hb (k % 0) (Nat.zero_le _), Bool.and_false,
            Bool.and_false, Bool.and_false, Bool.and_false]
        · obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hqk
          have e : decide (q + k' < (p + 1) * q) = decide (k' < p * q) := by
            rw [Nat.succ_mul]
            rcases Nat.lt_or_ge k' (p * q) with h | h
            · rw [decide_eq_true h, decide_eq_true (show q + k' < p * q + q by omega)]
            · rw [decide_eq_false (Nat.not_lt_of_le h),
                decide_eq_false (show ¬ q + k' < p * q + q by omega)]
          rw [Nat.add_sub_cancel_left, Nat.add_div_left k' hq, Nat.add_mod_left, e,
            Nat.add_comm 1]

theorem below_tens (p q a b : Nat) (hb : Below q b) : Below (p * q) (tens p q a b) := by
  intro j hj
  rw [testBit_tens p q a b j hb, decide_eq_false (Nat.not_lt_of_le hj)]
  rfl

/-! ## Slices -/

/-- Block `i` of a mask over `p * q` positions: the positions `i * q + k`. -/
def rowSlice (q i v : Nat) : Nat := maskFn q (fun k => v.testBit (i * q + k))

/-- The positions `i * q + j` of a mask, for the fixed `j`. -/
def colSlice (p q j v : Nat) : Nat := maskFn p (fun i => v.testBit (i * q + j))

theorem rowSlice_xor (q i v w : Nat) :
    rowSlice q i (v ^^^ w) = rowSlice q i v ^^^ rowSlice q i w := by
  unfold rowSlice
  rw [← maskFn_xor]
  congr 1
  funext k
  exact Nat.testBit_xor ..

theorem colSlice_xor (p q j v w : Nat) :
    colSlice p q j (v ^^^ w) = colSlice p q j v ^^^ colSlice p q j w := by
  unfold colSlice
  rw [← maskFn_xor]
  congr 1
  funext k
  exact Nat.testBit_xor ..

theorem rowSlice_zero (q i : Nat) : rowSlice q i 0 = 0 :=
  additive_zero (rowSlice q i) (rowSlice_xor q i)

theorem colSlice_zero (p q j : Nat) : colSlice p q j 0 = 0 :=
  additive_zero (colSlice p q j) (colSlice_xor p q j)

theorem below_rowSlice (q i v : Nat) : Below q (rowSlice q i v) := below_maskFn q _

theorem below_colSlice (p q j v : Nat) : Below p (colSlice p q j v) := below_maskFn p _

theorem rowSlice_tens (p q a b i : Nat) (hb : Below q b) (hi : i < p) :
    rowSlice q i (tens p q a b) = sel (a.testBit i) b := by
  apply Nat.eq_of_testBit_eq
  intro k
  unfold rowSlice
  rw [testBit_maskFn, testBit_tens p q a b _ hb, testBit_sel]
  rcases Nat.lt_or_ge k q with hk | hk
  · rw [decide_eq_true hk, decide_eq_true (mul_add_lt i p q k hi hk), mul_add_div i q k hk,
      mul_add_mod i q k hk, Bool.true_and, Bool.true_and]
  · rw [decide_eq_false (Nat.not_lt_of_le hk), hb k hk, Bool.false_and, Bool.and_false]

theorem colSlice_tens (p q a b j : Nat) (ha : Below p a) (hb : Below q b) (hj : j < q) :
    colSlice p q j (tens p q a b) = sel (b.testBit j) a := by
  apply Nat.eq_of_testBit_eq
  intro i
  unfold colSlice
  rw [testBit_maskFn, testBit_tens p q a b _ hb, testBit_sel, mul_add_div i q j hj,
    mul_add_mod i q j hj]
  rcases Nat.lt_or_ge i p with hi | hi
  · rw [decide_eq_true hi, decide_eq_true (mul_add_lt i p q j hi hj), Bool.true_and,
      Bool.true_and, Bool.and_comm]
  · rw [decide_eq_false (Nat.not_lt_of_le hi), ha i hi, Bool.false_and, Bool.and_false]

/-! ## Sums of tensors -/

/-- The sum of the tensors of two lists, taken position by position. -/
def tsum (p q : Nat) : List Nat → List Nat → Nat
  | a :: as, b :: bs => tens p q a b ^^^ tsum p q as bs
  | _, _ => 0

theorem tsum_zeros (p q : Nat) : ∀ (as : List Nat) (n : Nat),
    tsum p q as (List.replicate n 0) = 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | a :: as, n + 1 => by
      show tens p q a 0 ^^^ tsum p q as (List.replicate n 0) = 0
      rw [tens_zero_right, tsum_zeros p q as n, Nat.xor_self]

theorem bit_coeff (b : Bool) (x : Nat) :
    (if (if b then 1 else 0) = 1 then x else 0) = sel b x := by
  cases b <;> rfl

theorem colSlice_tsum (p q j : Nat) (hj : j < q) : ∀ (as bs : List Nat),
    (∀ a ∈ as, Below p a) → (∀ b ∈ bs, Below q b) →
    colSlice p q j (tsum p q as bs) =
      combineMasks as (bs.map (fun b => if b.testBit j then 1 else 0))
  | [], bs, _, _ => by
      show colSlice p q j 0 = _
      rw [colSlice_zero, combineMasks_nil]
  | a :: as, [], _, _ => by
      show colSlice p q j 0 = 0
      exact colSlice_zero p q j
  | a :: as, b :: bs, ha, hb => by
      show colSlice p q j (tens p q a b ^^^ tsum p q as bs) =
        combineMasks (a :: as)
          ((if b.testBit j then 1 else 0) :: bs.map (fun b => if b.testBit j then 1 else 0))
      rw [colSlice_xor, colSlice_tens p q a b j (ha a (List.mem_cons_self ..))
        (hb b (List.mem_cons_self ..)) hj, combineMasks_cons, bit_coeff,
        colSlice_tsum p q j hj as bs (fun x hx => ha x (List.mem_cons_of_mem _ hx))
          (fun x hx => hb x (List.mem_cons_of_mem _ hx))]

theorem rowSlice_tsum (p q i : Nat) (hi : i < p) : ∀ (as bs : List Nat),
    (∀ b ∈ bs, Below q b) →
    rowSlice q i (tsum p q as bs) =
      combineMasks bs (as.map (fun a => if a.testBit i then 1 else 0))
  | [], bs, _ => by
      show rowSlice q i 0 = combineMasks bs []
      rw [rowSlice_zero]
      cases bs <;> rfl
  | a :: as, [], _ => by
      show rowSlice q i 0 = 0
      exact rowSlice_zero q i
  | a :: as, b :: bs, hb => by
      show rowSlice q i (tens p q a b ^^^ tsum p q as bs) =
        combineMasks (b :: bs)
          ((if a.testBit i then 1 else 0) :: as.map (fun a => if a.testBit i then 1 else 0))
      rw [rowSlice_xor, rowSlice_tens p q a b i (hb b (List.mem_cons_self ..)) hi,
        combineMasks_cons, bit_coeff,
        rowSlice_tsum p q i hi as bs (fun x hx => hb x (List.mem_cons_of_mem _ hx))]

theorem bit_coeff_01 (l : List Nat) (j : Nat) :
    ∀ c ∈ l.map (fun b => if b.testBit j then 1 else 0), c = 0 ∨ c = 1 := by
  intro c hc
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hc
  cases b.testBit j
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem bit_false_of_coeff_zero {l : List Nat} {j : Nat}
    (h : ∀ c ∈ l.map (fun b => if b.testBit j then 1 else 0), c = 0) :
    ∀ b ∈ l, b.testBit j = false := by
  intro b hb
  have hc := h _ (List.mem_map_of_mem (f := fun b => if b.testBit j then 1 else 0) hb)
  cases hbit : b.testBit j with
  | false => rfl
  | true =>
      rw [hbit] at hc
      exact absurd hc (by decide)

/-- A sum of tensors with independent first factors is zero only when every
    second factor is zero. -/
theorem tsum_eq_zero_right (p q : Nat) (as bs : List Nat) (hind : independentMasks as)
    (hlen : bs.length = as.length) (ha : ∀ a ∈ as, Below p a) (hb : ∀ b ∈ bs, Below q b)
    (h : tsum p q as bs = 0) : ∀ b ∈ bs, b = 0 := by
  intro b hbm
  apply eq_zero_of_testBit
  intro j
  rcases Nat.lt_or_ge j q with hj | hj
  · have hc := colSlice_tsum p q j hj as bs ha hb
    rw [h, colSlice_zero] at hc
    exact bit_false_of_coeff_zero
      (hind _ (by rw [List.length_map, hlen]) (bit_coeff_01 bs j) hc.symm) b hbm
  · exact hb b hbm j hj

/-- A sum of tensors with independent second factors is zero only when
    every first factor is zero. -/
theorem tsum_eq_zero_left (p q : Nat) (as bs : List Nat) (hind : independentMasks bs)
    (hlen : as.length = bs.length) (ha : ∀ a ∈ as, Below p a) (hb : ∀ b ∈ bs, Below q b)
    (h : tsum p q as bs = 0) : ∀ a ∈ as, a = 0 := by
  intro a ham
  apply eq_zero_of_testBit
  intro i
  rcases Nat.lt_or_ge i p with hi | hi
  · have hc := rowSlice_tsum p q i hi as bs hb
    rw [h, rowSlice_zero] at hc
    exact bit_false_of_coeff_zero
      (hind _ (by rw [List.length_map, hlen]) (bit_coeff_01 as i) hc.symm) a ham
  · exact ha a ham i hi

/-! ## The rank of a family of tensors -/

/-- A member of the span of the tensors of `B` with `W` is a sum of tensors
    of the members of `B` with members of the span of `W`. -/
theorem inSpan_flatMap_tens (p q : Nat) (W : List Nat) : ∀ (B : List Nat) (c : Nat),
    inSpanMasks (B.flatMap (fun x => W.map (tens p q x))) c →
    ∃ ws, ws.length = B.length ∧ (∀ w ∈ ws, inSpanMasks W w) ∧ c = tsum p q B ws
  | [], c, h => by
      refine ⟨[], rfl, fun _ hw => absurd hw List.not_mem_nil, ?_⟩
      rw [(inSpanMasks_nil c).mp h]
      rfl
  | b :: B, c, h => by
      rw [List.flatMap_cons] at h
      obtain ⟨a, d, ha, hd, rfl⟩ := (inSpanMasks_append_iff _ _ c).mp h
      obtain ⟨w, hw, rfl⟩ :=
        (inSpanMasks_map_additive_iff (tens p q b) (tens_xor_right p q b) W a).mp ha
      obtain ⟨ws, hlen, hws, rfl⟩ := inSpan_flatMap_tens p q W B d hd
      refine ⟨w :: ws, by rw [List.length_cons, List.length_cons, hlen], ?_, rfl⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hw
      · exact hws x hx

theorem rank_tens_indep (p q : Nat) (W : List Nat) (hW : ∀ w ∈ W, Below q w) :
    ∀ (B : List Nat), independentMasks B → (∀ b ∈ B, Below p b) →
      rankBitmasks (B.flatMap (fun x => W.map (tens p q x))) = B.length * rankBitmasks W
  | [], _, _ => by
      show rankBitmasks [] = 0 * rankBitmasks W
      rw [Nat.zero_mul]
      rfl
  | b :: B, hind, hB => by
      have hinj : ∀ a, inSpanMasks W a → tens p q b a = 0 → a = 0 := by
        intro a ha h0
        have hz : tsum p q (b :: B) (a :: List.replicate B.length 0) = 0 := by
          show tens p q b a ^^^ tsum p q B (List.replicate B.length 0) = 0
          rw [h0, tsum_zeros, Nat.xor_self]
        refine tsum_eq_zero_right p q (b :: B) (a :: List.replicate B.length 0) hind
          (by rw [List.length_cons, List.length_cons, List.length_replicate]) hB ?_ hz a
          (List.mem_cons_self ..)
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact below_of_inSpan hW ha
        · rw [(List.mem_replicate.mp hx).2]
          exact below_zero q
      have hdis : ∀ a c, inSpanMasks (W.map (tens p q b)) a →
          inSpanMasks (B.flatMap (fun x => W.map (tens p q x))) c → a ^^^ c = 0 → a = 0 := by
        intro a c ha hc hac
        obtain ⟨w, hw, rfl⟩ :=
          (inSpanMasks_map_additive_iff (tens p q b) (tens_xor_right p q b) W a).mp ha
        obtain ⟨ws, hlen, hws, rfl⟩ := inSpan_flatMap_tens p q W B c hc
        have hw0 : w = 0 := by
          refine tsum_eq_zero_right p q (b :: B) (w :: ws) hind
            (by rw [List.length_cons, List.length_cons, hlen]) hB ?_ hac w
            (List.mem_cons_self ..)
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact below_of_inSpan hW hw
          · exact below_of_inSpan hW (hws x hx)
        rw [hw0, tens_zero_right]
      rw [List.flatMap_cons, rankBitmasks_append_of_disjoint _ _ hdis,
        rankBitmasks_map (tens p q b) (tens_xor_right p q b) W hinj,
        rank_tens_indep p q W hW B (independentMasks_tail hind)
          (fun x hx => hB x (List.mem_cons_of_mem _ hx)),
        List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- The rank of the tensors of two mask lists is the product of the ranks. -/
theorem rank_tens (p q : Nat) (X W : List Nat) (hX : ∀ x ∈ X, Below p x)
    (hW : ∀ w ∈ W, Below q w) :
    rankBitmasks (X.flatMap (fun x => W.map (tens p q x))) =
      rankBitmasks X * rankBitmasks W := by
  have key : ∀ X Y : List Nat, (∀ x ∈ X, inSpanMasks Y x) →
      ∀ v, v ∈ X.flatMap (fun x => W.map (tens p q x)) →
        inSpanMasks (Y.flatMap (fun x => W.map (tens p q x))) v := by
    intro X Y h v hv
    obtain ⟨x, hx, hv⟩ := List.mem_flatMap.mp hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    have h1 : inSpanMasks (Y.map (fun y => tens p q y w)) (tens p q x w) :=
      (inSpanMasks_map_additive_iff (fun y => tens p q y w)
        (fun a a' => tens_xor_left p q a a' w) Y _).mpr ⟨x, h x hx, rfl⟩
    exact inSpanMasks_trans (gen := Y.map (fun y => tens p q y w))
      (pre := Y.flatMap (fun x => W.map (tens p q x))) (fun g hg => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hg
        exact inSpanMasks_of_mem (List.mem_flatMap.mpr ⟨y, hy, List.mem_map_of_mem hw⟩)) h1
  rw [rankBitmasks_eq_of_span_eq (span_eq_of_mem
    (key X (basisOf X) (fun x hx => (basisOf_span X x).mpr (inSpanMasks_of_mem hx)))
    (key (basisOf X) X (fun b hb => (basisOf_span X b).mp (inSpanMasks_of_mem hb))))]
  exact rank_tens_indep p q W hW (basisOf X) (basisOf_indep X)
    (fun b hb => below_of_inSpan hX ((basisOf_span X b).mp (inSpanMasks_of_mem hb)))

end CodeCalculus
