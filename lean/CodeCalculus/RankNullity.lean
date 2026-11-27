import CodeCalculus.ConstructorRankTyped

/-!
# Rank and nullity for mask lists

`MaskRank.lean` and `ConstructorRank.lean` compare the greedy rank of two
mask lists with the same span. This module adds what the closed forms for
`k` of `L-HGP` and `A-PRODUCT` need on top of that:

* `rankBitmasks_le_of_span`: the rank is monotone in the span.
* `rank_nullity`: for an additive map `f` and a mask list `L`, the rank of
  the image of `L` plus the rank of a list spanning the kernel of `f` on
  the span of `L` is the rank of `L`.
* `comb`, `unitMasks`, and `kerList`: the combination of a mask list by the
  bits of a coefficient mask, the unit masks, and a list spanning the
  coefficient masks with zero combination, with
  `rank_kerList : rank (kerList A) + rank A = A.length`.

Nothing here mentions a code state.
-/

namespace CodeCalculus

/-! ## Selection by a Boolean -/

/-- `x` when `b` holds, and zero otherwise. -/
def sel (b : Bool) (x : Nat) : Nat := if b then x else 0

theorem sel_true (x : Nat) : sel true x = x := rfl

theorem sel_false (x : Nat) : sel false x = 0 := rfl

theorem sel_zero (b : Bool) : sel b 0 = 0 := by cases b <;> rfl

theorem sel_xor_bool (a b : Bool) (x : Nat) : sel (a ^^ b) x = sel a x ^^^ sel b x := by
  cases a <;> cases b
  · exact (Nat.xor_self 0).symm
  · exact (Nat.zero_xor x).symm
  · exact (Nat.xor_zero x).symm
  · exact (Nat.xor_self x).symm

theorem sel_xor_val (b : Bool) (x y : Nat) : sel b (x ^^^ y) = sel b x ^^^ sel b y := by
  cases b
  · exact (Nat.xor_self 0).symm
  · rfl

theorem sel_map (f : Nat → Nat) (h0 : f 0 = 0) (b : Bool) (x : Nat) :
    f (sel b x) = sel b (f x) := by
  cases b
  · exact h0
  · rfl

theorem testBit_sel (b : Bool) (x i : Nat) : (sel b x).testBit i = (b && x.testBit i) := by
  cases b
  · exact Nat.zero_testBit i
  · rfl

/-- The interchange law for `xor`. -/
theorem xor_interchange (a b c d : Nat) :
    (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  rw [Nat.xor_assoc, Nat.xor_assoc, xor3_left_comm b c d]

/-- No bit at or above position `n`. -/
def Below (n x : Nat) : Prop := ∀ j, n ≤ j → x.testBit j = false

theorem below_zero (n : Nat) : Below n 0 := fun j _ => Nat.zero_testBit j

theorem below_xor {n a b : Nat} (ha : Below n a) (hb : Below n b) : Below n (a ^^^ b) := by
  intro j hj
  rw [Nat.testBit_xor, ha j hj, hb j hj]
  rfl

theorem below_sel {n x : Nat} (b : Bool) (h : Below n x) : Below n (sel b x) := by
  cases b
  · exact below_zero n
  · exact h

theorem below_of_inSpan {n : Nat} {xs : List Nat} {v : Nat} (h : ∀ x ∈ xs, Below n x)
    (hv : inSpanMasks xs v) : Below n v :=
  fun j hj => testBit_false_of_inSpan (fun x hx => h x hx j hj) hv

theorem eq_zero_of_below_zero {x : Nat} (h : Below 0 x) : x = 0 :=
  Nat.eq_of_testBit_eq (fun i => by rw [h i (Nat.zero_le i), Nat.zero_testBit])

theorem eq_zero_of_testBit {x : Nat} (h : ∀ i, x.testBit i = false) : x = 0 :=
  Nat.eq_of_testBit_eq (fun i => by rw [h i, Nat.zero_testBit])

/-! ## Rank and spans -/

theorem length_le_insertBasis (basis : List Nat) (x : Nat) :
    basis.length ≤ (insertBasis basis x).length := by
  show basis.length ≤
    (if reduceByBasis basis x = 0 then basis else reduceByBasis basis x :: basis).length
  cases Nat.decEq (reduceByBasis basis x) 0 with
  | isTrue h => rw [ite_eq_left_of_eq_true _ _ (eq_true h)]; exact Nat.le_refl _
  | isFalse h => rw [ite_eq_right_of_eq_false _ _ (eq_false h)]; exact Nat.le_succ _

/-- Greedy insertion only prepends to the accumulator. -/
theorem foldl_insertBasis_suffix : ∀ (xs acc : List Nat),
    ∃ new, xs.foldl insertBasis acc = new ++ acc
  | [], acc => ⟨[], rfl⟩
  | x :: xs, acc => by
      obtain ⟨new, h⟩ := foldl_insertBasis_suffix xs (insertBasis acc x)
      rw [List.foldl_cons, h]
      show ∃ new', new ++
        (if reduceByBasis acc x = 0 then acc else reduceByBasis acc x :: acc) = new' ++ acc
      cases Nat.decEq (reduceByBasis acc x) 0 with
      | isTrue h0 => rw [ite_eq_left_of_eq_true _ _ (eq_true h0)]; exact ⟨new, rfl⟩
      | isFalse h0 =>
          rw [ite_eq_right_of_eq_false _ _ (eq_false h0)]
          exact ⟨new ++ [reduceByBasis acc x], by rw [List.append_assoc]; rfl⟩

theorem rankBitmasks_le_append (xs ys : List Nat) :
    rankBitmasks xs ≤ rankBitmasks (xs ++ ys) := by
  unfold rankBitmasks
  rw [List.foldl_append]
  obtain ⟨new, h⟩ := foldl_insertBasis_suffix ys (xs.foldl insertBasis [])
  rw [h, List.length_append]
  exact Nat.le_add_left _ _

/-- The rank is monotone in the span. -/
theorem rankBitmasks_le_of_span {xs ys : List Nat} (h : ∀ x ∈ xs, inSpanMasks ys x) :
    rankBitmasks xs ≤ rankBitmasks ys := by
  have hspan : ∀ v, inSpanMasks (xs ++ ys) v ↔ inSpanMasks ys v := by
    intro v
    constructor
    · intro hv
      exact inSpanMasks_trans (gen := xs ++ ys) (pre := ys) (fun g hg => by
        rcases List.mem_append.mp hg with hg | hg
        · exact h g hg
        · exact inSpanMasks_of_mem hg) hv
    · intro hv
      exact inSpanMasks_append_left hv
  rw [← rankBitmasks_eq_of_span_eq hspan]
  exact rankBitmasks_le_append xs ys

theorem rankBitmasks_append_le (xs ys : List Nat) :
    rankBitmasks (xs ++ ys) ≤ rankBitmasks xs + rankBitmasks ys := by
  have hspan : ∀ v, inSpanMasks (xs ++ ys) v ↔ inSpanMasks (basisOf xs ++ basisOf ys) v := by
    intro v
    rw [inSpanMasks_append_iff, inSpanMasks_append_iff]
    constructor
    · rintro ⟨a, b, ha, hb, rfl⟩
      exact ⟨a, b, (basisOf_span xs a).mpr ha, (basisOf_span ys b).mpr hb, rfl⟩
    · rintro ⟨a, b, ha, hb, rfl⟩
      exact ⟨a, b, (basisOf_span xs a).mp ha, (basisOf_span ys b).mp hb, rfl⟩
  rw [rankBitmasks_eq_of_span_eq hspan]
  have h := rankBitmasks_le_length (basisOf xs ++ basisOf ys)
  rw [List.length_append] at h
  exact h

/-- An additive map that kills the generators kills the span. -/
theorem additive_span_zero (f : Nat → Nat) (hadd : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    {xs : List Nat} (h : ∀ x ∈ xs, f x = 0) {v : Nat} (hv : inSpanMasks xs v) : f v = 0 := by
  have hv' : inSpanMasks (xs.map f) (f v) :=
    (inSpanMasks_map_additive_iff f hadd xs (f v)).mpr ⟨v, hv, rfl⟩
  apply eq_zero_of_testBit
  intro i
  apply testBit_false_of_inSpan _ hv'
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  rw [h x hx]
  exact Nat.zero_testBit i

/-- Induction over a span. -/
theorem span_induction {P : Nat → Prop} (h0 : P 0) (hx : ∀ a b, P a → P b → P (a ^^^ b)) :
    ∀ (xs : List Nat), (∀ x ∈ xs, P x) → ∀ v, inSpanMasks xs v → P v
  | [], _, v, hv => by
      rw [(inSpanMasks_nil v).mp hv]
      exact h0
  | x :: xs, hm, v, ⟨cs, hlen, h01, hval⟩ => by
      cases cs with
      | nil => exact absurd hlen.symm (Nat.succ_ne_zero _)
      | cons c cs =>
          rw [combineMasks_cons] at hval
          rw [← hval]
          apply hx
          · cases Nat.decEq c 1 with
            | isTrue h => rw [ite_eq_left_of_eq_true _ _ (eq_true h)]; exact hm x (List.mem_cons_self ..)
            | isFalse h => rw [ite_eq_right_of_eq_false _ _ (eq_false h)]; exact h0
          · exact span_induction h0 hx xs (fun y hy => hm y (List.mem_cons_of_mem _ hy)) _
              ⟨cs, Nat.succ.inj hlen, fun d hd => h01 d (List.mem_cons_of_mem _ hd), rfl⟩

theorem exists_preimages (f : Nat → Nat) (P : Nat → Prop) : ∀ ys : List Nat,
    (∀ y ∈ ys, ∃ p, P p ∧ f p = y) → ∃ ps : List Nat, (∀ p ∈ ps, P p) ∧ ps.map f = ys
  | [], _ => ⟨[], ⟨fun _ h => absurd h List.not_mem_nil, rfl⟩⟩
  | y :: ys, h => by
      obtain ⟨p, hp, hfp⟩ := h y (List.mem_cons_self ..)
      obtain ⟨ps, hps, hmap⟩ := exists_preimages f P ys
        (fun z hz => h z (List.mem_cons_of_mem _ hz))
      refine ⟨p :: ps, ?_, by rw [List.map_cons, hfp, hmap]⟩
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hp
      · exact hps r hr

/-- Rank and nullity: the rank of the image of `L` under an additive map,
    plus the rank of a list that spans the kernel on the span of `L`, is
    the rank of `L`. -/
theorem rank_nullity (f : Nat → Nat) (hadd : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    (L K : List Nat) (hK : ∀ k ∈ K, inSpanMasks L k) (hker : ∀ k ∈ K, f k = 0)
    (hfull : ∀ v, inSpanMasks L v → f v = 0 → inSpanMasks K v) :
    rankBitmasks (L.map f) + rankBitmasks K = rankBitmasks L := by
  have h0 := additive_zero f hadd
  -- the image has rank at most `rank L - rank K`
  have hupper : rankBitmasks (L.map f) + rankBitmasks K ≤ rankBitmasks L := by
    obtain ⟨new, hnew⟩ := foldl_insertBasis_suffix L (basisOf K)
    have hbasis : basisOf (K ++ L) = new ++ basisOf K := by
      unfold basisOf
      rw [List.foldl_append]
      exact hnew
    have hKL : rankBitmasks (K ++ L) = rankBitmasks L := by
      apply rankBitmasks_eq_of_span_eq
      intro v
      constructor
      · intro hv
        exact inSpanMasks_trans (gen := K ++ L) (pre := L) (fun g hg => by
          rcases List.mem_append.mp hg with hg | hg
          · exact hK g hg
          · exact inSpanMasks_of_mem hg) hv
      · intro hv
        exact inSpanMasks_append_left hv
    have hlen : new.length + rankBitmasks K = rankBitmasks L := by
      rw [← hKL, rankBitmasks_eq_basisOf_length (K ++ L), hbasis, List.length_append]
      rfl
    have himg : ∀ y ∈ L.map f, inSpanMasks (new.map f) y := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      have hx' : inSpanMasks (new ++ basisOf K) x := by
        rw [← hbasis]
        exact (basisOf_span (K ++ L) x).mpr (inSpanMasks_append_left (inSpanMasks_of_mem hx))
      obtain ⟨a, b, ha, hb, rfl⟩ := (inSpanMasks_append_iff new (basisOf K) x).mp hx'
      have hb0 : f b = 0 := additive_span_zero f hadd hker ((basisOf_span K b).mp hb)
      rw [hadd, hb0, Nat.xor_zero]
      exact (inSpanMasks_map_additive_iff f hadd new (f a)).mpr ⟨a, ha, rfl⟩
    have h1 := rankBitmasks_le_of_span himg
    have h2 := rankBitmasks_le_length (new.map f)
    rw [List.length_map] at h2
    omega
  -- `L` lies in the span of preimages of a basis of the image, and `K`
  have hlower : rankBitmasks L ≤ rankBitmasks (L.map f) + rankBitmasks K := by
    obtain ⟨ps, hps, hmap⟩ := exists_preimages f (fun p => inSpanMasks L p)
      (basisOf (L.map f)) (fun y hy => by
        have hy' : inSpanMasks (L.map f) y :=
          (basisOf_span (L.map f) y).mp (inSpanMasks_of_mem hy)
        obtain ⟨a, ha, rfl⟩ := (inSpanMasks_map_additive_iff f hadd L y).mp hy'
        exact ⟨a, ha, rfl⟩)
    have hin : ∀ v ∈ L, inSpanMasks (ps ++ K) v := by
      intro v hv
      have hfv : inSpanMasks (ps.map f) (f v) := by
        rw [hmap]
        exact (basisOf_span (L.map f) (f v)).mpr (inSpanMasks_of_mem (List.mem_map_of_mem hv))
      obtain ⟨a, ha, hfa⟩ := (inSpanMasks_map_additive_iff f hadd ps (f v)).mp hfv
      have haL : inSpanMasks L a := inSpanMasks_trans (gen := ps) (pre := L) hps ha
      have hk : inSpanMasks K (v ^^^ a) := by
        apply hfull
        · exact inSpanMasks_xor (inSpanMasks_of_mem hv) haL
        · rw [hadd, hfa, Nat.xor_self]
      have e : v = a ^^^ (v ^^^ a) := by
        rw [xor3_left_comm, Nat.xor_self, Nat.xor_zero]
      rw [e]
      exact inSpanMasks_xor (inSpanMasks_append_right ha) (inSpanMasks_append_left hk)
    have h1 := rankBitmasks_le_of_span hin
    have h2 := rankBitmasks_append_le ps K
    have h3 := rankBitmasks_le_length ps
    have h4 : ps.length = rankBitmasks (L.map f) := by
      rw [rankBitmasks_eq_basisOf_length, ← hmap, List.length_map]
    omega
  omega

/-! ## Combination by a coefficient mask -/

/-- The combination of `xs` whose coefficients are the bits of `y`. -/
def comb : List Nat → Nat → Nat
  | [], _ => 0
  | x :: xs, y => sel (y.testBit 0) x ^^^ comb xs (y >>> 1)

theorem comb_xor : ∀ (xs : List Nat) (y z : Nat),
    comb xs (y ^^^ z) = comb xs y ^^^ comb xs z
  | [], _, _ => (Nat.xor_self 0).symm
  | x :: xs, y, z => by
      show sel ((y ^^^ z).testBit 0) x ^^^ comb xs ((y ^^^ z) >>> 1) =
        (sel (y.testBit 0) x ^^^ comb xs (y >>> 1)) ^^^
          (sel (z.testBit 0) x ^^^ comb xs (z >>> 1))
      rw [Nat.testBit_xor, sel_xor_bool, Nat.shiftRight_xor_distrib, comb_xor xs,
        xor_interchange]

theorem comb_zero (xs : List Nat) : comb xs 0 = 0 :=
  additive_zero (comb xs) (comb_xor xs)

theorem comb_inSpan : ∀ (xs : List Nat) (y : Nat), inSpanMasks xs (comb xs y)
  | [], _ => inSpanMasks_zero []
  | x :: xs, y => by
      show inSpanMasks (x :: xs) (sel (y.testBit 0) x ^^^ comb xs (y >>> 1))
      apply inSpanMasks_xor
      · cases y.testBit 0
        · exact inSpanMasks_zero _
        · exact inSpanMasks_of_mem (List.mem_cons_self ..)
      · exact inSpanMasks_cons_zero (comb_inSpan xs (y >>> 1))

theorem two_pow_succ_shiftRight (i : Nat) : 2 ^ (i + 1) >>> 1 = 2 ^ i := by
  rw [Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.pow_one,
    Nat.mul_div_cancel _ (by decide : 0 < 2)]

theorem comb_two_pow : ∀ (xs : List Nat) (i : Nat), i < xs.length →
    comb xs (2 ^ i) = xs.getD i 0
  | [], i, h => absurd h (Nat.not_lt_zero i)
  | x :: xs, 0, _ => by
      show sel ((2 ^ 0).testBit 0) x ^^^ comb xs (2 ^ 0 >>> 1) = x
      have h1 : (2 ^ 0 : Nat).testBit 0 = true := by decide
      have h2 : (2 ^ 0 : Nat) >>> 1 = 0 := by decide
      rw [h1, h2, comb_zero, sel_true, Nat.xor_zero]
  | x :: xs, i + 1, h => by
      show sel ((2 ^ (i + 1)).testBit 0) x ^^^ comb xs (2 ^ (i + 1) >>> 1) =
        (x :: xs).getD (i + 1) 0
      have h1 : (2 ^ (i + 1) : Nat).testBit 0 = false := by
        rw [Nat.testBit_two_pow]
        exact decide_eq_false (Nat.succ_ne_zero i)
      rw [h1, two_pow_succ_shiftRight, sel_false, Nat.zero_xor,
        comb_two_pow xs i (Nat.lt_of_succ_lt_succ h)]
      rfl

theorem comb_map_additive (f : Nat → Nat) (hadd : ∀ a b, f (a ^^^ b) = f a ^^^ f b) :
    ∀ (xs : List Nat) (y : Nat), comb (xs.map f) y = f (comb xs y)
  | [], _ => (additive_zero f hadd).symm
  | x :: xs, y => by
      show sel (y.testBit 0) (f x) ^^^ comb (xs.map f) (y >>> 1) =
        f (sel (y.testBit 0) x ^^^ comb xs (y >>> 1))
      rw [hadd, sel_map f (additive_zero f hadd), comb_map_additive f hadd xs]

theorem comb_map_xor {α : Type} (F G : α → Nat) : ∀ (l : List α) (y : Nat),
    comb (l.map (fun i => F i ^^^ G i)) y = comb (l.map F) y ^^^ comb (l.map G) y
  | [], _ => (Nat.xor_self 0).symm
  | a :: l, y => by
      show sel (y.testBit 0) (F a ^^^ G a) ^^^ comb (l.map (fun i => F i ^^^ G i)) (y >>> 1) =
        (sel (y.testBit 0) (F a) ^^^ comb (l.map F) (y >>> 1)) ^^^
          (sel (y.testBit 0) (G a) ^^^ comb (l.map G) (y >>> 1))
      rw [sel_xor_val, comb_map_xor F G l, xor_interchange]

/-- Every member of a span is a combination by some coefficient mask. -/
theorem exists_comb_of_inSpan (xs : List Nat) (v : Nat) (hv : inSpanMasks xs v) :
    ∃ y, comb xs y = v := by
  refine span_induction (P := fun v => ∃ y, comb xs y = v) ⟨0, comb_zero xs⟩ ?_ xs ?_ v hv
  · rintro a b ⟨y, rfl⟩ ⟨z, rfl⟩
    exact ⟨y ^^^ z, comb_xor xs y z⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    refine ⟨2 ^ i, ?_⟩
    rw [comb_two_pow xs i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rfl

/-! ## Unit masks -/

/-- The masks `2 ^ 0, …, 2 ^ (n - 1)`. -/
def unitMasks (n : Nat) : List Nat := (List.range n).map (fun i => 2 ^ i)

theorem length_unitMasks (n : Nat) : (unitMasks n).length = n := by
  unfold unitMasks
  rw [List.length_map, List.length_range]

theorem unitMasks_succ (n : Nat) :
    unitMasks (n + 1) = [1] ++ (unitMasks n).map (· <<< 1) := by
  unfold unitMasks
  rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.map_map]
  show 2 ^ 0 :: _ = 1 :: _
  congr 1
  apply List.map_congr_left
  intro i _
  show 2 ^ (i + 1) = 2 ^ i <<< 1
  rw [Nat.shiftLeft_eq, Nat.pow_succ]

theorem rankBitmasks_singleton_one : rankBitmasks [1] = 1 := by
  apply rankBitmasks_eq_length_of_prefix_indep [1]
  intro l₁ v l₂ h hspan
  cases l₁ with
  | nil =>
      have hv : v = 1 := (List.cons.inj h).1.symm
      rw [hv] at hspan
      exact absurd ((inSpanMasks_nil 1).mp hspan) (by decide)
  | cons a l =>
      have h2 := (List.cons.inj h).2
      cases l with
      | nil => cases h2
      | cons _ _ => cases h2

theorem rank_unitMasks : ∀ n, rankBitmasks (unitMasks n) = n
  | 0 => rfl
  | n + 1 => by
      rw [unitMasks_succ, rankBitmasks_append_shift 1 [1] (unitMasks n), rank_unitMasks n,
        rankBitmasks_singleton_one, Nat.add_comm]
      intro x hx j hj
      rw [List.mem_singleton.mp hx]
      cases j with
      | zero => exact absurd hj (by decide)
      | succ j =>
          rw [Nat.testBit_succ]
          exact Nat.zero_testBit j

theorem below_unitMasks (n : Nat) : ∀ x ∈ unitMasks n, Below n x := by
  intro x hx j hj
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  rw [Nat.testBit_two_pow]
  apply decide_eq_false
  have := List.mem_range.mp hi
  omega

/-- A mask below `2 ^ 1` shifted bit by bit. -/
theorem eq_sel_xor_shift (y : Nat) : y = sel (y.testBit 0) 1 ^^^ ((y >>> 1) <<< 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, testBit_sel, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  cases i with
  | zero =>
      have h1 : (1 : Nat).testBit 0 = true := by decide
      have h2 : decide (0 ≥ 1) = false := by decide
      rw [h1, h2, Bool.and_true, Bool.false_and, Bool.xor_false]
  | succ i =>
      have h1 : (1 : Nat).testBit (i + 1) = false := by
        rw [Nat.testBit_succ]
        exact Nat.zero_testBit i
      have h2 : decide (i + 1 ≥ 1) = true := decide_eq_true (Nat.succ_le_succ (Nat.zero_le i))
      rw [h1, h2, Bool.and_false, Bool.false_xor, Bool.true_and, Nat.add_sub_cancel,
        Nat.add_comm]

/-- Every mask below `2 ^ n` is in the span of the unit masks. -/
theorem inSpan_unitMasks : ∀ (n : Nat) (y : Nat), Below n y → inSpanMasks (unitMasks n) y
  | 0, y, h => by
      rw [eq_zero_of_below_zero h]
      exact inSpanMasks_zero _
  | n + 1, y, h => by
      rw [unitMasks_succ, eq_sel_xor_shift y]
      apply inSpanMasks_xor
      · apply inSpanMasks_append_right
        cases y.testBit 0
        · exact inSpanMasks_zero _
        · exact inSpanMasks_of_mem (List.mem_singleton.mpr rfl)
      · apply inSpanMasks_append_left
        apply (inSpanMasks_map_additive_iff (· <<< 1) (shiftLeft_xor 1) (unitMasks n) _).mpr
        refine ⟨y >>> 1, inSpan_unitMasks n (y >>> 1) ?_, rfl⟩
        intro j hj
        rw [Nat.testBit_shiftRight]
        exact h (1 + j) (by omega)

/-- The image of the unit masks under the combination map is the list. -/
theorem map_comb_unitMasks (xs : List Nat) : (unitMasks xs.length).map (comb xs) = xs := by
  unfold unitMasks
  rw [List.map_map]
  have h : (List.range xs.length).map (comb xs ∘ fun i => 2 ^ i) =
      (List.range xs.length).map (fun i => id (xs.getD i 0)) := by
    apply List.map_congr_left
    intro i hi
    exact comb_two_pow xs i (List.mem_range.mp hi)
  rw [h]
  apply List.ext_getElem
  · rw [List.length_map, List.length_range]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range]
    show xs.getD i 0 = xs[i]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rfl

/-! ## The kernel of the combination map -/

/-- A list spanning the coefficient masks below `2 ^ xs.length` whose
    combination of `xs` is zero. -/
def kerList (xs : List Nat) : List Nat :=
  (spanList (unitMasks xs.length)).filter (fun y => comb xs y == 0)

theorem mem_kerList {xs : List Nat} {y : Nat} (h : y ∈ kerList xs) :
    comb xs y = 0 ∧ Below xs.length y := by
  obtain ⟨hmem, hz⟩ := List.mem_filter.mp h
  refine ⟨Nat.eq_of_beq_eq_true hz, ?_⟩
  exact below_of_inSpan (below_unitMasks xs.length)
    ((spanList_iff_inSpanMasks _ y).mp hmem)

theorem inSpan_kerList {xs : List Nat} {y : Nat} (hy : Below xs.length y)
    (h0 : comb xs y = 0) : inSpanMasks (kerList xs) y := by
  apply inSpanMasks_of_mem
  apply List.mem_filter.mpr
  refine ⟨(spanList_iff_inSpanMasks _ y).mpr (inSpan_unitMasks xs.length y hy), ?_⟩
  rw [h0]
  rfl

/-- The nullity of a mask list: the rank of its kernel list and its own
    rank add up to its length. -/
theorem rank_kerList (xs : List Nat) :
    rankBitmasks (kerList xs) + rankBitmasks xs = xs.length := by
  have h := rank_nullity (comb xs) (comb_xor xs) (unitMasks xs.length) (kerList xs)
    (fun k hk => (spanList_iff_inSpanMasks _ k).mp (List.mem_filter.mp hk).1)
    (fun k hk => (mem_kerList hk).1)
    (fun v hv h0 => inSpan_kerList (below_of_inSpan (below_unitMasks xs.length) hv) h0)
  rw [map_comb_unitMasks, rank_unitMasks] at h
  omega

end CodeCalculus
