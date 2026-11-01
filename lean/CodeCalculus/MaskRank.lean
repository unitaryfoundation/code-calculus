import CodeCalculus.Eval
import CodeCalculus.RebaseRank

namespace CodeCalculus

/-! ### Spans, greedy pivots, and the span-determined rank

The order-independent F₂-span algebra for `inSpanMasks`, the pivot
bookkeeping for the greedy basis that `rankBitmasks` computes, and the two
facts the rebase rank argument needs:

- `rankBitmasks_eq_of_span_eq`: the greedy rank is determined by the F₂ span
  of the mask list. Two pivot-distinct greedy bases of one span have equal
  length, compared through the `spanList` enumeration and a Nodup counting
  lemma — no independence hypothesis on the input list is needed.
- `rebaseMatrix_unit_coeff`: the rank clause of `rebaseMatrix_ok` (a square
  0/1 matrix whose column-position row masks have greedy rank `m`) puts every
  unit mask `2 ^ i`, `i < m`, into the span of the matrix's row masks, so
  each displayed row can be reselected through the rebase matrix.

Statements about these list functions only; no soundness claim for the
calculus is made here (README *Status*). -/

/-! ### Span algebra for `inSpanMasks` -/

/-- XOR is left-commutative (Std exposes `xor_comm` and `xor_assoc` only). -/
theorem xor3_left_comm (a b c : Nat) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← Nat.xor_assoc, ← Nat.xor_assoc, Nat.xor_comm a b]

/-- Zero is in every span. -/
theorem inSpanMasks_zero (xs : List Nat) : inSpanMasks xs 0 := by
  refine ⟨List.replicate xs.length 0, ?_, ?_, ?_⟩
  · rw [List.length_replicate]
  · intro c hc
    exact Or.inl (List.mem_replicate.mp hc).2
  · exact combineMasks_zero_coeffs xs (List.replicate xs.length 0)
      (fun c hc => (List.mem_replicate.mp hc).2)

/-- Prefixing a generator with coefficient zero preserves span membership. -/
theorem inSpanMasks_cons_zero {a v : Nat} {xs : List Nat} (h : inSpanMasks xs v) :
    inSpanMasks (a :: xs) v := by
  rcases h with ⟨cs, hlen, h01, hval⟩
  refine ⟨0 :: cs, by simp [hlen], ?_, ?_⟩
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Or.inl rfl
    · exact h01 c hc
  · rw [combineMasks_cons]
    simpa using hval

/-- A span is closed under XOR. -/
theorem inSpanMasks_xor {u v : Nat} {xs : List Nat}
    (hu : inSpanMasks xs u) (hv : inSpanMasks xs v) :
    inSpanMasks xs (u ^^^ v) := by
  rcases hu with ⟨ca, hlena, h01a, hva⟩
  rcases hv with ⟨cb, hlenb, h01b, hvb⟩
  refine ⟨List.zipWith (· ^^^ ·) ca cb, ?_, ?_, ?_⟩
  · rw [List.length_zipWith, hlena, hlenb, Nat.min_self]
  · intro c hc
    rcases mem_zipWith_xor ca cb c hc with ⟨x, hx, y, hy, hxy⟩
    rw [hxy]
    exact xor_mem01 (h01a x hx) (h01b y hy)
  · rw [combineMasks_zipWith_xor xs ca cb hlena hlenb h01a h01b, hva, hvb]

/-- Span membership is transitive through a generating list. -/
theorem inSpanMasks_trans {gen pre : List Nat}
    (hgen : ∀ g, g ∈ gen → inSpanMasks pre g) :
    ∀ {v : Nat}, inSpanMasks gen v → inSpanMasks pre v := by
  induction gen with
  | nil =>
      intro v hv
      rw [inSpanMasks_nil] at hv
      subst v
      exact inSpanMasks_zero pre
  | cons g gs ih =>
      intro v hv
      rcases hv with ⟨cs, hlen, h01, hval⟩
      cases cs with
      | nil => simp at hlen
      | cons c cs =>
          have hg : inSpanMasks pre g := hgen g (by simp)
          have hgs : ∀ x, x ∈ gs → inSpanMasks pre x := by
            intro x hx
            exact hgen x (by simp [hx])
          have hcs01 : ∀ x, x ∈ cs → x = 0 ∨ x = 1 := by
            intro x hx
            exact h01 x (by simp [hx])
          have hlen' : cs.length = gs.length := by simpa using hlen
          have hrest : inSpanMasks pre (combineMasks gs cs) :=
            ih hgs ⟨cs, hlen', hcs01, rfl⟩
          rw [combineMasks_cons] at hval
          by_cases hc1 : c = 1
          · simp only [hc1, reduceIte] at hval
            rw [← hval]
            exact inSpanMasks_xor hg hrest
          · simp only [hc1, reduceIte, Nat.zero_xor] at hval
            rw [← hval]
            exact hrest

/-- Membership of a generator in its own span. -/
theorem inSpanMasks_of_mem {xs : List Nat} {x : Nat} (h : x ∈ xs) :
    inSpanMasks xs x := by
  induction xs with
  | nil => cases h
  | cons a as ih =>
      rcases List.mem_cons.mp h with rfl | h
      · refine ⟨1 :: List.replicate as.length 0, ?_, ?_, ?_⟩
        · simp
        · intro c hc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact Or.inr rfl
          · exact Or.inl (List.mem_replicate.mp hc).2
        · rw [combineMasks_cons, combineMasks_zero_coeffs]
          · simp
          · intro c hc
            exact (List.mem_replicate.mp hc).2
      · exact inSpanMasks_cons_zero (a := a) (ih h)

/-- `combineMasks` splits across an append of the mask list and of the
    coefficient list. -/
theorem combineMasks_append (xs ys : List Nat) :
    ∀ (cs ds : List Nat), cs.length = xs.length →
      combineMasks (xs ++ ys) (cs ++ ds)
        = combineMasks xs cs ^^^ combineMasks ys ds := by
  induction xs with
  | nil =>
      intro cs ds hlen
      cases cs with
      | nil => simp [combineMasks_nil]
      | cons c cs => simp at hlen
  | cons a as ih =>
      intro cs ds hlen
      cases cs with
      | nil => simp at hlen
      | cons c cs =>
          have hlen' : cs.length = as.length := by simpa using hlen
          rw [List.cons_append, List.cons_append, combineMasks_cons, combineMasks_cons,
            ih cs ds hlen']
          rw [Nat.xor_assoc]

/-- Adding trailing generators with coefficient zero preserves membership. -/
theorem inSpanMasks_append_right {pre zs : List Nat} {v : Nat}
    (h : inSpanMasks pre v) : inSpanMasks (pre ++ zs) v := by
  rcases h with ⟨cs, hlen, h01, hval⟩
  refine ⟨cs ++ List.replicate zs.length 0, ?_, ?_, ?_⟩
  · simp [hlen]
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h01 c hc
    · exact Or.inl (List.mem_replicate.mp hc).2
  · rw [combineMasks_append pre zs cs (List.replicate zs.length 0) hlen,
        combineMasks_zero_coeffs zs (List.replicate zs.length 0)
          (fun c hc => (List.mem_replicate.mp hc).2),
        hval, Nat.xor_zero]

/-- Swapping two adjacent generators preserves span membership. -/
theorem inSpanMasks_swap_fwd (a b : Nat) (l : List Nat) (v : Nat) :
    inSpanMasks (a :: b :: l) v → inSpanMasks (b :: a :: l) v := by
  rintro ⟨cs, hlen, h01, hval⟩
  cases cs with
  | nil => simp at hlen
  | cons c cs =>
      cases cs with
      | nil => simp at hlen
      | cons d ds =>
          have hds : ds.length = l.length := by simpa using hlen
          refine ⟨d :: c :: ds, by simp [hds], ?_, ?_⟩
          · intro x' hx'
            simp only [List.mem_cons] at hx'
            rcases hx' with rfl | rfl | hx'
            · exact h01 _ (by simp)
            · exact h01 _ (by simp)
            · exact h01 _ (by simp [hx'])
          · rw [combineMasks_cons, combineMasks_cons] at hval
            rw [combineMasks_cons, combineMasks_cons]
            rw [← hval]
            exact (xor3_left_comm (if c = 1 then a else 0)
              (if d = 1 then b else 0) (combineMasks l ds)).symm

theorem inSpanMasks_swap (a b : Nat) (l : List Nat) (v : Nat) :
    inSpanMasks (a :: b :: l) v ↔ inSpanMasks (b :: a :: l) v :=
  ⟨inSpanMasks_swap_fwd a b l v, inSpanMasks_swap_fwd b a l v⟩

/-- Membership transfers along a permutation. -/
theorem perm_mem {xs ys : List Nat} (p : List.Perm xs ys) {a : Nat} (h : a ∈ xs) :
    a ∈ ys := by
  induction p with
  | nil => cases h
  | cons x p ih =>
      rcases List.mem_cons.mp h with rfl | h
      · simp
      · simp [ih h]
  | swap x y l =>
      rcases List.mem_cons.mp h with h1 | h'
      · subst h1
        simp
      · rcases List.mem_cons.mp h' with h1 | h2
        · simp [h1]
        · exact List.mem_cons_of_mem x (List.mem_cons_of_mem y h2)
  | trans p q ihp ihq => exact ihq (ihp h)

/-- Span membership is invariant under permutation of the generating list. -/
theorem inSpanMasks_perm {xs ys : List Nat} (p : List.Perm xs ys) :
    ∀ v : Nat, inSpanMasks xs v ↔ inSpanMasks ys v := by
  induction p with
  | nil => intro v; exact Iff.rfl
  | cons x p ih =>
      rename_i l1 l2
      intro v
      constructor
      · rintro ⟨cs, hlen, h01, hval⟩
        cases cs with
        | nil => simp at hlen
        | cons c cs =>
            have hlen' : cs.length = l1.length := by simpa using hlen
            have hcs01 : ∀ y, y ∈ cs → y = 0 ∨ y = 1 := fun y hy => h01 y (by simp [hy])
            have hrest : inSpanMasks l2 (combineMasks l1 cs) :=
              (ih _).mp ⟨cs, hlen', hcs01, rfl⟩
            rw [combineMasks_cons] at hval
            by_cases hc1 : c = 1
            · simp only [hc1, reduceIte] at hval
              rw [← hval]
              exact inSpanMasks_xor (inSpanMasks_of_mem (by simp))
                (inSpanMasks_cons_zero hrest)
            · simp only [hc1, reduceIte, Nat.zero_xor] at hval
              rw [← hval]
              exact inSpanMasks_cons_zero hrest
      · rintro ⟨cs, hlen, h01, hval⟩
        cases cs with
        | nil => simp at hlen
        | cons c cs =>
            have hlen' : cs.length = l2.length := by simpa using hlen
            have hcs01 : ∀ y, y ∈ cs → y = 0 ∨ y = 1 := fun y hy => h01 y (by simp [hy])
            have hrest : inSpanMasks l1 (combineMasks l2 cs) :=
              (ih _).mpr ⟨cs, hlen', hcs01, rfl⟩
            rw [combineMasks_cons] at hval
            by_cases hc1 : c = 1
            · simp only [hc1, reduceIte] at hval
              rw [← hval]
              exact inSpanMasks_xor (inSpanMasks_of_mem (by simp))
                (inSpanMasks_cons_zero hrest)
            · simp only [hc1, reduceIte, Nat.zero_xor] at hval
              rw [← hval]
              exact inSpanMasks_cons_zero hrest
  | swap x y l => intro v; exact inSpanMasks_swap y x l v
  | trans p q ihp ihq => intro v; exact (ihp v).trans (ihq v)

/-! ### Greedy reduction -/

/-- The insertion sort used by `reduceByBasis` is a permutation. -/
theorem insertByPivot_perm (b : Nat) (bs : List Nat) :
    List.Perm (insertByPivot b bs) (b :: bs) := by
  induction bs with
  | nil => simp [insertByPivot]
  | cons c cs ih =>
      unfold insertByPivot
      split
      · simp
      · exact (List.Perm.cons c ih).trans (List.Perm.swap b c cs)

theorem insertByPivot_mem (b : Nat) (bs : List Nat) :
    ∀ x, x ∈ insertByPivot b bs → x = b ∨ x ∈ bs := by
  induction bs with
  | nil =>
      intro x hx
      simp only [insertByPivot, List.mem_singleton] at hx
      exact Or.inl hx
  | cons c cs ih =>
      unfold insertByPivot
      split
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (by simp [hx])
      · rename_i h
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact Or.inr (by simp)
        · rcases ih x hx with h' | h'
          · exact Or.inl h'
          · exact Or.inr (by simp [h'])

theorem sortByPivotDesc_perm (bs : List Nat) :
    List.Perm (sortByPivotDesc bs) bs := by
  have foldPerm (xs acc : List Nat) :
      List.Perm (xs.foldl (fun out b => insertByPivot b out) acc)
        (xs.reverse ++ acc) := by
    induction xs generalizing acc with
    | nil => simp
    | cons b xs ih =>
        simp only [List.foldl_cons]
        apply List.Perm.trans (ih (insertByPivot b acc))
        simpa [List.reverse_cons, List.append_assoc] using
          (List.Perm.append_left xs.reverse (insertByPivot_perm b acc))
  have h := foldPerm bs []
  simp only [List.append_nil] at h
  simpa [sortByPivotDesc] using h.trans (List.reverse_perm bs)

theorem sortByPivotDesc_mem (bs : List Nat) {x : Nat} (h : x ∈ sortByPivotDesc bs) :
    x ∈ bs :=
  perm_mem (sortByPivotDesc_perm bs) h

/-- The single reduction step used by `reduceByBasis`. -/
def reduceStep (acc b : Nat) : Nat :=
  if b ≠ 0 && (acc >>> Nat.log2 b) &&& 1 = 1 then acc ^^^ b else acc

theorem reduceByBasis_eq_fold (basis : List Nat) (x : Nat) :
    reduceByBasis basis x = (sortByPivotDesc basis).foldl reduceStep x := rfl

theorem reduceStep_eq_or (acc b : Nat) :
    reduceStep acc b = acc ∨ reduceStep acc b = acc ^^^ b := by
  unfold reduceStep
  split <;> simp

/-- The reduction condition reads the pivot bit of the accumulator. -/
theorem reduceStep_condition (acc b : Nat) :
    ((acc >>> Nat.log2 b) &&& 1 = 1) ↔ acc.testBit (Nat.log2 b) = true := by
  constructor
  · intro h
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have hmod : (acc >>> Nat.log2 b) % 2 = 1 := by rw [← Nat.and_one_is_mod]; exact h
    rw [Nat.shiftRight_eq_div_pow] at hmod
    simpa using hmod
  · intro h
    have hmod : acc / 2 ^ Nat.log2 b % 2 = 1 := by
      rw [Nat.testBit_eq_decide_div_mod_eq] at h
      simpa using h
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
    exact hmod

/-- After one reduction step by a nonzero `b`, the pivot bit of `b` is
    clear. -/
theorem reduceStep_pivot_clear {b : Nat} (hb : b ≠ 0) (acc : Nat) :
    (reduceStep acc b).testBit (Nat.log2 b) = false := by
  unfold reduceStep
  simp only [reduceStep_condition]
  split
  · rename_i h
    have hbit : acc.testBit (Nat.log2 b) = true := by
      rw [Bool.and_eq_true] at h
      simpa using h.2
    rw [Nat.testBit_xor, Nat.testBit_log2 hb, hbit]
    simp
  · rename_i h
    have hbit : acc.testBit (Nat.log2 b) = false := by
      rw [Bool.and_eq_true] at h
      simp at h
      exact h hb
    rw [hbit]

/-- A reduction step by `b` does not touch bits above the pivot of `b`. -/
theorem reduceStep_above (acc b j : Nat) (hj : Nat.log2 b < j) :
    (reduceStep acc b).testBit j = acc.testBit j := by
  unfold reduceStep
  simp only [reduceStep_condition]
  split
  · have hbj : b.testBit j = false := by
      by_cases hb : b = 0
      · subst hb; exact testBit_zero_all j
      · exact Nat.testBit_lt_two_pow ((Nat.log2_lt hb).mp hj)
    rw [Nat.testBit_xor, hbj]
    simp
  · rfl

/-- Running the reduction over a whole basis preserves bits above every
    pivot in the basis. -/
theorem reduceFold_above (bs : List Nat) :
    ∀ (x j : Nat), (∀ b ∈ bs, Nat.log2 b < j) →
      (bs.foldl reduceStep x).testBit j = x.testBit j := by
  induction bs with
  | nil => intro x j _; rfl
  | cons b bs ih =>
      intro x j h
      rw [List.foldl_cons, ih (reduceStep x b) j (fun b' hb' => h b' (by simp [hb']))]
      exact reduceStep_above x b j (h b (by simp))

/-- Running the reduction over a pivot-sorted nonzero basis clears every
    pivot bit of the basis: later pivots are strictly smaller, so cleared
    bits stay clear. -/
theorem reduceFold_pivots_clear (bs : List Nat) :
    ∀ (x j : Nat), bs.Pairwise (fun a b => Nat.log2 a > Nat.log2 b) →
      (∀ b ∈ bs, b ≠ 0) → j ∈ bs.map Nat.log2 →
      (bs.foldl reduceStep x).testBit j = false := by
  induction bs with
  | nil => intro x j _ _ hj; simp at hj
  | cons b bs ih =>
      intro x j hpair hne hj
      have hp : (∀ y, y ∈ bs → Nat.log2 b > Nat.log2 y) ∧
          bs.Pairwise (fun a b => Nat.log2 a > Nat.log2 b) :=
        List.pairwise_cons.mp hpair
      rcases List.mem_map.mp hj with ⟨y, hy, hyj⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · subst hyj
        rw [List.foldl_cons, reduceFold_above bs (reduceStep x y) (y.log2)
          (fun b' hb' => hp.1 b' (by simp [hb']))]
        exact reduceStep_pivot_clear (hne y (by simp)) x
      · exact ih (reduceStep x b) j hp.2 (fun b' hb' => hne b' (by simp [hb']))
          (List.mem_map.mpr ⟨y, hy, hyj⟩)

/-! ### Bit facts -/

theorem lt_two_pow_of_log2_lt {x y : Nat} (hx : x ≠ 0) (h : Nat.log2 x < Nat.log2 y) :
    x < 2 ^ Nat.log2 y := by
  by_cases hge : 2 ^ Nat.log2 y ≤ x
  · exact absurd ((Nat.le_log2 hx).mpr hge) (Nat.not_le.mpr h)
  · omega

theorem log2_lt_of_lt_two_pow {x m : Nat} (hx : x ≠ 0) (h : x < 2 ^ m) :
    Nat.log2 x < m := by
  by_cases hge : m ≤ Nat.log2 x
  · have hle : 2 ^ m ≤ x :=
      Nat.le_trans (Nat.pow_le_pow_right (by decide) hge) (Nat.log2_self_le hx)
    omega
  · omega

theorem lt_two_pow_of_high_bits_false (x m : Nat)
    (h : ∀ j : Nat, m ≤ j → x.testBit j = false) : x < 2 ^ m := by
  by_cases hx : x = 0
  · subst x; exact Nat.two_pow_pos m
  · by_cases hge : 2 ^ m ≤ x
    · obtain ⟨j, hj, hbit⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow hge
      exact absurd (h j hj) (by simp [hbit])
    · omega

theorem two_pow_lt_two_pow {a b : Nat} (h : a < b) : 2 ^ a < 2 ^ b := by
  have hpos : 2 ^ a > 0 := Nat.two_pow_pos a
  have h1 : 2 ^ (a + 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) (by omega)
  rw [Nat.pow_succ] at h1
  omega

/-! ### Pivot bookkeeping -/

/-- Basis masks with strictly decreasing `Nat.log2` pivots. -/
def PivotSorted (bs : List Nat) : Prop :=
  bs.Pairwise (fun a b => Nat.log2 a > Nat.log2 b)

/-- Nonzero basis masks with distinct `Nat.log2` pivots. -/
def PivotDistinct (bs : List Nat) : Prop :=
  (∀ b ∈ bs, b ≠ 0) ∧ (bs.map Nat.log2).Nodup

theorem pivotDistinct_nil : PivotDistinct [] := by
  constructor
  · intro b hb; cases hb
  · simp

/-- Inserting one mask into a `≥`-descending basis keeps the basis
    `≥`-descending. -/
theorem insertByPivot_pairwiseGE (b : Nat) (acc : List Nat)
    (hs : acc.Pairwise (fun a b => Nat.log2 a ≥ Nat.log2 b)) :
    (insertByPivot b acc).Pairwise (fun a b => Nat.log2 a ≥ Nat.log2 b) := by
  induction acc with
  | nil => simp [insertByPivot]
  | cons c cs ih =>
      unfold insertByPivot
      split
      · rename_i hge
        rw [List.pairwise_cons]
        refine ⟨?_, hs⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact hge
        · have hge2 := (List.pairwise_cons.mp hs).1 y hy'
          omega
      · rename_i hlt
        rw [List.pairwise_cons]
        refine ⟨?_, ih (List.pairwise_cons.mp hs).2⟩
        intro y hy
        rcases insertByPivot_mem b cs y hy with rfl | hy'
        · omega
        · exact (List.pairwise_cons.mp hs).1 y hy'

theorem sortByPivotDesc_pairwiseGE_mem (bs : List Nat) :
    (sortByPivotDesc bs).Pairwise (fun a b => Nat.log2 a ≥ Nat.log2 b) ∧
      (∀ x ∈ sortByPivotDesc bs, x ∈ bs) := by
  have fold : ∀ (xs acc : List Nat), (∀ b ∈ xs, b ∈ bs) →
      acc.Pairwise (fun a b => Nat.log2 a ≥ Nat.log2 b) → (∀ x ∈ acc, x ∈ bs) →
      ((xs.foldl (fun out b => insertByPivot b out) acc).Pairwise
          (fun a b => Nat.log2 a ≥ Nat.log2 b) ∧
        (∀ x ∈ xs.foldl (fun out b => insertByPivot b out) acc, x ∈ bs)) := by
    intro xs
    induction xs with
    | nil => intro acc _ hs hmem; exact ⟨hs, hmem⟩
    | cons b xs ih =>
        intro acc hxbs hs hmem
        rw [List.foldl_cons]
        exact ih (insertByPivot b acc)
          (fun b' hb' => hxbs b' (by simp [hb']))
          (insertByPivot_pairwiseGE b acc hs)
          (fun x hx => by
            rcases insertByPivot_mem b acc x hx with hx' | hx'
            · subst x; exact hxbs b (by simp)
            · exact hmem x hx')
  rw [sortByPivotDesc]
  exact fold bs [] (fun b hb => hb) (by simp) (by simp)

theorem map_log2_nodup_of_perm {xs ys : List Nat} (p : List.Perm xs ys)
    (hd : (xs.map Nat.log2).Nodup) : (ys.map Nat.log2).Nodup := by
  have hp : List.Perm (xs.map Nat.log2) (ys.map Nat.log2) := p.map Nat.log2
  rw [List.nodup_iff_pairwise_ne] at hd ⊢
  exact hp.pairwise_iff (fun h => h.symm) |>.mp hd

/-- A `≥`-descending list with duplicate-free `log2`-map is strictly
    descending: the head's pivot is shared by no tail member. -/
theorem pairwiseGE_strict {bs : List Nat}
    (hge : bs.Pairwise (fun a b => Nat.log2 a ≥ Nat.log2 b))
    (hd : (bs.map Nat.log2).Nodup) :
    bs.Pairwise (fun a b => Nat.log2 a > Nat.log2 b) := by
  induction bs with
  | nil => constructor
  | cons b bs ih =>
      have hp : (∀ y, y ∈ bs → Nat.log2 b ≥ Nat.log2 y) ∧
          bs.Pairwise (fun a b => Nat.log2 a ≥ Nat.log2 b) := List.pairwise_cons.mp hge
      have hdn : (Nat.log2 b :: bs.map Nat.log2).Nodup := by
        simpa [List.map_cons] using hd
      have hnotin : Nat.log2 b ∉ bs.map Nat.log2 := (List.nodup_cons.mp hdn).1
      rw [List.pairwise_cons]
      refine ⟨?_, ih hp.2 (List.nodup_cons.mp hdn).2⟩
      intro y hy
      have hne : Nat.log2 b ≠ Nat.log2 y := by
        intro he
        exact hnotin (List.mem_map.mpr ⟨y, hy, he.symm⟩)
      have hgey := hp.1 y hy
      omega

theorem sortByPivotDesc_pivotSorted (bs : List Nat) (_hne : ∀ b ∈ bs, b ≠ 0)
    (hd : (bs.map Nat.log2).Nodup) : PivotSorted (sortByPivotDesc bs) := by
  have h1 := sortByPivotDesc_pairwiseGE_mem bs
  have h2 := map_log2_nodup_of_perm (sortByPivotDesc_perm bs).symm hd
  exact pairwiseGE_strict h1.1 h2

/-- Inserting a mask into a pivot-distinct basis keeps the basis
    pivot-distinct: the reduced mask has every basis pivot bit clear, so its
    own pivot is fresh. -/
theorem insertBasis_pivotDistinct (basis : List Nat) (x : Nat)
    (hd : PivotDistinct basis) : PivotDistinct (insertBasis basis x) := by
  by_cases h : reduceByBasis basis x = 0
  · have hins : insertBasis basis x = basis := by simp [insertBasis, h]
    rw [hins]
    exact hd
  · have hins : insertBasis basis x = reduceByBasis basis x :: basis := by
      simp [insertBasis, h]
    rw [hins]
    refine ⟨?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact h
      · exact hd.1 y hy'
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, hd.2⟩
      intro hmem
      obtain ⟨b, hb, hlog⟩ := List.mem_map.mp hmem
      have hclr : ∀ b' ∈ basis, (reduceByBasis basis x).testBit (Nat.log2 b') = false := by
        intro b' hb'
        rw [reduceByBasis_eq_fold]
        exact reduceFold_pivots_clear (sortByPivotDesc basis) x (Nat.log2 b')
          (sortByPivotDesc_pivotSorted basis hd.1 hd.2)
          (fun b'' hb'' => hd.1 b'' (sortByPivotDesc_mem basis hb''))
          (by
            have hmb : Nat.log2 b' ∈ basis.map Nat.log2 := List.mem_map.mpr ⟨b', hb', rfl⟩
            have := perm_mem ((sortByPivotDesc_perm basis).symm.map Nat.log2) hmb
            simpa using this)
      have hclr' := hclr b hb
      rw [hlog] at hclr'
      rw [Nat.testBit_log2 h] at hclr'
      exact absurd hclr' (by decide)

theorem foldl_insertBasis_pivotDistinct (xs : List Nat) :
    ∀ acc : List Nat, PivotDistinct acc → PivotDistinct (xs.foldl insertBasis acc) := by
  induction xs with
  | nil => intro acc h; exact h
  | cons x xs ih =>
      intro acc h
      rw [List.foldl_cons]
      exact ih (insertBasis acc x) (insertBasis_pivotDistinct acc x h)

/-! ### Independence of pivot bases -/

/-- A combination of masks whose bits at `j` are all clear has a clear bit
    `j`. -/
theorem combineMasks_testBit_false (gens : List Nat) :
    ∀ (cs : List Nat) (j : Nat), (∀ x ∈ gens, x.testBit j = false) →
      (combineMasks gens cs).testBit j = false := by
  induction gens with
  | nil => intro cs j _; rw [combineMasks_nil, testBit_zero_all]
  | cons g gs ih =>
      intro cs j h
      cases cs with
      | nil => simp [combineMasks]
      | cons c cs' =>
          rw [combineMasks_cons, Nat.testBit_xor]
          have hg : g.testBit j = false := h g (by simp)
          have hgs := ih cs' j (fun x hx => h x (by simp [hx]))
          by_cases hc1 : c = 1
          · simp only [hc1, reduceIte, hg]
            simp [hgs]
          · simp only [hc1, reduceIte, testBit_zero_all]
            simp [hgs]

/-- A pivot-sorted nonzero mask list is independent: the head of a
    descending list has the largest selected pivot, and no other selected
    mask touches that bit. -/
theorem independentMasks_of_pivotSorted : ∀ (bs : List Nat),
    PivotSorted bs → (∀ b ∈ bs, b ≠ 0) → independentMasks bs := by
  intro bs
  induction bs with
  | nil =>
      intro _ _ cs hlen _ _
      cases cs with
      | nil => intro c hc; cases hc
      | cons c cs' => simp at hlen
  | cons b bs ih =>
      intro hpair hne cs hlen h01 hval
      have hp : (∀ y, y ∈ bs → Nat.log2 b > Nat.log2 y) ∧
          bs.Pairwise (fun a b => Nat.log2 a > Nat.log2 b) :=
        List.pairwise_cons.mp hpair
      cases cs with
      | nil => intro d hd; cases hd
      | cons c cs' =>
          have hlen' : cs'.length = bs.length := by simpa using hlen
          have h01' : ∀ d ∈ cs', d = 0 ∨ d = 1 := fun d hd => h01 d (by simp [hd])
          rw [combineMasks_cons] at hval
          by_cases hc1 : c = 1
          · exfalso
            simp [hc1] at hval
            have hbx : b = combineMasks bs cs' := xor_eq_zero_cancel hval
            have hclr : (combineMasks bs cs').testBit (Nat.log2 b) = false :=
              combineMasks_testBit_false bs cs' (Nat.log2 b) (fun x hx =>
                Nat.testBit_lt_two_pow
                  (lt_two_pow_of_log2_lt (hne x (List.mem_cons_of_mem _ hx)) (hp.1 x hx)))
            rw [← hbx, Nat.testBit_log2 (hne b (List.mem_cons_self ..))] at hclr
            exact absurd hclr (by decide)
          · have hc0 : c = 0 := by
              rcases h01 c (by simp) with h0 | h1
              · exact h0
              · exact absurd hc1 (by simp [h1])
            simp [hc0] at hval
            have hall := ih hp.2 (fun x hx => hne x (List.mem_cons_of_mem _ hx)) cs'
              hlen' h01' hval
            intro d hd
            rcases List.mem_cons.mp hd with rfl | hd
            · exact hc0
            · exact hall d hd

/-- A zero combination transfers along a permutation of the generators,
    keeping a witness coefficient of `1`. -/
theorem combineMasks_perm_corr : ∀ {xs ys : List Nat}, List.Perm xs ys →
    ∀ cs : List Nat, cs.length = xs.length → (∀ c ∈ cs, c = 0 ∨ c = 1) →
      ∃ ds : List Nat, ds.length = ys.length ∧ (∀ d ∈ ds, d = 0 ∨ d = 1) ∧
        combineMasks ys ds = combineMasks xs cs ∧
        ((∃ c ∈ cs, c = 1) ↔ (∃ d ∈ ds, d = 1)) := by
  intro xs ys p
  induction p with
  | nil =>
      intro cs hlen _
      cases cs with
      | nil => exact ⟨[], rfl, fun d hd => absurd hd List.not_mem_nil, rfl, Iff.rfl⟩
      | cons c cs' => simp at hlen
  | cons x p ih =>
      rename_i l1 l2
      intro cs hlen h01
      cases cs with
      | nil => simp at hlen
      | cons c cs' =>
          have hlen' : cs'.length = l1.length := by simpa using hlen
          have h01' : ∀ d ∈ cs', d = 0 ∨ d = 1 := fun d hd => h01 d (by simp [hd])
          obtain ⟨ds', hdlen', hd01', hdval', hd1'⟩ := ih cs' hlen' h01'
          refine ⟨c :: ds', by simp [hdlen'], ?_, ?_, ?_⟩
          · intro d hd
            rcases List.mem_cons.mp hd with rfl | hd
            · exact h01 d (by simp)
            · exact hd01' d hd
          · rw [combineMasks_cons, combineMasks_cons, hdval']
          · constructor
            · rintro ⟨e, he, he1⟩
              rcases List.mem_cons.mp he with rfl | he
              · exact ⟨e, by simp, he1⟩
              · obtain ⟨d, hd, hd1⟩ := hd1'.mp ⟨e, he, he1⟩
                exact ⟨d, by simp [hd], hd1⟩
            · rintro ⟨d, hd, hd1⟩
              rcases List.mem_cons.mp hd with rfl | hd
              · exact ⟨d, by simp, hd1⟩
              · obtain ⟨e, he, he1⟩ := hd1'.mpr ⟨d, hd, hd1⟩
                exact ⟨e, by simp [he], he1⟩
  | swap x y l =>
      intro cs hlen h01
      cases cs with
      | nil => simp at hlen
      | cons c₁ cs' =>
          cases cs' with
          | nil => simp at hlen
          | cons c₂ cs'' =>
              have hlen'' : cs''.length = l.length := by simpa using hlen
              have h01'' : ∀ d ∈ cs'', d = 0 ∨ d = 1 := fun d hd => h01 d (by simp [hd])
              refine ⟨c₂ :: c₁ :: cs'', by simp [hlen''], ?_, ?_, ?_⟩
              · intro d hd
                simp only [List.mem_cons] at hd
                rcases hd with rfl | rfl | hd
                · exact h01 d (by simp)
                · exact h01 d (by simp)
                · exact h01'' d hd
              · rw [combineMasks_cons, combineMasks_cons, combineMasks_cons,
                  combineMasks_cons, xor3_left_comm]
              · constructor
                · rintro ⟨e, he, he1⟩
                  simp only [List.mem_cons] at he
                  rcases he with rfl | rfl | he
                  · exact ⟨e, by simp, he1⟩
                  · exact ⟨e, by simp, he1⟩
                  · exact ⟨e, by simp [he], he1⟩
                · rintro ⟨d, hd, hd1⟩
                  simp only [List.mem_cons] at hd
                  rcases hd with rfl | rfl | hd
                  · exact ⟨d, by simp, hd1⟩
                  · exact ⟨d, by simp, hd1⟩
                  · exact ⟨d, by simp [hd], hd1⟩
  | trans p q ihp ihq =>
      rename_i xs ys zs
      intro cs hlen h01
      obtain ⟨ds, hdlen, hd01, hdval, hd1⟩ := ihp cs hlen h01
      obtain ⟨es, helen, he01, heval, he1⟩ := ihq ds hdlen hd01
      exact ⟨es, helen, he01, by rw [heval, hdval], hd1.trans he1⟩

theorem independentMasks_perm {xs ys : List Nat} (p : List.Perm xs ys) :
    independentMasks xs ↔ independentMasks ys := by
  have forward : ∀ {us vs : List Nat}, List.Perm us vs →
      independentMasks us → independentMasks vs := by
    intro us vs p' hind cs hlen h01 hval
    by_cases h1 : ∃ c ∈ cs, c = 1
    · exfalso
      obtain ⟨ds, hdlen, hd01, hdval, hd1⟩ := combineMasks_perm_corr p'.symm cs hlen h01
      have hall := hind ds hdlen hd01 (by rw [hdval]; exact hval)
      obtain ⟨d, hd, hdne⟩ := hd1.mp h1
      exact absurd (hall d hd) (by simp [hdne])
    · intro c hc
      rcases h01 c hc with h0 | h11
      · exact h0
      · exact absurd ⟨c, hc, h11⟩ h1
  exact ⟨forward p, forward p.symm⟩

theorem independentMasks_pivotDistinct (bs : List Nat) (h : PivotDistinct bs) :
    independentMasks bs := by
  have hs := independentMasks_of_pivotSorted (sortByPivotDesc bs)
    (sortByPivotDesc_pivotSorted bs h.1 h.2) (fun b hb => h.1 b (sortByPivotDesc_mem bs hb))
  exact (independentMasks_perm (sortByPivotDesc_perm bs)).mp hs

/-! ### Span equality through insertion -/

theorem reduceFold_exists (bs : List Nat) :
    ∀ (x : Nat), ∃ v', inSpanMasks bs v' ∧ (bs.foldl reduceStep x) = x ^^^ v' := by
  induction bs with
  | nil =>
      intro x
      refine ⟨0, inSpanMasks_zero [], ?_⟩
      rw [Nat.xor_zero]
      rfl
  | cons b bs ih =>
      intro x
      obtain ⟨v', hv', heq⟩ := ih (reduceStep x b)
      have hfold : (b :: bs).foldl reduceStep x = reduceStep x b ^^^ v' := by
        rw [List.foldl_cons, heq]
      rcases reduceStep_eq_or x b with h | h
      · rw [hfold, h]
        exact ⟨v', inSpanMasks_cons_zero hv', rfl⟩
      · rw [hfold, h]
        refine ⟨b ^^^ v',
          inSpanMasks_xor (inSpanMasks_of_mem (List.mem_cons_self ..))
            (inSpanMasks_cons_zero hv'), ?_⟩
        exact Nat.xor_assoc x b v'

/-- `reduceByBasis` differs from its input by an element of the span of the
    basis. -/
theorem reduceByBasis_sound (acc : List Nat) (x : Nat) :
    ∃ v', inSpanMasks acc v' ∧ reduceByBasis acc x = x ^^^ v' := by
  obtain ⟨v', hv', heq⟩ := reduceFold_exists (sortByPivotDesc acc) x
  exact ⟨v', (inSpanMasks_perm (sortByPivotDesc_perm acc) v').mp hv',
    by rw [reduceByBasis_eq_fold]; exact heq⟩

theorem spanEq_insertBasis (acc : List Nat) (x : Nat) (v : Nat) :
    inSpanMasks (insertBasis acc x) v ↔ inSpanMasks (x :: acc) v := by
  by_cases h : reduceByBasis acc x = 0
  · have hins : insertBasis acc x = acc := by simp [insertBasis, h]
    rw [hins]
    constructor
    · intro hv; exact inSpanMasks_cons_zero hv
    · intro hv
      refine inSpanMasks_trans (fun g hg => ?_) hv
      rcases List.mem_cons.mp hg with rfl | hg'
      · obtain ⟨v', hv', hx⟩ := reduceByBasis_sound acc g
        rw [h] at hx
        rw [xor_eq_zero_cancel hx.symm]
        exact hv'
      · exact inSpanMasks_of_mem hg'
  · have hins : insertBasis acc x = reduceByBasis acc x :: acc := by
      simp [insertBasis, h]
    rw [hins]
    obtain ⟨v', hv', hx⟩ := reduceByBasis_sound acc x
    constructor
    · intro hv
      refine inSpanMasks_trans (fun g hg => ?_) hv
      rcases List.mem_cons.mp hg with rfl | hg'
      · rw [hx]
        exact inSpanMasks_xor (inSpanMasks_of_mem (by simp))
          (inSpanMasks_cons_zero hv')
      · exact inSpanMasks_cons_zero (inSpanMasks_of_mem hg')
    · intro hv
      refine inSpanMasks_trans (fun g hg => ?_) hv
      rcases List.mem_cons.mp hg with rfl | hg'
      · have hxinv : g = reduceByBasis acc g ^^^ v' := by
          rw [hx, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        rw [show inSpanMasks (reduceByBasis acc g :: acc) g
            = inSpanMasks (reduceByBasis acc g :: acc)
                (reduceByBasis acc g ^^^ v') from congrArg _ hxinv]
        exact inSpanMasks_xor (inSpanMasks_of_mem (by simp))
          (inSpanMasks_cons_zero hv')
      · exact inSpanMasks_cons_zero (inSpanMasks_of_mem hg')

theorem inSpanMasks_append_left {xs zs : List Nat} {v : Nat}
    (h : inSpanMasks xs v) : inSpanMasks (zs ++ xs) v :=
  (inSpanMasks_perm (List.perm_append_comm (l₁ := xs) (l₂ := zs)) v).mp
    (inSpanMasks_append_right h)

theorem spanEq_append_left {A B : List Nat}
    (h : ∀ v : Nat, inSpanMasks A v ↔ inSpanMasks B v) (C : List Nat) (v : Nat) :
    inSpanMasks (C ++ A) v ↔ inSpanMasks (C ++ B) v := by
  constructor
  · intro hv
    exact inSpanMasks_trans (fun g hg => by
      rcases List.mem_append.mp hg with hg' | hg'
      · exact inSpanMasks_append_right (inSpanMasks_of_mem hg')
      · exact inSpanMasks_append_left ((h g).mp (inSpanMasks_of_mem hg'))) hv
  · intro hv
    exact inSpanMasks_trans (fun g hg => by
      rcases List.mem_append.mp hg with hg' | hg'
      · exact inSpanMasks_append_right (inSpanMasks_of_mem hg')
      · exact inSpanMasks_append_left ((h g).mpr (inSpanMasks_of_mem hg'))) hv

theorem spanEq_foldl_insertBasis (xs : List Nat) :
    ∀ (acc : List Nat) (v : Nat),
      inSpanMasks (xs.foldl insertBasis acc) v ↔ inSpanMasks (xs ++ acc) v := by
  induction xs with
  | nil => intro acc v; exact Iff.rfl
  | cons x xs ih =>
      intro acc v
      rw [List.foldl_cons, List.cons_append]
      have hperm : List.Perm (xs ++ (x :: acc)) (x :: (xs ++ acc)) := by
        have h1 : List.Perm (xs ++ (x :: acc)) ((x :: acc) ++ xs) :=
          List.perm_append_comm
        have h2 : List.Perm (acc ++ xs) (xs ++ acc) := List.perm_append_comm
        exact h1.trans (List.Perm.cons x h2)
      exact (ih (insertBasis acc x) v).trans
        ((spanEq_append_left (spanEq_insertBasis acc x) xs v).trans
          (inSpanMasks_perm hperm v))

theorem spanEq_foldl_insertBasis_nil (xs : List Nat) (v : Nat) :
    inSpanMasks (xs.foldl insertBasis []) v ↔ inSpanMasks xs v := by
  have h := spanEq_foldl_insertBasis xs [] v
  rwa [List.append_nil] at h

theorem spanList_iff_inSpanMasks (xs : List Nat) (v : Nat) :
    v ∈ spanList xs ↔ inSpanMasks xs v := by
  constructor
  · exact spanList_combine xs v
  · intro hv
    induction xs generalizing v with
    | nil =>
        rw [inSpanMasks_nil] at hv
        subst v
        simp [spanList]
    | cons x xs ih =>
        rcases hv with ⟨cs, hlen, h01, hval⟩
        rw [spanList]
        cases cs with
        | nil => simp at hlen
        | cons c cs' =>
            have hlen' : cs'.length = xs.length := by simpa using hlen
            have h01' : ∀ d ∈ cs', d = 0 ∨ d = 1 := fun d hd => h01 d (by simp [hd])
            rw [combineMasks_cons] at hval
            by_cases hc1 : c = 1
            · simp only [hc1, reduceIte] at hval
              refine List.mem_append.mpr (Or.inr
                (List.mem_map.mpr ⟨combineMasks xs cs', ?_, ?_⟩))
              · exact ih _ ⟨cs', hlen', h01', rfl⟩
              · rw [Nat.xor_comm, hval]
            · have hc0 : c = 0 := by
                rcases h01 c (by simp) with h0 | h1
                · exact h0
                · exact absurd hc1 (by simp [h1])
              simp [hc0] at hval
              exact List.mem_append.mpr (Or.inl (ih _ ⟨cs', hlen', h01', hval⟩))

/-! ### Counting -/

theorem nodup_range (n : Nat) : (List.range n).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.nodup_append]
      refine ⟨ih, by simp, ?_⟩
      intro a ha b hb hab
      have ha' : a < n := List.mem_range.mp ha
      have hb' : b = n := List.mem_singleton.mp hb
      omega

/-- A duplicate-free list injects into a duplicate-free list that contains
    it, so its length is bounded. -/
theorem length_le_of_nodup_subset {L l : List Nat}
    (hL : L.Nodup) (hl : l.Nodup) (hsub : ∀ v ∈ l, v ∈ L) : l.length ≤ L.length := by
  induction l generalizing L with
  | nil => simp
  | cons a l' ih =>
      rcases List.nodup_cons.mp hl with ⟨ha, hl'⟩
      have haL : a ∈ L := hsub a (by simp)
      have hsub' : ∀ v ∈ l', v ∈ L.erase a := by
        intro v hv
        rw [List.Nodup.mem_erase_iff hL]
        refine ⟨?_, hsub v (by simp [hv])⟩
        intro hve
        exact ha (hve ▸ hv)
      have hih := ih (L := L.erase a) (List.Nodup.erase a hL) hl' hsub'
      rw [List.length_cons]
      rw [List.length_erase_of_mem haL] at hih
      have hLpos : 0 < L.length := List.length_pos_of_mem haL
      omega

/-! ### The greedy rank is span-determined -/

/-- The greedy rank is determined by the F₂ span of the mask list: two mask
    lists with the same span have the same `rankBitmasks`. -/
theorem rankBitmasks_eq_of_span_eq {xs ys : List Nat}
    (h : ∀ v : Nat, inSpanMasks xs v ↔ inSpanMasks ys v) :
    rankBitmasks xs = rankBitmasks ys := by
  have hBdx : PivotDistinct (xs.foldl insertBasis []) :=
    foldl_insertBasis_pivotDistinct xs [] pivotDistinct_nil
  have hBdy : PivotDistinct (ys.foldl insertBasis []) :=
    foldl_insertBasis_pivotDistinct ys [] pivotDistinct_nil
  have hnodx : (spanList (xs.foldl insertBasis [])).Nodup :=
    spanList_nodup _ (independentMasks_pivotDistinct _ hBdx)
  have hnody : (spanList (ys.foldl insertBasis [])).Nodup :=
    spanList_nodup _ (independentMasks_pivotDistinct _ hBdy)
  have hlenx : (spanList (xs.foldl insertBasis [])).length = 2 ^ rankBitmasks xs := by
    rw [spanList_length]; rfl
  have hleny : (spanList (ys.foldl insertBasis [])).length = 2 ^ rankBitmasks ys := by
    rw [spanList_length]; rfl
  have hsub1 : ∀ v ∈ spanList (ys.foldl insertBasis []),
      v ∈ spanList (xs.foldl insertBasis []) := by
    intro v hv
    have h1 : inSpanMasks (ys.foldl insertBasis []) v :=
      (spanList_iff_inSpanMasks _ v).mp hv
    have h2 : inSpanMasks ys v := (spanEq_foldl_insertBasis_nil ys v).mp h1
    have h3 : inSpanMasks xs v := (h v).mpr h2
    exact (spanList_iff_inSpanMasks _ v).mpr ((spanEq_foldl_insertBasis_nil xs v).mpr h3)
  have hsub2 : ∀ v ∈ spanList (xs.foldl insertBasis []),
      v ∈ spanList (ys.foldl insertBasis []) := by
    intro v hv
    have h1 : inSpanMasks (xs.foldl insertBasis []) v :=
      (spanList_iff_inSpanMasks _ v).mp hv
    have h2 : inSpanMasks xs v := (spanEq_foldl_insertBasis_nil xs v).mp h1
    have h3 : inSpanMasks ys v := (h v).mp h2
    exact (spanList_iff_inSpanMasks _ v).mpr ((spanEq_foldl_insertBasis_nil ys v).mpr h3)
  have hle1 : (spanList (ys.foldl insertBasis [])).length
      ≤ (spanList (xs.foldl insertBasis [])).length :=
    length_le_of_nodup_subset hnodx hnody hsub1
  have hle2 : (spanList (xs.foldl insertBasis [])).length
      ≤ (spanList (ys.foldl insertBasis [])).length :=
    length_le_of_nodup_subset hnody hnodx hsub2
  rw [hlenx, hleny] at hle1
  rw [hleny, hlenx] at hle2
  by_cases hlt : rankBitmasks xs < rankBitmasks ys
  · exact absurd hle1 (Nat.not_le.mpr (two_pow_lt_two_pow hlt))
  · by_cases hlt2 : rankBitmasks ys < rankBitmasks xs
    · exact absurd hle2 (Nat.not_le.mpr (two_pow_lt_two_pow hlt2))
    · omega

/-! ### Bits of the greedy basis and unit vectors -/

/-- Greedy insertion preserves nonzero members and high-bit-clear members. -/
theorem foldl_insertBasis_preserved (xs : List Nat) (m : Nat)
    (hxs : ∀ x ∈ xs, ∀ j : Nat, m ≤ j → x.testBit j = false) :
    ∀ acc : List Nat, (∀ a ∈ acc, a ≠ 0) →
      (∀ a ∈ acc, ∀ j : Nat, m ≤ j → a.testBit j = false) →
      (∀ a ∈ xs.foldl insertBasis acc, a ≠ 0) ∧
        (∀ a ∈ xs.foldl insertBasis acc, ∀ j : Nat, m ≤ j → a.testBit j = false) := by
  induction xs with
  | nil => intro acc hne hbits; exact ⟨hne, hbits⟩
  | cons x xs ih =>
      intro acc hne hbits
      rw [List.foldl_cons]
      have hne' : ∀ a ∈ insertBasis acc x, a ≠ 0 := by
        intro a ha
        simp only [insertBasis] at ha
        split at ha
        · exact hne a ha
        · rename_i h
          rcases List.mem_cons.mp ha with rfl | ha'
          · exact h
          · exact hne a ha'
      have hbits' : ∀ a ∈ insertBasis acc x, ∀ j : Nat, m ≤ j → a.testBit j = false := by
        intro a ha j hj
        simp only [insertBasis] at ha
        split at ha
        · exact hbits a ha j hj
        · rename_i h
          rcases List.mem_cons.mp ha with rfl | ha'
          · have hstep : ∀ b ∈ sortByPivotDesc acc, Nat.log2 b < j := by
              intro b hb
              have hbmem : b ∈ acc := sortByPivotDesc_mem acc hb
              exact log2_lt_of_lt_two_pow (hne b hbmem)
                (lt_two_pow_of_high_bits_false b j
                  (fun k hk => hbits b hbmem k (Nat.le_trans hj hk)))
            rw [reduceByBasis_eq_fold, reduceFold_above (sortByPivotDesc acc) x j hstep]
            exact hxs x (by simp) j hj
          · exact hbits a ha' j hj
      exact ih (fun x' hx => hxs x' (List.mem_cons_of_mem _ hx))
        (insertBasis acc x) hne' hbits'

/-- The rank clause of `rebaseMatrix_ok` puts every unit mask `2 ^ i` with
    `i < m` into the span of the matrix's column-position row masks: the
    greedy basis has `m` pivot-distinct masks below `2 ^ m`, so its span is
    everything below `2 ^ m`. -/
theorem rebaseMatrix_unit_coeff (matrix : List (List Nat)) (m : Nat)
    (hok : rebaseMatrix_ok matrix m) :
    ∀ i : Nat, i < m →
      ∃ d : List Nat, d.length = m ∧ (∀ c ∈ d, c = 0 ∨ c = 1) ∧
        combineMasks (matrix.map matrixRowMask) d = 2 ^ i := by
  have hmlen : (matrix.map matrixRowMask).length = m := by
    rw [List.length_map, hok.1]
  have hrank : rankBitmasks (matrix.map matrixRowMask) = m := hok.2.2
  have hBl : ((matrix.map matrixRowMask).foldl insertBasis []).length = m := by
    rw [← hrank]; rfl
  have hgensBits : ∀ x ∈ matrix.map matrixRowMask, ∀ j : Nat, m ≤ j → x.testBit j = false := by
    intro x hx j hj
    obtain ⟨row, hrow, hxe⟩ := List.mem_map.mp hx
    subst hxe
    have hrowl : row.length = m := (hok.2.1 row hrow).1
    rw [testBit_matrixRowMask row j]
    have hget : row.getD j 0 = 0 := by
      by_cases hjlt : j < row.length
      · omega
      · rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt hjlt)]
        simp
    rw [List.getD_eq_getElem?_getD] at hget
    simp [hget]
  obtain ⟨hne, hbits⟩ := foldl_insertBasis_preserved (matrix.map matrixRowMask) m hgensBits
    [] (by intro a ha; cases ha) (by intro a ha; cases ha)
  have hind : independentMasks ((matrix.map matrixRowMask).foldl insertBasis []) :=
    independentMasks_pivotDistinct _
      (foldl_insertBasis_pivotDistinct (matrix.map matrixRowMask) [] pivotDistinct_nil)
  have hnod : (spanList ((matrix.map matrixRowMask).foldl insertBasis [])).Nodup :=
    spanList_nodup _ hind
  have hhigh : ∀ v ∈ spanList ((matrix.map matrixRowMask).foldl insertBasis []),
      ∀ j : Nat, m ≤ j → v.testBit j = false := by
    intro v hv j hj
    have h1 : inSpanMasks ((matrix.map matrixRowMask).foldl insertBasis []) v :=
      (spanList_iff_inSpanMasks _ v).mp hv
    obtain ⟨cs, hclen, hc01, hcval⟩ := h1
    rw [← hcval]
    exact combineMasks_testBit_false _ cs j (fun x hx => hbits x hx j hj)
  have hlt : ∀ v ∈ spanList ((matrix.map matrixRowMask).foldl insertBasis []),
      v < 2 ^ m := fun v hv => lt_two_pow_of_high_bits_false v m (hhigh v hv)
  intro i hi
  by_cases hin : inSpanMasks ((matrix.map matrixRowMask).foldl insertBasis []) (2 ^ i)
  · have hgen : inSpanMasks (matrix.map matrixRowMask) (2 ^ i) :=
      (spanEq_foldl_insertBasis_nil (matrix.map matrixRowMask) (2 ^ i)).mp hin
    obtain ⟨d, hdlen, hd01, hdval⟩ := hgen
    refine ⟨d, ?_, hd01, hdval⟩
    rw [List.length_map, hok.1] at hdlen
    exact hdlen
  · exfalso
    have hnodL : (((spanList ((matrix.map matrixRowMask).foldl insertBasis [])).map
          (fun v => v ^^^ 2 ^ i)) ++
        spanList ((matrix.map matrixRowMask).foldl insertBasis [])).Nodup := by
      rw [List.nodup_append]
      refine ⟨nodup_map_xor _ _ hnod, hnod, ?_⟩
      intro a ha b hb hab
      rcases List.mem_map.mp ha with ⟨w, hw, hwe⟩
      have h1 : inSpanMasks ((matrix.map matrixRowMask).foldl insertBasis []) b :=
        (spanList_iff_inSpanMasks _ b).mp hb
      have h2 : inSpanMasks ((matrix.map matrixRowMask).foldl insertBasis []) w :=
        (spanList_iff_inSpanMasks _ w).mp hw
      have hbw : b ^^^ w = 2 ^ i := by
        calc b ^^^ w = (w ^^^ 2 ^ i) ^^^ w := by rw [← hab, hwe]
          _ = w ^^^ (2 ^ i ^^^ w) := Nat.xor_assoc w (2 ^ i) w
          _ = (2 ^ i ^^^ w) ^^^ w := by rw [Nat.xor_comm w (2 ^ i ^^^ w)]
          _ = 2 ^ i := by rw [Nat.xor_assoc, Nat.xor_self w, Nat.xor_zero]
      exact hin (hbw ▸ inSpanMasks_xor h1 h2)
    have hlenL : (((spanList ((matrix.map matrixRowMask).foldl insertBasis [])).map
          (fun v => v ^^^ 2 ^ i)) ++
        spanList ((matrix.map matrixRowMask).foldl insertBasis [])).length
        = 2 ^ m + 2 ^ m := by
      rw [List.length_append, List.length_map, spanList_length, hBl]
    have hsubL : ∀ v ∈ (((spanList ((matrix.map matrixRowMask).foldl insertBasis [])).map
          (fun v => v ^^^ 2 ^ i)) ++
        spanList ((matrix.map matrixRowMask).foldl insertBasis [])),
        v ∈ List.range (2 ^ m) := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · rcases List.mem_map.mp hv with ⟨w, hw, hwe⟩
        apply List.mem_range.mpr
        refine lt_two_pow_of_high_bits_false _ m ?_
        intro j hj
        rw [← hwe, Nat.testBit_xor, hhigh w hw j hj, Nat.testBit_two_pow]
        have hij : ¬ (i = j) := by omega
        simp [hij]
      · exact List.mem_range.mpr (hlt v hv)
    have hle := length_le_of_nodup_subset (nodup_range (2 ^ m)) hnodL hsubL
    rw [List.length_range] at hle
    have hpos := Nat.two_pow_pos m
    omega

end CodeCalculus
