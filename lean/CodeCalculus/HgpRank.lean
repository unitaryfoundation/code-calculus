import CodeCalculus.TensorRank
import CodeCalculus.ConstructorOrthogonality

/-!
# Row rank, column rank, and the rank of a two-block tensor family

Two results on mask lists that the closed forms for `k` of `L-HGP` and
`A-PRODUCT` use.

* `rank_colMasks`: the rank of the columns of a mask list is the rank of
  the list.
* `rank_hgRows`: for mask lists `A` (of length `S`, over `p` positions) and
  `D` (of length `T`, over `q` positions), the family indexed by `(s, t)`
  whose member is the tensor of `A_s` with the unit mask `t` in one block
  and the tensor of the unit mask `s` with `D_t` in another block has rank
  `rank A * T + (S - rank A) * rank D`. The two blocks are placed by the
  maps of an `HgLayout`.
-/

namespace CodeCalculus

/-! ## The unit masks are independent -/

theorem independent_unitMasks : ∀ n, independentMasks (unitMasks n)
  | 0 => by
      intro cs hlen _ _ c hc
      cases cs with
      | nil => exact absurd hc List.not_mem_nil
      | cons _ _ => exact absurd hlen (Nat.succ_ne_zero _)
  | n + 1 => by
      intro cs hlen h01 hval
      rw [unitMasks_succ] at hlen hval
      cases cs with
      | nil => exact absurd hlen.symm (Nat.succ_ne_zero _)
      | cons c cs =>
          have hlen' : cs.length = (unitMasks n).length := by
            have h : cs.length = ((unitMasks n).map (· <<< 1)).length := Nat.succ.inj hlen
            rw [List.length_map] at h
            exact h
          have hval' : (if c = 1 then 1 else 0) ^^^
              (combineMasks (unitMasks n) cs <<< 1) = 0 := by
            have h := hval
            rw [show [1] ++ (unitMasks n).map (· <<< 1) = 1 :: (unitMasks n).map (· <<< 1)
              from rfl, combineMasks_cons,
              combineMasks_map_additive (· <<< 1) (shiftLeft_xor 1) (Nat.zero_shiftLeft 1)]
              at h
            exact h
          have htail : ∀ d ∈ cs, d = 0 ∨ d = 1 := fun d hd => h01 d (List.mem_cons_of_mem _ hd)
          rcases h01 c (List.mem_cons_self ..) with hc | hc
          · subst hc
            have h2 : combineMasks (unitMasks n) cs <<< 1 = 0 := by
              have h := hval'
              rw [show (if (0 : Nat) = 1 then (1 : Nat) else 0) = 0 from rfl, Nat.zero_xor] at h
              exact h
            have h3 := independent_unitMasks n cs hlen' htail
              (eq_zero_of_shiftLeft_eq_zero 1 _ h2)
            intro d hd
            rcases List.mem_cons.mp hd with rfl | hd
            · rfl
            · exact h3 d hd
          · subst hc
            have hb : ((1 : Nat) ^^^ (combineMasks (unitMasks n) cs <<< 1)).testBit 0 = true := by
              rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
              rfl
            have h := hval'
            rw [show (if (1 : Nat) = 1 then (1 : Nat) else 0) = 1 from rfl] at h
            rw [h, Nat.zero_testBit] at hb
            exact absurd hb Bool.false_ne_true

/-! ## Columns of a mask list -/

/-- Column `j` of a mask list: bit `i` is bit `j` of member `i`. -/
def colMask (R : List Nat) (j : Nat) : Nat := boolsToMask (R.map (fun r => r.testBit j))

/-- The first `n` columns of a mask list. -/
def colMasks (n : Nat) (R : List Nat) : List Nat := (List.range n).map (colMask R)

theorem getD_map_testBit (j : Nat) : ∀ (R : List Nat) (i : Nat),
    (R.map (fun r => r.testBit j)).getD i false = (R.getD i 0).testBit j
  | [], i => by rw [List.map_nil, List.getD_nil, List.getD_nil, Nat.zero_testBit]
  | r :: R, 0 => by rw [List.map_cons, List.getD_cons_zero, List.getD_cons_zero]
  | r :: R, i + 1 => by
      rw [List.map_cons, List.getD_cons_succ, List.getD_cons_succ]
      exact getD_map_testBit j R i

theorem testBit_colMask (R : List Nat) (j i : Nat) :
    (colMask R j).testBit i = (R.getD i 0).testBit j := by
  unfold colMask
  rw [testBit_boolsToMask, getD_map_testBit]

theorem colMask_cons_testBit_zero (r : Nat) (R : List Nat) (j : Nat) :
    (colMask (r :: R) j).testBit 0 = r.testBit j := by
  rw [testBit_colMask, List.getD_cons_zero]

theorem colMask_cons_shiftRight (r : Nat) (R : List Nat) (j : Nat) :
    colMask (r :: R) j >>> 1 = colMask R j := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight, testBit_colMask, testBit_colMask, Nat.add_comm,
    List.getD_cons_succ]

theorem colMask_cons (r : Nat) (R : List Nat) (j : Nat) :
    colMask (r :: R) j = sel (r.testBit j) 1 ^^^ (colMask R j <<< 1) := by
  have h := eq_sel_xor_shift (colMask (r :: R) j)
  rw [colMask_cons_testBit_zero, colMask_cons_shiftRight] at h
  exact h

/-- The columns of a coefficient matrix with one more row, whose
    coefficients are the bits of `c`. -/
def coeffCols : Nat → List Nat → List Nat
  | _, [] => []
  | c, d :: ds => (sel (c.testBit 0) 1 ^^^ (d <<< 1)) :: coeffCols (c >>> 1) ds

theorem length_coeffCols : ∀ (c : Nat) (D : List Nat), (coeffCols c D).length = D.length
  | _, [] => rfl
  | c, d :: ds => by
      show (coeffCols (c >>> 1) ds).length + 1 = ds.length + 1
      rw [length_coeffCols]

theorem sel_sel (a b : Bool) (x : Nat) : sel a (sel b x) = sel (b && a) x := by
  cases a <;> cases b <;> rfl

theorem sel_shiftLeft (b : Bool) (x n : Nat) : sel b x <<< n = sel b (x <<< n) := by
  cases b
  · exact Nat.zero_shiftLeft n
  · rfl

theorem comb_coeffCols (j : Nat) : ∀ (B D : List Nat) (c : Nat), D.length = B.length →
    comb (coeffCols c D) (colMask B j) =
      sel ((comb B c).testBit j) 1 ^^^ (comb D (colMask B j) <<< 1)
  | [], [], c, _ => by
      show (0 : Nat) = sel ((0 : Nat).testBit j) 1 ^^^ ((0 : Nat) <<< 1)
      rw [Nat.zero_testBit, sel_false, Nat.zero_shiftLeft, Nat.xor_self]
  | [], _ :: _, _, h => absurd h (Nat.succ_ne_zero _)
  | _ :: _, [], _, h => absurd h.symm (Nat.succ_ne_zero _)
  | b :: B, d :: ds, c, h => by
      show sel ((colMask (b :: B) j).testBit 0) (sel (c.testBit 0) 1 ^^^ (d <<< 1)) ^^^
          comb (coeffCols (c >>> 1) ds) (colMask (b :: B) j >>> 1) =
        sel ((sel (c.testBit 0) b ^^^ comb B (c >>> 1)).testBit j) 1 ^^^
          ((sel ((colMask (b :: B) j).testBit 0) d ^^^
            comb ds (colMask (b :: B) j >>> 1)) <<< 1)
      rw [colMask_cons_testBit_zero, colMask_cons_shiftRight,
        comb_coeffCols j B ds (c >>> 1) (Nat.succ.inj h), Nat.testBit_xor, testBit_sel,
        sel_xor_bool, sel_xor_val, sel_sel, shiftLeft_xor, sel_shiftLeft, xor_interchange]

theorem comb_replicate_zero : ∀ (n y : Nat), comb (List.replicate n 0) y = 0
  | 0, _ => rfl
  | n + 1, y => by
      show sel (y.testBit 0) 0 ^^^ comb (List.replicate n 0) (y >>> 1) = 0
      rw [sel_zero, comb_replicate_zero, Nat.xor_self]

/-- When the members of `R` are in the span of `B`, the columns of `R` are
    combinations of one list as long as `B`. -/
theorem exists_col_factor (B : List Nat) : ∀ (R : List Nat), (∀ r ∈ R, inSpanMasks B r) →
    ∃ D : List Nat, D.length = B.length ∧ ∀ j, colMask R j = comb D (colMask B j)
  | [], _ => ⟨List.replicate B.length 0, List.length_replicate, fun j => by
      rw [comb_replicate_zero]
      rfl⟩
  | r :: R, h => by
      obtain ⟨D, hlen, hD⟩ := exists_col_factor B R
        (fun x hx => h x (List.mem_cons_of_mem _ hx))
      obtain ⟨c, hc⟩ := exists_comb_of_inSpan B r (h r (List.mem_cons_self ..))
      refine ⟨coeffCols c D, by rw [length_coeffCols, hlen], fun j => ?_⟩
      rw [colMask_cons, comb_coeffCols j B D c hlen, hc, hD j]

theorem rank_colMasks_le (n : Nat) (R : List Nat) :
    rankBitmasks (colMasks n R) ≤ rankBitmasks R := by
  obtain ⟨D, hlen, hD⟩ := exists_col_factor (basisOf R) R
    (fun r hr => (basisOf_span R r).mpr (inSpanMasks_of_mem hr))
  have h1 : rankBitmasks (colMasks n R) ≤ rankBitmasks D := by
    apply rankBitmasks_le_of_span
    intro y hy
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
    rw [hD j]
    exact comb_inSpan D _
  have h2 := rankBitmasks_le_length D
  rw [hlen] at h2
  exact Nat.le_trans h1 h2

theorem getD_colMasks (n : Nat) (R : List Nat) (j : Nat) :
    (colMasks n R).getD j 0 = if j < n then colMask R j else 0 := by
  unfold colMasks
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases Nat.lt_or_ge j n with h | h
  · rw [List.getElem?_range h, ite_eq_left_of_eq_true _ _ (eq_true h)]
    rfl
  · rw [List.getElem?_eq_none (by rw [List.length_range]; exact h),
      ite_eq_right_of_eq_false _ _ (eq_false (Nat.not_lt_of_le h))]
    rfl

/-- The columns of the columns are the list. -/
theorem colMasks_colMasks (n : Nat) (R : List Nat) (hR : ∀ r ∈ R, Below n r) :
    colMasks R.length (colMasks n R) = R := by
  apply List.ext_getElem?
  intro i
  show ((List.range R.length).map (colMask (colMasks n R)))[i]? = R[i]?
  rw [List.getElem?_map]
  rcases Nat.lt_or_ge i R.length with h2 | h2
  · rw [List.getElem?_range h2, List.getElem?_eq_getElem h2]
    show some (colMask (colMasks n R) i) = some R[i]
    congr 1
    apply Nat.eq_of_testBit_eq
    intro j
    have hget : R.getD i 0 = R[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
      rfl
    rw [testBit_colMask, getD_colMasks]
    rcases Nat.lt_or_ge j n with h | h
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h), testBit_colMask, hget]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (Nat.not_lt_of_le h)), Nat.zero_testBit,
        hR _ (List.getElem_mem h2) j h]
  · rw [List.getElem?_eq_none (by rw [List.length_range]; exact h2),
      List.getElem?_eq_none h2]
    rfl

/-- Row rank equals column rank. -/
theorem rank_colMasks (n : Nat) (R : List Nat) (hR : ∀ r ∈ R, Below n r) :
    rankBitmasks (colMasks n R) = rankBitmasks R := by
  apply Nat.le_antisymm (rank_colMasks_le n R)
  have h := rank_colMasks_le R.length (colMasks n R)
  rw [colMasks_colMasks n R hR] at h
  exact h

/-! ## The two-block tensor family -/

/-- Additive maps that place the two blocks: `lam` places the block over
    `p * T` positions, `rho` the block over `S * q` positions, and `phi`
    reads the first block back and kills the second. -/
structure HgLayout (lam rho phi : Nat → Nat) (S T p q : Nat) : Prop where
  lam_xor : ∀ a b, lam (a ^^^ b) = lam a ^^^ lam b
  rho_xor : ∀ a b, rho (a ^^^ b) = rho a ^^^ rho b
  phi_xor : ∀ a b, phi (a ^^^ b) = phi a ^^^ phi b
  phi_lam : ∀ x, Below (p * T) x → phi (lam x) = x
  phi_rho : ∀ y, Below (S * q) y → phi (rho y) = 0
  rho_inj : ∀ y, rho y = 0 → y = 0

/-- The combination, by the coefficient mask `y`, of the members `(s, t)`
    of the family for the fixed `t`. -/
def hgTerm (lam rho : Nat → Nat) (S T p q : Nat) (A D : List Nat) (t y : Nat) : Nat :=
  lam (tens p T (comb A y) (2 ^ t)) ^^^ rho (tens S q y (D.getD t 0))

/-- The family, indexed by `(s, t)`. -/
def hgRows (lam rho : Nat → Nat) (S T p q : Nat) (A D : List Nat) : List Nat :=
  (indexPairs S T).map (fun st => hgTerm lam rho S T p q A D st.2 (2 ^ st.1))

/-- The sum of `hgTerm (t + i) y_i` over a list of coefficient masks. -/
def hgSum (lam rho : Nat → Nat) (S T p q : Nat) (A D : List Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | t, y :: ys => hgTerm lam rho S T p q A D t y ^^^ hgSum lam rho S T p q A D (t + 1) ys

/-- The list whose rank is the nullity of the family. -/
def hgKer (rho : Nat → Nat) (S q : Nat) (A D : List Nat) : List Nat :=
  ((kerList A).flatMap (fun u => D.map (tens S q u))).map rho

theorem below_getD {n : Nat} {D : List Nat} (h : ∀ d ∈ D, Below n d) (t : Nat) :
    Below n (D.getD t 0) := by
  rw [List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge t D.length with ht | ht
  · rw [List.getElem?_eq_getElem ht]
    exact h _ (List.getElem_mem ht)
  · rw [List.getElem?_eq_none ht]
    exact below_zero n

theorem getD_mem_of_lt {D : List Nat} {t : Nat} (ht : t < D.length) : D.getD t 0 ∈ D := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
  exact List.getElem_mem ht

theorem below_two_pow {n t : Nat} (h : t < n) : Below n (2 ^ t) := by
  intro j hj
  rw [Nat.testBit_two_pow]
  exact decide_eq_false (by omega)

section Family

variable {lam rho phi : Nat → Nat} {S T p q : Nat}

theorem hgTerm_xor (h : HgLayout lam rho phi S T p q) (A D : List Nat) (t y z : Nat) :
    hgTerm lam rho S T p q A D t (y ^^^ z) =
      hgTerm lam rho S T p q A D t y ^^^ hgTerm lam rho S T p q A D t z := by
  unfold hgTerm
  rw [comb_xor, tens_xor_left, tens_xor_left, h.lam_xor, h.rho_xor, xor_interchange]

theorem hgTerm_zero (h : HgLayout lam rho phi S T p q) (A D : List Nat) (t : Nat) :
    hgTerm lam rho S T p q A D t 0 = 0 :=
  additive_zero _ (hgTerm_xor h A D t)

theorem hgSum_zeros (h : HgLayout lam rho phi S T p q) (A D : List Nat) : ∀ (n t : Nat),
    hgSum lam rho S T p q A D t (List.replicate n 0) = 0
  | 0, _ => rfl
  | n + 1, t => by
      show hgTerm lam rho S T p q A D t 0 ^^^
        hgSum lam rho S T p q A D (t + 1) (List.replicate n 0) = 0
      rw [hgTerm_zero h, hgSum_zeros h A D n, Nat.xor_self]

theorem hgSum_append (A D : List Nat) : ∀ (xs zs : List Nat) (t : Nat),
    hgSum lam rho S T p q A D t (xs ++ zs) =
      hgSum lam rho S T p q A D t xs ^^^ hgSum lam rho S T p q A D (t + xs.length) zs
  | [], zs, t => by
      show hgSum lam rho S T p q A D t zs = 0 ^^^ hgSum lam rho S T p q A D (t + 0) zs
      rw [Nat.zero_xor, Nat.add_zero]
  | x :: xs, zs, t => by
      show hgTerm lam rho S T p q A D t x ^^^ hgSum lam rho S T p q A D (t + 1) (xs ++ zs) =
        (hgTerm lam rho S T p q A D t x ^^^ hgSum lam rho S T p q A D (t + 1) xs) ^^^
          hgSum lam rho S T p q A D (t + (xs.length + 1)) zs
      rw [hgSum_append A D xs zs (t + 1), Nat.xor_assoc, Nat.add_assoc, Nat.add_comm 1]

theorem hgSum_zipWith (h : HgLayout lam rho phi S T p q) (A D : List Nat) :
    ∀ (ys zs : List Nat) (t : Nat), ys.length = zs.length →
      hgSum lam rho S T p q A D t (List.zipWith (· ^^^ ·) ys zs) =
        hgSum lam rho S T p q A D t ys ^^^ hgSum lam rho S T p q A D t zs
  | [], [], _, _ => (Nat.xor_self 0).symm
  | [], _ :: _, _, hl => absurd hl.symm (Nat.succ_ne_zero _)
  | _ :: _, [], _, hl => absurd hl (Nat.succ_ne_zero _)
  | y :: ys, z :: zs, t, hl => by
      show hgTerm lam rho S T p q A D t (y ^^^ z) ^^^
          hgSum lam rho S T p q A D (t + 1) (List.zipWith (· ^^^ ·) ys zs) =
        (hgTerm lam rho S T p q A D t y ^^^ hgSum lam rho S T p q A D (t + 1) ys) ^^^
          (hgTerm lam rho S T p q A D t z ^^^ hgSum lam rho S T p q A D (t + 1) zs)
      rw [hgTerm_xor h, hgSum_zipWith h A D ys zs (t + 1) (Nat.succ.inj hl), xor_interchange]

theorem below_zipWith_xor (n : Nat) : ∀ (ys zs : List Nat), (∀ y ∈ ys, Below n y) →
    (∀ z ∈ zs, Below n z) → ∀ w ∈ List.zipWith (· ^^^ ·) ys zs, Below n w
  | [], _, _, _, w, hw => absurd hw List.not_mem_nil
  | _ :: _, [], _, _, w, hw => absurd hw List.not_mem_nil
  | y :: ys, z :: zs, hy, hz, w, hw => by
      rcases List.mem_cons.mp hw with rfl | hw
      · exact below_xor (hy y (List.mem_cons_self ..)) (hz z (List.mem_cons_self ..))
      · exact below_zipWith_xor n ys zs (fun a ha => hy a (List.mem_cons_of_mem _ ha))
          (fun a ha => hz a (List.mem_cons_of_mem _ ha)) w hw

/-- Every member of the span of the family is a sum of `T` terms. -/
theorem exists_hgSum (h : HgLayout lam rho phi S T p q) (A D : List Nat) (v : Nat)
    (hv : inSpanMasks (hgRows lam rho S T p q A D) v) :
    ∃ ys : List Nat, ys.length = T ∧ (∀ y ∈ ys, Below S y) ∧
      v = hgSum lam rho S T p q A D 0 ys := by
  refine span_induction (P := fun v => ∃ ys : List Nat, ys.length = T ∧
    (∀ y ∈ ys, Below S y) ∧ v = hgSum lam rho S T p q A D 0 ys) ?_ ?_ _ ?_ v hv
  · refine ⟨List.replicate T 0, List.length_replicate, ?_, (hgSum_zeros h A D T 0).symm⟩
    intro y hy
    rw [(List.mem_replicate.mp hy).2]
    exact below_zero S
  · rintro a b ⟨ys, hys, hyb, rfl⟩ ⟨zs, hzs, hzb, rfl⟩
    refine ⟨List.zipWith (· ^^^ ·) ys zs, ?_, below_zipWith_xor S ys zs hyb hzb,
      (hgSum_zipWith h A D ys zs 0 (by rw [hys, hzs])).symm⟩
    rw [List.length_zipWith, hys, hzs, Nat.min_self]
  · intro x hx
    obtain ⟨st, hst, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hs, ht⟩ := (mem_indexPairs (a := st.1) (b := st.2)).mp hst
    refine ⟨List.replicate st.2 0 ++ 2 ^ st.1 :: List.replicate (T - st.2 - 1) 0, ?_, ?_, ?_⟩
    · rw [List.length_append, List.length_cons, List.length_replicate, List.length_replicate]
      omega
    · intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · rw [(List.mem_replicate.mp hy).2]
        exact below_zero S
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact below_two_pow hs
        · rw [(List.mem_replicate.mp hy).2]
          exact below_zero S
    · rw [hgSum_append, hgSum_zeros h, List.length_replicate, Nat.zero_xor, Nat.zero_add]
      show _ = hgTerm lam rho S T p q A D st.2 (2 ^ st.1) ^^^
        hgSum lam rho S T p q A D (st.2 + 1) (List.replicate (T - st.2 - 1) 0)
      rw [hgSum_zeros h, Nat.xor_zero]

/-- The first block of a sum of terms. -/
theorem phi_hgSum (h : HgLayout lam rho phi S T p q) (A D : List Nat)
    (hD : ∀ d ∈ D, Below q d) : ∀ (ys : List Nat) (t : Nat), t + ys.length ≤ T →
      phi (hgSum lam rho S T p q A D t ys) =
        tsum p T (ys.map (comb A)) ((List.range' t ys.length).map (fun i => 2 ^ i))
  | [], _, _ => additive_zero phi h.phi_xor
  | y :: ys, t, ht => by
      have ht' : t < T := by
        rw [List.length_cons] at ht
        omega
      show phi (hgTerm lam rho S T p q A D t y ^^^ hgSum lam rho S T p q A D (t + 1) ys) =
        tsum p T (comb A y :: ys.map (comb A))
          ((List.range' t (ys.length + 1)).map (fun i => 2 ^ i))
      rw [List.range'_succ, List.map_cons]
      show _ = tens p T (comb A y) (2 ^ t) ^^^
        tsum p T (ys.map (comb A)) ((List.range' (t + 1) ys.length).map (fun i => 2 ^ i))
      rw [h.phi_xor, phi_hgSum h A D hD ys (t + 1) (by rw [List.length_cons] at ht; omega)]
      unfold hgTerm
      rw [h.phi_xor, h.phi_lam _ (below_tens p T _ _ (below_two_pow ht')),
        h.phi_rho _ (below_tens S q _ _ (below_getD hD t)), Nat.xor_zero]

/-- A sum of terms whose coefficient masks have zero combination of `A` is
    in the span of the nullity list. -/
theorem hgSum_inSpan_ker (h : HgLayout lam rho phi S T p q) (A D : List Nat)
    (hA : A.length = S) (hDl : D.length = T) : ∀ (ys : List Nat) (t : Nat),
      t + ys.length ≤ T → (∀ y ∈ ys, Below S y) → (∀ y ∈ ys, comb A y = 0) →
      inSpanMasks (hgKer rho S q A D) (hgSum lam rho S T p q A D t ys)
  | [], _, _, _, _ => inSpanMasks_zero _
  | y :: ys, t, ht, hb, h0 => by
      have ht' : t < D.length := by
        rw [List.length_cons] at ht
        omega
      show inSpanMasks _ (hgTerm lam rho S T p q A D t y ^^^
        hgSum lam rho S T p q A D (t + 1) ys)
      apply inSpanMasks_xor
      · unfold hgTerm
        rw [h0 y (List.mem_cons_self ..), tens_zero_left, additive_zero lam h.lam_xor,
          Nat.zero_xor]
        have hy : inSpanMasks (kerList A) y :=
          inSpan_kerList (by rw [hA]; exact hb y (List.mem_cons_self ..))
            (h0 y (List.mem_cons_self ..))
        have h1 : inSpanMasks ((kerList A).map (fun u => rho (tens S q u (D.getD t 0))))
            (rho (tens S q y (D.getD t 0))) :=
          (inSpanMasks_map_additive_iff (fun u => rho (tens S q u (D.getD t 0)))
            (fun a b => by
              show rho (tens S q (a ^^^ b) _) = _
              rw [tens_xor_left, h.rho_xor]) (kerList A) _).mpr ⟨y, hy, rfl⟩
        refine inSpanMasks_trans (gen := (kerList A).map
          (fun u => rho (tens S q u (D.getD t 0)))) (pre := hgKer rho S q A D) ?_ h1
        intro g hg
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
        apply inSpanMasks_of_mem
        exact List.mem_map_of_mem (List.mem_flatMap.mpr
          ⟨u, hu, List.mem_map_of_mem (getD_mem_of_lt ht')⟩)
      · exact hgSum_inSpan_ker h A D hA hDl ys (t + 1)
          (by rw [List.length_cons] at ht; omega)
          (fun z hz => hb z (List.mem_cons_of_mem _ hz))
          (fun z hz => h0 z (List.mem_cons_of_mem _ hz))

/-- The rank of the two-block tensor family. -/
theorem rank_hgRows (h : HgLayout lam rho phi S T p q) (A D : List Nat)
    (hA : A.length = S) (hDl : D.length = T) (hAb : ∀ a ∈ A, Below p a)
    (hDb : ∀ d ∈ D, Below q d) :
    rankBitmasks (hgRows lam rho S T p q A D) =
      rankBitmasks A * T + (S - rankBitmasks A) * rankBitmasks D := by
  -- the image under `phi`
  have himg : rankBitmasks ((hgRows lam rho S T p q A D).map phi) = rankBitmasks A * T := by
    have e : rankBitmasks (A.flatMap (fun x => (unitMasks T).map (tens p T x))) =
        rankBitmasks A * T := by
      rw [rank_tens p T A (unitMasks T) hAb (below_unitMasks T), rank_unitMasks]
    rw [← e]
    apply rankBitmasks_eq_of_span_eq
    apply span_eq_of_mem
    · intro x hx
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
      obtain ⟨st, hst, rfl⟩ := List.mem_map.mp hr
      obtain ⟨hs, ht⟩ := (mem_indexPairs (a := st.1) (b := st.2)).mp hst
      apply inSpanMasks_of_mem
      unfold hgTerm
      rw [h.phi_xor, h.phi_lam _ (below_tens p T _ _ (below_two_pow ht)),
        h.phi_rho _ (below_tens S q _ _ (below_getD hDb st.2)), Nat.xor_zero,
        comb_two_pow A st.1 (by rw [hA]; exact hs)]
      exact List.mem_flatMap.mpr ⟨_, getD_mem_of_lt (by rw [hA]; exact hs),
        List.mem_map_of_mem (List.mem_map_of_mem (List.mem_range.mpr ht))⟩
    · intro x hx
      obtain ⟨a, ha, hx⟩ := List.mem_flatMap.mp hx
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hu
      obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem ha
      have ht' := List.mem_range.mp ht
      apply inSpanMasks_of_mem
      refine List.mem_map.mpr ⟨hgTerm lam rho S T p q A D t (2 ^ s),
        List.mem_map.mpr ⟨(s, t), mem_indexPairs.mpr ⟨by rw [← hA]; exact hs, ht'⟩, rfl⟩, ?_⟩
      unfold hgTerm
      rw [h.phi_xor, h.phi_lam _ (below_tens p T _ _ (below_two_pow ht')),
        h.phi_rho _ (below_tens S q _ _ (below_getD hDb t)), Nat.xor_zero,
        comb_two_pow A s hs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]
      rfl
  -- the nullity list
  have hker : rankBitmasks (hgKer rho S q A D) = (S - rankBitmasks A) * rankBitmasks D := by
    unfold hgKer
    rw [rankBitmasks_map rho h.rho_xor _ (fun a _ ha => h.rho_inj a ha),
      rank_tens S q (kerList A) D (fun u hu => by rw [← hA]; exact (mem_kerList hu).2) hDb]
    have hk := rank_kerList A
    rw [hA] at hk
    have e : rankBitmasks (kerList A) = S - rankBitmasks A := by omega
    rw [e]
  have hrn := rank_nullity phi h.phi_xor (hgRows lam rho S T p q A D) (hgKer rho S q A D)
    (by
      intro k hk
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk
      obtain ⟨u, hu, hx⟩ := List.mem_flatMap.mp hx
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hd
      have hterm : hgTerm lam rho S T p q A D t u = rho (tens S q u D[t]) := by
        unfold hgTerm
        rw [(mem_kerList hu).1, tens_zero_left, additive_zero lam h.lam_xor, Nat.zero_xor,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
        rfl
      rw [← hterm]
      have hu' : inSpanMasks (unitMasks S) u :=
        inSpan_unitMasks S u (by rw [← hA]; exact (mem_kerList hu).2)
      have h1 : inSpanMasks ((unitMasks S).map (hgTerm lam rho S T p q A D t))
          (hgTerm lam rho S T p q A D t u) :=
        (inSpanMasks_map_additive_iff _ (hgTerm_xor h A D t) (unitMasks S) _).mpr
          ⟨u, hu', rfl⟩
      refine inSpanMasks_trans (gen := (unitMasks S).map (hgTerm lam rho S T p q A D t))
        (pre := hgRows lam rho S T p q A D) ?_ h1
      intro g hg
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hg
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp he
      apply inSpanMasks_of_mem
      exact List.mem_map.mpr ⟨(s, t),
        mem_indexPairs.mpr ⟨List.mem_range.mp hs, by rw [← hDl]; exact ht⟩, rfl⟩)
    (by
      intro k hk
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk
      obtain ⟨u, hu, hx⟩ := List.mem_flatMap.mp hx
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
      exact h.phi_rho _ (below_tens S q u d (hDb d hd)))
    (by
      intro v hv hphi
      obtain ⟨ys, hlen, hyb, rfl⟩ := exists_hgSum h A D v hv
      rw [phi_hgSum h A D hDb ys 0 (by rw [hlen]; omega), hlen, ← List.range_eq_range'] at hphi
      have hz := tsum_eq_zero_left p T (ys.map (comb A)) (unitMasks T)
        (independent_unitMasks T) (by rw [List.length_map, hlen, length_unitMasks])
        (fun a ha => by
          obtain ⟨y, _, rfl⟩ := List.mem_map.mp ha
          exact below_of_inSpan hAb (comb_inSpan A y))
        (below_unitMasks T) hphi
      exact hgSum_inSpan_ker h A D hA hDl ys 0 (by rw [hlen]; omega) hyb
        (fun y hy => hz _ (List.mem_map_of_mem hy)))
  rw [himg, hker] at hrn
  exact hrn.symm

end Family

end CodeCalculus
