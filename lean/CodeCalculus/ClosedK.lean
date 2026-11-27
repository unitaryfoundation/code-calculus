import CodeCalculus.ProductRank
import CodeCalculus.ConcatRetention
import CodeCalculus.ConstructorAssembly
import CodeCalculus.Eval

/-!
# Closed forms for `stateK` of `L-HGP` and `A-PRODUCT`

Each statement is the Lean counterpart of the hand derivation in
`spec/OPERATIONAL_SEMANTICS.md` §4.34 / §4.35.

The ranks of the natural check matrices (`hgp_rankX`, `hgp_rankZ`,
`product_rankX`, `product_rankZ`) are theorems, proved from the rank of
the two-block tensor family (`rank_hgRows`) and from row rank equals
column rank (`rank_colMasks`). Until 2026-11-24 they were axioms of
`lean/extra/ClosedK.lean`.

`k_i` and `k_iᵀ` are written below as `n_i - rank(H_i)` and
`m_i - rank(H_i)` respectively, matching `hypergraph_parameters` in
`machine/constructors.py`.
-/

namespace CodeCalculus

/-! ## `L-HGP` -/

/-- The rows of a typed binary matrix all have the length of the first. -/
theorem length_of_binaryMatrixTyped {H : List (List Bool)} (h : binaryMatrixTyped H = true) :
    ∀ r ∈ H, r.length = matCols H := by
  cases H with
  | nil => exact nomatch h
  | cons r0 rs =>
      intro r hr
      show r.length = r0.length
      unfold binaryMatrixTyped at h
      rw [Bool.and_eq_true] at h
      rcases List.mem_cons.mp hr with rfl | hr'
      · rfl
      · exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp h.2 r hr')

/-- The rank of a typed binary matrix is at most its number of columns. -/
theorem rank_le_matCols {H : List (List Bool)} (h : binaryMatrixTyped H = true) :
    rankBitmasks (H.map boolsToMask) ≤ matCols H := by
  apply rankBitmasks_le_of_high_bits_false
  intro m hm j hj
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
  rw [testBit_boolsToMask, List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (by rw [length_of_binaryMatrixTyped h r hr]; exact hj)]
  rfl

/-- The rank of a matrix is at most its number of rows. -/
theorem rank_le_rows (H : List (List Bool)) :
    rankBitmasks (H.map boolsToMask) ≤ H.length := by
  have h := rankBitmasks_le_length (H.map boolsToMask)
  rw [List.length_map] at h
  exact h

/-- The arithmetic of the `L-HGP` closed form, for ranks bounded by the
    numbers of rows and columns. -/
theorem hgp_arith_nat (m1 n1 m2 n2 r1 r2 : Nat) (h1 : r1 ≤ m1) (h2 : r1 ≤ n1)
    (h3 : r2 ≤ m2) (h4 : r2 ≤ n2) :
    (n1 * n2 + m1 * m2) - (m1 * n2 - (m1 - r1) * (n2 - r2)) -
        (n1 * m2 - (n1 - r1) * (m2 - r2)) =
      (n1 - r1) * (n2 - r2) + (m1 - r1) * (m2 - r2) := by
  obtain ⟨a1, rfl⟩ := Nat.exists_eq_add_of_le h1
  obtain ⟨b1, rfl⟩ := Nat.exists_eq_add_of_le h2
  obtain ⟨a2, rfl⟩ := Nat.exists_eq_add_of_le h3
  obtain ⟨b2, rfl⟩ := Nat.exists_eq_add_of_le h4
  simp only [Nat.add_sub_cancel_left, Nat.add_mul, Nat.mul_add]
  omega

/-- The arithmetic that turns the two rank identities above into the closed
    form. -/
theorem hgp_arith (H1 H2 : List (List Bool))
    (h1 : binaryMatrixTyped H1 = true) (h2 : binaryMatrixTyped H2 = true) :
    (matCols H1 * matCols H2 + H1.length * H2.length) -
      (H1.length * matCols H2 -
        (H1.length - rankBitmasks (H1.map boolsToMask)) *
          (matCols H2 - rankBitmasks (H2.map boolsToMask))) -
      (matCols H1 * H2.length -
        (matCols H1 - rankBitmasks (H1.map boolsToMask)) *
          (H2.length - rankBitmasks (H2.map boolsToMask))) =
    (matCols H1 - rankBitmasks (H1.map boolsToMask)) *
      (matCols H2 - rankBitmasks (H2.map boolsToMask)) +
    (H1.length - rankBitmasks (H1.map boolsToMask)) *
      (H2.length - rankBitmasks (H2.map boolsToMask)) :=
  hgp_arith_nat _ _ _ _ _ _ (rank_le_rows H1) (rank_le_matCols h1) (rank_le_rows H2)
    (rank_le_matCols h2)

/-- The rows of a typed binary matrix, as masks, are below `2 ^ matCols`. -/
theorem below_rowMasks {H : List (List Bool)} (h : binaryMatrixTyped H = true) :
    ∀ r ∈ H.map boolsToMask, Below (matCols H) r := by
  intro r hr
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
  rw [← length_of_binaryMatrixTyped h v hv]
  exact below_boolsToMask v

theorem below_colMasks_rows (n : Nat) (H : List (List Bool)) :
    ∀ c ∈ colMasks n (H.map boolsToMask), Below H.length c := by
  have h := below_colMasks n (H.map boolsToMask)
  rw [List.length_map] at h
  exact h

theorem hgp_rank_arith (m n r s : Nat) (hr : r ≤ m) (hs : s ≤ n) :
    r * n + (m - r) * s = m * n - (m - r) * (n - s) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hr
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hs
  simp only [Nat.add_sub_cancel_left, Nat.add_mul, Nat.mul_add]
  omega

/-- The natural `X`-row `(a, j)` of `hgp(H₁, H₂)` is the member `(a, j)` of
    the two-block family of the rows of `H₁` and the columns of `H₂`. -/
theorem hgpX_mask (H1 H2 : List (List Bool)) (a j : Nat) (ha : a < H1.length)
    (hj : j < matCols H2) :
    boolsToMask (hgpXVector H1 H2 (a, j)) =
      hgTerm id (· <<< (matCols H1 * matCols H2)) H1.length (matCols H2) (matCols H1)
        H2.length (H1.map boolsToMask) (colMasks (matCols H2) (H2.map boolsToMask))
        j (2 ^ a) := by
  have e1 : maskFn (matCols H1 * matCols H2)
        (fun k => decide (k % matCols H2 = j) && matEntry H1 a (k / matCols H2)) =
      tens (matCols H1) (matCols H2) ((H1.map boolsToMask).getD a 0) (2 ^ j) := by
    rw [← maskFn_tens_unit_right _ _ j _ hj]
    congr 1
    funext k
    rw [testBit_rowMask]
  have e2 : maskFn (H1.length * H2.length)
        (fun k => decide (k / H2.length = a) && matEntry H2 (k % H2.length) j) =
      tens H1.length H2.length (2 ^ a) (colMask (H2.map boolsToMask) j) := by
    have hb : Below H2.length (colMask (H2.map boolsToMask) j) := by
      have h := below_colMask (H2.map boolsToMask) j
      rw [List.length_map] at h
      exact h
    rw [← maskFn_tens_unit_left _ _ a _ hb]
    congr 1
    funext k
    rw [testBit_colMask_rows]
  unfold hgpXVector hgTerm
  rw [boolsToMask_append, List.length_map, length_indexPairs, boolsToMask_map_indexPairs,
    boolsToMask_map_indexPairs, comb_two_pow _ a (by rw [List.length_map]; exact ha),
    getD_colMasks, ite_eq_left_of_eq_true _ _ (eq_true hj)]
  show maskFn _ (fun k => decide (k % matCols H2 = j) && matEntry H1 a (k / matCols H2)) ^^^
      (maskFn _ (fun k => decide (k / H2.length = a) && matEntry H2 (k % H2.length) j) <<< _) =
    _
  rw [e1, e2]
  rfl

/-- The rank of the natural `X`-rows of `hgp(H₁, H₂)`. -/
theorem hgp_rankX (H1 H2 : List (List Bool))
    (h1 : binaryMatrixTyped H1 = true) (h2 : binaryMatrixTyped H2 = true) :
    rankBitmasks ((indexPairs (H1.length) (matCols H2)).map
      (fun aj => boolsToMask (hgpXVector H1 H2 aj))) =
      H1.length * matCols H2 -
        (H1.length - rankBitmasks (H1.map boolsToMask)) *
          (matCols H2 - rankBitmasks (H2.map boolsToMask)) := by
  have hlist : (indexPairs (H1.length) (matCols H2)).map
        (fun aj => boolsToMask (hgpXVector H1 H2 aj)) =
      hgRows id (· <<< (matCols H1 * matCols H2)) H1.length (matCols H2) (matCols H1)
        H2.length (H1.map boolsToMask) (colMasks (matCols H2) (H2.map boolsToMask)) := by
    unfold hgRows
    apply List.map_congr_left
    intro aj haj
    obtain ⟨a, j⟩ := aj
    obtain ⟨ha, hj⟩ := mem_indexPairs.mp haj
    exact hgpX_mask H1 H2 a j ha hj
  rw [hlist, rank_hgRows (hgLayout_low _ _ _ _) _ _ (List.length_map _) (length_colMasks _ _)
    (below_rowMasks h1) (below_colMasks_rows _ H2),
    rank_colMasks _ _ (below_rowMasks h2)]
  exact hgp_rank_arith _ _ _ _ (rank_le_rows H1) (rank_le_matCols h2)

/-- The natural `Z`-row `(i, b)` of `hgp(H₁, H₂)` is the member `(i, b)` of
    the two-block family of the columns of `H₁` and the rows of `H₂`. -/
theorem hgpZ_mask (H1 H2 : List (List Bool)) (h2 : binaryMatrixTyped H2 = true) (i b : Nat)
    (hi : i < matCols H1) (hb : b < H2.length) :
    boolsToMask (hgpZVector H1 H2 (i, b)) =
      hgTerm (· <<< (matCols H1 * matCols H2)) id (matCols H1) H2.length H1.length
        (matCols H2) (colMasks (matCols H1) (H1.map boolsToMask)) (H2.map boolsToMask)
        b (2 ^ i) := by
  have e1 : maskFn (matCols H1 * matCols H2)
        (fun k => decide (k / matCols H2 = i) && matEntry H2 b (k % matCols H2)) =
      tens (matCols H1) (matCols H2) (2 ^ i) ((H2.map boolsToMask).getD b 0) := by
    rw [← maskFn_tens_unit_left _ _ i _ (below_getD (below_rowMasks h2) b)]
    congr 1
    funext k
    rw [testBit_rowMask]
  have e2 : maskFn (H1.length * H2.length)
        (fun k => decide (k % H2.length = b) && matEntry H1 (k / H2.length) i) =
      tens H1.length H2.length (colMask (H1.map boolsToMask) i) (2 ^ b) := by
    rw [← maskFn_tens_unit_right _ _ b _ hb]
    congr 1
    funext k
    rw [testBit_colMask_rows]
  unfold hgpZVector hgTerm
  rw [boolsToMask_append, List.length_map, length_indexPairs, boolsToMask_map_indexPairs,
    boolsToMask_map_indexPairs, comb_two_pow _ i (by rw [length_colMasks]; exact hi),
    getD_colMasks, ite_eq_left_of_eq_true _ _ (eq_true hi)]
  show maskFn _ (fun k => decide (k / matCols H2 = i) && matEntry H2 b (k % matCols H2)) ^^^
      (maskFn _ (fun k => decide (k % H2.length = b) && matEntry H1 (k / H2.length) i) <<< _) =
    _
  rw [e1, e2, Nat.xor_comm]
  rfl

/-- The rank of the natural `Z`-rows of `hgp(H₁, H₂)`. -/
theorem hgp_rankZ (H1 H2 : List (List Bool))
    (h1 : binaryMatrixTyped H1 = true) (h2 : binaryMatrixTyped H2 = true) :
    rankBitmasks ((indexPairs (matCols H1) (H2.length)).map
      (fun ib => boolsToMask (hgpZVector H1 H2 ib))) =
      matCols H1 * H2.length -
        (matCols H1 - rankBitmasks (H1.map boolsToMask)) *
          (H2.length - rankBitmasks (H2.map boolsToMask)) := by
  have hlist : (indexPairs (matCols H1) (H2.length)).map
        (fun ib => boolsToMask (hgpZVector H1 H2 ib)) =
      hgRows (· <<< (matCols H1 * matCols H2)) id (matCols H1) H2.length H1.length
        (matCols H2) (colMasks (matCols H1) (H1.map boolsToMask)) (H2.map boolsToMask) := by
    unfold hgRows
    apply List.map_congr_left
    intro ib hib
    obtain ⟨i, b⟩ := ib
    obtain ⟨hi, hb⟩ := mem_indexPairs.mp hib
    exact hgpZ_mask H1 H2 h2 i b hi hb
  rw [hlist, rank_hgRows (hgLayout_high _ _ _ _) _ _ (length_colMasks _ _) (List.length_map _)
    (below_colMasks_rows _ H1) (below_rowMasks h2),
    rank_colMasks _ _ (below_rowMasks h1)]
  exact hgp_rank_arith _ _ _ _ (rank_le_matCols h1) (rank_le_rows H2)

theorem hgpState_k_closed (H1 H2 : List (List Bool))
    (h1 : binaryMatrixTyped H1 = true) (h2 : binaryMatrixTyped H2 = true) :
    stateK (hgpState H1 H2) =
      (matCols H1 - rankBitmasks (H1.map boolsToMask)) *
        (matCols H2 - rankBitmasks (H2.map boolsToMask)) +
      (H1.length - rankBitmasks (H1.map boolsToMask)) *
        (H2.length - rankBitmasks (H2.map boolsToMask)) := by
  unfold hgpState
  rw [stateK_constructedState (hgpQubits H1 H2) (hgpVectors H1 H2)]
  have hX : naturalMasks (hgpQubits H1 H2) (hgpVectors H1 H2) Sector.X =
      (indexPairs (H1.length) (matCols H2)).map
        (fun aj => boolsToMask (hgpXVector H1 H2 aj)) := by
    unfold hgpVectors
    have := naturalMasks_XZ (hgpQubits H1 H2)
      (fun aj => hgpXVector H1 H2 aj) (fun ib => hgpZVector H1 H2 ib)
      (indexPairs H1.length (matCols H2)) (indexPairs (matCols H1) (H2.length))
    rcases this with ⟨hX, _⟩
    have hpt : ∀ aj, vecMask (hgpQubits H1 H2) (hgpXVector H1 H2 aj) =
        boolsToMask (hgpXVector H1 H2 aj) := by
      intro aj; exact vecMask_eq_boolsToMask (hgpQubits H1 H2) (hgpXVector H1 H2 aj)
        (length_hgpXVector H1 H2 aj)
    rw [hX]
    exact List.map_congr_left (fun aj _ => hpt aj)
  have hZ : naturalMasks (hgpQubits H1 H2) (hgpVectors H1 H2) Sector.Z =
      (indexPairs (matCols H1) (H2.length)).map
        (fun ib => boolsToMask (hgpZVector H1 H2 ib)) := by
    unfold hgpVectors
    have := naturalMasks_XZ (hgpQubits H1 H2)
      (fun aj => hgpXVector H1 H2 aj) (fun ib => hgpZVector H1 H2 ib)
      (indexPairs H1.length (matCols H2)) (indexPairs (matCols H1) (H2.length))
    rcases this with ⟨_, hZ⟩
    have hpt : ∀ ib, vecMask (hgpQubits H1 H2) (hgpZVector H1 H2 ib) =
        boolsToMask (hgpZVector H1 H2 ib) := by
      intro ib; exact vecMask_eq_boolsToMask (hgpQubits H1 H2) (hgpZVector H1 H2 ib)
        (length_hgpZVector H1 H2 ib)
    rw [hZ]
    exact List.map_congr_left (fun ib _ => hpt ib)
  rw [hX, hZ]
  rw [hgp_rankX H1 H2 h1 h2, hgp_rankZ H1 H2 h1 h2]
  exact hgp_arith H1 H2 h1 h2

theorem evalExpr_hgp_k {H1 H2 : List (List Bool)} {s : CodeState}
    (h : EvalExpr (StateExpr.hgp H1 H2) s) :
    stateK s =
      (matCols H1 - rankBitmasks (H1.map boolsToMask)) *
        (matCols H2 - rankBitmasks (H2.map boolsToMask)) +
      (H1.length - rankBitmasks (H1.map boolsToMask)) *
        (H2.length - rankBitmasks (H2.map boolsToMask)) := by
  cases h with
  | hgp h1 h2 _ => exact hgpState_k_closed H1 H2 h1 h2

/-! ## `A-PRODUCT` -/

theorem below_rowMasks_of_length {H : List (List Bool)} {n : Nat}
    (h : ∀ r ∈ H, r.length = n) : ∀ r ∈ H.map boolsToMask, Below n r := by
  intro r hr
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
  rw [← h v hv]
  exact below_boolsToMask v

theorem boolsToMask_three (u v w : List Bool) :
    boolsToMask (u ++ v ++ w) = boolsToMask u ^^^ (boolsToMask v <<< u.length) ^^^
      (boolsToMask w <<< (u.length + v.length)) := by
  rw [boolsToMask_append, boolsToMask_append, List.length_append]

theorem dotCount_rowMasks (n : Nat) (MX MZ : List (List Bool)) (x z : Nat) :
    dotCount n ((MX.map boolsToMask).getD x 0) ((MZ.map boolsToMask).getD z 0) =
      ((List.range n).filter (fun i => matEntry MX x i && matEntry MZ z i)).length := by
  unfold dotCount
  congr 1
  apply List.filter_congr
  intro i _
  rw [testBit_rowMask, testBit_rowMask]

/-- A row of `MX` has zero combination of the columns of `MZ`. -/
theorem comb_colMasks_Z_of_commute (n : Nat) (MX MZ : List (List Bool))
    (h : MatricesCommute n MX MZ) (x : Nat) (hx : x < MX.length) :
    comb (colMasks n (MZ.map boolsToMask)) ((MX.map boolsToMask).getD x 0) = 0 := by
  apply comb_colMasks_eq_zero
  intro z hz
  rw [List.length_map] at hz
  rw [dotCount_comm, dotCount_rowMasks]
  exact h x z hx hz

/-- A row of `MZ` has zero combination of the columns of `MX`. -/
theorem comb_colMasks_X_of_commute (n : Nat) (MX MZ : List (List Bool))
    (h : MatricesCommute n MX MZ) (z : Nat) (hz : z < MZ.length) :
    comb (colMasks n (MX.map boolsToMask)) ((MZ.map boolsToMask).getD z 0) = 0 := by
  apply comb_colMasks_eq_zero
  intro x hx
  rw [List.length_map] at hx
  rw [dotCount_rowMasks]
  exact h x z hx hz

section ProductMasks

variable (na nb : Nat) (AX AZ BX BZ : List (List Bool))

theorem productX1_mask (hBX : ∀ r ∈ BX, r.length = nb) (i x : Nat) (hx : x < BX.length) :
    boolsToMask (productX1 na nb AX AZ BX BZ (i, x)) =
      tens AZ.length BX.length (colMask (AZ.map boolsToMask) i) (2 ^ x) ^^^
        (tens na nb (2 ^ i) ((BX.map boolsToMask).getD x 0) <<< (AZ.length * BX.length)) := by
  have e1 : maskFn (AZ.length * BX.length)
        (fun k => decide (k % BX.length = x) && matEntry AZ (k / BX.length) i) =
      tens AZ.length BX.length (colMask (AZ.map boolsToMask) i) (2 ^ x) := by
    rw [← maskFn_tens_unit_right _ _ x _ hx]
    congr 1
    funext k
    rw [testBit_colMask_rows]
  have e2 : maskFn (na * nb) (fun k => decide (k / nb = i) && matEntry BX x (k % nb)) =
      tens na nb (2 ^ i) ((BX.map boolsToMask).getD x 0) := by
    rw [← maskFn_tens_unit_left _ _ i _ (below_getD (below_rowMasks_of_length hBX) x)]
    congr 1
    funext k
    rw [testBit_rowMask]
  unfold productX1
  rw [boolsToMask_three, List.length_map, List.length_map, length_indexPairs, length_indexPairs,
    boolsToMask_map_indexPairs, boolsToMask_map_indexPairs, boolsToMask_map_indexPairs,
    maskFn_false, Nat.zero_shiftLeft, Nat.xor_zero]
  show maskFn _ (fun k => decide (k % BX.length = x) && matEntry AZ (k / BX.length) i) ^^^
      (maskFn _ (fun k => decide (k / nb = i) && matEntry BX x (k % nb)) <<< _) = _
  rw [e1, e2]

theorem productX2_mask (x j : Nat) (hj : j < nb) :
    boolsToMask (productX2 na nb AX AZ BX BZ (x, j)) =
      (tens na nb ((AX.map boolsToMask).getD x 0) (2 ^ j) <<< (AZ.length * BX.length)) ^^^
        (tens AX.length BZ.length (2 ^ x) (colMask (BZ.map boolsToMask) j) <<<
          (AZ.length * BX.length + na * nb)) := by
  have e2 : maskFn (na * nb) (fun k => decide (k % nb = j) && matEntry AX x (k / nb)) =
      tens na nb ((AX.map boolsToMask).getD x 0) (2 ^ j) := by
    rw [← maskFn_tens_unit_right _ _ j _ hj]
    congr 1
    funext k
    rw [testBit_rowMask]
  have e3 : maskFn (AX.length * BZ.length)
        (fun k => decide (k / BZ.length = x) && matEntry BZ (k % BZ.length) j) =
      tens AX.length BZ.length (2 ^ x) (colMask (BZ.map boolsToMask) j) := by
    have hb : Below BZ.length (colMask (BZ.map boolsToMask) j) := by
      have h := below_colMask (BZ.map boolsToMask) j
      rw [List.length_map] at h
      exact h
    rw [← maskFn_tens_unit_left _ _ x _ hb]
    congr 1
    funext k
    rw [testBit_colMask_rows]
  unfold productX2
  rw [boolsToMask_three, List.length_map, List.length_map, length_indexPairs, length_indexPairs,
    boolsToMask_map_indexPairs, boolsToMask_map_indexPairs, boolsToMask_map_indexPairs,
    maskFn_false, Nat.zero_xor]
  show (maskFn _ (fun k => decide (k % nb = j) && matEntry AX x (k / nb)) <<< _) ^^^
      (maskFn _ (fun k => decide (k / BZ.length = x) && matEntry BZ (k % BZ.length) j) <<< _) =
    _
  rw [e2, e3]

theorem productZ1_mask (z j : Nat) (hj : j < nb) :
    boolsToMask (productZ1 na nb AX AZ BX BZ (z, j)) =
      tens AZ.length BX.length (2 ^ z) (colMask (BX.map boolsToMask) j) ^^^
        (tens na nb ((AZ.map boolsToMask).getD z 0) (2 ^ j) <<< (AZ.length * BX.length)) := by
  have e1 : maskFn (AZ.length * BX.length)
        (fun k => decide (k / BX.length = z) && matEntry BX (k % BX.length) j) =
      tens AZ.length BX.length (2 ^ z) (colMask (BX.map boolsToMask) j) := by
    have hb : Below BX.length (colMask (BX.map boolsToMask) j) := by
      have h := below_colMask (BX.map boolsToMask) j
      rw [List.length_map] at h
      exact h
    rw [← maskFn_tens_unit_left _ _ z _ hb]
    congr 1
    funext k
    rw [testBit_colMask_rows]
  have e2 : maskFn (na * nb) (fun k => decide (k % nb = j) && matEntry AZ z (k / nb)) =
      tens na nb ((AZ.map boolsToMask).getD z 0) (2 ^ j) := by
    rw [← maskFn_tens_unit_right _ _ j _ hj]
    congr 1
    funext k
    rw [testBit_rowMask]
  unfold productZ1
  rw [boolsToMask_three, List.length_map, List.length_map, length_indexPairs, length_indexPairs,
    boolsToMask_map_indexPairs, boolsToMask_map_indexPairs, boolsToMask_map_indexPairs,
    maskFn_false, Nat.zero_shiftLeft, Nat.xor_zero]
  show maskFn _ (fun k => decide (k / BX.length = z) && matEntry BX (k % BX.length) j) ^^^
      (maskFn _ (fun k => decide (k % nb = j) && matEntry AZ z (k / nb)) <<< _) = _
  rw [e1, e2]

theorem productZ2_mask (hBZ : ∀ r ∈ BZ, r.length = nb) (i z : Nat) (hz : z < BZ.length) :
    boolsToMask (productZ2 na nb AX AZ BX BZ (i, z)) =
      (tens na nb (2 ^ i) ((BZ.map boolsToMask).getD z 0) <<< (AZ.length * BX.length)) ^^^
        (tens AX.length BZ.length (colMask (AX.map boolsToMask) i) (2 ^ z) <<<
          (AZ.length * BX.length + na * nb)) := by
  have e2 : maskFn (na * nb) (fun k => decide (k / nb = i) && matEntry BZ z (k % nb)) =
      tens na nb (2 ^ i) ((BZ.map boolsToMask).getD z 0) := by
    rw [← maskFn_tens_unit_left _ _ i _ (below_getD (below_rowMasks_of_length hBZ) z)]
    congr 1
    funext k
    rw [testBit_rowMask]
  have e3 : maskFn (AX.length * BZ.length)
        (fun k => decide (k % BZ.length = z) && matEntry AX (k / BZ.length) i) =
      tens AX.length BZ.length (colMask (AX.map boolsToMask) i) (2 ^ z) := by
    rw [← maskFn_tens_unit_right _ _ z _ hz]
    congr 1
    funext k
    rw [testBit_colMask_rows]
  unfold productZ2
  rw [boolsToMask_three, List.length_map, List.length_map, length_indexPairs, length_indexPairs,
    boolsToMask_map_indexPairs, boolsToMask_map_indexPairs, boolsToMask_map_indexPairs,
    maskFn_false, Nat.zero_xor]
  show (maskFn _ (fun k => decide (k / nb = i) && matEntry BZ z (k % nb)) <<< _) ^^^
      (maskFn _ (fun k => decide (k % BZ.length = z) && matEntry AX (k / BZ.length) i) <<< _) =
    _
  rw [e2, e3]

/-- The map that reads the middle block of a product row. -/
def productMid (N1 N2 : Nat) (v : Nat) : Nat := (v >>> N1) % 2 ^ N2

theorem productMid_xor (N1 N2 x y : Nat) :
    productMid N1 N2 (x ^^^ y) = productMid N1 N2 x ^^^ productMid N1 N2 y := by
  unfold productMid
  rw [Nat.shiftRight_xor_distrib, Nat.xor_mod_two_pow]

theorem productMid_mid (N1 N2 x : Nat) (h : Below N2 x) : productMid N1 N2 (x <<< N1) = x := by
  unfold productMid
  rw [Nat.shiftLeft_shiftRight]
  exact Nat.mod_eq_of_lt (Nat.lt_pow_two_of_testBit x h)

theorem productMid_low (N1 N2 x : Nat) (h : Below N1 x) : productMid N1 N2 x = 0 := by
  unfold productMid
  rw [shiftRight_eq_zero_of_below h]
  exact Nat.zero_mod _

theorem productMid_high (N1 N2 x : Nat) : productMid N1 N2 (x <<< (N1 + N2)) = 0 := by
  unfold productMid
  rw [Nat.add_comm, Nat.shiftLeft_add, Nat.shiftLeft_shiftRight]
  exact shiftLeft_mod_two_pow x N2

/-- The rank of the natural `X`-rows of the product, for the factors'
    sector matrices. -/
theorem productX_rank (hAX : ∀ r ∈ AX, r.length = na) (hBX : ∀ r ∈ BX, r.length = nb)
    (hcA : MatricesCommute na AX AZ) (hcB : MatricesCommute nb BX BZ)
    (hiA : independentMasks (AX.map boolsToMask))
    (hiB : independentMasks (BX.map boolsToMask)) :
    rankBitmasks ((productXVectors na nb AX AZ BX BZ).map boolsToMask) =
      na * BX.length + AX.length * nb - AX.length * BX.length := by
  have hdata : ProdData (· <<< (AZ.length * BX.length))
      (productMid (AZ.length * BX.length) (na * nb))
      (fun i x => tens AZ.length BX.length (colMask (AZ.map boolsToMask) i) (2 ^ x))
      (fun x j => tens AX.length BZ.length (2 ^ x) (colMask (BZ.map boolsToMask) j) <<<
        (AZ.length * BX.length + na * nb))
      na nb (AX.map boolsToMask) (BX.map boolsToMask) :=
    { mu_xor := fun x y => shiftLeft_xor _ x y
      phi_xor := productMid_xor _ _
      phi_mu := fun x hx => productMid_mid _ _ x hx
      phi_E1 := fun i x hx => by
        rw [List.length_map] at hx
        exact productMid_low _ _ _ (below_tens _ _ _ _ (below_two_pow hx))
      phi_E2 := fun x j _ => productMid_high _ _ _
      indepP := hiA
      indepQ := hiB
      belowP := below_rowMasks_of_length hAX
      belowQ := below_rowMasks_of_length hBX
      dep := fun x' x hx' hx => by
        rw [List.length_map] at hx' hx
        have e1 : (List.range na).map (fun i =>
              tens AZ.length BX.length (colMask (AZ.map boolsToMask) i) (2 ^ x)) =
            (colMasks na (AZ.map boolsToMask)).map
              (fun c => tens AZ.length BX.length c (2 ^ x)) := by
          unfold colMasks
          rw [List.map_map]
          rfl
        have e2 : (List.range nb).map (fun j =>
              tens AX.length BZ.length (2 ^ x') (colMask (BZ.map boolsToMask) j) <<<
                (AZ.length * BX.length + na * nb)) =
            (colMasks nb (BZ.map boolsToMask)).map
              (fun c => tens AX.length BZ.length (2 ^ x') c <<<
                (AZ.length * BX.length + na * nb)) := by
          unfold colMasks
          rw [List.map_map]
          rfl
        rw [e1, e2,
          comb_map_additive (fun c => tens AZ.length BX.length c (2 ^ x))
            (fun c d => tens_xor_left _ _ c d _),
          comb_map_additive (fun c => tens AX.length BZ.length (2 ^ x') c <<<
              (AZ.length * BX.length + na * nb))
            (fun c d => by
              show tens _ _ _ (c ^^^ d) <<< _ = _
              rw [tens_xor_right, shiftLeft_xor]),
          comb_colMasks_Z_of_commute na AX AZ hcA x' hx',
          comb_colMasks_Z_of_commute nb BX BZ hcB x hx, tens_zero_left, tens_zero_right,
          Nat.zero_shiftLeft, Nat.xor_self] }
  have hlist : (productXVectors na nb AX AZ BX BZ).map boolsToMask =
      prodRows1 (· <<< (AZ.length * BX.length))
          (fun i x => tens AZ.length BX.length (colMask (AZ.map boolsToMask) i) (2 ^ x))
          na nb (BX.map boolsToMask) ++
        prodRows2 (· <<< (AZ.length * BX.length))
          (fun x j => tens AX.length BZ.length (2 ^ x) (colMask (BZ.map boolsToMask) j) <<<
            (AZ.length * BX.length + na * nb))
          na nb (AX.map boolsToMask) := by
    unfold productXVectors prodRows1 prodRows2
    rw [List.map_append, List.map_map, List.map_map, List.length_map, List.length_map]
    congr 1
    · apply List.map_congr_left
      intro ix hix
      obtain ⟨i, x⟩ := ix
      obtain ⟨_, hx⟩ := mem_indexPairs.mp hix
      exact productX1_mask na nb AX AZ BX BZ hBX i x hx
    · apply List.map_congr_left
      intro xj hxj
      obtain ⟨x, j⟩ := xj
      obtain ⟨_, hj⟩ := mem_indexPairs.mp hxj
      show boolsToMask (productX2 na nb AX AZ BX BZ (x, j)) = _
      rw [productX2_mask na nb AX AZ BX BZ x j hj, Nat.xor_comm]
  rw [hlist, rank_prodRows hdata, List.length_map, List.length_map]

/-- The rank of the natural `Z`-rows of the product, for the factors'
    sector matrices. -/
theorem productZ_rank (hAZ : ∀ r ∈ AZ, r.length = na) (hBZ : ∀ r ∈ BZ, r.length = nb)
    (hcA : MatricesCommute na AX AZ) (hcB : MatricesCommute nb BX BZ)
    (hiA : independentMasks (AZ.map boolsToMask))
    (hiB : independentMasks (BZ.map boolsToMask)) :
    rankBitmasks ((productZVectors na nb AX AZ BX BZ).map boolsToMask) =
      na * BZ.length + AZ.length * nb - AZ.length * BZ.length := by
  have hdata : ProdData (· <<< (AZ.length * BX.length))
      (productMid (AZ.length * BX.length) (na * nb))
      (fun i z => tens AX.length BZ.length (colMask (AX.map boolsToMask) i) (2 ^ z) <<<
        (AZ.length * BX.length + na * nb))
      (fun z j => tens AZ.length BX.length (2 ^ z) (colMask (BX.map boolsToMask) j))
      na nb (AZ.map boolsToMask) (BZ.map boolsToMask) :=
    { mu_xor := fun x y => shiftLeft_xor _ x y
      phi_xor := productMid_xor _ _
      phi_mu := fun x hx => productMid_mid _ _ x hx
      phi_E1 := fun i z _ => productMid_high _ _ _
      phi_E2 := fun z j _ => by
        have hb : Below BX.length (colMask (BX.map boolsToMask) j) := by
          have h := below_colMask (BX.map boolsToMask) j
          rw [List.length_map] at h
          exact h
        exact productMid_low _ _ _ (below_tens _ _ _ _ hb)
      indepP := hiA
      indepQ := hiB
      belowP := below_rowMasks_of_length hAZ
      belowQ := below_rowMasks_of_length hBZ
      dep := fun z' z hz' hz => by
        rw [List.length_map] at hz' hz
        have e1 : (List.range na).map (fun i =>
              tens AX.length BZ.length (colMask (AX.map boolsToMask) i) (2 ^ z) <<<
                (AZ.length * BX.length + na * nb)) =
            (colMasks na (AX.map boolsToMask)).map
              (fun c => tens AX.length BZ.length c (2 ^ z) <<<
                (AZ.length * BX.length + na * nb)) := by
          unfold colMasks
          rw [List.map_map]
          rfl
        have e2 : (List.range nb).map (fun j =>
              tens AZ.length BX.length (2 ^ z') (colMask (BX.map boolsToMask) j)) =
            (colMasks nb (BX.map boolsToMask)).map
              (fun c => tens AZ.length BX.length (2 ^ z') c) := by
          unfold colMasks
          rw [List.map_map]
          rfl
        rw [e1, e2,
          comb_map_additive (fun c => tens AX.length BZ.length c (2 ^ z) <<<
              (AZ.length * BX.length + na * nb))
            (fun c d => by
              show tens _ _ (c ^^^ d) _ <<< _ = _
              rw [tens_xor_left, shiftLeft_xor]),
          comb_map_additive (fun c => tens AZ.length BX.length (2 ^ z') c)
            (fun c d => tens_xor_right _ _ _ c d),
          comb_colMasks_X_of_commute na AX AZ hcA z' hz',
          comb_colMasks_X_of_commute nb BX BZ hcB z hz, tens_zero_left, tens_zero_right,
          Nat.zero_shiftLeft, Nat.xor_self] }
  have hlist : (productZVectors na nb AX AZ BX BZ).map boolsToMask =
      prodRows2 (· <<< (AZ.length * BX.length))
          (fun z j => tens AZ.length BX.length (2 ^ z) (colMask (BX.map boolsToMask) j))
          na nb (AZ.map boolsToMask) ++
        prodRows1 (· <<< (AZ.length * BX.length))
          (fun i z => tens AX.length BZ.length (colMask (AX.map boolsToMask) i) (2 ^ z) <<<
            (AZ.length * BX.length + na * nb))
          na nb (BZ.map boolsToMask) := by
    unfold productZVectors prodRows1 prodRows2
    rw [List.map_append, List.map_map, List.map_map, List.length_map, List.length_map]
    congr 1
    · apply List.map_congr_left
      intro zj hzj
      obtain ⟨z, j⟩ := zj
      obtain ⟨_, hj⟩ := mem_indexPairs.mp hzj
      exact productZ1_mask na nb AX AZ BX BZ z j hj
    · apply List.map_congr_left
      intro iz hiz
      obtain ⟨i, z⟩ := iz
      obtain ⟨_, hz⟩ := mem_indexPairs.mp hiz
      show boolsToMask (productZ2 na nb AX AZ BX BZ (i, z)) = _
      rw [productZ2_mask na nb AX AZ BX BZ hBZ i z hz, Nat.xor_comm]
  rw [hlist, rankBitmasks_append_comm, rank_prodRows hdata, List.length_map, List.length_map]

end ProductMasks

theorem length_sectorMatrix_rows (s : CodeState) (σ : Sector) :
    ∀ v ∈ sectorMatrix s σ, v.length = s.Q.length := by
  intro v hv
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hv
  exact rowVector_length s.Q r

theorem length_sectorMatrix (s : CodeState) (σ : Sector) :
    (sectorMatrix s σ).length = (sectorRows s σ).length := by
  unfold sectorMatrix sectorRows
  rw [List.length_map]

/-- The displayed rows of one sector of a well-formed state are independent
    as masks. -/
theorem independent_sectorMasks (s : CodeState) (hwf : EncodingWellFormed s) (σ : Sector) :
    independentMasks ((sectorMatrix s σ).map boolsToMask) := by
  have h := independentMasks_of_vecIndep s.Q.length ((sectorRows s σ).map (rowVector s.Q))
    (fun v hv => by
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hv
      exact rowVector_length s.Q r) (vecIndep_sectorRows s hwf σ)
  have e : ((sectorRows s σ).map (rowVector s.Q)).map (vecMask s.Q.length) =
      (sectorMatrix s σ).map boolsToMask := by
    show (sectorMatrix s σ).map (vecMask s.Q.length) = _
    apply List.map_congr_left
    intro v hv
    exact vecMask_eq_boolsToMask _ v (length_sectorMatrix_rows s σ v hv)
  rw [e] at h
  exact h

/-- Rank of the `X`-sector of the natural rows of `A-PRODUCT`, as a
    function of the factors' qubit counts and displayed row counts. -/
theorem product_rankX (A B : CodeState)
    (hA : EncodingWellFormed A) (hB : EncodingWellFormed B) :
    rankBitmasks (naturalMasks (productQubits A B) (productVectors A B) Sector.X) =
      A.Q.length * (sectorRows B Sector.X).length +
      (sectorRows A Sector.X).length * B.Q.length -
      (sectorRows A Sector.X).length * (sectorRows B Sector.X).length := by
  have hmasks : naturalMasks (productQubits A B) (productVectors A B) Sector.X =
      (productXVectors A.Q.length B.Q.length (sectorMatrix A Sector.X)
        (sectorMatrix A Sector.Z) (sectorMatrix B Sector.X) (sectorMatrix B Sector.Z)).map
        boolsToMask := by
    unfold productVectors
    rw [(naturalMasks_XZ (productQubits A B) (fun v => v) (fun v => v) _ _).1]
    apply List.map_congr_left
    intro v hv
    exact vecMask_eq_boolsToMask _ v (length_productXVectors _ _ _ _ _ _ v hv)
  rw [hmasks, productX_rank _ _ _ _ _ _ (length_sectorMatrix_rows A Sector.X)
    (length_sectorMatrix_rows B Sector.X) (sectorMatrix_commute A hA)
    (sectorMatrix_commute B hB) (independent_sectorMasks A hA Sector.X)
    (independent_sectorMasks B hB Sector.X), length_sectorMatrix, length_sectorMatrix]

/-- Rank of the `Z`-sector of the natural rows of `A-PRODUCT`. -/
theorem product_rankZ (A B : CodeState)
    (hA : EncodingWellFormed A) (hB : EncodingWellFormed B) :
    rankBitmasks (naturalMasks (productQubits A B) (productVectors A B) Sector.Z) =
      A.Q.length * (sectorRows B Sector.Z).length +
      (sectorRows A Sector.Z).length * B.Q.length -
      (sectorRows A Sector.Z).length * (sectorRows B Sector.Z).length := by
  have hmasks : naturalMasks (productQubits A B) (productVectors A B) Sector.Z =
      (productZVectors A.Q.length B.Q.length (sectorMatrix A Sector.X)
        (sectorMatrix A Sector.Z) (sectorMatrix B Sector.X) (sectorMatrix B Sector.Z)).map
        boolsToMask := by
    unfold productVectors
    rw [(naturalMasks_XZ (productQubits A B) (fun v => v) (fun v => v) _ _).2]
    apply List.map_congr_left
    intro v hv
    exact vecMask_eq_boolsToMask _ v (length_productZVectors _ _ _ _ _ _ v hv)
  rw [hmasks, productZ_rank _ _ _ _ _ _ (length_sectorMatrix_rows A Sector.Z)
    (length_sectorMatrix_rows B Sector.Z) (sectorMatrix_commute A hA)
    (sectorMatrix_commute B hB) (independent_sectorMasks A hA Sector.Z)
    (independent_sectorMasks B hB Sector.Z), length_sectorMatrix, length_sectorMatrix]

/-- On a well-formed state the displayed rows of the two sectors number at
    most the qubits. -/
theorem rows_le_qubits (s : CodeState) (hwf : EncodingWellFormed s) :
    (sectorRows s Sector.X).length + (sectorRows s Sector.Z).length ≤ s.Q.length := by
  have hfit := ranksFit_of_wf s hwf
  obtain ⟨hQ, hids, _, _, _, _, _, hI2⟩ := hwf
  unfold RanksFit at hfit
  rw [sectorRank_eq_length_of_I2 s hQ hids hI2 Sector.X,
    sectorRank_eq_length_of_I2 s hQ hids hI2 Sector.Z] at hfit
  exact hfit

/-- The arithmetic of the `A-PRODUCT` closed form, for row counts bounded
    by the qubit counts. -/
theorem product_arith_nat (nA xA zA nB xB zB : Nat) (hA : xA + zA ≤ nA)
    (hB : xB + zB ≤ nB) :
    zA * xB + nA * nB + xA * zB - (nA * xB + xA * nB - xA * xB) -
        (nA * zB + zA * nB - zA * zB) =
      (nA - xA - zA) * (nB - xB - zB) := by
  obtain ⟨kA, rfl⟩ := Nat.exists_eq_add_of_le hA
  obtain ⟨kB, rfl⟩ := Nat.exists_eq_add_of_le hB
  have eA : xA + zA + kA - xA - zA = kA := by omega
  have eB : xB + zB + kB - xB - zB = kB := by omega
  rw [eA, eB]
  simp only [Nat.add_mul, Nat.mul_add]
  omega

/-- The arithmetic that turns the two rank identities above into
    `k_prod = k_A * k_B`. -/
theorem product_arith (A B : CodeState)
    (hA : EncodingWellFormed A) (hB : EncodingWellFormed B) :
    (sectorRows A Sector.Z).length * (sectorRows B Sector.X).length +
      A.Q.length * B.Q.length +
      (sectorRows A Sector.X).length * (sectorRows B Sector.Z).length -
    (A.Q.length * (sectorRows B Sector.X).length +
      (sectorRows A Sector.X).length * B.Q.length -
      (sectorRows A Sector.X).length * (sectorRows B Sector.X).length) -
    (A.Q.length * (sectorRows B Sector.Z).length +
      (sectorRows A Sector.Z).length * B.Q.length -
      (sectorRows A Sector.Z).length * (sectorRows B Sector.Z).length) =
    stateK A * stateK B := by
  rw [stateK_of_wf A hA, stateK_of_wf B hB]
  exact product_arith_nat _ _ _ _ _ _ (rows_le_qubits A hA) (rows_le_qubits B hB)

/-- Closed form for the logical count of the CSS tensor product. -/
theorem productState_k_closed (A B : CodeState)
    (hA : EncodingWellFormed A) (hB : EncodingWellFormed B) :
    stateK (productState A B) = stateK A * stateK B := by
  unfold productState
  rw [stateK_constructedState]
  rw [product_rankX A B hA hB, product_rankZ A B hA hB]
  unfold productQubits sectorMatrix
  simp only [List.length_map]
  exact product_arith A B hA hB

theorem evalExpr_product_k {eA eB : StateExpr} {s : CodeState}
    (h : EvalExpr (StateExpr.product eA eB) s) :
    ∃ sA sB, EvalExpr eA sA ∧ EvalExpr eB sB ∧
      stateK s = stateK sA * stateK sB := by
  cases h with
  | product hAwf hBwf _ hEvalA hEvalB =>
      exact ⟨_, _, hEvalA, hEvalB, productState_k_closed _ _ hAwf hBwf⟩

end CodeCalculus
