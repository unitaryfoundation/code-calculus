import CodeCalculus.Eval

namespace CodeCalculus

/-! ### Mask-level F₂ algebra for the rebase rank argument

Support for the rank-preservation argument owed for the `P-REBASE`
conditional cell (`spec/JUDGMENT_LAYER.md` §2a; hand derivation in
`spec/OPERATIONAL_SEMANTICS.md` §4.26). The argument is an F₂ span argument
under a GL basis change; this module carries its mask-level toolkit:

- `combineMasks` algebra: the F₂ combination of a mask list by a
  coefficient list;
- `combineCoeffRowsM` and `combineMasks_combineCoeffRowsM`: composition of
  two F₂ linear maps, stated at mask level;
- the bit anatomy of `matrixRowMask` (`testBit_matrixRowMask`) and the
  entry↔bit bridge `combineCoeffRowsM_testBit_matrixRowMask`, which transport
  the `rebaseMatrix_ok` rank clause (`rankBitmasks (matrix.map matrixRowMask)
  = m`) to entry statements about `combineCoeffRowsM`;
- `unitRow`, the coefficient list selecting one displayed row;
- the `spanList` enumeration and `independentMasks` facts used by the
  counting step in `MaskRank`.

Statements about these list functions only; no soundness claim for the
calculus is made here (README *Status*). -/

theorem xor_right_cancel {a b x : Nat} (h : a ^^^ x = b ^^^ x) : a = b := by
  have key : (a ^^^ x) ^^^ x = (b ^^^ x) ^^^ x := by rw [h]
  calc
    a = a ^^^ x ^^^ x := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    _ = b ^^^ x ^^^ x := by rw [key]
    _ = b := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem xor_eq_zero_cancel {a b : Nat} (h : a ^^^ b = 0) : a = b := by
  apply xor_right_cancel (x := b)
  calc a ^^^ b = 0 := h
    _ = b ^^^ b := (Nat.xor_self b).symm

theorem xor_mem01 {a b : Nat} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    a ^^^ b = 0 ∨ a ^^^ b = 1 := by
  rcases ha with rfl | rfl
  <;> rcases hb with rfl | rfl
  <;> simp [Nat.zero_xor]

/-- A combination whose every coefficient is zero is zero. -/
theorem combineMasks_zero_coeffs (ms cs : List Nat) (h : ∀ c ∈ cs, c = 0) :
    combineMasks ms cs = 0 := by
  induction ms generalizing cs with
  | nil => exact combineMasks_nil cs
  | cons m ms ih =>
    cases cs with
    | nil => rfl
    | cons c cs =>
      have hc : c = 0 := h c (List.mem_cons_self ..)
      have hcs : ∀ x ∈ cs, x = 0 := fun x hx => h x (List.mem_cons_of_mem _ hx)
      rw [combineMasks_cons, hc]
      simp [ih cs hcs]

/-- Combining with the entrywise F₂ difference of two 0/1 coefficient lists
    splits into the two combinations. -/
theorem combineMasks_zipWith_xor (xs ca cb : List Nat)
    (hca : ca.length = xs.length) (hcb : cb.length = xs.length)
    (hca01 : ∀ c ∈ ca, c = 0 ∨ c = 1) (hcb01 : ∀ c ∈ cb, c = 0 ∨ c = 1) :
    combineMasks xs (List.zipWith (· ^^^ ·) ca cb) =
      combineMasks xs ca ^^^ combineMasks xs cb := by
  induction xs generalizing ca cb with
  | nil =>
      cases ca <;> cases cb <;> simp [combineMasks]
  | cons x xs ih =>
      cases ca with
      | nil => simp at hca
      | cons a as =>
        cases cb with
        | nil => simp at hcb
        | cons b bs =>
          have ihs := ih as bs (by simpa using hca) (by simpa using hcb)
              (fun c hc => hca01 c (by simp [hc]))
              (fun c hc => hcb01 c (by simp [hc]))
          have ha01 : a = 0 ∨ a = 1 := hca01 a (by simp)
          have hb01 : b = 0 ∨ b = 1 := hcb01 b (by simp)
          rcases ha01 with rfl | rfl
          · rcases hb01 with rfl | rfl
            · -- a = 0, b = 0
              simp [combineMasks, Nat.zero_xor]
              exact ihs
            · -- a = 0, b = 1
              simp [combineMasks, Nat.zero_xor]
              rw [ihs]
              calc
                x ^^^ (combineMasks xs as ^^^ combineMasks xs bs)
                    = x ^^^ combineMasks xs as ^^^ combineMasks xs bs :=
                    (Nat.xor_assoc x (combineMasks xs as) (combineMasks xs bs)).symm
                _ = combineMasks xs as ^^^ x ^^^ combineMasks xs bs := by
                    rw [Nat.xor_comm x (combineMasks xs as)]
                _ = combineMasks xs as ^^^ (x ^^^ combineMasks xs bs) :=
                    Nat.xor_assoc (combineMasks xs as) x (combineMasks xs bs)
          · rcases hb01 with rfl | rfl
            · -- a = 1, b = 0
              simp [combineMasks, Nat.zero_xor]
              rw [ihs]
              exact (Nat.xor_assoc x (combineMasks xs as) (combineMasks xs bs)).symm
            · -- a = 1, b = 1
              simp [combineMasks]
              rw [ihs]
              symm
              rw [← Nat.xor_assoc (x ^^^ combineMasks xs as) x (combineMasks xs bs)]
              rw [Nat.xor_assoc x (combineMasks xs as) x]
              rw [Nat.xor_comm (combineMasks xs as) x]
              rw [← Nat.xor_assoc x x (combineMasks xs as)]
              rw [Nat.xor_self x]
              rw [Nat.zero_xor]

theorem mem_zipWith_xor (as : List Nat) : ∀ (bs : List Nat) (c : Nat),
    c ∈ List.zipWith (· ^^^ ·) as bs → ∃ x ∈ as, ∃ y ∈ bs, c = x ^^^ y := by
  induction as with
  | nil =>
      intro bs c h
      simp [List.zipWith] at h
  | cons a as ih =>
      intro bs c h
      cases bs with
      | nil => simp [List.zipWith] at h
      | cons b bs =>
          rw [List.zipWith_cons_cons] at h
          rcases List.mem_cons.mp h with rfl | h
          · exact ⟨a, List.mem_cons_self .., b, List.mem_cons_self .., rfl⟩
          · rcases ih bs c h with ⟨x, hx, y, hy, hxy⟩
            exact ⟨x, List.mem_cons_of_mem _ hx, y, List.mem_cons_of_mem _ hy, hxy⟩

/-- Componentwise F₂ sum of the coefficient rows selected by `cs`, with an
    explicit column count `m` fixing the zero row emitted when the matrix
    runs out of rows before the coefficients do. -/
def combineCoeffRowsM (m : Nat) : List (List Nat) → List Nat → List Nat
  | [], _ => List.replicate m 0
  | _ :: _, [] => List.replicate m 0
  | row :: rows, c :: cs =>
      let rest := combineCoeffRowsM m rows cs
      if c = 1 then List.zipWith (· ^^^ ·) row rest else rest

theorem combineCoeffRowsM_01 (m : Nat) : ∀ (rows : List (List Nat)),
    (∀ row ∈ rows, ∀ c ∈ row, c = 0 ∨ c = 1) →
    ∀ (cs : List Nat), ∀ c ∈ combineCoeffRowsM m rows cs, c = 0 ∨ c = 1 := by
  intro rows
  induction rows with
  | nil =>
      intro _ cs c hc
      have hc0 : c = 0 := by
        simp only [combineCoeffRowsM, List.mem_replicate] at hc
        exact hc.2
      exact Or.inl hc0
  | cons row rows ih =>
      intro h01 cs c hc
      cases cs with
      | nil =>
          have hc0 : c = 0 := by
            simp only [combineCoeffRowsM, List.mem_replicate] at hc
            exact hc.2
          exact Or.inl hc0
      | cons kk ks =>
          simp only [combineCoeffRowsM] at hc
          by_cases hsel : kk = 1
          · simp only [hsel] at hc
            rcases mem_zipWith_xor row (combineCoeffRowsM m rows ks) c hc
                with ⟨x, hx, y, hy, hxy⟩
            rw [hxy]
            exact xor_mem01 (h01 row (List.mem_cons_self ..) x hx)
              (ih (fun r hr cc hcc => h01 r (List.mem_cons_of_mem _ hr) cc hcc) ks y hy)
          · simp only [hsel] at hc
            exact ih (fun r hr cc hcc => h01 r (List.mem_cons_of_mem _ hr) cc hcc) ks c hc

theorem combineCoeffRowsM_length (m : Nat) : ∀ (rows : List (List Nat)),
    (∀ row ∈ rows, row.length = m) →
    ∀ (cs : List Nat), (combineCoeffRowsM m rows cs).length = m := by
  intro rows
  induction rows with
  | nil =>
      intro _ cs
      rw [combineCoeffRowsM, List.length_replicate]
  | cons row rows ih =>
      intro hlen cs
      cases cs with
      | nil => rw [combineCoeffRowsM, List.length_replicate]
      | cons kk ks =>
          simp only [combineCoeffRowsM]
          by_cases hsel : kk = 1
          · simp only [hsel, reduceIte]
            rw [List.length_zipWith,
              ih (fun r hr => hlen r (List.mem_cons_of_mem _ hr)) ks,
              hlen row (List.mem_cons_self ..)]
            exact Nat.min_self m
          · simp only [hsel, reduceIte]
            rw [ih (fun r hr => hlen r (List.mem_cons_of_mem _ hr)) ks]

/-! ### Bit anatomy of `matrixRowMask`

`matrixRowMask` records a 0/1 coefficient row as a bitmask over column
positions: bit `k` records whether entry `k` differs from zero. -/

theorem testBit_zero_all (q : Nat) : (0 : Nat).testBit q = false := by
  induction q with
  | zero => simp [Nat.testBit_zero]
  | succ q ih =>
      rw [show ((0 : Nat) = 0 * 2 ^ 1) from by rw [Nat.zero_mul],
        Nat.testBit_mul_two_pow]
      have hle : (decide (1 ≤ q + 1) = true) :=
        decide_eq_true_iff.mpr (Nat.succ_le_succ (Nat.zero_le q))
      rw [hle]
      simp [ih]

theorem testBit_bit01 (z q : Nat) :
    Nat.testBit (if z = 0 then 0 else 1) q = (decide (z ≠ 0) && decide (q = 0)) := by
  by_cases hz : z = 0
  · have hif : (if z = 0 then 0 else 1) = 0 := by simp [hz]
    rw [hif, testBit_zero_all]
    simp [hz]
  · have hif : (if z = 0 then 0 else 1) = 1 := by simp [hz]
    have hneq : (decide (z ≠ 0) = true) := decide_eq_true_iff.mpr hz
    rw [hif]
    rcases q with _ | k'
    · rw [Nat.testBit_zero, hneq]
      simp
    · rw [show ((1 : Nat) = 2 ^ 0) from (Nat.pow_zero (2 : Nat)).symm, Nat.testBit_two_pow]
      have hf : (decide (0 = k' + 1) = false) :=
        decide_eq_false_iff_not.mpr (fun h' => Nat.succ_ne_zero k' h'.symm)
      have hs0 : (decide (k' + 1 = 0) = false) :=
        decide_eq_false_iff_not.mpr (Nat.succ_ne_zero k')
      rw [hf, hs0, hneq]
      rfl

theorem two_mul_testBit (x q : Nat) :
    Nat.testBit (2 * x) q = (decide (q ≠ 0) && Nat.testBit x (q - 1)) := by
  cases q with
  | zero =>
      simp [Nat.testBit_zero, Nat.mul_mod_right (2 : Nat) x]
  | succ q' =>
      have h2m : (2 * x) = x * 2 ^ 1 := by rw [Nat.mul_comm, Nat.pow_one]
      have hle : (decide (1 ≤ q' + 1) = true) :=
        decide_eq_true_iff.mpr (Nat.succ_le_succ (Nat.zero_le q'))
      have hs0 : (decide (q' + 1 ≠ 0) = true) :=
        decide_eq_true_iff.mpr (Nat.succ_ne_zero q')
      rw [h2m, Nat.testBit_mul_two_pow, hs0, hle]

/-- Bit `k` of a coefficient row's column-position mask records whether
    entry `k` differs from zero; entries past the row's length are zero. -/
theorem testBit_matrixRowMask (row : List Nat) :
    ∀ k : Nat, (matrixRowMask row).testBit k = decide (row.getD k 0 ≠ 0) := by
  intro k
  induction row generalizing k with
  | nil => rw [matrixRowMask, testBit_zero_all]; simp
  | cons c cs ih =>
      rw [matrixRowMask, Nat.testBit_or, testBit_bit01]
      cases k with
      | zero => simp
      | succ k' =>
          rw [Nat.mul_comm (matrixRowMask cs) 2, two_mul_testBit, ih]
          simp

/-- A 0/1 row's entry equals the corresponding mask bit. -/
theorem getD01_of_testBit_matrixRowMask (row : List Nat)
    (h01 : ∀ c ∈ row, c = 0 ∨ c = 1) :
    ∀ k : Nat, row.getD k 0 = if (matrixRowMask row).testBit k then 1 else 0 := by
  intro k
  by_cases h : row.getD k 0 = 0
  · rw [testBit_matrixRowMask row k, h]
    simp
  · have hone : row.getD k 0 = 1 := by
      have hlt : k < row.length := by
        by_cases hlt : k < row.length
        · exact hlt
        · rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt hlt)] at h
          simp at h
      have hmem : row.getD k 0 ∈ row := by
        rw [← List.getElem_eq_getD (fallback := 0) (i := k) (h := hlt)]
        exact List.mem_iff_getElem.mpr ⟨k, hlt, rfl⟩
      rcases h01 _ hmem with h0 | h1
      · exact absurd h0 h
      · exact h1
    rw [testBit_matrixRowMask row k, hone]
    simp

/-- Componentwise XOR distributes over `getD` when the two lists have equal
    length. -/
theorem getD_zipWith_xor (r : List Nat) :
    ∀ (d : List Nat), r.length = d.length → ∀ k : Nat,
      (List.zipWith (· ^^^ ·) r d).getD k 0 = r.getD k 0 ^^^ d.getD k 0 := by
  induction r with
  | nil =>
      intro d hlen k
      cases d with
      | nil => simp
      | cons b bs => simp at hlen
  | cons a as ih =>
      intro d hlen k
      cases d with
      | nil => simp at hlen
      | cons b bs =>
          rw [List.zipWith_cons_cons]
          cases k with
          | zero => simp
          | succ k' =>
              have hlen' : as.length = bs.length := by simpa using hlen
              simpa [List.getD_cons_succ] using ih bs hlen' k'

/-- Entry↔bit bridge: for a 0/1 matrix, entry `k` of the componentwise
    combination selected by `cs` equals bit `k` of the combination of the
    matrix's column-position row masks. -/
theorem combineCoeffRowsM_testBit_matrixRowMask (m : Nat) :
    (matrix : List (List Nat)) →
    (∀ row ∈ matrix, ∀ c ∈ row, c = 0 ∨ c = 1) →
    (∀ row ∈ matrix, row.length = m) → ∀ cs : List Nat, ∀ k : Nat,
      (combineCoeffRowsM m matrix cs).getD k 0
        = if (combineMasks (matrix.map matrixRowMask) cs).testBit k then 1 else 0 := by
  intro matrix
  induction matrix with
  | nil =>
      intro _ _ cs k
      have hrhs : (combineMasks (List.map matrixRowMask ([] : List (List Nat))) cs).testBit k
          = false := by
        rw [List.map_nil, combineMasks_nil, testBit_zero_all]
      have hlhs : (combineCoeffRowsM m ([] : List (List Nat)) cs).getD k 0 = 0 := by
        rw [combineCoeffRowsM]
        by_cases hkm : k < m
        · rw [List.getD_eq_getElem?_getD, List.getElem?_replicate_of_lt hkm]; simp
        · rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_eq_right hkm]; simp
      rw [hlhs, hrhs]
      simp
  | cons row rows ih =>
      intro h01 hrowlen cs k
      have h01' : ∀ r ∈ rows, ∀ c ∈ r, c = 0 ∨ c = 1 :=
        fun r hr c hc => h01 r (List.mem_cons_of_mem _ hr) c hc
      have hrowlen' : ∀ r ∈ rows, r.length = m :=
        fun r hr => hrowlen r (List.mem_cons_of_mem _ hr)
      have hrow01 : ∀ c ∈ row, c = 0 ∨ c = 1 := h01 row (List.mem_cons_self ..)
      have hrowl : row.length = m := hrowlen row (List.mem_cons_self ..)
      cases cs with
      | nil =>
          rw [combineCoeffRowsM, List.map_cons]
          have hrhs : combineMasks (matrixRowMask row :: List.map matrixRowMask rows)
              ([] : List Nat) = 0 := by
            simp [combineMasks]
          have hlhs : (List.replicate m 0).getD k 0 = 0 := by
            by_cases hkm : k < m
            · rw [List.getD_eq_getElem?_getD, List.getElem?_replicate_of_lt hkm]; simp
            · rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_eq_right hkm]; simp
          rw [hlhs, hrhs, testBit_zero_all]
          simp
      | cons c cs' =>
          rw [combineCoeffRowsM, List.map_cons, combineMasks_cons]
          by_cases hc : c = 1
          · simp only [hc, reduceIte]
            have hdlen : row.length = (combineCoeffRowsM m rows cs').length := by
              rw [hrowl, combineCoeffRowsM_length m rows hrowlen' cs']
            have hget := getD_zipWith_xor row (combineCoeffRowsM m rows cs') hdlen k
            rw [hget, getD01_of_testBit_matrixRowMask row hrow01 k,
              ih h01' hrowlen' cs' k, Nat.testBit_xor]
            cases hb1 : (matrixRowMask row).testBit k <;>
              cases hb2 : (combineMasks (rows.map matrixRowMask) cs').testBit k <;>
              simp
          · simp only [hc, reduceIte, ih h01' hrowlen' cs' k, Nat.zero_xor]

/-- Combining the new masks with coefficients `cs` equals combining the old
    masks with the componentwise combination of the matrix's rows selected by
    `cs`: the composition of the two F₂ linear maps, stated at mask level. -/
theorem combineMasks_combineCoeffRowsM (olds : List Nat) (m : Nat) :
    (matrix : List (List Nat)) →
    (∀ row ∈ matrix, ∀ c ∈ row, c = 0 ∨ c = 1) →
    (∀ row ∈ matrix, row.length = m) → (m = olds.length) → ∀ cs : List Nat,
      combineMasks (matrix.map (combineMasks olds)) cs
        = combineMasks olds (combineCoeffRowsM m matrix cs) := by
  intro matrix
  induction matrix with
  | nil =>
      intro _ _ _ _
      have hzero : (∀ x ∈ List.replicate m 0, x = 0) :=
        fun x hx => (List.mem_replicate.mp hx).2
      simp [combineMasks, combineCoeffRowsM,
        combineMasks_zero_coeffs olds (List.replicate m 0) hzero]
  | cons row rows ih =>
      intro h01 hrowlen hm cs
      cases cs with
      | nil =>
          have hzero : (∀ x ∈ List.replicate m 0, x = 0) :=
            fun x hx => (List.mem_replicate.mp hx).2
          simp [combineMasks, combineCoeffRowsM,
            combineMasks_zero_coeffs olds (List.replicate m 0) hzero]
      | cons kk ks =>
          have h01tail : (∀ r ∈ rows, ∀ c ∈ r, c = 0 ∨ c = 1) :=
            fun r hr c hc => h01 r (List.mem_cons_of_mem row hr) c hc
          have htail01 : (∀ c ∈ combineCoeffRowsM m rows ks, c = 0 ∨ c = 1) :=
            combineCoeffRowsM_01 m rows h01tail ks
          have htaill : ((combineCoeffRowsM m rows ks).length = m) :=
            combineCoeffRowsM_length m rows
              (fun r hr => hrowlen r (List.mem_cons_of_mem row hr)) ks
          have hrowl : row.length = m := hrowlen row (List.mem_cons_self ..)
          have hrow01 : (∀ c ∈ row, c = 0 ∨ c = 1) := h01 row (List.mem_cons_self ..)
          simp only [List.map_cons, combineCoeffRowsM, combineMasks_cons]
          by_cases hsel : kk = 1
          · simp only [hsel, reduceIte]
            rw [ih h01tail (fun r hr => hrowlen r (List.mem_cons_of_mem row hr)) hm ks,
              combineMasks_zipWith_xor olds row (combineCoeffRowsM m rows ks) (hrowl.trans hm)
                (htaill.trans hm) hrow01 htail01]
          · simp only [hsel, reduceIte]
            rw [Nat.zero_xor, ih h01tail (fun r hr => hrowlen r (List.mem_cons_of_mem row hr)) hm ks]

/-! ### Unit coefficient rows

`unitRow n i` is the length-`n` 0/1 list whose entry `i` is `1`. -/

def unitRow : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, 0 => 1 :: List.replicate n 0
  | n + 1, i + 1 => 0 :: unitRow n i

theorem unitRow_length : ∀ (n i : Nat), (unitRow n i).length = n := by
  intro n
  induction n with
  | zero => intro i; rfl
  | succ n ih =>
      intro i
      cases i with
      | zero => simp [unitRow]
      | succ i' => simp [unitRow, ih i']

theorem unitRow_getElem : ∀ (n i j : Nat), i < n → j < n →
    (unitRow n i).getD j 0 = if j = i then 1 else 0 := by
  intro n
  induction n with
  | zero => intro i j hi _; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
      intro i j hi hj
      cases i with
      | zero =>
          cases j with
          | zero => simp [unitRow]
          | succ j' =>
              have h0 : (List.replicate n 0).getD j' 0 = 0 := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
                split <;> simp
              simp [unitRow]
              rw [List.getD_eq_getElem?_getD] at h0
              simp [h0]
      | succ i' =>
          cases j with
          | zero => simp [unitRow]
          | succ j' =>
              rw [unitRow, List.getD_cons_succ, ih i' j' (by omega) (by omega)]
              simp

/-- Combining a mask list by `unitRow` selects the masked row at position
    `i`. -/
theorem combineMasks_unitRow (ms : List Nat) :
    ∀ (i : Nat), i < ms.length →
      combineMasks ms (unitRow ms.length i) = ms.getD i 0 := by
  induction ms with
  | nil => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | cons m₀ ms ih =>
      intro i hi
      cases i with
      | zero =>
          rw [List.length_cons, unitRow, combineMasks_cons, combineMasks_zero_coeffs ms
            (List.replicate (List.length ms) 0)
            (fun c hc => (List.mem_replicate.mp hc).2)]
          simp
      | succ i' =>
          rw [List.length_cons, unitRow, combineMasks_cons]
          simp
          exact ih i' (by simpa using hi)

/-! ### Span enumeration

`spanList xs` enumerates all `2 ^ k` F₂ combinations of `xs`;
`independentMasks xs` says no nontrivial 0/1 combination of the masks is
zero, which makes the enumeration duplicate-free. -/

/-- Display independence at the mask level: no nontrivial 0/1 combination of
    the masks is zero. -/
def independentMasks (xs : List Nat) : Prop :=
  ∀ cs, cs.length = xs.length → (∀ c ∈ cs, c = 0 ∨ c = 1) →
    combineMasks xs cs = 0 → (∀ c ∈ cs, c = 0)

theorem spanList_length (xs : List Nat) : (spanList xs).length = 2 ^ xs.length := by
  induction xs with
  | nil => simp [spanList]
  | cons x xs ih =>
      have hexp : ((x :: xs).length) = xs.length.succ := rfl
      calc
        (spanList (x :: xs)).length
            = (spanList xs).length + (spanList xs).length := by
              rw [spanList, List.length_append, List.length_map]
        _ = 2 ^ xs.length + 2 ^ xs.length := by rw [ih]
        _ = 2 * 2 ^ xs.length := (Nat.two_mul _).symm
        _ = 2 ^ xs.length.succ := by rw [Nat.mul_comm, Nat.pow_succ]
        _ = 2 ^ (x :: xs).length := by rw [hexp]

theorem independentMasks_tail {x : Nat} {xs : List Nat} (h : independentMasks (x :: xs)) :
    independentMasks xs := by
  intro cs hlen h01 hval
  have hc0 : (0 :: cs).length = (x :: xs).length := by simp [hlen]
  have h01' : (∀ c ∈ (0 :: cs), c = 0 ∨ c = 1) := by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Or.inl rfl
    · exact h01 c hc
  have hcomb : combineMasks (x :: xs) (0 :: cs) = 0 := by
    rw [combineMasks_cons]
    simp [hval]
  have hres := h (0 :: cs) hc0 h01' hcomb
  intro c hc
  exact hres c (List.mem_cons_of_mem _ hc)

theorem spanList_combine (xs : List Nat) : ∀ v, v ∈ spanList xs →
    ∃ cs, cs.length = xs.length ∧ (∀ c ∈ cs, c = 0 ∨ c = 1) ∧ combineMasks xs cs = v := by
  induction xs with
  | nil =>
      intro v hv
      rw [spanList] at hv
      rcases List.mem_singleton.mp hv with rfl
      refine ⟨[], rfl, fun c hc => ?_, rfl⟩
      exact absurd hc (List.not_mem_nil)
  | cons x xs ih =>
      intro v hv
      rw [spanList] at hv
      rcases List.mem_append.mp hv with hmem | hmem
      · rcases ih v hmem with ⟨cs, hlen, h01, hval⟩
        have h01x : (∀ c ∈ (0 :: cs), c = 0 ∨ c = 1) := by
          intro c hc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact Or.inl rfl
          · exact h01 c hc
        refine ⟨0 :: cs, by simp [hlen], h01x, ?_⟩
        rw [combineMasks_cons]
        simp [Nat.zero_xor, hval]
      · rcases List.mem_map.mp hmem with ⟨w, hwmem, hwe⟩
        rcases ih _ hwmem with ⟨cs, hlen, h01, hval⟩
        have h01x : (∀ c ∈ (1 :: cs), c = 0 ∨ c = 1) := by
          intro c hc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact Or.inr rfl
          · exact h01 c hc
        refine ⟨1 :: cs, by simp [hlen], h01x, ?_⟩
        rw [combineMasks_cons, hval]
        simp only [reduceIte]
        rw [Nat.xor_comm x w, hwe]

theorem nodup_map_xor (l : List Nat) (x : Nat) (h : l.Nodup) :
    (l.map (fun v => v ^^^ x)).Nodup := by
  induction l with
  | nil => simp
  | cons a as ih =>
      rcases List.nodup_cons.mp h with ⟨ha, has⟩
      have has' := ih has
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, has'⟩
      intro hmem
      rcases List.mem_map.mp hmem with ⟨b, hbmem, hbeq⟩
      have hba : b = a := xor_right_cancel hbeq
      rw [hba] at hbmem
      exact ha hbmem

theorem spanList_nodup (xs : List Nat) (h : independentMasks xs) :
    (spanList xs).Nodup := by
  induction xs with
  | nil => simp [spanList]
  | cons x xs ih =>
      have htail : independentMasks xs := independentMasks_tail h
      have htn : (spanList xs).Nodup := ih htail
      rw [spanList, List.nodup_append]
      refine ⟨htn, nodup_map_xor (spanList xs) x htn, ?_⟩
      intro t hmemt v hmemv hv
      rcases List.mem_map.mp hmemv with ⟨w, hwmem, hwe⟩
      rcases spanList_combine xs t hmemt with ⟨ct, hctlen, hct01, hctval⟩
      rcases spanList_combine xs w hwmem with ⟨cw, hcwlen, hcw01, hcwval⟩
      have h01xor : (∀ c ∈ List.zipWith (· ^^^ ·) ct cw, c = 0 ∨ c = 1) := by
        intro c hc
        rcases mem_zipWith_xor ct cw c hc with ⟨u, hu, v', hv', huv⟩
        rw [huv]
        exact xor_mem01 (hct01 u hu) (hcw01 v' hv')
      have htw : t ^^^ w = x := by
        calc
          t ^^^ w = (w ^^^ x) ^^^ w := by rw [hv, hwe]
          _ = w ^^^ (x ^^^ w) := Nat.xor_assoc w x w
          _ = w ^^^ (w ^^^ x) := by rw [Nat.xor_comm x w]
          _ = (w ^^^ w) ^^^ x := (Nat.xor_assoc w w x).symm
          _ = 0 ^^^ x := by rw [Nat.xor_self w]
          _ = x := Nat.zero_xor x
      have h01xorx : (∀ c ∈ (1 :: List.zipWith (· ^^^ ·) ct cw), c = 0 ∨ c = 1) := by
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact Or.inr rfl
        · exact h01xor c hc
      have hzero : combineMasks (x :: xs) (1 :: List.zipWith (· ^^^ ·) ct cw) = 0 := by
        rw [combineMasks_cons, combineMasks_zipWith_xor xs ct cw hctlen hcwlen hct01 hcw01,
          hctval, hcwval, htw]
        simp
      have hres := h (1 :: List.zipWith (· ^^^ ·) ct cw)
        (by simp [List.length_zipWith, hctlen, hcwlen])
        h01xorx hzero
      exact absurd (hres 1 (List.mem_cons_self ..)) (by decide)

end CodeCalculus
