import CodeCalculus.Eval
import CodeCalculus.RebaseRank

namespace CodeCalculus

/-! ### The support-to-bitmask bridge

`mixSupport` combines displayed rows' supports by symmetric difference and
sorts; `rowBitmask` reads a support as a bitmask over the qubit list through
`indexOfQubit`. The bridge below is unconditional: `indexOfQubit` returns the
*first* occurrence, so a qubit contributes to exactly one bit position no
matter which list it is read from. In particular no well-formedness
hypothesis — not `Q.Nodup`, not support containment, not a length or 0/1
condition on the coefficients — is needed. -/

/-- `indexOfQubit` returns the position of the first occurrence. -/
theorem indexOfQubit_some_imp : ∀ (Q : List Nat) (q i : Nat),
    indexOfQubit Q q = some i → Q[i]? = some q
  | [], q, i, h => by simp [indexOfQubit] at h
  | a :: as, q, i, h => by
      unfold indexOfQubit at h
      by_cases haq : a = q
      · subst a
        have h0 : i = 0 := by simpa using h.symm
        subst i
        simp
      · simp [haq] at h
        cases has : indexOfQubit as q with
        | none => simp [has] at h
        | some j =>
            simp [has] at h
            subst i
            simp
            exact indexOfQubit_some_imp as q j has

/-- Two qubits with the same first-occurrence index are equal. -/
theorem indexOfQubit_inj (Q : List Nat) {q q' i : Nat}
    (h : indexOfQubit Q q = some i) (h' : indexOfQubit Q q' = some i) : q = q' := by
  have hq : Q[i]? = some q := indexOfQubit_some_imp Q q i h
  have hq' : Q[i]? = some q' := indexOfQubit_some_imp Q q' i h'
  rw [hq] at hq'
  exact Option.some.inj hq'

/-- The bit contributed by a qubit. -/
def supportBit (i : Nat) : Nat := 1 <<< i

theorem testBit_supportBit (i j : Nat) :
    (supportBit j).testBit i = decide (i = j) := by
  unfold supportBit
  rw [Nat.testBit_shiftLeft]
  rw [show (1 : Nat) = 2 ^ 0 by simp, Nat.testBit_two_pow]
  by_cases h : i = j
  · subst i
    simp
  · by_cases hle : j ≤ i
    · have hz : ¬ (0 = i - j) := by omega
      simp [h, hle, hz]
    · simp [h, hle]

/-- One step of the OR-fold that builds a row's bitmask. -/
def addSupportBit (Q : List Nat) (acc q : Nat) : Nat :=
  match indexOfQubit Q q with
  | some i => acc ||| supportBit i
  | none => acc

def maskOfSupport (Q sup : List Nat) : Nat :=
  sup.foldl (addSupportBit Q) 0

theorem rowBitmask_eq_maskOfSupport (Q : List Nat) (r : Row) :
    rowBitmask Q r = maskOfSupport Q r.support := rfl

/-- One OR-fold step toggles exactly the first-occurrence bit of `q`. -/
theorem testBit_addSupportBit (Q : List Nat) (acc q i : Nat) :
    (addSupportBit Q acc q).testBit i
      = (acc.testBit i || decide (indexOfQubit Q q = some i)) := by
  unfold addSupportBit
  cases hidx : indexOfQubit Q q with
  | none => simp only; simp
  | some j =>
      simp only
      rw [Nat.testBit_or, testBit_supportBit]
      by_cases hij : i = j
      · simp [hij]
      · simp [hij]
        intro he
        exact absurd he.symm hij

/-- The OR-fold's bit characterization, with an arbitrary accumulator. -/
theorem testBit_fold_addSupportBit (Q : List Nat) :
    ∀ (sup : List Nat) (acc i : Nat),
      (sup.foldl (addSupportBit Q) acc).testBit i
        = (sup.any (fun q => decide (indexOfQubit Q q = some i)) || acc.testBit i) := by
  intro sup
  induction sup with
  | nil => intro acc i; simp
  | cons q qs ih =>
      intro acc i
      rw [List.foldl_cons, ih (addSupportBit Q acc q) i, testBit_addSupportBit,
        List.any_cons, Bool.or_assoc]
      by_cases hidx : indexOfQubit Q q = some i <;> simp [hidx, Bool.or_comm]

/-- Bit `i` of a support's mask records whether some member of the support
    has its first occurrence at position `i`. -/
theorem testBit_maskOfSupport_iff (Q sup : List Nat) (i : Nat) :
    (maskOfSupport Q sup).testBit i = true ↔ ∃ q ∈ sup, indexOfQubit Q q = some i := by
  have h := testBit_fold_addSupportBit Q sup 0 i
  rw [maskOfSupport, h, testBit_zero_all, Bool.or_false]
  constructor
  · intro hbit
    rw [List.any_eq_true] at hbit
    obtain ⟨q, hq, hdec⟩ := hbit
    exact ⟨q, hq, by simpa using hdec⟩
  · rintro ⟨q, hq, hidx⟩
    rw [List.any_eq_true]
    exact ⟨q, hq, by simpa using hidx⟩

/-- Membership in the symmetric difference. -/
theorem mem_xorList {a b : List Nat} {q : Nat} :
    q ∈ xorList a b ↔ (q ∈ a ∧ q ∉ b) ∨ (q ∈ b ∧ q ∉ a) := by
  unfold xorList
  simp [List.mem_append, List.mem_filter]

/-- The mask of a symmetric difference is the XOR of the masks: each qubit's
    contribution lands at its unique first-occurrence bit. -/
theorem maskOfSupport_xorList (Q a b : List Nat) :
    maskOfSupport Q (xorList a b) = maskOfSupport Q a ^^^ maskOfSupport Q b := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hL : (maskOfSupport Q (xorList a b)).testBit i = true ↔
      ∃ q ∈ xorList a b, indexOfQubit Q q = some i := testBit_maskOfSupport_iff Q _ i
  have hA : (maskOfSupport Q a).testBit i = true ↔ ∃ q ∈ a, indexOfQubit Q q = some i :=
    testBit_maskOfSupport_iff Q a i
  have hB : (maskOfSupport Q b).testBit i = true ↔ ∃ q ∈ b, indexOfQubit Q q = some i :=
    testBit_maskOfSupport_iff Q b i
  by_cases hA' : (maskOfSupport Q a).testBit i = true
  · by_cases hB' : (maskOfSupport Q b).testBit i = true
    · rw [Nat.testBit_xor, hA', hB']
      have hno : ¬ ∃ q ∈ xorList a b, indexOfQubit Q q = some i := by
        rintro ⟨q, hq, hidx⟩
        rcases mem_xorList.mp hq with ⟨hqa, hqb⟩ | ⟨hqb, hqa⟩
        · obtain ⟨q', hq'mem, hq'idx⟩ := hB.mp hB'
          have : q' = q := indexOfQubit_inj Q hq'idx hidx
          exact hqb (this ▸ hq'mem)
        · obtain ⟨q', hq'mem, hq'idx⟩ := hA.mp hA'
          have : q' = q := indexOfQubit_inj Q hq'idx hidx
          exact hqa (this ▸ hq'mem)
      have hfalse : (maskOfSupport Q (xorList a b)).testBit i = false := by
        by_cases hL' : (maskOfSupport Q (xorList a b)).testBit i = true
        · exact absurd (hL.mp hL') hno
        · exact Bool.eq_false_iff.mpr hL'
      rw [hfalse]
      simp
    · rw [Nat.testBit_xor, hA']
      have hBf : (maskOfSupport Q b).testBit i = false := Bool.eq_false_iff.mpr hB'
      rw [hBf]
      obtain ⟨qₐ, hqₐmem, hqₐidx⟩ := hA.mp hA'
      have hqₐnb : qₐ ∉ b := by
        intro hmem
        exact hB' (hB.mpr ⟨qₐ, hmem, hqₐidx⟩)
      have htrue : (maskOfSupport Q (xorList a b)).testBit i = true :=
        hL.mpr ⟨qₐ, by
          rw [mem_xorList]
          exact Or.inl ⟨hqₐmem, hqₐnb⟩, hqₐidx⟩
      rw [htrue]
      simp
  · by_cases hB' : (maskOfSupport Q b).testBit i = true
    · rw [Nat.testBit_xor, hB']
      have hAf : (maskOfSupport Q a).testBit i = false := Bool.eq_false_iff.mpr hA'
      rw [hAf]
      obtain ⟨q_b, hq_bmem, hq_bidx⟩ := hB.mp hB'
      have hq_bna : q_b ∉ a := by
        intro hmem
        exact hA' (hA.mpr ⟨q_b, hmem, hq_bidx⟩)
      have htrue : (maskOfSupport Q (xorList a b)).testBit i = true :=
        hL.mpr ⟨q_b, by
          rw [mem_xorList]
          exact Or.inr ⟨hq_bmem, hq_bna⟩, hq_bidx⟩
      rw [htrue]
      simp
    · rw [Nat.testBit_xor]
      have hAf : (maskOfSupport Q a).testBit i = false := Bool.eq_false_iff.mpr hA'
      have hBf : (maskOfSupport Q b).testBit i = false := Bool.eq_false_iff.mpr hB'
      rw [hAf, hBf]
      have hno : ¬ ∃ q ∈ xorList a b, indexOfQubit Q q = some i := by
        rintro ⟨q, hq, hidx⟩
        rcases mem_xorList.mp hq with ⟨hqa, _⟩ | ⟨hqb, _⟩
        · exact hA' (hA.mpr ⟨q, hqa, hidx⟩)
        · exact hB' (hB.mpr ⟨q, hqb, hidx⟩)
      have hfalse : (maskOfSupport Q (xorList a b)).testBit i = false := by
        by_cases hL' : (maskOfSupport Q (xorList a b)).testBit i = true
        · exact absurd (hL.mp hL') hno
        · exact Bool.eq_false_iff.mpr hL'
      rw [hfalse]
      simp

theorem maskOfSupport_perm (Q : List Nat) {a b : List Nat} (h : List.Perm a b) :
    maskOfSupport Q a = maskOfSupport Q b := by
  unfold maskOfSupport
  apply List.Perm.foldl_eq' h
  intro x _ y _ z
  unfold addSupportBit
  cases hx : indexOfQubit Q x <;> cases hy : indexOfQubit Q y <;>
    simp only <;>
    rw [Nat.or_assoc, Nat.or_assoc, Nat.or_comm (supportBit _)]

theorem insertSorted_perm (x : Nat) (xs : List Nat) :
    List.Perm (insertSorted x xs) (x :: xs) := by
  induction xs with
  | nil => simp [insertSorted]
  | cons y ys ih =>
      unfold insertSorted
      split
      · simp
      · exact (List.Perm.cons y ih).trans (List.Perm.swap x y ys)

theorem sortNat_perm (qs : List Nat) : List.Perm (sortNat qs) qs := by
  induction qs with
  | nil => simp [sortNat]
  | cons x xs ih =>
      simp only [sortNat]
      exact (insertSorted_perm x (sortNat xs)).trans (List.Perm.cons x ih)

/-- The `mixSupport` bridge: the mask of the mixed support is the F₂
    combination of the rows' masks by the coefficient list. Unconditional:
    `zip` truncates and `combineMasks` ignores surplus coefficients on both
    sides alike. -/
theorem maskOfSupport_mixSupport (Q : List Nat) (ordered : List Row) (cs : List Nat) :
    maskOfSupport Q (mixSupport ordered cs)
      = combineMasks (ordered.map (fun r => maskOfSupport Q r.support)) cs := by
  unfold mixSupport
  rw [maskOfSupport_perm Q (sortNat_perm _)]
  suffices h : ∀ (ordered : List Row) (cs : List Nat) (acc : List Nat),
      maskOfSupport Q ((ordered.zip cs).foldl
        (fun acc rc => match rc with
          | (r, c) => if c = 1 then xorList acc r.support else acc) acc)
        = maskOfSupport Q acc
          ^^^ combineMasks (ordered.map (fun r => maskOfSupport Q r.support)) cs by
    simpa [maskOfSupport] using h ordered cs []
  intro ordered
  induction ordered with
  | nil =>
      intro cs acc
      simp [combineMasks_nil]
  | cons r rs ih =>
      intro cs acc
      cases cs with
      | nil => simp [combineMasks]
      | cons c cs' =>
          rw [List.zip_cons_cons, List.foldl_cons, List.map_cons, combineMasks_cons]
          by_cases hc : c = 1
          · have hsel : (if c = 1 then xorList acc r.support else acc)
                = xorList acc r.support := by simp [hc]
            have hif : (if c = 1 then maskOfSupport Q r.support else 0)
                = maskOfSupport Q r.support := by simp [hc]
            rw [show (match (r, c) with
                  | (r, c) => if c = 1 then xorList acc r.support else acc)
                    = (if c = 1 then xorList acc r.support else acc) from rfl]
            rw [hsel, hif, ih cs' (xorList acc r.support), maskOfSupport_xorList,
              ← Nat.xor_assoc]
          · have hsel : (if c = 1 then xorList acc r.support else acc) = acc := by
              simp [hc]
            have hif : (if c = 1 then maskOfSupport Q r.support else 0) = 0 := by
              simp [hc]
            rw [show (match (r, c) with
                  | (r, c) => if c = 1 then xorList acc r.support else acc)
                    = (if c = 1 then xorList acc r.support else acc) from rfl]
            rw [hsel, hif, Nat.zero_xor, ih cs' acc]

/-- The support-to-bitmask bridge for `mixSupport`, at the `rowBitmask`
    level, with no well-formedness hypothesis. -/
theorem rowBitmask_mixSupport (Q : List Nat) (ordered : List Row) (cs : List Nat)
    (id : Nat) (sec : Sector) :
    rowBitmask Q ⟨id, sec, mixSupport ordered cs⟩
      = combineMasks (ordered.map (rowBitmask Q)) cs := by
  rw [rowBitmask_eq_maskOfSupport]
  have h := maskOfSupport_mixSupport Q ordered cs
  have hmap : List.map (fun r => maskOfSupport Q r.support) ordered
      = List.map (rowBitmask Q) ordered := by
    apply List.map_congr_left
    intro r _
    exact (rowBitmask_eq_maskOfSupport Q r).symm
  rw [h, hmap]

end CodeCalculus
