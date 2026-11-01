import CodeCalculus.WellFormedness

namespace CodeCalculus

/-!
# The dimension bound `rank X + rank Z ≤ |Q|` ()

`RanksFit` (`WellFormedness.lean`) is the premise the `k` rows of
`Soundness.lean` take so that the truncated subtraction in `stateK` is exact.
`ranksFit_of_wf` derives it from well-formedness, so that the premise can be
dropped.

The argument is at the mask level. I1 says every X row has even intersection
with every Z row; over bit positions below `n = |Q|` this is a parity form
(`dotCount`, `Orth`) that is bilinear under XOR, so it vanishes on the two
spans (`orth_of_inSpan`). Let `BX` and `BZ` be the greedy bases that
`rankBitmasks` computes. The greedy basis is pivot-distinct and *reduced*: a
mask inserted later has the pivot bits of every earlier mask clear
(`Reduced`, `foldl_insertBasis_reduced`). A mask whose set bits all lie at
pivots of `BZ` and which is orthogonal to every member of `BZ` is zero,
by forward substitution down the reduced basis (`eq_zero_of_orth_reduced`).
Hence the family `BX ++ E`, where `E` lists the unit masks at the pivots of
`BZ`, is independent: a unit `2 ^ p` in the span of `BX` and the earlier units
would put a nonzero vector of span `X`, supported on pivots of `BZ`, orthogonal
to `BZ`. Its greedy rank is therefore `|BX| + |BZ|`, and the greedy rank of
any list of masks below `2 ^ n` is at most `n`
(`rankBitmasks_le_of_high_bits_false`), which is the bound.

Statements about these list functions only; no soundness claim for the
calculus is made here (README *Status*).
-/

/-! ### The greedy rank is bounded by the list length -/

theorem insertBasis_length_le (basis : List Nat) (x : Nat) :
    (insertBasis basis x).length ≤ basis.length + 1 := by
  by_cases h : reduceByBasis basis x = 0 <;> simp [insertBasis, h]

theorem foldl_insertBasis_length_le (xs : List Nat) :
    ∀ acc : List Nat, (xs.foldl insertBasis acc).length ≤ acc.length + xs.length := by
  induction xs with
  | nil => intro acc; simp
  | cons x xs ih =>
    intro acc
    rw [List.foldl_cons]
    have h1 := ih (insertBasis acc x)
    have h2 := insertBasis_length_le acc x
    simp only [List.length_cons]
    omega

theorem rankBitmasks_le_length (xs : List Nat) : rankBitmasks xs ≤ xs.length := by
  unfold rankBitmasks
  have := foldl_insertBasis_length_le xs []
  simpa using this

theorem sectorRank_le_length (Q : List Nat) (rows : List Row) (σ : Sector) :
    sectorRank Q rows σ ≤ (rows.filter (fun r => r.sector = σ)).length := by
  unfold sectorRank
  calc rankBitmasks ((rows.filter (fun r => r.sector = σ)).map (rowBitmask Q))
      ≤ ((rows.filter (fun r => r.sector = σ)).map (rowBitmask Q)).length :=
        rankBitmasks_le_length _
    _ = (rows.filter (fun r => r.sector = σ)).length := List.length_map _

/-! ### Counting helpers -/

/-- Over any list, the symmetric difference of two membership tests is counted
    with the parity of the sum of the two counts. -/
theorem length_filter_bne_parity (L R b : Nat → Bool) :
    ∀ Q : List Nat,
      (Q.filter (fun x => decide (L x ≠ R x) && b x)).length % 2 =
        ((Q.filter (fun x => L x && b x)).length +
          (Q.filter (fun x => R x && b x)).length) % 2 := by
  intro Q
  induction Q with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons]
    cases hL : L x <;> cases hR : R x <;> cases hb : b x <;> simp at ih ⊢ <;> omega

/-- The intersection size of a duplicate-free support inside `Q` with `b`,
    counted over `Q`. -/
theorem supportIntersectionSize_eq_count (Q L b : List Nat) (hQ : Q.Nodup) (hL : L.Nodup)
    (hsub : ∀ x ∈ L, x ∈ Q) :
    supportIntersectionSize L b = (Q.filter (fun x => L.contains x && b.contains x)).length := by
  rw [supportIntersectionSize_eq_length_filter]
  apply List.Perm.length_eq
  rw [List.perm_ext_iff_of_nodup (hL.sublist List.filter_sublist) (hQ.sublist List.filter_sublist)]
  intro x
  simp only [List.mem_filter, Bool.and_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨hx, hb⟩
    exact ⟨hsub x hx, hx, hb⟩
  · rintro ⟨_, hx, hb⟩
    exact ⟨hx, hb⟩

/-- Reindexing a filter over a list by positions. -/
theorem length_filter_range_eq_filter {α : Type} (Q : List α) (p : α → Bool) :
    ∀ f : Nat → Bool, (∀ i (h : i < Q.length), f i = p Q[i]) →
      ((List.range Q.length).filter f).length = (Q.filter p).length := by
  induction Q with
  | nil => intro f _; simp
  | cons x xs ih =>
    intro f hf
    have h0 : f 0 = p x := hf 0 (by simp)
    have ih' := ih (f ∘ Nat.succ) (fun i h => by
      have := hf (i + 1) (by simp; omega)
      simpa using this)
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map, h0,
      List.filter_cons]
    by_cases hp : p x = true
    · simp [hp, ih']
    · simp [hp, ih']

/-- The positions below `n` equal to `p`, filtered: exactly one when `p < n`. -/
theorem length_filter_range_eq (p : Nat) : ∀ n, p < n →
    ((List.range n).filter (fun i => decide (i = p))).length = 1 := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (Nat.not_lt_zero p)
  | succ n ih =>
    intro h
    rw [List.range_succ, List.filter_append, List.length_append]
    by_cases hp : p < n
    · rw [ih hp]
      have hnil : [n].filter (fun i => decide (i = p)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        rw [List.mem_singleton] at ha
        subst ha
        simp only [decide_eq_true_eq]
        omega
      rw [hnil]
      rfl
    · have hpn : p = n := by omega
      subst hpn
      have h1 : (List.range p).filter (fun i => decide (i = p)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        rw [List.mem_range] at ha
        simp only [decide_eq_true_eq]
        omega
      rw [h1]
      simp

theorem length_filter_range_single (n p : Nat) (hp : p < n) (c : Bool) :
    ((List.range n).filter (fun i => decide (i = p) && c)).length = if c then 1 else 0 := by
  cases c
  · simp
  · simp only [Bool.and_true]
    rw [length_filter_range_eq p n hp]
    rfl

/-! ### The parity form over bit positions -/

/-- The number of positions below `n` at which both masks have a set bit. -/
def dotCount (n a b : Nat) : Nat :=
  ((List.range n).filter (fun i => a.testBit i && b.testBit i)).length

/-- Even intersection over the positions below `n`. -/
def Orth (n a b : Nat) : Prop := dotCount n a b % 2 = 0

theorem dotCount_comm (n a b : Nat) : dotCount n a b = dotCount n b a := by
  unfold dotCount
  congr 1
  apply List.filter_congr
  intro i _
  exact Bool.and_comm _ _

theorem dotCount_zero_left (n b : Nat) : dotCount n 0 b = 0 := by
  simp [dotCount, Nat.zero_testBit]

theorem dotCount_xor_left (n a b c : Nat) :
    dotCount n (a ^^^ b) c % 2 = (dotCount n a c + dotCount n b c) % 2 := by
  unfold dotCount
  have h := length_filter_bne_parity (fun i => a.testBit i) (fun i => b.testBit i)
    (fun i => c.testBit i) (List.range n)
  have hcongr : (List.range n).filter (fun i => (a ^^^ b).testBit i && c.testBit i) =
      (List.range n).filter (fun i => decide (a.testBit i ≠ b.testBit i) && c.testBit i) := by
    apply List.filter_congr
    intro i _
    rw [Nat.testBit_xor]
    cases a.testBit i <;> cases b.testBit i <;> rfl
  rw [hcongr]
  exact h

theorem orth_combine_left (n : Nat) (ms : List Nat) :
    ∀ (cs : List Nat) (c : Nat), (∀ m ∈ ms, Orth n m c) → Orth n (combineMasks ms cs) c := by
  induction ms with
  | nil => intro cs c _; simp [combineMasks_nil, Orth, dotCount_zero_left]
  | cons m ms ih =>
    intro cs c h
    cases cs with
    | nil => simp [combineMasks, Orth, dotCount_zero_left]
    | cons k ks =>
      simp only [combineMasks]
      unfold Orth
      rw [dotCount_xor_left]
      have h1 : dotCount n (if k = 1 then m else 0) c % 2 = 0 := by
        split
        · exact h m (List.mem_cons_self ..)
        · simp [dotCount_zero_left]
      have h2 := ih ks c (fun m' hm' => h m' (List.mem_cons_of_mem _ hm'))
      unfold Orth at h2
      omega

theorem orth_of_inSpan_left (n : Nat) {ms : List Nat} {v c : Nat} (hv : inSpanMasks ms v)
    (h : ∀ m ∈ ms, Orth n m c) : Orth n v c := by
  obtain ⟨cs, _, _, rfl⟩ := hv
  exact orth_combine_left n ms cs c h

/-- Orthogonality of the generators extends to the two spans. -/
theorem orth_of_inSpan (n : Nat) {xs zs : List Nat} {u v : Nat} (hu : inSpanMasks xs u)
    (hv : inSpanMasks zs v) (h : ∀ x ∈ xs, ∀ z ∈ zs, Orth n x z) : Orth n u v := by
  apply orth_of_inSpan_left n hu
  intro x hx
  unfold Orth
  rw [dotCount_comm]
  exact orth_of_inSpan_left n hv (fun z hz => by
    unfold Orth
    rw [dotCount_comm]
    exact h x hx z hz)

/-! ### From I1 to the parity form -/

theorem dotCount_rowBitmask (Q : List Nat) (hQ : Q.Nodup) (rX rZ : Row)
    (hXnd : rX.support.Nodup) (hXQ : ∀ x ∈ rX.support, x ∈ Q) :
    dotCount Q.length (rowBitmask Q rX) (rowBitmask Q rZ) =
      supportIntersectionSize rX.support rZ.support := by
  unfold dotCount
  rw [supportIntersectionSize_eq_count Q rX.support rZ.support hQ hXnd hXQ]
  apply length_filter_range_eq_filter
  intro i h
  simp only [testBit_rowBitmask Q hQ]
  unfold qubitBit
  rw [List.getElem?_eq_getElem h]

theorem rowBitmask_testBit_high (Q : List Nat) (hQ : Q.Nodup) (r : Row) (j : Nat)
    (hj : Q.length ≤ j) : (rowBitmask Q r).testBit j = false := by
  rw [testBit_rowBitmask Q hQ]
  unfold qubitBit
  rw [List.getElem?_eq_none hj]

/-! ### Rank is bounded by the ambient dimension -/

theorem rankBitmasks_le_of_high_bits_false (ms : List Nat) (n : Nat)
    (h : ∀ m ∈ ms, ∀ j, n ≤ j → m.testBit j = false) : rankBitmasks ms ≤ n := by
  have hpd := foldl_insertBasis_pivotDistinct ms [] pivotDistinct_nil
  have hpres := foldl_insertBasis_preserved ms n h [] (by simp) (by simp)
  unfold rankBitmasks
  have hsub : ∀ v ∈ (ms.foldl insertBasis []).map Nat.log2, v ∈ List.range n := by
    intro v hv
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv
    rw [List.mem_range]
    exact log2_lt_of_lt_two_pow (hpres.1 b hb)
      (lt_two_pow_of_high_bits_false b n (hpres.2 b hb))
  have := length_le_of_nodup_subset (nodup_range n) hpd.2 hsub
  rw [List.length_map, List.length_range] at this
  exact this

/-! ### The greedy basis is reduced -/

/-- Every mask has the pivot bits of all later (earlier-inserted) masks clear. -/
def Reduced : List Nat → Prop
  | [] => True
  | b :: bs => (∀ b' ∈ bs, b.testBit (Nat.log2 b') = false) ∧ Reduced bs

theorem reduceByBasis_pivots_clear (acc : List Nat) (x : Nat) (hpd : PivotDistinct acc) :
    ∀ b ∈ acc, (reduceByBasis acc x).testBit (Nat.log2 b) = false := by
  intro b hb
  rw [reduceByBasis_eq_fold]
  apply reduceFold_pivots_clear (sortByPivotDesc acc) x (Nat.log2 b)
  · exact sortByPivotDesc_pivotSorted acc hpd.1 hpd.2
  · intro b' hb'
    exact hpd.1 b' (sortByPivotDesc_mem acc hb')
  · exact List.mem_map.mpr ⟨b, (sortByPivotDesc_perm acc).mem_iff.mpr hb, rfl⟩

theorem insertBasis_reduced (acc : List Nat) (x : Nat) (hpd : PivotDistinct acc)
    (hr : Reduced acc) : Reduced (insertBasis acc x) := by
  simp only [insertBasis]
  split
  · exact hr
  · exact ⟨reduceByBasis_pivots_clear acc x hpd, hr⟩

theorem foldl_insertBasis_reduced (xs : List Nat) :
    ∀ acc, PivotDistinct acc → Reduced acc → Reduced (xs.foldl insertBasis acc) := by
  induction xs with
  | nil => intro acc _ hr; exact hr
  | cons x xs ih =>
    intro acc hpd hr
    rw [List.foldl_cons]
    exact ih _ (insertBasis_pivotDistinct acc x hpd) (insertBasis_reduced acc x hpd hr)

/-- A nonzero mask has its pivot bit set. -/
theorem testBit_log2_self {b : Nat} (hb : b ≠ 0) : b.testBit (Nat.log2 b) = true := by
  cases hc : b.testBit (Nat.log2 b)
  · exfalso
    have hlt : b < 2 ^ Nat.log2 b := by
      apply Nat.lt_pow_two_of_testBit
      intro i hi
      rcases Nat.eq_or_lt_of_le hi with h | h
      · rw [← h]
        exact hc
      · exact Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) h))
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt (Nat.log2_self_le hb))
  · rfl

/-- Forward substitution down a reduced basis: a mask supported on the pivots
    and orthogonal to every basis mask is zero. -/
theorem eq_zero_of_orth_reduced (n : Nat) : ∀ (bs : List Nat), Reduced bs →
    (∀ b ∈ bs, b ≠ 0) → (∀ b ∈ bs, b < 2 ^ n) →
    ∀ w : Nat, (∀ i, w.testBit i = true → i ∈ bs.map Nat.log2) →
      (∀ b ∈ bs, Orth n w b) → w = 0 := by
  intro bs
  induction bs with
  | nil =>
    intro _ _ _ w hw _
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.zero_testBit]
    cases h : w.testBit i
    · rfl
    · exact absurd (hw i h) (by simp)
  | cons b bs ih =>
    intro hred hnz hlt w hw horth
    have hb0 : b ≠ 0 := hnz b (List.mem_cons_self ..)
    have hbn : Nat.log2 b < n := log2_lt_of_lt_two_pow hb0 (hlt b (List.mem_cons_self ..))
    have hwp : w.testBit (Nat.log2 b) = false := by
      have h1 := horth b (List.mem_cons_self ..)
      unfold Orth dotCount at h1
      have hcongr : (List.range n).filter (fun i => w.testBit i && b.testBit i) =
          (List.range n).filter (fun i => decide (i = Nat.log2 b) && w.testBit (Nat.log2 b)) := by
        apply List.filter_congr
        intro i _
        by_cases hip : i = Nat.log2 b
        · subst hip
          rw [testBit_log2_self hb0]
          simp
        · simp only [hip, decide_false, Bool.false_and]
          cases hwi : w.testBit i
          · rfl
          · have hmem := hw i hwi
            rw [List.map_cons, List.mem_cons] at hmem
            rcases hmem with h | h
            · exact absurd h hip
            · obtain ⟨b', hb', rfl⟩ := List.mem_map.mp h
              rw [hred.1 b' hb']
              rfl
      rw [hcongr, length_filter_range_single n _ hbn] at h1
      cases hc : w.testBit (Nat.log2 b)
      · rfl
      · rw [hc] at h1
        simp at h1
    apply ih hred.2 (fun b' hb' => hnz b' (List.mem_cons_of_mem _ hb'))
      (fun b' hb' => hlt b' (List.mem_cons_of_mem _ hb')) w
    · intro i hi
      have hmem := hw i hi
      rw [List.map_cons, List.mem_cons] at hmem
      rcases hmem with h | h
      · exfalso
        rw [h, hwp] at hi
        exact Bool.false_ne_true hi
      · exact h
    · intro b' hb'
      exact horth b' (List.mem_cons_of_mem _ hb')

/-! ### Independent families have full greedy rank -/

theorem rankBitmasks_eq_length_of_prefix_indep (l : List Nat)
    (h : ∀ l₁ v l₂, l = l₁ ++ v :: l₂ → ¬ inSpanMasks l₁ v) : rankBitmasks l = l.length := by
  have key : ∀ l₂ l₁ : List Nat, l = l₁ ++ l₂ → rankBitmasks l₁ = l₁.length →
      rankBitmasks (l₁ ++ l₂) = (l₁ ++ l₂).length := by
    intro l₂
    induction l₂ with
    | nil => intro l₁ _ h1; simpa using h1
    | cons v l₂ ih =>
      intro l₁ hsplit h1
      have hnot := h l₁ v l₂ hsplit
      have hstep : rankBitmasks (l₁ ++ [v]) = (l₁ ++ [v]).length := by
        rw [rankBitmasks_append_singleton_of_not_mem _ _ hnot, h1]
        simp
      have := ih (l₁ ++ [v]) (by rw [hsplit, List.append_assoc]; rfl) hstep
      rw [List.append_assoc] at this
      simpa using this
  have := key l [] rfl rfl
  simpa using this

/-- An independent mask list has no member in the span of the members before
    it. -/
theorem not_inSpan_of_independent {xs : List Nat} (h : independentMasks xs) :
    ∀ l₁ v l₂, xs = l₁ ++ v :: l₂ → ¬ inSpanMasks l₁ v := by
  intro l₁ v l₂ hx ⟨cs, hlen, h01, hval⟩
  subst hx
  have hall := h (cs ++ 1 :: List.replicate l₂.length 0) (by simp [hlen]) ?_ ?_
  · have := hall 1 (List.mem_append_right _ (List.mem_cons_self ..))
    exact absurd this (by decide)
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h01 c hc
    · rcases List.mem_cons.mp hc with hc | hc
      · exact Or.inr hc
      · exact Or.inl (List.mem_replicate.mp hc).2
  · rw [combineMasks_append l₁ (v :: l₂) cs _ hlen, hval]
    simp only [combineMasks]
    rw [combineMasks_zero_coeffs l₂ _ (fun c hc => (List.mem_replicate.mp hc).2)]
    simp

/-! ### The dimension bound -/

/-- Two mask lists below `2 ^ n` with pairwise orthogonal generators have
    ranks summing to at most `n`. -/
theorem rank_add_rank_le (n : Nat) (mX mZ : List Nat)
    (hX : ∀ m ∈ mX, ∀ j, n ≤ j → m.testBit j = false)
    (hZ : ∀ m ∈ mZ, ∀ j, n ≤ j → m.testBit j = false)
    (horth : ∀ x ∈ mX, ∀ z ∈ mZ, Orth n x z) :
    rankBitmasks mX + rankBitmasks mZ ≤ n := by
  have hpdX := foldl_insertBasis_pivotDistinct mX [] pivotDistinct_nil
  have hpdZ := foldl_insertBasis_pivotDistinct mZ [] pivotDistinct_nil
  have hpresX := foldl_insertBasis_preserved mX n hX [] (by simp) (by simp)
  have hpresZ := foldl_insertBasis_preserved mZ n hZ [] (by simp) (by simp)
  have hredZ := foldl_insertBasis_reduced mZ [] pivotDistinct_nil trivial
  have hspanX := spanEq_foldl_insertBasis_nil mX
  have hspanZ := spanEq_foldl_insertBasis_nil mZ
  have hrX : rankBitmasks mX = (mX.foldl insertBasis []).length := rfl
  have hrZ : rankBitmasks mZ = (mZ.foldl insertBasis []).length := rfl
  rw [hrX, hrZ]
  generalize mX.foldl insertBasis [] = BX at hpdX hpresX hspanX ⊢
  generalize mZ.foldl insertBasis [] = BZ at hpdZ hpresZ hredZ hspanZ ⊢
  -- the unit masks at the pivots of `BZ`
  let E : List Nat := BZ.map (fun b => 2 ^ Nat.log2 b)
  have hElen : E.length = BZ.length := List.length_map _
  have hEmem : ∀ e ∈ E, ∃ b ∈ BZ, e = 2 ^ Nat.log2 b := by
    intro e he
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
    exact ⟨b, hb, rfl⟩
  have hBZlt : ∀ b ∈ BZ, b < 2 ^ n := fun b hb =>
    lt_two_pow_of_high_bits_false b n (hpresZ.2 b hb)
  have hElog : E.map Nat.log2 = BZ.map Nat.log2 := by
    rw [List.map_map]
    apply List.map_congr_left
    intro b _
    simp [Nat.log2_two_pow]
  -- every member of span X is orthogonal to every member of BZ
  have horthX : ∀ u, inSpanMasks BX u → ∀ b ∈ BZ, Orth n u b := by
    intro u hu b hb
    exact orth_of_inSpan n ((hspanX u).mp hu) ((hspanZ b).mp (inSpanMasks_of_mem hb)) horth
  -- the unit case of prefix independence
  have unit_case : ∀ (a' : List Nat) (v : Nat) (l₂ : List Nat), E = a' ++ v :: l₂ →
      ¬ inSpanMasks (BX ++ a') v := by
    intro a' v l₂ hE ⟨cs, hlen, h01, hval⟩
    -- v is a unit at a pivot p
    have hvE : v ∈ E := by rw [hE]; exact List.mem_append_right _ (List.mem_cons_self ..)
    obtain ⟨bv, hbv, hv⟩ := hEmem v hvE
    -- the exponents of a' avoid p
    have hnd : (E.map Nat.log2).Nodup := by rw [hElog]; exact hpdZ.2
    rw [hE, List.map_append, List.map_cons] at hnd
    have hpnot : ∀ e ∈ a', Nat.log2 e ≠ Nat.log2 v := by
      intro e he
      exact (List.nodup_append.mp hnd).2.2 (Nat.log2 e) (List.mem_map.mpr ⟨e, he, rfl⟩)
        (Nat.log2 v) (List.mem_cons_self ..)
    have ha'E : ∀ e ∈ a', e ∈ E := by
      intro e he
      rw [hE]
      exact List.mem_append_left _ he
    -- a' members have a single bit, at a pivot other than p
    have ha'bit : ∀ e ∈ a', ∀ i, e.testBit i = true → i ∈ BZ.map Nat.log2 ∧ i ≠ Nat.log2 v := by
      intro e he i hi
      obtain ⟨b, hb, rfl⟩ := hEmem e (ha'E e he)
      rw [Nat.testBit_two_pow] at hi
      have hi' : Nat.log2 b = i := by simpa using hi
      refine ⟨List.mem_map.mpr ⟨b, hb, hi'⟩, ?_⟩
      have hne := hpnot _ he
      rw [Nat.log2_two_pow] at hne
      rw [← hi']
      exact hne
    -- split the combination at the seam
    rw [← List.take_append_drop BX.length cs,
      combineMasks_append BX a' _ _ (by rw [List.length_take, hlen, List.length_append]; omega)]
      at hval
    generalize hu : combineMasks BX (cs.take BX.length) = u at hval
    generalize he : combineMasks a' (cs.drop BX.length) = e at hval
    have huspan : inSpanMasks BX u :=
      ⟨cs.take BX.length, by rw [List.length_take, hlen, List.length_append]; omega,
        fun c hc => h01 c (List.mem_of_mem_take hc), hu⟩
    -- e has clear bits off the pivots of a', in particular at p
    have hebit : ∀ i, e.testBit i = true → i ∈ BZ.map Nat.log2 ∧ i ≠ Nat.log2 v := by
      intro i hi
      by_cases hex : ∃ x ∈ a', x.testBit i = true
      · obtain ⟨x, hx, hxi⟩ := hex
        exact ha'bit x hx i hxi
      · have hall : ∀ x ∈ a', x.testBit i = false := by
          intro x hx
          cases h : x.testBit i
          · rfl
          · exact absurd ⟨x, hx, h⟩ hex
        rw [← he, combineMasks_testBit_false a' _ i hall] at hi
        exact absurd hi Bool.false_ne_true
    -- u = v ^^^ e is supported on the pivots of BZ
    have hueq : u = v ^^^ e := by
      rw [← hval, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    have husupp : ∀ i, u.testBit i = true → i ∈ BZ.map Nat.log2 := by
      intro i hi
      rw [hueq, Nat.testBit_xor, hv, Nat.testBit_two_pow] at hi
      by_cases hip : Nat.log2 bv = i
      · exact List.mem_map.mpr ⟨bv, hbv, hip⟩
      · simp only [hip, decide_false, Bool.false_xor] at hi
        exact (hebit i hi).1
    -- hence u = 0
    have hu0 : u = 0 := eq_zero_of_orth_reduced n BZ hredZ hpdZ.1 hBZlt u husupp
      (horthX u huspan)
    -- so v = e, but e has bit p clear while v has it set
    have hve : v = e := by
      rw [hu0] at hueq
      exact xor_eq_zero_cancel hueq.symm
    have hvbit : v.testBit (Nat.log2 v) = true := by
      rw [hv, Nat.log2_two_pow, Nat.testBit_two_pow_self]
    have hvbit' : e.testBit (Nat.log2 v) = true := by
      rw [← hve]
      exact hvbit
    exact (hebit _ hvbit').2 rfl
  -- prefix independence of BX ++ E
  have hindep : ∀ l₁ v l₂, BX ++ E = l₁ ++ v :: l₂ → ¬ inSpanMasks l₁ v := by
    intro l₁ v l₂ hsplit
    rcases List.append_eq_append_iff.mp hsplit with ⟨a', hl₁, hE⟩ | ⟨c', hBX, hc'⟩
    · rw [hl₁]
      exact unit_case a' v l₂ hE
    · cases c' with
      | nil =>
        rw [List.append_nil] at hBX
        rw [List.nil_append] at hc'
        rw [← hBX]
        have := unit_case [] v l₂ (by rw [List.nil_append]; exact hc'.symm)
        rw [List.append_nil] at this
        exact this
      | cons v' c'' =>
        rw [List.cons_append] at hc'
        have hv := (List.cons.inj hc').1
        subst hv
        exact not_inSpan_of_independent (independentMasks_pivotDistinct BX hpdX) l₁ v c'' hBX
  have hfull := rankBitmasks_eq_length_of_prefix_indep (BX ++ E) hindep
  have hbound : rankBitmasks (BX ++ E) ≤ n := by
    apply rankBitmasks_le_of_high_bits_false
    intro m hm j hj
    rcases List.mem_append.mp hm with hm | hm
    · exact hpresX.2 m hm j hj
    · obtain ⟨b, hb, rfl⟩ := hEmem m hm
      rw [Nat.testBit_two_pow]
      have := log2_lt_of_lt_two_pow (hpdZ.1 b hb) (hBZlt b hb)
      simp only [decide_eq_false_iff_not]
      omega
  rw [hfull, List.length_append, hElen] at hbound
  exact hbound

/-- The dimension bound from well-formedness: I1 makes the two sector spans
    orthogonal, I2 is not needed beyond what the greedy rank already reads. -/
theorem ranksFit_of_wf (s : CodeState) (hwf : EncodingWellFormed s) : RanksFit s := by
  have hsupQ := supports_subset_of_wf hwf
  have hQ : s.Q.Nodup := hwf.1
  have hnd : ∀ r ∈ s.rows, r.support.Nodup := fun r hr => by
    simpa using List.all_eq_true.mp hwf.2.2.2.2.1 r hr
  have hI1 : I1 s := hwf.2.2.2.2.2.2.1
  unfold RanksFit sectorRank
  apply rank_add_rank_le s.Q.length
  · intro m hm j hj
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hm
    exact rowBitmask_testBit_high s.Q hQ r j hj
  · intro m hm j hj
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hm
    exact rowBitmask_testBit_high s.Q hQ r j hj
  · intro x hx z hz
    obtain ⟨rX, hrX, rfl⟩ := List.mem_map.mp hx
    obtain ⟨rZ, hrZ, rfl⟩ := List.mem_map.mp hz
    have hrXs := (List.mem_filter.mp hrX).1
    have hrZs := (List.mem_filter.mp hrZ).1
    have hrXσ : rX.sector = Sector.X := by simpa using (List.mem_filter.mp hrX).2
    have hrZσ : rZ.sector = Sector.Z := by simpa using (List.mem_filter.mp hrZ).2
    unfold Orth
    rw [dotCount_rowBitmask s.Q hQ rX rZ (hnd rX hrXs) (hsupQ rX hrXs)]
    exact hI1 rX rZ hrXs hrZs hrXσ hrZσ

end CodeCalculus
