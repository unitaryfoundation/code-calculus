import CodeCalculus.WellFormedness
import CodeCalculus.RanksFit
import CodeCalculus.RebaseRankSector

namespace CodeCalculus

/-!
# Graft well-formedness preservation ()

`EncodingWellFormed` is preserved by the structural graft transition
(`spec/OPERATIONAL_SEMANTICS.md` §4.12) under the transition's own premises
(`wf_graftState`, `wf_graft_of_eval`), and `wf_of_eval_all` lifts
well-formedness preservation to every evaluation of every command.
`Soundness.lean` discharges the graft's output well-formedness row against
`wf_graft_of_eval`.

The list-level clauses, I1, and the identifier discipline follow §4.12
clause by clause: a minted adjacent-sum row has no `q`-coordinate because both
chain rows contain `q`, so its intersection with a shortened opposite-sector
row has the parity of the sum of two input intersections; a surviving row of
the graft sector does not touch `q`, so shortening the opposite sector at `q`
leaves its intersections unchanged.

I2 is derived by counting rather than by the lifting argument §4.12 writes
out. The greedy rank of a mask list is at most its length, and equals it
exactly when every row is independent of its peers (`rankBitmasks_le_length`,
`sectorRank_eq_length_of_I2`, `i2_of_full_rank`). Deleting the `q` bit from
every mask is an XOR-linear map, and such a map cannot raise the greedy rank
(`rankBitmasks_map_le`), so the opposite sector's rank does not grow; the
graft sector loses one row. The transition's `k`-preservation premise, read
with the dimension bound `RanksFit` on the input so that the truncated
subtraction in `stateK` is exact, then forces both output sectors to full
rank, which is I2. The bound is derived from well-formedness by
`ranksFit_of_wf` (`RanksFit.lean`, ).

Statements about these list functions only; no soundness claim for the
calculus is made here (README *Status*).
-/

/-! ### XOR-linear maps on masks do not raise the rank -/

/-- A map on masks that respects zero and XOR. -/
def XorLinear (f : Nat → Nat) : Prop := f 0 = 0 ∧ ∀ a b, f (a ^^^ b) = f a ^^^ f b

theorem combineMasks_map (f : Nat → Nat) (hf : XorLinear f) :
    ∀ (xs cs : List Nat), combineMasks (xs.map f) cs = f (combineMasks xs cs) := by
  intro xs
  induction xs with
  | nil => intro cs; simp [combineMasks_nil, hf.1]
  | cons m ms ih =>
    intro cs
    cases cs with
    | nil => simp [combineMasks, hf.1]
    | cons c cs =>
      simp only [List.map_cons, combineMasks]
      rw [hf.2, ih]
      by_cases hc : c = 1
      · simp [hc]
      · simp [hc, hf.1]

theorem inSpanMasks_map (f : Nat → Nat) (hf : XorLinear f) {xs : List Nat} {v : Nat}
    (h : inSpanMasks xs v) : inSpanMasks (xs.map f) (f v) := by
  obtain ⟨cs, hlen, h01, hval⟩ := h
  refine ⟨cs, by rw [hlen, List.length_map], h01, ?_⟩
  rw [combineMasks_map f hf, hval]

theorem inSpanMasks_map_iff (f : Nat → Nat) (hf : XorLinear f) (xs : List Nat) (w : Nat) :
    inSpanMasks (xs.map f) w ↔ ∃ v, inSpanMasks xs v ∧ f v = w := by
  constructor
  · rintro ⟨cs, hlen, h01, hval⟩
    refine ⟨combineMasks xs cs, ⟨cs, by rw [hlen, List.length_map], h01, rfl⟩, ?_⟩
    rw [← combineMasks_map f hf, hval]
  · rintro ⟨v, hv, rfl⟩
    exact inSpanMasks_map f hf hv

/-- The image of a mask list under an XOR-linear map has greedy rank at most
    the greedy rank of the list: the image of a greedy basis spans the image. -/
theorem rankBitmasks_map_le (f : Nat → Nat) (hf : XorLinear f) (xs : List Nat) :
    rankBitmasks (xs.map f) ≤ rankBitmasks xs := by
  have hspan : ∀ w, inSpanMasks (xs.map f) w ↔
      inSpanMasks ((xs.foldl insertBasis []).map f) w := by
    intro w
    rw [inSpanMasks_map_iff f hf, inSpanMasks_map_iff f hf]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, (spanEq_foldl_insertBasis_nil xs v).mpr hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, (spanEq_foldl_insertBasis_nil xs v).mp hv, rfl⟩
  rw [rankBitmasks_eq_of_span_eq hspan]
  calc rankBitmasks ((xs.foldl insertBasis []).map f)
      ≤ ((xs.foldl insertBasis []).map f).length := rankBitmasks_le_length _
    _ = (xs.foldl insertBasis []).length := List.length_map _
    _ = rankBitmasks xs := rfl

/-! ### Deleting one bit position -/

/-- Delete bit position `i` from a mask: the bits below `i` stay in place and
    the bits above `i` move down by one. -/
def deleteBit (i m : Nat) : Nat :=
  (m &&& (2 ^ i - 1)) ||| ((m >>> (i + 1)) <<< i)

theorem testBit_deleteBit (i m j : Nat) :
    (deleteBit i m).testBit j = if j < i then m.testBit j else m.testBit (j + 1) := by
  unfold deleteBit
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  by_cases h : j < i
  · have h' : ¬ (j ≥ i) := by omega
    simp [h, h']
  · have h' : j ≥ i := by omega
    have e : i + 1 + (j - i) = j + 1 := by omega
    simp [h, h', e]

theorem deleteBit_xorLinear (i : Nat) : XorLinear (deleteBit i) := by
  refine ⟨?_, ?_⟩
  · apply Nat.eq_of_testBit_eq
    intro j
    rw [testBit_deleteBit]
    simp [Nat.zero_testBit]
  · intro a b
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [testBit_deleteBit, Nat.testBit_xor]
    by_cases h : j < i <;> simp [h]

/-! ### Fresh identifiers -/

theorem mintFresh_not_mem (used : List Nat) : ∀ n, ∀ x ∈ mintFresh used n, x ∉ used := by
  intro n
  induction n generalizing used with
  | zero => intro x hx; simp [mintFresh] at hx
  | succ n ih =>
    intro x hx
    simp only [mintFresh, List.mem_cons] at hx
    rcases hx with rfl | hx
    · intro h
      exact canonicalMint_fresh used (List.contains_iff_mem.mpr h)
    · intro h
      exact ih (used ++ [canonicalMint used]) x hx (List.mem_append_left _ h)

theorem mintFresh_nodup (used : List Nat) : ∀ n, (mintFresh used n).Nodup := by
  intro n
  induction n generalizing used with
  | zero => simp [mintFresh]
  | succ n ih =>
    simp only [mintFresh]
    rw [List.nodup_cons]
    refine ⟨?_, ih _⟩
    intro h
    exact mintFresh_not_mem _ n _ h (List.mem_append_right _ (List.mem_singleton.mpr rfl))

/-! ### Sorting -/

theorem insertSorted_sorted (x : Nat) : ∀ xs : List Nat, xs.Pairwise (· ≤ ·) →
    (insertSorted x xs).Pairwise (· ≤ ·) := by
  intro xs
  induction xs with
  | nil => intro _; simp [insertSorted]
  | cons y ys ih =>
    intro h
    rw [List.pairwise_cons] at h
    simp only [insertSorted]
    split
    · rename_i hxy
      rw [List.pairwise_cons]
      refine ⟨?_, List.pairwise_cons.mpr h⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hxy
      · exact Nat.le_trans hxy (h.1 z hz)
    · rename_i hxy
      rw [List.pairwise_cons]
      refine ⟨?_, ih h.2⟩
      intro z hz
      rw [(insertSorted_perm x ys).mem_iff, List.mem_cons] at hz
      rcases hz with rfl | hz
      · omega
      · exact h.1 z hz

theorem sortNat_sorted : ∀ qs : List Nat, (sortNat qs).Pairwise (· ≤ ·) := by
  intro qs
  induction qs with
  | nil => simp [sortNat]
  | cons x xs ih => exact insertSorted_sorted x _ ih

/-! ### Counting helpers -/

theorem length_filter_and_split {α : Type} (p r : α → Bool) (l : List α) :
    (l.filter p).length =
      (l.filter (fun x => p x && r x)).length + (l.filter (fun x => p x && !r x)).length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons]
    cases hp : p x <;> cases hr : r x <;> simp <;> omega

theorem supportIntersectionSize_perm_left {a a' : List Nat} (h : a.Perm a') (b : List Nat) :
    supportIntersectionSize a b = supportIntersectionSize a' b := by
  rw [supportIntersectionSize_eq_length_filter, supportIntersectionSize_eq_length_filter]
  exact (h.filter _).length_eq

theorem map_snd_zip_sublist {α β : Type} :
    ∀ (a : List α) (b : List β), ((a.zip b).map Prod.snd).Sublist b := by
  intro a
  induction a with
  | nil => intro b; simp
  | cons x xs ih =>
    intro b
    cases b with
    | nil => simp
    | cons y ys =>
      rw [List.zip_cons_cons, List.map_cons]
      exact (ih ys).cons_cons y

theorem length_filter_ne_succ (q : Nat) : ∀ Q : List Nat, Q.Nodup → q ∈ Q →
    (Q.filter (fun x => x ≠ q)).length + 1 = Q.length := by
  intro Q
  induction Q with
  | nil => intro _ h; simp at h
  | cons x xs ih =>
    intro hnd hmem
    rw [List.nodup_cons] at hnd
    by_cases hxq : x = q
    · subst hxq
      have hxs : xs.filter (fun y => y ≠ x) = xs := by
        rw [List.filter_eq_self]
        intro a ha
        simp only [decide_eq_true_eq]
        intro h
        exact hnd.1 (h ▸ ha)
      rw [List.filter_cons_of_neg (by simp), hxs, List.length_cons]
    · have hmem' : q ∈ xs := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h.symm hxq
        · exact h
      rw [List.filter_cons_of_pos (by simpa using hxq), List.length_cons, List.length_cons,
        ih hnd.2 hmem']

/-- Positions of a duplicate-free list after filtering out one member. -/
theorem getElem?_filter_ne (q : Nat) : ∀ (Q : List Nat) (i j : Nat), Q.Nodup → Q[i]? = some q →
    (Q.filter (fun x => x ≠ q))[j]? = if j < i then Q[j]? else Q[j + 1]? := by
  intro Q
  induction Q with
  | nil => intro i j _ hi; simp at hi
  | cons x xs ih =>
    intro i j hnd hi
    rw [List.nodup_cons] at hnd
    by_cases hxq : x = q
    · subst hxq
      cases i with
      | zero =>
        have hxs : xs.filter (fun y => y ≠ x) = xs := by
          rw [List.filter_eq_self]
          intro a ha
          simp only [decide_eq_true_eq]
          intro h
          exact hnd.1 (h ▸ ha)
        rw [List.filter_cons_of_neg (by simp), hxs]
        simp
      | succ i =>
        exfalso
        rw [List.getElem?_cons_succ] at hi
        exact hnd.1 (List.mem_of_getElem? hi)
    · cases i with
      | zero =>
        rw [List.getElem?_cons_zero] at hi
        exact absurd (Option.some.inj hi) hxq
      | succ i =>
        rw [List.getElem?_cons_succ] at hi
        rw [List.filter_cons_of_pos (by simpa using hxq)]
        cases j with
        | zero => simp
        | succ j =>
          rw [List.getElem?_cons_succ, ih i j hnd.2 hi]
          simp only [List.getElem?_cons_succ]
          by_cases hj : j < i
          · simp [hj]
          · have : ¬ (j + 1 < i + 1) := by omega
            simp [hj, this]

/-! ### Supports with one qubit removed -/

/-- `a` is `b` with the qubit `q` removed, read as membership tests. -/
def SupportMinus (q : Nat) (a b : List Nat) : Prop :=
  (∀ x, x ≠ q → a.contains x = b.contains x) ∧ a.contains q = false

theorem supportMinus_filter (q : Nat) (b : List Nat) :
    SupportMinus q (b.filter (fun x => x ≠ q)) b := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_filter]
    simp [hx]
  · rw [Bool.eq_false_iff]
    intro h
    have := List.mem_filter.mp (List.contains_iff_mem.mp h)
    simp at this

theorem supportMinus_self (q : Nat) (b : List Nat) (h : b.contains q = false) :
    SupportMinus q b b :=
  ⟨fun _ _ => rfl, h⟩

theorem qubitBit_filter_ne (Q : List Nat) (hQ : Q.Nodup) (q i : Nat) (hi : Q[i]? = some q)
    (a b : List Nat) (h : SupportMinus q a b) (j : Nat) :
    qubitBit (Q.filter (fun x => x ≠ q)) a j =
      if j < i then qubitBit Q b j else qubitBit Q b (j + 1) := by
  have hsome : ∀ x, (Q.filter (fun y => y ≠ q))[j]? = some x → x ≠ q := by
    intro x hx
    have := List.mem_filter.mp (List.mem_of_getElem? hx)
    simpa using this.2
  unfold qubitBit
  rw [getElem?_filter_ne q Q i j hQ hi] at hsome ⊢
  by_cases hj : j < i
  · simp only [hj, ↓reduceIte] at hsome ⊢
    cases hQj : Q[j]? with
    | none => rfl
    | some x => exact h.1 x (hsome x hQj)
  · simp only [hj, ↓reduceIte] at hsome ⊢
    cases hQj : Q[j + 1]? with
    | none => rfl
    | some x => exact h.1 x (hsome x hQj)

/-- The bitmask of a row with `q` removed, over the namespace with `q`
    removed, is the input bitmask with the `q` position deleted. -/
theorem rowBitmask_filter_of_supportMinus (Q : List Nat) (hQ : Q.Nodup) (q i : Nat)
    (hi : Q[i]? = some q) (r r' : Row) (h : SupportMinus q r'.support r.support) :
    rowBitmask (Q.filter (fun x => x ≠ q)) r' = deleteBit i (rowBitmask Q r) := by
  have hQ' : (Q.filter (fun x => x ≠ q)).Nodup := hQ.sublist List.filter_sublist
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_rowBitmask _ hQ', testBit_deleteBit]
  simp only [testBit_rowBitmask Q hQ]
  exact qubitBit_filter_ne Q hQ q i hi _ _ h j

/-! ### Independence and full rank -/

/-- On a state whose displayed generators are independent (I2), every
    sector's greedy rank is its row count. -/
theorem sectorRank_eq_length_of_I2 (s : CodeState) (hQ : s.Q.Nodup)
    (hids : (s.rows.map Row.id).Nodup) (hI2 : I2 s) (σ : Sector) :
    sectorRank s.Q s.rows σ = (sectorRows s σ).length := by
  have key : ∀ l₂ l₁ : List Row, sectorRows s σ = l₁ ++ l₂ →
      rankBitmasks (l₁.map (rowBitmask s.Q)) = l₁.length →
      rankBitmasks ((l₁ ++ l₂).map (rowBitmask s.Q)) = (l₁ ++ l₂).length := by
    intro l₂
    induction l₂ with
    | nil => intro l₁ _ h; simpa using h
    | cons r l₂ ih =>
      intro l₁ hsplit h1
      have hrsec : r ∈ sectorRows s σ := by
        rw [hsplit]
        exact List.mem_append_right _ (List.mem_cons_self ..)
      have hr : r ∈ s.rows := (List.mem_filter.mp hrsec).1
      have hrσ : r.sector = σ := by simpa using (List.mem_filter.mp hrsec).2
      have hl₁ : l₁.Sublist (sectorRows s σ) := by
        rw [hsplit]
        exact List.sublist_append_left _ _
      have hsubpeers : l₁.Sublist
          (s.rows.filter (fun r' => r'.sector = r.sector ∧ r'.id ≠ r.id)) := by
        have hnd : ((sectorRows s σ).map Row.id).Nodup :=
          hids.sublist (List.filter_sublist.map Row.id)
        rw [hsplit, List.map_append, List.map_cons] at hnd
        have hall : ∀ x ∈ l₁, decide (x.sector = r.sector ∧ x.id ≠ r.id) = true := by
          intro x hx
          have hxσ : x.sector = σ := by simpa using (List.mem_filter.mp (hl₁.subset hx)).2
          have hne : x.id ≠ r.id := by
            intro heq
            exact (List.nodup_append.mp hnd).2.2 x.id (List.mem_map.mpr ⟨x, hx, rfl⟩) r.id
              (List.mem_cons_self ..) heq
          simp [hxσ, hrσ, hne]
        have h1' : l₁ = l₁.filter (fun r' => r'.sector = r.sector ∧ r'.id ≠ r.id) :=
          (List.filter_eq_self.mpr hall).symm
        have h2 : (sectorRows s σ).filter (fun r' => r'.sector = r.sector ∧ r'.id ≠ r.id) =
            s.rows.filter (fun r' => r'.sector = r.sector ∧ r'.id ≠ r.id) := by
          unfold sectorRows
          rw [List.filter_filter]
          apply List.filter_congr
          intro x _
          by_cases hx : x.sector = σ <;> simp [hx, hrσ]
        rw [h1', ← h2]
        exact hl₁.filter _
      have hnot : ¬ inSpanMasks (l₁.map (rowBitmask s.Q)) (rowBitmask s.Q r) := by
        intro hsp
        have hind := (independentGenerator_iff s hids r hr).mp (hI2 r hr)
        exact hind (inSpanRows_of_sublist s.Q hsubpeers _
          ((inSpanRows_iff_inSpanMasks s.Q hQ l₁ r).mpr hsp))
      have hstep : rankBitmasks ((l₁ ++ [r]).map (rowBitmask s.Q)) = (l₁ ++ [r]).length := by
        rw [List.map_append, List.map_singleton, rankBitmasks_append_singleton_of_not_mem _ _ hnot,
          h1]
        simp
      have := ih (l₁ ++ [r]) (by rw [hsplit, List.append_assoc]; rfl) hstep
      rw [List.append_assoc] at this
      simpa using this
  have := key (sectorRows s σ) [] rfl rfl
  simpa [sectorRank, sectorRows] using this

/-- A state whose every sector has full greedy rank satisfies I2. -/
theorem i2_of_full_rank (t : CodeState) (hQ : t.Q.Nodup) (hids : (t.rows.map Row.id).Nodup)
    (hfull : ∀ σ, sectorRank t.Q t.rows σ = (sectorRows t σ).length) : I2 t := by
  intro row hrow
  rw [independentGenerator_iff t hids row hrow]
  intro hspan
  have hmask := (inSpanRows_iff_inSpanMasks t.Q hQ _ row).mp hspan
  have hperm := sectorRows_perm_peers t hids row hrow
  have hrank := hfull row.sector
  unfold sectorRank sectorRows at hrank
  rw [rankBitmasks_perm (hperm.map (rowBitmask t.Q)), hperm.length_eq, List.map_append,
    List.map_singleton, List.length_append, List.length_singleton] at hrank
  have hspaneq : ∀ v,
      inSpanMasks ((t.rows.filter (fun r' => r'.sector = row.sector ∧ r'.id ≠ row.id)).map
        (rowBitmask t.Q) ++ [rowBitmask t.Q row]) v ↔
      inSpanMasks ((t.rows.filter (fun r' => r'.sector = row.sector ∧ r'.id ≠ row.id)).map
        (rowBitmask t.Q)) v := by
    intro v
    constructor
    · intro hv
      refine inSpanMasks_trans ?_ hv
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact inSpanMasks_of_mem hg
      · rw [List.mem_singleton] at hg
        rw [hg]
        exact hmask
    · exact inSpanMasks_append_right
  rw [rankBitmasks_eq_of_span_eq hspaneq] at hrank
  have hle := rankBitmasks_le_length
    ((t.rows.filter (fun r' => r'.sector = row.sector ∧ r'.id ≠ row.id)).map (rowBitmask t.Q))
  rw [List.length_map] at hle
  omega

/-! ### The graft update, piece by piece -/

/-- The shortening the graft applies to a non-chain row. -/
def graftShorten (q : Nat) (σ : Sector) (r : Row) : Row :=
  if r.sector = oppositeSector σ ∧ r.support.contains q then shortenRow q r else r

/-- The rows the graft keeps (shortened or not). -/
def graftNonChain (s : CodeState) (ids : List Nat) : List Row :=
  s.rows.filter (fun r => ¬ ids.contains r.id)

/-- The chain rows named by the command, in command order. -/
def graftChain (s : CodeState) (ids : List Nat) : List Row := ids.filterMap (rowById s)

/-- One minted adjacent-sum row. -/
def graftMintedRow (s : CodeState) (q : Nat) (σ : Sector) (x : (Row × Row) × Nat) : Row :=
  { id := x.2
  , sector := σ
  , support := sortNat ((s.Q.filter (fun y => y ≠ q)).filter (fun y =>
      x.1.1.support.contains y ≠ x.1.2.support.contains y)) }

/-- The minted rows of the graft. -/
def graftMintedRows (s : CodeState) (q : Nat) (σ : Sector) (ids : List Nat) : List Row :=
  (((graftChain s ids).zip ((graftChain s ids).drop 1)).zip
    (mintFresh s.used (ids.length - 1))).map (graftMintedRow s q σ)

theorem graftState_Q' (s : CodeState) (q : Nat) (σ : Sector) (ids : List Nat) :
    (graftState s q σ ids).Q = s.Q.filter (fun x => x ≠ q) := rfl

theorem graftState_rows (s : CodeState) (q : Nat) (σ : Sector) (ids : List Nat) :
    (graftState s q σ ids).rows =
      (graftNonChain s ids).map (graftShorten q σ) ++ graftMintedRows s q σ ids := rfl

theorem graftState_used (s : CodeState) (q : Nat) (σ : Sector) (ids : List Nat) :
    (graftState s q σ ids).used = s.used ++ mintFresh s.used (ids.length - 1) := rfl

theorem sector_eq_or_opp (τ σ : Sector) : τ = σ ∨ τ = oppositeSector σ := by
  cases τ <;> cases σ <;> simp [oppositeSector]

theorem graftShorten_id (q : Nat) (σ : Sector) (r : Row) : (graftShorten q σ r).id = r.id := by
  unfold graftShorten shortenRow
  split <;> (try split) <;> rfl

theorem graftShorten_sector (q : Nat) (σ : Sector) (r : Row) :
    (graftShorten q σ r).sector = r.sector := by
  unfold graftShorten shortenRow
  split <;> (try split) <;> rfl

theorem graftShorten_support_cases (q : Nat) (σ : Sector) (r : Row) :
    (graftShorten q σ r).support = r.support.filter (fun x => x ≠ q) ∨
      (graftShorten q σ r).support = r.support := by
  unfold graftShorten shortenRow
  split
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exact Or.inr rfl

theorem graftShorten_eq_of_same (q : Nat) (σ : Sector) (r : Row) (hσ : r.sector = σ) :
    graftShorten q σ r = r := by
  unfold graftShorten
  split
  · rename_i h
    exact absurd (hσ.symm.trans h.1) (oppositeSector_ne σ).symm
  · rfl

theorem shortenRow_support_of_contains (q : Nat) (r : Row) (h : r.support.contains q = true) :
    (shortenRow q r).support = r.support.filter (fun x => x ≠ q) := by
  unfold shortenRow
  split
  · rfl
  · rename_i h'
    exact absurd h h'

theorem graftShorten_supportMinus_of_opp (q : Nat) (σ : Sector) (r : Row)
    (hσ : r.sector = oppositeSector σ) :
    SupportMinus q (graftShorten q σ r).support r.support := by
  unfold graftShorten
  split
  · rename_i h
    rw [shortenRow_support_of_contains q r h.2]
    exact supportMinus_filter q r.support
  · rename_i h
    have hc : r.support.contains q = false := by
      by_cases hc : r.support.contains q = true
      · exact absurd ⟨hσ, hc⟩ h
      · exact Bool.eq_false_iff.mpr hc
    exact supportMinus_self q r.support hc

theorem graftNonChain_sublist (s : CodeState) (ids : List Nat) :
    (graftNonChain s ids).Sublist s.rows := List.filter_sublist

theorem mem_graftNonChain {s : CodeState} {ids : List Nat} {r : Row}
    (hr : r ∈ graftNonChain s ids) : r ∈ s.rows ∧ r.id ∉ ids := by
  have h := List.mem_filter.mp hr
  refine ⟨h.1, ?_⟩
  intro hmem
  have h2 := h.2
  simp only [decide_eq_true_eq] at h2
  exact h2 (List.contains_iff_mem.mpr hmem)

theorem mem_graftChain {s : CodeState} {ids : List Nat} {L : Row}
    (hL : L ∈ graftChain s ids) : L ∈ s.rows ∧ L.id ∈ ids := by
  unfold graftChain at hL
  obtain ⟨a, ha, hfind⟩ := List.mem_filterMap.mp hL
  unfold rowById at hfind
  refine ⟨List.mem_of_find?_eq_some hfind, ?_⟩
  have hid : L.id = a := by simpa using List.find?_some hfind
  rw [hid]
  exact ha

theorem mem_graftMintedRows {s : CodeState} {q : Nat} {σ : Sector} {ids : List Nat} {u : Row}
    (hu : u ∈ graftMintedRows s q σ ids) :
    ∃ L R id, L ∈ graftChain s ids ∧ R ∈ graftChain s ids ∧
      id ∈ mintFresh s.used (ids.length - 1) ∧ u = graftMintedRow s q σ ((L, R), id) := by
  unfold graftMintedRows at hu
  obtain ⟨⟨⟨L, R⟩, id⟩, hmem, rfl⟩ := List.mem_map.mp hu
  have h1 := List.of_mem_zip hmem
  have h2 := List.of_mem_zip h1.1
  exact ⟨L, R, id, h2.1, (List.drop_sublist 1 _).subset h2.2, h1.2, rfl⟩

theorem mem_graftState_rows {s : CodeState} {q : Nat} {σ : Sector} {ids : List Nat} {u : Row}
    (hu : u ∈ (graftState s q σ ids).rows) :
    (∃ r ∈ graftNonChain s ids, u = graftShorten q σ r) ∨ u ∈ graftMintedRows s q σ ids := by
  rw [graftState_rows] at hu
  rcases List.mem_append.mp hu with hu | hu
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hu
    exact Or.inl ⟨r, hr, rfl⟩
  · exact Or.inr hu

theorem graftMintedRows_length_le (s : CodeState) (q : Nat) (σ : Sector) (ids : List Nat) :
    (graftMintedRows s q σ ids).length ≤ ids.length - 1 := by
  unfold graftMintedRows
  rw [List.length_map, List.length_zip, mintFresh_length]
  exact Nat.min_le_right _ _

theorem graftMintedRows_ids_sublist (s : CodeState) (q : Nat) (σ : Sector) (ids : List Nat) :
    ((graftMintedRows s q σ ids).map Row.id).Sublist (mintFresh s.used (ids.length - 1)) := by
  unfold graftMintedRows
  rw [List.map_map]
  exact map_snd_zip_sublist _ _

/-! ### The command's identifier list names exactly the touching rows -/

theorem touchingRows_eq (s : CodeState) (σ : Sector) (q : Nat) :
    touchingRows s σ q = s.rows.filter (fun r => decide (r.sector = σ) && r.support.contains q) := by
  unfold touchingRows
  apply List.filter_congr
  intro r _
  cases r.support.contains q <;> simp

/-- Under the graft's premises, a displayed row's identifier is in the command's
    list exactly when the row is a graft-sector row touching `q`. -/
theorem graft_ids_iff (s : CodeState) (q : Nat) (σ : Sector) (ids : List Nat)
    (hidsnd : (s.rows.map Row.id).Nodup)
    (hlen : ids.length = (touchingRows s σ q).length) (hnodup : ids.Nodup)
    (hids : ∀ id ∈ ids, id ∈ (touchingRows s σ q).map Row.id) :
    ∀ r ∈ s.rows, (r.id ∈ ids ↔ (r.sector = σ ∧ r.support.contains q = true)) := by
  intro r hr
  have hT : ((touchingRows s σ q).map Row.id).Nodup :=
    hidsnd.sublist (List.filter_sublist.map Row.id)
  constructor
  · intro hin
    obtain ⟨r', hr', hrid⟩ := List.mem_map.mp (hids r.id hin)
    have hr'mem : r' ∈ s.rows := (List.mem_filter.mp hr').1
    have heq : r' = r := id_inj_of_nodup hidsnd hr'mem hr hrid
    subst heq
    simpa using (List.mem_filter.mp hr').2
  · intro hcond
    have hrT : r ∈ touchingRows s σ q :=
      List.mem_filter.mpr ⟨hr, by simp [hcond.1, List.contains_iff_mem.mp hcond.2]⟩
    have hidT : r.id ∈ (touchingRows s σ q).map Row.id := List.mem_map.mpr ⟨r, hrT, rfl⟩
    by_cases hnot : r.id ∈ ids
    · exact hnot
    exfalso
    have hnd' : (r.id :: ids).Nodup := List.nodup_cons.mpr ⟨hnot, hnodup⟩
    have hsub : ∀ v ∈ r.id :: ids, v ∈ (touchingRows s σ q).map Row.id := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hidT
      · exact hids v hv
    have := length_le_of_nodup_subset hT hnd' hsub
    rw [List.length_cons, List.length_map, ← hlen] at this
    omega

/-! ### The two sectors of the graft update -/

theorem graftMintedRow_support (s : CodeState) (q : Nat) (σ : Sector) (L R : Row) (id : Nat) :
    (graftMintedRow s q σ ((L, R), id)).support =
      sortNat ((s.Q.filter (fun y => y ≠ q)).filter (fun y =>
        L.support.contains y ≠ R.support.contains y)) := rfl

/-- The graft-sector rows of the input that do not touch `q`. -/
def graftUntouched (s : CodeState) (q : Nat) (σ : Sector) : List Row :=
  s.rows.filter (fun r => decide (r.sector = σ) && !r.support.contains q)

theorem graftUntouched_length (s : CodeState) (q : Nat) (σ : Sector) :
    (sectorRows s σ).length = (touchingRows s σ q).length + (graftUntouched s q σ).length := by
  unfold sectorRows graftUntouched
  rw [touchingRows_eq]
  exact length_filter_and_split (fun r : Row => decide (r.sector = σ))
    (fun r => r.support.contains q) s.rows

/-- The opposite sector of the update is the input's opposite sector,
    shortened at `q` row by row. -/
theorem graft_sectorRows_opp (s : CodeState) (q : Nat) (σ : Sector) (ids : List Nat)
    (hidsnd : (s.rows.map Row.id).Nodup)
    (hlen : ids.length = (touchingRows s σ q).length) (hnodup : ids.Nodup)
    (hids : ∀ id ∈ ids, id ∈ (touchingRows s σ q).map Row.id) :
    sectorRows (graftState s q σ ids) (oppositeSector σ) =
      (sectorRows s (oppositeSector σ)).map (graftShorten q σ) := by
  have hiff := graft_ids_iff s q σ ids hidsnd hlen hnodup hids
  unfold sectorRows
  rw [graftState_rows, List.filter_append]
  have hminted : (graftMintedRows s q σ ids).filter
      (fun r => r.sector = oppositeSector σ) = [] := by
    rw [List.filter_eq_nil_iff]
    intro u hu
    obtain ⟨L, R, id, _, _, _, rfl⟩ := mem_graftMintedRows hu
    simp [graftMintedRow, (oppositeSector_ne σ).symm]
  rw [hminted, List.append_nil, List.filter_map]
  congr 1
  unfold graftNonChain
  rw [List.filter_filter]
  apply List.filter_congr
  intro r hr
  simp only [Function.comp, graftShorten_sector]
  by_cases hs : r.sector = oppositeSector σ
  · have hnot : r.id ∉ ids := by
      intro hin
      have := (hiff r hr).mp hin
      exact oppositeSector_ne σ (hs.symm.trans this.1)
    simp [hs, hnot]
  · simp [hs]

/-- The graft sector of the update is the input's untouched graft-sector rows
    followed by the minted rows. -/
theorem graft_sectorRows_same (s : CodeState) (q : Nat) (σ : Sector) (ids : List Nat)
    (hidsnd : (s.rows.map Row.id).Nodup)
    (hlen : ids.length = (touchingRows s σ q).length) (hnodup : ids.Nodup)
    (hids : ∀ id ∈ ids, id ∈ (touchingRows s σ q).map Row.id) :
    sectorRows (graftState s q σ ids) σ =
      (graftUntouched s q σ).map (graftShorten q σ) ++ graftMintedRows s q σ ids := by
  have hiff := graft_ids_iff s q σ ids hidsnd hlen hnodup hids
  unfold sectorRows
  rw [graftState_rows, List.filter_append]
  have hminted : (graftMintedRows s q σ ids).filter (fun r => r.sector = σ) =
      graftMintedRows s q σ ids := by
    rw [List.filter_eq_self]
    intro u hu
    obtain ⟨L, R, id, _, _, _, rfl⟩ := mem_graftMintedRows hu
    simp [graftMintedRow]
  rw [hminted, List.filter_map]
  congr 2
  unfold graftNonChain graftUntouched
  rw [List.filter_filter]
  apply List.filter_congr
  intro r hr
  simp only [Function.comp, graftShorten_sector]
  by_cases hs : r.sector = σ
  · have : r.id ∈ ids ↔ q ∈ r.support :=
      (hiff r hr).trans ⟨fun h => List.contains_iff_mem.mp h.2,
        fun h => ⟨hs, List.contains_iff_mem.mpr h⟩⟩
    simp [hs, this]
  · simp [hs]

theorem graft_sectorRows_same_length_le (s : CodeState) (q : Nat) (σ : Sector) (ids : List Nat)
    (hidsnd : (s.rows.map Row.id).Nodup) (htouch : touchingRows s σ q ≠ [])
    (hlen : ids.length = (touchingRows s σ q).length) (hnodup : ids.Nodup)
    (hids : ∀ id ∈ ids, id ∈ (touchingRows s σ q).map Row.id) :
    (sectorRows (graftState s q σ ids) σ).length + 1 ≤ (sectorRows s σ).length := by
  rw [graft_sectorRows_same s q σ ids hidsnd hlen hnodup hids, List.length_append,
    List.length_map, graftUntouched_length s q σ, ← hlen]
  have h1 := graftMintedRows_length_le s q σ ids
  have hm : 1 ≤ ids.length := by
    rw [hlen]
    exact Nat.pos_of_ne_zero (fun h => htouch (List.eq_nil_of_length_eq_zero h))
  omega

/-- Shortening every opposite-sector row at `q` deletes one bit position from
    every mask, which cannot raise the greedy rank. -/
theorem graft_sectorRank_opp_le (s : CodeState) (q : Nat) (σ : Sector) (ids : List Nat)
    (hQ : s.Q.Nodup) (hq : q ∈ s.Q) (hidsnd : (s.rows.map Row.id).Nodup)
    (hlen : ids.length = (touchingRows s σ q).length) (hnodup : ids.Nodup)
    (hids : ∀ id ∈ ids, id ∈ (touchingRows s σ q).map Row.id) :
    sectorRank (graftState s q σ ids).Q (graftState s q σ ids).rows (oppositeSector σ) ≤
      sectorRank s.Q s.rows (oppositeSector σ) := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq
  have hrows := graft_sectorRows_opp s q σ ids hidsnd hlen hnodup hids
  unfold sectorRows at hrows
  unfold sectorRank
  rw [hrows, graftState_Q', List.map_map]
  have hmaps : ((s.rows.filter (fun r => r.sector = oppositeSector σ)).map
      (rowBitmask (s.Q.filter (fun x => x ≠ q)) ∘ graftShorten q σ)) =
      ((s.rows.filter (fun r => r.sector = oppositeSector σ)).map (rowBitmask s.Q)).map
        (deleteBit i) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro r hr
    have hrσ : r.sector = oppositeSector σ := by simpa using (List.mem_filter.mp hr).2
    exact rowBitmask_filter_of_supportMinus s.Q hQ q i hi r _
      (graftShorten_supportMinus_of_opp q σ r hrσ)
  rw [hmaps]
  exact rankBitmasks_map_le _ (deleteBit_xorLinear i) _

/-! ### The theorem -/

/-- Well-formedness is preserved by the graft update under the transition's
    premises (§4.12). The opposite-sector guard and the coverage premise of
    `Eval.graft` are not needed. -/
theorem wf_graftState (s : CodeState) (q : Nat) (σ : Sector) (ids : List Nat)
    (hwf : EncodingWellFormed s)
    (hq : q ∈ s.Q) (htouch : touchingRows s σ q ≠ [])
    (hlen : ids.length = (touchingRows s σ q).length) (hnodup : ids.Nodup)
    (hids : ∀ id ∈ ids, id ∈ (touchingRows s σ q).map Row.id)
    (hk : stateK (graftState s q σ ids) = stateK s) :
    EncodingWellFormed (graftState s q σ ids) := by
  have hfit : RanksFit s := ranksFit_of_wf s hwf
  have hsupQ := supports_subset_of_wf hwf
  have hidused := ids_subset_used_of_wf hwf
  obtain ⟨hQ, hidsnd, hused, hsup, hnd, hsort, hI1, hI2⟩ := hwf
  have hiff := graft_ids_iff s q σ ids hidsnd hlen hnodup hids
  have htQnd : (graftState s q σ ids).Q.Nodup := by
    rw [graftState_Q']
    exact hQ.sublist List.filter_sublist
  -- every kept row is an input row with `q` removed from its support
  have hnonchain : ∀ r ∈ graftNonChain s ids,
      SupportMinus q (graftShorten q σ r).support r.support ∧ r ∈ s.rows := by
    intro r hr
    obtain ⟨hrs, hrid⟩ := mem_graftNonChain hr
    refine ⟨?_, hrs⟩
    rcases sector_eq_or_opp r.sector σ with hs | hs
    · rw [graftShorten_eq_of_same q σ r hs]
      apply supportMinus_self
      rw [Bool.eq_false_iff]
      intro hc
      exact hrid ((hiff r hrs).mpr ⟨hs, hc⟩)
    · exact graftShorten_supportMinus_of_opp q σ r hs
  -- every minted row is the adjacent sum of two chain rows, both touching `q`
  have hminted : ∀ u ∈ graftMintedRows s q σ ids, ∃ L R id,
      L ∈ s.rows ∧ L.sector = σ ∧ L.support.contains q = true ∧
      R ∈ s.rows ∧ R.sector = σ ∧ R.support.contains q = true ∧
      id ∈ mintFresh s.used (ids.length - 1) ∧ u = graftMintedRow s q σ ((L, R), id) := by
    intro u hu
    obtain ⟨L, R, id, hL, hR, hid, rfl⟩ := mem_graftMintedRows hu
    obtain ⟨hLs, hLid⟩ := mem_graftChain hL
    obtain ⟨hRs, hRid⟩ := mem_graftChain hR
    have hL' := (hiff L hLs).mp hLid
    have hR' := (hiff R hRs).mp hRid
    exact ⟨L, R, id, hLs, hL'.1, hL'.2, hRs, hR'.1, hR'.2, hid, rfl⟩
  -- identifiers
  have hidsmap : (graftState s q σ ids).rows.map Row.id =
      (graftNonChain s ids).map Row.id ++ (graftMintedRows s q σ ids).map Row.id := by
    rw [graftState_rows, List.map_append, List.map_map]
    congr 1
    apply List.map_congr_left
    intro r _
    exact graftShorten_id q σ r
  have hidsnd' : ((graftState s q σ ids).rows.map Row.id).Nodup := by
    rw [hidsmap, List.nodup_append]
    refine ⟨hidsnd.sublist ((graftNonChain_sublist s ids).map Row.id),
      (mintFresh_nodup _ _).sublist (graftMintedRows_ids_sublist s q σ ids), ?_⟩
    intro a ha b hb heq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
    have hau : r.id ∈ s.used := hidused r (mem_graftNonChain hr).1
    have hb' : b ∈ mintFresh s.used (ids.length - 1) :=
      (graftMintedRows_ids_sublist s q σ ids).subset hb
    exact mintFresh_not_mem _ _ b hb' (heq ▸ hau)
  -- supports
  have hsupnd : ∀ u ∈ (graftState s q σ ids).rows, u.support.Nodup := by
    intro u hu
    rcases mem_graftState_rows hu with ⟨r, hr, rfl⟩ | hu
    · have hrnd : r.support.Nodup := by
        simpa using List.all_eq_true.mp hnd r (mem_graftNonChain hr).1
      rcases graftShorten_support_cases q σ r with h | h <;> rw [h]
      · exact hrnd.sublist List.filter_sublist
      · exact hrnd
    · obtain ⟨L, R, id, _, _, _, _, _, _, _, rfl⟩ := hminted u hu
      rw [graftMintedRow_support, (sortNat_perm _).nodup_iff]
      exact (hQ.sublist List.filter_sublist).sublist List.filter_sublist
  refine ⟨htQnd, hidsnd', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- identifiers are in `used`
    rw [List.all_eq_true]
    intro x hx
    rw [hidsmap] at hx
    rw [graftState_used, List.contains_iff_mem]
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
      exact List.mem_append_left _ (hidused r (mem_graftNonChain hr).1)
    · exact List.mem_append_right _ ((graftMintedRows_ids_sublist s q σ ids).subset hx)
  · -- supports inside the namespace
    rw [List.all_eq_true]
    intro u hu
    rw [List.all_eq_true]
    intro x hx
    rw [List.contains_iff_mem, graftState_Q', List.mem_filter]
    rcases mem_graftState_rows hu with ⟨r, hr, rfl⟩ | hu
    · obtain ⟨hsm, hrs⟩ := hnonchain r hr
      have hxq : x ≠ q := by
        intro hxq
        rw [hxq] at hx
        exact (Bool.eq_false_iff.mp hsm.2) (List.contains_iff_mem.mpr hx)
      have h1 : (graftShorten q σ r).support.contains x = true := List.contains_iff_mem.mpr hx
      rw [hsm.1 x hxq] at h1
      exact ⟨hsupQ r hrs x (List.contains_iff_mem.mp h1), by simp [hxq]⟩
    · obtain ⟨L, R, id, _, _, _, _, _, _, _, rfl⟩ := hminted u hu
      rw [graftMintedRow_support] at hx
      have hx' := (sortNat_perm _).mem_iff.mp hx
      exact List.mem_filter.mp (List.mem_filter.mp hx').1
  · -- supports have no duplicates
    rw [List.all_eq_true]
    intro u hu
    exact decide_eq_true (hsupnd u hu)
  · -- supports are sorted
    rw [List.all_eq_true]
    intro u hu
    rcases mem_graftState_rows hu with ⟨r, hr, rfl⟩ | hu
    · have hrs : r.support.Pairwise (· ≤ ·) := by
        simpa using List.all_eq_true.mp hsort r (mem_graftNonChain hr).1
      rcases graftShorten_support_cases q σ r with h | h <;> rw [h]
      · exact decide_eq_true (hrs.sublist List.filter_sublist)
      · exact decide_eq_true hrs
    · obtain ⟨L, R, id, _, _, _, _, _, _, _, rfl⟩ := hminted u hu
      rw [graftMintedRow_support]
      exact decide_eq_true (sortNat_sorted _)
  · -- I1
    have core : ∀ u ∈ (graftState s q σ ids).rows, u.sector = σ →
        ∀ w ∈ (graftState s q σ ids).rows, w.sector = oppositeSector σ →
        supportIntersectionSize u.support w.support % 2 = 0 := by
      intro u hu huσ w hw hwσ
      obtain ⟨r', hr', hw'⟩ : ∃ r' ∈ graftNonChain s ids, w = graftShorten q σ r' := by
        rcases mem_graftState_rows hw with h | h
        · exact h
        · exfalso
          obtain ⟨L, R, id, _, _, _, _, _, _, _, rfl⟩ := hminted w h
          exact oppositeSector_ne σ hwσ.symm
      obtain ⟨hsm, hr's⟩ := hnonchain r' hr'
      have hr'σ : r'.sector = oppositeSector σ := by
        rw [hw', graftShorten_sector] at hwσ
        exact hwσ
      -- against a support avoiding `q`, the shortened row counts like the input row
      have hshift : ∀ a : List Nat, a.contains q = false →
          supportIntersectionSize a w.support = supportIntersectionSize a r'.support := by
        intro a ha
        rw [supportIntersectionSize_eq_length_filter, supportIntersectionSize_eq_length_filter]
        congr 1
        apply List.filter_congr
        intro x hx
        have hxq : x ≠ q := by
          intro hxq
          rw [hxq] at hx
          exact (Bool.eq_false_iff.mp ha) (List.contains_iff_mem.mpr hx)
        rw [hw']
        exact hsm.1 x hxq
      -- an input graft-sector row is orthogonal to `r'`
      have hpar : ∀ r ∈ s.rows, r.sector = σ →
          supportIntersectionSize r.support r'.support % 2 = 0 := by
        intro r hr hrσ
        have hrnd : r.support.Nodup := by simpa using List.all_eq_true.mp hnd r hr
        have hr'nd : r'.support.Nodup := by simpa using List.all_eq_true.mp hnd r' hr's
        cases σ with
        | X => exact hI1 r r' hr hr's hrσ hr'σ
        | Z =>
          rw [supportIntersectionSize_comm _ _ hrnd hr'nd]
          exact hI1 r' r hr's hr hr'σ hrσ
      rcases mem_graftState_rows hu with ⟨r, hr, rfl⟩ | hu
      · obtain ⟨hrs, hrid⟩ := mem_graftNonChain hr
        rw [graftShorten_sector] at huσ
        have hrq : r.support.contains q = false := by
          rw [Bool.eq_false_iff]
          intro hc
          exact hrid ((hiff r hrs).mpr ⟨huσ, hc⟩)
        rw [graftShorten_eq_of_same q σ r huσ, hshift r.support hrq]
        exact hpar r hrs huσ
      · obtain ⟨L, R, id, hLs, hLσ, hLq, hRs, hRσ, hRq, _, rfl⟩ := hminted u hu
        rw [graftMintedRow_support]
        have hLnd : L.support.Nodup := by simpa using List.all_eq_true.mp hnd L hLs
        have hRnd : R.support.Nodup := by simpa using List.all_eq_true.mp hnd R hRs
        have hLQ : ∀ x ∈ L.support, x ∈ s.Q := hsupQ L hLs
        have hRQ : ∀ x ∈ R.support, x ∈ s.Q := hsupQ R hRs
        have hsupp_q : (sortNat ((s.Q.filter (fun y => y ≠ q)).filter
            (fun y => L.support.contains y ≠ R.support.contains y))).contains q = false := by
          rw [Bool.eq_false_iff]
          intro hc
          have h1 := (sortNat_perm _).mem_iff.mp (List.contains_iff_mem.mp hc)
          have h2 := (List.mem_filter.mp (List.mem_filter.mp h1).1).2
          simp at h2
        rw [hshift _ hsupp_q, supportIntersectionSize_perm_left (sortNat_perm _),
          supportIntersectionSize_eq_length_filter, List.filter_filter, List.filter_filter]
        show (s.Q.filter (fun x => (r'.support.contains x &&
            decide (L.support.contains x ≠ R.support.contains x)) && decide (x ≠ q))).length % 2 = 0
        have hcongr : s.Q.filter (fun x => (r'.support.contains x &&
            decide (L.support.contains x ≠ R.support.contains x)) && decide (x ≠ q)) =
            s.Q.filter (fun x => decide (L.support.contains x ≠ R.support.contains x) &&
              r'.support.contains x) := by
          apply List.filter_congr
          intro x _
          by_cases hxq : x = q
          · rw [hxq]
            simp [List.contains_iff_mem.mp hLq, List.contains_iff_mem.mp hRq]
          · simp [hxq, Bool.and_comm]
        rw [hcongr, length_filter_bne_parity,
          ← supportIntersectionSize_eq_count s.Q L.support r'.support hQ hLnd hLQ,
          ← supportIntersectionSize_eq_count s.Q R.support r'.support hQ hRnd hRQ]
        have h1 := hpar L hLs hLσ
        have h2 := hpar R hRs hRσ
        omega
    intro rX rZ hX hZ hsX hsZ
    cases σ with
    | X => exact core rX hX hsX rZ hZ hsZ
    | Z =>
      rw [supportIntersectionSize_comm _ _ (hsupnd rX hX) (hsupnd rZ hZ)]
      exact core rZ hZ hsZ rX hX hsX
  · -- I2, by counting ranks
    have hrs : ∀ τ, sectorRank s.Q s.rows τ = (sectorRows s τ).length :=
      fun τ => sectorRank_eq_length_of_I2 s hQ hidsnd hI2 τ
    have hn : (graftState s q σ ids).Q.length + 1 = s.Q.length := by
      rw [graftState_Q']
      exact length_filter_ne_succ q s.Q hQ hq
    have hopp_le := graft_sectorRank_opp_le s q σ ids hQ hq hidsnd hlen hnodup hids
    have hopp_len : (sectorRows (graftState s q σ ids) (oppositeSector σ)).length =
        (sectorRows s (oppositeSector σ)).length := by
      rw [graft_sectorRows_opp s q σ ids hidsnd hlen hnodup hids, List.length_map]
    have hsame_le : sectorRank (graftState s q σ ids).Q (graftState s q σ ids).rows σ ≤
        (sectorRows (graftState s q σ ids) σ).length :=
      sectorRank_le_length _ _ _
    have hsame_len := graft_sectorRows_same_length_le s q σ ids hidsnd htouch hlen hnodup hids
    have hsX := hrs Sector.X
    have hsZ := hrs Sector.Z
    unfold RanksFit at hfit
    unfold stateK at hk
    apply i2_of_full_rank _ htQnd hidsnd'
    intro τ
    cases σ <;> cases τ <;> simp only [oppositeSector] at * <;> omega

/-- The graft instance of §4.7 at an evaluation: output well-formedness from
    input well-formedness. -/
theorem wf_graft_of_eval {q : Nat} {σ : Sector} {ids : List Nat} {s t : CodeState}
    (h : Eval (Command.graft q σ ids) s t) (hwf : EncodingWellFormed s) :
    EncodingWellFormed t := by
  cases h with
  | graft hq _ htouch hlen hnodup hids _ hk hst =>
    rw [hst]
    exact wf_graftState s q σ ids hwf hq htouch hlen hnodup hids hk

/-- Well-formedness is preserved by every evaluation of every command: skip
    trivially, deletion, addition, and the graft by their lemmas, sequencing by
    composition, and the Gate 6 cells by the premise their transitions carry.
    This is `wf_of_eval` without the `GraftFree` restriction. -/
theorem wf_of_eval_all {m : Command} {s t : CodeState} (h : Eval m s t)
    (hwf : EncodingWellFormed s) : EncodingWellFormed t := by
  induction h with
  | skip _ => exact hwf
  | seq _ _ ih1 ih2 => exact ih2 (ih1 hwf)
  | delete _ _ heq =>
    rw [heq]
    exact wf_deleteState _ _ hwf
  | add hsub hnodup hsorted hcomm hspan heq =>
    rw [heq]
    exact wf_addState _ _ _ hwf hsub hnodup hsorted hcomm hspan
  | graft hq _ htouch hlen hnodup hids _ hk hst =>
    rw [hst]
    exact wf_graftState _ _ _ _ hwf hq htouch hlen hnodup hids hk
  | rebase _ _ _ hwf' => exact hwf'
  | hadamard _ _ hwf' => exact hwf'
  | peel _ _ _ _ _ hwf' => exact hwf'
  | puncture _ _ hwf' => exact hwf'
  | extend _ _ hwf' => exact hwf'

end CodeCalculus
