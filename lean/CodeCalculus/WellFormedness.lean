import CodeCalculus.Eval
import CodeCalculus.KernelObligations
import CodeCalculus.MaskRank
import CodeCalculus.MixSupport

namespace CodeCalculus

/-!
# Well-formedness preservation and rank decrease ()

Two groups of per-primitive lemmas that `Soundness.lean` discharges its
instantiation rows against.

1. Well-formedness preservation (`OBL-WELL-FORMEDNESS-PRESERVATION`,
   `spec/OPERATIONAL_SEMANTICS.md` §4.7): `EncodingWellFormed` is preserved by
   `deleteState` (for any identifier) and by `addState` under the
   `C-ADD-CHECK` premises (`wf_deleteState`, `wf_addState`). `wf_of_eval`
   lifts these to every evaluation of a graft-free command: skip and
   sequencing structurally, deletion and addition through the lemmas, the
   Gate 6 cells through the well-formedness premise their transitions carry.
   The graft is excluded from this lift: its well-formedness preservation is
   the content of §4.12 and is mechanized in `GraftWellFormedness.lean`
   (`wf_graft_of_eval`), where `wf_of_eval_all` lifts preservation to every
   command. The `C-DIRECT-SUM` instance is a state expression, not a command
   step, and is the subject of .

2. Rank decrease: deleting an independent generator lowers its sector's rank
   by exactly one and leaves the other sector's rank unchanged
   (`sectorRank_deleteState_same`, `sectorRank_deleteState_other`); adding an
   independent row raises its sector's rank by exactly one
   (`sectorRank_addState_same`, `sectorRank_addState_other`). The `k` cells
   follow (`stateK_deleteState`, `stateK_addState`) under `RanksFit`, the
   dimension bound `rank X + rank Z ≤ |Q|`, which keeps the truncated
   subtraction in `stateK` honest. That bound is a consequence of I1 and I2
   (`X ⊆ Z^⊥` over `F₂`), derived in `RanksFit.lean` (`ranksFit_of_wf`); the
   `k` rows of `Soundness.lean` obtain it from the context's
   well-formedness.

The independence premises of `Eval.delete` and `Eval.add` are stated over
`rowVector` (`List Bool` over `Q`) while `stateK` reads `rankBitmasks` over
`rowBitmask` (`Nat`). `inSpanRows_iff_inSpanMasks` is the bridge, bit by bit,
for a duplicate-free `Q`.
-/

/-! ### Vector algebra over `xorVec` and `combineRows` -/

theorem xorVec_comm (a b : List Bool) : xorVec a b = xorVec b a := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih =>
    cases b with
    | nil => rfl
    | cons y ys =>
      simp only [xorVec]
      rw [ih ys]
      cases x <;> cases y <;> rfl

theorem xorVec_cancel_left (v w : List Bool) (h : v.length = w.length) :
    xorVec v (xorVec v w) = w := by
  induction v generalizing w with
  | nil =>
    cases w with
    | nil => rfl
    | cons _ _ => simp at h
  | cons x xs ih =>
    cases w with
    | nil => simp at h
    | cons y ys =>
      simp only [xorVec, List.length_cons] at *
      rw [ih ys (by omega)]
      cases x <;> cases y <;> rfl

theorem xorVec_cancel_right (w v : List Bool) (h : w.length = v.length) :
    xorVec (xorVec w v) v = w := by
  rw [xorVec_comm (xorVec w v) v, xorVec_comm w v]
  exact xorVec_cancel_left v w h.symm

theorem xorVec_assoc (a b c : List Bool) (hab : a.length = b.length)
    (hbc : b.length = c.length) :
    xorVec (xorVec a b) c = xorVec a (xorVec b c) := by
  induction a generalizing b c with
  | nil =>
    cases b with
    | nil =>
      cases c with
      | nil => rfl
      | cons _ _ => simp at hbc
    | cons _ _ => simp at hab
  | cons x xs ih =>
    cases b with
    | nil => simp at hab
    | cons y ys =>
      cases c with
      | nil => simp at hbc
      | cons z zs =>
        simp only [xorVec, List.length_cons] at *
        rw [ih ys zs (by omega) (by omega)]
        cases x <;> cases y <;> cases z <;> rfl

theorem xorVec_left_comm (a b c : List Bool) (hab : a.length = b.length)
    (hbc : b.length = c.length) :
    xorVec a (xorVec b c) = xorVec b (xorVec a c) := by
  induction a generalizing b c with
  | nil =>
    cases b with
    | nil =>
      cases c with
      | nil => rfl
      | cons _ _ => simp at hbc
    | cons _ _ => simp at hab
  | cons x xs ih =>
    cases b with
    | nil => simp at hab
    | cons y ys =>
      cases c with
      | nil => simp at hbc
      | cons z zs =>
        simp only [xorVec, List.length_cons] at *
        rw [ih ys zs (by omega) (by omega)]
        cases x <;> cases y <;> cases z <;> rfl

theorem xorVec_replicate_false_right (n : Nat) (a : List Bool) (h : a.length = n) :
    xorVec a (List.replicate n false) = a := by
  rw [xorVec_comm]
  exact xorVec_replicate_false_left n a h

theorem rowVectors_length (Q : List Nat) (rows : List Row) :
    ∀ v ∈ rows.map (rowVector Q), v.length = Q.length := by
  intro v hv
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hv
  exact rowVector_length Q r

/-- A combination over an append is the XOR of the two combinations. -/
theorem combineRows_append (n : Nat) (vs1 vs2 : List (List Bool)) (cs1 cs2 : List Bool)
    (hv1 : ∀ v ∈ vs1, v.length = n) (hv2 : ∀ v ∈ vs2, v.length = n)
    (hcs1 : cs1.length = vs1.length) (_hcs2 : cs2.length = vs2.length) :
    combineRows n (vs1 ++ vs2) (cs1 ++ cs2) =
      xorVec (combineRows n vs1 cs1) (combineRows n vs2 cs2) := by
  induction vs1 generalizing cs1 with
  | nil =>
    cases cs1 with
    | nil =>
      show combineRows n vs2 cs2 = xorVec (List.replicate n false) (combineRows n vs2 cs2)
      rw [xorVec_replicate_false_left n _ (combineRows_length n vs2 cs2 hv2)]
    | cons _ _ => simp at hcs1
  | cons v vs1 ih =>
    cases cs1 with
    | nil => simp at hcs1
    | cons c cs1 =>
      have hv0 := hv1 v (List.mem_cons.mpr (Or.inl rfl))
      have hv1' : ∀ v' ∈ vs1, v'.length = n :=
        fun v' h => hv1 v' (List.mem_cons.mpr (Or.inr h))
      have hcs1' : cs1.length = vs1.length := by
        simp only [List.length_cons] at hcs1
        omega
      cases c with
      | true =>
        show xorVec v (combineRows n (vs1 ++ vs2) (cs1 ++ cs2)) =
          xorVec (xorVec v (combineRows n vs1 cs1)) (combineRows n vs2 cs2)
        rw [ih cs1 hv1' hcs1',
          xorVec_assoc v _ _ (by rw [hv0, combineRows_length n vs1 cs1 hv1'])
            (by rw [combineRows_length n vs1 cs1 hv1', combineRows_length n vs2 cs2 hv2])]
      | false =>
        show combineRows n (vs1 ++ vs2) (cs1 ++ cs2) =
          xorVec (combineRows n vs1 cs1) (combineRows n vs2 cs2)
        exact ih cs1 hv1' hcs1'

/-- Coefficientwise XOR of two combinations. -/
theorem combineRows_zipWith_bne (n : Nat) (vs : List (List Bool))
    (hv : ∀ v ∈ vs, v.length = n) :
    ∀ (ca cb : List Bool), ca.length = vs.length → cb.length = vs.length →
      combineRows n vs (List.zipWith (· != ·) ca cb) =
        xorVec (combineRows n vs ca) (combineRows n vs cb) := by
  induction vs with
  | nil =>
    intro ca cb hca hcb
    cases ca with
    | nil =>
      cases cb with
      | nil =>
        show List.replicate n false =
          xorVec (List.replicate n false) (List.replicate n false)
        rw [xorVec_replicate_false_left n _ (by simp)]
      | cons _ _ => simp at hcb
    | cons _ _ => simp at hca
  | cons v vs ih =>
    intro ca cb hca hcb
    cases ca with
    | nil => simp at hca
    | cons a ca =>
      cases cb with
      | nil => simp at hcb
      | cons b cb =>
        have hv0 := hv v (List.mem_cons.mpr (Or.inl rfl))
        have hv' : ∀ v' ∈ vs, v'.length = n :=
          fun v' h => hv v' (List.mem_cons.mpr (Or.inr h))
        have hA : (combineRows n vs ca).length = n := combineRows_length n vs ca hv'
        have hB : (combineRows n vs cb).length = n := combineRows_length n vs cb hv'
        have ih' := ih hv' ca cb (by simpa using hca) (by simpa using hcb)
        cases a <;> cases b
        · show combineRows n vs (List.zipWith (· != ·) ca cb) =
            xorVec (combineRows n vs ca) (combineRows n vs cb)
          exact ih'
        · show xorVec v (combineRows n vs (List.zipWith (· != ·) ca cb)) =
            xorVec (combineRows n vs ca) (xorVec v (combineRows n vs cb))
          rw [ih', xorVec_left_comm v _ _ (by rw [hv0, hA]) (by rw [hA, hB])]
        · show xorVec v (combineRows n vs (List.zipWith (· != ·) ca cb)) =
            xorVec (xorVec v (combineRows n vs ca)) (combineRows n vs cb)
          rw [ih', xorVec_assoc v _ _ (by rw [hv0, hA]) (by rw [hA, hB])]
        · show combineRows n vs (List.zipWith (· != ·) ca cb) =
            xorVec (xorVec v (combineRows n vs ca)) (xorVec v (combineRows n vs cb))
          rw [ih', xorVec_assoc v _ _ (by rw [hv0, hA]) (by rw [hA, xorVec_length _ _ (by rw [hv0, hB]), hv0]),
            xorVec_left_comm _ v _ (by rw [hA, hv0]) (by rw [hv0, hB]),
            xorVec_cancel_left v _ (by rw [hv0, xorVec_length _ _ (by rw [hA, hB]), hA])]

/-! ### Span lemmas over `inSpanRows` -/

theorem inSpanRows_of_sublist (Q : List Nat) {l₁ l₂ : List Row} (h : l₁.Sublist l₂) :
    ∀ t : List Bool, inSpanRows Q l₁ t → inSpanRows Q l₂ t := by
  induction h with
  | slnil => intro t hs; exact hs
  | cons a h ih =>
    intro t hs
    obtain ⟨cs, hlen, heq⟩ := ih t hs
    exact ⟨false :: cs, by simp [hlen], heq⟩
  | cons_cons a h ih =>
    intro t hs
    obtain ⟨cs, hlen, heq⟩ := hs
    cases cs with
    | nil => simp at hlen
    | cons c cs =>
      obtain ⟨cs', hlen', heq'⟩ := ih _ ⟨cs, by simpa using hlen, rfl⟩
      refine ⟨c :: cs', by simp [hlen'], ?_⟩
      cases c
      · simp only [List.map_cons, combineRows] at heq ⊢
        rw [heq']
        exact heq
      · simp only [List.map_cons, combineRows] at heq ⊢
        rw [heq']
        exact heq

theorem inSpanRows_of_mem (Q : List Nat) {rows : List Row} {row : Row} (h : row ∈ rows) :
    inSpanRows Q rows (rowVector Q row) := by
  induction rows with
  | nil => cases h
  | cons r rs ih =>
    rcases List.mem_cons.mp h with hr | h'
    · subst hr
      refine ⟨true :: List.replicate rs.length false, by simp, ?_⟩
      show xorVec (rowVector Q row) (combineRows Q.length (rs.map (rowVector Q))
        (List.replicate rs.length false)) = rowVector Q row
      rw [show List.replicate rs.length false =
          List.replicate (rs.map (rowVector Q)).length false by rw [List.length_map],
        combineRows_zero_coeffs]
      exact xorVec_replicate_false_right Q.length _ (rowVector_length Q row)
    · obtain ⟨cs, hlen, heq⟩ := ih h'
      refine ⟨false :: cs, by simp [hlen], ?_⟩
      show combineRows Q.length (rs.map (rowVector Q)) cs = rowVector Q row
      exact heq

theorem inSpanRows_xor (Q : List Nat) (rows : List Row) {a b : List Bool}
    (ha : inSpanRows Q rows a) (hb : inSpanRows Q rows b) :
    inSpanRows Q rows (xorVec a b) := by
  obtain ⟨ca, hca, heqa⟩ := ha
  obtain ⟨cb, hcb, heqb⟩ := hb
  refine ⟨List.zipWith (· != ·) ca cb, ?_, ?_⟩
  · rw [List.length_zipWith, hca, hcb, Nat.min_self]
  · rw [combineRows_zipWith_bne Q.length _ (rowVectors_length Q rows) ca cb
      (by rw [hca, List.length_map]) (by rw [hcb, List.length_map]), heqa, heqb]

/-- Span membership over a list with one appended row: either the target is in
    the span of the rest, or the target XOR the appended row is. -/
theorem inSpanRows_append_singleton_iff (Q : List Nat) (rows : List Row) (r : Row)
    (t : List Bool) (ht : t.length = Q.length) :
    inSpanRows Q (rows ++ [r]) t ↔
      inSpanRows Q rows t ∨ inSpanRows Q rows (xorVec t (rowVector Q r)) := by
  have hlenC : ∀ cs, (combineRows Q.length (rows.map (rowVector Q)) cs).length = Q.length :=
    fun cs => combineRows_length _ _ _ (rowVectors_length Q rows)
  constructor
  · rintro ⟨cs, hlen, heq⟩
    rw [List.length_append, List.length_singleton] at hlen
    have hlt : (cs.take rows.length).length = rows.length := by
      rw [List.length_take]
      omega
    have hld : (cs.drop rows.length).length = 1 := by
      rw [List.length_drop]
      omega
    obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp hld
    rw [← List.take_append_drop rows.length cs, hb, List.map_append,
      combineRows_append Q.length _ _ _ _ (rowVectors_length Q rows) (rowVectors_length Q [r])
        (by rw [hlt, List.length_map]) (by simp)] at heq
    cases b with
    | false =>
      refine Or.inl ⟨cs.take rows.length, hlt, ?_⟩
      show combineRows Q.length (rows.map (rowVector Q)) (cs.take rows.length) = t
      rw [← heq]
      show _ = xorVec _ (List.replicate Q.length false)
      rw [xorVec_replicate_false_right Q.length _ (hlenC _)]
    | true =>
      refine Or.inr ⟨cs.take rows.length, hlt, ?_⟩
      show combineRows Q.length (rows.map (rowVector Q)) (cs.take rows.length) =
        xorVec t (rowVector Q r)
      rw [← heq]
      show _ = xorVec (xorVec _ (xorVec (rowVector Q r) (List.replicate Q.length false)))
        (rowVector Q r)
      rw [xorVec_replicate_false_right Q.length _ (rowVector_length Q r),
        xorVec_cancel_right _ _ (by rw [hlenC, rowVector_length])]
  · rintro (⟨cs, hlen, heq⟩ | ⟨cs, hlen, heq⟩)
    · refine ⟨cs ++ [false], by simp [hlen], ?_⟩
      rw [List.map_append, combineRows_append Q.length _ _ _ _ (rowVectors_length Q rows)
        (rowVectors_length Q [r]) (by rw [hlen, List.length_map]) (by simp), heq]
      show xorVec t (List.replicate Q.length false) = t
      exact xorVec_replicate_false_right Q.length t ht
    · refine ⟨cs ++ [true], by simp [hlen], ?_⟩
      rw [List.map_append, combineRows_append Q.length _ _ _ _ (rowVectors_length Q rows)
        (rowVectors_length Q [r]) (by rw [hlen, List.length_map]) (by simp), heq]
      show xorVec (xorVec t (rowVector Q r)) (xorVec (rowVector Q r) (List.replicate Q.length false)) = t
      rw [xorVec_replicate_false_right Q.length _ (rowVector_length Q r)]
      exact xorVec_cancel_right t _ (by rw [ht, rowVector_length])


/-! ### The vector-to-bitmask bridge -/

/-- Bit `i` of a Boolean vector, `false` past its end. -/
def bitAt : List Bool → Nat → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: bs, i + 1 => bitAt bs i

theorem bitAt_xorVec (a b : List Bool) (h : a.length = b.length) (i : Nat) :
    bitAt (xorVec a b) i = (bitAt a i != bitAt b i) := by
  induction a generalizing b i with
  | nil =>
    cases b with
    | nil => cases i <;> rfl
    | cons _ _ => simp at h
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      cases i with
      | zero => rfl
      | succ i =>
        show bitAt (xorVec xs ys) i = (bitAt xs i != bitAt ys i)
        exact ih ys (by simpa using h) i

theorem bitAt_replicate_false (n i : Nat) : bitAt (List.replicate n false) i = false := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i =>
      show bitAt (List.replicate n false) i = false
      exact ih i

theorem ext_bitAt (a b : List Bool) (hlen : a.length = b.length)
    (h : ∀ i, bitAt a i = bitAt b i) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases b with
    | nil => simp at hlen
    | cons y ys =>
      have hx : x = y := h 0
      have hrest : xs = ys := ih ys (by simpa using hlen) (fun i => h (i + 1))
      rw [hx, hrest]

/-- The bit a qubit list position contributes for a support. -/
def qubitBit (Q sup : List Nat) (i : Nat) : Bool :=
  match Q[i]? with
  | some q => sup.contains q
  | none => false

theorem bitAt_rowVector (Q : List Nat) (r : Row) (i : Nat) :
    bitAt (rowVector Q r) i = qubitBit Q r.support i := by
  induction Q generalizing i with
  | nil => simp [rowVector, bitAt, qubitBit]
  | cons q qs ih =>
    cases i with
    | zero => simp [rowVector, bitAt, qubitBit]
    | succ i =>
      show bitAt (rowVector qs r) i = qubitBit (q :: qs) r.support (i + 1)
      rw [ih i]
      simp [qubitBit]

/-- `indexOfQubit` inverts positional lookup on a duplicate-free list. -/
theorem indexOfQubit_of_getElem? (Q : List Nat) (hnd : Q.Nodup) (q i : Nat)
    (h : Q[i]? = some q) : indexOfQubit Q q = some i := by
  induction Q generalizing i with
  | nil => simp at h
  | cons q' qs ih =>
    have hnd' := List.nodup_cons.mp hnd
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [indexOfQubit]
    | succ i =>
      rw [List.getElem?_cons_succ] at h
      have hmem : q ∈ qs := List.mem_of_getElem? h
      have hne : q' ≠ q := by
        intro heq
        apply hnd'.1
        rw [heq]
        exact hmem
      simp only [indexOfQubit, ite_eq_right hne, ih hnd'.2 i h, Option.map_some]

theorem testBit_rowBitmask (Q : List Nat) (hnd : Q.Nodup) (r : Row) (i : Nat) :
    (rowBitmask Q r).testBit i = qubitBit Q r.support i := by
  rw [rowBitmask_eq_maskOfSupport]
  unfold qubitBit
  cases hQi : Q[i]? with
  | none =>
    show (maskOfSupport Q r.support).testBit i = false
    apply Bool.eq_false_iff.mpr
    intro ht
    obtain ⟨q, _, hidx⟩ := (testBit_maskOfSupport_iff Q r.support i).mp ht
    have h := indexOfQubit_some_imp Q q i hidx
    rw [hQi] at h
    cases h
  | some q =>
    show (maskOfSupport Q r.support).testBit i = r.support.contains q
    cases hc : r.support.contains q with
    | true =>
      rw [testBit_maskOfSupport_iff]
      exact ⟨q, List.contains_iff_mem.mp hc, indexOfQubit_of_getElem? Q hnd q i hQi⟩
    | false =>
      apply Bool.eq_false_iff.mpr
      intro ht
      obtain ⟨q', hq', hidx⟩ := (testBit_maskOfSupport_iff Q r.support i).mp ht
      have h1 := indexOfQubit_some_imp Q q' i hidx
      rw [hQi] at h1
      have hqq : q = q' := Option.some.inj h1
      subst hqq
      have h2 := List.contains_iff_mem.mpr hq'
      rw [hc] at h2
      exact Bool.false_ne_true h2

/-- Coefficient translation between the two span notions. -/
def natOfBool : Bool → Nat
  | true => 1
  | false => 0

theorem bitAt_combineRows (Q : List Nat) (hnd : Q.Nodup) (rows : List Row) (cs : List Bool)
    (hlen : cs.length = rows.length) (i : Nat) :
    bitAt (combineRows Q.length (rows.map (rowVector Q)) cs) i =
      (combineMasks (rows.map (rowBitmask Q)) (cs.map natOfBool)).testBit i := by
  induction rows generalizing cs with
  | nil =>
    cases cs with
    | nil =>
      show bitAt (List.replicate Q.length false) i = (combineMasks [] []).testBit i
      rw [bitAt_replicate_false, combineMasks_nil, Nat.zero_testBit]
    | cons _ _ => simp at hlen
  | cons r rs ih =>
    cases cs with
    | nil => simp at hlen
    | cons c cs =>
      have hlen' : cs.length = rs.length := by simpa using hlen
      cases c with
      | true =>
        show bitAt (xorVec (rowVector Q r) (combineRows Q.length (rs.map (rowVector Q)) cs)) i =
          (combineMasks (rowBitmask Q r :: rs.map (rowBitmask Q)) (1 :: cs.map natOfBool)).testBit i
        rw [combineMasks_cons, ite_eq_left_of_eq_true _ _ (eq_self 1), Nat.testBit_xor,
          bitAt_xorVec _ _ (by rw [rowVector_length, combineRows_length _ _ _ (rowVectors_length Q rs)]),
          bitAt_rowVector, ih cs hlen', testBit_rowBitmask Q hnd]
      | false =>
        show bitAt (combineRows Q.length (rs.map (rowVector Q)) cs) i =
          (combineMasks (rowBitmask Q r :: rs.map (rowBitmask Q)) (0 :: cs.map natOfBool)).testBit i
        rw [combineMasks_cons, ite_eq_right_of_eq_false _ _ (by decide), Nat.zero_xor, ih cs hlen']

/-- The vector-level span premise of `Eval.delete` and `Eval.add` is the
    bitmask-level one, for a duplicate-free qubit list. -/
theorem inSpanRows_iff_inSpanMasks (Q : List Nat) (hnd : Q.Nodup) (rows : List Row) (row : Row) :
    inSpanRows Q rows (rowVector Q row) ↔
      inSpanMasks (rows.map (rowBitmask Q)) (rowBitmask Q row) := by
  constructor
  · rintro ⟨cs, hlen, heq⟩
    refine ⟨cs.map natOfBool, by rw [List.length_map, List.length_map]; exact hlen, ?_, ?_⟩
    · intro c hc
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hc
      cases b
      · exact Or.inl rfl
      · exact Or.inr rfl
    · apply Nat.eq_of_testBit_eq
      intro i
      rw [← bitAt_combineRows Q hnd rows cs hlen i, heq, bitAt_rowVector, testBit_rowBitmask Q hnd]
  · rintro ⟨cs, hlen, h01, heq⟩
    rw [List.length_map] at hlen
    have hcs : (cs.map (fun c => decide (c = 1))).map natOfBool = cs := by
      rw [List.map_map]
      have hid : ∀ c ∈ cs, (natOfBool ∘ fun c => decide (c = 1)) c = id c := by
        intro c hc
        rcases h01 c hc with rfl | rfl <;> rfl
      rw [List.map_congr_left hid, List.map_id]
    refine ⟨cs.map (fun c => decide (c = 1)), by rw [List.length_map]; exact hlen, ?_⟩
    apply ext_bitAt _ _ (by rw [combineRows_length _ _ _ (rowVectors_length Q rows), rowVector_length])
    intro i
    rw [bitAt_combineRows Q hnd rows _ (by rw [List.length_map]; exact hlen) i, hcs, heq,
      bitAt_rowVector, testBit_rowBitmask Q hnd]

/-! ### Rank decrease -/

theorem rankBitmasks_perm {xs ys : List Nat} (p : xs.Perm ys) :
    rankBitmasks xs = rankBitmasks ys :=
  rankBitmasks_eq_of_span_eq (inSpanMasks_perm p)

/-- Appending a mask outside the span raises the greedy rank by exactly one. -/
theorem rankBitmasks_append_singleton_of_not_mem (xs : List Nat) (v : Nat)
    (h : ¬ inSpanMasks xs v) : rankBitmasks (xs ++ [v]) = rankBitmasks xs + 1 := by
  unfold rankBitmasks
  rw [List.foldl_append]
  show (insertBasis (xs.foldl insertBasis []) v).length = (xs.foldl insertBasis []).length + 1
  have hne : reduceByBasis (xs.foldl insertBasis []) v ≠ 0 := by
    intro h0
    apply h
    obtain ⟨v', hv', heq⟩ := reduceByBasis_sound (xs.foldl insertBasis []) v
    rw [h0] at heq
    rw [xor_eq_zero_cancel heq.symm]
    exact (spanEq_foldl_insertBasis_nil xs v').mp hv'
  simp [insertBasis, hne]

/-- Identifiers determine rows when they are unique. -/
theorem id_inj_of_nodup {rows : List Row} (hnd : (rows.map Row.id).Nodup) {x y : Row}
    (hx : x ∈ rows) (hy : y ∈ rows) (h : x.id = y.id) : x = y := by
  induction rows with
  | nil => cases hx
  | cons z zs ih =>
    rw [List.map_cons] at hnd
    have hnd' := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hx with hxz | hx'
    · rcases List.mem_cons.mp hy with hyz | hy'
      · rw [hxz, hyz]
      · exfalso
        apply hnd'.1
        rw [← hxz, h]
        exact List.mem_map.mpr ⟨y, hy', rfl⟩
    · rcases List.mem_cons.mp hy with hyz | hy'
      · exfalso
        apply hnd'.1
        rw [← hyz, ← h]
        exact List.mem_map.mpr ⟨x, hx', rfl⟩
      · exact ih hnd'.2 hx' hy'

theorem find?_id_of_mem (rows : List Row) (hnd : (rows.map Row.id).Nodup) (row : Row)
    (hmem : row ∈ rows) : rows.find? (fun x => x.id = row.id) = some row := by
  induction rows with
  | nil => cases hmem
  | cons x xs ih =>
    rw [List.map_cons] at hnd
    have hnd' := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hmem with hrx | hmem'
    · rw [hrx, List.find?_cons_of_pos (by simp)]
    · have hne : x.id ≠ row.id := by
        intro heq
        apply hnd'.1
        rw [heq]
        exact List.mem_map.mpr ⟨row, hmem', rfl⟩
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact ih hnd'.2 hmem'

theorem rowById_of_mem (s : CodeState) (hids : (s.rows.map Row.id).Nodup) (row : Row)
    (hmem : row ∈ s.rows) : rowById s row.id = some row :=
  find?_id_of_mem s.rows hids row hmem

/-- `IndependentGenerator` unfolded at a displayed row of a state with unique
    identifiers. -/
theorem independentGenerator_iff (s : CodeState) (hids : (s.rows.map Row.id).Nodup) (row : Row)
    (hmem : row ∈ s.rows) :
    IndependentGenerator row.id s ↔
      ¬ inSpanRows s.Q (s.rows.filter (fun r' => r'.sector = row.sector ∧ r'.id ≠ row.id))
        (rowVector s.Q row) := by
  unfold IndependentGenerator
  rw [rowById_of_mem s hids row hmem]

/-- The one row carrying an identifier, when identifiers are unique. -/
theorem filter_id_eq_singleton (rows : List Row) (hnd : (rows.map Row.id).Nodup) (row : Row)
    (hmem : row ∈ rows) : rows.filter (fun x => x.id = row.id) = [row] := by
  induction rows with
  | nil => cases hmem
  | cons x xs ih =>
    rw [List.map_cons] at hnd
    have hnd' := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hmem with hrx | hmem'
    · subst hrx
      rw [List.filter_cons_of_pos (by simp)]
      have hnil : xs.filter (fun y => y.id = row.id) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy hyid
        apply hnd'.1
        have hyid' : y.id = row.id := by simpa using hyid
        rw [← hyid']
        exact List.mem_map.mpr ⟨y, hy, rfl⟩
      rw [hnil]
    · have hne : x.id ≠ row.id := by
        intro h
        apply hnd'.1
        rw [h]
        exact List.mem_map.mpr ⟨row, hmem', rfl⟩
      rw [List.filter_cons_of_neg (by simpa using hne)]
      exact ih hnd'.2 hmem'

theorem sectorRows_deleteState (s : CodeState) (r : Nat) (σ : Sector) :
    (deleteState s r).rows.filter (fun x => x.sector = σ) =
      s.rows.filter (fun x => x.sector = σ ∧ x.id ≠ r) := by
  show (s.rows.filter (fun x => x.id ≠ r)).filter (fun x => x.sector = σ) = _
  rw [List.filter_filter]
  apply List.filter_congr
  intro x _
  simp

/-- A sector's rows are its peers of a displayed row plus that row, up to order. -/
theorem sectorRows_perm_peers (s : CodeState) (hids : (s.rows.map Row.id).Nodup) (row : Row)
    (hmem : row ∈ s.rows) :
    (s.rows.filter (fun x => x.sector = row.sector)).Perm
      (s.rows.filter (fun x => x.sector = row.sector ∧ x.id ≠ row.id) ++ [row]) := by
  have h := List.filter_append_perm (fun x : Row => decide (x.id ≠ row.id))
    (s.rows.filter (fun x => x.sector = row.sector))
  have h1 : (s.rows.filter (fun x => x.sector = row.sector)).filter
      (fun x => decide (x.id ≠ row.id)) =
      s.rows.filter (fun x => x.sector = row.sector ∧ x.id ≠ row.id) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro x _
    simp [Bool.and_comm]
  have h2 : (s.rows.filter (fun x => x.sector = row.sector)).filter
      (fun x => !decide (x.id ≠ row.id)) = [row] := by
    have hsub : ((s.rows.filter (fun x => x.sector = row.sector)).map Row.id).Sublist
        (s.rows.map Row.id) := List.filter_sublist.map Row.id
    have hnd' := hids.sublist hsub
    have hmem' : row ∈ s.rows.filter (fun x => x.sector = row.sector) :=
      List.mem_filter.mpr ⟨hmem, by simp⟩
    rw [← filter_id_eq_singleton _ hnd' row hmem']
    apply List.filter_congr
    intro x _
    simp
  rw [h1, h2] at h
  exact h.symm

/-- Deleting an independent generator lowers its sector's rank by exactly one. -/
theorem sectorRank_deleteState_same (s : CodeState) (hQ : s.Q.Nodup)
    (hids : (s.rows.map Row.id).Nodup) (row : Row) (hmem : row ∈ s.rows)
    (hind : IndependentGenerator row.id s) :
    sectorRank s.Q (deleteState s row.id).rows row.sector + 1 =
      sectorRank s.Q s.rows row.sector := by
  have hind' := (independentGenerator_iff s hids row hmem).mp hind
  have hmask : ¬ inSpanMasks ((s.rows.filter (fun x => x.sector = row.sector ∧ x.id ≠ row.id)).map
      (rowBitmask s.Q)) (rowBitmask s.Q row) :=
    fun h => hind' ((inSpanRows_iff_inSpanMasks s.Q hQ _ row).mpr h)
  have hperm := sectorRows_perm_peers s hids row hmem
  unfold sectorRank
  rw [sectorRows_deleteState s row.id row.sector, rankBitmasks_perm (hperm.map (rowBitmask s.Q)),
    List.map_append, List.map_singleton]
  exact (rankBitmasks_append_singleton_of_not_mem _ _ hmask).symm

/-- Deleting a row leaves the other sector's rank unchanged. -/
theorem sectorRank_deleteState_other (s : CodeState) (hids : (s.rows.map Row.id).Nodup)
    (row : Row) (hmem : row ∈ s.rows) (σ : Sector) (hσ : σ ≠ row.sector) :
    sectorRank s.Q (deleteState s row.id).rows σ = sectorRank s.Q s.rows σ := by
  unfold sectorRank
  have e : (deleteState s row.id).rows.filter (fun x => x.sector = σ) =
      s.rows.filter (fun x => x.sector = σ) := by
    show (s.rows.filter (fun x => x.id ≠ row.id)).filter (fun x => x.sector = σ) = _
    rw [List.filter_filter]
    apply List.filter_congr
    intro x hx
    by_cases hs : x.sector = σ
    · have hne : x.id ≠ row.id := by
        intro h
        have hx_eq : x = row := id_inj_of_nodup hids hx hmem h
        rw [hx_eq] at hs
        exact hσ hs.symm
      simp [hs, hne]
    · simp [hs]
  rw [e]

/-- The row minted by `addState`. -/
def addRow (s : CodeState) (sector : Sector) (support : List Nat) : Row :=
  ⟨canonicalMint s.used, sector, support⟩

theorem addState_rows (s : CodeState) (sector : Sector) (support : List Nat) :
    (addState s sector support).rows = s.rows ++ [addRow s sector support] := rfl

/-- Adding an independent row raises its sector's rank by exactly one. -/
theorem sectorRank_addState_same (s : CodeState) (hQ : s.Q.Nodup) (sector : Sector)
    (support : List Nat)
    (hspan : ¬ inSpanRows s.Q (sectorRows s sector) (rowVector s.Q (addRow s sector support))) :
    sectorRank s.Q (addState s sector support).rows sector =
      sectorRank s.Q s.rows sector + 1 := by
  unfold sectorRank
  have e : (addState s sector support).rows.filter (fun x => x.sector = sector) =
      s.rows.filter (fun x => x.sector = sector) ++ [addRow s sector support] := by
    rw [addState_rows, List.filter_append]
    simp [addRow]
  rw [e, List.map_append, List.map_singleton]
  exact rankBitmasks_append_singleton_of_not_mem _ _
    (fun h => hspan ((inSpanRows_iff_inSpanMasks s.Q hQ _ _).mpr h))

theorem sectorRank_addState_other (s : CodeState) (sector : Sector) (support : List Nat)
    (σ : Sector) (hσ : σ ≠ sector) :
    sectorRank s.Q (addState s sector support).rows σ = sectorRank s.Q s.rows σ := by
  unfold sectorRank
  have e : (addState s sector support).rows.filter (fun x => x.sector = σ) =
      s.rows.filter (fun x => x.sector = σ) := by
    rw [addState_rows, List.filter_append]
    have hnil : [addRow s sector support].filter (fun x => x.sector = σ) = [] := by
      simp [addRow, Ne.symm hσ]
    rw [hnil, List.append_nil]
  rw [e]

/-- The dimension bound `rank X + rank Z ≤ |Q|`. It follows from I1 and I2
    (`X ⊆ Z^⊥` over `F₂`), as `ranksFit_of_wf` in `RanksFit.lean` derives; the
    rank-decrease lemmas below take it as a premise so that the truncated
    subtraction in `stateK` is exact. -/
def RanksFit (s : CodeState) : Prop :=
  sectorRank s.Q s.rows Sector.X + sectorRank s.Q s.rows Sector.Z ≤ s.Q.length

/-- The `k` cell of deletion: `k' = k + 1`. -/
theorem stateK_deleteState (s : CodeState) (hQ : s.Q.Nodup) (hids : (s.rows.map Row.id).Nodup)
    (row : Row) (hmem : row ∈ s.rows) (hind : IndependentGenerator row.id s) (hfit : RanksFit s) :
    stateK (deleteState s row.id) = stateK s + 1 := by
  have hsame := sectorRank_deleteState_same s hQ hids row hmem hind
  unfold RanksFit at hfit
  show s.Q.length - sectorRank s.Q (deleteState s row.id).rows Sector.X -
      sectorRank s.Q (deleteState s row.id).rows Sector.Z =
    s.Q.length - sectorRank s.Q s.rows Sector.X - sectorRank s.Q s.rows Sector.Z + 1
  cases hsec : row.sector with
  | X =>
    rw [hsec] at hsame
    have hother := sectorRank_deleteState_other s hids row hmem Sector.Z (by rw [hsec]; decide)
    rw [hother]
    omega
  | Z =>
    rw [hsec] at hsame
    have hother := sectorRank_deleteState_other s hids row hmem Sector.X (by rw [hsec]; decide)
    rw [hother]
    omega

/-- The `k` cell of addition: `k = k' + 1`, under the dimension bound of the
    output. -/
theorem stateK_addState (s : CodeState) (hQ : s.Q.Nodup) (sector : Sector) (support : List Nat)
    (hspan : ¬ inSpanRows s.Q (sectorRows s sector) (rowVector s.Q (addRow s sector support)))
    (hfit : RanksFit (addState s sector support)) :
    stateK s = stateK (addState s sector support) + 1 := by
  have hsame := sectorRank_addState_same s hQ sector support hspan
  have hfit' : sectorRank s.Q (addState s sector support).rows Sector.X +
      sectorRank s.Q (addState s sector support).rows Sector.Z ≤ s.Q.length := hfit
  show s.Q.length - sectorRank s.Q s.rows Sector.X - sectorRank s.Q s.rows Sector.Z =
    s.Q.length - sectorRank s.Q (addState s sector support).rows Sector.X -
      sectorRank s.Q (addState s sector support).rows Sector.Z + 1
  cases sector with
  | X =>
    have hother := sectorRank_addState_other s Sector.X support Sector.Z (by decide)
    rw [hsame, hother] at hfit' ⊢
    omega
  | Z =>
    have hother := sectorRank_addState_other s Sector.Z support Sector.X (by decide)
    rw [hsame, hother] at hfit' ⊢
    omega

theorem stateK_delete_of_eval {r : Nat} {s t : CodeState} (h : Eval (Command.delete r) s t)
    (hwf : EncodingWellFormed s) (hfit : RanksFit s) : stateK t = stateK s + 1 := by
  cases h with
  | delete hdisp hind heq =>
    obtain ⟨row, hmem, hid⟩ := hdisp
    subst hid
    rw [heq]
    exact stateK_deleteState s hwf.1 hwf.2.1 row hmem hind hfit

theorem stateK_add_of_eval {sector : Sector} {support : List Nat} {s t : CodeState}
    (h : Eval (Command.addStab sector support) s t)
    (hwf : EncodingWellFormed s) (hfit : RanksFit t) : stateK s = stateK t + 1 := by
  cases h with
  | add _ _ _ _ hspan heq =>
    subst heq
    exact stateK_addState s hwf.1 sector support hspan hfit

/-! ### Well-formedness preservation -/

theorem supports_subset_of_wf {s : CodeState} (hwf : EncodingWellFormed s) :
    ∀ row ∈ s.rows, supportSubset row.support s.Q := by
  intro row hrow q hq
  have h1 := List.all_eq_true.mp hwf.2.2.2.1 row hrow
  have h2 := List.all_eq_true.mp h1 q hq
  exact List.contains_iff_mem.mp h2

theorem ids_subset_used_of_wf {s : CodeState} (hwf : EncodingWellFormed s) :
    ∀ row ∈ s.rows, row.id ∈ s.used := by
  intro row hrow
  have h := List.all_eq_true.mp hwf.2.2.1 row.id (List.mem_map.mpr ⟨row, hrow, rfl⟩)
  exact List.contains_iff_mem.mp h

theorem supportIntersectionSize_eq_length_filter (a b : List Nat) :
    supportIntersectionSize a b = (a.filter (fun q => b.contains q)).length := by
  unfold supportIntersectionSize
  suffices hgen : ∀ acc, a.foldl (fun n q => if b.contains q then n + 1 else n) acc =
      acc + (a.filter (fun q => b.contains q)).length by
    have := hgen 0
    rwa [Nat.zero_add] at this
  induction a with
  | nil => intro acc; rfl
  | cons q qs ih =>
    intro acc
    rw [List.foldl_cons]
    by_cases hq : b.contains q = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hq), List.filter_cons_of_pos (p := fun q => b.contains q) hq,
        ih, List.length_cons]
      omega
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hq), List.filter_cons_of_neg (p := fun q => b.contains q) hq,
        ih]

/-- Intersection size is symmetric on duplicate-free supports. -/
theorem supportIntersectionSize_comm (a b : List Nat) (ha : a.Nodup) (hb : b.Nodup) :
    supportIntersectionSize a b = supportIntersectionSize b a := by
  rw [supportIntersectionSize_eq_length_filter, supportIntersectionSize_eq_length_filter]
  apply List.Perm.length_eq
  rw [List.perm_ext_iff_of_nodup (ha.sublist List.filter_sublist) (hb.sublist List.filter_sublist)]
  intro x
  simp only [List.mem_filter, List.contains_iff_mem]
  exact And.comm

/-- Deleting any row preserves well-formedness (§4.7, `C-DELETE-CHECK`). -/
theorem wf_deleteState (s : CodeState) (r : Nat) (hwf : EncodingWellFormed s) :
    EncodingWellFormed (deleteState s r) := by
  obtain ⟨hQ, hids, hused, hsup, hnd, hsort, hI1, hI2⟩ := hwf
  have hsub : (deleteState s r).rows.Sublist s.rows := List.filter_sublist
  have hids' : ((deleteState s r).rows.map Row.id).Nodup := hids.sublist (hsub.map Row.id)
  refine ⟨hQ, hids', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.all_eq_true] at hused ⊢
    intro x hx
    exact hused x ((hsub.map Row.id).subset hx)
  · rw [List.all_eq_true] at hsup ⊢
    intro row hrow
    exact hsup row (hsub.subset hrow)
  · rw [List.all_eq_true] at hnd ⊢
    intro row hrow
    exact hnd row (hsub.subset hrow)
  · rw [List.all_eq_true] at hsort ⊢
    intro row hrow
    exact hsort row (hsub.subset hrow)
  · intro rX rZ hX hZ hsX hsZ
    exact hI1 rX rZ (hsub.subset hX) (hsub.subset hZ) hsX hsZ
  · intro row hrow
    have hrow' : row ∈ s.rows := hsub.subset hrow
    rw [independentGenerator_iff (deleteState s r) hids' row hrow]
    intro hspan
    apply (independentGenerator_iff s hids row hrow').mp (hI2 row hrow')
    exact inSpanRows_of_sublist s.Q (hsub.filter _) _ hspan

theorem filter_sublist_filter_of_imp {α : Type} (p q : α → Bool) (l : List α)
    (h : ∀ x ∈ l, p x = true → q x = true) : (l.filter p).Sublist (l.filter q) := by
  induction l with
  | nil => exact List.Sublist.refl _
  | cons x xs ih =>
    have ih' := ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))
    by_cases hp : p x = true
    · rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos (h x (List.mem_cons.mpr (Or.inl rfl)) hp)]
      exact ih'.cons_cons x
    · rw [List.filter_cons_of_neg hp]
      by_cases hq : q x = true
      · rw [List.filter_cons_of_pos hq]
        exact ih'.cons x
      · rw [List.filter_cons_of_neg hq]
        exact ih'

/-- Adding a row under the `C-ADD-CHECK` premises preserves well-formedness
    (§4.7, `C-ADD-CHECK`). -/
theorem wf_addState (s : CodeState) (sector : Sector) (support : List Nat)
    (hwf : EncodingWellFormed s)
    (hsub : supportSubset support s.Q) (hnodup : support.Nodup)
    (hsorted : support.Pairwise (· ≤ ·))
    (hcomm : ∀ row ∈ s.rows, row.sector = oppositeSector sector →
      supportIntersectionSize support row.support % 2 = 0)
    (hspan : ¬ inSpanRows s.Q (sectorRows s sector) (rowVector s.Q (addRow s sector support))) :
    EncodingWellFormed (addState s sector support) := by
  have hidused := ids_subset_used_of_wf hwf
  obtain ⟨hQ, hids, hused, hsupQ, hnd, hsrt, hI1, hI2⟩ := hwf
  have hcfresh : canonicalMint s.used ∉ s.used :=
    fun h => canonicalMint_fresh s.used (List.contains_iff_mem.mpr h)
  have hcne : ∀ row ∈ s.rows, row.id ≠ canonicalMint s.used := by
    intro row hrow h
    apply hcfresh
    rw [← h]
    exact hidused row hrow
  have hrows' := addState_rows s sector support
  have hids' : ((addState s sector support).rows.map Row.id).Nodup := by
    rw [hrows', List.map_append, List.map_singleton, List.nodup_append]
    refine ⟨hids, by simp, ?_⟩
    intro a ha b hb
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp ha
    rw [List.mem_singleton] at hb
    rw [hb]
    exact hcne row hrow
  refine ⟨hQ, hids', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.all_eq_true]
    intro x hx
    rw [hrows', List.map_append, List.map_singleton] at hx
    show (s.used ++ [canonicalMint s.used]).contains x = true
    rw [List.contains_iff_mem]
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (List.contains_iff_mem.mp (List.all_eq_true.mp hused x hx))
    · rw [List.mem_singleton] at hx
      rw [hx]
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  · rw [List.all_eq_true]
    intro row hrow
    rw [hrows'] at hrow
    rcases List.mem_append.mp hrow with hrow | hrow
    · exact List.all_eq_true.mp hsupQ row hrow
    · rw [List.mem_singleton] at hrow
      rw [hrow]
      show support.all (fun q => s.Q.contains q) = true
      rw [List.all_eq_true]
      intro q hq
      exact List.contains_iff_mem.mpr (hsub q hq)
  · rw [List.all_eq_true]
    intro row hrow
    rw [hrows'] at hrow
    rcases List.mem_append.mp hrow with hrow | hrow
    · exact List.all_eq_true.mp hnd row hrow
    · rw [List.mem_singleton] at hrow
      rw [hrow]
      exact decide_eq_true hnodup
  · rw [List.all_eq_true]
    intro row hrow
    rw [hrows'] at hrow
    rcases List.mem_append.mp hrow with hrow | hrow
    · exact List.all_eq_true.mp hsrt row hrow
    · rw [List.mem_singleton] at hrow
      rw [hrow]
      exact decide_eq_true hsorted
  · intro rX rZ hX hZ hsX hsZ
    rw [hrows'] at hX hZ
    rcases List.mem_append.mp hX with hX | hX
    · rcases List.mem_append.mp hZ with hZ | hZ
      · exact hI1 rX rZ hX hZ hsX hsZ
      · rw [List.mem_singleton] at hZ
        subst hZ
        have hsec : sector = Sector.Z := hsZ
        have hopp : rX.sector = oppositeSector sector := by
          rw [hsX, hsec]
          rfl
        have h := hcomm rX hX hopp
        have hndX : rX.support.Nodup := by
          have := List.all_eq_true.mp hnd rX hX
          simpa using this
        rw [supportIntersectionSize_comm support rX.support hnodup hndX] at h
        exact h
    · rw [List.mem_singleton] at hX
      subst hX
      rcases List.mem_append.mp hZ with hZ | hZ
      · have hsec : sector = Sector.X := hsX
        have hopp : rZ.sector = oppositeSector sector := by
          rw [hsZ, hsec]
          rfl
        exact hcomm rZ hZ hopp
      · rw [List.mem_singleton] at hZ
        subst hZ
        have h1 : sector = Sector.X := hsX
        have h2 : sector = Sector.Z := hsZ
        rw [h1] at h2
        exact absurd h2 (by decide)
  · intro row hrow
    rw [independentGenerator_iff _ hids' row hrow]
    rw [hrows'] at hrow
    rcases List.mem_append.mp hrow with hrow | hrow
    · have hold := (independentGenerator_iff s hids row hrow).mp (hI2 row hrow)
      have hQ' : (addState s sector support).Q = s.Q := rfl
      rw [hQ']
      by_cases hs : sector = row.sector
      · have hpeers : (addState s sector support).rows.filter
            (fun r' => r'.sector = row.sector ∧ r'.id ≠ row.id) =
            s.rows.filter (fun r' => r'.sector = row.sector ∧ r'.id ≠ row.id) ++
              [addRow s sector support] := by
          rw [hrows', List.filter_append]
          have hkeep : [addRow s sector support].filter
              (fun r' => r'.sector = row.sector ∧ r'.id ≠ row.id) = [addRow s sector support] := by
            simp [addRow, hs, (hcne row hrow).symm]
          rw [hkeep]
        rw [hpeers, inSpanRows_append_singleton_iff s.Q _ _ _ (rowVector_length s.Q row)]
        rintro (h1 | h2)
        · exact hold h1
        · apply hspan
          have hpeers_sub : (s.rows.filter (fun r' => r'.sector = row.sector ∧ r'.id ≠ row.id)).Sublist
              (sectorRows s sector) := by
            apply filter_sublist_filter_of_imp
            intro x _ hx
            simp only [decide_eq_true_eq] at hx
            simp [hx.1, hs]
          have hrow_in : inSpanRows s.Q (sectorRows s sector) (rowVector s.Q row) :=
            inSpanRows_of_mem s.Q (List.mem_filter.mpr ⟨hrow, by simp [hs]⟩)
          have hx := inSpanRows_of_sublist s.Q hpeers_sub _ h2
          have hxor := inSpanRows_xor s.Q _ hrow_in hx
          rwa [xorVec_cancel_left _ _ (by rw [rowVector_length, rowVector_length])] at hxor
      · have hpeers : (addState s sector support).rows.filter
            (fun r' => r'.sector = row.sector ∧ r'.id ≠ row.id) =
            s.rows.filter (fun r' => r'.sector = row.sector ∧ r'.id ≠ row.id) := by
          rw [hrows', List.filter_append]
          have hdrop : [addRow s sector support].filter
              (fun r' => r'.sector = row.sector ∧ r'.id ≠ row.id) = [] := by
            simp [addRow, hs]
          rw [hdrop, List.append_nil]
        rw [hpeers]
        exact hold
    · rw [List.mem_singleton] at hrow
      subst hrow
      have hQ' : (addState s sector support).Q = s.Q := rfl
      rw [hQ']
      have hpeers : (addState s sector support).rows.filter
          (fun r' => r'.sector = (addRow s sector support).sector ∧
            r'.id ≠ (addRow s sector support).id) = sectorRows s sector := by
        rw [hrows', List.filter_append]
        have hdrop : [addRow s sector support].filter
            (fun r' => r'.sector = (addRow s sector support).sector ∧
              r'.id ≠ (addRow s sector support).id) = [] := by
          simp
        rw [hdrop, List.append_nil]
        unfold sectorRows
        apply List.filter_congr
        intro x hx
        simp [addRow, hcne x hx]
      rw [hpeers]
      exact hspan

/-- Commands whose well-formedness preservation is proved in this module:
    everything but the graft, whose preservation is `wf_graft_of_eval` in
    `GraftWellFormedness.lean`; `wf_of_eval_all` there covers every command. -/
def GraftFree : Command → Prop
  | .graft _ _ _ => False
  | .seq m1 m2 => GraftFree m1 ∧ GraftFree m2
  | _ => True

/-- Well-formedness is preserved by every evaluation of a graft-free command:
    skip trivially, deletion and addition by the lemmas above, sequencing by
    composition, and the Gate 6 cells by the premise their transitions carry. -/
theorem wf_of_eval {m : Command} {s t : CodeState} (hm : GraftFree m) (h : Eval m s t)
    (hwf : EncodingWellFormed s) : EncodingWellFormed t := by
  induction h with
  | skip _ => exact hwf
  | seq h1 h2 ih1 ih2 => exact ih2 hm.2 (ih1 hm.1 hwf)
  | delete _ _ heq =>
    rw [heq]
    exact wf_deleteState _ _ hwf
  | add hsub hnodup hsorted hcomm hspan heq =>
    rw [heq]
    exact wf_addState _ _ _ hwf hsub hnodup hsorted hcomm hspan
  | graft => exact absurd hm id
  | rebase _ _ _ hwf' => exact hwf'
  | hadamard _ _ hwf' => exact hwf'
  | peel _ _ _ _ _ hwf' => exact hwf'
  | puncture _ _ hwf' => exact hwf'
  | extend _ _ hwf' => exact hwf'

end CodeCalculus
