import CodeCalculus.ConstructorRankTyped

/-!
# `A-CONCAT` retains every natural row

The retained display of `A-CONCAT` drops no natural row. By
`sectorRank_constructedState` the displayed rows of one sector of a
constructed state number the rank of the natural rows of that sector, so
the statement is that the natural rows of each sector are linearly
independent. This module proves that independence from the independence of
the displayed rows of the two factors (I2) and the duality of the
representatives, following `spec/OPERATIONAL_SEMANTICS.md` §4.34.

* `VecIndep n vs`: no nontrivial `F₂` combination of the vectors `vs` of
  length `n` is zero.
* `vecIndep_append_of_kill_right` and `vecIndep_append_of_kill_left`: a
  list `A ++ B` is independent when an additive map kills one part, keeps
  the other independent, and the killed part is independent.
* `vecIndep_sectorRows`: the displayed rows of one sector of a well-formed
  state are independent.
* `constructedState_rows_length_of_indep`: a constructed state whose
  natural rows are independent sector by sector displays all of them.
* `combineRows_take_drop`: projecting a combination of length `nb * blockSize`
  onto block `j` is the combination of the projected rows (corollary of
  `combineRows_map_additive` and `additive_blockAt`).
* `vecIndep_concat`: the natural rows of one sector of `A-CONCAT` are
  independent. The inner rows on copy `j` are separated from the other
  copies by the projection onto block `j`. The lifted outer rows are
  separated from the inner rows by the overlap parities with the
  representatives of the opposite sector, copy by copy: these vanish on
  the inner rows, and on the lift of an outer row they read off its vector
  over the outer labels.
* `concatState_rows_length`: the retention statement, with no hypothesis
  beyond the typing and the well-formedness of the factors.
* `concatState_k_closed` and `evalExpr_concat_k`: `k = k_O`.
-/

namespace CodeCalculus

/-! ## Combinations -/

theorem combineRows_nil (n : Nat) (cs : List Bool) :
    combineRows n [] cs = List.replicate n false := by
  cases cs <;> rfl

theorem combineRows_cons_true (n : Nat) (v : List Bool) (vs : List (List Bool))
    (cs : List Bool) :
    combineRows n (v :: vs) (true :: cs) = xorVec v (combineRows n vs cs) := rfl

theorem combineRows_cons_false (n : Nat) (v : List Bool) (vs : List (List Bool))
    (cs : List Bool) :
    combineRows n (v :: vs) (false :: cs) = combineRows n vs cs := rfl

/-- A combination with every coefficient `false` is the zero vector. -/
theorem combineRows_all_false (n : Nat) : ∀ (vs : List (List Bool)) (cs : List Bool),
    (∀ c ∈ cs, c = false) → combineRows n vs cs = List.replicate n false
  | [], cs, _ => combineRows_nil n cs
  | _ :: _, [], _ => rfl
  | v :: vs, c :: cs, h => by
      have hc : c = false := h c (List.mem_cons_self ..)
      subst hc
      exact combineRows_all_false n vs cs (fun c hc => h c (List.mem_cons_of_mem _ hc))

/-- A combination of zero vectors is the zero vector. -/
theorem combineRows_all_zero (n : Nat) : ∀ (vs : List (List Bool)) (cs : List Bool),
    (∀ v ∈ vs, v = List.replicate n false) → combineRows n vs cs = List.replicate n false
  | [], cs, _ => combineRows_nil n cs
  | _ :: _, [], _ => rfl
  | v :: vs, true :: cs, h => by
      rw [combineRows_cons_true, h v (List.mem_cons_self ..),
        combineRows_all_zero n vs cs (fun w hw => h w (List.mem_cons_of_mem _ hw))]
      exact xorVec_replicate_false_left n _ List.length_replicate
  | v :: vs, false :: cs, h =>
      combineRows_all_zero n vs cs (fun w hw => h w (List.mem_cons_of_mem _ hw))

/-- A combination over an appended list is the sum of the two
    combinations. -/
theorem combineRows_append_left (n : Nat) : ∀ (A B : List (List Bool)) (ca cb : List Bool),
    ca.length = A.length → (∀ v ∈ A, v.length = n) → (∀ v ∈ B, v.length = n) →
    combineRows n (A ++ B) (ca ++ cb) = xorVec (combineRows n A ca) (combineRows n B cb)
  | [], B, [], cb, _, _, hB => by
      rw [List.nil_append, List.nil_append, combineRows_nil]
      exact (xorVec_replicate_false_left n _ (combineRows_length n B cb hB)).symm
  | [], _, _ :: _, _, h, _, _ => nomatch h
  | _ :: _, _, [], _, h, _, _ => nomatch h
  | v :: A, B, true :: ca, cb, h, hA, hB => by
      have hA' : ∀ w ∈ A, w.length = n := fun w hw => hA w (List.mem_cons_of_mem _ hw)
      have ih := combineRows_append_left n A B ca cb (Nat.succ.inj h) hA' hB
      show xorVec v (combineRows n (A ++ B) (ca ++ cb)) =
        xorVec (xorVec v (combineRows n A ca)) (combineRows n B cb)
      rw [ih, xorVec_assoc _ _ _
        (by rw [hA v (List.mem_cons_self ..), combineRows_length n A ca hA'])
        (by rw [combineRows_length n A ca hA', combineRows_length n B cb hB])]
  | v :: A, B, false :: ca, cb, h, hA, hB =>
      combineRows_append_left n A B ca cb (Nat.succ.inj h)
        (fun w hw => hA w (List.mem_cons_of_mem _ hw)) hB

theorem split_coeffs (cs : List Bool) (k : Nat) (h : k ≤ cs.length) :
    ∃ ca cb, cs = ca ++ cb ∧ ca.length = k ∧ cb.length = cs.length - k :=
  ⟨cs.take k, cs.drop k, (List.take_append_drop k cs).symm,
    by rw [List.length_take]; exact Nat.min_eq_left h, List.length_drop⟩

theorem eq_of_xorVec_zero (n : Nat) (a b : List Bool) (ha : a.length = n) (hb : b.length = n)
    (h : xorVec a b = List.replicate n false) : a = b := by
  have h1 := xorVec_cancel_right a b (by rw [ha, hb])
  rw [h, xorVec_replicate_false_left n b hb] at h1
  exact h1.symm

/-! ## Additive maps -/

/-- A map of vectors of length `n` to vectors of length `m` that commutes
    with the sum and sends zero to zero. -/
structure AdditiveMap (n m : Nat) (f : List Bool → List Bool) : Prop where
  add : ∀ a b, a.length = n → b.length = n → f (xorVec a b) = xorVec (f a) (f b)
  zero : f (List.replicate n false) = List.replicate m false
  len : ∀ a, a.length = n → (f a).length = m

/-- An additive map commutes with combinations. -/
theorem combineRows_map_additive {n m : Nat} {f : List Bool → List Bool}
    (hf : AdditiveMap n m f) : ∀ (vs : List (List Bool)) (cs : List Bool),
    (∀ v ∈ vs, v.length = n) → f (combineRows n vs cs) = combineRows m (vs.map f) cs
  | [], cs, _ => by
      rw [combineRows_nil, List.map_nil, combineRows_nil]
      exact hf.zero
  | _ :: _, [], _ => hf.zero
  | v :: vs, true :: cs, h => by
      have h' : ∀ w ∈ vs, w.length = n := fun w hw => h w (List.mem_cons_of_mem _ hw)
      show f (xorVec v (combineRows n vs cs)) = xorVec (f v) (combineRows m (vs.map f) cs)
      rw [hf.add v _ (h v (List.mem_cons_self ..)) (combineRows_length n vs cs h'),
        combineRows_map_additive hf vs cs h']
  | v :: vs, false :: cs, h =>
      combineRows_map_additive hf vs cs (fun w hw => h w (List.mem_cons_of_mem _ hw))

/-! ## Independence -/

/-- Linear independence over `F₂` of a list of vectors of length `n`: a
    combination that vanishes has every coefficient `false`. -/
def VecIndep (n : Nat) (vs : List (List Bool)) : Prop :=
  ∀ cs : List Bool, cs.length = vs.length →
    combineRows n vs cs = List.replicate n false → ∀ c ∈ cs, c = false

theorem vecIndep_nil (n : Nat) : VecIndep n [] := by
  intro cs hlen _ c hc
  cases cs with
  | nil => nomatch hc
  | cons _ _ => nomatch hlen

theorem length_map_additive {n m : Nat} {f : List Bool → List Bool} (hf : AdditiveMap n m f)
    (A : List (List Bool)) (hA : ∀ v ∈ A, v.length = n) : ∀ w ∈ A.map f, w.length = m := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
  exact hf.len v (hA v hv)

theorem vecIndep_append_core {n m : Nat} {f : List Bool → List Bool} (hf : AdditiveMap n m f)
    (A B : List (List Bool)) (hA : ∀ v ∈ A, v.length = n) (hB : ∀ v ∈ B, v.length = n)
    (ca cb : List Bool) (hca : ca.length = A.length)
    (h : combineRows n (A ++ B) (ca ++ cb) = List.replicate n false) :
    xorVec (combineRows m (A.map f) ca) (combineRows m (B.map f) cb) =
      List.replicate m false := by
  have h1 := congrArg f h
  rw [combineRows_append_left n A B ca cb hca hA hB,
    hf.add _ _ (combineRows_length n A ca hA) (combineRows_length n B cb hB),
    combineRows_map_additive hf A ca hA, combineRows_map_additive hf B cb hB, hf.zero] at h1
  exact h1

/-- `A ++ B` is independent when an additive map kills `B` and keeps `A`
    independent, and `B` is independent. -/
theorem vecIndep_append_of_kill_right {n m : Nat} {f : List Bool → List Bool}
    (hf : AdditiveMap n m f) (A B : List (List Bool))
    (hA : ∀ v ∈ A, v.length = n) (hB : ∀ v ∈ B, v.length = n)
    (hkill : ∀ v ∈ B, f v = List.replicate m false)
    (hAf : VecIndep m (A.map f)) (hBi : VecIndep n B) : VecIndep n (A ++ B) := by
  intro cs hlen hzero
  rw [List.length_append] at hlen
  obtain ⟨ca, cb, rfl, hca, hcb⟩ := split_coeffs cs A.length (by omega)
  have hcb' : cb.length = B.length := by rw [hcb, hlen]; omega
  have hcore := vecIndep_append_core hf A B hA hB ca cb hca hzero
  have hBz : combineRows m (B.map f) cb = List.replicate m false :=
    combineRows_all_zero m _ cb (fun w hw => by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      exact hkill v hv)
  rw [hBz, xorVec_replicate_false_right m _
    (combineRows_length m _ ca (length_map_additive hf A hA))] at hcore
  have hca0 := hAf ca (by rw [List.length_map]; exact hca) hcore
  rw [combineRows_append_left n A B ca cb hca hA hB, combineRows_all_false n A ca hca0,
    xorVec_replicate_false_left n _ (combineRows_length n B cb hB)] at hzero
  have hcb0 := hBi cb hcb' hzero
  intro c hc
  rcases List.mem_append.mp hc with h1 | h1
  · exact hca0 c h1
  · exact hcb0 c h1

/-- `A ++ B` is independent when an additive map kills `A` and keeps `B`
    independent, and `A` is independent. -/
theorem vecIndep_append_of_kill_left {n m : Nat} {f : List Bool → List Bool}
    (hf : AdditiveMap n m f) (A B : List (List Bool))
    (hA : ∀ v ∈ A, v.length = n) (hB : ∀ v ∈ B, v.length = n)
    (hkill : ∀ v ∈ A, f v = List.replicate m false)
    (hBf : VecIndep m (B.map f)) (hAi : VecIndep n A) : VecIndep n (A ++ B) := by
  intro cs hlen hzero
  rw [List.length_append] at hlen
  obtain ⟨ca, cb, rfl, hca, hcb⟩ := split_coeffs cs A.length (by omega)
  have hcb' : cb.length = B.length := by rw [hcb, hlen]; omega
  have hcore := vecIndep_append_core hf A B hA hB ca cb hca hzero
  have hAz : combineRows m (A.map f) ca = List.replicate m false :=
    combineRows_all_zero m _ ca (fun w hw => by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      exact hkill v hv)
  rw [hAz, xorVec_replicate_false_left m _
    (combineRows_length m _ cb (length_map_additive hf B hB))] at hcore
  have hcb0 := hBf cb (by rw [List.length_map]; exact hcb') hcore
  rw [combineRows_append_left n A B ca cb hca hA hB, combineRows_all_false n B cb hcb0,
    xorVec_replicate_false_right n _ (combineRows_length n A ca hA)] at hzero
  have hca0 := hAi ca hca hzero
  intro c hc
  rcases List.mem_append.mp hc with h1 | h1
  · exact hca0 c h1
  · exact hcb0 c h1

/-- Appending a vector outside the span of an independent list keeps it
    independent. -/
theorem vecIndep_snoc {n : Nat} (A : List (List Bool)) (w : List Bool)
    (hA : ∀ v ∈ A, v.length = n) (hw : w.length = n) (hAi : VecIndep n A)
    (hnot : ¬ ∃ cs : List Bool, cs.length = A.length ∧ combineRows n A cs = w) :
    VecIndep n (A ++ [w]) := by
  intro cs hlen hzero
  rw [List.length_append, List.length_singleton] at hlen
  obtain ⟨ca, cb, rfl, hca, hcb⟩ := split_coeffs cs A.length (by omega)
  have hcb1 : cb.length = 1 := by rw [hcb, hlen]; omega
  rw [combineRows_append_left n A [w] ca cb hca hA
    (fun v hv => by rw [List.mem_singleton.mp hv]; exact hw)] at hzero
  have hlenA := combineRows_length n A ca hA
  cases cb with
  | nil => nomatch hcb1
  | cons c cb' =>
      cases cb' with
      | cons _ _ =>
          rw [List.length_cons, List.length_cons] at hcb1
          omega
      | nil =>
          cases c with
          | true =>
              have e : combineRows n [w] [true] = w := by
                show xorVec w (List.replicate n false) = w
                exact xorVec_replicate_false_right n w hw
              rw [e] at hzero
              exact absurd ⟨ca, hca, eq_of_xorVec_zero n _ w hlenA hw hzero⟩ hnot
          | false =>
              have e : combineRows n [w] [false] = List.replicate n false := rfl
              rw [e, xorVec_replicate_false_right n _ hlenA] at hzero
              have hca0 := hAi ca hca hzero
              intro c hc
              rcases List.mem_append.mp hc with h1 | h1
              · exact hca0 c h1
              · exact List.mem_singleton.mp h1

/-! ## The displayed rows of a well-formed state -/

/-- On a well-formed state a displayed row is outside the span of the rows
    of its sector displayed before it. -/
theorem prefix_not_inSpan_of_wf (s : CodeState) (hwf : EncodingWellFormed s) (σ : Sector)
    (l₁ : List Row) (r : Row) (l₂ : List Row) (hsplit : sectorRows s σ = l₁ ++ r :: l₂) :
    ¬ inSpanRows s.Q l₁ (rowVector s.Q r) := by
  obtain ⟨_, hids, _, _, _, _, _, hI2⟩ := hwf
  have hrsec : r ∈ sectorRows s σ := by
    rw [hsplit]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  have hr : r ∈ s.rows := (List.mem_filter.mp hrsec).1
  have hrσ : r.sector = σ := of_decide_eq_true (List.mem_filter.mp hrsec).2
  have hl₁ : l₁.Sublist (sectorRows s σ) := by
    rw [hsplit]
    exact List.sublist_append_left _ _
  have hnd : ((sectorRows s σ).map Row.id).Nodup :=
    hids.sublist (List.filter_sublist.map Row.id)
  rw [hsplit, List.map_append, List.map_cons] at hnd
  have hall : ∀ x ∈ l₁, decide (x.sector = r.sector ∧ x.id ≠ r.id) = true := by
    intro x hx
    have hxσ : x.sector = σ := of_decide_eq_true (List.mem_filter.mp (hl₁.subset hx)).2
    have hne : x.id ≠ r.id := by
      intro heq
      exact (List.nodup_append.mp hnd).2.2 x.id (List.mem_map.mpr ⟨x, hx, rfl⟩) r.id
        (List.mem_cons_self ..) heq
    exact decide_eq_true ⟨hxσ.trans hrσ.symm, hne⟩
  have hsub : l₁.Sublist (s.rows.filter (fun r' => r'.sector = r.sector ∧ r'.id ≠ r.id)) := by
    have h1 : l₁.filter (fun r' => r'.sector = r.sector ∧ r'.id ≠ r.id) = l₁ :=
      List.filter_eq_self.mpr hall
    rw [← h1]
    exact (hl₁.trans List.filter_sublist).filter _
  intro hsp
  exact (independentGenerator_iff s hids r hr).mp (hI2 r hr)
    (inSpanRows_of_sublist s.Q hsub _ hsp)

/-- The displayed rows of one sector of a well-formed state are
    independent. -/
theorem vecIndep_sectorRows (s : CodeState) (hwf : EncodingWellFormed s) (σ : Sector) :
    VecIndep s.Q.length ((sectorRows s σ).map (rowVector s.Q)) := by
  have key : ∀ l₂ l₁ : List Row, sectorRows s σ = l₁ ++ l₂ →
      VecIndep s.Q.length (l₁.map (rowVector s.Q)) →
      VecIndep s.Q.length ((l₁ ++ l₂).map (rowVector s.Q)) := by
    intro l₂
    induction l₂ with
    | nil =>
        intro l₁ _ h
        rw [List.append_nil]
        exact h
    | cons r l₂ ih =>
        intro l₁ hsplit h1
        have hnot := prefix_not_inSpan_of_wf s hwf σ l₁ r l₂ hsplit
        have hstep : VecIndep s.Q.length ((l₁ ++ [r]).map (rowVector s.Q)) := by
          rw [List.map_append]
          apply vecIndep_snoc _ _ (rowVectors_length s.Q l₁) (rowVector_length s.Q r) h1
          intro ⟨cs, hlen, hval⟩
          exact hnot ⟨cs, by rw [hlen, List.length_map], hval⟩
        have h2 := ih (l₁ ++ [r]) (by rw [hsplit, List.append_assoc]; rfl) hstep
        rw [List.append_assoc] at h2
        exact h2
  exact key (sectorRows s σ) [] rfl (vecIndep_nil _)

/-! ## From independent vectors to independent masks -/

theorem getD_xorVec : ∀ (a b : List Bool) (i : Nat), a.length = b.length →
    (xorVec a b).getD i false = (a.getD i false != b.getD i false)
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h
  | _ :: _, _ :: _, 0, _ => rfl
  | _ :: a, _ :: b, i + 1, h => getD_xorVec a b i (Nat.succ.inj h)

theorem getD_replicate_false : ∀ (n i : Nat), (List.replicate n false).getD i false = false
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | n + 1, i + 1 => getD_replicate_false n i

theorem vecMask_xorVec (n : Nat) (a b : List Bool) (h : a.length = b.length) :
    vecMask n (xorVec a b) = vecMask n a ^^^ vecMask n b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, testBit_vecMask, testBit_vecMask, testBit_vecMask, getD_xorVec a b i h]
  cases decide (i < n) <;> cases a.getD i false <;> cases b.getD i false <;> rfl

theorem vecMask_replicate_false (n : Nat) : vecMask n (List.replicate n false) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_vecMask, getD_replicate_false, Bool.and_false, Nat.zero_testBit]

theorem eq_replicate_of_vecMask_zero (n : Nat) (v : List Bool) (hv : v.length = n)
    (h : vecMask n v = 0) : v = List.replicate n false := by
  apply List.ext_getElem
  · rw [hv, List.length_replicate]
  · intro i h1 h2
    rw [List.getElem_replicate]
    have hi : i < n := by rw [← hv]; exact h1
    have hb := testBit_vecMask n v i
    rw [h, Nat.zero_testBit, decide_eq_true hi, Bool.true_and, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h1] at hb
    exact hb.symm

/-- The mask of a combination of vectors is the combination of the masks. -/
theorem combineMasks_vecMask (n : Nat) : ∀ (vs : List (List Bool)) (cs : List Nat),
    (∀ v ∈ vs, v.length = n) →
    combineMasks (vs.map (vecMask n)) cs =
      vecMask n (combineRows n vs (cs.map (fun c => decide (c = 1))))
  | [], cs, _ => by
      rw [List.map_nil, combineRows_nil, vecMask_replicate_false]
      rfl
  | v :: vs, [], _ => by
      show 0 = vecMask n (List.replicate n false)
      rw [vecMask_replicate_false]
  | v :: vs, c :: cs, h => by
      have h' : ∀ w ∈ vs, w.length = n := fun w hw => h w (List.mem_cons_of_mem _ hw)
      have ih := combineMasks_vecMask n vs cs h'
      show (if c = 1 then vecMask n v else 0) ^^^ combineMasks (vs.map (vecMask n)) cs =
        vecMask n (combineRows n (v :: vs)
          (decide (c = 1) :: cs.map (fun c => decide (c = 1))))
      rcases Decidable.em (c = 1) with hc | hc
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), decide_eq_true hc, combineRows_cons_true,
          vecMask_xorVec n _ _ (by
            rw [h v (List.mem_cons_self ..), combineRows_length n vs _ h']), ih]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hc), decide_eq_false hc, combineRows_cons_false,
          Nat.zero_xor, ih]

/-- Independent vectors of length `n` have independent masks. -/
theorem independentMasks_of_vecIndep (n : Nat) (vs : List (List Bool))
    (hlen : ∀ v ∈ vs, v.length = n) (h : VecIndep n vs) :
    independentMasks (vs.map (vecMask n)) := by
  intro cs hcs _ hzero
  rw [combineMasks_vecMask n vs cs hlen] at hzero
  have hz := eq_replicate_of_vecMask_zero n _ (combineRows_length n vs _ hlen) hzero
  have hb := h (cs.map (fun c => decide (c = 1)))
    (by rw [List.length_map, hcs, List.length_map]) hz
  intro c hc
  have hc1 := hb (decide (c = 1)) (List.mem_map.mpr ⟨c, hc, rfl⟩)
  rcases Decidable.em (c = 1) with h1 | h1
  · rw [decide_eq_true h1] at hc1
    exact absurd hc1 (by decide)
  · rename_i h01
    rcases h01 c hc with h0 | h0
    · exact h0
    · exact absurd h0 h1

/-! ## Retention from independence -/

theorem length_filter_sector_add {α : Type} : ∀ (vs : List (Sector × α)),
    (vs.filter (fun x => x.1 = Sector.X)).length +
      (vs.filter (fun x => x.1 = Sector.Z)).length = vs.length
  | [] => rfl
  | x :: vs => by
      have ih := length_filter_sector_add vs
      cases hs : x.1 with
      | X =>
          rw [List.filter_cons_of_pos (by rw [hs]; exact decide_eq_true rfl),
            List.filter_cons_of_neg (by rw [hs]; decide), List.length_cons, List.length_cons]
          omega
      | Z =>
          rw [List.filter_cons_of_neg (by rw [hs]; decide),
            List.filter_cons_of_pos (by rw [hs]; exact decide_eq_true rfl),
            List.length_cons, List.length_cons]
          omega

/-- A constructed state whose natural rows are independent sector by sector
    displays every natural row. -/
theorem constructedState_rows_length_of_indep (n : Nat) (vs : List (Sector × List Bool))
    (horth : NaturalOrthogonal (naturalRows n vs))
    (hlen : ∀ x ∈ vs, x.2.length = n)
    (hind : ∀ σ, VecIndep n ((vs.filter (fun x => x.1 = σ)).map Prod.snd)) :
    (constructedState n vs).rows.length = vs.length := by
  obtain ⟨hQ, hids, _, _, _, _, _, hI2⟩ := wf_constructedState n vs horth
  have hrank : ∀ σ, (sectorRows (constructedState n vs) σ).length =
      (vs.filter (fun x => x.1 = σ)).length := by
    intro σ
    rw [← sectorRank_eq_length_of_I2 _ hQ hids hI2 σ, sectorRank_constructedState]
    have hm : naturalMasks n vs σ =
        ((vs.filter (fun x => x.1 = σ)).map Prod.snd).map (vecMask n) := by
      unfold naturalMasks
      rw [List.map_map]
      rfl
    rw [hm, rankBitmasks_of_indep (independentMasks_of_vecIndep n _ (fun v hv => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      exact hlen x (List.mem_filter.mp hx).1) (hind σ)), List.length_map, List.length_map]
  rw [← length_sectorRows_add, hrank, hrank, length_filter_sector_add]

/-! ## Blocks of a vector -/

theorem xorVec_take : ∀ (k : Nat) (a b : List Bool), a.length = b.length →
    (xorVec a b).take k = xorVec (a.take k) (b.take k)
  | 0, _, _, _ => rfl
  | _ + 1, [], [], _ => rfl
  | _ + 1, [], _ :: _, h => nomatch h
  | _ + 1, _ :: _, [], h => nomatch h
  | k + 1, x :: a, y :: b, h => by
      show (x != y) :: (xorVec a b).take k = (x != y) :: xorVec (a.take k) (b.take k)
      rw [xorVec_take k a b (Nat.succ.inj h)]

theorem xorVec_drop : ∀ (k : Nat) (a b : List Bool), a.length = b.length →
    (xorVec a b).drop k = xorVec (a.drop k) (b.drop k)
  | 0, _, _, _ => rfl
  | _ + 1, [], [], _ => rfl
  | _ + 1, [], _ :: _, h => nomatch h
  | _ + 1, _ :: _, [], h => nomatch h
  | k + 1, _ :: a, _ :: b, h => xorVec_drop k a b (Nat.succ.inj h)

/-- Block `j` of a vector made of blocks of length `ℓ`. -/
def blockAt (ℓ j : Nat) (v : List Bool) : List Bool := (v.drop (j * ℓ)).take ℓ

/-- The projection onto block `j` is additive. -/
theorem additive_blockAt (ℓ nb j : Nat) (hj : j < nb) :
    AdditiveMap (nb * ℓ) ℓ (blockAt ℓ j) := by
  have hle : j * ℓ + ℓ ≤ nb * ℓ := by
    have h := Nat.mul_le_mul_right ℓ (Nat.succ_le_of_lt hj)
    rw [Nat.succ_mul] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · intro a b ha hb
    unfold blockAt
    rw [xorVec_drop _ a b (by rw [ha, hb]),
      xorVec_take _ _ _ (by rw [List.length_drop, List.length_drop, ha, hb])]
  · unfold blockAt
    rw [List.drop_replicate, List.take_replicate, Nat.min_eq_left (by omega)]
  · intro a ha
    unfold blockAt
    rw [List.length_take, List.length_drop, ha, Nat.min_eq_left (by omega)]

/-- Projecting a combination of length `nb * blockSize` onto block `j` is the
    combination of the projected rows. -/
theorem combineRows_take_drop (blockSize nb j : Nat) (vs : List (List Bool)) (cs : List Bool)
    (hj : j < nb) (hvs : ∀ v ∈ vs, v.length = nb * blockSize) :
    ((combineRows (nb * blockSize) vs cs).drop (j * blockSize)).take blockSize =
      combineRows blockSize
        (vs.map (fun v => (v.drop (j * blockSize)).take blockSize)) cs :=
  combineRows_map_additive (additive_blockAt blockSize nb j hj) vs cs hvs

/-- Block `j` of a list of blocks of one length is the `j`-th block. -/
theorem blockAt_flatMap {α : Type} (ℓ : Nat) (F : α → List Bool) (d : α) :
    ∀ (L : List α) (j : Nat), (∀ a ∈ L, (F a).length = ℓ) → j < L.length →
    blockAt ℓ j (L.flatMap F) = F (L.getD j d)
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | a :: L, 0, hF, _ => by
      unfold blockAt
      rw [Nat.zero_mul, List.drop_zero, List.flatMap_cons,
        List.take_left' (hF a (List.mem_cons_self ..))]
      rfl
  | a :: L, j + 1, hF, h => by
      have ih := blockAt_flatMap ℓ F d L j (fun b hb => hF b (List.mem_cons_of_mem _ hb))
        (Nat.lt_of_succ_lt_succ h)
      unfold blockAt at ih ⊢
      rw [List.flatMap_cons, Nat.succ_mul, Nat.add_comm (j * ℓ) ℓ, ← List.drop_drop,
        List.drop_left' (hF a (List.mem_cons_self ..)), ih]
      rfl

theorem getD_range (n j : Nat) (hj : j < n) : (List.range n).getD j 0 = j := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_range hj]
  rfl

theorem length_concatInner_block (I : CodeState) (c : Prop) [Decidable c] (r : Row) :
    (if c then rowVector I.Q r else List.replicate I.Q.length false).length = I.Q.length := by
  split
  · exact rowVector_length I.Q r
  · exact List.length_replicate

/-- Block `j` of the inner row on copy `j2`. -/
theorem blockAt_concatInner (I : CodeState) (nb j j2 : Nat) (hj : j < nb) (r : Row) :
    blockAt I.Q.length j (concatInner I nb j2 r) =
      if j = j2 then rowVector I.Q r else List.replicate I.Q.length false := by
  unfold concatInner
  rw [blockAt_flatMap I.Q.length _ 0 (List.range nb) j
    (fun j' _ => length_concatInner_block I _ r) (by rw [List.length_range]; exact hj),
    getD_range nb j hj]

/-- The inner rows of one sector, on the copies of a repeat-free list, are
    independent. -/
theorem vecIndep_concatInner (I : CodeState) (hI : EncodingWellFormed I) (σ : Sector)
    (nb : Nat) : ∀ L : List Nat, L.Nodup → (∀ j ∈ L, j < nb) →
    VecIndep (nb * I.Q.length)
      (L.flatMap (fun j => (sectorRows I σ).map (concatInner I nb j)))
  | [], _, _ => vecIndep_nil _
  | j :: L, hnd, hlt => by
      rw [List.nodup_cons] at hnd
      have hj : j < nb := hlt j (List.mem_cons_self ..)
      rw [List.flatMap_cons]
      apply vecIndep_append_of_kill_right (additive_blockAt I.Q.length nb j hj)
      · intro v hv
        obtain ⟨r, _, rfl⟩ := List.mem_map.mp hv
        exact length_concatInner I nb j r
      · intro v hv
        obtain ⟨j2, _, hm⟩ := List.mem_flatMap.mp hv
        obtain ⟨r, _, rfl⟩ := List.mem_map.mp hm
        exact length_concatInner I nb j2 r
      · intro v hv
        obtain ⟨j2, hj2, hm⟩ := List.mem_flatMap.mp hv
        obtain ⟨r, _, rfl⟩ := List.mem_map.mp hm
        rw [blockAt_concatInner I nb j j2 hj r, ite_eq_right_of_eq_false _ _
          (eq_false (fun (e : j = j2) => hnd.1 (by rw [e]; exact hj2)))]
      · rw [List.map_map]
        have e : (sectorRows I σ).map (blockAt I.Q.length j ∘ concatInner I nb j) =
            (sectorRows I σ).map (rowVector I.Q) :=
          List.map_congr_left (fun r _ => by
            show blockAt I.Q.length j (concatInner I nb j r) = rowVector I.Q r
            rw [blockAt_concatInner I nb j j hj r, ite_eq_left_of_eq_true _ _ (eq_self j)])
        rw [e]
        exact vecIndep_sectorRows I hI σ
      · exact vecIndep_concatInner I hI σ nb L hnd.2
          (fun j' hj' => hlt j' (List.mem_cons_of_mem _ hj'))

/-! ## Overlap parities with a list of test vectors -/

theorem xorVec_map_map_gen {α : Type} (f g : α → Bool) : ∀ L : List α,
    xorVec (L.map f) (L.map g) = L.map (fun q => f q != g q)
  | [] => rfl
  | q :: L => by
      rw [List.map_cons, List.map_cons, List.map_cons, xorVec_cons, xorVec_map_map_gen f g L]

theorem map_eq_replicate_false {α : Type} (g : α → Bool) : ∀ L : List α,
    (∀ a ∈ L, g a = false) → L.map g = List.replicate L.length false
  | [], _ => rfl
  | a :: L, h => by
      rw [List.map_cons, h a (List.mem_cons_self ..),
        map_eq_replicate_false g L (fun b hb => h b (List.mem_cons_of_mem _ hb))]
      rfl

theorem all_false_of_map_eq_replicate {α : Type} (g : α → Bool) : ∀ L : List α,
    L.map g = List.replicate L.length false → ∀ a ∈ L, g a = false
  | [], _, _, h => nomatch h
  | x :: L, h, a, ha => by
      have h' : g x :: L.map g = false :: List.replicate L.length false := h
      obtain ⟨h1, h2⟩ := List.cons.inj h'
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact h1
      · exact all_false_of_map_eq_replicate g L h2 a ha'

theorem decide_parity_add (x y z : Nat) (h : z % 2 = (x + y) % 2) :
    decide (z % 2 = 1) = (decide (x % 2 = 1) != decide (y % 2 = 1)) := by
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx
  · rcases Nat.mod_two_eq_zero_or_one y with hy | hy
    · have hz : z % 2 = 0 := by omega
      rw [hz, hx, hy]
      rfl
    · have hz : z % 2 = 1 := by omega
      rw [hz, hx, hy]
      rfl
  · rcases Nat.mod_two_eq_zero_or_one y with hy | hy
    · have hz : z % 2 = 1 := by omega
      rw [hz, hx, hy]
      rfl
    · have hz : z % 2 = 0 := by omega
      rw [hz, hx, hy]
      rfl

/-- The overlap parities of a vector with a list of test vectors. -/
def pairVec (T : List (List Bool)) (v : List Bool) : List Bool :=
  T.map (fun t => decide (dotPar t v % 2 = 1))

/-- The overlap parities are additive in the vector. -/
theorem additive_pairVec (n : Nat) (T : List (List Bool)) :
    AdditiveMap n T.length (pairVec T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b ha hb
    unfold pairVec
    rw [xorVec_map_map_gen]
    exact List.map_congr_left (fun t _ =>
      decide_parity_add _ _ _ (dotPar_xorVec t a b (by rw [ha, hb])))
  · unfold pairVec
    exact map_eq_replicate_false _ T (fun t _ => by
      show decide (dotPar t (List.replicate n false) % 2 = 1) = false
      rw [dotPar_replicate_false]
      rfl)
  · intro a _
    unfold pairVec
    rw [List.length_map]

/-! ## Dual representatives -/

theorem dualLists_symm (n : Nat) : ∀ (xs zs : List (List Bool)), DualLists n xs zs →
    DualLists n zs xs
  | [], [], _ => trivial
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | x :: xs, z :: zs, h => by
      obtain ⟨hx, hz, hxz, hxzs, hzxs, hd⟩ := h
      exact ⟨hz, hx, by rw [dotPar_comm]; exact hxz, hzxs, hxzs, dualLists_symm n xs zs hd⟩

/-- A dual vector reads off its coefficient from a combination. -/
theorem dotPar_getD_combineRows_dual (n : Nat) :
    ∀ (xs zs : List (List Bool)) (c : List Bool) (p : Nat),
    DualLists n xs zs → c.length = xs.length → p < zs.length →
    dotPar (zs.getD p []) (combineRows n xs c) % 2 = if c.getD p false then 1 else 0
  | [], [], _, _, _, _, hp => absurd hp (Nat.not_lt_zero _)
  | [], _ :: _, _, _, h, _, _ => nomatch h
  | _ :: _, [], _, _, h, _, _ => nomatch h
  | _ :: _, _ :: _, [], _, _, h, _ => nomatch h
  | x :: xs, z :: zs, b :: cs, 0, hd, _, _ => by
      obtain ⟨hx, _, hxz, _, hzxs, hdual⟩ := hd
      have hl := dualLists_lengths n xs zs hdual
      have e : dotPar z (combineRows n xs cs) % 2 = 0 :=
        dotPar_combineRows_even n z xs cs hl.1 hzxs
      cases b with
      | true =>
          show dotPar z (xorVec x (combineRows n xs cs)) % 2 = 1
          have a := dotPar_xorVec z x (combineRows n xs cs)
            (by rw [hx, combineRows_length n xs cs hl.1])
          have hzx : dotPar z x % 2 = 1 := by rw [dotPar_comm]; exact hxz
          omega
      | false =>
          show dotPar z (combineRows n xs cs) % 2 = 0
          exact e
  | x :: xs, z :: zs, b :: cs, p + 1, hd, hc, hp => by
      obtain ⟨hx, _, _, hxzs, _, hdual⟩ := hd
      have hl := dualLists_lengths n xs zs hdual
      have hp' : p < zs.length := Nat.lt_of_succ_lt_succ hp
      have ih := dotPar_getD_combineRows_dual n xs zs cs p hdual (Nat.succ.inj hc) hp'
      cases b with
      | true =>
          show dotPar (zs.getD p []) (xorVec x (combineRows n xs cs)) % 2 =
            if cs.getD p false then 1 else 0
          have a := dotPar_xorVec (zs.getD p []) x (combineRows n xs cs)
            (by rw [hx, combineRows_length n xs cs hl.1])
          have e : dotPar (zs.getD p []) x % 2 = 0 := by
            rw [dotPar_comm]
            exact hxzs _ (getD_mem [] zs p hp')
          rw [← ih]
          omega
      | false =>
          show dotPar (zs.getD p []) (combineRows n xs cs) % 2 =
            if cs.getD p false then 1 else 0
          exact ih

/-- The representatives of the two sectors, as vectors, are dual. -/
theorem dualLists_repVecs (I : CodeState) (hI : EncodingWellFormed I)
    (repsX repsZ : List (List Nat)) (hk : repsZ.length = repsX.length)
    (hX : ∀ sup ∈ repsX, sup.Nodup ∧ ∀ q ∈ sup, q ∈ I.Q)
    (hdual : ∀ p p', p < repsX.length → p' < repsX.length →
      supportIntersectionSize (repsX.getD p []) (repsZ.getD p' []) % 2 =
        if p = p' then 1 else 0) :
    DualLists I.Q.length (repVecs I repsX) (repVecs I repsZ) := by
  apply dualLists_of_indexed _ _ _ (by
    unfold repVecs
    rw [List.length_map, List.length_map, hk]) (length_repVecs I repsX) (length_repVecs I repsZ)
  intro p p' hp hp'
  have hp1 : p < repsX.length := by
    unfold repVecs at hp
    rw [List.length_map] at hp
    exact hp
  have hp1' : p' < repsX.length := by
    unfold repVecs at hp'
    rw [List.length_map] at hp'
    exact hp'
  unfold repVecs
  rw [getD_map_lt _ [] [] repsX p hp1, getD_map_lt _ [] [] repsZ p' (by rw [hk]; exact hp1')]
  have hx := hX _ (getD_mem [] repsX p hp1)
  rw [← supportIntersectionSize_eq_dotPar I.Q _ _ hI.1 hx.1 hx.2]
  exact hdual p p' hp1 hp1'

/-! ## Overlaps of the natural rows of `A-CONCAT` -/

/-- Two rows carried on copies `j` and `j2` have even overlap when the
    copies differ or the two rows have even overlap. -/
theorem dotPar_concatInner_even (I : CodeState) (nb j j2 : Nat) (r r2 : Row)
    (h : j = j2 → dotPar (rowVector I.Q r) (rowVector I.Q r2) % 2 = 0) :
    dotPar (concatInner I nb j r) (concatInner I nb j2 r2) % 2 = 0 := by
  unfold concatInner
  rw [dotPar_flatMap _ _ _ (fun j' _ => by
    rw [length_concatInner_block, length_concatInner_block])]
  apply sum_map_even
  intro j' _
  show dotPar (if j' = j then rowVector I.Q r else List.replicate I.Q.length false)
    (if j' = j2 then rowVector I.Q r2 else List.replicate I.Q.length false) % 2 = 0
  rcases Decidable.em (j' = j) with h1 | h1
  · rcases Decidable.em (j' = j2) with h2 | h2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true h2)]
      exact h (h1.symm.trans h2)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), dotPar_replicate_false]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), dotPar_comm, dotPar_replicate_false]

/-- A row carried on copy `j` meets a lifted outer row on that copy only. -/
theorem dotPar_concatInner_concatOuter (I : CodeState) (blocks reps : List (List Nat))
    (j : Nat) (hj : j < blocks.length) (r r' : Row) :
    dotPar (concatInner I blocks.length j r) (concatOuter I blocks reps r') =
      dotPar (rowVector I.Q r) (combineRows I.Q.length (repVecs I reps)
        ((blocks.getD j []).map (fun q => r'.support.contains q))) := by
  unfold concatInner concatOuter
  rw [flatMap_range_getD [] (fun B =>
    combineRows I.Q.length (repVecs I reps) (B.map (fun q => r'.support.contains q))) blocks]
  rw [dotPar_flatMap _ _ _ (fun j' _ => by
    rw [combineRows_length _ _ _ (length_repVecs I reps), length_concatInner_block])]
  apply sum_map_point j _ _ (List.range blocks.length) (nodup_range_cf _)
    (List.mem_range.mpr hj)
  intro j' _
  show dotPar (if j' = j then rowVector I.Q r else List.replicate I.Q.length false)
      (combineRows I.Q.length (repVecs I reps)
        ((blocks.getD j' []).map (fun q => r'.support.contains q))) =
    if j' = j then dotPar (rowVector I.Q r) (combineRows I.Q.length (repVecs I reps)
        ((blocks.getD j []).map (fun q => r'.support.contains q))) else 0
  rcases Decidable.em (j' = j) with h1 | h1
  · rw [h1, ite_eq_left_of_eq_true _ _ (eq_self j), ite_eq_left_of_eq_true _ _ (eq_self j)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h1),
      dotPar_comm, dotPar_replicate_false]

theorem map_range_getD {α β : Type} (d : α) (G : α → β) (L : List α) :
    L.map G = (List.range L.length).map (fun i => G (L.getD i d)) := by
  have h : L.map G = ((List.range L.length).map (fun i => L.getD i d)).map G := by
    rw [map_getD_range_gen d L]
  rw [h, List.map_map]
  rfl

theorem flatMap_congr_mem {α β : Type} (f g : α → List β) : ∀ L : List α,
    (∀ a ∈ L, f a = g a) → L.flatMap f = L.flatMap g
  | [], _ => rfl
  | a :: L, h => by
      rw [List.flatMap_cons, List.flatMap_cons, h a (List.mem_cons_self ..),
        flatMap_congr_mem f g L (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- The test vectors that separate the lifted outer rows from the inner
    rows: every representative of `reps'` on every copy. -/
def concatTests (I : CodeState) (nb : Nat) (reps' : List (List Nat)) : List (List Bool) :=
  (List.range nb).flatMap (fun j =>
    reps'.map (fun sup => concatInner I nb j ⟨0, Sector.X, sup⟩))

/-- The overlap parities of a lifted outer row with the dual representatives
    on every copy are its vector over the block labels. -/
theorem pairVec_concatOuter (I : CodeState) (blocks reps reps' : List (List Nat))
    (hD : DualLists I.Q.length (repVecs I reps) (repVecs I reps'))
    (hB : ∀ B ∈ blocks, B.length = reps'.length) (hk : reps.length = reps'.length)
    (r : Row) :
    pairVec (concatTests I blocks.length reps') (concatOuter I blocks reps r) =
      rowVector blocks.flatten r := by
  have hR : rowVector blocks.flatten r =
      (List.range blocks.length).flatMap (fun j =>
        (blocks.getD j []).map (fun q => r.support.contains q)) := by
    unfold rowVector
    rw [List.map_flatten, ← List.flatMap_def]
    exact flatMap_range_getD [] _ blocks
  rw [hR]
  unfold pairVec concatTests
  rw [List.map_flatMap]
  apply flatMap_congr_mem
  intro j hj
  have hj' : j < blocks.length := List.mem_range.mp hj
  have hBj : (blocks.getD j []).length = reps'.length := hB _ (getD_mem [] blocks j hj')
  show (reps'.map (fun sup => concatInner I blocks.length j ⟨0, Sector.X, sup⟩)).map
      (fun t => decide (dotPar t (concatOuter I blocks reps r) % 2 = 1)) =
    (blocks.getD j []).map (fun q => r.support.contains q)
  rw [List.map_map, map_range_getD [] _ reps',
    map_range_getD 0 (fun q => r.support.contains q) (blocks.getD j []), hBj]
  apply List.map_congr_left
  intro p hp
  have hp' : p < reps'.length := List.mem_range.mp hp
  show decide (dotPar (concatInner I blocks.length j ⟨0, Sector.X, reps'.getD p []⟩)
      (concatOuter I blocks reps r) % 2 = 1) =
    r.support.contains ((blocks.getD j []).getD p 0)
  rw [dotPar_concatInner_concatOuter I blocks reps j hj']
  have e : rowVector I.Q ⟨0, Sector.X, reps'.getD p []⟩ = (repVecs I reps').getD p [] := by
    unfold repVecs
    rw [getD_map_lt _ [] [] reps' p hp']
    rfl
  rw [e, dotPar_getD_combineRows_dual I.Q.length (repVecs I reps) (repVecs I reps') _ p hD
    (by unfold repVecs; rw [List.length_map, List.length_map, hBj, hk])
    (by unfold repVecs; rw [List.length_map]; exact hp'),
    getD_map_lt _ 0 false (blocks.getD j []) p (by rw [hBj]; exact hp')]
  cases r.support.contains ((blocks.getD j []).getD p 0) <;> rfl

/-! ## Row vectors over another list of labels -/

/-- Entry `q` of a combination of rows. -/
def combBit : List Row → List Bool → Nat → Bool
  | [], _, _ => false
  | _ :: _, [], _ => false
  | r :: rs, c :: cs, q => ((c && r.support.contains q) != combBit rs cs q)

theorem combineRows_rowVector (Q : List Nat) : ∀ (rows : List Row) (cs : List Bool),
    combineRows Q.length (rows.map (rowVector Q)) cs = Q.map (combBit rows cs)
  | [], cs => by
      rw [List.map_nil, combineRows_nil]
      exact (map_eq_replicate_false _ Q (fun _ _ => rfl)).symm
  | _ :: _, [] => (map_eq_replicate_false _ Q (fun _ _ => rfl)).symm
  | r :: rs, true :: cs => by
      show xorVec (rowVector Q r) (combineRows Q.length (rs.map (rowVector Q)) cs) =
        Q.map (combBit (r :: rs) (true :: cs))
      rw [combineRows_rowVector Q rs cs]
      unfold rowVector
      rw [xorVec_map_map_gen]
      rfl
  | r :: rs, false :: cs => by
      show combineRows Q.length (rs.map (rowVector Q)) cs =
        Q.map (combBit (r :: rs) (false :: cs))
      rw [combineRows_rowVector Q rs cs]
      exact List.map_congr_left (fun q _ => by
        show combBit rs cs q = ((false && r.support.contains q) != combBit rs cs q)
        cases combBit rs cs q <;> rfl)

/-- Independence of row vectors passes to any list of labels that contains
    the labels it was stated over. -/
theorem vecIndep_rowVector_of_subset (Q Q' : List Nat) (rows : List Row)
    (hsub : ∀ q ∈ Q, q ∈ Q') (h : VecIndep Q.length (rows.map (rowVector Q))) :
    VecIndep Q'.length (rows.map (rowVector Q')) := by
  intro cs hlen hzero
  rw [List.length_map] at hlen
  apply h cs (by rw [List.length_map]; exact hlen)
  rw [combineRows_rowVector] at hzero ⊢
  have hall := all_false_of_map_eq_replicate _ Q' hzero
  exact map_eq_replicate_false _ Q (fun q hq => hall q (hsub q hq))

/-! ## The natural rows of `A-CONCAT` are independent -/

/-- The natural rows of one sector of `A-CONCAT` are independent. -/
theorem vecIndep_concat (O I : CodeState) (blocks repsX repsZ : List (List Nat))
    (hO : EncodingWellFormed O) (hI : EncodingWellFormed I)
    (hty : concatTyped O I blocks repsX repsZ = true) (σ : Sector) :
    VecIndep (blocks.length * I.Q.length)
      ((List.range blocks.length).flatMap (fun j =>
          (sectorRows I σ).map (concatInner I blocks.length j)) ++
        (sectorRows O σ).map (concatOuter I blocks (concatReps repsX repsZ σ))) := by
  simp only [concatTyped, Bool.and_eq_true] at hty
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, t2⟩, _⟩, t4⟩, _⟩, _⟩, t7⟩, t8⟩, t9⟩, t10⟩, t11⟩ := hty
  have hk : repsZ.length = repsX.length := Nat.eq_of_beq_eq_true t2
  have hB : ∀ B ∈ blocks, B.length = repsX.length :=
    fun B hBm => Nat.eq_of_beq_eq_true (List.all_eq_true.mp t4 B hBm)
  have hsub : ∀ q ∈ O.Q, q ∈ blocks.flatten :=
    fun q hq => List.contains_iff_mem.mp (List.all_eq_true.mp t7 q hq)
  have hreps : ∀ sup ∈ repsX ++ repsZ, sup.Nodup ∧ ∀ q ∈ sup, q ∈ I.Q := by
    intro sup hsup
    have h := List.all_eq_true.mp t8 sup hsup
    rw [Bool.and_eq_true] at h
    exact ⟨of_decide_eq_true h.1,
      fun q hq => List.contains_iff_mem.mp (List.all_eq_true.mp h.2 q hq)⟩
  have hcX : ∀ sup ∈ repsX, ∀ ρ ∈ I.rows, ρ.sector = Sector.Z →
      supportIntersectionSize sup ρ.support % 2 = 0 := by
    intro sup hsup ρ hρ hsec
    have h := List.all_eq_true.mp (List.all_eq_true.mp t9 sup hsup) ρ hρ
    rw [hsec, Bool.or_eq_true] at h
    rcases h with h | h
    · exact absurd h (by decide)
    · exact Nat.eq_of_beq_eq_true h
  have hcZ : ∀ sup ∈ repsZ, ∀ ρ ∈ I.rows, ρ.sector = Sector.X →
      supportIntersectionSize sup ρ.support % 2 = 0 := by
    intro sup hsup ρ hρ hsec
    have h := List.all_eq_true.mp (List.all_eq_true.mp t10 sup hsup) ρ hρ
    rw [hsec, Bool.or_eq_true] at h
    rcases h with h | h
    · exact absurd h (by decide)
    · exact Nat.eq_of_beq_eq_true h
  have hdual : ∀ p p', p < repsX.length → p' < repsX.length →
      supportIntersectionSize (repsX.getD p []) (repsZ.getD p' []) % 2 =
        if p = p' then 1 else 0 := by
    intro p p' hp hp'
    have h := List.all_eq_true.mp (List.all_eq_true.mp t11 p (List.mem_range.mpr hp)) p'
      (List.mem_range.mpr hp')
    have h' := eq_of_beq h
    rcases Decidable.em (p = p') with e | e
    · rw [ite_eq_left_of_eq_true _ _ (eq_true e)]
      rw [beq_iff_eq.mpr e] at h'
      exact Nat.eq_of_beq_eq_true h'
    · rw [ite_eq_right_of_eq_false _ _ (eq_false e)]
      rw [beq_eq_false_iff_ne.mpr e] at h'
      have hne := beq_eq_false_iff_ne.mp h'
      omega
  have hD := dualLists_repVecs I hI repsX repsZ hk
    (fun sup hsup => hreps sup (List.mem_append_left _ hsup)) hdual
  have hσ : ∃ reps' : List (List Nat),
      DualLists I.Q.length (repVecs I (concatReps repsX repsZ σ)) (repVecs I reps') ∧
      (∀ B ∈ blocks, B.length = reps'.length) ∧
      (concatReps repsX repsZ σ).length = reps'.length ∧
      (∀ sup ∈ reps', ∀ ρ ∈ sectorRows I σ, sup.Nodup ∧ (∀ q ∈ sup, q ∈ I.Q) ∧
        supportIntersectionSize sup ρ.support % 2 = 0) := by
    cases σ with
    | X =>
        refine ⟨repsZ, hD, fun B hBm => (hB B hBm).trans hk.symm, hk.symm, ?_⟩
        intro sup hsup ρ hρ
        have hr := hreps sup (List.mem_append_right _ hsup)
        have hρ' := List.mem_filter.mp hρ
        exact ⟨hr.1, hr.2, hcZ sup hsup ρ hρ'.1 (of_decide_eq_true hρ'.2)⟩
    | Z =>
        refine ⟨repsX, dualLists_symm _ _ _ hD, hB, hk, ?_⟩
        intro sup hsup ρ hρ
        have hr := hreps sup (List.mem_append_left _ hsup)
        have hρ' := List.mem_filter.mp hρ
        exact ⟨hr.1, hr.2, hcX sup hsup ρ hρ'.1 (of_decide_eq_true hρ'.2)⟩
  obtain ⟨reps', hDσ, hBσ, hkσ, hcomm⟩ := hσ
  have hT : ∀ r : Row, pairVec (concatTests I blocks.length reps')
      (concatOuter I blocks (concatReps repsX repsZ σ) r) = rowVector blocks.flatten r :=
    pairVec_concatOuter I blocks _ reps' hDσ hBσ hkσ
  have hTlen : (concatTests I blocks.length reps').length = blocks.flatten.length := by
    have h := congrArg List.length (hT ⟨0, Sector.X, []⟩)
    unfold pairVec at h
    rw [List.length_map, rowVector_length] at h
    exact h
  apply vecIndep_append_of_kill_left
    (additive_pairVec (blocks.length * I.Q.length) (concatTests I blocks.length reps'))
  · intro v hv
    obtain ⟨j, _, hm⟩ := List.mem_flatMap.mp hv
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hm
    exact length_concatInner I _ j r
  · intro v hv
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hv
    exact length_concatOuter I blocks _ r
  · intro v hv
    obtain ⟨j2, _, hm⟩ := List.mem_flatMap.mp hv
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
    unfold pairVec
    apply map_eq_replicate_false
    intro t ht
    unfold concatTests at ht
    obtain ⟨j, _, hm2⟩ := List.mem_flatMap.mp ht
    obtain ⟨sup, hsup, rfl⟩ := List.mem_map.mp hm2
    obtain ⟨hnd, hsubI, hev⟩ := hcomm sup hsup r hr
    have h0 : dotPar (concatInner I blocks.length j ⟨0, Sector.X, sup⟩)
        (concatInner I blocks.length j2 r) % 2 = 0 :=
      dotPar_concatInner_even I blocks.length j j2 _ r (fun _ => by
        show dotPar (I.Q.map (fun q => sup.contains q))
          (I.Q.map (fun q => r.support.contains q)) % 2 = 0
        rw [← supportIntersectionSize_eq_dotPar I.Q sup r.support hI.1 hnd hsubI]
        exact hev)
    show decide (dotPar (concatInner I blocks.length j ⟨0, Sector.X, sup⟩)
      (concatInner I blocks.length j2 r) % 2 = 1) = false
    rw [h0]
    rfl
  · rw [List.map_map]
    have e : (sectorRows O σ).map (pairVec (concatTests I blocks.length reps') ∘
        concatOuter I blocks (concatReps repsX repsZ σ)) =
        (sectorRows O σ).map (rowVector blocks.flatten) :=
      List.map_congr_left (fun r _ => hT r)
    rw [e, hTlen]
    exact vecIndep_rowVector_of_subset O.Q blocks.flatten _ hsub (vecIndep_sectorRows O hO σ)
  · exact vecIndep_concatInner I hI σ blocks.length (List.range blocks.length)
      (nodup_range_cf _) (fun j hj => List.mem_range.mp hj)

/-! ## Retention and `k` -/

theorem filter_tagged_rows (σ : Sector) (G : Sector → Row → List Bool) : ∀ L : List Row,
    ((L.map (fun r => (r.sector, G r.sector r))).filter (fun x => x.1 = σ)).map Prod.snd =
      (L.filter (fun r => r.sector = σ)).map (G σ)
  | [] => rfl
  | r :: L => by
      have ih := filter_tagged_rows σ G L
      rcases Decidable.em (r.sector = σ) with h | h
      · rw [List.map_cons, List.filter_cons_of_pos (by exact decide_eq_true h),
          List.filter_cons_of_pos (by exact decide_eq_true h), List.map_cons, List.map_cons,
          ih, h]
      · rw [List.map_cons,
          List.filter_cons_of_neg (by rw [Bool.not_eq_true]; exact decide_eq_false h),
          List.filter_cons_of_neg (by rw [Bool.not_eq_true]; exact decide_eq_false h), ih]

/-- The natural rows of one sector of `A-CONCAT`: the inner rows of that
    sector copy by copy, then the lifted outer rows of that sector. -/
theorem concat_filter (O I : CodeState) (blocks repsX repsZ : List (List Nat)) (σ : Sector) :
    ((concatVectors O I blocks repsX repsZ).filter (fun x => x.1 = σ)).map Prod.snd =
      (List.range blocks.length).flatMap (fun j =>
          (sectorRows I σ).map (concatInner I blocks.length j)) ++
        (sectorRows O σ).map (concatOuter I blocks (concatReps repsX repsZ σ)) := by
  rw [concatVectors_eq, List.filter_append, List.map_append]
  have h1 : ∀ L : List Nat,
      ((L.flatMap (fun j => I.rows.map (fun r =>
        (r.sector, concatInner I blocks.length j r)))).filter (fun x => x.1 = σ)).map Prod.snd =
      L.flatMap (fun j => (sectorRows I σ).map (concatInner I blocks.length j)) := by
    intro L
    induction L with
    | nil => rfl
    | cons j L ih =>
        rw [List.flatMap_cons, List.filter_append, List.map_append, List.flatMap_cons, ih]
        exact congrArg (· ++ _)
          (filter_tagged_rows σ (fun _ r => concatInner I blocks.length j r) I.rows)
  rw [h1]
  exact congrArg (_ ++ ·)
    (filter_tagged_rows σ (fun τ r => concatOuter I blocks (concatReps repsX repsZ τ) r) O.rows)

/-- The retained display of `A-CONCAT` drops no natural row. -/
theorem concatState_rows_length (O I : CodeState) (blocks repsX repsZ : List (List Nat))
    (hO : EncodingWellFormed O) (hI : EncodingWellFormed I)
    (hty : concatTyped O I blocks repsX repsZ = true) :
    (concatState O I blocks repsX repsZ).rows.length =
      (concatVectors O I blocks repsX repsZ).length := by
  unfold concatState
  apply constructedState_rows_length_of_indep _ _
    (concat_naturalOrthogonal O I blocks repsX repsZ hO hI hty)
  · intro x hx
    rw [concatVectors_eq] at hx
    unfold concatQubits
    rcases List.mem_append.mp hx with h1 | h1
    · obtain ⟨j, _, hm⟩ := List.mem_flatMap.mp h1
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hm
      rw [Nat.mul_comm]
      exact length_concatInner I _ j r
    · obtain ⟨r, _, rfl⟩ := List.mem_map.mp h1
      rw [Nat.mul_comm]
      exact length_concatOuter I blocks _ r
  · intro σ
    rw [concat_filter]
    unfold concatQubits
    rw [Nat.mul_comm]
    exact vecIndep_concat O I blocks repsX repsZ hO hI hty σ

/-- Closed form for the logical count of `A-CONCAT`: it is the outer
    code's `k`. -/
theorem concatState_k_closed (O I : CodeState) (blocks repsX repsZ : List (List Nat))
    (hO : EncodingWellFormed O) (hI : EncodingWellFormed I)
    (hty : concatTyped O I blocks repsX repsZ = true) :
    stateK (concatState O I blocks repsX repsZ) = stateK O :=
  concatState_k_of_retention O I blocks repsX repsZ hO hI hty
    (concatState_rows_length O I blocks repsX repsZ hO hI hty)

theorem evalExpr_concat_k {eO eI : StateExpr} {blocks repsX repsZ : List (List Nat)}
    {s : CodeState}
    (h : EvalExpr (StateExpr.concat eO eI blocks repsX repsZ) s) :
    ∃ sO, EvalExpr eO sO ∧ stateK s = stateK sO := by
  cases h with
  | concat hO hI hty _ hEvalO hEvalI =>
      exact ⟨_, hEvalO, concatState_k_closed _ _ blocks repsX repsZ hO hI hty⟩

end CodeCalculus
