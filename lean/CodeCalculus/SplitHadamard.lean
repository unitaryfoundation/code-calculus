import CodeCalculus.Gate6Soundness

/-!
# The split-subset `E-LOCAL-HADAMARD` and the exact distance (issue #571)

`spec/OPERATIONAL_SEMANTICS.md` §4.27(b) derives, for the split-subset
instance `∅ ⊊ T ⊊ Q` under the row-space splitting guard, that the full
distance is unchanged and that each child sector distance is at least the
parent's full distance. This module proves both for the exact sector
distance of `ExactDistance.lean`, from the state update `splitHadamardState`
and the guard `splitGuard` of `Eval.lean`.

The argument has three parts.

* **Projection algebra.** `projVec m v` keeps the coordinates of `v` where the
  Boolean mask `m` is set. The masks `tMask Q T` and `rMask Q T` select `T`
  and `Q ∖ T`. Restriction is linear, moves across the overlap parity, and
  does not raise the weight, and every vector is the sum of its two
  restrictions.
* **The update's spans.** Every child row is the outer piece of a parent row
  in its own sector or the inner piece of a parent row of the other sector
  (`splitRow_origin`). Conversely, every piece of every parent row lies in the
  span of the child rows of its output sector (`piece_inSpan_child`): the
  greedy selection keeps a basis of the offered pieces. The guard puts the
  inner piece of each parent row in its own sector's span (`guard_inner`).
* **Distances.** A child σ-logical restricts to a parent σ-logical on
  `Q ∖ T` or to a parent σ̄-logical on `T`. This needs no guard, and gives
  `d_σ' ≥ d`. A parent σ-logical restricts to a child σ-logical on `Q ∖ T` or
  to a child σ̄-logical on `T`. This uses the guard, and gives `d' ≤ d`.
-/

namespace CodeCalculus

/-! ## Projection algebra -/

/-- Keep the coordinates of `v` where the mask `m` is set. -/
def projVec (m v : List Bool) : List Bool := List.zipWith (· && ·) m v

/-- The mask of `T` over `Q`. -/
def tMask (Q T : List Nat) : List Bool := Q.map (fun q => T.contains q)

/-- The mask of `Q ∖ T` over `Q`. -/
def rMask (Q T : List Nat) : List Bool := Q.map (fun q => !T.contains q)

theorem projVec_length (m v : List Bool) (h : m.length = v.length) :
    (projVec m v).length = v.length := by
  unfold projVec
  rw [List.length_zipWith, h, Nat.min_self]

theorem projVec_xorVec : ∀ (m a b : List Bool), m.length = a.length → a.length = b.length →
    projVec m (xorVec a b) = xorVec (projVec m a) (projVec m b)
  | [], [], [], _, _ => rfl
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
      have ih := projVec_xorVec xs ys zs h1 h2
      simp only [projVec, xorVec, List.zipWith_cons_cons] at ih ⊢
      rw [ih]
      cases x <;> cases y <;> cases z <;> rfl
  | [], _ :: _, _, h, _ => nomatch h
  | _ :: _, [], _, h, _ => nomatch h
  | [], [], _ :: _, _, h => nomatch h
  | _ :: _, _ :: _, [], _, h => nomatch h

theorem projVec_replicate : ∀ (m : List Bool), projVec m (List.replicate m.length false) =
    List.replicate m.length false
  | [] => rfl
  | x :: xs => by
      have ih := projVec_replicate xs
      simp only [projVec, List.length_cons, List.replicate_succ, List.zipWith_cons_cons] at ih ⊢
      rw [ih]
      cases x <;> rfl

theorem projVec_combineRows (m : List Bool) :
    ∀ (vs : List (List Bool)) (cs : List Bool), (∀ v ∈ vs, v.length = m.length) →
      projVec m (combineRows m.length vs cs) = combineRows m.length (vs.map (projVec m)) cs
  | [], cs, _ => by
      cases cs <;> exact projVec_replicate m
  | v :: vs, [], _ => projVec_replicate m
  | v :: vs, true :: cs, h => by
      have hv : v.length = m.length := h v (List.mem_cons_self ..)
      have hvs : ∀ w ∈ vs, w.length = m.length := fun w hw => h w (List.mem_cons_of_mem v hw)
      show projVec m (xorVec v (combineRows m.length vs cs)) =
        xorVec (projVec m v) (combineRows m.length (vs.map (projVec m)) cs)
      rw [projVec_xorVec m v _ hv.symm (by rw [hv, combineRows_length _ _ _ hvs]),
        projVec_combineRows m vs cs hvs]
  | v :: vs, false :: cs, h => by
      have hvs : ∀ w ∈ vs, w.length = m.length := fun w hw => h w (List.mem_cons_of_mem v hw)
      exact projVec_combineRows m vs cs hvs

theorem projVec_idem : ∀ (m v : List Bool), projVec m (projVec m v) = projVec m v
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
      have ih := projVec_idem xs ys
      simp only [projVec, List.zipWith_cons_cons] at ih ⊢
      rw [ih]
      cases x <;> cases y <;> rfl

theorem tMask_length (Q T : List Nat) : (tMask Q T).length = Q.length := by simp [tMask]
theorem rMask_length (Q T : List Nat) : (rMask Q T).length = Q.length := by simp [rMask]

/-- Restricting to `Q ∖ T` after `T` gives zero. -/
theorem projVec_r_t : ∀ (Q : List Nat) (T : List Nat) (v : List Bool), v.length = Q.length →
    projVec (rMask Q T) (projVec (tMask Q T) v) = List.replicate Q.length false
  | [], _, _, _ => rfl
  | q :: qs, T, b :: bs, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      have ih := projVec_r_t qs T bs h
      simp only [projVec, rMask, tMask, List.map_cons, List.zipWith_cons_cons,
        List.length_cons, List.replicate_succ] at ih ⊢
      rw [ih]
      cases T.contains q <;> cases b <;> rfl
  | _ :: _, _, [], h => nomatch h

/-- Restricting to `T` after `Q ∖ T` gives zero. -/
theorem projVec_t_r : ∀ (Q : List Nat) (T : List Nat) (v : List Bool), v.length = Q.length →
    projVec (tMask Q T) (projVec (rMask Q T) v) = List.replicate Q.length false
  | [], _, _, _ => rfl
  | q :: qs, T, b :: bs, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      have ih := projVec_t_r qs T bs h
      simp only [projVec, rMask, tMask, List.map_cons, List.zipWith_cons_cons,
        List.length_cons, List.replicate_succ] at ih ⊢
      rw [ih]
      cases T.contains q <;> cases b <;> rfl
  | _ :: _, _, [], h => nomatch h

/-- Every vector is the sum of its two restrictions. -/
theorem xorVec_projVec_t_r : ∀ (Q : List Nat) (T : List Nat) (v : List Bool), v.length = Q.length →
    xorVec (projVec (tMask Q T) v) (projVec (rMask Q T) v) = v
  | [], _, [], _ => rfl
  | q :: qs, T, b :: bs, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      have ih := xorVec_projVec_t_r qs T bs h
      simp only [projVec, rMask, tMask, List.map_cons, List.zipWith_cons_cons, xorVec] at ih ⊢
      rw [ih]
      cases T.contains q <;> cases b <;> rfl
  | [], _, _ :: _, h => nomatch h
  | _ :: _, _, [], h => nomatch h

/-- The overlap parity moves across a restriction. -/
theorem dotPar_projVec : ∀ (m a b : List Bool), m.length = a.length → a.length = b.length →
    dotPar (projVec m a) b = dotPar a (projVec m b)
  | [], [], [], _, _ => rfl
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
      have ih := dotPar_projVec xs ys zs h1 h2
      simp only [projVec, dotPar, List.zipWith_cons_cons] at ih ⊢
      rw [ih]
      cases x <;> cases y <;> cases z <;> rfl
  | [], _ :: _, _, h, _ => nomatch h
  | _ :: _, [], _, h, _ => nomatch h
  | [], [], _ :: _, _, h => nomatch h
  | _ :: _, _ :: _, [], _, h => nomatch h

/-- A restriction to `T` and one to `Q ∖ T` have no common support. -/
theorem dotPar_projVec_t_r : ∀ (Q : List Nat) (T : List Nat) (a b : List Bool),
    dotPar (projVec (tMask Q T) a) (projVec (rMask Q T) b) = 0
  | [], _, _, _ => by simp [projVec, tMask, dotPar]
  | _ :: _, _, [], _ => by simp [projVec, tMask, dotPar]
  | _ :: _, _, _ :: _, [] => by simp [projVec, rMask, dotPar]
  | q :: qs, T, x :: xs, y :: ys => by
      have ih := dotPar_projVec_t_r qs T xs ys
      simp only [projVec, rMask, tMask, List.map_cons, List.zipWith_cons_cons, dotPar] at ih ⊢
      rw [ih]
      cases T.contains q <;> cases x <;> cases y <;> rfl

theorem dotPar_projVec_r_t (Q T : List Nat) (a b : List Bool) (ha : a.length = Q.length)
    (hb : b.length = Q.length) :
    dotPar (projVec (rMask Q T) a) (projVec (tMask Q T) b) = 0 := by
  rw [dotPar_projVec (rMask Q T) a _ (by rw [rMask_length, ha])
    (by rw [projVec_length _ _ (by rw [tMask_length, hb]), ha, hb]),
    projVec_r_t Q T b hb]
  exact dotPar_replicate_false a Q.length

/-- A restriction does not raise the weight. -/
theorem weight_projVec_le : ∀ (m v : List Bool), weight (projVec m v) ≤ weight v
  | [], v => by simp [projVec, weight]
  | _ :: _, [] => by simp [projVec, weight]
  | x :: xs, y :: ys => by
      have ih := weight_projVec_le xs ys
      simp only [projVec, weight, List.zipWith_cons_cons, List.count_cons] at ih ⊢
      cases x <;> cases y <;> simp <;> omega

/-! ## Spans over vectors -/

theorem splitInSpan_zero (Q : List Nat) (rows : List Row) :
    inSpanRows Q rows (List.replicate Q.length false) :=
  ⟨List.replicate rows.length false, List.length_replicate ..,
    by
      have h := combineRows_zero_coeffs Q.length (rows.map (rowVector Q))
      rw [List.length_map] at h
      exact h⟩

/-- Span transitivity: if every row of `A` lies in the span of `B`, so does
    every vector of the span of `A`. -/
theorem inSpanRows_trans (Q : List Nat) (B : List Row) :
    ∀ (A : List Row) (v : List Bool), inSpanRows Q A v →
      (∀ r ∈ A, inSpanRows Q B (rowVector Q r)) → inSpanRows Q B v
  | [], v, ⟨cs, _, hv⟩, _ => by
      rw [← hv]
      cases cs <;> exact splitInSpan_zero Q B
  | r :: rs, v, ⟨cs, hlen, hv⟩, h => by
      have hrs : ∀ r' ∈ rs, inSpanRows Q B (rowVector Q r') :=
        fun r' hr' => h r' (List.mem_cons_of_mem r hr')
      cases cs with
      | nil => nomatch hlen
      | cons c cs =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          have hrest : inSpanRows Q B (combineRows Q.length (rs.map (rowVector Q)) cs) :=
            inSpanRows_trans Q B rs _ ⟨cs, hlen, rfl⟩ hrs
          rw [← hv]
          cases c with
          | true =>
              exact inSpanRows_xor Q B (h r (List.mem_cons_self ..)) hrest
          | false => exact hrest

/-! ## The pieces of a row -/

/-- `p` is a piece of `r` landing in output sector `τ`: the outer piece in the
    row's own sector, or the inner piece in the opposite sector. -/
def IsPiece (T : List Nat) (r : Row) (τ : Sector) (p : List Nat) : Prop :=
  (τ = r.sector ∧ p = outerPiece T r.support) ∨
  (τ = oppositeSector r.sector ∧ p = innerPiece T r.support)

theorem pieceMask_nil (Q : List Nat) : pieceMask Q [] = 0 := rfl

theorem rowBitmask_eq_pieceMask (Q : List Nat) (r : Row) :
    rowBitmask Q r = pieceMask Q r.support := rfl

theorem outerPiece_eq_of_inner_nil {T : List Nat} :
    ∀ {sup : List Nat}, innerPiece T sup = [] → outerPiece T sup = sup
  | [], _ => rfl
  | a :: l, h => by
      unfold innerPiece at h
      unfold outerPiece
      cases ha : T.contains a with
      | true =>
          rw [List.filter_cons_of_pos (p := fun q => T.contains q) ha] at h
          exact nomatch h
      | false =>
          rw [List.filter_cons_of_neg (p := fun q => T.contains q) (by rw [ha]; decide)] at h
          rw [List.filter_cons_of_pos (by rw [ha]; decide)]
          exact congrArg (a :: ·) (outerPiece_eq_of_inner_nil h)

theorem innerPiece_eq_of_outer_nil {T : List Nat} :
    ∀ {sup : List Nat}, outerPiece T sup = [] → innerPiece T sup = sup
  | [], _ => rfl
  | a :: l, h => by
      unfold outerPiece at h
      unfold innerPiece
      cases ha : T.contains a with
      | false =>
          rw [List.filter_cons_of_pos (by rw [ha]; decide)] at h
          exact nomatch h
      | true =>
          rw [List.filter_cons_of_neg (by rw [ha]; decide)] at h
          rw [List.filter_cons_of_pos (p := fun q => T.contains q) ha]
          exact congrArg (a :: ·) (innerPiece_eq_of_outer_nil h)

/-- The nonempty piece of a pure row is its whole support, in its output
    sector; the other piece is empty. -/
theorem pure_piece {T : List Nat} {r : Row} (hp : isPureRow T r = true) {τ : Sector}
    {p : List Nat} (h : IsPiece T r τ p) :
    p = [] ∨ (τ = pureSector T r ∧ p = r.support) := by
  unfold isPureRow at hp
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · by_cases ho : outerPiece T r.support = []
    · exact Or.inl ho
    · right
      have hi : innerPiece T r.support = [] := by
        rcases Bool.or_eq_true_iff.mp hp with h | h
        · exact List.isEmpty_iff.mp h
        · exact absurd (List.isEmpty_iff.mp h) ho
      refine ⟨?_, outerPiece_eq_of_inner_nil hi⟩
      unfold pureSector
      rw [if_neg]
      rintro ⟨_, h2⟩
      exact h2 (by rw [hi]; rfl)
  · by_cases hi : innerPiece T r.support = []
    · exact Or.inl hi
    · right
      have ho : outerPiece T r.support = [] := by
        rcases Bool.or_eq_true_iff.mp hp with h | h
        · exact absurd (List.isEmpty_iff.mp h) hi
        · exact List.isEmpty_iff.mp h
      refine ⟨?_, innerPiece_eq_of_outer_nil ho⟩
      unfold pureSector
      rw [if_pos ⟨by rw [ho]; rfl, by intro h; exact hi (List.isEmpty_iff.mp (by simpa using h))⟩]

/-! ## One piece step -/

theorem basisFor_insertFor_same (xb zb : List Nat) (τ : Sector) (m : Nat) :
    basisFor (insertFor xb zb τ m).1 (insertFor xb zb τ m).2 τ =
      insertBasis (basisFor xb zb τ) m := by
  cases τ <;> rfl

theorem basisFor_insertFor_other (xb zb : List Nat) {τ τ' : Sector} (h : τ' ≠ τ) (m : Nat) :
    basisFor (insertFor xb zb τ m).1 (insertFor xb zb τ m).2 τ' = basisFor xb zb τ' := by
  cases τ <;> cases τ' <;> first | rfl | exact absurd rfl h

/-- The offered piece lies in the span of its sector's basis after the step. -/
theorem pieceStep_mem (Q : List Nat) (b : List Nat × List Nat) (τ : Sector) (p : List Nat) :
    inSpanMasks (basisFor (pieceStep Q b τ p).2.1 (pieceStep Q b τ p).2.2 τ) (pieceMask Q p) := by
  unfold pieceStep
  split
  · rename_i h
    obtain ⟨v', hv', hx⟩ := reduceByBasis_sound (basisFor b.1 b.2 τ) (pieceMask Q p)
    rw [h] at hx
    rw [xor_eq_zero_cancel hx.symm]
    exact hv'
  · rw [basisFor_insertFor_same]
    exact (spanEq_insertBasis _ _ _).mpr (inSpanMasks_of_mem (List.mem_cons_self ..))

/-- A step only grows each basis's span. -/
theorem pieceStep_mono (Q : List Nat) (b : List Nat × List Nat) (τ : Sector) (p : List Nat)
    (τ' : Sector) {v : Nat} (h : inSpanMasks (basisFor b.1 b.2 τ') v) :
    inSpanMasks (basisFor (pieceStep Q b τ p).2.1 (pieceStep Q b τ p).2.2 τ') v := by
  unfold pieceStep
  split
  · exact h
  · by_cases hτ : τ' = τ
    · subst hτ
      rw [basisFor_insertFor_same]
      exact (spanEq_insertBasis _ _ _).mpr (inSpanMasks_cons_zero h)
    · rw [basisFor_insertFor_other _ _ hτ]
      exact h

/-- A step leaves the other sector's basis unchanged. -/
theorem pieceStep_other (Q : List Nat) (b : List Nat × List Nat) {τ τ' : Sector} (h : τ' ≠ τ)
    (p : List Nat) :
    basisFor (pieceStep Q b τ p).2.1 (pieceStep Q b τ p).2.2 τ' = basisFor b.1 b.2 τ' := by
  unfold pieceStep
  split
  · rfl
  · exact basisFor_insertFor_other _ _ h _

/-- A step's basis is spanned by the old basis and, if the piece is kept, the
    piece. -/
theorem pieceStep_gen (Q : List Nat) (b : List Nat × List Nat) (τ : Sector) (p : List Nat)
    {v : Nat} (h : inSpanMasks (basisFor (pieceStep Q b τ p).2.1 (pieceStep Q b τ p).2.2 τ) v) :
    inSpanMasks (basisFor b.1 b.2 τ ++
      (if (pieceStep Q b τ p).1 then [pieceMask Q p] else [])) v := by
  unfold pieceStep at h ⊢
  by_cases hr : reduceByBasis (basisFor b.1 b.2 τ) (pieceMask Q p) = 0
  · simp only [hr, if_true] at h ⊢
    simpa using h
  · simp only [hr, if_false] at h ⊢
    rw [basisFor_insertFor_same] at h
    have h' := (spanEq_insertBasis _ _ _).mp h
    refine inSpanMasks_trans (fun g hg => ?_) h'
    rcases List.mem_cons.mp hg with rfl | hg
    · exact inSpanMasks_append_left (inSpanMasks_of_mem (List.mem_singleton_self _))
    · exact inSpanMasks_append_right (inSpanMasks_of_mem hg)

/-! ## The greedy invariants of pass 1 -/

/-- The masks of the entries of output sector `τ`. -/
def entryMasks (Q : List Nat) (τ : Sector) (E : List (Option Nat × Sector × List Nat)) :
    List Nat :=
  (E.filter (fun e => decide (e.2.1 = τ))).map (fun e => pieceMask Q e.2.2)

theorem mem_entryMasks {Q : List Nat} {τ : Sector} {E : List (Option Nat × Sector × List Nat)}
    {e : Option Nat × Sector × List Nat} (he : e ∈ E) (hτ : e.2.1 = τ) :
    pieceMask Q e.2.2 ∈ entryMasks Q τ E :=
  List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he, by simp [hτ]⟩, rfl⟩

theorem entryMasks_append (Q : List Nat) (τ : Sector) (E F : List (Option Nat × Sector × List Nat)) :
    entryMasks Q τ (E ++ F) = entryMasks Q τ E ++ entryMasks Q τ F := by
  simp [entryMasks, List.filter_append]

theorem entryMasks_cons_sub (Q : List Nat) (τ : Sector) (e : Option Nat × Sector × List Nat)
    (E : List (Option Nat × Sector × List Nat)) {g : Nat} (h : g ∈ entryMasks Q τ E) :
    g ∈ entryMasks Q τ (e :: E) := by
  obtain ⟨e', he', rfl⟩ := List.mem_map.mp h
  exact List.mem_map.mpr ⟨e', List.mem_filter.mpr ⟨List.mem_cons_of_mem e (List.mem_filter.mp he').1,
    (List.mem_filter.mp he').2⟩, rfl⟩

/-- Enlarging the generators past a fixed prefix keeps span membership. -/
theorem inSpanMasks_append_mono {A C D : List Nat} {v : Nat} (h : inSpanMasks (A ++ C) v)
    (hCD : ∀ g ∈ C, g ∈ D) : inSpanMasks (A ++ D) v := by
  refine inSpanMasks_trans (fun g hg => ?_) h
  rcases List.mem_append.mp hg with hg | hg
  · exact inSpanMasks_append_right (inSpanMasks_of_mem hg)
  · exact inSpanMasks_append_left (inSpanMasks_of_mem (hCD g hg))

/-- The bases only grow along pass 1. -/
theorem splitFinal_mono (Q T : List Nat) :
    ∀ (rows : List Row) (b : List Nat × List Nat) (τ : Sector) {v : Nat},
      inSpanMasks (basisFor b.1 b.2 τ) v →
      inSpanMasks (basisFor (splitFinal Q T b rows).1 (splitFinal Q T b rows).2 τ) v
  | [], _, _, _, h => h
  | r :: rs, b, τ, v, h => by
      unfold splitFinal
      split
      · exact splitFinal_mono Q T rs b τ h
      · exact splitFinal_mono Q T rs _ τ (pieceStep_mono _ _ _ _ τ (pieceStep_mono _ _ _ _ τ h))

/-- The final bases are spanned by the initial bases and the emitted entries. -/
theorem splitFinal_gen (Q T : List Nat) :
    ∀ (rows : List Row) (b : List Nat × List Nat) (τ : Sector) {v : Nat},
      inSpanMasks (basisFor (splitFinal Q T b rows).1 (splitFinal Q T b rows).2 τ) v →
      inSpanMasks (basisFor b.1 b.2 τ ++ entryMasks Q τ (splitGo Q T b rows)) v
  | [], _, _, _, h => inSpanMasks_append_right h
  | r :: rs, b, τ, v, h => by
      unfold splitFinal at h
      unfold splitGo
      split
      · rename_i hp
        rw [if_pos hp] at h
        exact inSpanMasks_append_mono (splitFinal_gen Q T rs b τ h)
          (fun g hg => entryMasks_cons_sub Q τ _ _ hg)
      · rename_i hp
        rw [if_neg hp] at h
        have ih := splitFinal_gen Q T rs _ τ h
        rw [entryMasks_append]
        -- the generators of the step's basis
        refine inSpanMasks_trans (fun g hg => ?_) ih
        rcases List.mem_append.mp hg with hg | hg
        · have hgs := inSpanMasks_of_mem hg
          rcases sector_eq_or_opp τ r.sector with rfl | rfl
          · rw [pieceStep_other Q _ (oppositeSector_ne r.sector).symm] at hgs
            have h1 := pieceStep_gen Q b r.sector (outerPiece T r.support) hgs
            refine inSpanMasks_append_mono (C := if (pieceStep Q b r.sector
              (outerPiece T r.support)).1 then [pieceMask Q (outerPiece T r.support)] else []) h1 ?_
            intro g' hg'
            apply List.mem_append_left
            split at hg'
            · rename_i hko
              rw [List.mem_singleton.mp hg']
              refine mem_entryMasks (e := (some r.id, r.sector, outerPiece T r.support)) ?_ rfl
              unfold mixedEntries
              rw [if_pos hko]
              exact List.mem_append_left _ (List.mem_singleton_self _)
            · cases hg'
          · have h1 := pieceStep_gen Q _ (oppositeSector r.sector) (innerPiece T r.support) hgs
            rw [pieceStep_other Q _ (oppositeSector_ne r.sector)] at h1
            refine inSpanMasks_append_mono h1 ?_
            intro g' hg'
            apply List.mem_append_left
            split at hg'
            · rename_i hki
              rw [List.mem_singleton.mp hg']
              refine mem_entryMasks (e := (if (pieceStep Q b r.sector (outerPiece T r.support)).1
                then none else some r.id, oppositeSector r.sector, innerPiece T r.support)) ?_ rfl
              unfold mixedEntries
              rw [if_pos hki]
              exact List.mem_append_right _ (List.mem_singleton_self _)
            · cases hg'
        · exact inSpanMasks_append_left (inSpanMasks_append_left (inSpanMasks_of_mem hg))

/-- Every piece of every row lies in the final basis of its output sector,
    provided the pure rows' pieces already lie in the initial bases. -/
theorem splitFinal_pieces (Q T : List Nat) :
    ∀ (rows : List Row) (b : List Nat × List Nat),
      (∀ r ∈ rows, isPureRow T r = true → ∀ τ p, IsPiece T r τ p →
        inSpanMasks (basisFor b.1 b.2 τ) (pieceMask Q p)) →
      ∀ r ∈ rows, ∀ τ p, IsPiece T r τ p →
        inSpanMasks (basisFor (splitFinal Q T b rows).1 (splitFinal Q T b rows).2 τ)
          (pieceMask Q p)
  | [], _, _, r, hr, _, _, _ => by cases hr
  | r :: rs, b, hpure, r', hr', τ, p, hpc => by
      unfold splitFinal
      split
      · rename_i hp
        rcases List.mem_cons.mp hr' with rfl | hr'
        · exact splitFinal_mono Q T rs b τ (hpure r' (List.mem_cons_self ..) hp τ p hpc)
        · exact splitFinal_pieces Q T rs b
            (fun r'' h'' => hpure r'' (List.mem_cons_of_mem r h'')) r' hr' τ p hpc
      · rename_i hp
        have hstep : ∀ τ' {v : Nat}, inSpanMasks (basisFor b.1 b.2 τ') v →
            inSpanMasks (basisFor
              (pieceStep Q (pieceStep Q b r.sector (outerPiece T r.support)).2
                (oppositeSector r.sector) (innerPiece T r.support)).2.1
              (pieceStep Q (pieceStep Q b r.sector (outerPiece T r.support)).2
                (oppositeSector r.sector) (innerPiece T r.support)).2.2 τ') v :=
          fun τ' _ h => pieceStep_mono _ _ _ _ τ' (pieceStep_mono _ _ _ _ τ' h)
        rcases List.mem_cons.mp hr' with rfl | hr'
        · apply splitFinal_mono
          rcases hpc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact pieceStep_mono _ _ _ _ _ (pieceStep_mem Q b r'.sector _)
          · exact pieceStep_mem Q _ _ _
        · exact splitFinal_pieces Q T rs _
            (fun r'' h'' hp'' τ'' p'' hpc'' =>
              hstep τ'' (hpure r'' (List.mem_cons_of_mem r h'') hp'' τ'' p'' hpc''))
            r' hr' τ p hpc

/-- A pure row's entry is emitted. -/
theorem pure_entry_mem (Q T : List Nat) :
    ∀ (rows : List Row) (b : List Nat × List Nat) (r : Row), r ∈ rows → isPureRow T r = true →
      (some r.id, pureSector T r, r.support) ∈ splitGo Q T b rows
  | [], _, _, h, _ => by cases h
  | r' :: rs, b, r, hr, hp => by
      unfold splitGo
      split
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (pure_entry_mem Q T rs b r hr hp)
      · rename_i hp'
        rcases List.mem_cons.mp hr with rfl | hr
        · exact absurd hp hp'
        · exact List.mem_append_right _ (pure_entry_mem Q T rs _ r hr hp)

/-- Every emitted entry is a piece of an input row. -/
theorem entry_origin (Q T : List Nat) :
    ∀ (rows : List Row) (b : List Nat × List Nat) (e : Option Nat × Sector × List Nat),
      e ∈ splitGo Q T b rows → ∃ r ∈ rows, IsPiece T r e.2.1 e.2.2
  | [], _, _, h => by cases h
  | r :: rs, b, e, h => by
      unfold splitGo at h
      split at h
      · rename_i hp
        rcases List.mem_cons.mp h with rfl | h
        · refine ⟨r, List.mem_cons_self .., ?_⟩
          unfold isPureRow at hp
          by_cases hc : (outerPiece T r.support).isEmpty = true ∧
              ¬ (innerPiece T r.support).isEmpty = true
          · right
            refine ⟨by simp [pureSector, hc], ?_⟩
            exact (innerPiece_eq_of_outer_nil (List.isEmpty_iff.mp hc.1)).symm
          · left
            refine ⟨by simp only [pureSector]; rw [if_neg hc], ?_⟩
            show r.support = outerPiece T r.support
            cases hi : (innerPiece T r.support).isEmpty with
            | true => exact (outerPiece_eq_of_inner_nil (List.isEmpty_iff.mp hi)).symm
            | false =>
                have ho : (outerPiece T r.support).isEmpty = true := by
                  rw [hi] at hp
                  simpa using hp
                exact absurd ⟨ho, by rw [hi]; decide⟩ hc
        · obtain ⟨r', hr', hpc⟩ := entry_origin Q T rs b e h
          exact ⟨r', List.mem_cons_of_mem r hr', hpc⟩
      · dsimp only at h
        rcases List.mem_append.mp h with h | h
        · refine ⟨r, List.mem_cons_self .., ?_⟩
          unfold mixedEntries at h
          rcases List.mem_append.mp h with h | h
          · split at h
            · rw [List.mem_singleton.mp h]; exact Or.inl ⟨rfl, rfl⟩
            · cases h
          · split at h
            · rw [List.mem_singleton.mp h]; exact Or.inr ⟨rfl, rfl⟩
            · cases h
        · obtain ⟨r', hr', hpc⟩ := entry_origin Q T rs _ e h
          exact ⟨r', List.mem_cons_of_mem r hr', hpc⟩

/-! ## Identifier assignment keeps every entry -/

theorem assignIds_origin : ∀ (es : List (Option Nat × Sector × List Nat)) (ids : List Nat)
    (c : Row), c ∈ assignIds es ids → ∃ e ∈ es, c.sector = e.2.1 ∧ c.support = e.2.2
  | [], _, _, h => by cases h
  | (some id, σ, sup) :: rest, ids, c, h => by
      simp only [assignIds, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨_, List.mem_cons_self .., rfl, rfl⟩
      · obtain ⟨e, he, h1, h2⟩ := assignIds_origin rest ids c h
        exact ⟨e, List.mem_cons_of_mem _ he, h1, h2⟩
  | (none, σ, sup) :: rest, id :: ids, c, h => by
      simp only [assignIds, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨_, List.mem_cons_self .., rfl, rfl⟩
      · obtain ⟨e, he, h1, h2⟩ := assignIds_origin rest ids c h
        exact ⟨e, List.mem_cons_of_mem _ he, h1, h2⟩
  | (none, σ, sup) :: rest, [], c, h => by
      simp only [assignIds] at h
      obtain ⟨e, he, h1, h2⟩ := assignIds_origin rest [] c h
      exact ⟨e, List.mem_cons_of_mem _ he, h1, h2⟩

theorem assignIds_mem : ∀ (es : List (Option Nat × Sector × List Nat)) (ids : List Nat),
    (es.filter (fun e => e.1.isNone)).length ≤ ids.length →
    ∀ e ∈ es, ∃ c ∈ assignIds es ids, c.sector = e.2.1 ∧ c.support = e.2.2
  | [], _, _, e, h => by cases h
  | (some id, σ, sup) :: rest, ids, hlen, e, he => by
      simp only [List.filter_cons, Option.isNone_some] at hlen
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨_, List.mem_cons_self .., rfl, rfl⟩
      · obtain ⟨c, hc, h1, h2⟩ := assignIds_mem rest ids (by simpa using hlen) e he
        exact ⟨c, List.mem_cons_of_mem _ hc, h1, h2⟩
  | (none, σ, sup) :: rest, id :: ids, hlen, e, he => by
      simp only [List.filter_cons, Option.isNone_none, if_true, List.length_cons] at hlen
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨_, List.mem_cons_self .., rfl, rfl⟩
      · obtain ⟨c, hc, h1, h2⟩ := assignIds_mem rest ids (by omega) e he
        exact ⟨c, List.mem_cons_of_mem _ hc, h1, h2⟩
  | (none, σ, sup) :: rest, [], hlen, e, he => by
      simp only [List.filter_cons, Option.isNone_none, if_true, List.length_cons,
        List.length_nil] at hlen
      omega

/-! ## Identifier-order sorting and row-order invariance -/

theorem mem_insertRowByRank (x : Row) : ∀ (rs : List Row) (r : Row),
    r ∈ insertRowByRank x rs ↔ r = x ∨ r ∈ rs
  | [], r => by simp [insertRowByRank]
  | y :: ys, r => by
      unfold insertRowByRank
      split
      · simp [List.mem_cons]
      · have ih := mem_insertRowByRank x ys r
        constructor
        · intro h
          rcases List.mem_cons.mp h with rfl | h'
          · exact Or.inr (List.mem_cons_self ..)
          · rcases ih.mp h' with rfl | h''
            · exact Or.inl rfl
            · exact Or.inr (List.mem_cons_of_mem y h'')
        · intro h
          rcases h with rfl | h'
          · exact List.mem_cons_of_mem y (ih.mpr (Or.inl rfl))
          · rcases List.mem_cons.mp h' with rfl | h''
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem y (ih.mpr (Or.inr h''))

theorem mem_sortRowsByRank : ∀ (rs : List Row) (r : Row),
    r ∈ sortRowsByRank rs ↔ r ∈ rs
  | [], _ => Iff.rfl
  | x :: xs, r => by
      unfold sortRowsByRank
      rw [mem_insertRowByRank, mem_sortRowsByRank xs r, List.mem_cons]

theorem pairwise_insertRowByRank (x : Row) : ∀ (rs : List Row),
    rs.Pairwise (fun a b => a.id < b.id) →
    (∀ r ∈ rs, x.id ≠ r.id) →
    (insertRowByRank x rs).Pairwise (fun a b => a.id < b.id)
  | [], _, _ => List.pairwise_singleton _ _
  | y :: ys, hpw, hneq => by
      have hcons := List.pairwise_cons.mp hpw
      unfold insertRowByRank
      split
      · rename_i hle
        have hlt : x.id < y.id := by
          have hxy := hneq y (List.mem_cons_self ..)
          omega
        refine List.pairwise_cons.mpr ⟨?_, hpw⟩
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact hlt
        · exact Nat.lt_trans hlt (hcons.1 r hr')
      · rename_i hgt
        have hlt : y.id < x.id := by omega
        refine List.pairwise_cons.mpr ⟨?_,
          pairwise_insertRowByRank x ys hcons.2 (fun r hr => hneq r (List.mem_cons_of_mem y hr))⟩
        intro r hr
        rcases (mem_insertRowByRank x ys r).mp hr with rfl | hr'
        · exact hlt
        · exact hcons.1 r hr'

theorem pairwise_sortRowsByRank : ∀ (rs : List Row),
    (rs.map Row.id).Nodup →
    (sortRowsByRank rs).Pairwise (fun a b => a.id < b.id)
  | [], _ => List.Pairwise.nil
  | x :: xs, hnd => by
      simp only [List.map_cons, List.nodup_cons] at hnd
      refine pairwise_insertRowByRank x (sortRowsByRank xs)
        (pairwise_sortRowsByRank xs hnd.2) ?_
      intro r hr heq
      exact hnd.1 (List.mem_map.mpr ⟨r, (mem_sortRowsByRank xs r).mp hr, heq.symm⟩)

theorem eq_of_pairwise_lt_id (l1 : List Row) : ∀ (l2 : List Row),
    l1.Pairwise (fun a b => a.id < b.id) →
    l2.Pairwise (fun a b => a.id < b.id) →
    (∀ r, r ∈ l1 ↔ r ∈ l2) →
    l1 = l2 := by
  induction l1 with
  | nil =>
      intro l2 _ _ hmem
      cases l2 with
      | nil => rfl
      | cons b _ => exact nomatch (hmem b).mpr (List.mem_cons_self ..)
  | cons a as ih =>
      intro l2 h1 h2 hmem
      cases l2 with
      | nil => exact nomatch (hmem a).mp (List.mem_cons_self ..)
      | cons b bs =>
          have ha := List.pairwise_cons.mp h1
          have hb := List.pairwise_cons.mp h2
          have hab : a = b := by
            rcases List.mem_cons.mp ((hmem a).mp (List.mem_cons_self ..)) with rfl | ha_bs
            · rfl
            · rcases List.mem_cons.mp ((hmem b).mpr (List.mem_cons_self ..)) with hba | hb_as
              · exact hba.symm
              · exact absurd (Nat.lt_trans (hb.1 a ha_bs) (ha.1 b hb_as)) (Nat.lt_irrefl _)
          subst hab
          refine congrArg (a :: ·) (ih bs ha.2 hb.2 ?_)
          intro r
          constructor
          · intro hr
            rcases List.mem_cons.mp ((hmem r).mp (List.mem_cons_of_mem a hr)) with rfl | hr'
            · exact absurd (ha.1 r hr) (Nat.lt_irrefl _)
            · exact hr'
          · intro hr
            rcases List.mem_cons.mp ((hmem r).mpr (List.mem_cons_of_mem a hr)) with rfl | hr'
            · exact absurd (hb.1 r hr) (Nat.lt_irrefl _)
            · exact hr'

theorem sortRowsByRank_eq_of_mem_iff {rs1 rs2 : List Row}
    (h1 : (rs1.map Row.id).Nodup) (h2 : (rs2.map Row.id).Nodup)
    (hmem : ∀ r, r ∈ rs1 ↔ r ∈ rs2) :
    sortRowsByRank rs1 = sortRowsByRank rs2 :=
  eq_of_pairwise_lt_id _ _ (pairwise_sortRowsByRank rs1 h1) (pairwise_sortRowsByRank rs2 h2)
    (fun r => (mem_sortRowsByRank rs1 r).trans ((hmem r).trans (mem_sortRowsByRank rs2 r).symm))

theorem canonicalMint_eq_of_contains_iff {u1 u2 : List Nat}
    (h : ∀ x, u1.contains x ↔ u2.contains x) :
    canonicalMint u1 = canonicalMint u2 := by
  rcases Nat.lt_or_ge (canonicalMint u1) (canonicalMint u2) with hlt | hge
  · exact absurd ((h _).mpr (canonicalMint_least u2 _ hlt)) (canonicalMint_fresh u1)
  · rcases Nat.lt_or_ge (canonicalMint u2) (canonicalMint u1) with hgt | hle
    · exact absurd ((h _).mp (canonicalMint_least u1 _ hgt)) (canonicalMint_fresh u2)
    · omega

theorem mintFresh_eq_of_contains_iff : ∀ (n : Nat) {u1 u2 : List Nat},
    (∀ x, u1.contains x ↔ u2.contains x) →
    mintFresh u1 n = mintFresh u2 n
  | 0, _, _, _ => rfl
  | n + 1, u1, u2, h => by
      have hm : canonicalMint u1 = canonicalMint u2 := canonicalMint_eq_of_contains_iff h
      unfold mintFresh
      rw [hm]
      refine congrArg (canonicalMint u2 :: ·) (mintFresh_eq_of_contains_iff n ?_)
      intro x
      simp only [List.contains_iff_mem, List.mem_append, List.mem_singleton]
      constructor
      · rintro (hx | rfl)
        · exact Or.inl (List.contains_iff_mem.mp ((h x).mp (List.contains_iff_mem.mpr hx)))
        · exact Or.inr rfl
      · rintro (hx | rfl)
        · exact Or.inl (List.contains_iff_mem.mp ((h x).mpr (List.contains_iff_mem.mpr hx)))
        · exact Or.inr rfl

theorem sector_beq_iff (a b : Sector) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide

theorem row_beq_iff (a b : Row) : (a == b) = true ↔ a = b := by
  cases a with | mk i1 s1 p1 =>
  cases b with | mk i2 s2 p2 =>
  show (i1 == i2 && (s1 == s2 && p1 == p2)) = true ↔ _
  simp only [Bool.and_eq_true, beq_iff_eq, sector_beq_iff, Row.mk.injEq]

theorem row_contains_iff_mem : ∀ (rs : List Row) (r : Row),
    rs.contains r = true ↔ r ∈ rs
  | [], _ => by simp
  | x :: xs, r => by
      rw [List.contains_cons, Bool.or_eq_true, row_beq_iff, row_contains_iff_mem xs r,
        List.mem_cons]

/-- `≡`-input invariance of `splitHadamardState`: two states with the same
    qubit list `Q`, pairwise-distinct row identifiers (I3), and `s1 ≡ s2`
    produce identical output row lists and `≡`-equal child states. -/
theorem splitHadamardState_equiv {s1 s2 : CodeState} (T : List Nat)
    (hQ : s1.Q = s2.Q)
    (h1 : (s1.rows.map Row.id).Nodup) (h2 : (s2.rows.map Row.id).Nodup)
    (heq : s1 ≡ s2) :
    (splitHadamardState s1 T).rows = (splitHadamardState s2 T).rows ∧
    splitHadamardState s1 T ≡ splitHadamardState s2 T := by
  have hrows : sortRowsByRank s1.rows = sortRowsByRank s2.rows :=
    sortRowsByRank_eq_of_mem_iff h1 h2 (fun r =>
      (row_contains_iff_mem s1.rows r).symm.trans
        ((heq.2.1 r).trans (row_contains_iff_mem s2.rows r)))
  have hpm : ∀ σ, pureMasks s1 T σ = pureMasks s2 T σ := by
    intro σ; unfold pureMasks; rw [hQ, hrows]
  have hseed : splitSeed s1 T = splitSeed s2 T := by
    unfold splitSeed; rw [hpm Sector.X, hpm Sector.Z]
  have hent : splitEntries s1 T = splitEntries s2 T := by
    unfold splitEntries; rw [hQ, hseed, hrows]
  have hcnt : splitMintCount s1 T = splitMintCount s2 T := by
    unfold splitMintCount; rw [hent]
  have hids : mintFresh s1.used (splitMintCount s1 T) =
      mintFresh s2.used (splitMintCount s2 T) := by
    rw [hcnt]
    exact mintFresh_eq_of_contains_iff _ heq.2.2
  have hresRows : (splitHadamardState s1 T).rows = (splitHadamardState s2 T).rows := by
    unfold splitHadamardState
    rw [hent, hids]
  refine ⟨hresRows, ?_, ?_, ?_⟩
  · intro q; simp only [splitHadamardState, hQ]
  · intro r; rw [hresRows]
  · intro x
    simp only [splitHadamardState, hids, List.contains_iff_mem, List.mem_append]
    constructor
    · rintro (hx | hx)
      · exact Or.inl (List.contains_iff_mem.mp ((heq.2.2 x).mp (List.contains_iff_mem.mpr hx)))
      · exact Or.inr hx
    · rintro (hx | hx)
      · exact Or.inl (List.contains_iff_mem.mp ((heq.2.2 x).mpr (List.contains_iff_mem.mpr hx)))
      · exact Or.inr hx

/-! ## The child state's spans -/

/-- Every child row is a piece of a parent row. -/
theorem splitRow_origin (s : CodeState) (T : List Nat) (c : Row)
    (hc : c ∈ (splitHadamardState s T).rows) : ∃ r ∈ s.rows, IsPiece T r c.sector c.support := by
  obtain ⟨e, he, h1, h2⟩ := assignIds_origin _ _ c hc
  obtain ⟨r, hr, hpc⟩ := entry_origin s.Q T (sortRowsByRank s.rows) _ e he
  exact ⟨r, (mem_sortRowsByRank s.rows r).mp hr, by rw [h1, h2]; exact hpc⟩

theorem seed_basis_span (s : CodeState) (T : List Nat) (τ : Sector) {v : Nat} :
    inSpanMasks (basisFor (splitSeed s T).1 (splitSeed s T).2 τ) v ↔
      inSpanMasks (pureMasks s T τ) v := by
  cases τ
  · exact spanEq_foldl_insertBasis_nil _ v
  · exact spanEq_foldl_insertBasis_nil _ v

/-- Every piece of every parent row lies in the mask span of the child rows of
    its output sector. -/
theorem piece_inSpan_child_masks (s : CodeState) (T : List Nat) (r : Row) (hr : r ∈ s.rows)
    (τ : Sector) (p : List Nat) (hpc : IsPiece T r τ p) :
    inSpanMasks ((sectorRows (splitHadamardState s T) τ).map (rowBitmask s.Q)) (pieceMask s.Q p) := by
  -- the pure rows' pieces lie in the seed
  have hpure : ∀ r' ∈ sortRowsByRank s.rows, isPureRow T r' = true → ∀ τ' p', IsPiece T r' τ' p' →
      inSpanMasks (basisFor (splitSeed s T).1 (splitSeed s T).2 τ') (pieceMask s.Q p') := by
    intro r' hr' hp' τ' p' hpc'
    rcases pure_piece hp' hpc' with rfl | ⟨rfl, rfl⟩
    · exact inSpanMasks_zero _
    · refine (seed_basis_span s T _).mpr (inSpanMasks_of_mem ?_)
      exact List.mem_map.mpr ⟨r', List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hr', hp'⟩,
        by simp⟩, rfl⟩
  have h1 := splitFinal_pieces s.Q T (sortRowsByRank s.rows) (splitSeed s T) hpure r
    ((mem_sortRowsByRank s.rows r).mpr hr) τ p hpc
  have h2 := splitFinal_gen s.Q T (sortRowsByRank s.rows) (splitSeed s T) τ h1
  -- the seed and the entries lie in the child span
  have hE : ∀ g ∈ entryMasks s.Q τ (splitEntries s T),
      g ∈ (sectorRows (splitHadamardState s T) τ).map (rowBitmask s.Q) := by
    intro g hg
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hg
    have he' := List.mem_filter.mp he
    have hlen : ((splitEntries s T).filter (fun e => e.1.isNone)).length ≤
        (mintFresh s.used (splitMintCount s T)).length := by
      rw [mintFresh_length]; exact Nat.le_refl _
    obtain ⟨c, hc, hcs, hcp⟩ := assignIds_mem _ _ hlen e he'.1
    refine List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, ?_⟩, ?_⟩
    · have := he'.2
      simp only [decide_eq_true_eq] at this
      simp [hcs, this]
    · rw [rowBitmask_eq_pieceMask, hcp]
  refine inSpanMasks_trans (fun g hg => ?_) h2
  rcases List.mem_append.mp hg with hg | hg
  · have hgs := (seed_basis_span s T τ).mp (inSpanMasks_of_mem hg)
    refine inSpanMasks_trans (fun g' hg' => ?_) hgs
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hg'
    have hr'' := List.mem_filter.mp hr'
    have hrp := List.mem_filter.mp hr''.1
    refine inSpanMasks_of_mem (hE _ ?_)
    refine mem_entryMasks (e := (some r'.id, pureSector T r', r'.support))
      (pure_entry_mem s.Q T (sortRowsByRank s.rows) _ r' hrp.1 hrp.2) ?_
    simpa using hr''.2
  · exact inSpanMasks_of_mem (hE g hg)

/-! ## Pieces as vectors -/

theorem contains_cons_eq (a q : Nat) (l : List Nat) :
    (a :: l).contains q = ((q == a) || l.contains q) := List.contains_cons

theorem contains_filter_eq (p : Nat → Bool) (q : Nat) :
    ∀ l : List Nat, (l.filter p).contains q = (p q && l.contains q)
  | [] => by cases p q <;> rfl
  | a :: l => by
      have ih := contains_filter_eq p q l
      cases hqa : (q == a) with
      | true =>
          have hq : q = a := LawfulBEq.eq_of_beq hqa
          subst hq
          cases hpa : p q with
          | true =>
              rw [List.filter_cons_of_pos hpa, contains_cons_eq, contains_cons_eq, hqa]
              rfl
          | false =>
              rw [List.filter_cons_of_neg (by rw [hpa]; decide), ih, hpa]
              rfl
      | false =>
          cases hpa : p a with
          | true =>
              rw [List.filter_cons_of_pos hpa, contains_cons_eq, contains_cons_eq, hqa, ih]
              cases p q <;> rfl
          | false =>
              rw [List.filter_cons_of_neg (by rw [hpa]; decide), ih, contains_cons_eq, hqa]
              cases p q <;> rfl

theorem rowVector_inner (Q T sup : List Nat) (i j : Nat) (σ τ : Sector) :
    rowVector Q ⟨i, σ, innerPiece T sup⟩ = projVec (tMask Q T) (rowVector Q ⟨j, τ, sup⟩) := by
  induction Q with
  | nil => rfl
  | cons q qs ih =>
      show (innerPiece T sup).contains q :: rowVector qs ⟨i, σ, innerPiece T sup⟩ =
        (T.contains q && sup.contains q) :: projVec (tMask qs T) (rowVector qs ⟨j, τ, sup⟩)
      rw [ih]
      unfold innerPiece
      rw [contains_filter_eq]

theorem rowVector_outer (Q T sup : List Nat) (i j : Nat) (σ τ : Sector) :
    rowVector Q ⟨i, σ, outerPiece T sup⟩ = projVec (rMask Q T) (rowVector Q ⟨j, τ, sup⟩) := by
  induction Q with
  | nil => rfl
  | cons q qs ih =>
      show (outerPiece T sup).contains q :: rowVector qs ⟨i, σ, outerPiece T sup⟩ =
        (!T.contains q && sup.contains q) :: projVec (rMask qs T) (rowVector qs ⟨j, τ, sup⟩)
      rw [ih]
      unfold outerPiece
      rw [contains_filter_eq]
      cases T.contains q <;> rfl

theorem rowVector_eta (Q : List Nat) (r : Row) :
    rowVector Q r = rowVector Q ⟨r.id, r.sector, r.support⟩ := rfl

/-- Every piece of every parent row lies in the vector span of the child rows
    of its output sector. -/
theorem piece_inSpan_child (s : CodeState) (hnd : s.Q.Nodup) (T : List Nat) (r : Row)
    (hr : r ∈ s.rows) (τ : Sector) (p : List Nat) (hpc : IsPiece T r τ p) :
    inSpanRows s.Q (sectorRows (splitHadamardState s T) τ) (rowVector s.Q ⟨0, τ, p⟩) :=
  (inSpanRows_iff_inSpanMasks s.Q hnd _ ⟨0, τ, p⟩).mpr
    (piece_inSpan_child_masks s T r hr τ p hpc)

/-- The outer piece of a parent row, as a vector, lies in the child span of the
    row's own sector. -/
theorem outer_inSpan_child (s : CodeState) (hnd : s.Q.Nodup) (T : List Nat) (r : Row)
    (hr : r ∈ s.rows) :
    inSpanRows s.Q (sectorRows (splitHadamardState s T) r.sector)
      (projVec (rMask s.Q T) (rowVector s.Q r)) := by
  rw [rowVector_eta, ← rowVector_outer s.Q T r.support 0 r.id r.sector r.sector]
  exact piece_inSpan_child s hnd T r hr _ _ (Or.inl ⟨rfl, rfl⟩)

/-- The inner piece of a parent row lies in the child span of the opposite
    sector. -/
theorem inner_inSpan_child (s : CodeState) (hnd : s.Q.Nodup) (T : List Nat) (r : Row)
    (hr : r ∈ s.rows) :
    inSpanRows s.Q (sectorRows (splitHadamardState s T) (oppositeSector r.sector))
      (projVec (tMask s.Q T) (rowVector s.Q r)) := by
  rw [rowVector_eta, ← rowVector_inner s.Q T r.support 0 r.id (oppositeSector r.sector) r.sector]
  exact piece_inSpan_child s hnd T r hr _ _ (Or.inr ⟨rfl, rfl⟩)

/-- Every child row of sector `τ`, as a vector, is the outer piece of a parent
    `τ`-row or the inner piece of a parent row of the other sector. -/
theorem child_row_vector (s : CodeState) (T : List Nat) (τ : Sector) (c : Row)
    (hc : c ∈ sectorRows (splitHadamardState s T) τ) :
    ∃ r ∈ s.rows,
      (r.sector = τ ∧ rowVector s.Q c = projVec (rMask s.Q T) (rowVector s.Q r)) ∨
      (r.sector = oppositeSector τ ∧ rowVector s.Q c = projVec (tMask s.Q T) (rowVector s.Q r)) := by
  have hc' := List.mem_filter.mp hc
  have hcτ : c.sector = τ := by simpa using hc'.2
  obtain ⟨r, hr, hpc⟩ := splitRow_origin s T c hc'.1
  refine ⟨r, hr, ?_⟩
  rcases hpc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine ⟨by rw [← h1, hcτ], ?_⟩
    rw [rowVector_eta s.Q c, h2, rowVector_eta s.Q r]
    exact rowVector_outer _ _ _ _ _ _ _
  · right
    refine ⟨by rw [← hcτ, h1, oppositeSector_involutive], ?_⟩
    rw [rowVector_eta s.Q c, h2, rowVector_eta s.Q r]
    exact rowVector_inner _ _ _ _ _ _ _

/-- Under the guard, the inner piece of each parent row lies in its own
    sector's span. -/
theorem guard_inner (s : CodeState) (hnd : s.Q.Nodup) (T : List Nat)
    (hg : splitGuard s T = true) (r : Row) (hr : r ∈ s.rows) :
    inSpanRows s.Q (sectorRows s r.sector) (projVec (tMask s.Q T) (rowVector s.Q r)) := by
  have h0 := List.all_eq_true.mp hg r hr
  have h0' : reduceByBasis (sectorBasis s r.sector)
      (pieceMask s.Q (innerPiece T r.support)) = 0 := by simpa using h0
  obtain ⟨v', hv', hx⟩ := reduceByBasis_sound (sectorBasis s r.sector)
    (pieceMask s.Q (innerPiece T r.support))
  rw [h0'] at hx
  have hm : inSpanMasks (sectorBasis s r.sector) (pieceMask s.Q (innerPiece T r.support)) := by
    rw [xor_eq_zero_cancel hx.symm]; exact hv'
  have hm' := (spanEq_foldl_insertBasis_nil _ _).mp hm
  rw [rowVector_eta, ← rowVector_inner s.Q T r.support 0 r.id r.sector r.sector]
  exact (inSpanRows_iff_inSpanMasks s.Q hnd _ ⟨0, r.sector, innerPiece T r.support⟩).mpr hm'

/-- Under the guard, the outer piece of each parent row lies in its own
    sector's span too. -/
theorem guard_outer (s : CodeState) (hnd : s.Q.Nodup) (T : List Nat)
    (hg : splitGuard s T = true) (r : Row) (hr : r ∈ s.rows) :
    inSpanRows s.Q (sectorRows s r.sector) (projVec (rMask s.Q T) (rowVector s.Q r)) := by
  have hlen := rowVector_length s.Q r
  have hT := projVec_length (tMask s.Q T) (rowVector s.Q r) (by rw [tMask_length, hlen])
  have hR := projVec_length (rMask s.Q T) (rowVector s.Q r) (by rw [rMask_length, hlen])
  have hdec := xorVec_projVec_t_r s.Q T (rowVector s.Q r) hlen
  have heq : xorVec (projVec (tMask s.Q T) (rowVector s.Q r)) (rowVector s.Q r) =
      projVec (rMask s.Q T) (rowVector s.Q r) := by
    have h := xorVec_cancel_left (projVec (tMask s.Q T) (rowVector s.Q r))
      (projVec (rMask s.Q T) (rowVector s.Q r)) (by rw [hT, hR])
    rw [hdec] at h
    exact h
  rw [← heq]
  have hrσ : r ∈ sectorRows s r.sector := List.mem_filter.mpr ⟨hr, by simp⟩
  exact inSpanRows_xor s.Q _ (guard_inner s hnd T hg r hr) (inSpanRows_of_mem s.Q hrσ)

/-! ## Logicals across the split update -/

theorem isLogical_iff (s : CodeState) (σ : Sector) (v : List Bool) :
    isLogicalBool s σ v = true ↔
      (∀ r ∈ sectorRows s (oppositeSector σ), dotPar v (rowVector s.Q r) % 2 = 0) ∧
      ¬ inSpanRows s.Q (sectorRows s σ) v := by
  unfold isLogicalBool
  rw [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', ← exact_inSpanRowsBool_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun r hr => Nat.eq_of_beq_eq_true (h1 r hr), by rw [h2]; simp⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun r hr => by rw [h1 r hr]; rfl, ?_⟩
    cases h : inSpanRowsBool s.Q (sectorRows s σ) v
    · rfl
    · exact absurd h h2

/-- A constructive case split on span membership, through the computable
    test `inSpanRowsBool` (a `by_cases` on the `Prop` would be classical). -/
theorem inSpanRows_em (Q : List Nat) (rows : List Row) (v : List Bool) :
    inSpanRows Q rows v ∨ ¬ inSpanRows Q rows v := by
  cases h : inSpanRowsBool Q rows v with
  | true => exact Or.inl ((exact_inSpanRowsBool_iff _ _ _).mp h)
  | false =>
      exact Or.inr (fun h' => by
        rw [(exact_inSpanRowsBool_iff _ _ _).mpr h'] at h
        exact Bool.noConfusion h)

theorem mem_logicalVectors_iff (s : CodeState) (σ : Sector) (v : List Bool) :
    v ∈ logicalVectors s σ ↔ v.length = s.Q.length ∧ isLogicalBool s σ v = true := by
  unfold logicalVectors
  rw [List.mem_filter, exact_mem_allBoolLists]

theorem combineRows_inSpan (Q : List Nat) (B : List Row) :
    ∀ (ws : List (List Bool)) (cs : List Bool), (∀ w ∈ ws, inSpanRows Q B w) →
      inSpanRows Q B (combineRows Q.length ws cs)
  | [], cs, _ => by cases cs <;> exact splitInSpan_zero Q B
  | w :: ws, [], _ => splitInSpan_zero Q B
  | w :: ws, true :: cs, h =>
      inSpanRows_xor Q B (h w (List.mem_cons_self ..))
        (combineRows_inSpan Q B ws cs (fun w' hw' => h w' (List.mem_cons_of_mem w hw')))
  | w :: ws, false :: cs, h =>
      combineRows_inSpan Q B ws cs (fun w' hw' => h w' (List.mem_cons_of_mem w hw'))

/-- Restriction maps the span of `A` into the span of `B` when it maps every
    row of `A` there. -/
theorem inSpanRows_projVec (Q : List Nat) (m : List Bool) (hm : m.length = Q.length)
    (A B : List Row) (v : List Bool) (hv : inSpanRows Q A v)
    (h : ∀ r ∈ A, inSpanRows Q B (projVec m (rowVector Q r))) :
    inSpanRows Q B (projVec m v) := by
  obtain ⟨cs, _, hc⟩ := hv
  rw [← hc]
  have hlen : ∀ w ∈ A.map (rowVector Q), w.length = m.length := by
    intro w hw
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hw
    rw [rowVector_length, hm]
  have e := projVec_combineRows m (A.map (rowVector Q)) cs hlen
  rw [hm] at e
  rw [e]
  apply combineRows_inSpan
  intro w hw
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hu
  exact h r hr

theorem zero_proj_inSpan (Q T : List Nat) (B : List Row) (v : List Bool) (hv : v.length = Q.length) :
    inSpanRows Q B (projVec (rMask Q T) (projVec (tMask Q T) v)) ∧
    inSpanRows Q B (projVec (tMask Q T) (projVec (rMask Q T) v)) := by
  rw [projVec_r_t Q T v hv, projVec_t_r Q T v hv]
  exact ⟨splitInSpan_zero Q B, splitInSpan_zero Q B⟩

theorem mem_sectorRows {s : CodeState} {σ : Sector} {r : Row} (hr : r ∈ sectorRows s σ) :
    r ∈ s.rows ∧ r.sector = σ := by
  have h := List.mem_filter.mp hr
  exact ⟨h.1, by simpa using h.2⟩

/-- A child σ-logical restricts to a parent σ-logical on `Q ∖ T` or to a parent
    σ̄-logical on `T`, of no larger weight. No guard is needed. -/
theorem split_logical_child (s : CodeState) (hnd : s.Q.Nodup) (T : List Nat) (σ : Sector)
    (v : List Bool) (hv : v ∈ logicalVectors (splitHadamardState s T) σ) :
    ∃ w, weight w ≤ weight v ∧ (w ∈ logicalVectors s σ ∨ w ∈ logicalVectors s (oppositeSector σ)) := by
  have hv' := (mem_logicalVectors_iff _ σ v).mp hv
  have hlen : v.length = s.Q.length := hv'.1
  obtain ⟨horth, hns⟩ := (isLogical_iff _ σ v).mp hv'.2
  have htl : (tMask s.Q T).length = v.length := by rw [tMask_length, hlen]
  have hrl : (rMask s.Q T).length = v.length := by rw [rMask_length, hlen]
  have hdot : ∀ (m : List Bool), m.length = s.Q.length → ∀ r : Row,
      dotPar (projVec m v) (rowVector s.Q r) = dotPar v (projVec m (rowVector s.Q r)) :=
    fun m hm r => dotPar_projVec m v _ (by rw [hm, hlen]) (by rw [hlen, rowVector_length])
  rcases inSpanRows_em s.Q (sectorRows s σ) (projVec (rMask s.Q T) v) with hR | hR
  · refine ⟨projVec (tMask s.Q T) v, weight_projVec_le _ _, Or.inr ?_⟩
    refine (mem_logicalVectors_iff _ _ _).mpr ⟨by rw [projVec_length _ _ htl, hlen], ?_⟩
    refine (isLogical_iff _ _ _).mpr ⟨?_, ?_⟩
    · intro r hr
      rw [oppositeSector_involutive] at hr
      obtain ⟨hr, hrσ⟩ := mem_sectorRows hr
      rw [hdot _ (tMask_length _ _)]
      have hin := inner_inSpan_child s hnd T r hr
      rw [hrσ] at hin
      exact dotPar_even_of_inSpanRows s.Q _ v _ hin horth
    · intro hT
      apply hns
      have h1 : inSpanRows s.Q (sectorRows (splitHadamardState s T) σ) (projVec (rMask s.Q T) v) := by
        have := inSpanRows_projVec s.Q (rMask s.Q T) (rMask_length _ _) _ _ _ hR (fun r hr => by
          obtain ⟨hr, hrσ⟩ := mem_sectorRows hr
          have := outer_inSpan_child s hnd T r hr
          rwa [hrσ] at this)
        rwa [projVec_idem] at this
      have h2 : inSpanRows s.Q (sectorRows (splitHadamardState s T) σ) (projVec (tMask s.Q T) v) := by
        have := inSpanRows_projVec s.Q (tMask s.Q T) (tMask_length _ _) _ _ _ hT (fun r hr => by
          obtain ⟨hr, hrσ⟩ := mem_sectorRows hr
          have := inner_inSpan_child s hnd T r hr
          rwa [hrσ, oppositeSector_involutive] at this)
        rwa [projVec_idem] at this
      have := inSpanRows_xor s.Q _ h2 h1
      rwa [xorVec_projVec_t_r s.Q T v hlen] at this
  · refine ⟨projVec (rMask s.Q T) v, weight_projVec_le _ _, Or.inl ?_⟩
    refine (mem_logicalVectors_iff _ _ _).mpr ⟨by rw [projVec_length _ _ hrl, hlen], ?_⟩
    refine (isLogical_iff _ _ _).mpr ⟨?_, hR⟩
    intro r hr
    obtain ⟨hr, hrσ⟩ := mem_sectorRows hr
    rw [hdot _ (rMask_length _ _)]
    have hin := outer_inSpan_child s hnd T r hr
    rw [hrσ] at hin
    exact dotPar_even_of_inSpanRows s.Q _ v _ hin horth

/-- Under the guard, a parent σ-logical restricts to a child σ-logical on
    `Q ∖ T` or to a child σ̄-logical on `T`, of no larger weight. -/
theorem split_logical_parent (s : CodeState) (hnd : s.Q.Nodup) (T : List Nat)
    (hg : splitGuard s T = true) (σ : Sector) (v : List Bool) (hv : v ∈ logicalVectors s σ) :
    ∃ w, weight w ≤ weight v ∧ (w ∈ logicalVectors (splitHadamardState s T) σ ∨
      w ∈ logicalVectors (splitHadamardState s T) (oppositeSector σ)) := by
  have hv' := (mem_logicalVectors_iff _ σ v).mp hv
  have hlen : v.length = s.Q.length := hv'.1
  obtain ⟨horth, hns⟩ := (isLogical_iff _ σ v).mp hv'.2
  have htl : (tMask s.Q T).length = v.length := by rw [tMask_length, hlen]
  have hrl : (rMask s.Q T).length = v.length := by rw [rMask_length, hlen]
  have hdot : ∀ (m : List Bool), m.length = s.Q.length → ∀ r : Row,
      dotPar (projVec m v) (projVec m (rowVector s.Q r)) = dotPar v (projVec m (rowVector s.Q r)) := by
    intro m hm r
    rw [dotPar_projVec m v _ (by rw [hm, hlen])
      (by rw [hlen, projVec_length _ _ (by rw [hm, rowVector_length]), rowVector_length]),
      projVec_idem]
  have hrv : ∀ r : Row, (rowVector s.Q r).length = s.Q.length := rowVector_length s.Q
  let child := splitHadamardState s T
  rcases inSpanRows_em s.Q (sectorRows child σ) (projVec (rMask s.Q T) v) with hR | hR
  · refine ⟨projVec (tMask s.Q T) v, weight_projVec_le _ _, Or.inr ?_⟩
    refine (mem_logicalVectors_iff _ _ _).mpr ⟨by rw [projVec_length _ _ htl, hlen]; rfl, ?_⟩
    refine (isLogical_iff _ _ _).mpr ⟨?_, ?_⟩
    · intro c hc
      rw [oppositeSector_involutive] at hc
      obtain ⟨r, hr, ⟨hrσ, hcv⟩ | ⟨hrσ, hcv⟩⟩ := child_row_vector s T σ c hc
      · show dotPar (projVec (tMask s.Q T) v) (rowVector s.Q c) % 2 = 0
        rw [hcv, dotPar_projVec_t_r]
      · show dotPar (projVec (tMask s.Q T) v) (rowVector s.Q c) % 2 = 0
        rw [hcv, hdot _ (tMask_length _ _)]
        have hin := guard_inner s hnd T hg r hr
        rw [hrσ] at hin
        exact dotPar_even_of_inSpanRows s.Q _ v _ hin horth
    · intro hT
      apply hns
      have h1 : inSpanRows s.Q (sectorRows s σ) (projVec (rMask s.Q T) v) := by
        have := inSpanRows_projVec s.Q (rMask s.Q T) (rMask_length _ _) _ _ _ hR (fun c hc => by
          obtain ⟨r, hr, ⟨hrσ, hcv⟩ | ⟨hrσ, hcv⟩⟩ := child_row_vector s T σ c hc
          · rw [hcv, projVec_idem]
            have := guard_outer s hnd T hg r hr
            rwa [hrσ] at this
          · rw [hcv]
            exact (zero_proj_inSpan s.Q T (sectorRows s σ) _ (hrv r)).1)
        rwa [projVec_idem] at this
      have h2 : inSpanRows s.Q (sectorRows s σ) (projVec (tMask s.Q T) v) := by
        have := inSpanRows_projVec s.Q (tMask s.Q T) (tMask_length _ _)
          (sectorRows child (oppositeSector σ)) (sectorRows s σ) _ hT (fun c hc => by
          obtain ⟨r, hr, ⟨hrσ, hcv⟩ | ⟨hrσ, hcv⟩⟩ :=
            child_row_vector s T (oppositeSector σ) c hc
          · rw [hcv]
            exact (zero_proj_inSpan s.Q T (sectorRows s σ) _ (hrv r)).2
          · rw [hcv, projVec_idem]
            have := guard_inner s hnd T hg r hr
            rwa [hrσ, oppositeSector_involutive] at this)
        rwa [projVec_idem] at this
      have := inSpanRows_xor s.Q _ h2 h1
      rwa [xorVec_projVec_t_r s.Q T v hlen] at this
  · refine ⟨projVec (rMask s.Q T) v, weight_projVec_le _ _, Or.inl ?_⟩
    refine (mem_logicalVectors_iff _ _ _).mpr ⟨by rw [projVec_length _ _ hrl, hlen]; rfl, ?_⟩
    refine (isLogical_iff _ _ _).mpr ⟨?_, hR⟩
    intro c hc
    obtain ⟨r, hr, ⟨hrσ, hcv⟩ | ⟨hrσ, hcv⟩⟩ := child_row_vector s T (oppositeSector σ) c hc
    · show dotPar (projVec (rMask s.Q T) v) (rowVector s.Q c) % 2 = 0
      rw [hcv, hdot _ (rMask_length _ _)]
      have hin := guard_outer s hnd T hg r hr
      rw [hrσ] at hin
      exact dotPar_even_of_inSpanRows s.Q _ v _ hin horth
    · show dotPar (projVec (rMask s.Q T) v) (rowVector s.Q c) % 2 = 0
      rw [hcv, dotPar_projVec_r_t s.Q T v _ hlen (hrv r)]

/-! ## The exact distances -/

theorem splitHadamardState_Q (s : CodeState) (T : List Nat) :
    (splitHadamardState s T).Q = s.Q := rfl

/-- Each child sector distance is at least the parent's full distance (read in
    `Nat`, with the shared sentinel). -/
theorem exactDistance_split_ge (s : CodeState) (hnd : s.Q.Nodup) (T : List Nat) (σ : Sector) :
    min (exactDistance σ s) (exactDistance (oppositeSector σ) s) ≤
      exactDistance σ (splitHadamardState s T) := by
  unfold exactDistance
  rw [splitHadamardState_Q]
  rcases minWeight_attained (s.Q.length + 1) (logicalVectors (splitHadamardState s T) σ)
    with h | ⟨v, hv, hw⟩
  · rw [h]
    exact Nat.le_trans (Nat.min_le_left _ _) (minWeight_le_init _ _)
  · rw [hw]
    obtain ⟨w, hwv, hmem | hmem⟩ := split_logical_child s hnd T σ v hv
    · exact Nat.le_trans (Nat.min_le_left _ _)
        (Nat.le_trans (minWeight_le_of_mem _ _ hmem) hwv)
    · exact Nat.le_trans (Nat.min_le_right _ _)
        (Nat.le_trans (minWeight_le_of_mem _ _ hmem) hwv)

/-- Under the guard, each parent sector distance is at least the child's full
    distance. -/
theorem exactDistance_split_le (s : CodeState) (hnd : s.Q.Nodup) (T : List Nat)
    (hg : splitGuard s T = true) (σ : Sector) :
    min (exactDistance σ (splitHadamardState s T))
        (exactDistance (oppositeSector σ) (splitHadamardState s T)) ≤ exactDistance σ s := by
  unfold exactDistance
  rw [splitHadamardState_Q]
  rcases minWeight_attained (s.Q.length + 1) (logicalVectors s σ) with h | ⟨v, hv, hw⟩
  · rw [h]
    exact Nat.le_trans (Nat.min_le_left _ _) (minWeight_le_init _ _)
  · rw [hw]
    obtain ⟨w, hwv, hmem | hmem⟩ := split_logical_parent s hnd T hg σ v hv
    · exact Nat.le_trans (Nat.min_le_left _ _)
        (Nat.le_trans (minWeight_le_of_mem _ _ hmem) hwv)
    · exact Nat.le_trans (Nat.min_le_right _ _)
        (Nat.le_trans (minWeight_le_of_mem _ _ hmem) hwv)

/-- The full distance is unchanged by the split-subset Hadamard (§4.27(b)). -/
theorem exactDistance_split_min (s : CodeState) (hnd : s.Q.Nodup) (T : List Nat)
    (hg : splitGuard s T = true) :
    min (exactDistance Sector.X (splitHadamardState s T))
        (exactDistance Sector.Z (splitHadamardState s T)) =
      min (exactDistance Sector.X s) (exactDistance Sector.Z s) := by
  have a1 := exactDistance_split_ge s hnd T Sector.X
  have a2 := exactDistance_split_ge s hnd T Sector.Z
  have b1 := exactDistance_split_le s hnd T hg Sector.X
  have b2 := exactDistance_split_le s hnd T hg Sector.Z
  simp only [oppositeSector] at a1 a2 b1 b2
  omega

/-! ## The `Option Nat` reading -/

theorem exactDistOpt_eq (σ : Sector) (s : CodeState) :
    exactDistOpt σ s =
      if exactDistance σ s = s.Q.length + 1 then none else some (exactDistance σ s) := rfl

theorem minOpt_sentinel (n a b : Nat) (ha : a ≤ n + 1) (hb : b ≤ n + 1) :
    minOpt (if a = n + 1 then none else some a) (if b = n + 1 then none else some b) =
      if min a b = n + 1 then none else some (min a b) := by
  by_cases h1 : a = n + 1
  · by_cases h2 : b = n + 1
    · rw [if_pos h1, if_pos h2, if_pos (by rw [h1, h2, Nat.min_self])]
      rfl
    · have hm : min a b = b := Nat.min_eq_right (by omega)
      rw [if_pos h1, if_neg h2, hm, if_neg h2]
      rfl
  · by_cases h2 : b = n + 1
    · have hm : min a b = a := Nat.min_eq_left (by omega)
      rw [if_neg h1, if_pos h2, hm, if_neg h1]
      rfl
    · have hm : min a b ≠ n + 1 := by
        have := Nat.min_le_left a b
        omega
      rw [if_neg h1, if_neg h2, if_neg hm]
      rfl

theorem leOpt_sentinel (n a b : Nat) (hb : b ≤ n + 1) (h : a ≤ b) :
    leOpt (if a = n + 1 then none else some a) (if b = n + 1 then none else some b) := by
  by_cases h1 : a = n + 1 <;> by_cases h2 : b = n + 1 <;> simp [h1, h2, leOpt] <;> omega

theorem exactDist_full_sentinel (s : CodeState) :
    (exactDist s).full =
      if min (exactDistance Sector.X s) (exactDistance Sector.Z s) = s.Q.length + 1 then none
      else some (min (exactDistance Sector.X s) (exactDistance Sector.Z s)) := by
  show minOpt (exactDistOpt Sector.X s) (exactDistOpt Sector.Z s) = _
  rw [exactDistOpt_eq, exactDistOpt_eq]
  exact minOpt_sentinel _ _ _ (exactDistance_le_sentinel _ _) (exactDistance_le_sentinel _ _)

/-- §4.27(b) for the exact distance: the full distance is unchanged, and each
    child sector distance is bounded below by the parent's full distance. -/
theorem exactDist_splitHadamardState (s : CodeState) (hnd : s.Q.Nodup) (T : List Nat)
    (hg : splitGuard s T = true) :
    (exactDist (splitHadamardState s T)).full = (exactDist s).full ∧
    leOpt (exactDist s).full (exactDist (splitHadamardState s T)).x ∧
    leOpt (exactDist s).full (exactDist (splitHadamardState s T)).z := by
  refine ⟨?_, ?_, ?_⟩
  · rw [exactDist_full_sentinel, exactDist_full_sentinel, exactDistance_split_min s hnd T hg,
      splitHadamardState_Q]
  · rw [exactDist_full_sentinel]
    show leOpt _ (exactDistOpt Sector.X (splitHadamardState s T))
    rw [exactDistOpt_eq, splitHadamardState_Q]
    have h := exactDistance_split_ge s hnd T Sector.X
    simp only [oppositeSector] at h
    have hs := exactDistance_le_sentinel Sector.X (splitHadamardState s T)
    rw [splitHadamardState_Q] at hs
    exact leOpt_sentinel _ _ _ hs h
  · rw [exactDist_full_sentinel]
    show leOpt _ (exactDistOpt Sector.Z (splitHadamardState s T))
    rw [exactDistOpt_eq, splitHadamardState_Q]
    have h := exactDistance_split_ge s hnd T Sector.Z
    simp only [oppositeSector] at h
    have hs := exactDistance_le_sentinel Sector.Z (splitHadamardState s T)
    rw [splitHadamardState_Q] at hs
    exact leOpt_sentinel _ _ _ hs (by rw [Nat.min_comm]; exact h)

end CodeCalculus
