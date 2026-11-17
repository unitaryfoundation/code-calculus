import CodeCalculus.ExactDirectSum

/-!
# The exact distance does not depend on the order of the namespace (issue #367)

`E-EXTEND` with `Δ = ∅` appends rows and re-sorts the qubit list
(`extendState`), so its addition law for the exact distance needs the
distance to be invariant under a reordering of `Q`
(`exactDistance?_perm`). With that, the §4.30 law with `Δ = ∅` is the
row-space monotonicity of `Gate6Exact.lean` on the re-sorted namespace
(`exactDist_extend_nil`).

A vector over a repeat-free `Q` is `Q.map f` for the function `f` that reads
it (`valueAt`). Reindexing to a reordering `Q'` is `Q'.map f`. Weight and
overlap parity are counts over `Q`, which a permutation preserves, and
reindexing is linear, so it maps the span of the rows over `Q` into their
span over `Q'`.
-/

namespace CodeCalculus

/-! ## Reading a vector by qubit -/

/-- The entry of `v` at the first occurrence of `q` in `Q`, `false` if none. -/
def valueAt : List Nat → List Bool → Nat → Bool
  | q' :: Q, b :: v, q => if q' = q then b else valueAt Q v q
  | _, _, _ => false

/-- The vector over `Q'` that reads `v`, a vector over `Q`, qubit by qubit. -/
def reindex (Q Q' : List Nat) (v : List Bool) : List Bool := Q'.map (valueAt Q v)

theorem valueAt_map (f : Nat → Bool) : ∀ (Q : List Nat) (q : Nat), q ∈ Q →
    valueAt Q (Q.map f) q = f q
  | [], _, h => nomatch h
  | q' :: Q, q, h => by
      show (if q' = q then f q' else valueAt Q (Q.map f) q) = f q
      rcases Decidable.em (q' = q) with heq | hne
      · rw [if_pos heq, heq]
      · rw [if_neg hne]
        rcases List.mem_cons.mp h with h' | h'
        · exact absurd h'.symm hne
        · exact valueAt_map f Q q h'

theorem map_valueAt : ∀ (Q : List Nat) (v : List Bool), Q.Nodup → v.length = Q.length →
    Q.map (valueAt Q v) = v
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | q' :: Q, b :: v, hnd, hlen => by
      rw [List.nodup_cons] at hnd
      rw [List.map_cons]
      have hhead : valueAt (q' :: Q) (b :: v) q' = b := by
        show (if q' = q' then b else valueAt Q v q') = b
        rw [if_pos rfl]
      have htail : Q.map (valueAt (q' :: Q) (b :: v)) = Q.map (valueAt Q v) := by
        apply List.map_congr_left
        intro q hq
        show (if q' = q then b else valueAt Q v q) = valueAt Q v q
        rw [if_neg (fun (h : q' = q) => hnd.1 (by rw [h]; exact hq))]
      rw [hhead, htail, map_valueAt Q v hnd.2 (Nat.succ.inj hlen)]

theorem reindex_length (Q Q' : List Nat) (v : List Bool) : (reindex Q Q' v).length = Q'.length :=
  List.length_map ..

/-- Reindexing a row's vector gives the row's vector over the other list. -/
theorem reindex_rowVector (Q Q' : List Nat) (r : Row) (hsub : ∀ q ∈ Q', q ∈ Q) :
    reindex Q Q' (rowVector Q r) = rowVector Q' r := by
  unfold reindex rowVector
  apply List.map_congr_left
  intro q hq
  exact valueAt_map _ Q q (hsub q hq)

/-- Reindexing back recovers the vector. -/
theorem reindex_reindex (Q Q' : List Nat) (v : List Bool) (hnd : Q.Nodup)
    (hlen : v.length = Q.length) (hsub : ∀ q ∈ Q, q ∈ Q') :
    reindex Q' Q (reindex Q Q' v) = v := by
  unfold reindex
  have h : Q.map (valueAt Q' (Q'.map (valueAt Q v))) = Q.map (valueAt Q v) := by
    apply List.map_congr_left
    intro q hq
    exact valueAt_map _ Q' q (hsub q hq)
  rw [h, map_valueAt Q v hnd hlen]

/-! ## Reindexing is linear -/

theorem valueAt_xorVec : ∀ (Q : List Nat) (a b : List Bool) (q : Nat), a.length = b.length →
    valueAt Q (xorVec a b) q = (valueAt Q a q != valueAt Q b q)
  | [], a, b, _, _ => by
      cases a <;> cases b <;> rfl
  | _ :: _, [], [], _, _ => rfl
  | _ :: _, [], _ :: _, _, h => by cases h
  | _ :: _, _ :: _, [], _, h => by cases h
  | q' :: Q, x :: a, y :: b, q, h => by
      show (if q' = q then (x != y) else valueAt Q (xorVec a b) q) =
        ((if q' = q then x else valueAt Q a q) != (if q' = q then y else valueAt Q b q))
      rcases Decidable.em (q' = q) with heq | hne
      · rw [if_pos heq, if_pos heq, if_pos heq]
      · rw [if_neg hne, if_neg hne, if_neg hne]
        exact valueAt_xorVec Q a b q (Nat.succ.inj h)

theorem xorVec_map_map (f g : Nat → Bool) : ∀ L : List Nat,
    xorVec (L.map f) (L.map g) = L.map (fun q => f q != g q)
  | [] => rfl
  | q :: L => by
      rw [List.map_cons, List.map_cons, List.map_cons, xorVec_cons, xorVec_map_map f g L]

theorem reindex_xorVec (Q Q' : List Nat) (a b : List Bool) (h : a.length = b.length) :
    reindex Q Q' (xorVec a b) = xorVec (reindex Q Q' a) (reindex Q Q' b) := by
  unfold reindex
  rw [xorVec_map_map]
  apply List.map_congr_left
  intro q _
  exact valueAt_xorVec Q a b q h

theorem valueAt_replicate_false : ∀ (Q : List Nat) (n q : Nat),
    valueAt Q (List.replicate n false) q = false
  | [], n, _ => by cases n <;> rfl
  | _ :: _, 0, _ => rfl
  | q' :: Q, n + 1, q => by
      rw [List.replicate_succ]
      show (if q' = q then false else valueAt Q (List.replicate n false) q) = false
      rcases Decidable.em (q' = q) with heq | hne
      · rw [if_pos heq]
      · rw [if_neg hne]
        exact valueAt_replicate_false Q n q

theorem reindex_replicate_false (Q Q' : List Nat) (n : Nat) :
    reindex Q Q' (List.replicate n false) = List.replicate Q'.length false := by
  unfold reindex
  rw [List.eq_replicate_iff]
  refine ⟨List.length_map .., ?_⟩
  intro b hb
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hb
  exact valueAt_replicate_false Q n q

theorem reindex_combineRows (Q Q' : List Nat) (n : Nat) :
    ∀ (vs : List (List Bool)) (cs : List Bool), (∀ v ∈ vs, v.length = n) →
      reindex Q Q' (combineRows n vs cs) =
        combineRows Q'.length (vs.map (reindex Q Q')) cs
  | [], cs, _ => by
      show reindex Q Q' (List.replicate n false) = List.replicate Q'.length false
      exact reindex_replicate_false Q Q' n
  | v :: vs, [], _ => by
      show reindex Q Q' (List.replicate n false) = List.replicate Q'.length false
      exact reindex_replicate_false Q Q' n
  | v :: vs, true :: cs, h => by
      have hvs : ∀ w ∈ vs, w.length = n := fun w hw => h w (List.mem_cons_of_mem v hw)
      show reindex Q Q' (xorVec v (combineRows n vs cs)) =
        xorVec (reindex Q Q' v) (combineRows Q'.length (vs.map (reindex Q Q')) cs)
      rw [reindex_xorVec Q Q' _ _ (by
        rw [h v (List.mem_cons_self ..), combineRows_length n vs cs hvs]),
        reindex_combineRows Q Q' n vs cs hvs]
  | v :: vs, false :: cs, h => by
      have hvs : ∀ w ∈ vs, w.length = n := fun w hw => h w (List.mem_cons_of_mem v hw)
      show reindex Q Q' (combineRows n vs cs) =
        combineRows Q'.length (vs.map (reindex Q Q')) cs
      exact reindex_combineRows Q Q' n vs cs hvs

/-- Reindexing maps the span of the rows over `Q` into their span over `Q'`. -/
theorem inSpanRows_reindex (Q Q' : List Nat) (rows : List Row) (v : List Bool)
    (hsub : ∀ q ∈ Q', q ∈ Q) (h : inSpanRows Q rows v) :
    inSpanRows Q' rows (reindex Q Q' v) := by
  obtain ⟨cs, hlen, hcomb⟩ := h
  refine ⟨cs, hlen, ?_⟩
  rw [← hcomb, reindex_combineRows Q Q' Q.length _ cs (rowVectors_length Q rows), List.map_map]
  congr 1
  apply List.map_congr_left
  intro r _
  exact (reindex_rowVector Q Q' r hsub).symm

/-! ## Counts over a permuted namespace -/

theorem weight_map_perm (f : Nat → Bool) {Q Q' : List Nat} (h : Q'.Perm Q) :
    weight (Q'.map f) = weight (Q.map f) := by
  unfold weight
  exact (h.map f).count_eq true

theorem dotPar_map_perm (f g : Nat → Bool) {Q Q' : List Nat} (h : Q'.Perm Q) :
    dotPar (Q'.map f) (Q'.map g) = dotPar (Q.map f) (Q.map g) := by
  rw [dotPar_map_map, dotPar_map_map]
  exact (h.filter _).length_eq

/-! ## Invariance -/

/-- A logical over `Q`, reindexed to a reordering `Q'`, is a logical there of
    the same weight. The two states display the same rows. -/
theorem logical_reindex {s t : CodeState} (hrows : t.rows = s.rows) (hperm : t.Q.Perm s.Q)
    (hnd : s.Q.Nodup) (σ : Sector) {v : List Bool} (hv : v ∈ logicalVectors s σ) :
    reindex s.Q t.Q v ∈ logicalVectors t σ ∧ weight (reindex s.Q t.Q v) = weight v := by
  obtain ⟨hlen, hlog⟩ := (mem_logicalVectors_iff _ _ _).mp hv
  obtain ⟨horth, hspan⟩ := (isLogicalBool_iff_prop _ _ _).mp hlog
  have hsec : ∀ τ, sectorRows t τ = sectorRows s τ := by
    intro τ
    unfold sectorRows
    rw [hrows]
  have hts : ∀ q ∈ t.Q, q ∈ s.Q := fun q hq => hperm.mem_iff.mp hq
  have hst : ∀ q ∈ s.Q, q ∈ t.Q := fun q hq => hperm.mem_iff.mpr hq
  have hvmap : s.Q.map (valueAt s.Q v) = v := map_valueAt s.Q v hnd hlen
  refine ⟨?_, ?_⟩
  · rw [mem_logicalVectors_iff]
    refine ⟨by rw [reindex_length, hperm.length_eq], ?_⟩
    rw [isLogicalBool_iff_prop]
    refine ⟨?_, ?_⟩
    · intro r hr
      rw [hsec] at hr
      have h0 := horth r hr
      rw [← hvmap] at h0
      show dotPar (t.Q.map (valueAt s.Q v)) (t.Q.map (fun q => r.support.contains q)) % 2 = 0
      rw [dotPar_map_perm _ _ hperm]
      exact h0
    · intro hin
      rw [hsec] at hin
      have hback := inSpanRows_reindex t.Q s.Q _ _ hst hin
      rw [reindex_reindex s.Q t.Q v hnd hlen hst] at hback
      exact hspan hback
  · show weight (t.Q.map (valueAt s.Q v)) = weight v
    rw [weight_map_perm _ hperm, hvmap]

/-- The exact sector distance does not depend on the order of the namespace. -/
theorem exactDistance?_perm {s t : CodeState} (hrows : t.rows = s.rows) (hperm : t.Q.Perm s.Q)
    (hnd : s.Q.Nodup) (σ : Sector) : exactDistance? σ t = exactDistance? σ s := by
  have hndt : t.Q.Nodup := hperm.nodup_iff.mpr hnd
  apply leOpt_antisymm
  · apply leOpt_exactDistance?_of_map
    intro v hv
    obtain ⟨hmem, hw⟩ := logical_reindex hrows hperm hnd σ hv
    exact ⟨_, hmem, Nat.le_of_eq hw⟩
  · apply leOpt_exactDistance?_of_map
    intro v hv
    obtain ⟨hmem, hw⟩ := logical_reindex hrows.symm hperm.symm hndt σ hv
    exact ⟨_, hmem, Nat.le_of_eq hw⟩

/-- `exactDist` does not depend on the order of the namespace. -/
theorem exactDist_perm {s t : CodeState} (hrows : t.rows = s.rows) (hperm : t.Q.Perm s.Q)
    (hnd : s.Q.Nodup) : exactDist t = exactDist s := by
  have h : ∀ σ, exactDistOpt σ t = exactDistOpt σ s := by
    intro σ
    rw [exactDistOpt_eq_exactDistance?, exactDistOpt_eq_exactDistance?]
    exact exactDistance?_perm hrows hperm hnd σ
  unfold exactDist
  rw [h Sector.X, h Sector.Z]

end CodeCalculus
