import CodeCalculus.Eval
import CodeCalculus.WellFormedness
import CodeCalculus.RanksFit
import CodeCalculus.MixSupport
import CodeCalculus.RebaseRankSector
import CodeCalculus.GraftWellFormedness

/-!
# Well-formedness of the rebase update (WP6)

`Eval.rebase` carries `EncodingWellFormed s'` as a premise, mirroring the
consumer's validity report on the output (`spec/OPERATIONAL_SEMANTICS.md`
§4.25). Review finding RG-17 of  observed that nothing in the
development derived that premise. This module does: a well-formed parent and
an invertible 0/1 matrix give a well-formed rebased state (`wf_rebaseState`),
so the premise is discharged by the constructor's other premises
(`eval_rebase_of_wf`). The constructor itself is unchanged.

The argument. The other sector's display is retained, so its rows keep every
list-level property. A minted row's support is the symmetric difference of
the selected sector's supports chosen by a 0/1 coefficient row, sorted: it
lies inside `Q`, has no repeats, and is sorted. Its bitmask is the `F_2`
combination of the old masks (`rowBitmask_mixSupport`), hence in their span,
and the parent's I1 makes every old mask orthogonal to every other-sector mask,
so the combination is too (`orth_of_inSpan_left`). Identifiers are the minted
fresh ones, disjoint from `used` and from each other. I2 follows from rank
counting: the rebased sector keeps its rank (`sectorRank_rebaseState`), which
equals its display length on the parent (`sectorRank_eq_length_of_I2`), and
the new display has that many rows; the other sector is unchanged; a state of
full rank in both sectors satisfies I2 (`i2_of_full_rank`).
-/

namespace CodeCalculus

/-! ## The mixing fold -/

/-- Every qubit of the fold's result is in the accumulator or in a selected
    row's support. -/
theorem mem_foldl_mix {f : List Nat → Row × Nat → List Nat}
    (hf : ∀ acc r c, f acc (r, c) = if c = 1 then xorList acc r.support else acc) {q : Nat} :
    ∀ (ordered : List Row) (cs acc : List Nat),
      q ∈ (ordered.zip cs).foldl f acc → q ∈ acc ∨ ∃ r ∈ ordered, q ∈ r.support
  | [], cs, acc, h => by
      simp only [List.zip_nil_left, List.foldl_nil] at h
      exact Or.inl h
  | _ :: _, [], acc, h => by
      simp only [List.zip_nil_right, List.foldl_nil] at h
      exact Or.inl h
  | r :: rs, c :: cs', acc, h => by
      rw [List.zip_cons_cons, List.foldl_cons, hf] at h
      rcases mem_foldl_mix hf rs cs' _ h with hacc | ⟨r', hr', hq⟩
      · by_cases hc : c = 1
        · simp only [hc, ↓reduceIte] at hacc
          rcases mem_xorList.mp hacc with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact Or.inl h1
          · exact Or.inr ⟨r, List.mem_cons_self .., h1⟩
        · simp only [hc, ↓reduceIte] at hacc
          exact Or.inl hacc
      · exact Or.inr ⟨r', List.mem_cons_of_mem r hr', hq⟩

/-- The symmetric difference of two repeat-free lists is repeat-free. -/
theorem nodup_xorList {a b : List Nat} (ha : a.Nodup) (hb : b.Nodup) :
    (xorList a b).Nodup := by
  unfold xorList
  rw [List.nodup_append]
  refine ⟨ha.filter _, hb.filter _, ?_⟩
  intro x hx y hy hxy
  subst hxy
  have hx' := List.mem_filter.mp hx
  have hy' := List.mem_filter.mp hy
  have h1 : ¬ b.contains x = true := by simpa using hx'.2
  exact h1 (List.contains_iff_mem.mpr hy'.1)

/-- The fold keeps supports repeat-free. -/
theorem nodup_foldl_mix {f : List Nat → Row × Nat → List Nat}
    (hf : ∀ acc r c, f acc (r, c) = if c = 1 then xorList acc r.support else acc) :
    ∀ (ordered : List Row) (cs acc : List Nat), acc.Nodup →
      (∀ r ∈ ordered, r.support.Nodup) → ((ordered.zip cs).foldl f acc).Nodup
  | [], cs, acc, hacc, _ => by simpa using hacc
  | _ :: _, [], acc, hacc, _ => by simpa using hacc
  | r :: rs, c :: cs', acc, hacc, hrows => by
      rw [List.zip_cons_cons, List.foldl_cons, hf]
      apply nodup_foldl_mix hf rs cs' _ ?_ (fun r' hr' => hrows r' (List.mem_cons_of_mem r hr'))
      by_cases hc : c = 1
      · simp only [hc, ↓reduceIte]
        exact nodup_xorList hacc (hrows r (List.mem_cons_self ..))
      · simp only [hc, ↓reduceIte]
        exact hacc

theorem mem_mixSupport {q : Nat} (ordered : List Row) (cs : List Nat)
    (h : q ∈ mixSupport ordered cs) : ∃ r ∈ ordered, q ∈ r.support := by
  unfold mixSupport at h
  have h' := (sortNat_perm _).mem_iff.mp h
  rcases mem_foldl_mix (fun _ _ _ => rfl) ordered cs [] h' with h0 | h1
  · cases h0
  · exact h1

theorem mixSupport_nodup (ordered : List Row) (cs : List Nat)
    (h : ∀ r ∈ ordered, r.support.Nodup) : (mixSupport ordered cs).Nodup := by
  unfold mixSupport
  exact (sortNat_perm _).nodup_iff.mpr
    (nodup_foldl_mix (fun _ _ _ => rfl) ordered cs [] List.nodup_nil h)

theorem mixSupport_sorted (ordered : List Row) (cs : List Nat) :
    (mixSupport ordered cs).Pairwise (· ≤ ·) := by
  unfold mixSupport
  exact sortNat_sorted _

/-! ## The minted rows -/

/-- The rows the rebase mints. -/
def rebaseNewRows (s : CodeState) (sector : Sector) (M : List (List Nat)) : List Row :=
  (M.zip (mintFresh s.used M.length)).map
    (fun cs_id => ⟨cs_id.2, sector, mixSupport (sectorRows s sector) cs_id.1⟩)

theorem rebaseState_rows (s : CodeState) (sector : Sector) (M : List (List Nat)) :
    (rebaseState s sector M).rows =
      s.rows.filter (fun r => r.sector ≠ sector) ++ rebaseNewRows s sector M := rfl

theorem rebaseState_used (s : CodeState) (sector : Sector) (M : List (List Nat)) :
    (rebaseState s sector M).used = s.used ++ mintFresh s.used M.length := rfl

theorem mem_rebaseNewRows {s : CodeState} {sector : Sector} {M : List (List Nat)} {u : Row}
    (h : u ∈ rebaseNewRows s sector M) :
    ∃ cs id, (cs, id) ∈ M.zip (mintFresh s.used M.length) ∧
      u = ⟨id, sector, mixSupport (sectorRows s sector) cs⟩ := by
  unfold rebaseNewRows at h
  obtain ⟨⟨cs, id⟩, hmem, rfl⟩ := List.mem_map.mp h
  exact ⟨cs, id, hmem, rfl⟩

theorem map_snd_zip_of_length_eq {α β : Type} :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length → (xs.zip ys).map Prod.snd = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
      rw [List.zip_cons_cons, List.map_cons]
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rw [map_snd_zip_of_length_eq xs ys h]

theorem rebaseNewRows_ids (s : CodeState) (sector : Sector) (M : List (List Nat)) :
    (rebaseNewRows s sector M).map Row.id = mintFresh s.used M.length := by
  unfold rebaseNewRows
  rw [List.map_map]
  have hcomp : (Row.id ∘ fun cs_id : List Nat × Nat =>
      (⟨cs_id.2, sector, mixSupport (sectorRows s sector) cs_id.1⟩ : Row)) = Prod.snd := by
    funext p; rfl
  rw [hcomp]
  exact map_snd_zip_of_length_eq _ _ (by rw [mintFresh_length])

/-! ## The theorem -/

/-- A well-formed parent and an invertible 0/1 matrix give a well-formed
    rebased state. -/
theorem wf_rebaseState (s : CodeState) (sector : Sector) (M : List (List Nat))
    (hwf : EncodingWellFormed s)
    (hok : rebaseMatrix_ok M (sectorRows s sector).length) :
    EncodingWellFormed (rebaseState s sector M) := by
  have hidused := ids_subset_used_of_wf hwf
  have hsupQ := supports_subset_of_wf hwf
  obtain ⟨hQ, hids, hused, hsup, hnd, hsort, hI1, hI2⟩ := hwf
  have htrows := rebaseState_rows s sector M
  have htused := rebaseState_used s sector M
  have hkeep_sub : (s.rows.filter (fun r => r.sector ≠ sector)).Sublist s.rows :=
    List.filter_sublist
  have hrow_nd : ∀ r ∈ s.rows, r.support.Nodup := by
    intro r hr
    have := List.all_eq_true.mp hnd r hr
    simpa using this
  have hord_nd : ∀ r ∈ sectorRows s sector, r.support.Nodup :=
    fun r hr => hrow_nd r (List.mem_filter.mp hr).1
  have hord_Q : ∀ r ∈ sectorRows s sector, ∀ q ∈ r.support, q ∈ s.Q :=
    fun r hr => hsupQ r (List.mem_filter.mp hr).1
  have hnew_nd : ∀ u ∈ rebaseNewRows s sector M, u.support.Nodup := by
    intro u hu
    obtain ⟨cs, id, _, rfl⟩ := mem_rebaseNewRows hu
    exact mixSupport_nodup _ _ hord_nd
  have hnew_sorted : ∀ u ∈ rebaseNewRows s sector M, u.support.Pairwise (· ≤ ·) := by
    intro u hu
    obtain ⟨cs, id, _, rfl⟩ := mem_rebaseNewRows hu
    exact mixSupport_sorted _ _
  have hnew_Q : ∀ u ∈ rebaseNewRows s sector M, ∀ q ∈ u.support, q ∈ s.Q := by
    intro u hu q hq
    obtain ⟨cs, id, _, rfl⟩ := mem_rebaseNewRows hu
    obtain ⟨r, hr, hqr⟩ := mem_mixSupport _ _ hq
    exact hord_Q r hr q hqr
  have hnew_sec : ∀ u ∈ rebaseNewRows s sector M, u.sector = sector := by
    intro u hu
    obtain ⟨cs, id, _, rfl⟩ := mem_rebaseNewRows hu
    rfl
  have hkeep_ne : ∀ r ∈ s.rows.filter (fun r => r.sector ≠ sector), r.sector ≠ sector := by
    intro r hr
    simpa using (List.mem_filter.mp hr).2
  have hids_t : ((rebaseState s sector M).rows.map Row.id).Nodup := by
    rw [htrows, List.map_append, rebaseNewRows_ids, List.nodup_append]
    refine ⟨hids.sublist (hkeep_sub.map Row.id), mintFresh_nodup _ _, ?_⟩
    intro x hx y hy hxy
    subst hxy
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    exact mintFresh_not_mem s.used _ _ hy (hidused r (hkeep_sub.subset hr))
  -- orthogonality of a minted row against a retained row of the other sector
  have hnew_orth : ∀ u ∈ rebaseNewRows s sector M, ∀ z ∈ s.rows, z.sector ≠ sector →
      Orth s.Q.length (rowBitmask s.Q u) (rowBitmask s.Q z) := by
    intro u hu z hz hzsec
    obtain ⟨cs, id, hmem, rfl⟩ := mem_rebaseNewRows hu
    have hcs : cs ∈ M := (List.of_mem_zip hmem).1
    have hcslen : cs.length = (sectorRows s sector).length := (hok.2.1 cs hcs).1
    have hcs01 : ∀ c ∈ cs, c = 0 ∨ c = 1 := (hok.2.1 cs hcs).2
    have hspan : inSpanMasks ((sectorRows s sector).map (rowBitmask s.Q))
        (rowBitmask s.Q ⟨id, sector, mixSupport (sectorRows s sector) cs⟩) :=
      ⟨cs, by rw [List.length_map, hcslen], hcs01,
        (rowBitmask_mixSupport s.Q _ cs id sector).symm⟩
    apply orth_of_inSpan_left s.Q.length hspan
    intro m hm
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
    have hr_rows : r ∈ s.rows := (List.mem_filter.mp hr).1
    have hr_sec : r.sector = sector := by simpa using (List.mem_filter.mp hr).2
    unfold Orth
    cases sector with
    | X =>
        have hzZ : z.sector = Sector.Z := by
          cases hzs : z.sector
          · exact absurd hzs hzsec
          · rfl
        rw [dotCount_rowBitmask s.Q hQ r z (hord_nd r hr) (hord_Q r hr)]
        exact hI1 r z hr_rows hz hr_sec hzZ
    | Z =>
        have hzX : z.sector = Sector.X := by
          cases hzs : z.sector
          · rfl
          · exact absurd hzs hzsec
        rw [dotCount_comm, dotCount_rowBitmask s.Q hQ z r (hrow_nd z hz) (hsupQ z hz)]
        exact hI1 z r hz hr_rows hzX hr_sec
  refine ⟨hQ, hids_t, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.all_eq_true]
    intro x hx
    rw [htrows, List.map_append] at hx
    show (rebaseState s sector M).used.contains x = true
    rw [htused, List.contains_iff_mem]
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
      exact List.mem_append_left _ (hidused r (hkeep_sub.subset hr))
    · rw [rebaseNewRows_ids] at hx
      exact List.mem_append_right _ hx
  · rw [List.all_eq_true]
    intro u hu
    rw [htrows] at hu
    show u.support.all (fun q => s.Q.contains q) = true
    rcases List.mem_append.mp hu with hu | hu
    · exact List.all_eq_true.mp hsup u (hkeep_sub.subset hu)
    · rw [List.all_eq_true]
      intro q hq
      exact List.contains_iff_mem.mpr (hnew_Q u hu q hq)
  · rw [List.all_eq_true]
    intro u hu
    rw [htrows] at hu
    rcases List.mem_append.mp hu with hu | hu
    · exact List.all_eq_true.mp hnd u (hkeep_sub.subset hu)
    · exact decide_eq_true (hnew_nd u hu)
  · rw [List.all_eq_true]
    intro u hu
    rw [htrows] at hu
    rcases List.mem_append.mp hu with hu | hu
    · exact List.all_eq_true.mp hsort u (hkeep_sub.subset hu)
    · exact decide_eq_true (hnew_sorted u hu)
  · intro rX rZ hX hZ hsX hsZ
    rw [htrows] at hX hZ
    rcases List.mem_append.mp hX with hX | hX <;> rcases List.mem_append.mp hZ with hZ | hZ
    · exact hI1 rX rZ (hkeep_sub.subset hX) (hkeep_sub.subset hZ) hsX hsZ
    · have horth := hnew_orth rZ hZ rX (hkeep_sub.subset hX) (hkeep_ne rX hX)
      unfold Orth at horth
      rw [dotCount_comm, dotCount_rowBitmask s.Q hQ rX rZ
        (hrow_nd rX (hkeep_sub.subset hX)) (hsupQ rX (hkeep_sub.subset hX))] at horth
      exact horth
    · have horth := hnew_orth rX hX rZ (hkeep_sub.subset hZ) (hkeep_ne rZ hZ)
      unfold Orth at horth
      rw [dotCount_rowBitmask s.Q hQ rX rZ (hnew_nd rX hX) (hnew_Q rX hX)] at horth
      exact horth
    · have h1 := hnew_sec rX hX
      have h2 := hnew_sec rZ hZ
      rw [hsX] at h1
      rw [hsZ] at h2
      rw [← h1] at h2
      exact absurd h2 (by decide)
  · apply i2_of_full_rank (rebaseState s sector M) hQ hids_t
    intro σ
    have hlen_sec : sectorRank s.Q s.rows sector = (sectorRows s sector).length :=
      sectorRank_eq_length_of_I2 s hQ hids hI2 sector
    rcases sector_eq_or_opp σ sector with rfl | hσ
    · show sectorRank s.Q (rebaseState s σ M).rows σ = (sectorRows (rebaseState s σ M) σ).length
      rw [sectorRank_rebaseState s σ M hok, hlen_sec, sectorRows_rebaseState, List.length_map,
        List.length_zip, mintFresh_length, Nat.min_self]
      exact hok.1.symm
    · subst hσ
      show sectorRank s.Q (rebaseState s sector M).rows (oppositeSector sector)
        = (sectorRows (rebaseState s sector M) (oppositeSector sector)).length
      have hrows_eq := sectorRows_rebaseState_other s sector M
      rw [sectorRank_congr_rows s.Q (oppositeSector sector) hrows_eq, hrows_eq]
      exact sectorRank_eq_length_of_I2 s hQ hids hI2 _

/-- The output well-formedness premise of `Eval.rebase` is discharged by the
    other premises: a well-formed parent with a nonempty display and an
    invertible matrix evaluates. -/
theorem eval_rebase_of_wf (s : CodeState) (sector : Sector) (M : List (List Nat))
    (hwf : EncodingWellFormed s) (hne : sectorRows s sector ≠ [])
    (hok : rebaseMatrix_ok M (sectorRows s sector).length) :
    Eval (Command.rebase sector M) s (rebaseState s sector M) :=
  Eval.rebase hne hok rfl (wf_rebaseState s sector M hwf hok)

end CodeCalculus
