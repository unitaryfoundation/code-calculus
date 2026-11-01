import CodeCalculus.MixSupport
import CodeCalculus.MaskRank
import CodeCalculus.RebaseRank

namespace CodeCalculus

/-! ### Assembly: rebase preserves the displayed-sector rank

The general (arbitrary-GL) rebase rank statement for `sectorRank`. Following
the review of the conditional development: `Eval.rebase` asks
`EncodingWellFormed` of the *output* only, so the rank statement carries no
hypothesis on the source state — `rebaseMatrix_ok M (sectorRows s sector).length`
suffices. The argument:

- the new sector's masks are the old masks combined by the matrix's
  coefficient rows (`rowBitmask_mixSupport`, unconditional);
- each new mask lies in the old span, and conversely each old mask lies in
  the new span, because the rank clause of `rebaseMatrix_ok` makes every unit
  vector a 0/1 combination of the matrix's column-position row masks
  (`rebaseMatrix_unit_rows`) and the composition lemma transports that
  through `combineCoeffRowsM`;
- the greedy rank is determined by the F₂ span (`rankBitmasks_eq_of_span_eq`),
  so the two ranks agree.

`sectorRank_rebaseState_of_eval` records the instantiation from the
`Eval.rebase` premises, and `sectorRank_rebaseState_shear_example` pins the
decided two-row shear instance carried by the earlier elementary slice. -/

theorem mintFresh_length (used : List Nat) (n : Nat) :
    (mintFresh used n).length = n := by
  induction n generalizing used with
  | zero => rfl
  | succ n ih => simp [mintFresh, ih]

/-- The displayed rows of a rebased sector are exactly the newly minted rows. -/
theorem sectorRows_rebaseState (s : CodeState) (sector : Sector)
    (matrix : List (List Nat)) :
    sectorRows (rebaseState s sector matrix) sector
      = (matrix.zip (mintFresh s.used matrix.length)).map
          (fun cs_id =>
            ⟨cs_id.2, sector, mixSupport (sectorRows s sector) cs_id.1⟩) := by
  unfold sectorRows rebaseState
  simp only [List.filter_append, List.filter_map, List.filter_filter]
  have hnil : List.filter
      (fun x => decide (x.sector = sector) && decide (x.sector ≠ sector))
      s.rows = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x _
    by_cases hx : x.sector = sector <;> simp [hx]
  rw [hnil, List.nil_append]
  have hfilter : List.filter
      ((fun r => decide (r.sector = sector)) ∘ fun cs_id =>
        (⟨cs_id.2, sector, mixSupport (sectorRows s sector) cs_id.1⟩ : Row))
      (matrix.zip (mintFresh s.used matrix.length))
      = matrix.zip (mintFresh s.used matrix.length) := by
    apply List.filter_eq_self.mpr
    intro p _
    simp
  rw [hfilter]
  simp [sectorRows]

theorem mem_zip_left {α β : Type} :
    ∀ {l₁ : List α} {l₂ : List β} {p : α × β}, p ∈ l₁.zip l₂ → p.1 ∈ l₁
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: as, b :: bs, p, h => by
      simp only [List.zip_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (mem_zip_left h)

theorem map_zip_left {α β γ : Type} (f : α → γ) :
    ∀ (l₁ : List α) (l₂ : List β), l₂.length = l₁.length →
      (l₁.zip l₂).map (fun p => f p.1) = l₁.map f := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ h
      cases l₂ with
      | nil => simp
      | cons b bs => simp at h
  | cons a as ih =>
      intro l₂ h
      cases l₂ with
      | nil => simp at h
      | cons b bs =>
          simp only [List.zip_cons_cons, List.map_cons]
          rw [ih bs (by simpa using h)]

theorem oppositeSector_ne (sec : Sector) : oppositeSector sec ≠ sec := by
  cases sec <;> simp [oppositeSector]

/-- The other sector's display is untouched by a rebase. -/
theorem sectorRows_rebaseState_other (s : CodeState) (sector : Sector)
    (matrix : List (List Nat)) :
    sectorRows (rebaseState s sector matrix) (oppositeSector sector)
      = sectorRows s (oppositeSector sector) := by
  unfold sectorRows rebaseState
  simp only [List.filter_append, List.filter_filter]
  have hnil : List.filter (fun x => decide (x.sector = oppositeSector sector))
      ((matrix.zip (mintFresh s.used matrix.length)).map
        (fun cs_id => (⟨cs_id.2, sector, mixSupport (sectorRows s sector) cs_id.1⟩ : Row)))
      = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    have hxs : x.sector = sector := by
      obtain ⟨p, _, hp⟩ := List.mem_map.mp hx
      rw [← hp]
    have hopp : ¬sector = oppositeSector sector := fun h => oppositeSector_ne sector h.symm
    simp [hxs, hopp]
  rw [hnil, List.append_nil]
  refine List.filter_congr (fun x _ => ?_)
  by_cases hx : x.sector = sector
  · rw [hx]
    by_cases hopp : sector = oppositeSector sector
    · exact absurd hopp (fun h => oppositeSector_ne sector h.symm)
    · simp [hopp]
  · simp [hx]

/-- The unit coefficient rows, as a list: entry `i` of the componentwise
    combination selected by row `i` of `drows` is `1`, every other entry is
    `0`. -/
theorem rebaseMatrix_unit_rows (matrix : List (List Nat)) (m : Nat)
    (hok : rebaseMatrix_ok matrix m) :
    ∃ drows : List (List Nat), drows.length = m ∧
      (∀ d ∈ drows, d.length = m ∧ (∀ c ∈ d, c = 0 ∨ c = 1)) ∧
      (∀ i, i < m → combineMasks (matrix.map matrixRowMask) (drows.getD i []) = 2 ^ i) := by
  have htot : ∀ i : Nat, ∃ d : List Nat, i < m →
      (d.length = m ∧ (∀ c ∈ d, c = 0 ∨ c = 1) ∧
        combineMasks (matrix.map matrixRowMask) d = 2 ^ i) := by
    intro i
    by_cases hi : i < m
    · have h := rebaseMatrix_unit_coeff matrix m hok i hi
      exact ⟨Classical.choose h, fun _ => Classical.choose_spec h⟩
    · exact ⟨[], fun h => absurd h hi⟩
  let d : Nat → List Nat := fun i => Classical.choose (htot i)
  refine ⟨(List.range m).map d, ?_, ?_, ?_⟩
  · rw [List.length_map, List.length_range]
  · intro dd hdd
    obtain ⟨i, hi, hie⟩ := List.mem_map.mp hdd
    subst hie
    have him : i < m := List.mem_range.mp hi
    have hch := Classical.choose_spec (htot i) him
    exact ⟨hch.1, hch.2.1⟩
  · intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    show combineMasks (matrix.map matrixRowMask) (d i) = 2 ^ i
    exact (Classical.choose_spec (htot i) hi).2.2

/-- Rank depends on the displayed rows only through the sector filter. -/
theorem sectorRank_congr_rows (Q : List Nat) {rows₁ rows₂ : List Row} (sec : Sector)
    (h : rows₁.filter (fun r => r.sector = sec) = rows₂.filter (fun r => r.sector = sec)) :
    sectorRank Q rows₁ sec = sectorRank Q rows₂ sec := by
  rw [sectorRank, sectorRank, h]

/-- Rebase preserves the displayed-sector rank, from `rebaseMatrix_ok`
    alone — no hypothesis on the source state. -/
theorem sectorRank_rebaseState (s : CodeState) (sector : Sector) (M : List (List Nat))
    (hok : rebaseMatrix_ok M (sectorRows s sector).length) :
    sectorRank s.Q (rebaseState s sector M).rows sector
      = sectorRank s.Q s.rows sector := by
  have hmatlen : M.length = (sectorRows s sector).length := hok.1
  have h01 : ∀ row ∈ M, ∀ c ∈ row, c = 0 ∨ c = 1 := fun row hr => (hok.2.1 row hr).2
  have hrowlen : ∀ row ∈ M, row.length = (sectorRows s sector).length :=
    fun row hr => (hok.2.1 row hr).1
  have hmlen : ((sectorRows s sector).map (rowBitmask s.Q)).length
      = (sectorRows s sector).length := List.length_map _
  -- the rebased sector's masks are the old masks combined by the matrix rows
  have hstep1 : ((M.zip (mintFresh s.used M.length)).map
        (fun cs_id => (⟨cs_id.2, sector, mixSupport (sectorRows s sector) cs_id.1⟩ : Row))).map
      (rowBitmask s.Q)
      = (M.zip (mintFresh s.used M.length)).map
          (fun p : List Nat × Nat =>
            combineMasks ((sectorRows s sector).map (rowBitmask s.Q)) p.1) := by
    rw [List.map_map]
    refine List.map_congr_left ?_
    intro p hp
    obtain ⟨cs, id⟩ := p
    exact rowBitmask_mixSupport s.Q (sectorRows s sector) cs id sector
  have hstep2 : (M.zip (mintFresh s.used M.length)).map
        (fun p : List Nat × Nat =>
          combineMasks ((sectorRows s sector).map (rowBitmask s.Q)) p.1)
      = M.map (combineMasks ((sectorRows s sector).map (rowBitmask s.Q))) := by
    rw [map_zip_left (fun cs =>
      combineMasks ((sectorRows s sector).map (rowBitmask s.Q)) cs)
      M (mintFresh s.used M.length) (by rw [mintFresh_length])]
  have hnew : ((M.zip (mintFresh s.used M.length)).map
        (fun cs_id => (⟨cs_id.2, sector, mixSupport (sectorRows s sector) cs_id.1⟩ : Row))).map
      (rowBitmask s.Q)
      = M.map (combineMasks ((sectorRows s sector).map (rowBitmask s.Q))) :=
    hstep1.trans hstep2
  -- span inclusions, both ways
  have hspanNewOld : ∀ v,
      inSpanMasks (M.map (combineMasks ((sectorRows s sector).map (rowBitmask s.Q)))) v →
      inSpanMasks ((sectorRows s sector).map (rowBitmask s.Q)) v := by
    intro v hv
    refine inSpanMasks_trans (fun g hg => ?_) hv
    obtain ⟨row, hrow, hge⟩ := List.mem_map.mp hg
    subst hge
    exact ⟨row, (hrowlen row hrow).trans hmlen.symm, h01 row hrow, rfl⟩
  have hspanOldNew : ∀ v,
      inSpanMasks ((sectorRows s sector).map (rowBitmask s.Q)) v →
      inSpanMasks (M.map (combineMasks ((sectorRows s sector).map (rowBitmask s.Q)))) v := by
    intro v hv
    obtain ⟨cs, hcslen, hcs01, hcsval⟩ := hv
    obtain ⟨drows, hdrl, hdrmem, hdri⟩ :=
      rebaseMatrix_unit_rows M (sectorRows s sector).length hok
    have hd01 : ∀ d ∈ drows, ∀ c ∈ d, c = 0 ∨ c = 1 := fun d hd => (hdrmem d hd).2
    have hdlen : ∀ d ∈ drows, d.length = (sectorRows s sector).length :=
      fun d hd => (hdrmem d hd).1
    have hpoint : ∀ i, i < (sectorRows s sector).length →
        combineMasks (M.map (combineMasks ((sectorRows s sector).map (rowBitmask s.Q))))
            (drows.getD i [])
          = ((sectorRows s sector).map (rowBitmask s.Q)).getD i 0 := by
      intro i hi
      rw [combineMasks_combineCoeffRowsM _ _ M h01 hrowlen hmlen.symm]
      have hE := combineCoeffRowsM_testBit_matrixRowMask (sectorRows s sector).length M
        h01 hrowlen (drows.getD i [])
      have hi' : i < ((sectorRows s sector).map (rowBitmask s.Q)).length := by
        rw [hmlen]; exact hi
      have heq : combineCoeffRowsM (sectorRows s sector).length M (drows.getD i [])
          = unitRow ((sectorRows s sector).map (rowBitmask s.Q)).length i := by
        refine List.ext_getElem ?_ ?_
        · rw [combineCoeffRowsM_length _ M hrowlen, unitRow_length, hmlen]
        · intro j hj
          have hj' : j < ((sectorRows s sector).map (rowBitmask s.Q)).length := by
            have htmp := hj
            rw [combineCoeffRowsM_length _ M hrowlen, ← hmlen] at htmp
            exact htmp
          simp only [List.getElem_eq_getD (fallback := 0)]
          rw [unitRow_getElem _ i j hi' hj']
          rw [hE j, hdri i hi, Nat.testBit_two_pow]
          intro _
          by_cases hij : j = i
          · simp [hij]
          · have hij' : ¬i = j := fun h => hij h.symm
            simp [hij, hij']
      rw [heq, combineMasks_unitRow _ i hi']
    have hmapd : drows.map
        (combineMasks (M.map (combineMasks ((sectorRows s sector).map (rowBitmask s.Q)))))
      = (sectorRows s sector).map (rowBitmask s.Q) := by
      refine List.ext_getElem ?_ ?_
      · rw [List.length_map, hdrl, hmlen]
      · intro j hj
        rw [List.length_map] at hj
        have hj' : j < ((sectorRows s sector).map (rowBitmask s.Q)).length := by
          have htmp := hj
          rw [hdrl, ← hmlen] at htmp
          exact htmp
        rw [List.getElem_map]
        simp only [List.getElem_eq_getD (fallback := []),
          List.getElem_eq_getD (fallback := 0)]
        intro _
        exact hpoint j (by rw [hdrl] at hj; exact hj)
    have hdcomblen : (combineCoeffRowsM (sectorRows s sector).length drows cs).length
        = (M.map (combineMasks ((sectorRows s sector).map (rowBitmask s.Q)))).length := by
      rw [combineCoeffRowsM_length _ drows hdlen cs, List.length_map, ← hmatlen]
    refine ⟨combineCoeffRowsM (sectorRows s sector).length drows cs, hdcomblen,
      combineCoeffRowsM_01 _ drows hd01 cs, ?_⟩
    calc combineMasks (M.map (combineMasks ((sectorRows s sector).map (rowBitmask s.Q))))
          (combineCoeffRowsM (sectorRows s sector).length drows cs)
        = combineMasks (drows.map
            (combineMasks (M.map (combineMasks
              ((sectorRows s sector).map (rowBitmask s.Q))))))
          cs := by
            rw [← combineMasks_combineCoeffRowsM
              (M.map (combineMasks ((sectorRows s sector).map (rowBitmask s.Q))))
              (sectorRows s sector).length drows hd01 hdlen
              ((combineCoeffRowsM_length _ drows hdlen cs).symm.trans hdcomblen) cs]
      _ = combineMasks ((sectorRows s sector).map (rowBitmask s.Q)) cs := by rw [hmapd]
      _ = v := hcsval
  have hspanEq : ∀ v,
      inSpanMasks ((sectorRows s sector).map (rowBitmask s.Q)) v ↔
        inSpanMasks (M.map (combineMasks ((sectorRows s sector).map (rowBitmask s.Q)))) v :=
    fun v => ⟨hspanOldNew v, hspanNewOld v⟩
  have hrankEq : rankBitmasks ((sectorRows s sector).map (rowBitmask s.Q))
      = rankBitmasks (M.map (combineMasks ((sectorRows s sector).map (rowBitmask s.Q)))) :=
    rankBitmasks_eq_of_span_eq hspanEq
  show rankBitmasks
      ((sectorRows (rebaseState s sector M) sector).map (rowBitmask s.Q))
    = rankBitmasks ((sectorRows s sector).map (rowBitmask s.Q))
  rw [sectorRows_rebaseState s sector M, hnew, hrankEq]

/-- `stateK` is preserved by a rebase. -/
theorem stateK_rebaseState (s : CodeState) (sector : Sector) (M : List (List Nat))
    (hok : rebaseMatrix_ok M (sectorRows s sector).length) :
    stateK (rebaseState s sector M) = stateK s := by
  have hQ : (rebaseState s sector M).Q = s.Q := rfl
  show s.Q.length
      - sectorRank (rebaseState s sector M).Q (rebaseState s sector M).rows Sector.X
      - sectorRank (rebaseState s sector M).Q (rebaseState s sector M).rows Sector.Z
    = s.Q.length - sectorRank s.Q s.rows Sector.X - sectorRank s.Q s.rows Sector.Z
  rw [hQ]
  cases sector with
  | X =>
      rw [sectorRank_rebaseState s Sector.X M hok,
        sectorRank_congr_rows s.Q (sec := Sector.Z)
          (sectorRows_rebaseState_other s Sector.X M)]
  | Z =>
      rw [sectorRank_congr_rows s.Q (sec := Sector.X)
          (sectorRows_rebaseState_other s Sector.Z M),
        sectorRank_rebaseState s Sector.Z M hok]

/-- The rank statement is instantiable from the `Eval.rebase` premises as
    they stand: the rule asks `EncodingWellFormed` of the output only. -/
theorem sectorRank_rebaseState_of_eval {sector : Sector} {matrix : List (List Nat)}
    {s s' : CodeState} (h : Eval (Command.rebase sector matrix) s s') :
    sectorRank s'.Q s'.rows sector = sectorRank s.Q s.rows sector := by
  cases h with
  | rebase _ hok hseq _ =>
      rw [hseq]
      exact sectorRank_rebaseState s sector matrix hok

/-- A concrete integration check: `rebaseState` applies the two-row shear
    through `mixSupport`, and the displayed-sector rank is preserved. -/
def rebaseShearExample : CodeState :=
  { Q := [0, 1, 2]
  , rows := [⟨1, Sector.X, [0, 1]⟩, ⟨2, Sector.X, [1, 2]⟩]
  , used := [1, 2] }

theorem sectorRank_rebaseState_shear_example :
    sectorRank
      (rebaseState rebaseShearExample Sector.X [[1, 1], [0, 1]]).Q
      (rebaseState rebaseShearExample Sector.X [[1, 1], [0, 1]]).rows
      Sector.X
      = sectorRank rebaseShearExample.Q rebaseShearExample.rows Sector.X := by
  decide

end CodeCalculus
