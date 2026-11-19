import CodeCalculus.GraftWellFormedness
import CodeCalculus.ExactDistance
import CodeCalculus.Refinement

/-!
# The separating deletion as a derived command (issue #546)

`design/E_SPLIT_PROPOSAL.md` states a candidate `E-SPLIT` as a derived
command: delete a list of displayed rows (the cut rows) so that every row
left lies on one side of a partition of the qubits. This module carries the
part of that proposal that is a consequence of the kernel. Nothing here
admits `E-SPLIT`: the module adds no constructor to `Command` or
`StateExpr`, and the proposal is not normative.

* `splitCommand R` is the `C-SEQUENCE` of `C-DELETE-CHECK` over the
  identifiers `R`, the mirror of `glueCommand` (`Gate6Soundness.lean`).
* `eval_splitCommand_iff` gives its applicability on a well-formed state:
  it evaluates exactly when `R` has no repeated identifier and every
  identifier in `R` is displayed. Independence is not a premise, because I2
  supplies it.
* `stateK_of_eval_split` is `k' = k + |R|`, and `exactDistanceExt_split_le`
  is the non-increase of each sector distance.
* `separated_deleteAll` is the postcondition: when `R` contains the
  identifier of every row that meets both sides, the child is separated.
* `deleteAll_glueState_rows`, `deleteAll_glueState_Q`, and
  `deleteAll_glueState_used` are the partial inverse law against `E-GLUE`:
  deleting the minted seam rows of a glued state gives the rows and qubits
  of the direct sum, with `used` grown by the retired seam identifiers.
-/

namespace CodeCalculus

/-- The cut rows of a split, deleted one at a time. -/
def splitCommand : List Nat → Command
  | [] => Command.skip
  | r :: rest => Command.seq (Command.delete r) (splitCommand rest)

/-- The state update of `splitCommand`: `deleteState` over the list. -/
def deleteAll (s : CodeState) : List Nat → CodeState
  | [] => s
  | r :: rest => deleteAll (deleteState s r) rest

theorem deleteAll_Q (R : List Nat) : ∀ s : CodeState, (deleteAll s R).Q = s.Q := by
  induction R with
  | nil => intro s; rfl
  | cons r rest ih => intro s; exact ih (deleteState s r)

theorem deleteAll_used (R : List Nat) : ∀ s : CodeState, (deleteAll s R).used = s.used := by
  induction R with
  | nil => intro s; rfl
  | cons r rest ih => intro s; exact ih (deleteState s r)

/-- A row is displayed after the deletions exactly when it was displayed
    before and its identifier is not among those deleted. -/
theorem mem_deleteAll_rows (R : List Nat) :
    ∀ (s : CodeState) (row : Row),
      row ∈ (deleteAll s R).rows ↔ row ∈ s.rows ∧ row.id ∉ R := by
  induction R with
  | nil =>
      intro s row
      exact ⟨fun h => ⟨h, fun hmem => nomatch hmem⟩, fun h => h.1⟩
  | cons r rest ih =>
      intro s row
      show row ∈ (deleteAll (deleteState s r) rest).rows ↔ _
      rw [ih (deleteState s r) row]
      show (row ∈ s.rows.filter (fun row => row.id ≠ r) ∧ row.id ∉ rest) ↔ _
      rw [List.mem_filter]
      constructor
      · rintro ⟨⟨hmem, hne⟩, hrest⟩
        refine ⟨hmem, fun hin => ?_⟩
        rcases List.mem_cons.mp hin with h | h
        · exact (of_decide_eq_true hne) h
        · exact hrest h
      · rintro ⟨hmem, hnot⟩
        exact ⟨⟨hmem, decide_eq_true (fun h => hnot (h ▸ List.mem_cons_self))⟩,
          fun h => hnot (List.mem_cons_of_mem _ h)⟩

/-- The deletions keep the rows in their order. -/
theorem deleteAll_rows_sublist (R : List Nat) :
    ∀ s : CodeState, (deleteAll s R).rows.Sublist s.rows := by
  induction R with
  | nil => intro s; exact List.Sublist.refl _
  | cons r rest ih =>
      intro s
      exact (ih (deleteState s r)).trans List.filter_sublist

/-- An evaluation of `splitCommand` produces `deleteAll`. -/
theorem eval_splitCommand_eq (R : List Nat) :
    ∀ {s t : CodeState}, Eval (splitCommand R) s t → t = deleteAll s R := by
  induction R with
  | nil => intro s t h; exact eval_skip_eq h
  | cons r rest ih =>
      intro s t h
      cases h with
      | seq h1 h2 =>
          have h1' := eval_delete_eq h1
          subst h1'
          exact ih h2

/-- Well-formedness is preserved (§4.7, the deletion instance, iterated). -/
theorem wf_of_eval_split {R : List Nat} {s t : CodeState}
    (h : Eval (splitCommand R) s t) (hwf : EncodingWellFormed s) :
    EncodingWellFormed t :=
  wf_of_eval_all h hwf

/-- `k' = k + |R|`: each deleted row raises the logical dimension by one. -/
theorem stateK_of_eval_split (R : List Nat) :
    ∀ {s t : CodeState}, EncodingWellFormed s → Eval (splitCommand R) s t →
      stateK t = stateK s + R.length := by
  induction R with
  | nil =>
      intro s t _ h
      rw [eval_skip_eq h]
      rfl
  | cons r rest ih =>
      intro s t hwf h
      cases h with
      | seq h1 h2 =>
          have hk1 := stateK_delete_of_eval h1 hwf (ranksFit_of_wf _ hwf)
          have hk2 := ih (wf_of_eval_all h1 hwf) h2
          rw [hk2, hk1, List.length_cons]
          omega

/-- No sector distance rises (§4.5, iterated). -/
theorem exactDistanceExt_split_le (R : List Nat) (σ : Sector) :
    ∀ {s t : CodeState}, Eval (splitCommand R) s t →
      exactDistanceExt σ t ≤ exactDistanceExt σ s := by
  induction R with
  | nil =>
      intro s t h
      rw [eval_skip_eq h]
      exact ExtNat.le_refl _
  | cons r rest ih =>
      intro s t h
      cases h with
      | seq h1 h2 =>
          exact ExtNat.le_trans (ih h2) (exactDistanceExt_delete_le h1 σ)

/-- Applicability, one direction: on a well-formed state the command
    evaluates when the identifiers are distinct and displayed. I2 supplies
    the independence premise of each `C-DELETE-CHECK`. -/
theorem eval_splitCommand_of_displayed (R : List Nat) :
    ∀ {s : CodeState}, EncodingWellFormed s → R.Nodup →
      (∀ r ∈ R, DisplayedGenerator r s) → Eval (splitCommand R) s (deleteAll s R) := by
  induction R with
  | nil => intro s _ _ _; exact Eval.skip s
  | cons r rest ih =>
      intro s hwf hnd hdisp
      have hr : DisplayedGenerator r s := hdisp r List.mem_cons_self
      obtain ⟨row, hmem, hid⟩ := hr
      have hind : IndependentGenerator r s := hid ▸ hwf.2.2.2.2.2.2.2 row hmem
      have h1 : Eval (Command.delete r) s (deleteState s r) :=
        Eval.delete ⟨row, hmem, hid⟩ hind rfl
      have hnd' := List.nodup_cons.mp hnd
      refine Eval.seq h1 (ih (wf_deleteState s r hwf) hnd'.2 ?_)
      intro r' hr'
      obtain ⟨row', hmem', hid'⟩ := hdisp r' (List.mem_cons_of_mem _ hr')
      refine ⟨row', ?_, hid'⟩
      show row' ∈ s.rows.filter (fun row => row.id ≠ r)
      exact List.mem_filter.mpr ⟨hmem', decide_eq_true (fun h =>
        hnd'.1 (by rw [← h, hid']; exact hr'))⟩

/-- Applicability, the other direction: an evaluation forces distinct
    displayed identifiers. -/
theorem displayed_of_eval_split (R : List Nat) :
    ∀ {s t : CodeState}, Eval (splitCommand R) s t →
      R.Nodup ∧ ∀ r ∈ R, DisplayedGenerator r s := by
  induction R with
  | nil =>
      intro s t _
      exact ⟨List.nodup_nil, fun r hr => nomatch hr⟩
  | cons r rest ih =>
      intro s t h
      cases h with
      | seq h1 h2 =>
          have h1eq := eval_delete_eq h1
          subst h1eq
          obtain ⟨hnd, hdisp⟩ := ih h2
          have hr : DisplayedGenerator r s := by
            cases h1 with
            | delete hd _ _ => exact hd
          refine ⟨List.nodup_cons.mpr ⟨fun hin => ?_, hnd⟩, ?_⟩
          · obtain ⟨row, hmem, hid⟩ := hdisp r hin
            have hmem' : row ∈ s.rows.filter (fun row => row.id ≠ r) := hmem
            exact (of_decide_eq_true (List.mem_filter.mp hmem').2) hid
          · intro r' hr'
            rcases List.mem_cons.mp hr' with h | h
            · exact h ▸ hr
            · obtain ⟨row, hmem, hid⟩ := hdisp r' h
              have hmem' : row ∈ s.rows.filter (fun row => row.id ≠ r) := hmem
              exact ⟨row, (List.mem_filter.mp hmem').1, hid⟩

/-- Applicability of the derived command on a well-formed state. -/
theorem eval_splitCommand_iff (R : List Nat) {s : CodeState} (hwf : EncodingWellFormed s) :
    (∃ t, Eval (splitCommand R) s t) ↔ R.Nodup ∧ ∀ r ∈ R, DisplayedGenerator r s :=
  ⟨fun ⟨_, h⟩ => displayed_of_eval_split R h,
   fun ⟨hnd, hdisp⟩ => ⟨_, eval_splitCommand_of_displayed R hwf hnd hdisp⟩⟩

/-! ## The separation postcondition -/

/-- Every displayed row lies inside `QA` or misses it: no row meets both
    sides of the partition of the qubits into `QA` and the rest. -/
def Separated (QA : List Nat) (s : CodeState) : Prop :=
  ∀ row ∈ s.rows, (∀ q ∈ row.support, q ∈ QA) ∨ (∀ q ∈ row.support, q ∉ QA)

/-- When the deleted identifiers include every row that meets both sides,
    the child is separated. -/
theorem separated_deleteAll (QA R : List Nat) (s : CodeState)
    (hcut : ∀ row ∈ s.rows,
      (∀ q ∈ row.support, q ∈ QA) ∨ (∀ q ∈ row.support, q ∉ QA) ∨ row.id ∈ R) :
    Separated QA (deleteAll s R) := by
  intro row hrow
  obtain ⟨hmem, hnot⟩ := (mem_deleteAll_rows R s row).mp hrow
  rcases hcut row hmem with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hnot

/-- A direct sum of well-formed states on disjoint qubits is separated at
    the first summand's qubits. -/
theorem separated_directSumState (a b : CodeState)
    (ha : EncodingWellFormed a) (hb : EncodingWellFormed b)
    (hdisj : ∀ q ∈ b.Q, q ∉ a.Q) :
    Separated a.Q (directSumState a b) := by
  intro row hrow
  rcases List.mem_append.mp hrow with h | h
  · left
    intro q hq
    have hall := List.all_eq_true.mp ha.2.2.2.1 row h
    exact List.contains_iff_mem.mp (List.all_eq_true.mp hall q hq)
  · right
    intro q hq
    have hall := List.all_eq_true.mp hb.2.2.2.1 row h
    exact hdisj q (List.contains_iff_mem.mp (List.all_eq_true.mp hall q hq))

/-! ## The partial inverse law against `E-GLUE` -/

theorem deleteAll_glueState_Q (a b : CodeState) (seams : List (Sector × List Nat)) :
    (deleteAll (glueState a b seams) (mintFresh (a.used ++ b.used) seams.length)).Q =
      (directSumState a b).Q := by
  rw [deleteAll_Q]
  rfl

/-- `used` grows by the retired seam identifiers and is otherwise that of
    the direct sum. -/
theorem deleteAll_glueState_used (a b : CodeState) (seams : List (Sector × List Nat)) :
    (deleteAll (glueState a b seams) (mintFresh (a.used ++ b.used) seams.length)).used =
      (directSumState a b).used ++ mintFresh (a.used ++ b.used) seams.length := by
  rw [deleteAll_used]
  rfl

/-- A list is unchanged by a filter that keeps each of its elements. -/
theorem filter_eq_self_of_all {α : Type} (p : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, p x = true) → l.filter p = l
  | [], _ => rfl
  | x :: xs, h => by
      rw [List.filter_cons_of_pos (h x List.mem_cons_self),
        filter_eq_self_of_all p xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- A filter that rejects every element of a list returns the empty list. -/
theorem filter_eq_nil_of_none {α : Type} (p : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, p x = false) → l.filter p = []
  | [], _ => rfl
  | x :: xs, h => by
      rw [List.filter_cons_of_neg (by rw [h x List.mem_cons_self]; exact Bool.false_ne_true),
        filter_eq_nil_of_none p xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- The rows after the deletions, as one filter. -/
theorem deleteAll_rows (R : List Nat) :
    ∀ s : CodeState, (deleteAll s R).rows = s.rows.filter (fun row => !R.contains row.id) := by
  induction R with
  | nil =>
      intro s
      exact (filter_eq_self_of_all _ s.rows (fun _ _ => rfl)).symm
  | cons r rest ih =>
      intro s
      show (deleteAll (deleteState s r) rest).rows = _
      rw [ih (deleteState s r)]
      show (s.rows.filter (fun row => row.id ≠ r)).filter _ = _
      rw [List.filter_filter]
      apply List.filter_congr
      intro row _
      cases hrest : rest.contains row.id with
      | true =>
          have : (r :: rest).contains row.id = true :=
            List.contains_iff_mem.mpr
              (List.mem_cons_of_mem _ (List.contains_iff_mem.mp hrest))
          rw [this]
          rfl
      | false =>
          rcases Decidable.em (row.id = r) with heq | hne
          · have hin : (r :: rest).contains row.id = true :=
              List.contains_iff_mem.mpr (heq ▸ List.mem_cons_self)
            rw [hin]
            show (true && decide (row.id ≠ r)) = false
            rw [decide_eq_false (fun h => h heq)]
            rfl
          · have hnot : (r :: rest).contains row.id = false := by
              cases hc : (r :: rest).contains row.id with
              | false => rfl
              | true =>
                  rcases List.mem_cons.mp (List.contains_iff_mem.mp hc) with h | h
                  · exact absurd h hne
                  · rw [List.contains_iff_mem.mpr h] at hrest
                    exact nomatch hrest
            rw [hnot]
            show (true && decide (row.id ≠ r)) = true
            rw [decide_eq_true hne]
            rfl

/-- Deleting the minted seam rows of a glued state leaves the rows of the
    direct sum, in their order. The hypotheses are the clause of
    well-formedness that puts every displayed identifier in `used`. -/
theorem deleteAll_glueState_rows (a b : CodeState) (seams : List (Sector × List Nat))
    (ha : ∀ row ∈ a.rows, row.id ∈ a.used) (hb : ∀ row ∈ b.rows, row.id ∈ b.used) :
    (deleteAll (glueState a b seams) (mintFresh (a.used ++ b.used) seams.length)).rows =
      (directSumState a b).rows := by
  rw [deleteAll_rows]
  show ((a.rows ++ b.rows) ++ ((seams.zip (mintFresh (a.used ++ b.used) seams.length)).map
      (fun (p : (Sector × List Nat) × Nat) =>
        ({ id := p.2, sector := p.1.1, support := p.1.2 } : Row)))).filter _ =
    a.rows ++ b.rows
  rw [List.filter_append]
  have hkeep : (a.rows ++ b.rows).filter
      (fun row => !(mintFresh (a.used ++ b.used) seams.length).contains row.id) =
      a.rows ++ b.rows := by
    apply filter_eq_self_of_all
    intro row hrow
    have hused : row.id ∈ a.used ++ b.used := by
      rcases List.mem_append.mp hrow with h | h
      · exact List.mem_append_left _ (ha row h)
      · exact List.mem_append_right _ (hb row h)
    cases hc : (mintFresh (a.used ++ b.used) seams.length).contains row.id with
    | false => rfl
    | true =>
        exact absurd hused
          (mintFresh_not_mem _ _ _ (List.contains_iff_mem.mp hc))
  have hdrop : ((seams.zip (mintFresh (a.used ++ b.used) seams.length)).map
      (fun (p : (Sector × List Nat) × Nat) =>
        ({ id := p.2, sector := p.1.1, support := p.1.2 } : Row))).filter
      (fun row => !(mintFresh (a.used ++ b.used) seams.length).contains row.id) = [] := by
    apply filter_eq_nil_of_none
    intro row hrow
    obtain ⟨⟨si, id⟩, hpair, hrow'⟩ := List.mem_map.mp hrow
    have hid : id ∈ mintFresh (a.used ++ b.used) seams.length := (List.of_mem_zip hpair).2
    have : (mintFresh (a.used ++ b.used) seams.length).contains row.id = true := by
      rw [← hrow']
      exact List.contains_iff_mem.mpr hid
    rw [this]
    rfl
  rw [hkeep, hdrop, List.append_nil]

end CodeCalculus
