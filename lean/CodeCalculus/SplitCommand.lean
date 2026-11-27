import CodeCalculus.GraftWellFormedness
import CodeCalculus.ExactDistance
import CodeCalculus.Refinement
import CodeCalculus.ExactPermute
import CodeCalculus.Gate6Exact

/-!
# `E-SPLIT`: separating deletion, factorization, exact decompositions, and conditional cell

Admitted on 2026-11-25 (`issue #546`, `spec/OPERATIONAL_SEMANTICS.md` §4.48,
`spec/JUDGMENT_LAYER.md` §2a–§2c, `spec/CLAIMS.md`).

* `splitCommand R` is the `C-SEQUENCE` of `C-DELETE-CHECK` over the
  identifiers `R`, the mirror of `glueCommand` (`Gate6Soundness.lean`).
* `eval_split_iff_eval_splitCommand` proves the factorization of the admitted
  command `Command.split QA R` into `splitCommand R` on every well-formed state.
* `eval_splitCommand_iff` gives the applicability of `splitCommand R`: it
  evaluates on a well-formed state exactly when `R` has no repeated identifier
  and every identifier in `R` is displayed. Independence is supplied by I2.
* `stateK_of_eval_split` / `stateK_of_eval_split_cmd` prove `k' = k + |R|`,
  and `exactDistanceExt_split_le` / `exactDistanceExt_split_cmd_le` prove
  non-increase of each sector distance.
* `separated_deleteAll` / `separated_of_eval_split` prove the separation
  postcondition `Separated QA t`.
* `deleteAll_glueState_rows`, `deleteAll_glueState_Q`, `deleteAll_glueState_used`,
  and `eval_split_glueState` prove the partial inverse law against `E-GLUE`.
* `exactDistanceExt_separated_eq_min` proves the block-minimum decomposition
  `d_σ(D) = min(d_σ(D|_A), d_σ(D|_B))` for any separated well-formed state `D`.
* `exactDistanceExt_split_eq_min_price` proves the exact price decomposition
  `d_σ(C') = min(d_σ(C), w_del,σ, w_exp,σ)` across the three classes of child
  logicals (parent logicals, promoted stabilizers, and exposed vectors).
* `splitLedger_unpriced_sound`, `splitLedger_priced_sound`, and
  `splitLedger_priced_monotone` prove soundness and precision monotonicity of
  the unpriced and `split_block_intervals`-priced `E-SPLIT` interval transformers.
-/

namespace CodeCalculus

/-- The cut rows of a split, deleted one at a time. -/
def splitCommand : List Nat → Command
  | [] => Command.skip
  | r :: rest => Command.seq (Command.delete r) (splitCommand rest)

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

/-- Well-formedness is preserved (§4.7, §4.48, iterated deletion). -/
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

/-! ## Factorization of `Command.split` into `splitCommand` (§4.48) -/

/-- Exact equivalence between the admitted `Command.split QA R` transition
    and the derived deletion sequence `splitCommand R` together with the
    partition typing and cut-coverage premises, on every well-formed state. -/
theorem eval_split_iff_eval_splitCommand (QA R : List Nat) {s t : CodeState}
    (hwf : EncodingWellFormed s) :
    Eval (Command.split QA R) s t ↔
      QA.Nodup ∧ (∀ q ∈ QA, q ∈ s.Q) ∧
      (∀ row ∈ s.rows,
        (∀ q ∈ row.support, q ∈ QA) ∨ (∀ q ∈ row.support, q ∉ QA) ∨ row.id ∈ R) ∧
      Eval (splitCommand R) s t := by
  constructor
  · intro h
    cases h with
    | split hQAnd hQA hRnd hRdisp hcut hs' =>
        subst hs'
        exact ⟨hQAnd, hQA, hcut, eval_splitCommand_of_displayed R hwf hRnd hRdisp⟩
  · rintro ⟨hQAnd, hQA, hcut, hcmd⟩
    obtain ⟨hRnd, hRdisp⟩ := displayed_of_eval_split R hcmd
    exact Eval.split hQAnd hQA hRnd hRdisp hcut (eval_splitCommand_eq R hcmd)

theorem stateK_of_eval_split_cmd {QA R : List Nat} {s t : CodeState}
    (hwf : EncodingWellFormed s) (h : Eval (Command.split QA R) s t) :
    stateK t = stateK s + R.length :=
  stateK_of_eval_split R hwf ((eval_split_iff_eval_splitCommand QA R hwf).mp h).2.2.2

theorem exactDistanceExt_split_cmd_le {QA R : List Nat} {s t : CodeState} (σ : Sector)
    (hwf : EncodingWellFormed s) (h : Eval (Command.split QA R) s t) :
    exactDistanceExt σ t ≤ exactDistanceExt σ s :=
  exactDistanceExt_split_le R σ ((eval_split_iff_eval_splitCommand QA R hwf).mp h).2.2.2

/-! ## The separation postcondition -/

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

/-- Every `Command.split QA R` evaluation produces a `QA`-separated child state. -/
theorem separated_of_eval_split {QA R : List Nat} {s t : CodeState}
    (h : Eval (Command.split QA R) s t) : Separated QA t := by
  cases h with
  | split _ _ _ _ hcut hs' =>
      subst hs'
      exact separated_deleteAll QA R s hcut

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

private theorem mem_zip_snd_of_eq_length {α β : Type} :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
      ∀ y ∈ ys, ∃ x, (x, y) ∈ xs.zip ys
  | [], [], _, _, hy => nomatch hy
  | _ :: _, [], h, _, _ => by cases h
  | [], _ :: _, h, _, _ => by cases h
  | x :: xs, y :: ys, h, z, hz => by
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact ⟨x, List.mem_cons_self⟩
      · obtain ⟨x', hx'⟩ := mem_zip_snd_of_eq_length xs ys (Nat.succ.inj h) z hz'
        exact ⟨x', List.mem_cons_of_mem _ hx'⟩

/-- `Command.split` applies to any glued state on well-formed disjoint factors
    when given `QA = a.Q` and the minted seam identifiers `R = ids`, and
    recovers the direct sum's qubits and displayed rows (with `used` grown by
    the retired seam identifiers). -/
theorem eval_split_glueState {a b : CodeState} {seams : List (Sector × List Nat)}
    (ha : EncodingWellFormed a) (hb : EncodingWellFormed b)
    (hQ : DisjointList a.Q b.Q) :
    let ids := mintFresh (a.used ++ b.used) seams.length
    Eval (Command.split a.Q ids) (glueState a b seams) (deleteAll (glueState a b seams) ids) := by
  intro ids
  apply Eval.split
  · exact ha.1
  · intro q hq
    exact List.mem_append_left _ hq
  · exact mintFresh_nodup (a.used ++ b.used) seams.length
  · intro r hr
    have hlen : seams.length = ids.length := (mintFresh_length _ _).symm
    obtain ⟨si, hpair⟩ := mem_zip_snd_of_eq_length seams ids hlen r hr
    refine ⟨⟨r, si.1, si.2⟩, ?_, rfl⟩
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨(si, r), hpair, rfl⟩
  · intro row hrow
    rcases List.mem_append.mp hrow with hfactors | hseams
    · rcases List.mem_append.mp hfactors with hA | hB
      · left
        intro q hq
        exact List.contains_iff_mem.mp
          (List.all_eq_true.mp (List.all_eq_true.mp ha.2.2.2.1 row hA) q hq)
      · right; left
        intro q hq hqA
        exact hQ q hqA
          (List.contains_iff_mem.mp
            (List.all_eq_true.mp (List.all_eq_true.mp hb.2.2.2.1 row hB) q hq))
    · right; right
      obtain ⟨⟨si, id⟩, hpair, hrow'⟩ := List.mem_map.mp hseams
      rw [← hrow']
      exact (List.of_mem_zip hpair).2
  · rfl

/-! ## Block-minimum decomposition on a separated state (§4.48) -/

/-- Restriction of a state to the qubits in `QA` and the rows supported
    entirely inside `QA`. -/
def restrictBlock (s : CodeState) (QA : List Nat) : CodeState :=
  { Q := s.Q.filter (fun q => QA.contains q)
  , rows := s.rows.filter (fun r => r.support.all (fun q => QA.contains q))
  , used := s.used }

/-- Restriction of a state to the complement qubits `Q \ QA` and the rows
    not supported entirely inside `QA` (on a `QA`-separated state, the rows
    supported entirely inside `Q \ QA`). -/
def restrictComplement (s : CodeState) (QA : List Nat) : CodeState :=
  { Q := s.Q.filter (fun q => !QA.contains q)
  , rows := s.rows.filter (fun r => !r.support.all (fun q => QA.contains q))
  , used := s.used }

private theorem perm_append_cons {α : Type} (a : α) :
    ∀ (l1 l2 : List α), (l1 ++ a :: l2).Perm (a :: (l1 ++ l2))
  | [], _ => List.Perm.refl _
  | x :: l1, l2 =>
      (List.Perm.cons x (perm_append_cons a l1 l2)).trans (List.Perm.swap a x _)

private theorem perm_filter_append_filter_not {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (xs.filter p ++ xs.filter (fun x => !p x)).Perm xs
  | [] => List.Perm.nil
  | x :: xs => by
      cases hx : p x with
      | true =>
          simp only [List.filter_cons, hx, ↓reduceIte, Bool.not_true, Bool.false_eq_true,
            List.cons_append]
          exact List.Perm.cons x (perm_filter_append_filter_not p xs)
      | false =>
          simp only [List.filter_cons, hx, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
          exact (perm_append_cons x _ _).trans
            (List.Perm.cons x (perm_filter_append_filter_not p xs))

private theorem extNat_le_antisymm {a b : ExtNat} (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  cases a with
  | finite m =>
      cases b with
      | finite n => exact congrArg ExtNat.finite (Nat.le_antisymm h1 h2)
      | inf => exact False.elim h2
  | inf =>
      cases b with
      | finite _ => exact False.elim h1
      | inf => rfl

private theorem extNat_ofOption_inj {a b : Option Nat}
    (h : ExtNat.ofOption a = ExtNat.ofOption b) : a = b := by
  cases a <;> cases b <;> cases h <;> rfl

/-- Permuting the displayed row list on a fixed namespace preserves the exact
    sector distance. -/
theorem exactDistance?_rows_perm {s t : CodeState} (hQ : t.Q = s.Q)
    (hperm : t.rows.Perm s.rows) (σ : Sector) :
    exactDistance? σ t = exactDistance? σ s := by
  have hspan_sub : ∀ τ, SpanLE s.Q (sectorRows t τ) (sectorRows s τ) := by
    intro τ
    apply spanLE_of_forall_mem
    intro r hr
    exact inSpanRows_of_mem s.Q ((hperm.filter _).mem_iff.mp hr)
  have hspan_sup : ∀ τ, SpanLE s.Q (sectorRows s τ) (sectorRows t τ) := by
    intro τ
    apply spanLE_of_forall_mem
    intro r hr
    exact inSpanRows_of_mem s.Q ((hperm.filter _).mem_iff.mpr hr)
  have h1 : exactDistanceExt σ t ≤ exactDistanceExt σ s :=
    exactDistanceExt_le_of_spanLE s t σ hQ (hspan_sub σ) (hspan_sub (oppositeSector σ))
  have h2 : exactDistanceExt σ s ≤ exactDistanceExt σ t :=
    exactDistanceExt_le_of_spanLE t s σ hQ.symm (by rw [hQ]; exact hspan_sup σ)
      (by rw [hQ]; exact hspan_sup (oppositeSector σ))
  exact extNat_ofOption_inj (extNat_le_antisymm h1 h2)

/-- Direct-sum context for the two block restrictions of a separated
    well-formed state. -/
theorem directSumCtx_restrict {s : CodeState} {QA : List Nat}
    (hwf : EncodingWellFormed s) (hsep : Separated QA s) :
    DirectSumCtx (restrictBlock s QA) (restrictComplement s QA) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hqA hqB
    have h1 := (List.mem_filter.mp hqA).2
    have h2 := (List.mem_filter.mp hqB).2
    rw [h1] at h2
    cases h2
  · intro row hrow q hq
    have hf := List.mem_filter.mp hrow
    have hqQ : q ∈ s.Q :=
      List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp hwf.2.2.2.1 row hf.1) q hq)
    have hqA : QA.contains q = true := List.all_eq_true.mp hf.2 q hq
    exact List.mem_filter.mpr ⟨hqQ, hqA⟩
  · intro row hrow q hq
    have hf := List.mem_filter.mp hrow
    have hqQ : q ∈ s.Q :=
      List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp hwf.2.2.2.1 row hf.1) q hq)
    have hnotAll : row.support.all (fun q' => QA.contains q') = false := by
      cases hall : row.support.all (fun q' => QA.contains q') with
      | false => rfl
      | true => rw [hall] at hf; cases hf.2
    rcases hsep row hf.1 with hIn | hOut
    · exfalso
      have hall : row.support.all (fun q' => QA.contains q') = true :=
        List.all_eq_true.mpr (fun q' hq' => List.contains_iff_mem.mpr (hIn q' hq'))
      rw [hall] at hnotAll
      cases hnotAll
    · have hqNotA : QA.contains q = false := by
        cases hc : QA.contains q with
        | false => rfl
        | true => exact absurd (List.contains_iff_mem.mp hc) (hOut q hq)
      exact List.mem_filter.mpr ⟨hqQ, by show (!QA.contains q) = true; rw [hqNotA]; rfl⟩

/-- Block-minimum decomposition in `Option Nat`: on any `QA`-separated
    well-formed state, each exact sector distance is the minimum of the two
    block restrictions' exact sector distances (§4.48). -/
theorem exactDistance?_separated_eq_min {s : CodeState} {QA : List Nat}
    (hwf : EncodingWellFormed s) (hsep : Separated QA s) (σ : Sector) :
    exactDistance? σ s =
      minOpt (exactDistance? σ (restrictBlock s QA))
             (exactDistance? σ (restrictComplement s QA)) := by
  let A := restrictBlock s QA
  let B := restrictComplement s QA
  let D := directSumState A B
  let sMid : CodeState := { Q := s.Q, rows := D.rows, used := s.used }
  have hpermQ : D.Q.Perm s.Q := perm_filter_append_filter_not (fun q => QA.contains q) s.Q
  have hpermR : D.rows.Perm s.rows :=
    perm_filter_append_filter_not (fun r : Row => r.support.all (fun q => QA.contains q)) s.rows
  have h1 : exactDistance? σ D = exactDistance? σ sMid :=
    exactDistance?_perm (s := sMid) (t := D) rfl hpermQ hwf.1 σ
  have h2 : exactDistance? σ sMid = exactDistance? σ s :=
    exactDistance?_rows_perm (s := s) (t := sMid) rfl hpermR σ
  have h3 : exactDistance? σ D = minOpt (exactDistance? σ A) (exactDistance? σ B) :=
    exactDistance?_directSum (directSumCtx_restrict hwf hsep) σ
  rw [← h2, ← h1, h3]

/-- Block-minimum decomposition in `ExtNat` (`ℕ ∪ {+∞}`, §4.48):
    `d_σ(D) = min(d_σ(D|_A), d_σ(D|_B))` for any `QA`-separated well-formed state. -/
theorem exactDistanceExt_separated_eq_min {s : CodeState} {QA : List Nat}
    (hwf : EncodingWellFormed s) (hsep : Separated QA s) (σ : Sector) :
    exactDistanceExt σ s =
      ExtNat.min (exactDistanceExt σ (restrictBlock s QA))
                 (exactDistanceExt σ (restrictComplement s QA)) := by
  unfold exactDistanceExt
  rw [exactDistance?_separated_eq_min hwf hsep σ, ofOption_minOpt]

/-- Block-minimum decomposition for `exactDist` (both sectors and full). -/
theorem exactDist_separated_eq_min {s : CodeState} {QA : List Nat}
    (hwf : EncodingWellFormed s) (hsep : Separated QA s) :
    exactDist s =
      ExactDist.mk
        (minOpt (exactDist (restrictBlock s QA)).full (exactDist (restrictComplement s QA)).full)
        (minOpt (exactDist (restrictBlock s QA)).x (exactDist (restrictComplement s QA)).x)
        (minOpt (exactDist (restrictBlock s QA)).z (exactDist (restrictComplement s QA)).z) := by
  have hx : exactDistOpt Sector.X s =
      minOpt (exactDistOpt Sector.X (restrictBlock s QA))
             (exactDistOpt Sector.X (restrictComplement s QA)) := by
    rw [exactDistOpt_eq_exactDistance?, exactDistOpt_eq_exactDistance?,
      exactDistOpt_eq_exactDistance?]
    exact exactDistance?_separated_eq_min hwf hsep Sector.X
  have hz : exactDistOpt Sector.Z s =
      minOpt (exactDistOpt Sector.Z (restrictBlock s QA))
             (exactDistOpt Sector.Z (restrictComplement s QA)) := by
    rw [exactDistOpt_eq_exactDistance?, exactDistOpt_eq_exactDistance?,
      exactDistOpt_eq_exactDistance?]
    exact exactDistance?_separated_eq_min hwf hsep Sector.Z
  unfold exactDist
  rw [hx, hz, minOpt_interchange]

/-! ## Exact price decomposition for `E-SPLIT` (§4.48) -/

/-- Child `σ`-logicals promoted from the parent's `σ`-stabilizer space
    `S_σ(C) \ S_σ(C')`. -/
def splitPromotedVectors (s : CodeState) (R : List Nat) (σ : Sector) : List (List Bool) :=
  (logicalVectors (deleteAll s R) σ).filter (fun v => inSpanRowsBool s.Q (sectorRows s σ) v)

/-- Child `σ`-logicals newly exposed by deleting opposite-sector cut rows
    `N_σ(C') \ N_σ(C)`. -/
def splitExposedVectors (s : CodeState) (R : List Nat) (σ : Sector) : List (List Bool) :=
  (logicalVectors (deleteAll s R) σ).filter
    (fun v => !((sectorRows s (oppositeSector σ)).all (fun r => dotPar v (rowVector s.Q r) % 2 == 0)))

/-- Minimum weight among promoted vectors (`+∞` when none exist). -/
def splitPriceDel (s : CodeState) (R : List Nat) (σ : Sector) : ExtNat :=
  ExtNat.ofOption (minWeight? (splitPromotedVectors s R σ))

/-- Minimum weight among exposed vectors (`+∞` when none exist). -/
def splitPriceExp (s : CodeState) (R : List Nat) (σ : Sector) : ExtNat :=
  ExtNat.ofOption (minWeight? (splitExposedVectors s R σ))

private theorem leOpt_minWeight?_of_mem {v : List Bool} :
    ∀ {vs : List (List Bool)}, v ∈ vs → leOpt (minWeight? vs) (some (weight v))
  | [], h => nomatch h
  | w :: ws, h => by
      rw [minWeight?_cons]
      rcases List.mem_cons.mp h with rfl | h'
      · cases hws : minWeight? ws with
        | none => exact Nat.le_refl _
        | some m => exact Nat.min_le_left _ _
      · have ih := leOpt_minWeight?_of_mem h'
        cases hws : minWeight? ws with
        | none => rw [hws] at ih; exact False.elim ih
        | some m =>
            rw [hws] at ih
            exact Nat.le_trans (Nat.min_le_right _ _) ih

private theorem leOpt_minWeight?_of_subset {vs ws : List (List Bool)}
    (h : ∀ v ∈ ws, v ∈ vs) : leOpt (minWeight? vs) (minWeight? ws) := by
  cases hws : minWeight? ws with
  | none => exact leOpt_none _
  | some m =>
      obtain ⟨v, hv, hw⟩ := minWeight?_attained ws m hws
      rw [← hw]
      exact leOpt_minWeight?_of_mem (h v hv)

/-- Exact price decomposition in `Option Nat`: every child `σ`-logical is
    either a parent `σ`-logical, a promoted parent stabilizer, or an exposed
    vector, so `d_σ(C') = min(d_σ(C), w_del,σ, w_exp,σ)` (§4.48). -/
theorem exactDistance?_split_eq_min_price (s : CodeState) (R : List Nat) (σ : Sector) :
    exactDistance? σ (deleteAll s R) =
      minOpt (exactDistance? σ s)
        (minOpt (minWeight? (splitPromotedVectors s R σ))
                (minWeight? (splitExposedVectors s R σ))) := by
  have hQ : (deleteAll s R).Q = s.Q := deleteAll_Q R s
  have hsub : (deleteAll s R).rows.Sublist s.rows := deleteAll_rows_sublist R s
  apply leOpt_antisymm
  · apply leOpt_min
    · apply leOpt_minWeight?_of_subset
      intro v hv
      unfold logicalVectors at hv ⊢
      rw [List.mem_filter] at hv ⊢
      rw [hQ]
      exact ⟨hv.1, isLogical_mono s (deleteAll s R) σ hQ
        (spanLE_of_sublist _ (hsub.filter _))
        (spanLE_of_sublist _ (hsub.filter _)) v hv.2⟩
    · apply leOpt_min
      · exact leOpt_minWeight?_of_subset (fun v hv => (List.mem_filter.mp hv).1)
      · exact leOpt_minWeight?_of_subset (fun v hv => (List.mem_filter.mp hv).1)
  · cases hC' : exactDistance? σ (deleteAll s R) with
    | none => exact leOpt_none _
    | some m =>
        obtain ⟨v, hv, hw⟩ := minWeight?_attained _ m hC'
        cases horth : (sectorRows s (oppositeSector σ)).all
            (fun r => dotPar v (rowVector s.Q r) % 2 == 0) with
        | false =>
            have hexp : v ∈ splitExposedVectors s R σ :=
              List.mem_filter.mpr ⟨hv, by simp [horth]⟩
            have hle := leOpt_minWeight?_of_mem hexp
            rw [hw] at hle
            exact leOpt_trans (minOpt_le_right _ _) (leOpt_trans (minOpt_le_right _ _) hle)
        | true =>
            cases hspan : inSpanRowsBool s.Q (sectorRows s σ) v with
            | true =>
                have hprom : v ∈ splitPromotedVectors s R σ :=
                  List.mem_filter.mpr ⟨hv, hspan⟩
                have hle := leOpt_minWeight?_of_mem hprom
                rw [hw] at hle
                exact leOpt_trans (minOpt_le_right _ _) (leOpt_trans (minOpt_le_left _ _) hle)
            | false =>
                have hpar : v ∈ logicalVectors s σ := by
                  unfold logicalVectors at hv ⊢
                  rw [List.mem_filter] at hv ⊢
                  rw [hQ] at hv
                  refine ⟨hv.1, ?_⟩
                  unfold isLogicalBool
                  simp [horth, hspan]
                have hle := leOpt_minWeight?_of_mem hpar
                rw [hw] at hle
                exact leOpt_trans (minOpt_le_left _ _) hle

/-- Exact price decomposition in `ExtNat` (`ℕ ∪ {+∞}`, §4.48):
    `d_σ(deleteAll s R) = min(d_σ(s), splitPriceDel s R σ, splitPriceExp s R σ)`. -/
theorem exactDistanceExt_split_eq_min_price (s : CodeState) (R : List Nat) (σ : Sector) :
    exactDistanceExt σ (deleteAll s R) =
      ExtNat.min (exactDistanceExt σ s)
        (ExtNat.min (splitPriceDel s R σ) (splitPriceExp s R σ)) := by
  unfold exactDistanceExt splitPriceDel splitPriceExp
  rw [exactDistance?_split_eq_min_price s R σ, ofOption_minOpt, ofOption_minOpt]

/-- The same price decomposition read off an `Eval (Command.split QA R)` step. -/
theorem exactDistanceExt_eval_split_eq_min_price {QA R : List Nat} {s t : CodeState}
    (h : Eval (Command.split QA R) s t) (σ : Sector) :
    exactDistanceExt σ t =
      ExtNat.min (exactDistanceExt σ s)
        (ExtNat.min (splitPriceDel s R σ) (splitPriceExp s R σ)) := by
  rw [eval_split_eq h]
  exact exactDistanceExt_split_eq_min_price s R σ

/-! ## Conditional interval cell for `E-SPLIT` (§2a, §2b, §2c, §4.48) -/

/-- Sector-level `E-SPLIT` interval rule: unpriced resets lower to `0` and
    carries the parent upper endpoint; priced (`some (ia, ib)`) emits
    `[min(ia.lower, ib.lower), min(ia.upper, ib.upper, parent.upper)]`. -/
def splitSectorInterval (parent : Interval) (blocks : Option (Interval × Interval)) : Interval :=
  match blocks with
  | none => Interval.mk (some 0) parent.upper
  | some (ia, ib) =>
      Interval.mk (minOpt ia.lower ib.lower)
        (minOpt (minOpt ia.upper ib.upper) parent.upper)

/-- Priced `E-SPLIT` ledger transformer (`spec/JUDGMENT_LAYER.md` §2b–§2c, §4.48):
    when both sectors are supplied in `split_block_intervals`, the full interval
    is `minInterval ix iz`; otherwise the full lower endpoint resets to `0` and
    its upper endpoint is `min(ix.upper, iz.upper, L.full.upper)`. -/
def splitLedgerPriced (L : DistanceLedger)
    (xBlocks zBlocks : Option (Interval × Interval)) : DistanceLedger :=
  let ix := splitSectorInterval L.x xBlocks
  let iz := splitSectorInterval L.z zBlocks
  let ifull := match xBlocks, zBlocks with
    | some _, some _ => minInterval ix iz
    | _, _ => Interval.mk (some 0) (minOpt (minOpt ix.upper iz.upper) L.full.upper)
  { full := ifull, x := ix, z := iz }

/-- Unpriced `E-SPLIT` interval soundness for the exact distance (§4.48):
    `splitLedgerUnpriced L` contains `exactDist t` whenever `L` contains
    `exactDist s`. -/
theorem splitLedger_unpriced_sound {QA R : List Nat} {s t : CodeState}
    (_hwf : EncodingWellFormed s) (h : Eval (Command.split QA R) s t)
    (L : DistanceLedger) (hL : LedgerSound (exactDist s) L) :
    LedgerSound (exactDist t) (splitLedgerUnpriced L) := by
  have ht := eval_split_eq h
  subst ht
  obtain ⟨hdf, hdx, hdz⟩ :=
    exactDist_le_of_rows_sublist (deleteAll_Q R s) (deleteAll_rows_sublist R s)
  obtain ⟨hLf, hLx, hLz⟩ := hL
  exact ⟨⟨some_zero_leOpt _, leOpt_trans hdf hLf.2⟩,
    ⟨some_zero_leOpt _, leOpt_trans hdx hLx.2⟩,
    ⟨some_zero_leOpt _, leOpt_trans hdz hLz.2⟩⟩

private theorem splitSectorInterval_sound {parent : Interval} {blocks : Option (Interval × Interval)}
    {dPar dChild dA dB : Option Nat}
    (hPar : parent.contains dPar) (hle : leOpt dChild dPar)
    (hmin : dChild = minOpt dA dB)
    (hblocks : ∀ ia ib, blocks = some (ia, ib) → ia.contains dA ∧ ib.contains dB) :
    (splitSectorInterval parent blocks).contains dChild := by
  cases blocks with
  | none =>
      exact ⟨some_zero_leOpt _, leOpt_trans hle hPar.2⟩
  | some pair =>
      rcases pair with ⟨ia, ib⟩
      obtain ⟨hA, hB⟩ := hblocks ia ib rfl
      refine ⟨?_, ?_⟩
      · rw [hmin]
        exact minOpt_monotone hA.1 hB.1
      · apply leOpt_min
        · rw [hmin]
          exact minOpt_monotone hA.2 hB.2
        · exact leOpt_trans hle hPar.2

/-- Priced `E-SPLIT` interval soundness for the exact distance (§4.48):
    under sound block-restriction intervals for whichever sectors are priced,
    `splitLedgerPriced L xBlocks zBlocks` contains `exactDist t`. -/
theorem splitLedger_priced_sound {QA R : List Nat} {s t : CodeState}
    (hwf : EncodingWellFormed s) (h : Eval (Command.split QA R) s t)
    (L : DistanceLedger) (hL : LedgerSound (exactDist s) L)
    (xBlocks zBlocks : Option (Interval × Interval))
    (hx : ∀ ia ib, xBlocks = some (ia, ib) →
      ia.contains (exactDist (restrictBlock t QA)).x ∧
      ib.contains (exactDist (restrictComplement t QA)).x)
    (hz : ∀ ia ib, zBlocks = some (ia, ib) →
      ia.contains (exactDist (restrictBlock t QA)).z ∧
      ib.contains (exactDist (restrictComplement t QA)).z) :
    LedgerSound (exactDist t) (splitLedgerPriced L xBlocks zBlocks) := by
  have hwfT : EncodingWellFormed t := wf_of_eval_all h hwf
  have hsepT : Separated QA t := separated_of_eval_split h
  have hdecomp := exactDist_separated_eq_min hwfT hsepT
  have hle : leOpt (exactDist t).full (exactDist s).full ∧
      leOpt (exactDist t).x (exactDist s).x ∧
      leOpt (exactDist t).z (exactDist s).z := by
    rw [eval_split_eq h]
    exact exactDist_le_of_rows_sublist (deleteAll_Q R s) (deleteAll_rows_sublist R s)
  have hxSound : (splitSectorInterval L.x xBlocks).contains (exactDist t).x :=
    splitSectorInterval_sound hL.2.1 hle.2.1 (congrArg ExactDist.x hdecomp) hx
  have hzSound : (splitSectorInterval L.z zBlocks).contains (exactDist t).z :=
    splitSectorInterval_sound hL.2.2 hle.2.2 (congrArg ExactDist.z hdecomp) hz
  refine ⟨?_, hxSound, hzSound⟩
  cases xBlocks with
  | none =>
      refine ⟨some_zero_leOpt _, leOpt_min _ _ _ ?_ (leOpt_trans hle.1 hL.1.2)⟩
      rw [exactDist_full]
      exact minOpt_monotone hxSound.2 hzSound.2
  | some px =>
      cases zBlocks with
      | none =>
          refine ⟨some_zero_leOpt _, leOpt_min _ _ _ ?_ (leOpt_trans hle.1 hL.1.2)⟩
          rw [exactDist_full]
          exact minOpt_monotone hxSound.2 hzSound.2
      | some pz =>
          show (minInterval (splitSectorInterval L.x (some px))
                  (splitSectorInterval L.z (some pz))).contains (exactDist t).full
          rw [exactDist_full]
          exact minInterval_contains hxSound hzSound

private theorem splitSectorInterval_monotone {p1 p2 : Interval}
    (hp : p1.refines p2) {b1 b2 : Option (Interval × Interval)}
    (hb : match b1, b2 with
      | none, none => True
      | some (a1, c1), some (a2, c2) => a1.refines a2 ∧ c1.refines c2
      | _, _ => False) :
    (splitSectorInterval p1 b1).refines (splitSectorInterval p2 b2) := by
  cases b1 with
  | none =>
      cases b2 with
      | none => exact ⟨leOpt_refl _, hp.2⟩
      | some _ => exact False.elim hb
  | some p1b =>
      cases b2 with
      | none => exact False.elim hb
      | some p2b =>
          rcases p1b with ⟨a1, c1⟩
          rcases p2b with ⟨a2, c2⟩
          obtain ⟨ha, hc⟩ := hb
          exact ⟨minOpt_monotone ha.1 hc.1,
            minOpt_monotone (minOpt_monotone ha.2 hc.2) hp.2⟩

/-- Precision monotonicity of `splitLedgerPriced` (`JUDGMENT_LAYER.md` §8.4(2), §4.48):
    tightening the parent ledger and/or supplied block intervals tightens the output
    ledger componentwise. -/
theorem splitLedger_priced_monotone {L1 L2 : DistanceLedger}
    (hL : L1.refines L2)
    {x1 x2 z1 z2 : Option (Interval × Interval)}
    (hx : match x1, x2 with
      | none, none => True
      | some (a1, b1), some (a2, b2) => a1.refines a2 ∧ b1.refines b2
      | _, _ => False)
    (hz : match z1, z2 with
      | none, none => True
      | some (a1, b1), some (a2, b2) => a1.refines a2 ∧ b1.refines b2
      | _, _ => False) :
    (splitLedgerPriced L1 x1 z1).refines (splitLedgerPriced L2 x2 z2) := by
  have hrx := splitSectorInterval_monotone hL.2.1 hx
  have hrz := splitSectorInterval_monotone hL.2.2 hz
  refine ⟨?_, hrx, hrz⟩
  cases x1 with
  | none =>
      cases x2 with
      | none =>
          exact ⟨leOpt_refl _, minOpt_monotone (minOpt_monotone hrx.2 hrz.2) hL.1.2⟩
      | some _ => exact False.elim hx
  | some px1 =>
      cases x2 with
      | none => exact False.elim hx
      | some px2 =>
          cases z1 with
          | none =>
              cases z2 with
              | none =>
                  exact ⟨leOpt_refl _, minOpt_monotone (minOpt_monotone hrx.2 hrz.2) hL.1.2⟩
              | some _ => exact False.elim hz
          | some pz1 =>
              cases z2 with
              | none => exact False.elim hz
              | some pz2 =>
                  exact minInterval_monotone hrx hrz

end CodeCalculus
