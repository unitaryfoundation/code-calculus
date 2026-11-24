import CodeCalculus.WellFormedness
import CodeCalculus.WellFormedBool

/-!
# The retained display is well-formed

The first claim of `spec/OPERATIONAL_SEMANTICS.md` §4.34, for the state
updates of `Constructors.lean`: if the natural rows of the two sectors have
pairwise even overlap, the constructed state is well-formed
(`wf_constructedState`). The retained display is a sequence of `C-ADD-CHECK`
updates from the state with no rows, one for each natural row outside the
span of its sector's displayed rows, so the proof is an induction over
`wf_addState`. The qubit list is `0, …, n - 1` whatever the rows are
(`constructedState_Q`), which gives the `n` of each card.
-/

namespace CodeCalculus

/-! ## Supports of vectors -/

theorem supportOfVector_subset (n : Nat) (v : List Bool) :
    supportSubset (supportOfVector n v) (List.range n) := by
  intro q hq
  exact (List.mem_filter.mp hq).1

theorem supportOfVector_nodup (n : Nat) (v : List Bool) : (supportOfVector n v).Nodup :=
  List.Nodup.sublist List.filter_sublist (nodup_range_cf _)

theorem supportOfVector_sorted (n : Nat) (v : List Bool) :
    (supportOfVector n v).Pairwise (· ≤ ·) := by
  have h : (List.range n).Pairwise (· ≤ ·) :=
    List.Pairwise.imp (fun h => Nat.le_of_lt h) (pairwise_lt_range_cf _)
  exact List.Pairwise.sublist List.filter_sublist h

/-! ## The retained display as a sequence of additions -/

theorem retainStep_Q (s : CodeState) (x : Sector × List Nat) : (retainStep s x).Q = s.Q := by
  unfold retainStep
  split <;> rfl

theorem foldl_retainStep_Q : ∀ (l : List (Sector × List Nat)) (s : CodeState),
    (l.foldl retainStep s).Q = s.Q
  | [], _ => rfl
  | x :: l, s => by
      rw [List.foldl_cons, foldl_retainStep_Q l, retainStep_Q]

/-- The qubits of a constructed state are the labels `0, …, n - 1`. -/
theorem constructedState_Q (n : Nat) (vs : List (Sector × List Bool)) :
    (constructedState n vs).Q = List.range n := by
  unfold constructedState
  rw [foldl_retainStep_Q]
  rfl

/-- The `n` of a constructed state. -/
theorem constructedState_n (n : Nat) (vs : List (Sector × List Bool)) :
    (constructedState n vs).Q.length = n := by
  rw [constructedState_Q, List.length_range]

theorem constructedStateFrom_Q (used0 : List Nat) (n : Nat) (vs : List (Sector × List Bool)) :
    (constructedStateFrom used0 n vs).Q = List.range n := by
  unfold constructedStateFrom
  rw [foldl_retainStep_Q]
  rfl

theorem constructedStateFrom_n (used0 : List Nat) (n : Nat) (vs : List (Sector × List Bool)) :
    (constructedStateFrom used0 n vs).Q.length = n := by
  rw [constructedStateFrom_Q, List.length_range]

theorem wf_emptyState (n : Nat) : EncodingWellFormed (emptyState n) := by
  refine ⟨(nodup_range_cf _), List.nodup_nil, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro rX rZ hX
    cases hX
  · intro r hr
    cases hr

theorem wf_emptyStateWithUsed (n : Nat) (used0 : List Nat) :
    EncodingWellFormed (emptyStateWithUsed n used0) := by
  refine ⟨(nodup_range_cf _), List.nodup_nil, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro rX rZ hX
    cases hX
  · intro r hr
    cases hr

/-- The natural rows of the two sectors have pairwise even overlap. -/
def NaturalOrthogonal (rows : List (Sector × List Nat)) : Prop :=
  ∀ x ∈ rows, ∀ y ∈ rows, y.1 = oppositeSector x.1 →
    supportIntersectionSize x.2 y.2 % 2 = 0

/-- The decidable form of `NaturalOrthogonal`. -/
def naturalOrthogonalBool (rows : List (Sector × List Nat)) : Bool :=
  rows.all (fun x => rows.all (fun y =>
    !decide (y.1 = oppositeSector x.1) || supportIntersectionSize x.2 y.2 % 2 == 0))

theorem naturalOrthogonal_of_bool {rows : List (Sector × List Nat)}
    (h : naturalOrthogonalBool rows = true) : NaturalOrthogonal rows := by
  intro x hx y hy hsec
  unfold naturalOrthogonalBool at h
  rw [List.all_eq_true] at h
  have hx' := h x hx
  rw [List.all_eq_true] at hx'
  have hy' := hx' y hy
  rw [Bool.or_eq_true] at hy'
  rcases hy' with hneg | heven
  · rw [Bool.not_eq_true', decide_eq_false_iff_not] at hneg
    exact absurd hsec hneg
  · exact Nat.eq_of_beq_eq_true heven

/-- The invariant of the retained display along the natural rows. -/
theorem wf_foldl_retainStep (n : Nat) (all : List (Sector × List Nat))
    (hsup : ∀ x ∈ all, supportSubset x.2 (List.range n) ∧ x.2.Nodup ∧ x.2.Pairwise (· ≤ ·))
    (horth : NaturalOrthogonal all) :
    ∀ (l : List (Sector × List Nat)) (s : CodeState), (∀ x ∈ l, x ∈ all) →
      EncodingWellFormed s → s.Q = List.range n →
      (∀ r ∈ s.rows, (r.sector, r.support) ∈ all) →
      EncodingWellFormed (l.foldl retainStep s) ∧
        ∀ r ∈ (l.foldl retainStep s).rows, (r.sector, r.support) ∈ all
  | [], s, _, hwf, _, hrows => ⟨hwf, hrows⟩
  | x :: l, s, hl, hwf, hQ, hrows => by
      rw [List.foldl_cons]
      have hx : x ∈ all := hl x (List.mem_cons_self ..)
      have hl' : ∀ y ∈ l, y ∈ all := fun y hy => hl y (List.mem_cons_of_mem x hy)
      have hQ' : (retainStep s x).Q = List.range n := by rw [retainStep_Q, hQ]
      cases hb : inSpanRowsBool s.Q (s.rows.filter (fun r => r.sector = x.1))
          (s.Q.map (fun q => x.2.contains q)) with
      | true =>
          have hstep : retainStep s x = s := by
            unfold retainStep
            rw [hb]
            rfl
          rw [hstep]
          exact wf_foldl_retainStep n all hsup horth l s hl' hwf hQ hrows
      | false =>
          have hstep : retainStep s x = addState s x.1 x.2 := by
            unfold retainStep
            rw [hb]
            rfl
          obtain ⟨hsub, hnodup, hsorted⟩ := hsup x hx
          have hcomm : ∀ row ∈ s.rows, row.sector = oppositeSector x.1 →
              supportIntersectionSize x.2 row.support % 2 = 0 :=
            fun row hrow hsec => horth x hx (row.sector, row.support) (hrows row hrow) hsec
          have hspan : ¬ inSpanRows s.Q (sectorRows s x.1)
              (rowVector s.Q (addRow s x.1 x.2)) := by
            intro hin
            have := (inSpanRowsBool_iff _ _ _).mpr hin
            have hb' : inSpanRowsBool s.Q (sectorRows s x.1)
                (rowVector s.Q (addRow s x.1 x.2)) = false := hb
            rw [hb'] at this
            exact Bool.false_ne_true this
          have hwf' : EncodingWellFormed (addState s x.1 x.2) :=
            wf_addState s x.1 x.2 hwf (by rw [hQ]; exact hsub) hnodup hsorted hcomm hspan
          have hrows' : ∀ r ∈ (addState s x.1 x.2).rows, (r.sector, r.support) ∈ all := by
            intro r hr
            rcases List.mem_append.mp hr with h | h
            · exact hrows r h
            · have hr' : r = ⟨canonicalMint s.used, x.1, x.2⟩ := List.mem_singleton.mp h
              rw [hr']
              exact hx
          rw [hstep]
          rw [hstep] at hQ'
          exact wf_foldl_retainStep n all hsup horth l _ hl' hwf' hQ' hrows'

/-- §4.34, the retained display: natural rows with pairwise even overlap
    across the sectors give a well-formed constructed state. -/
theorem wf_constructedState (n : Nat) (vs : List (Sector × List Bool))
    (horth : NaturalOrthogonal (naturalRows n vs)) :
    EncodingWellFormed (constructedState n vs) := by
  have hsup : ∀ x ∈ naturalRows n vs,
      supportSubset x.2 (List.range n) ∧ x.2.Nodup ∧ x.2.Pairwise (· ≤ ·) := by
    intro x hx
    unfold naturalRows at hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact ⟨supportOfVector_subset n y.2, supportOfVector_nodup n y.2,
      supportOfVector_sorted n y.2⟩
  exact (wf_foldl_retainStep n (naturalRows n vs) hsup horth (naturalRows n vs)
    (emptyState n) (fun _ h => h) (wf_emptyState n) rfl (fun _ h => nomatch h)).1

/-- The same from the decidable overlap test. -/
theorem wf_constructedState_of_bool (n : Nat) (vs : List (Sector × List Bool))
    (h : naturalOrthogonalBool (naturalRows n vs) = true) :
    EncodingWellFormed (constructedState n vs) :=
  wf_constructedState n vs (naturalOrthogonal_of_bool h)

/-- §4.45: the retained display with identifiers canonically minted starting
    from `used0` is well-formed when the natural rows have pairwise even overlap. -/
theorem wf_constructedStateFrom (used0 : List Nat) (n : Nat) (vs : List (Sector × List Bool))
    (horth : NaturalOrthogonal (naturalRows n vs)) :
    EncodingWellFormed (constructedStateFrom used0 n vs) := by
  have hsup : ∀ x ∈ naturalRows n vs,
      supportSubset x.2 (List.range n) ∧ x.2.Nodup ∧ x.2.Pairwise (· ≤ ·) := by
    intro x hx
    unfold naturalRows at hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact ⟨supportOfVector_subset n y.2, supportOfVector_nodup n y.2,
      supportOfVector_sorted n y.2⟩
  exact (wf_foldl_retainStep n (naturalRows n vs) hsup horth (naturalRows n vs)
    (emptyStateWithUsed n used0) (fun _ h => h) (wf_emptyStateWithUsed n used0)
    rfl (fun _ h => nomatch h)).1

/-! ## The `n` of each card -/

theorem hgpState_n (H1 H2 : List (List Bool)) :
    (hgpState H1 H2).Q.length = matCols H1 * matCols H2 + H1.length * H2.length :=
  constructedState_n _ _

theorem liftState_n (orders : List Nat) (A B : List (List (List (List Nat)))) :
    (liftState orders A B).Q.length =
      (groupElements orders).length * (matCols A * matCols B + A.length * B.length) :=
  constructedState_n _ _

theorem twoblockState_n (orders : List Nat) (a b : List (List Nat)) :
    (twoblockState orders a b).Q.length = 2 * (groupElements orders).length :=
  constructedState_n _ _

theorem concatState_n (O I : CodeState) (blocks repsX repsZ : List (List Nat)) :
    (concatState O I blocks repsX repsZ).Q.length = I.Q.length * blocks.length :=
  constructedState_n _ _

end CodeCalculus
