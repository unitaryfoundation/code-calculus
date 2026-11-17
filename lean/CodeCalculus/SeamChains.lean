import CodeCalculus.Transport

namespace CodeCalculus

/-!
# The seam condition on chains of kernel, graft, and Gate 6 steps

`Derives.shift_gen` (`Transport.lean`) transports a derivation of a
generator-referencing claim from the second segment of a sequence into the
composed chain under the seam condition `SeamRowsDerived`: the composed
chain must derive, at the seam, the claim of every row the seam state
displays. This module proves that condition for every chain whose steps are single
(non-sequence) commands: the predicate `Command.isStep` is true exactly for
every command other than `seq`, so a `StepChain` is any chain with one state
per command.

`StepChain cs` says that every step of the chain `cs` is one `skip`,
deletion, addition, or graft. The result is a completeness statement for
the generator rows of `Derives` on such a chain:

* `derives_gen_of_displayed`: at every position, the claim of every row the
  state displays is derivable. The input display is the source at position
  0 (`Derives.genInput`), and across a step each row of the output is the
  image of an input row under the step's transport row or is a source of
  the step (`Derives.genMint`, `Derives.genGraftMint`).
* `seamRowsDerived_of_stepChain`: the seam condition holds whenever
  the composed chain is a `StepChain`.
* `Derives.shift_gen_of_stepChain`: the shift of `Derives.shift_gen`
  with the seam condition discharged.

With `judgment_soundness`, the claim `Ann.gen i r σ S` is derivable over a
well-formed `StepChain` exactly when the state at position `i`
displays the row (`derives_gen_iff_displayed`).

`Derives` has rows for `Ann.gen` under `E-EXTEND`, `E-PEEL`,
`E-PUNCTURE`, `E-LOCAL-HADAMARD`, and `P-REBASE`. The seam condition is
proved on every chain of single steps: at every position, the claim of
every row the state displays is derivable, and
`seamRowsDerived_of_stepChain` discharges the seam condition.
-/

/-- A single (non-sequence) command: every command except `seq`.
    Sequences are excluded, so a chain of such commands has one state per
    command step. -/
def Command.isStep : Command → Bool
  | .skip => true
  | .delete _ => true
  | .addStab _ _ => true
  | .graft _ _ _ => true
  | .peel _ _ _ => true
  | .puncture _ => true
  | .extend _ _ => true
  | .hadamard _ => true
  | .rebase _ _ => true
  | _ => false

/-- A chain whose every step is one single (non-sequence) command. -/
inductive StepChain : List CodeState → Prop where
  | single (s : CodeState) : StepChain [s]
  | cons {m : Command} {s t : CodeState} {cs : List CodeState}
      (hm : m.isStep = true) (hstep : Eval m s t)
      (hrest : StepChain (t :: cs)) : StepChain (s :: t :: cs)

theorem StepChain.toChain {cs : List CodeState} (h : StepChain cs) :
    Chain cs := by
  induction h with
  | single s => exact Chain.single s
  | cons _ hstep _ ih => exact Chain.cons hstep ih

/-- Two consecutive states of the chain are related by one single
    (non-sequence) command. -/
theorem StepChain.step {cs : List CodeState} (h : StepChain cs) :
    ∀ {i : Nat} {s t : CodeState}, cs[i]? = some s → cs[i + 1]? = some t →
      ∃ m, m.isStep = true ∧ Eval m s t := by
  induction h with
  | single x =>
      intro i s t _ hj
      simp at hj
  | @cons m x y cs' hm hstep _ ih =>
      intro i s t hi hj
      cases i with
      | zero =>
          have hx : x = s := by
            simpa only [List.getElem?_cons_zero, Option.some.injEq] using hi
          have hy : y = t := by
            simpa only [Nat.zero_add, List.getElem?_cons_succ, List.getElem?_cons_zero,
              Option.some.injEq] using hj
          subst hx
          subst hy
          exact ⟨m, hm, hstep⟩
      | succ i =>
          have hi' : (y :: cs')[i]? = some s := by
            simpa only [List.getElem?_cons_succ] using hi
          have hj' : (y :: cs')[i + 1]? = some t := by
            simpa only [List.getElem?_cons_succ] using hj
          exact ih hi' hj'

/-- The graft's shortening of a row, in the form of `graftSupport`. -/
theorem graftShorten_eq (q : Nat) (σ : Sector) (row : Row) :
    graftShorten q σ row =
      { id := row.id, sector := row.sector
      , support := graftSupport q σ row.sector row.support } := by
  cases row with
  | mk r τ S =>
      unfold graftShorten graftSupport
      rcases Decidable.em (τ = oppositeSector σ ∧ S.contains q = true) with hc | hc
      · rw [if_pos hc, if_pos hc]
        unfold shortenRow
        rw [if_pos hc.2]
      · rw [if_neg hc, if_neg hc]

/-- Completeness of the generator rows on a chain of single steps: at
    every position, the claim of every displayed row is derivable. -/
theorem derives_gen_of_displayed (dMeasure : Field → CodeState → Nat)
    {cs : List CodeState} (hchain : StepChain cs) :
    ∀ (i : Nat) (t : CodeState), cs[i]? = some t →
      ∀ (r : Nat) (σ : Sector) (S : List Nat),
        ({ id := r, sector := σ, support := S } : Row) ∈ t.rows →
        Derives dMeasure cs (Ann.gen i r σ S) := by
  intro i
  induction i with
  | zero =>
      intro t ht r σ S hrow
      exact Derives.genInput r σ S t ht hrow
  | succ i ih =>
      intro t ht r σ S hrow
      have hlt : i < cs.length := by
        have := (List.getElem?_eq_some_iff.mp ht).1
        omega
      obtain ⟨s, hs⟩ : ∃ s, cs[i]? = some s := ⟨cs[i], List.getElem?_eq_getElem hlt⟩
      obtain ⟨m, hm, hstep⟩ := hchain.step hs ht
      cases m with
      | skip =>
          have hts := eval_skip_eq hstep
          subst hts
          exact Derives.genSkip i r σ S _ _ hs ht hstep (ih _ hs r σ S hrow)
      | delete r' =>
          have hts := eval_delete_eq hstep
          subst hts
          have hmem := List.mem_filter.mp hrow
          have hne : r ≠ r' := of_decide_eq_true hmem.2
          exact Derives.genDelete i r r' σ S _ _ hs ht hstep hne (ih _ hs r σ S hmem.1)
      | addStab sector support =>
          have hts := eval_add_eq hstep
          subst hts
          rcases List.mem_append.mp hrow with hold | hnew
          · exact Derives.genAdd i r σ S sector support _ _ hs ht hstep (ih _ hs r σ S hold)
          · have hrow' := List.mem_singleton.mp hnew
            have hr : r = canonicalMint s.used := congrArg Row.id hrow'
            have hσ : σ = sector := congrArg Row.sector hrow'
            have hS : S = support := congrArg Row.support hrow'
            subst hr
            subst hσ
            subst hS
            exact Derives.genMint i σ S _ _ hs ht hstep
      | graft q sector ids =>
          have hts := eval_graft_eq hstep
          subst hts
          rcases mem_graftState_rows hrow with ⟨row0, hrow0, hshort⟩ | hminted
          · rw [graftShorten_eq] at hshort
            have hr : r = row0.id := congrArg Row.id hshort
            have hσ : σ = row0.sector := congrArg Row.sector hshort
            have hS : S = graftSupport q sector row0.sector row0.support :=
              congrArg Row.support hshort
            subst hr
            subst hσ
            subst hS
            have hfilter := List.mem_filter.mp hrow0
            have hnot : row0.id ∉ ids := by
              intro hc
              exact of_decide_eq_true hfilter.2 (List.contains_iff_mem.mpr hc)
            exact Derives.genGraft i row0.id row0.sector row0.support q sector ids _ _ hs ht
              hstep hnot (ih _ hs row0.id row0.sector row0.support hfilter.1)
          · exact Derives.genGraftMint i q sector ids _ _ _ hs ht hstep hminted
      | peel q tau r_id =>
          have hts := eval_peel_eq hstep
          subst hts
          have hmem := List.mem_map.mp hrow
          obtain ⟨row0, hrow0, hshort⟩ := hmem
          have hrow0' := List.mem_filter.mp hrow0
          have hid : (shortenRow q row0).id = row0.id := by unfold shortenRow; cases row0.support.contains q <;> rfl
          have hsec : (shortenRow q row0).sector = row0.sector := by unfold shortenRow; cases row0.support.contains q <;> rfl
          have hsup : (shortenRow q row0).support = peelSupport q row0.support := by unfold shortenRow peelSupport; cases row0.support.contains q <;> rfl
          have hr : row0.id = r := hid.symm.trans (congrArg Row.id hshort)
          have hσ : row0.sector = σ := hsec.symm.trans (congrArg Row.sector hshort)
          have hS : peelSupport q row0.support = S := hsup.symm.trans (congrArg Row.support hshort)
          rw [← hr, ← hσ, ← hS]
          have hnot : row0.id ≠ r_id := of_decide_eq_true hrow0'.2
          exact Derives.genPeel i row0.id r_id row0.sector row0.support q tau _ _ hs ht hstep hnot
            (ih _ hs row0.id row0.sector row0.support hrow0'.1)
      | puncture q =>
          have hts := eval_puncture_eq hstep
          subst hts
          have hmem := List.mem_filter.mp hrow
          have hsurvives : ¬ S.contains q := of_decide_eq_true hmem.2
          exact Derives.genPuncture i r σ S q _ _ hs ht hstep hsurvives
            (ih _ hs r σ S hmem.1)
      | extend delta adds =>
          have hts := eval_extend_eq hstep
          subst hts
          rcases List.mem_append.mp hrow with hold | hnew
          · exact Derives.genExtend i r σ S delta adds _ _ hs ht hstep
              (ih _ hs r σ S hold)
          · exact Derives.genExtendMint i delta adds _ _ ({ id := r, sector := σ, support := S }) hs ht hstep hnew
      | hadamard T =>
          if hT : T.isEmpty = true then
            have hts := eval_hadamard_eq hstep
            have hrow' : { id := r, sector := σ, support := S } ∈ s.rows := by
              rw [hts] at hrow
              simp [hadamardState, hT] at hrow
              exact hrow
            exact cast (congrArg (Derives dMeasure cs)
              (congrArg (fun x => Ann.gen (i + 1) r x S) (if_pos hT)))
              (Derives.genHadamard i r σ S T _ _ hs ht hstep (ih _ hs r σ S hrow'))
          else
            have hts := eval_hadamard_eq hstep
            have hrow' : { id := r, sector := σ, support := S } ∈ t.rows := hrow
            rw [hts] at hrow'
            have hT' : T.isEmpty = false := Bool.eq_false_of_ne_true hT
            simp [hadamardState, hT'] at hrow'
            have hmem := List.mem_map.mp hrow'
            obtain ⟨row0, hrow0, hswap⟩ := hmem
            have hrow0' : row0 ∈ s.rows := hrow0
            have hr : row0.id = r := congrArg Row.id hswap
            have hσ : oppositeSector row0.sector = σ := congrArg Row.sector hswap
            have hS : row0.support = S := congrArg Row.support hswap
            have heq : Ann.gen (i + 1) row0.id (if T.isEmpty = true then row0.sector else oppositeSector row0.sector) row0.support =
                Ann.gen (i + 1) r σ S := by
              rw [if_neg hT]
              rw [hr, hS, hσ]
            exact cast (congrArg (Derives dMeasure cs) heq)
              (Derives.genHadamard i row0.id row0.sector row0.support T _ _ hs ht hstep
                (ih _ hs row0.id row0.sector row0.support hrow0'))
      | rebase sector matrix =>
          have hts := eval_rebase_eq hstep
          subst hts
          rcases List.mem_append.mp hrow with hold | hnew
          · have hmem := List.mem_filter.mp hold
            have hsurvives : σ ≠ sector := of_decide_eq_true hmem.2
            exact Derives.genRebase i r σ S sector matrix _ _ hs ht hstep hsurvives
              (ih _ hs r σ S hmem.1)
          · exact Derives.genRebaseMint i sector matrix _ _ ({ id := r, sector := σ, support := S }) hs ht hstep hnew
      | seq _ _ => cases hm

/-- The seam condition of `Derives.shift_gen` holds when the composed chain
    is a chain of single steps. -/
theorem seamRowsDerived_of_stepChain (dMeasure : Field → CodeState → Nat)
    {cs ds : List CodeState} (hchain : StepChain (cs ++ ds)) :
    SeamRowsDerived dMeasure cs ds := by
  intro r σ S s h0 hrow
  have hpos : (cs ++ ds)[cs.length]? = some s := by
    have h := getElem?_shift_of_some (cs := cs) h0
    rwa [Nat.zero_add] at h
  exact derives_gen_of_displayed dMeasure hchain cs.length s hpos r σ S hrow

/-- `Derives.shift_gen` with the seam condition discharged: over a composed
    chain of kernel and graft steps, a derivation over the second segment
    shifts into the composed chain, generator-referencing claims
    included. -/
theorem Derives.shift_gen_of_stepChain {dMeasure : Field → CodeState → Nat}
    (cs : List CodeState) {ds : List CodeState} {a : Ann} (h : Derives dMeasure ds a)
    (hchain : StepChain (cs ++ ds)) :
    Derives dMeasure (cs ++ ds) (a.shift cs.length) :=
  h.shift_gen cs (seamRowsDerived_of_stepChain dMeasure hchain)

/-- On a well-formed chain of kernel and graft steps, the claim
    `Ann.gen i r σ S` is derivable exactly when the state at position `i`
    displays the row. -/
theorem derives_gen_iff_displayed (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) {cs : List CodeState}
    (hchain : StepChain cs) (hctxt : WellFormedContext cs)
    (i r : Nat) (σ : Sector) (S : List Nat) :
    Derives dMeasure cs (Ann.gen i r σ S) ↔
      ∃ s, cs[i]? = some s ∧ ({ id := r, sector := σ, support := S } : Row) ∈ s.rows := by
  constructor
  · intro h
    exact (judgment_soundness dMeasure hmono cs hctxt hchain.toChain _ h).truth
  · intro ⟨s, hs, hrow⟩
    exact derives_gen_of_displayed dMeasure hchain i s hs r σ S hrow

end CodeCalculus
