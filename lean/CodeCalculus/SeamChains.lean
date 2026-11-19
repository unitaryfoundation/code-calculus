import CodeCalculus.Transport
import CodeCalculus.TermSoundness

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

`StepChain cs` says that every step of the chain `cs` is one single
(non-sequence) command: `skip`, deletion, addition, graft, or one of the five
Gate 6 commands (`peel`, `puncture`, `extend`, `hadamard`, `rebase`). The
result is a completeness statement for the generator rows of `Derives` on such
a chain:

* `derives_gen_of_displayed`: at every position, the claim of every row the
  state displays is derivable. The input display is the source at position
  0 (`Derives.genInput`), and across a step each row of the output is the
  image of an input row under the step's transport row or is a source of
  the step (`Derives.genMint`, `Derives.genGraftMint`, `Derives.genExtendMint`,
  `Derives.genRebaseMint`).
* `seamRowsDerived_of_stepChain` and `seamRowsDerived_of_prefix_stepChain`:
  the seam condition holds whenever the composed chain (or even just its
  prefix up to the seam) is a `StepChain`.
* `Derives.shift_gen_of_stepChain` and `transport_right_gen_of_stepChain`:
  the shift of `Derives.shift_gen` with the seam condition discharged.
* `Trace.stepChain`, `seamRowsDerived_of_trace`, and
  `Derives.shift_gen_of_trace`: every command evaluation's `Trace`
  (`TermSoundness.lean`) is a `StepChain`, so the seam condition holds
  unconditionally across every sequenced command evaluation.

With `judgment_soundness`, the claim `Ann.gen i r σ S` is derivable over a
well-formed `StepChain` — and over any command `Trace` from a well-formed
input — exactly when the state at position `i` displays the row
(`derives_gen_iff_displayed`, `derives_gen_iff_displayed_of_trace`).
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
    chain of single (non-sequence) steps — kernel, graft, and Gate 6 — a
    derivation over the second segment shifts into the composed chain,
    generator-referencing claims included. -/
theorem Derives.shift_gen_of_stepChain {dMeasure : Field → CodeState → Nat}
    (cs : List CodeState) {ds : List CodeState} {a : Ann} (h : Derives dMeasure ds a)
    (hchain : StepChain (cs ++ ds)) :
    Derives dMeasure (cs ++ ds) (a.shift cs.length) :=
  h.shift_gen cs (seamRowsDerived_of_stepChain dMeasure hchain)

/-- On a well-formed chain of single (non-sequence) steps — kernel, graft,
    and Gate 6 — the claim `Ann.gen i r σ S` is derivable exactly when the
    state at position `i` displays the row. -/
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

/-! ## Composition of `StepChain` and connection to `Trace` (issue #534) -/

/-- `Command.isStep` is the exact complement of `Command.isSeq`. -/
theorem Command.isStep_iff_isSeq_false (m : Command) :
    m.isStep = true ↔ m.isSeq = false := by
  cases m <;> simp [Command.isStep, Command.isSeq]

/-- Two `StepChain`s sharing their seam state compose to a `StepChain`. -/
theorem stepChain_append {s : CodeState} {ds : List CodeState} :
    ∀ {cs : List CodeState}, StepChain (cs ++ [s]) → StepChain (s :: ds) →
      StepChain (cs ++ s :: ds)
  | [], _, h2 => h2
  | [x], h1, h2 => by
      have h1' : StepChain (x :: s :: []) := h1
      cases h1' with
      | cons hm hstep _ => exact StepChain.cons hm hstep h2
  | x :: y :: cs, h1, h2 => by
      have h1' : StepChain (x :: y :: (cs ++ [s])) := h1
      cases h1' with
      | cons hm hstep hrest =>
          have hrest' : StepChain ((y :: cs) ++ [s]) := hrest
          exact StepChain.cons hm hstep (stepChain_append hrest' h2)

/-- Two `StepChain`s compose when the first ends where the second starts. -/
theorem stepChain_glue {u : CodeState} {ds : List CodeState} :
    ∀ {cs : List CodeState} {s : CodeState}, StepChain (s :: cs) →
      (s :: cs).getLast? = some u → StepChain (u :: ds) →
      StepChain (s :: (cs ++ ds))
  | [], s, _, hlast, h2 => by
      have hs : s = u := by
        simpa only [List.getLast?_singleton, Option.some.injEq] using hlast
      subst hs
      exact h2
  | y :: cs, s, h1, hlast, h2 => by
      have hlast' : (y :: cs).getLast? = some u := by
        simpa only [List.getLast?_cons_cons] using hlast
      cases h1 with
      | cons hm hstep hrest =>
          show StepChain (s :: y :: (cs ++ ds))
          exact StepChain.cons hm hstep (stepChain_glue hrest hlast' h2)

/-- Every command evaluation trace unfolds to a `StepChain`: every leaf of
    `Trace` is a single (non-sequence) kernel, graft, or Gate 6 step. -/
theorem Trace.stepChain {m : Command} {s t : CodeState} {cs : List CodeState}
    (h : Trace m s cs t) : StepChain (s :: cs) := by
  induction h with
  | @step m s t hm hstep =>
      exact StepChain.cons ((Command.isStep_iff_isSeq_false m).mpr hm) hstep (StepChain.single t)
  | seq h1 _ ih1 ih2 => exact stepChain_glue ih1 h1.getLast ih2

/-- A prefix `StepChain` ending at the seam state `s` already discharges
    `SeamRowsDerived` for any suffix starting at `s`: the seam state's rows
    are derived on the prefix and weakened across the suffix. -/
theorem seamRowsDerived_of_prefix_stepChain (dMeasure : Field → CodeState → Nat)
    {cs ds : List CodeState} {s : CodeState} (h1 : StepChain (cs ++ [s])) :
    SeamRowsDerived dMeasure cs (s :: ds) := by
  intro r σ S s' h0 hrow
  have hs' : s = s' := Option.some.inj h0
  subst hs'
  have hpos : (cs ++ [s])[cs.length]? = some s := by
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  exact transport_left (derives_gen_of_displayed dMeasure h1 cs.length s hpos r σ S hrow)

/-- Segment-2 transport for generator-referencing claims (the `StepChain`
    counterpart of `transport_right`): a prefix `StepChain` ending at the seam
    state suffices to shift any derivation over the second segment. -/
theorem transport_right_gen_of_stepChain {dMeasure : Field → CodeState → Nat}
    {cs ds : List CodeState} {s : CodeState} {b : Ann}
    (h1 : StepChain (cs ++ [s])) (h : Derives dMeasure (s :: ds) b) :
    Derives dMeasure (cs ++ s :: ds) (b.shift cs.length) :=
  h.shift_gen cs (seamRowsDerived_of_prefix_stepChain dMeasure h1)

private theorem cons_eq_dropLast_append_last :
    ∀ (s : CodeState) (cs : List CodeState) (u : CodeState),
      (s :: cs).getLast? = some u →
      s :: cs = (s :: cs).dropLast ++ [u] ∧ (s :: cs).dropLast.length = cs.length
  | s, [], u, hlast => by
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      simp
  | s, y :: cs, u, hlast => by
      have hlast' : (y :: cs).getLast? = some u := by
        simpa only [List.getLast?_cons_cons] using hlast
      obtain ⟨heq, hlen⟩ := cons_eq_dropLast_append_last y cs u hlast'
      constructor
      · show s :: y :: cs = s :: (y :: cs).dropLast ++ [u]
        simpa only [List.cons_append] using congrArg (s :: ·) heq
      · show (s :: (y :: cs).dropLast).length = (y :: cs).length
        simp only [List.length_cons, hlen]

/-- The seam condition holds unconditionally on the trace of any first
    segment `m1` (including any sequence of kernel, graft, and Gate 6
    commands). -/
theorem seamRowsDerived_of_trace (dMeasure : Field → CodeState → Nat)
    {m1 : Command} {s u : CodeState} {cs ds : List CodeState}
    (h1 : Trace m1 s cs u) :
    SeamRowsDerived dMeasure (s :: cs).dropLast (u :: ds) := by
  obtain ⟨heq, _⟩ := cons_eq_dropLast_append_last s cs u h1.getLast
  have hpre : StepChain ((s :: cs).dropLast ++ [u]) := heq ▸ h1.stepChain
  exact seamRowsDerived_of_prefix_stepChain dMeasure hpre

/-- Unconditional shift of any derivation (generator-referencing claims
    included) from the second segment of a sequence into the composed trace
    `s :: (cs ++ ds)` of `Command.seq m1 m2`. -/
theorem Derives.shift_gen_of_trace {dMeasure : Field → CodeState → Nat}
    {m1 : Command} {s u : CodeState} {cs ds : List CodeState} {b : Ann}
    (h1 : Trace m1 s cs u) (hb : Derives dMeasure (u :: ds) b) :
    Derives dMeasure (s :: (cs ++ ds)) (b.shift cs.length) := by
  obtain ⟨heq, hlen⟩ := cons_eq_dropLast_append_last s cs u h1.getLast
  have hpre : StepChain ((s :: cs).dropLast ++ [u]) := heq ▸ h1.stepChain
  have hshift := transport_right_gen_of_stepChain hpre hb
  have hchainEq : (s :: cs).dropLast ++ u :: ds = s :: (cs ++ ds) := by
    calc (s :: cs).dropLast ++ u :: ds
        = (s :: cs).dropLast ++ ([u] ++ ds) := rfl
      _ = ((s :: cs).dropLast ++ [u]) ++ ds := (List.append_assoc _ _ _).symm
      _ = (s :: cs) ++ ds := by rw [← heq]
      _ = s :: (cs ++ ds) := rfl
  rw [hchainEq, hlen] at hshift
  exact hshift

/-- On the trace of any evaluated command from a well-formed input state,
    `Ann.gen i r σ S` is derivable exactly when the state at position `i`
    displays the row. -/
theorem derives_gen_iff_displayed_of_trace (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) {m : Command} {s t : CodeState}
    {cs : List CodeState} (htrace : Trace m s cs t) (hwf : EncodingWellFormed s)
    (i r : Nat) (σ : Sector) (S : List Nat) :
    Derives dMeasure (s :: cs) (Ann.gen i r σ S) ↔
      ∃ u, (s :: cs)[i]? = some u ∧ ({ id := r, sector := σ, support := S } : Row) ∈ u.rows :=
  derives_gen_iff_displayed dMeasure hmono htrace.stepChain
    (htrace.chain.wellFormedContext (fun x hx => by
      have hx' : s = x := Option.some.inj hx
      exact hx' ▸ hwf))
    i r σ S

/-! ### Worked multi-step Gate 6 seam chain (issue #534)

A three-step pure Gate 6 chain starting from `graftableState`:
1. `P-REBASE` in sector `X` with shear `[[1, 1], [0, 1]]` (retires `1, 2`;
   keeps `Z`-rows `3, 4`; mints `0 : X [1, 2, 3, 4]` and `5 : X [0, 2, 3, 4]`).
2. `E-LOCAL-HADAMARD` with `T = Q` (swaps all sectors: `0, 5` become `Z`;
   `3, 4` become `X`).
3. `E-PEEL` at qubit `1` in sector `Z` on the rebase-minted row `0` (retires
   `0`; shortens opposite-sector row `3` from `[0, 1, 2]` to `[0, 2]`; keeps
   `5 : Z [0, 2, 3, 4]` and `4 : X [3, 4]`).

Derivations over segment 2 (`[s1, s2, s3]`) start from `Derives.genInput` at
the seam state `s1` and shift into the composed chain `[s0, s1, s2, s3]` via
`Derives.shift_gen_of_stepChain` and `Derives.shift_gen_of_trace`. -/

def gate6SeamS1 : CodeState := rebaseState graftableState Sector.X [[1, 1], [0, 1]]
def gate6SeamS2 : CodeState := hadamardState gate6SeamS1 [0, 1, 2, 3, 4]
def gate6SeamS3 : CodeState := peelState gate6SeamS2 1 0

theorem gate6SeamS1_rows :
    gate6SeamS1.rows =
      [⟨3, Sector.Z, [0, 1, 2]⟩, ⟨4, Sector.Z, [3, 4]⟩,
       ⟨0, Sector.X, [1, 2, 3, 4]⟩, ⟨5, Sector.X, [0, 2, 3, 4]⟩] := by decide

theorem gate6SeamS2_rows :
    gate6SeamS2.rows =
      [⟨3, Sector.X, [0, 1, 2]⟩, ⟨4, Sector.X, [3, 4]⟩,
       ⟨0, Sector.Z, [1, 2, 3, 4]⟩, ⟨5, Sector.Z, [0, 2, 3, 4]⟩] := by decide

theorem eval_hadamard_gate6SeamS1 :
    Eval (Command.hadamard [0, 1, 2, 3, 4]) gate6SeamS1 gate6SeamS2 := by
  apply Eval.hadamard
  · exact Or.inl (List.Perm.refl _)
  · rfl
  · exact (wellFormedBool_iff _).mp (by decide)

theorem eval_peel_gate6SeamS2 :
    Eval (Command.peel 1 Sector.Z 0) gate6SeamS2 gate6SeamS3 := by
  apply Eval.peel
  · decide
  · exact ⟨⟨0, Sector.Z, [1, 2, 3, 4]⟩, by rw [gate6SeamS2_rows]; simp, rfl, rfl, by decide⟩
  · decide
  · decide
  · rfl
  · exact (wellFormedBool_iff _).mp (by decide)

theorem gate6PrefixStepChain : StepChain [graftableState, gate6SeamS1] :=
  StepChain.cons rfl eval_rebase_graftable (StepChain.single _)

theorem gate6SuffixStepChain : StepChain [gate6SeamS1, gate6SeamS2, gate6SeamS3] :=
  StepChain.cons rfl eval_hadamard_gate6SeamS1
    (StepChain.cons rfl eval_peel_gate6SeamS2 (StepChain.single _))

theorem gate6ComposedStepChain :
    StepChain [graftableState, gate6SeamS1, gate6SeamS2, gate6SeamS3] :=
  stepChain_append (cs := [graftableState]) gate6PrefixStepChain gate6SuffixStepChain

theorem gate6PrefixTrace :
    Trace (Command.rebase Sector.X [[1, 1], [0, 1]]) graftableState [gate6SeamS1] gate6SeamS1 :=
  Trace.step rfl eval_rebase_graftable

/-- Segment-2 derivation from `genInput` at the seam `gate6SeamS1`: row `3`
    swaps `Z → X` under `E-LOCAL-HADAMARD` and shortens `[0, 1, 2] → [0, 2]`
    under `E-PEEL`. -/
theorem derives_gate6_suffix_row3 (dMeasure : Field → CodeState → Nat) :
    Derives dMeasure [gate6SeamS1, gate6SeamS2, gate6SeamS3] (Ann.gen 2 3 Sector.X [0, 2]) :=
  Derives.genPeel 1 3 0 Sector.X [0, 1, 2] 1 Sector.Z _ _ rfl rfl eval_peel_gate6SeamS2
    (by decide)
    (Derives.genHadamard 0 3 Sector.Z [0, 1, 2] [0, 1, 2, 3, 4] _ _ rfl rfl
      eval_hadamard_gate6SeamS1
      (Derives.genInput 3 Sector.Z [0, 1, 2] _ rfl (by rw [gate6SeamS1_rows]; simp)))

/-- Segment-2 derivation from `genInput` at the seam `gate6SeamS1`: row `5`
    (minted by `P-REBASE` in segment 1) swaps `X → Z` under
    `E-LOCAL-HADAMARD` and survives `E-PEEL` unchanged. -/
theorem derives_gate6_suffix_row5 (dMeasure : Field → CodeState → Nat) :
    Derives dMeasure [gate6SeamS1, gate6SeamS2, gate6SeamS3]
      (Ann.gen 2 5 Sector.Z [0, 2, 3, 4]) :=
  Derives.genPeel 1 5 0 Sector.Z [0, 2, 3, 4] 1 Sector.Z _ _ rfl rfl eval_peel_gate6SeamS2
    (by decide)
    (Derives.genHadamard 0 5 Sector.X [0, 2, 3, 4] [0, 1, 2, 3, 4] _ _ rfl rfl
      eval_hadamard_gate6SeamS1
      (Derives.genInput 5 Sector.X [0, 2, 3, 4] _ rfl (by rw [gate6SeamS1_rows]; simp)))

/-- Seam transport on the composed Gate 6 chain via
    `Derives.shift_gen_of_stepChain`: row `3` at position `3`. -/
theorem derives_gate6_seam_row3 (dMeasure : Field → CodeState → Nat) :
    Derives dMeasure [graftableState, gate6SeamS1, gate6SeamS2, gate6SeamS3]
      (Ann.gen 3 3 Sector.X [0, 2]) :=
  (derives_gate6_suffix_row3 dMeasure).shift_gen_of_stepChain [graftableState]
    gate6ComposedStepChain

/-- Seam transport on the composed Gate 6 chain via `Derives.shift_gen_of_trace`:
    the rebase-minted row `5` shifts unconditionally across the seam to
    position `3`. -/
theorem derives_gate6_seam_row5 (dMeasure : Field → CodeState → Nat) :
    Derives dMeasure [graftableState, gate6SeamS1, gate6SeamS2, gate6SeamS3]
      (Ann.gen 3 5 Sector.Z [0, 2, 3, 4]) :=
  (derives_gate6_suffix_row5 dMeasure).shift_gen_of_trace gate6PrefixTrace

/-- `W13` refusal on the composed Gate 6 chain: row `0` (minted by `P-REBASE`,
    swapped by `E-LOCAL-HADAMARD`, and peeled by `E-PEEL`) has no derivable
    claim at position `3`, whatever sector and support are stated. -/
theorem not_derivable_gate6_seam_peeled_minted (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) (σ : Sector) (S : List Nat) :
    ¬ Derives dMeasure [graftableState, gate6SeamS1, gate6SeamS2, gate6SeamS3]
      (Ann.gen 3 0 σ S) :=
  not_derivable_gen_of_peeled dMeasure hmono
    (gate6ComposedStepChain.toChain.wellFormedContext (fun x hx => by
      have hx' : graftableState = x := Option.some.inj hx
      exact hx' ▸ encodingWellFormed_graftableState))
    gate6ComposedStepChain.toChain (i := 2) rfl rfl eval_peel_gate6SeamS2

end CodeCalculus
