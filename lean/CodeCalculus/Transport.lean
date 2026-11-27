import CodeCalculus.Soundness

namespace CodeCalculus

/-!
# Judgment transport through sequences (`OBL-JUDGMENT-TRANSPORT`)

Mechanized form of the transport half of `spec/OPERATIONAL_SEMANTICS.md` §4.11
("structural judgments compose through valid sequences; a claim that refers to
a deleted generator is not transported automatically"), on the `Chain`,
`Derives`, and `Models` machinery of `Soundness.lean`, together with the
fixed-reference-set invalidation model of §4.15 (a reviewed disposition) on
which the obligation's transported-context conclusion rests.

Four pieces.

1. Chains compose through `C-SEQUENCE`. Two valid chains that share their seam
   state compose to a valid chain (`chain_append`); a valid chain is the
   evaluation of one sequenced command from its head to its last state
   (`eval_of_chain`); a sequenced evaluation unfolds through its intermediate
   state (`chain_of_eval_seq`).

2. Derivations transport along that composition. A derivation over the first
   segment is a derivation over the composed chain unchanged
   (`Derives.weaken`), and one over the second segment is a derivation over the
   composed chain with every atom position shifted past the first segment
   (`Derives.shift`, for sentences that are not generator-referencing
   claims; item 6 covers those). The schema-composition condition of §4.11 is, in this
   encoding, position bookkeeping: a sentence derived over a segment mentions
   chain positions of that segment, and the two renamings are the identity and
   the shift. Across the seam, equalities compose by substitution and
   one-sided bounds of one polarity by transitivity (`transport_eq_eq`,
   `transport_le_le_down`, `transport_le_le_up`, `transport_le_eq`,
   `transport_eq_le`), which are §4.11's composition clauses;
   `transport_models` closes with `judgment_soundness` on the composed chain.
   The worked example of `Soundness.lean` is rederived this way
   (`derives_two_step_n_by_transport`).

3. The fixed-reference-set model (§4.15, annotation-transport part). Over any
   certificate type with a reference set `Ref c` of generator identifiers,
   deleting `r` maps `V ↦ V \ {c : r ∈ Ref c}` (`invalidate`). The family is
   pairwise commuting (`invalidate_comm`) and idempotent (`invalidate_idem`),
   and its composition over a list of deleted identifiers depends only on that
   list as a set (`invalidateAll_eq_filter`, `invalidateAll_set_determined`,
   `invalidateAll_perm`, `invalidateAll_idem`). A certificate that refers to a
   deleted identifier is absent from the transported context
   (`not_mem_invalidateAll_of_ref`), and one that refers to no deleted
   identifier survives (`mem_invalidateAll_of_survives`): the two halves of the
   obligation at the context level.

4. The `W13` refutation shape, absence of derivation as the witness
   (`spec/JUDGMENT_LAYER.md` §4, F7 disposition of 2026-10-11). A sentence
   false of a well-formed evaluation chain has no derivation over it
   (`not_derivable_of_false`, the contrapositive of `judgment_soundness`); that
   is the per-evaluation witness. It is instantiated on §4.11's own
   non-composition clause: on a delete-then-add chain the two one-sided
   distance bounds are derivable (`derives_mixed_delete_dX`,
   `derives_mixed_add_dX`) while neither composite bound is
   (`not_derivable_mixed_le`, `not_derivable_mixed_ge`). Separately, in a chain
   with no identity step, no equality between distance atoms at two positions
   is derivable for any choice of the measure
   (`not_derivable_distance_eq`), since the skip row is the only
   instantiation row that equates distance atoms; `not_derivable_mixed_eq` is
   its instance.

5. The derivation-level `W13` half. `Ann.gen i r σ S` is the
   claim that refers to a generator (`spec/JUDGMENT_LAYER.md` §4). It is
   sourced at the addition that mints the generator and transported through
   steps under which the generator survives; no row covers the deletion of
   the referenced generator, and `not_derivable_gen_of_deleted` is the
   resulting refutation, instantiated at the end of this module.

6. The input display and the graft. `Derives.genInput` is the
   source rule for the rows of the input display: at position 0 the claim of
   every displayed row is derivable. The graft has two rows. A generator
   outside the graft's chain survives, an opposite-sector row losing the
   grafted qubit (`Derives.genGraft`, with the support `graftSupport`), and
   each minted adjacent-product row is a source (`Derives.genGraftMint`).
   There is no row for a generator of the chain, which the graft retires,
   and `not_derivable_gen_of_grafted` is the refutation. The source rule
   reads the input of the chain it is used over, so a derivation over the
   second segment of a sequence shifts into the composed chain under a seam
   condition (`SeamRowsDerived`, `Derives.shift_gen`): the composed chain
   must derive the claims of the seam state's rows. Sentences that are not
   generator-referencing claims shift with no condition (`Derives.shift`).
   `SeamChains.lean` proves the seam condition on every chain of single
   (non-sequence) steps — kernel, graft, and Gate 6 — and connects it to the
   `Trace` of any evaluated command (`TermSoundness.lean`). The Gate 6 rows
   for `Ann.gen` — `E-EXTEND`, `E-PEEL`, `E-PUNCTURE`, `E-LOCAL-HADAMARD`,
   and `P-REBASE` — carry transport/mint rows, identifier-level refusals, and
   worked instances below.

What the slice does not do. The fixed-reference-set model is mechanized
abstractly, over an arbitrary certificate type, because the context-update
table that would fix `Ref` for concrete certificates is future context (R7
disposition at `OBL-ORDER-INDEPENDENT-DELETION`), and it is not connected to
`Eval`, since `spec/` does not specify what a non-deletion command does to a
context. Every refutation here is relative to the `Derives` inventory of this
development: it says that no derivation closes, not that none can (F7
disposition, second cost).
-/

/-! ## Chains compose through `C-SEQUENCE` -/

/-- Two valid chains that share their seam state compose to a valid chain. -/
theorem chain_append {s : CodeState} {ds : List CodeState} :
    ∀ {cs : List CodeState}, Chain (cs ++ [s]) → Chain (s :: ds) → Chain (cs ++ s :: ds)
  | [], _, h2 => h2
  | [x], h1, h2 => by
      have h1' : Chain (x :: s :: []) := h1
      cases h1' with
      | cons hstep _ => exact Chain.cons hstep h2
  | x :: y :: cs, h1, h2 => by
      have h1' : Chain (x :: y :: (cs ++ [s])) := h1
      cases h1' with
      | cons hstep hrest =>
          have hrest' : Chain ((y :: cs) ++ [s]) := hrest
          exact Chain.cons hstep (chain_append hrest' h2)

/-- A sequenced evaluation unfolds through its intermediate state. -/
theorem chain_of_eval_seq {m1 m2 : Command} {s t : CodeState}
    (h : Eval (Command.seq m1 m2) s t) :
    ∃ s1, Eval m1 s s1 ∧ Eval m2 s1 t ∧ Chain [s, s1, t] := by
  cases h with
  | seq h1 h2 => exact ⟨_, h1, h2, Chain.cons h1 (Chain.cons h2 (Chain.single _))⟩

/-- A valid chain is the evaluation of one sequenced command from its head to
    its last state. -/
theorem eval_of_chain : ∀ {cs : List CodeState} {s t : CodeState},
    Chain (s :: cs) → (s :: cs).getLast? = some t → ∃ m, Eval m s t
  | [], s, t, _, hlast => by
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      exact ⟨Command.skip, Eval.skip s⟩
  | u :: cs, s, t, h, hlast => by
      cases h with
      | cons hstep hrest =>
          have hlast' : (u :: cs).getLast? = some t := by
            simpa only [List.getLast?_cons_cons] using hlast
          obtain ⟨m2, h2⟩ := eval_of_chain hrest hlast'
          exact ⟨Command.seq _ m2, Eval.seq hstep h2⟩

/-- The well-formedness context of a composed chain. -/
theorem wellFormedContext_append {cs ds : List CodeState} {s : CodeState}
    (h1 : WellFormedContext (cs ++ [s])) (h2 : WellFormedContext (s :: ds)) :
    WellFormedContext (cs ++ s :: ds) := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact h1 t (List.mem_append_left _ h)
  · exact h2 t h

/-! ## Derivations transport along the composition -/

/-- Shift every atom position by `k`: the renaming a sentence undergoes when
    the chain it was derived over becomes the suffix of a longer chain. -/
def AExpr.shift (k : Nat) : AExpr → AExpr
  | .const v => .const v
  | .atom a => .atom ⟨a.pos + k, a.field⟩
  | .sub x y => .sub (x.shift k) (y.shift k)
  | .add x y => .add (x.shift k) (y.shift k)
  | .minOf x y => .minOf (x.shift k) (y.shift k)

/-- The shift on sentences. -/
def Ann.shift (k : Nat) : Ann → Ann
  | .le x y => .le (x.shift k) (y.shift k)
  | .eq x y => .eq (x.shift k) (y.shift k)
  | .wf i => .wf (i + k)
  | .gen i r σ S => .gen (i + k) r σ S

/-- A position of the first segment names the same state in the composed
    chain. -/
theorem getElem?_append_of_some {cs ds : List CodeState} {i : Nat} {s : CodeState}
    (h : cs[i]? = some s) : (cs ++ ds)[i]? = some s := by
  have hi : i < cs.length := (List.getElem?_eq_some_iff.mp h).1
  rw [List.getElem?_append_left hi]
  exact h

/-- A position of the second segment, shifted, names the same state in the
    composed chain. -/
theorem getElem?_append_shift (cs ds : List CodeState) (i : Nat) :
    (cs ++ ds)[i + cs.length]? = ds[i]? := by
  rw [List.getElem?_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel]

theorem getElem?_shift_of_some {cs ds : List CodeState} {i : Nat} {s : CodeState}
    (h : ds[i]? = some s) : (cs ++ ds)[i + cs.length]? = some s := by
  rw [getElem?_append_shift]
  exact h

theorem getElem?_shift_succ_of_some {cs ds : List CodeState} {i : Nat} {t : CodeState}
    (h : ds[i + 1]? = some t) : (cs ++ ds)[i + cs.length + 1]? = some t := by
  rw [Nat.add_right_comm i cs.length 1]
  exact getElem?_shift_of_some h

/-- The value of a shifted term over the composed chain is its value over the
    second segment. -/
theorem aexprValue_shift (dMeasure : Field → CodeState → Nat) (cs ds : List CodeState) :
    ∀ x : AExpr,
      aexprValue dMeasure (cs ++ ds) (x.shift cs.length) = aexprValue dMeasure ds x
  | .const _ => rfl
  | .atom a => by
      simp only [AExpr.shift, aexprValue, atomValue]
      rw [getElem?_append_shift]
  | .sub x y => by
      simp only [AExpr.shift, aexprValue]
      rw [aexprValue_shift dMeasure cs ds x, aexprValue_shift dMeasure cs ds y]
  | .add x y => by
      simp only [AExpr.shift, aexprValue]
      rw [aexprValue_shift dMeasure cs ds x, aexprValue_shift dMeasure cs ds y]
  | .minOf x y => by
      simp only [AExpr.shift, aexprValue]
      rw [aexprValue_shift dMeasure cs ds x, aexprValue_shift dMeasure cs ds y]

theorem denotes_shift {dMeasure : Field → CodeState → Nat} {cs ds : List CodeState}
    {x : AExpr} :
    denotes dMeasure (cs ++ ds) (x.shift cs.length) ↔ denotes dMeasure ds x := by
  unfold denotes
  rw [aexprValue_shift]

/-- Truth of a shifted sentence over the composed chain is its truth over the
    second segment. -/
theorem annTrue_shift {dMeasure : Field → CodeState → Nat} {cs ds : List CodeState}
    (a : Ann) :
    AnnTrue dMeasure (cs ++ ds) (a.shift cs.length) ↔ AnnTrue dMeasure ds a := by
  cases a with
  | le x y => simp only [Ann.shift, AnnTrue, aexprValue_shift]
  | eq x y => simp only [Ann.shift, AnnTrue, aexprValue_shift]
  | wf i =>
      simp only [Ann.shift, AnnTrue]
      constructor
      · rintro ⟨s, h, hwf⟩
        rw [getElem?_append_shift] at h
        exact ⟨s, h, hwf⟩
      · rintro ⟨s, h, hwf⟩
        exact ⟨s, by rw [getElem?_append_shift]; exact h, hwf⟩
  | gen i r σ S =>
      simp only [Ann.shift, AnnTrue]
      constructor
      · rintro ⟨s, h, hmem⟩
        rw [getElem?_append_shift] at h
        exact ⟨s, h, hmem⟩
      · rintro ⟨s, h, hmem⟩
        exact ⟨s, by rw [getElem?_append_shift]; exact h, hmem⟩

/-- `optMin` is defined when either argument is. -/
theorem optMin_eq_some_iff (a b : Option Nat) :
    (∃ v, optMin a b = some v) ↔ ((∃ v, a = some v) ∨ (∃ v, b = some v)) := by
  cases a <;> cases b <;> simp [optMin]

/-- A term that denotes over the first segment denotes over the composed
    chain (its value may change when a `min` argument beyond the first segment
    becomes defined, which is why this is stated on `denotes`, not on the
    value). -/
theorem denotes_append {dMeasure : Field → CodeState → Nat} {cs ds : List CodeState} :
    ∀ {x : AExpr}, denotes dMeasure cs x → denotes dMeasure (cs ++ ds) x
  | .const v, _ => ⟨v, rfl⟩
  | .atom a, h => by
      obtain ⟨v, hv⟩ := h
      simp only [aexprValue, atomValue] at hv
      cases hcs : cs[a.pos]? with
      | none =>
          rw [hcs] at hv
          simp at hv
      | some s =>
          exact ⟨fieldValue dMeasure a.field s, by
            simp only [aexprValue, atomValue]
            rw [getElem?_append_of_some hcs]
            rfl⟩
  | .sub x y, h => by
      obtain ⟨v, hv⟩ := h
      simp only [aexprValue] at hv ⊢
      revert hv
      cases hx : aexprValue dMeasure cs x <;> cases hy : aexprValue dMeasure cs y <;> intro hv
      · simp at hv
      · simp at hv
      · simp at hv
      · obtain ⟨a', ha'⟩ := denotes_append (ds := ds) (x := x) ⟨_, hx⟩
        obtain ⟨b', hb'⟩ := denotes_append (ds := ds) (x := y) ⟨_, hy⟩
        exact ⟨a' - b', by simp [aexprValue, ha', hb']⟩
  | .add x y, h => by
      obtain ⟨v, hv⟩ := h
      simp only [aexprValue] at hv ⊢
      revert hv
      cases hx : aexprValue dMeasure cs x <;> cases hy : aexprValue dMeasure cs y <;> intro hv
      · simp at hv
      · simp at hv
      · simp at hv
      · obtain ⟨a', ha'⟩ := denotes_append (ds := ds) (x := x) ⟨_, hx⟩
        obtain ⟨b', hb'⟩ := denotes_append (ds := ds) (x := y) ⟨_, hy⟩
        exact ⟨a' + b', by simp [aexprValue, ha', hb']⟩
  | .minOf x y, h => by
      simp only [denotes, aexprValue] at h ⊢
      rcases (optMin_eq_some_iff _ _).mp h with hx | hy
      · obtain ⟨a', ha'⟩ := denotes_append (ds := ds) (x := x) hx
        rw [ha']
        cases aexprValue dMeasure (cs ++ ds) y <;> exact ⟨_, rfl⟩
      · obtain ⟨b', hb'⟩ := denotes_append (ds := ds) (x := y) hy
        rw [hb']
        cases aexprValue dMeasure (cs ++ ds) x <;> exact ⟨_, rfl⟩

/-- Positive half, first segment: a derivation over a chain is a derivation
    over any extension of it, unchanged. -/
theorem Derives.weaken {dMeasure : Field → CodeState → Nat} {cs : List CodeState}
    (ds : List CodeState) {a : Ann} (h : Derives dMeasure cs a) :
    Derives dMeasure (cs ++ ds) a := by
  induction h with
  | instSkip i f s t hi hj hstep =>
      exact Derives.instSkip i f s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instDeleteN i r s t hi hj hstep =>
      exact Derives.instDeleteN i r s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instAddN i sector support s t hi hj hstep =>
      exact Derives.instAddN i sector support s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instGraftN i q sector ids s t hi hj hstep =>
      exact Derives.instGraftN i q sector ids s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instDeleteK i r s t hi hj hstep =>
      exact Derives.instDeleteK i r s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instDeleteKSub i r s t hi hj hstep =>
      exact Derives.instDeleteKSub i r s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instAddK i sector support s t hi hj hstep =>
      exact Derives.instAddK i sector support s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instAddKSub i sector support s t hi hj hstep =>
      exact Derives.instAddKSub i sector support s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instGraftK i q sector ids s t hi hj hstep =>
      exact Derives.instGraftK i q sector ids s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instSkipWF i s t hi hj hstep =>
      exact Derives.instSkipWF i s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instDeleteWF i r s t hi hj hstep =>
      exact Derives.instDeleteWF i r s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instAddWF i sector support s t hi hj hstep =>
      exact Derives.instAddWF i sector support s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instGraftWF i q sector ids s t hi hj hstep =>
      exact Derives.instGraftWF i q sector ids s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instDeleteDX i r s t hi hj hstep =>
      exact Derives.instDeleteDX i r s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instDeleteDZ i r s t hi hj hstep =>
      exact Derives.instDeleteDZ i r s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instDeleteD i r s t hi hj hstep =>
      exact Derives.instDeleteD i r s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instAddDX i sector support s t hi hj hstep =>
      exact Derives.instAddDX i sector support s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instAddDZ i sector support s t hi hj hstep =>
      exact Derives.instAddDZ i sector support s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instAddD i sector support s t hi hj hstep =>
      exact Derives.instAddD i sector support s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | transit_le_le x y z _ _ ih1 ih2 => exact Derives.transit_le_le x y z ih1 ih2
  | transit_le_eq x y z _ _ ih1 ih2 => exact Derives.transit_le_eq x y z ih1 ih2
  | transit_eq_le x y z _ _ ih1 ih2 => exact Derives.transit_eq_le x y z ih1 ih2
  | transit_eq_eq x y z _ _ ih1 ih2 => exact Derives.transit_eq_eq x y z ih1 ih2
  | min_le_left x y hx => exact Derives.min_le_left x y (denotes_append hx)
  | min_le_right x y hy => exact Derives.min_le_right x y (denotes_append hy)
  | le_min t x y _ _ ih1 ih2 => exact Derives.le_min t x y ih1 ih2
  | le_refl x hx => exact Derives.le_refl x (denotes_append hx)
  | eq_refl x hx => exact Derives.eq_refl x (denotes_append hx)
  | eq_sym x y _ ih => exact Derives.eq_sym x y ih
  | genMint i sector support s t hi hj hstep =>
      exact Derives.genMint i sector support s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | genSkip i r σ S s t hi hj hstep _ ih =>
      exact Derives.genSkip i r σ S s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep ih
  | genDelete i r r' σ S s t hi hj hstep hsurvives _ ih =>
      exact Derives.genDelete i r r' σ S s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hsurvives ih
  | genAdd i r σ S sector support s t hi hj hstep _ ih =>
      exact Derives.genAdd i r σ S sector support s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep ih
  | genInput r σ S s h0 hrow =>
      exact Derives.genInput r σ S s (getElem?_append_of_some h0) hrow
  | genGraft i r σ S q sector ids s t hi hj hstep hsurvives _ ih =>
      exact Derives.genGraft i r σ S q sector ids s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hsurvives ih
  | genGraftMint i q sector ids s t row hi hj hstep hrow =>
      exact Derives.genGraftMint i q sector ids s t row (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hrow
  | genExtend i r σ S delta adds s t hi hj hstep _ ih =>
      exact Derives.genExtend i r σ S delta adds s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep ih
  | genExtendMint i delta adds s t row hi hj hstep hrow =>
      exact Derives.genExtendMint i delta adds s t row (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hrow
  | genPeel i r r_id σ S q tau s t hi hj hstep hsurvives _ ih =>
      exact Derives.genPeel i r r_id σ S q tau s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hsurvives ih
  | genPuncture i r σ S q s t hi hj hstep hsurvives _ ih =>
      exact Derives.genPuncture i r σ S q s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hsurvives ih
  | genHadamard i r σ S T s t hi hj hstep hg _ ih =>
      exact Derives.genHadamard i r σ S T s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hg ih
  | genHadamardSplit i T s t row hi hj hstep hsplit hrow =>
      exact Derives.genHadamardSplit i T s t row (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hsplit hrow
  | genRebase i r σ S sector matrix s t hi hj hstep hsurvives _ ih =>
      exact Derives.genRebase i r σ S sector matrix s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hsurvives ih
  | genRebaseMint i sector matrix s t row hi hj hstep hrow =>
      exact Derives.genRebaseMint i sector matrix s t row (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hrow
  | genCnotSwap i r σ S U s t hi hj hstep _ ih =>
      exact Derives.genCnotSwap i r σ S U s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep ih
  | genSplit i r σ S QA R s t hi hj hstep hsurvives _ ih =>
      exact Derives.genSplit i r σ S QA R s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hsurvives ih

/-- A sentence is a generator-referencing claim. -/
def Ann.isGen : Ann → Bool
  | .gen _ _ _ _ => true
  | _ => false

/-- The seam condition for generator-referencing claims : the
    composed chain derives, at the seam, the claim of every row the second
    segment's input displays. The source rule `Derives.genInput` reads the
    input display of the chain it is used over, and the second segment's
    input is the seam state of the composed chain, where a claim has to be
    derived from the composed chain's own sources. -/
def SeamRowsDerived (dMeasure : Field → CodeState → Nat) (cs ds : List CodeState) : Prop :=
  ∀ (r : Nat) (σ : Sector) (S : List Nat) (s : CodeState), ds[0]? = some s →
    ({ id := r, sector := σ, support := S } : Row) ∈ s.rows →
    Derives dMeasure (cs ++ ds) (Ann.gen cs.length r σ S)

/-- Positive half, second segment, in one statement: a derivation over a
    chain is a derivation over any chain that has it as a suffix, with every
    position shifted past the prefix, provided that, when the sentence is a
    generator-referencing claim, the seam condition holds. -/
theorem Derives.shift_cond {dMeasure : Field → CodeState → Nat} (cs : List CodeState)
    {ds : List CodeState} {a : Ann} (h : Derives dMeasure ds a) :
    (a.isGen = true → SeamRowsDerived dMeasure cs ds) →
    Derives dMeasure (cs ++ ds) (a.shift cs.length) := by
  induction h with
  | instSkip i f s t hi hj hstep =>
      intro hsrc
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instSkip (i + cs.length) f s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instDeleteN i r s t hi hj hstep =>
      intro hsrc
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instDeleteN (i + cs.length) r s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instAddN i sector support s t hi hj hstep =>
      intro hsrc
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instAddN (i + cs.length) sector support s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instGraftN i q sector ids s t hi hj hstep =>
      intro hsrc
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instGraftN (i + cs.length) q sector ids s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instDeleteK i r s t hi hj hstep =>
      intro hsrc
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instDeleteK (i + cs.length) r s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instDeleteKSub i r s t hi hj hstep =>
      intro hsrc
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instDeleteKSub (i + cs.length) r s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instAddK i sector support s t hi hj hstep =>
      intro hsrc
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instAddK (i + cs.length) sector support s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instAddKSub i sector support s t hi hj hstep =>
      intro hsrc
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instAddKSub (i + cs.length) sector support s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instGraftK i q sector ids s t hi hj hstep =>
      intro hsrc
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instGraftK (i + cs.length) q sector ids s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instSkipWF i s t hi hj hstep =>
      intro hsrc
      simp only [Ann.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instSkipWF (i + cs.length) s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instDeleteWF i r s t hi hj hstep =>
      intro hsrc
      simp only [Ann.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instDeleteWF (i + cs.length) r s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instAddWF i sector support s t hi hj hstep =>
      intro hsrc
      simp only [Ann.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instAddWF (i + cs.length) sector support s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instGraftWF i q sector ids s t hi hj hstep =>
      intro hsrc
      simp only [Ann.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instGraftWF (i + cs.length) q sector ids s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instDeleteDX i r s t hi hj hstep =>
      intro hsrc
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instDeleteDX (i + cs.length) r s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instDeleteDZ i r s t hi hj hstep =>
      intro hsrc
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instDeleteDZ (i + cs.length) r s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instDeleteD i r s t hi hj hstep =>
      intro hsrc
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instDeleteD (i + cs.length) r s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instAddDX i sector support s t hi hj hstep =>
      intro hsrc
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instAddDX (i + cs.length) sector support s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instAddDZ i sector support s t hi hj hstep =>
      intro hsrc
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instAddDZ (i + cs.length) sector support s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instAddD i sector support s t hi hj hstep =>
      intro hsrc
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instAddD (i + cs.length) sector support s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | transit_le_le x y z _ _ ih1 ih2 =>
      intro hsrc
      have ih1 := ih1 (fun h => absurd h Bool.false_ne_true)
      have ih2 := ih2 (fun h => absurd h Bool.false_ne_true)
      simp only [Ann.shift] at ih1 ih2 ⊢
      exact Derives.transit_le_le _ _ _ ih1 ih2
  | transit_le_eq x y z _ _ ih1 ih2 =>
      intro hsrc
      have ih1 := ih1 (fun h => absurd h Bool.false_ne_true)
      have ih2 := ih2 (fun h => absurd h Bool.false_ne_true)
      simp only [Ann.shift] at ih1 ih2 ⊢
      exact Derives.transit_le_eq _ _ _ ih1 ih2
  | transit_eq_le x y z _ _ ih1 ih2 =>
      intro hsrc
      have ih1 := ih1 (fun h => absurd h Bool.false_ne_true)
      have ih2 := ih2 (fun h => absurd h Bool.false_ne_true)
      simp only [Ann.shift] at ih1 ih2 ⊢
      exact Derives.transit_eq_le _ _ _ ih1 ih2
  | transit_eq_eq x y z _ _ ih1 ih2 =>
      intro hsrc
      have ih1 := ih1 (fun h => absurd h Bool.false_ne_true)
      have ih2 := ih2 (fun h => absurd h Bool.false_ne_true)
      simp only [Ann.shift] at ih1 ih2 ⊢
      exact Derives.transit_eq_eq _ _ _ ih1 ih2
  | min_le_left x y hx =>
      intro hsrc
      simp only [Ann.shift, AExpr.shift]
      exact Derives.min_le_left _ _ (denotes_shift.mpr hx)
  | min_le_right x y hy =>
      intro hsrc
      simp only [Ann.shift, AExpr.shift]
      exact Derives.min_le_right _ _ (denotes_shift.mpr hy)
  | le_min t x y _ _ ih1 ih2 =>
      intro hsrc
      have ih1 := ih1 (fun h => absurd h Bool.false_ne_true)
      have ih2 := ih2 (fun h => absurd h Bool.false_ne_true)
      simp only [Ann.shift, AExpr.shift] at ih1 ih2 ⊢
      exact Derives.le_min _ _ _ ih1 ih2
  | le_refl x hx =>
      intro hsrc
      simp only [Ann.shift]
      exact Derives.le_refl _ (denotes_shift.mpr hx)
  | eq_refl x hx =>
      intro hsrc
      simp only [Ann.shift]
      exact Derives.eq_refl _ (denotes_shift.mpr hx)
  | eq_sym x y _ ih =>
      intro hsrc
      have ih := ih (fun h => absurd h Bool.false_ne_true)
      simp only [Ann.shift] at ih ⊢
      exact Derives.eq_sym _ _ ih
  | genMint i sector support s t hi hj hstep =>
      intro hsrc
      simp only [Ann.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.genMint (i + cs.length) sector support s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | genSkip i r σ S s t hi hj hstep _ ih =>
      intro hsrc
      have ih := ih (fun _ => hsrc rfl)
      simp only [Ann.shift] at ih ⊢
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.genSkip (i + cs.length) r σ S s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep ih
  | genDelete i r r' σ S s t hi hj hstep hsurvives _ ih =>
      intro hsrc
      have ih := ih (fun _ => hsrc rfl)
      simp only [Ann.shift] at ih ⊢
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.genDelete (i + cs.length) r r' σ S s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep hsurvives ih
  | genAdd i r σ S sector support s t hi hj hstep _ ih =>
      intro hsrc
      have ih := ih (fun _ => hsrc rfl)
      simp only [Ann.shift] at ih ⊢
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.genAdd (i + cs.length) r σ S sector support s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep ih
  | genInput r σ S s h0 hrow =>
      intro hsrc
      simp only [Ann.shift]
      rw [Nat.zero_add]
      exact hsrc rfl r σ S s h0 hrow
  | genGraft i r σ S q sector ids s t hi hj hstep hsurvives _ ih =>
      intro hsrc
      have ih := ih (fun _ => hsrc rfl)
      simp only [Ann.shift] at ih ⊢
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.genGraft (i + cs.length) r σ S q sector ids s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep hsurvives ih
  | genGraftMint i q sector ids s t row hi hj hstep hrow =>
      intro hsrc
      simp only [Ann.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.genGraftMint (i + cs.length) q sector ids s t row
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep hrow
  | genExtend i r σ S delta adds s t hi hj hstep _ ih =>
      intro hsrc
      have ih := ih (fun _ => hsrc rfl)
      simp only [Ann.shift] at ih ⊢
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.genExtend (i + cs.length) r σ S delta adds s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep ih
  | genExtendMint i delta adds s t row hi hj hstep hrow =>
      intro hsrc
      simp only [Ann.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.genExtendMint (i + cs.length) delta adds s t row
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep hrow
  | genPeel i r r_id σ S q tau s t hi hj hstep hsurvives _ ih =>
      intro hsrc
      have ih := ih (fun _ => hsrc rfl)
      simp only [Ann.shift] at ih ⊢
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.genPeel (i + cs.length) r r_id σ S q tau s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep hsurvives ih
  | genPuncture i r σ S q s t hi hj hstep hsurvives _ ih =>
      intro hsrc
      have ih := ih (fun _ => hsrc rfl)
      simp only [Ann.shift] at ih ⊢
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.genPuncture (i + cs.length) r σ S q s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep hsurvives ih
  | genHadamard i r σ S T s t hi hj hstep hg _ ih =>
      intro hsrc
      have ih := ih (fun _ => hsrc rfl)
      simp only [Ann.shift] at ih ⊢
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.genHadamard (i + cs.length) r σ S T s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep hg ih
  | genHadamardSplit i T s t row hi hj hstep hsplit hrow =>
      intro hsrc
      simp only [Ann.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.genHadamardSplit (i + cs.length) T s t row (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep hsplit hrow
  | genRebase i r σ S sector matrix s t hi hj hstep hsurvives _ ih =>
      intro hsrc
      have ih := ih (fun _ => hsrc rfl)
      simp only [Ann.shift] at ih ⊢
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.genRebase (i + cs.length) r σ S sector matrix s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep hsurvives ih
  | genRebaseMint i sector matrix s t row hi hj hstep hrow =>
      intro hsrc
      simp only [Ann.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.genRebaseMint (i + cs.length) sector matrix s t row (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep hrow
  | genCnotSwap i r σ S U s t hi hj hstep _ ih =>
      intro hsrc
      have ih := ih (fun _ => hsrc rfl)
      simp only [Ann.shift] at ih ⊢
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.genCnotSwap (i + cs.length) r σ S U s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep ih
  | genSplit i r σ S QA R s t hi hj hstep hsurvives _ ih =>
      intro hsrc
      have ih := ih (fun _ => hsrc rfl)
      simp only [Ann.shift] at ih ⊢
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.genSplit (i + cs.length) r σ S QA R s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep hsurvives ih

/-- Positive half, second segment: a derivation of a sentence that is not a
    generator-referencing claim over a chain is a derivation over any chain
    that has it as a suffix, with every position shifted past the prefix. -/
theorem Derives.shift {dMeasure : Field → CodeState → Nat} (cs : List CodeState)
    {ds : List CodeState} {a : Ann} (h : Derives dMeasure ds a)
    (ha : a.isGen = false := by rfl) :
    Derives dMeasure (cs ++ ds) (a.shift cs.length) :=
  h.shift_cond cs (fun hg => absurd (ha.symm.trans hg) Bool.false_ne_true)

/-- Positive half, second segment, for generator-referencing claims: the
    shift holds under the seam condition. -/
theorem Derives.shift_gen {dMeasure : Field → CodeState → Nat} (cs : List CodeState)
    {ds : List CodeState} {a : Ann} (h : Derives dMeasure ds a)
    (hsrc : SeamRowsDerived dMeasure cs ds) :
    Derives dMeasure (cs ++ ds) (a.shift cs.length) :=
  h.shift_cond cs (fun _ => hsrc)

/-- A judgment derived over the first segment of a sequence is derivable over
    the composed chain, unchanged. -/
theorem transport_left {dMeasure : Field → CodeState → Nat} {cs ds : List CodeState}
    {s : CodeState} {a : Ann} (h : Derives dMeasure (cs ++ [s]) a) :
    Derives dMeasure (cs ++ s :: ds) a := by
  have h' := h.weaken ds
  rwa [List.append_assoc, List.singleton_append] at h'

/-- A judgment derived over the second segment of a sequence is derivable over
    the composed chain, its positions shifted past the first segment. -/
theorem transport_right {dMeasure : Field → CodeState → Nat} (cs : List CodeState)
    {ds : List CodeState} {s : CodeState} {b : Ann} (h : Derives dMeasure (s :: ds) b)
    (hb : b.isGen = false := by rfl) :
    Derives dMeasure (cs ++ s :: ds) (b.shift cs.length) :=
  h.shift cs hb

/-- The seam state is read at position `cs.length` by the first segment and at
    position `0` by the second; the shift identifies the two readings. -/
theorem seam_atom_shift (cs : List CodeState) (f : Field) :
    (AExpr.atom ⟨0, f⟩).shift cs.length = AExpr.atom ⟨cs.length, f⟩ := by
  simp [AExpr.shift]

/-- Equalities compose by substitution across the seam: the first segment ends
    with the seam value equal to `x`, the second starts with `y` equal to the
    seam value, so `y` (shifted) equals `x` over the composed chain. -/
theorem transport_eq_eq {dMeasure : Field → CodeState → Nat} {cs ds : List CodeState}
    {s : CodeState} {f : Field} {x y : AExpr}
    (h1 : Derives dMeasure (cs ++ [s]) (Ann.eq (AExpr.atom ⟨cs.length, f⟩) x))
    (h2 : Derives dMeasure (s :: ds) (Ann.eq y (AExpr.atom ⟨0, f⟩))) :
    Derives dMeasure (cs ++ s :: ds) (Ann.eq (y.shift cs.length) x) := by
  have h2' := transport_right cs h2
  simp only [Ann.shift, seam_atom_shift] at h2'
  exact Derives.transit_eq_eq _ _ _ h2' (transport_left h1)

/-- Non-increasing bounds compose by transitivity across the seam (the
    deletion polarity: seam `≤ x` and `y ≤` seam give `y ≤ x`). -/
theorem transport_le_le_down {dMeasure : Field → CodeState → Nat} {cs ds : List CodeState}
    {s : CodeState} {f : Field} {x y : AExpr}
    (h1 : Derives dMeasure (cs ++ [s]) (Ann.le (AExpr.atom ⟨cs.length, f⟩) x))
    (h2 : Derives dMeasure (s :: ds) (Ann.le y (AExpr.atom ⟨0, f⟩))) :
    Derives dMeasure (cs ++ s :: ds) (Ann.le (y.shift cs.length) x) := by
  have h2' := transport_right cs h2
  simp only [Ann.shift, seam_atom_shift] at h2'
  exact Derives.transit_le_le _ _ _ h2' (transport_left h1)

/-- Non-decreasing bounds compose by transitivity across the seam (the
    addition polarity: `x ≤` seam and seam `≤ y` give `x ≤ y`). -/
theorem transport_le_le_up {dMeasure : Field → CodeState → Nat} {cs ds : List CodeState}
    {s : CodeState} {f : Field} {x y : AExpr}
    (h1 : Derives dMeasure (cs ++ [s]) (Ann.le x (AExpr.atom ⟨cs.length, f⟩)))
    (h2 : Derives dMeasure (s :: ds) (Ann.le (AExpr.atom ⟨0, f⟩) y)) :
    Derives dMeasure (cs ++ s :: ds) (Ann.le x (y.shift cs.length)) := by
  have h2' := transport_right cs h2
  simp only [Ann.shift, seam_atom_shift] at h2'
  exact Derives.transit_le_le _ _ _ (transport_left h1) h2'

/-- A bound followed by an equality: `x ≤` seam and `y =` seam give
    `x ≤ y`. -/
theorem transport_le_eq {dMeasure : Field → CodeState → Nat} {cs ds : List CodeState}
    {s : CodeState} {f : Field} {x y : AExpr}
    (h1 : Derives dMeasure (cs ++ [s]) (Ann.le x (AExpr.atom ⟨cs.length, f⟩)))
    (h2 : Derives dMeasure (s :: ds) (Ann.eq y (AExpr.atom ⟨0, f⟩))) :
    Derives dMeasure (cs ++ s :: ds) (Ann.le x (y.shift cs.length)) := by
  have h2' := transport_right cs h2
  simp only [Ann.shift, seam_atom_shift] at h2'
  exact Derives.transit_le_eq _ _ _ (transport_left h1) (Derives.eq_sym _ _ h2')

/-- An equality followed by a bound: seam `= x` and `y ≤` seam give
    `y ≤ x`. -/
theorem transport_eq_le {dMeasure : Field → CodeState → Nat} {cs ds : List CodeState}
    {s : CodeState} {f : Field} {x y : AExpr}
    (h1 : Derives dMeasure (cs ++ [s]) (Ann.eq (AExpr.atom ⟨cs.length, f⟩) x))
    (h2 : Derives dMeasure (s :: ds) (Ann.le y (AExpr.atom ⟨0, f⟩))) :
    Derives dMeasure (cs ++ s :: ds) (Ann.le (y.shift cs.length) x) := by
  have h2' := transport_right cs h2
  simp only [Ann.shift, seam_atom_shift] at h2'
  exact Derives.transit_le_eq _ _ _ h2' (transport_left h1)

/-- Transported judgments are true of the composed chain: `judgment_soundness`
    on the composition, under the two segments' chain and context
    hypotheses. -/
theorem transport_models {dMeasure : Field → CodeState → Nat}
    (hmono : MeasureMonotone dMeasure) {cs ds : List CodeState}
    {s : CodeState}
    (hctxt1 : WellFormedContext (cs ++ [s])) (hctxt2 : WellFormedContext (s :: ds))
    (hchain1 : Chain (cs ++ [s])) (hchain2 : Chain (s :: ds))
    {a : Ann} (h : Derives dMeasure (cs ++ s :: ds) a) :
    Models dMeasure (cs ++ s :: ds) a :=
  judgment_soundness dMeasure hmono _ (wellFormedContext_append hctxt1 hctxt2)
    (chain_append hchain1 hchain2) a h

/-- The worked example of `Soundness.lean`, rederived by transport: the two
    one-step chains of the two-deletion term are composed at their seam, and
    the two `n` cells compose into the sentence about the outer pair. -/
theorem derives_two_step_n_by_transport (dMeasure : Field → CodeState → Nat) :
    Derives dMeasure [twoDeleteState, deleteState twoDeleteState 1,
      deleteState (deleteState twoDeleteState 1) 2]
      (Ann.eq (AExpr.atom ⟨2, Field.n⟩) (AExpr.atom ⟨0, Field.n⟩)) :=
  transport_eq_eq (cs := [twoDeleteState])
    (ds := [deleteState (deleteState twoDeleteState 1) 2])
    (Derives.instDeleteN 0 1 _ _ rfl rfl eval_delete_1_twoDeleteState)
    (Derives.instDeleteN 0 2 _ _ rfl rfl eval_delete_2_of_deleteState)

/-! ## The fixed-reference-set model (§4.15, a reviewed disposition) -/

section FixedReferenceSet

variable {C : Type} (Ref : C → List Nat)

/-- Deleting identifier `r` removes every certificate that refers to it:
    `V ↦ V \ {c : r ∈ Ref c}`. -/
def invalidate (r : Nat) (V : List C) : List C :=
  V.filter (fun c => decide (r ∉ Ref c))

/-- Deleting the identifiers of `S`, in order. -/
def invalidateAll (S : List Nat) (V : List C) : List C :=
  S.foldl (fun V r => invalidate Ref r V) V

theorem mem_invalidate {r : Nat} {V : List C} {c : C} :
    c ∈ invalidate Ref r V ↔ c ∈ V ∧ r ∉ Ref c := by
  simp [invalidate, List.mem_filter]

/-- The update family is pairwise commuting. -/
theorem invalidate_comm (r r' : Nat) (V : List C) :
    invalidate Ref r (invalidate Ref r' V) = invalidate Ref r' (invalidate Ref r V) := by
  simp only [invalidate, List.filter_filter]
  apply List.filter_congr
  intro c _
  exact Bool.and_comm _ _

/-- The update family is idempotent: a certificate is invalidated once. -/
theorem invalidate_idem (r : Nat) (V : List C) :
    invalidate Ref r (invalidate Ref r V) = invalidate Ref r V := by
  simp only [invalidate, List.filter_filter]
  apply List.filter_congr
  intro c _
  exact Bool.and_self _

theorem invalidateAll_nil (V : List C) : invalidateAll Ref [] V = V := rfl

theorem invalidateAll_cons (r : Nat) (S : List Nat) (V : List C) :
    invalidateAll Ref (r :: S) V = invalidateAll Ref S (invalidate Ref r V) := rfl

/-- Sequencing two deletion batches composes their updates. -/
theorem invalidateAll_append (S T : List Nat) (V : List C) :
    invalidateAll Ref (S ++ T) V = invalidateAll Ref T (invalidateAll Ref S V) :=
  List.foldl_append

theorem mem_invalidateAll {S : List Nat} {V : List C} {c : C} :
    c ∈ invalidateAll Ref S V ↔ c ∈ V ∧ ∀ r ∈ S, r ∉ Ref c := by
  induction S generalizing V with
  | nil => simp [invalidateAll]
  | cons r S ih =>
      rw [invalidateAll_cons, ih, mem_invalidate]
      constructor
      · rintro ⟨⟨hc, hr⟩, hS⟩
        refine ⟨hc, fun r' hr' => ?_⟩
        rcases List.mem_cons.mp hr' with rfl | h
        · exact hr
        · exact hS r' h
      · rintro ⟨hc, h⟩
        exact ⟨⟨hc, h r List.mem_cons_self⟩, fun r' hr' => h r' (List.mem_cons_of_mem _ hr')⟩

/-- The composition over a deleted-identifier list is the set-level
    difference `V \ ⋃_{r ∈ S} {c : r ∈ Ref c}`. -/
theorem invalidateAll_eq_filter (S : List Nat) (V : List C) :
    invalidateAll Ref S V = V.filter (fun c => decide (∀ r ∈ S, r ∉ Ref c)) := by
  induction S generalizing V with
  | nil => exact (List.filter_eq_self.mpr (fun _ _ => by simp)).symm
  | cons r S ih =>
      rw [invalidateAll_cons, ih]
      simp only [invalidate, List.filter_filter]
      apply List.filter_congr
      intro c _
      simp [Bool.and_comm]

/-- The transported context depends only on the deleted identifiers as a
    set. -/
theorem invalidateAll_set_determined {S S' : List Nat} (h : ∀ r, r ∈ S ↔ r ∈ S')
    (V : List C) : invalidateAll Ref S V = invalidateAll Ref S' V := by
  rw [invalidateAll_eq_filter, invalidateAll_eq_filter]
  apply List.filter_congr
  intro c _
  exact decide_eq_decide.mpr
    ⟨fun hS r hr => hS r ((h r).mpr hr), fun hS' r hr => hS' r ((h r).mp hr)⟩

/-- Order independence: any enumeration order of the deleted set gives the
    same transported context. -/
theorem invalidateAll_perm {S S' : List Nat} (p : S.Perm S') (V : List C) :
    invalidateAll Ref S V = invalidateAll Ref S' V :=
  invalidateAll_set_determined Ref (fun _r => p.mem_iff) V

/-- Deleting a batch twice is deleting it once. -/
theorem invalidateAll_idem (S : List Nat) (V : List C) :
    invalidateAll Ref S (invalidateAll Ref S V) = invalidateAll Ref S V := by
  rw [← invalidateAll_append]
  exact invalidateAll_set_determined Ref (fun _r => by simp) V

/-- Invalidation adds nothing to the context. -/
theorem invalidateAll_sublist (S : List Nat) (V : List C) :
    (invalidateAll Ref S V).Sublist V := by
  rw [invalidateAll_eq_filter]
  exact List.filter_sublist

/-- `W13` at the context level: a certificate that refers to a deleted
    identifier is not in the transported context. -/
theorem not_mem_invalidateAll_of_ref {S : List Nat} {V : List C} {c : C} {r : Nat}
    (hr : r ∈ S) (hc : r ∈ Ref c) : c ∉ invalidateAll Ref S V :=
  fun h => ((mem_invalidateAll Ref).mp h).2 r hr hc

/-- The positive half at the context level: a certificate that refers to no
    deleted identifier is transported. -/
theorem mem_invalidateAll_of_survives {S : List Nat} {V : List C} {c : C}
    (hc : c ∈ V) (h : ∀ r ∈ S, r ∉ Ref c) : c ∈ invalidateAll Ref S V :=
  (mem_invalidateAll Ref).mpr ⟨hc, h⟩

end FixedReferenceSet

/-! ## Absence of derivation as the witness (`W13` shape) -/

/-- A sentence false of a well-formed evaluation chain has no derivation over
    it: the contrapositive of `judgment_soundness`, and the per-evaluation
    refutation witness of the F7 disposition. Relative to the `Derives`
    inventory: no derivation closes, not none can. -/
theorem not_derivable_of_false (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) (cs : List CodeState)
    (hctxt : WellFormedContext cs) (hchain : Chain cs) {a : Ann}
    (hfalse : ¬ AnnTrue dMeasure cs a) : ¬ Derives dMeasure cs a :=
  fun h => hfalse (judgment_soundness dMeasure hmono cs hctxt hchain a h).truth

/-- Every atom of the term reads a structural field (`n` or `k`). -/
def AExpr.structural : AExpr → Prop
  | .const _ => True
  | .atom a => a.field = Field.n ∨ a.field = Field.k
  | .sub x y => x.structural ∧ y.structural
  | .add x y => x.structural ∧ y.structural
  | .minOf x y => x.structural ∧ y.structural

/-- Derivable equalities are trivial or structural: the invariant that
    excludes distance equalities from the chains below. -/
def EqInvariant : Ann → Prop
  | .le _ _ => True
  | .eq x y => x = y ∨ (x.structural ∧ y.structural)
  | .wf _ => True
  | .gen _ _ _ _ => True

/-- No step of the chain is an identity. The skip row is the only
    instantiation row whose conclusion equates a distance atom at two
    positions, and it needs an identity step. -/
def ConsecutiveDistinct (cs : List CodeState) : Prop :=
  ∀ i s t, cs[i]? = some s → cs[i + 1]? = some t → s ≠ t

theorem eqInvariant_of_derives {dMeasure : Field → CodeState → Nat} {cs : List CodeState}
    (hcd : ConsecutiveDistinct cs) {a : Ann} (h : Derives dMeasure cs a) : EqInvariant a := by
  induction h with
  | instSkip i f s t hi hj hstep => exact absurd (eval_skip_eq hstep).symm (hcd i s t hi hj)
  | instDeleteN _ _ _ _ _ _ _ => exact Or.inr ⟨Or.inl rfl, Or.inl rfl⟩
  | instAddN _ _ _ _ _ _ _ _ => exact Or.inr ⟨Or.inl rfl, Or.inl rfl⟩
  | instGraftN _ _ _ _ _ _ _ _ _ => exact Or.inr ⟨Or.inl rfl, Or.inl rfl, trivial⟩
  | instDeleteK _ _ _ _ _ _ _ => exact Or.inr ⟨Or.inr rfl, Or.inr rfl, trivial⟩
  | instDeleteKSub _ _ _ _ _ _ _ => exact Or.inr ⟨Or.inr rfl, Or.inr rfl, trivial⟩
  | instAddK _ _ _ _ _ _ _ _ => exact Or.inr ⟨Or.inr rfl, Or.inr rfl, trivial⟩
  | instAddKSub _ _ _ _ _ _ _ _ => exact Or.inr ⟨Or.inr rfl, Or.inr rfl, trivial⟩
  | instGraftK _ _ _ _ _ _ _ _ _ => exact Or.inr ⟨Or.inr rfl, Or.inr rfl⟩
  | instSkipWF _ _ _ _ _ _ => trivial
  | instDeleteWF _ _ _ _ _ _ _ => trivial
  | instAddWF _ _ _ _ _ _ _ _ => trivial
  | instGraftWF _ _ _ _ _ _ _ _ _ => trivial
  | instDeleteDX _ _ _ _ _ _ _ => trivial
  | instDeleteDZ _ _ _ _ _ _ _ => trivial
  | instDeleteD _ _ _ _ _ _ _ => trivial
  | instAddDX _ _ _ _ _ _ _ _ => trivial
  | instAddDZ _ _ _ _ _ _ _ _ => trivial
  | instAddD _ _ _ _ _ _ _ _ => trivial
  | transit_le_le _ _ _ _ _ _ _ => trivial
  | transit_le_eq _ _ _ _ _ _ _ => trivial
  | transit_eq_le _ _ _ _ _ _ _ => trivial
  | transit_eq_eq x y z _ _ ih1 ih2 =>
      rcases ih1 with rfl | ⟨hx, hy⟩
      · exact ih2
      · rcases ih2 with rfl | ⟨_, hz⟩
        · exact Or.inr ⟨hx, hy⟩
        · exact Or.inr ⟨hx, hz⟩
  | min_le_left _ _ _ => trivial
  | min_le_right _ _ _ => trivial
  | le_min _ _ _ _ _ _ _ => trivial
  | le_refl _ _ => trivial
  | eq_refl _ _ => exact Or.inl rfl
  | eq_sym x y _ ih =>
      rcases ih with rfl | ⟨hx, hy⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hy, hx⟩
  | genMint _ _ _ _ _ _ _ _ => trivial
  | genSkip _ _ _ _ _ _ _ _ _ _ _ => trivial
  | genDelete _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  | genAdd _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  | genInput _ _ _ _ _ _ => trivial
  | genGraft _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  | genGraftMint _ _ _ _ _ _ _ _ _ _ _ => trivial
  | genExtend _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  | genExtendMint _ _ _ _ _ _ _ _ _ _ => trivial
  | genPeel _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  | genPuncture _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  | genHadamard _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  | genHadamardSplit _ _ _ _ _ _ _ _ _ _ => trivial
  | genRebase _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  | genRebaseMint _ _ _ _ _ _ _ _ _ _ => trivial
  | genCnotSwap _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  | genSplit _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial

/-- In a chain with no identity step, no equality between distance atoms at
    two positions is derivable, for any choice of the measure: instantiation
    is the only source of a distance fact (§4.11), and the distance rows of
    this inventory are one-sided. Relative to the inventory, as above. -/
theorem not_derivable_distance_eq (dMeasure : Field → CodeState → Nat) {cs : List CodeState}
    (hcd : ConsecutiveDistinct cs) {i j : Nat} {f : Field}
    (hf : f = Field.dX ∨ f = Field.dZ ∨ f = Field.d) (hij : i ≠ j) :
    ¬ Derives dMeasure cs (Ann.eq (AExpr.atom ⟨i, f⟩) (AExpr.atom ⟨j, f⟩)) := by
  intro h
  have hinv := eqInvariant_of_derives hcd h
  simp only [EqInvariant, AExpr.structural, AExpr.atom.injEq, Atom.mk.injEq] at hinv
  rcases hinv with ⟨hij', _⟩ | ⟨hx, _⟩
  · exact hij hij'
  · rcases hf with rfl | rfl | rfl <;> rcases hx with h' | h' <;> cases h'

/-! ### The mixed delete-then-add instance of §4.11's non-composition clause -/

/-- The canonical mint over the two-deletion state's `used` set. -/
theorem canonicalMint_twoDelete : canonicalMint [1, 2] = 0 := by decide

/-- The two-deletion state after one deletion and one addition: `X` row `2`
    on qubit `1` survives, and an `X` row on qubit `0` is added under the
    canonical mint. -/
def mixedState : CodeState := addState (deleteState twoDeleteState 1) Sector.X [0]

theorem independent_added_mixedState :
    ¬ inSpanRows (deleteState twoDeleteState 1).Q
      (sectorRows (deleteState twoDeleteState 1) Sector.X)
      (rowVector (deleteState twoDeleteState 1).Q
        ⟨canonicalMint (deleteState twoDeleteState 1).used, Sector.X, [0]⟩) := by
  intro hspan
  rcases hspan with ⟨coeffs, hlen, hcomb⟩
  cases coeffs with
  | nil => simp [sectorRows, deleteState, twoDeleteState] at hlen
  | cons c0 tl =>
    cases tl with
    | cons _ _ => cases hlen
    | nil =>
      cases c0 <;>
        simp [combineRows, xorVec, rowVector, sectorRows, deleteState, twoDeleteState] at hcomb

theorem eval_add_mixedState :
    Eval (Command.addStab Sector.X [0]) (deleteState twoDeleteState 1) mixedState :=
  Eval.add
    (by
      intro q hq
      simp [deleteState, twoDeleteState] at hq ⊢
      omega)
    (by decide)
    (by decide)
    (by
      intro row hrow hsec
      simp [deleteState, twoDeleteState] at hrow
      subst hrow
      simp [oppositeSector] at hsec)
    independent_added_mixedState
    rfl
    (by decide)

/-- The delete-then-add chain. -/
def mixedChain : List CodeState :=
  [twoDeleteState, deleteState twoDeleteState 1, mixedState]

theorem chain_mixed : Chain mixedChain :=
  Chain.cons eval_delete_1_twoDeleteState
    (Chain.cons eval_add_mixedState (Chain.single _))

theorem independent_2_mixedState : IndependentGenerator 2 mixedState := by
  show ¬ inSpanRows mixedState.Q
    (mixedState.rows.filter (fun r' => r'.sector = Sector.X ∧ r'.id ≠ 2))
    (rowVector mixedState.Q ⟨2, Sector.X, [1]⟩)
  intro hspan
  rcases hspan with ⟨coeffs, hlen, hcomb⟩
  cases coeffs with
  | nil => simp [mixedState, addState, deleteState, twoDeleteState, canonicalMint_twoDelete] at hlen
  | cons c0 tl =>
    cases tl with
    | cons _ _ =>
        cases hlen
    | nil =>
      cases c0 <;>
        simp [combineRows, xorVec, rowVector, mixedState, addState, deleteState,
          twoDeleteState, canonicalMint_twoDelete] at hcomb

theorem independent_added_mixedState' :
    IndependentGenerator (canonicalMint (deleteState twoDeleteState 1).used) mixedState := by
  show ¬ inSpanRows mixedState.Q
    (mixedState.rows.filter (fun r' => r'.sector = Sector.X ∧
      r'.id ≠ canonicalMint (deleteState twoDeleteState 1).used))
    (rowVector mixedState.Q ⟨canonicalMint (deleteState twoDeleteState 1).used, Sector.X, [0]⟩)
  intro hspan
  rcases hspan with ⟨coeffs, hlen, hcomb⟩
  cases coeffs with
  | nil => simp [mixedState, addState, deleteState, twoDeleteState, canonicalMint_twoDelete] at hlen
  | cons c0 tl =>
    cases tl with
    | cons _ _ =>
        cases hlen
    | nil =>
      cases c0 <;>
        simp [combineRows, xorVec, rowVector, mixedState, addState, deleteState,
          twoDeleteState, canonicalMint_twoDelete] at hcomb

theorem encodingWellFormed_mixedState : EncodingWellFormed mixedState := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro rX rZ hX hZ hsecX hsecZ
    simp [mixedState, addState, deleteState, twoDeleteState] at hZ
    rcases hZ with rfl | rfl <;> simp at hsecZ
  · intro r hr
    simp only [mixedState, addState, deleteState, twoDeleteState] at hr
    simp at hr
    rcases hr with rfl | rfl
    · exact independent_2_mixedState
    · exact independent_added_mixedState'

theorem wellFormedContext_mixedChain : WellFormedContext mixedChain := by
  intro s hs
  simp only [mixedChain, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact encodingWellFormed_twoDeleteState
  · exact encodingWellFormed_deleteState_1
  · exact encodingWellFormed_mixedState

theorem consecutiveDistinct_mixedChain : ConsecutiveDistinct mixedChain := by
  intro i s t hi hj
  rcases i with _ | _ | i
  · simp only [mixedChain] at hi hj
    cases hi; cases hj
    decide
  · simp only [mixedChain] at hi hj
    cases hi; cases hj
    decide
  · simp [mixedChain] at hj

/-- A measure under which the distance drops at the deletion and rises past
    its original value at the addition. -/
def measureUp : Field → CodeState → Nat := fun _ s => s.rows.length + s.used.length

/-- A measure under which the distance drops at the deletion and recovers only
    part of the way at the addition. -/
def measureDown : Field → CodeState → Nat := fun _ s => 2 * s.rows.length + (3 - s.used.length)

/-- The deletion's one-sided bound is derivable (for every measure). -/
theorem derives_mixed_delete_dX (dMeasure : Field → CodeState → Nat) :
    Derives dMeasure mixedChain (Ann.le (AExpr.atom ⟨1, Field.dX⟩) (AExpr.atom ⟨0, Field.dX⟩)) :=
  Derives.instDeleteDX 0 1 _ _ rfl rfl eval_delete_1_twoDeleteState

/-- The addition's one-sided bound is derivable (for every measure). -/
theorem derives_mixed_add_dX (dMeasure : Field → CodeState → Nat) :
    Derives dMeasure mixedChain (Ann.le (AExpr.atom ⟨1, Field.dX⟩) (AExpr.atom ⟨2, Field.dX⟩)) :=
  Derives.instAddDX 1 Sector.X [0] _ _ rfl rfl eval_add_mixedState

/-- `measureUp` satisfies the metatheorem's hypothesis on every deletion and
    addition, not only on the chain below. -/
theorem measureUp_monotone : MeasureMonotone measureUp where
  delete_le := fun r s t hstep => by
    rw [eval_delete_eq hstep]
    exact ⟨Nat.add_le_add_right (List.length_filter_le _ _) _,
      Nat.add_le_add_right (List.length_filter_le _ _) _⟩
  add_le := fun sector support s t hstep => by
    rw [eval_add_eq hstep]
    simp only [measureUp, addState, List.length_append, List.length_singleton]
    exact ⟨by omega, by omega⟩

/-- `measureDown` satisfies the hypothesis as well. -/
theorem measureDown_monotone : MeasureMonotone measureDown where
  delete_le := fun r s t hstep => by
    rw [eval_delete_eq hstep]
    exact ⟨Nat.add_le_add_right (Nat.mul_le_mul_left 2 (List.length_filter_le _ _)) _,
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 (List.length_filter_le _ _)) _⟩
  add_le := fun sector support s t hstep => by
    rw [eval_add_eq hstep]
    simp only [measureDown, addState, List.length_append, List.length_singleton]
    exact ⟨by omega, by omega⟩

/-- The composite bound `d_X(2) ≤ d_X(0)` has no derivation over the mixed
    chain under `measureUp`, although both one-sided bounds do. -/
theorem not_derivable_mixed_le :
    ¬ Derives measureUp mixedChain (Ann.le (AExpr.atom ⟨2, Field.dX⟩) (AExpr.atom ⟨0, Field.dX⟩)) :=
  not_derivable_of_false measureUp measureUp_monotone mixedChain wellFormedContext_mixedChain
    chain_mixed (by
    rintro ⟨v, w, hv, hw, hvw⟩
    have hv' : aexprValue measureUp mixedChain (AExpr.atom ⟨2, Field.dX⟩) = some 5 := by decide
    have hw' : aexprValue measureUp mixedChain (AExpr.atom ⟨0, Field.dX⟩) = some 4 := by decide
    rw [hv'] at hv
    rw [hw'] at hw
    cases hv
    cases hw
    omega)

/-- The composite bound `d_X(0) ≤ d_X(2)` has no derivation over the mixed
    chain under `measureDown`, although both one-sided bounds do. -/
theorem not_derivable_mixed_ge :
    ¬ Derives measureDown mixedChain (Ann.le (AExpr.atom ⟨0, Field.dX⟩) (AExpr.atom ⟨2, Field.dX⟩)) :=
  not_derivable_of_false measureDown measureDown_monotone mixedChain wellFormedContext_mixedChain
    chain_mixed (by
    rintro ⟨v, w, hv, hw, hvw⟩
    have hv' : aexprValue measureDown mixedChain (AExpr.atom ⟨0, Field.dX⟩) = some 5 := by decide
    have hw' : aexprValue measureDown mixedChain (AExpr.atom ⟨2, Field.dX⟩) = some 4 := by decide
    rw [hv'] at hv
    rw [hw'] at hw
    cases hv
    cases hw
    omega)

/-- The two-sided bound `d_X(2) = d_X(0)` has no derivation over the mixed
    chain for any choice of the measure. -/
theorem not_derivable_mixed_eq (dMeasure : Field → CodeState → Nat) :
    ¬ Derives dMeasure mixedChain (Ann.eq (AExpr.atom ⟨2, Field.dX⟩) (AExpr.atom ⟨0, Field.dX⟩)) :=
  not_derivable_distance_eq dMeasure consecutiveDistinct_mixedChain (Or.inl rfl) (by decide)

/-! ## The derivation-level `W13` half

`Ann.gen i r σ S` is the claim that refers to a generator: at position `i`
the identifier `r` names a displayed generator of sector `σ` with support
`S`. Its source is the addition that mints the generator (`Derives.genMint`),
and it transports through a step under which the generator survives
(`Derives.genSkip`, `Derives.genDelete` with `r ≠ r'`, `Derives.genAdd`),
which is the positive half's schema condition of §4.11 read on this claim.
The inventory has no row whose premise is the deletion of the referenced
generator, so across that step no derivation closes
(`not_derivable_gen_of_deleted`): the claim is not false of a row, it names
no row there. Both halves are instantiated on one parent: the minted
generator's claim transports across the deletion of another row
(`derives_gen_across_other_deletion`) and does not transport across its own
(`not_derivable_gen_across_own_deletion`). As everywhere in this module, the
refutation is relative to the `Derives` inventory. -/

/-- The deleted identifier names no displayed row of the deletion's output. -/
theorem not_mem_rows_deleteState (s : CodeState) (r : Nat) (σ : Sector) (S : List Nat) :
    ({ id := r, sector := σ, support := S } : Row) ∉ (deleteState s r).rows := by
  intro hmem
  have h := (List.mem_filter.mp hmem).2
  exact absurd rfl (of_decide_eq_true h)

/-- The `W13` half: a claim that refers to a generator is not derivable at
    the output of the step that deletes it, whatever sector and support it
    states. -/
theorem not_derivable_gen_of_deleted (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) {cs : List CodeState}
    (hctxt : WellFormedContext cs) (hchain : Chain cs) {i r : Nat} {s t : CodeState}
    (_hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
    (hstep : Eval (Command.delete r) s t) (σ : Sector) (S : List Nat) :
    ¬ Derives dMeasure cs (Ann.gen (i + 1) r σ S) := by
  apply not_derivable_of_false dMeasure hmono cs hctxt hchain
  rintro ⟨t', ht', hmem⟩
  have ht : t' = t := Option.some.inj (ht'.symm.trans hj)
  rw [ht, eval_delete_eq hstep] at hmem
  exact not_mem_rows_deleteState s r σ S hmem

/-- The identifier minted on the mixed chain's addition. -/
abbrev mintedId : Nat := canonicalMint (deleteState twoDeleteState 1).used

theorem displayed_2_mixedState : DisplayedGenerator 2 mixedState :=
  ⟨⟨2, Sector.X, [1]⟩,
    List.mem_append_left _ (by simp [deleteState, twoDeleteState]), rfl⟩

theorem displayed_minted_mixedState : DisplayedGenerator mintedId mixedState :=
  ⟨⟨mintedId, Sector.X, [0]⟩, List.mem_append_right _ (List.mem_singleton.mpr rfl), rfl⟩

theorem eval_delete_2_mixedState :
    Eval (Command.delete 2) mixedState (deleteState mixedState 2) :=
  Eval.delete displayed_2_mixedState independent_2_mixedState rfl

theorem eval_delete_minted_mixedState :
    Eval (Command.delete mintedId) mixedState (deleteState mixedState mintedId) :=
  Eval.delete displayed_minted_mixedState independent_added_mixedState' rfl

/-- Add a generator, then delete another one. -/
def survivingChain : List CodeState :=
  [deleteState twoDeleteState 1, mixedState, deleteState mixedState 2]

/-- Add a generator, then delete it. -/
def deletedChain : List CodeState :=
  [deleteState twoDeleteState 1, mixedState, deleteState mixedState mintedId]

theorem chain_surviving : Chain survivingChain :=
  Chain.cons eval_add_mixedState (Chain.cons eval_delete_2_mixedState (Chain.single _))

theorem chain_deleted : Chain deletedChain :=
  Chain.cons eval_add_mixedState (Chain.cons eval_delete_minted_mixedState (Chain.single _))

theorem wellFormedContext_deletedChain : WellFormedContext deletedChain := by
  intro s hs
  simp only [deletedChain, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact encodingWellFormed_deleteState_1
  · exact encodingWellFormed_mixedState
  · exact wf_of_eval (by trivial) eval_delete_minted_mixedState encodingWellFormed_mixedState

/-- Source: the minted generator's claim is derivable at the addition's
    output, on either chain. -/
theorem derives_gen_minted (dMeasure : Field → CodeState → Nat) (u : CodeState) :
    Derives dMeasure [deleteState twoDeleteState 1, mixedState, u]
      (Ann.gen 1 mintedId Sector.X [0]) :=
  Derives.genMint 0 Sector.X [0] _ _ rfl rfl eval_add_mixedState

/-- Positive half: the claim transports across the deletion of another
    generator. -/
theorem derives_gen_across_other_deletion (dMeasure : Field → CodeState → Nat) :
    Derives dMeasure survivingChain (Ann.gen 2 mintedId Sector.X [0]) :=
  Derives.genDelete 1 mintedId 2 Sector.X [0] _ _ rfl rfl eval_delete_2_mixedState
    (by rw [show mintedId = 0 from canonicalMint_twoDelete]; decide)
    (derives_gen_minted dMeasure _)

/-- `W13` half: the same claim, derivable before the step, has no derivation
    across the deletion of the generator it refers to. -/
theorem not_derivable_gen_across_own_deletion (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) (σ : Sector) (S : List Nat) :
    ¬ Derives dMeasure deletedChain (Ann.gen 2 mintedId σ S) :=
  not_derivable_gen_of_deleted dMeasure hmono wellFormedContext_deletedChain chain_deleted
    (i := 1) rfl rfl eval_delete_minted_mixedState σ S

/-! ## The input display and the graft

`Derives.genInput` sources the claim of a row the input state displays, so
the `W13` half also holds of a generator that was never minted in the term:
on `survivingChain` the input row `2` is claimed at position 0, transported
across the addition, and has no derivation after its deletion.

The graft retires the generators of its chain, shortens the opposite-sector
rows that contain the grafted qubit, keeps the other rows, and mints the
adjacent-product rows. `Derives.genGraft` and `Derives.genGraftMint` are the
rows for the surviving and the minted generators. No row covers a generator
of the chain, and `not_derivable_gen_of_grafted` is the refutation, by
soundness: the chain identifiers are displayed in the input, so they are in
`used`, while the minted identifiers are not, and every other output row
keeps an identifier outside the chain. All four cases are instantiated on
the graft of `graftableState`. -/

/-- A generator of the graft's chain names no displayed row of the graft's
    output. -/
theorem not_mem_rows_graftState_of_chain {s : CodeState} (hwf : EncodingWellFormed s)
    {q : Nat} {sector : Sector} {ids : List Nat}
    (hids : ∀ id ∈ ids, id ∈ (touchingRows s sector q).map Row.id) {r : Nat} (hr : r ∈ ids)
    (σ : Sector) (S : List Nat) :
    ({ id := r, sector := σ, support := S } : Row) ∉ (graftState s q sector ids).rows := by
  intro hmem
  rcases id_of_mem_graftState hmem with hout | hminted
  · exact hout hr
  · have hfresh : r ∉ s.used :=
      mintFresh_not_mem s.used _ r (id_mem_mintFresh_of_minted hminted)
    obtain ⟨row, hrow, hid⟩ := List.mem_map.mp (hids r hr)
    have hrow' : row ∈ s.rows := (List.mem_filter.mp hrow).1
    exact hfresh (hid ▸ ids_subset_used_of_wf hwf row hrow')

/-- The `W13` half for the graft: a claim that refers to a generator of the
    graft's chain is not derivable at the graft's output, whatever sector
    and support it states. -/
theorem not_derivable_gen_of_grafted (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) {cs : List CodeState}
    (hctxt : WellFormedContext cs) (hchain : Chain cs) {i q r : Nat} {sector : Sector}
    {ids : List Nat} {s t : CodeState}
    (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
    (hstep : Eval (Command.graft q sector ids) s t) (hr : r ∈ ids)
    (σ : Sector) (S : List Nat) :
    ¬ Derives dMeasure cs (Ann.gen (i + 1) r σ S) := by
  apply not_derivable_of_false dMeasure hmono cs hctxt hchain
  rintro ⟨t', ht', hmem⟩
  have ht : t' = t := Option.some.inj (ht'.symm.trans hj)
  rw [ht, eval_graft_eq hstep] at hmem
  have hwf : EncodingWellFormed s := hctxt s (mem_of_getElem? hi)
  cases hstep with
  | graft _ _ _ _ _ hids _ _ _ _ =>
      exact not_mem_rows_graftState_of_chain hwf hids hr σ S hmem

/-- Source for the input display: on `survivingChain` the input row `2` is
    claimed at position 0 and transported across the addition. -/
theorem derives_gen_input_across_addition (dMeasure : Field → CodeState → Nat)
    (u : CodeState) :
    Derives dMeasure [deleteState twoDeleteState 1, mixedState, u]
      (Ann.gen 1 2 Sector.X [1]) :=
  Derives.genAdd 0 2 Sector.X [1] Sector.X [0] _ _ rfl rfl eval_add_mixedState
    (Derives.genInput 2 Sector.X [1] _ rfl (by simp [deleteState, twoDeleteState]))

theorem wellFormedContext_survivingChain : WellFormedContext survivingChain := by
  intro s hs
  simp only [survivingChain, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact encodingWellFormed_deleteState_1
  · exact encodingWellFormed_mixedState
  · exact wf_of_eval (by trivial) eval_delete_2_mixedState encodingWellFormed_mixedState

/-- `W13` half for an input row: the same claim has no derivation across the
    deletion of the input generator it refers to. -/
theorem not_derivable_gen_input_across_own_deletion (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) (σ : Sector) (S : List Nat) :
    ¬ Derives dMeasure survivingChain (Ann.gen 2 2 σ S) :=
  not_derivable_gen_of_deleted dMeasure hmono wellFormedContext_survivingChain chain_surviving
    (i := 1) rfl rfl eval_delete_2_mixedState σ S

/-- The graft of `graftableState` at qubit `0` in the `X` sector along the
    chain `[1, 2]`. -/
def graftChainExample : List CodeState :=
  [graftableState, graftState graftableState 0 Sector.X [1, 2]]

theorem chain_graftChainExample : Chain graftChainExample :=
  Chain.cons eval_graft_graftable (Chain.single _)

theorem encodingWellFormed_graftableState : EncodingWellFormed graftableState :=
  (wellFormedBool_iff _).mp (by decide)

theorem wellFormedContext_graftChainExample : WellFormedContext graftChainExample := by
  intro s hs
  simp only [graftChainExample, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact encodingWellFormed_graftableState
  · exact wf_graft_of_eval eval_graft_graftable encodingWellFormed_graftableState

/-- The opposite-sector row `3` contains the grafted qubit and survives
    without it. -/
theorem derives_gen_graft_shortened (dMeasure : Field → CodeState → Nat) :
    Derives dMeasure graftChainExample (Ann.gen 1 3 Sector.Z [1, 2]) :=
  Derives.genGraft 0 3 Sector.Z [0, 1, 2] 0 Sector.X [1, 2] _ _ rfl rfl eval_graft_graftable
    (by decide) (Derives.genInput 3 Sector.Z [0, 1, 2] _ rfl (by simp [graftableState]))

/-- The opposite-sector row `4` does not contain the grafted qubit and
    survives unchanged. -/
theorem derives_gen_graft_kept (dMeasure : Field → CodeState → Nat) :
    Derives dMeasure graftChainExample (Ann.gen 1 4 Sector.Z [3, 4]) :=
  Derives.genGraft 0 4 Sector.Z [3, 4] 0 Sector.X [1, 2] _ _ rfl rfl eval_graft_graftable
    (by decide) (Derives.genInput 4 Sector.Z [3, 4] _ rfl (by simp [graftableState]))

/-- The minted adjacent-product row of the chain `[1, 2]`. -/
theorem derives_gen_graft_minted (dMeasure : Field → CodeState → Nat) :
    Derives dMeasure graftChainExample (Ann.gen 1 0 Sector.X [1, 2, 3, 4]) :=
  Derives.genGraftMint 0 0 Sector.X [1, 2] _ _ ⟨0, Sector.X, [1, 2, 3, 4]⟩ rfl rfl
    eval_graft_graftable (by
      rw [show graftMintedRows graftableState 0 Sector.X [1, 2] =
        [⟨0, Sector.X, [1, 2, 3, 4]⟩] from by decide]
      exact List.mem_singleton.mpr rfl)

/-- `W13` half for the graft: neither generator of the chain has a
    derivable claim at the graft's output. -/
theorem not_derivable_gen_graft_chain (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) (σ : Sector) (S : List Nat) :
    ¬ Derives dMeasure graftChainExample (Ann.gen 1 1 σ S) ∧
      ¬ Derives dMeasure graftChainExample (Ann.gen 1 2 σ S) :=
  ⟨not_derivable_gen_of_grafted dMeasure hmono wellFormedContext_graftChainExample
      chain_graftChainExample (i := 0) rfl rfl eval_graft_graftable (by decide) σ S,
    not_derivable_gen_of_grafted dMeasure hmono wellFormedContext_graftChainExample
      chain_graftChainExample (i := 0) rfl rfl eval_graft_graftable (by decide) σ S⟩


/-! ## `W13` halves for the Gate 6 commands -/

/-- A peeled row's identifier is not in the peel's output display. -/
theorem not_mem_rows_peelState_of_peeled {s : CodeState} {q r_id : Nat}
    {σ : Sector} {S : List Nat} :
    ({ id := r_id, sector := σ, support := S } : Row) ∉ (peelState s q r_id).rows := by
  intro hmem
  rcases List.mem_map.mp hmem with ⟨row, hrow, heq⟩
  have hsurv : row.id ≠ r_id := of_decide_eq_true (List.mem_filter.mp hrow).2
  have hid : (shortenRow q row).id = row.id := by
    unfold shortenRow; split <;> rfl
  have : row.id = r_id := hid.symm.trans (congrArg Row.id heq)
  exact hsurv this

/-- A row whose support contains the punctured qubit is not in the puncture's
    output display. -/
theorem not_mem_rows_punctureState_of_contains {s : CodeState} {q : Nat}
    {r : Nat} {σ : Sector} {S : List Nat} (hq : q ∈ S) :
    ({ id := r, sector := σ, support := S } : Row) ∉ (punctureState s q).rows := by
  intro hmem
  have hfilt := List.mem_filter.mp hmem
  have hnot : ¬ ({ id := r, sector := σ, support := S } : Row).support.contains q := of_decide_eq_true hfilt.2
  have heq : ({ id := r, sector := σ, support := S } : Row).support = S := rfl
  rw [heq] at hnot
  exact hnot (List.contains_iff_mem.mpr hq)

/-- A generator whose input row contains the punctured qubit `q` names no
    displayed row of the puncture's output, whatever sector and support are
    claimed (by I3 identifier injectivity in `EncodingWellFormed s`). -/
theorem not_mem_rows_punctureState_of_retired {s : CodeState}
    (hwf : EncodingWellFormed s) {q r : Nat}
    (hr : r ∈ (s.rows.filter (fun row => row.support.contains q)).map Row.id)
    (σ : Sector) (S : List Nat) :
    ({ id := r, sector := σ, support := S } : Row) ∉ (punctureState s q).rows := by
  intro hmem
  have hfilt := List.mem_filter.mp hmem
  have hnot : ¬ S.contains q := of_decide_eq_true hfilt.2
  rcases List.mem_map.mp hr with ⟨row0, hrow0, hid0⟩
  have hrow0' := List.mem_filter.mp hrow0
  have heq : ({ id := r, sector := σ, support := S } : Row) = row0 :=
    id_inj_of_nodup hwf.2.1 hfilt.1 hrow0'.1 hid0.symm
  have hS : S = row0.support := congrArg Row.support heq
  exact hnot (hS ▸ hrow0'.2)

/-- A row of the rebased sector (an old row, whose identifier is in
    `s.used`) is not in the rebase's output display. -/
theorem not_mem_rows_rebaseState_of_sector {s : CodeState} {sector : Sector}
    {matrix : List (List Nat)} {r : Nat} {σ : Sector} {S : List Nat}
    (hr : σ = sector) (hrused : r ∈ s.used) :
    ({ id := r, sector := σ, support := S } : Row) ∉ (rebaseState s sector matrix).rows := by
  intro hmem
  rcases List.mem_append.mp hmem with hleft | hright
  · have hfilt := List.mem_filter.mp hleft
    have hneq : ({ id := r, sector := σ, support := S } : Row).sector ≠ sector := of_decide_eq_true hfilt.2
    have hsec : ({ id := r, sector := σ, support := S } : Row).sector = sector := hr
    exact hneq hsec
  · rcases List.mem_map.mp hright with ⟨cs_id, hcs, heq⟩
    have hid : cs_id.2 = r :=
      congrArg Row.id heq
    have hfresh : cs_id.2 ∉ s.used := by
      have hmem' : cs_id.2 ∈ mintFresh s.used matrix.length :=
        (List.of_mem_zip hcs).2
      exact mintFresh_not_mem s.used matrix.length cs_id.2 hmem'
    exact hfresh (hid ▸ hrused)

/-- A generator of the rebased sector names no displayed row of the rebase's
    output, whatever sector and support are claimed: surviving rows come from
    the opposite sector (disjoint from `r` by I3 identifier injectivity), and
    minted rows carry fresh identifiers outside `s.used`. -/
theorem not_mem_rows_rebaseState_of_retired {s : CodeState}
    (hwf : EncodingWellFormed s) {sector : Sector} {matrix : List (List Nat)}
    {r : Nat}
    (hr : r ∈ (s.rows.filter (fun row => row.sector = sector)).map Row.id)
    (σ : Sector) (S : List Nat) :
    ({ id := r, sector := σ, support := S } : Row) ∉ (rebaseState s sector matrix).rows := by
  intro hmem
  rcases List.mem_map.mp hr with ⟨row0, hrow0, hid0⟩
  have hrow0' := List.mem_filter.mp hrow0
  rcases List.mem_append.mp hmem with hleft | hright
  · have hfilt := List.mem_filter.mp hleft
    have hneq : σ ≠ sector := of_decide_eq_true hfilt.2
    have heq : ({ id := r, sector := σ, support := S } : Row) = row0 :=
      id_inj_of_nodup hwf.2.1 hfilt.1 hrow0'.1 hid0.symm
    have hσ : σ = sector :=
      (congrArg Row.sector heq).trans (of_decide_eq_true hrow0'.2)
    exact hneq hσ
  · rcases List.mem_map.mp hright with ⟨cs_id, hcs, heq⟩
    have hid : cs_id.2 = r := congrArg Row.id heq
    have hfresh : cs_id.2 ∉ s.used :=
      mintFresh_not_mem s.used matrix.length cs_id.2 (List.of_mem_zip hcs).2
    have hrused : r ∈ s.used := hid0 ▸ ids_subset_used_of_wf hwf row0 hrow0'.1
    exact hfresh (hid ▸ hrused)

/-- The `W13` half for the peel: a claim that refers to the peeled row's
    identifier is not derivable at the peel's output, whatever sector and
    support it states. -/
theorem not_derivable_gen_of_peeled {τ : Sector} (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) {cs : List CodeState}
    (hctxt : WellFormedContext cs) (hchain : Chain cs) {i q r_id : Nat}
    {s t : CodeState} {σ : Sector} {S : List Nat}
    (_hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
    (hstep : Eval (Command.peel q τ r_id) s t) :
    ¬ Derives dMeasure cs (Ann.gen (i + 1) r_id σ S) := by
  apply not_derivable_of_false dMeasure hmono cs hctxt hchain
  rintro ⟨t', ht', hmem⟩
  have ht : t' = t := Option.some.inj (ht'.symm.trans hj)
  rw [ht, eval_peel_eq hstep] at hmem
  exact not_mem_rows_peelState_of_peeled (σ := σ) (S := S) hmem

/-- The `W13` half for the puncture (support form): a claim whose support
    contains the punctured qubit is not derivable at the puncture's output. -/
theorem not_derivable_gen_of_punctured (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) {cs : List CodeState}
    (hctxt : WellFormedContext cs) (hchain : Chain cs) {i q : Nat}
    {s t : CodeState} {r : Nat} {σ : Sector} {S : List Nat}
    (_hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
    (hstep : Eval (Command.puncture q) s t) (hq : q ∈ S) :
    ¬ Derives dMeasure cs (Ann.gen (i + 1) r σ S) := by
  apply not_derivable_of_false dMeasure hmono cs hctxt hchain
  rintro ⟨t', ht', hmem⟩
  have ht : t' = t := Option.some.inj (ht'.symm.trans hj)
  rw [ht, eval_puncture_eq hstep] at hmem
  exact not_mem_rows_punctureState_of_contains hq hmem

/-- The `W13` half for the puncture (identifier form): a generator
    whose input row contains the punctured qubit has no derivable claim at the
    puncture's output, whatever sector and support it states (even when
    `q ∉ S`). -/
theorem not_derivable_gen_of_punctured_id (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) {cs : List CodeState}
    (hctxt : WellFormedContext cs) (hchain : Chain cs) {i q : Nat}
    {s t : CodeState} {r : Nat} {σ : Sector} {S : List Nat}
    (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
    (hstep : Eval (Command.puncture q) s t)
    (hr : r ∈ (s.rows.filter (fun row => row.support.contains q)).map Row.id) :
    ¬ Derives dMeasure cs (Ann.gen (i + 1) r σ S) := by
  apply not_derivable_of_false dMeasure hmono cs hctxt hchain
  rintro ⟨t', ht', hmem⟩
  have ht : t' = t := Option.some.inj (ht'.symm.trans hj)
  rw [ht, eval_puncture_eq hstep] at hmem
  have hwf : EncodingWellFormed s := hctxt s (mem_of_getElem? hi)
  exact not_mem_rows_punctureState_of_retired hwf hr σ S hmem

/-- The `W13` half for the rebase: a generator of the rebased sector has no
    derivable claim at the rebase's output, whatever sector and support it
    states. -/
theorem not_derivable_gen_of_rebased (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) {cs : List CodeState}
    (hctxt : WellFormedContext cs) (hchain : Chain cs) {i : Nat}
    {sector : Sector} {matrix : List (List Nat)} {s t : CodeState}
    {r : Nat} {σ : Sector} {S : List Nat}
    (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
    (hstep : Eval (Command.rebase sector matrix) s t)
    (hr : r ∈ (s.rows.filter (fun row => row.sector = sector)).map Row.id) :
    ¬ Derives dMeasure cs (Ann.gen (i + 1) r σ S) := by
  apply not_derivable_of_false dMeasure hmono cs hctxt hchain
  rintro ⟨t', ht', hmem⟩
  have ht : t' = t := Option.some.inj (ht'.symm.trans hj)
  rw [ht, eval_rebase_eq hstep] at hmem
  have hwf : EncodingWellFormed s := hctxt s (mem_of_getElem? hi)
  exact not_mem_rows_rebaseState_of_retired hwf hr σ S hmem

/-! ### Worked instances for the five Gate 6 commands

Each Gate 6 command is instantiated on `graftableState`, exercising every
transport row (`genExtend`, `genPeel`, `genPuncture`, `genHadamard`,
`genRebase`), every minting source (`genExtendMint`, `genRebaseMint`), and
every refusal (`not_derivable_gen_of_peeled`, `not_derivable_gen_of_punctured`,
`not_derivable_gen_of_punctured_id`, `not_derivable_gen_of_rebased`). -/

/-- `E-EXTEND` on `graftableState`: add qubit `5` and one `X`-row on `[5]`. -/
theorem eval_extend_graftable :
    Eval (Command.extend [5] [(Sector.X, [5])]) graftableState
      (extendState graftableState [5] [(Sector.X, [5])]) := by
  apply Eval.extend
  · refine ⟨by decide, by decide, ?_, trivial⟩
    intro rec hrec
    have hEq : rec = (Sector.X, [5]) := List.mem_singleton.mp hrec
    subst hEq
    exact ⟨by decide, by decide, by decide, fun q hq => by
      rw [List.mem_singleton.mp hq]; decide⟩
  · rfl
  · exact (wellFormedBool_iff _).mp (by decide)
  · decide

def extendChainExample : List CodeState :=
  [graftableState, extendState graftableState [5] [(Sector.X, [5])]]

/-- Pre-existing row `1` survives `E-EXTEND` unchanged. -/
theorem derives_gen_extend_kept (dMeasure : Field → CodeState → Nat) :
    Derives dMeasure extendChainExample (Ann.gen 1 1 Sector.X [0, 1]) :=
  Derives.genExtend 0 1 Sector.X [0, 1] [5] [(Sector.X, [5])] _ _ rfl rfl
    eval_extend_graftable
    (Derives.genInput 1 Sector.X [0, 1] _ rfl (by simp [graftableState]))

/-- The newly minted row `0` (`X`, `[5]`) is sourced by `Derives.genExtendMint`. -/
theorem derives_gen_extend_minted (dMeasure : Field → CodeState → Nat) :
    Derives dMeasure extendChainExample (Ann.gen 1 0 Sector.X [5]) :=
  Derives.genExtendMint 0 [5] [(Sector.X, [5])] _ _ ⟨0, Sector.X, [5]⟩ rfl rfl
    eval_extend_graftable (by
      rw [show extendMintedRows graftableState [(Sector.X, [5])] =
        [⟨0, Sector.X, [5]⟩] from by decide]
      exact List.mem_singleton.mpr rfl)

/-- `E-PEEL` on `graftableState`: peel qubit `1` in sector `X` along the
    unique touching `X`-row `1`. -/
theorem eval_peel_graftable :
    Eval (Command.peel 1 Sector.X 1) graftableState (peelState graftableState 1 1) := by
  apply Eval.peel
  · decide
  · exact ⟨⟨1, Sector.X, [0, 1]⟩, List.mem_cons_self, rfl, rfl, by decide⟩
  · decide
  · decide
  · rfl
  · exact (wellFormedBool_iff _).mp (by decide)

def peelChainExample : List CodeState :=
  [graftableState, peelState graftableState 1 1]

theorem chain_peelChainExample : Chain peelChainExample :=
  Chain.cons eval_peel_graftable (Chain.single _)

theorem wellFormedContext_peelChainExample : WellFormedContext peelChainExample :=
  chain_peelChainExample.wellFormedContext (fun s hs => by
    have hs' : graftableState = s := Option.some.inj hs
    exact hs' ▸ encodingWellFormed_graftableState)

/-- Opposite-sector row `3` contains the peeled qubit `1` and survives
    shortened to `[0, 2]`. -/
theorem derives_gen_peel_shortened (dMeasure : Field → CodeState → Nat) :
    Derives dMeasure peelChainExample (Ann.gen 1 3 Sector.Z [0, 2]) :=
  Derives.genPeel 0 3 1 Sector.Z [0, 1, 2] 1 Sector.X _ _ rfl rfl eval_peel_graftable
    (by decide)
    (Derives.genInput 3 Sector.Z [0, 1, 2] _ rfl (by simp [graftableState]))

/-- Same-sector row `2` avoids the peeled qubit and survives unchanged. -/
theorem derives_gen_peel_kept (dMeasure : Field → CodeState → Nat) :
    Derives dMeasure peelChainExample (Ann.gen 1 2 Sector.X [0, 2, 3, 4]) :=
  Derives.genPeel 0 2 1 Sector.X [0, 2, 3, 4] 1 Sector.X _ _ rfl rfl eval_peel_graftable
    (by decide)
    (Derives.genInput 2 Sector.X [0, 2, 3, 4] _ rfl (by simp [graftableState]))

/-- `W13` half for the peel: the peeled row `1` has no derivable claim at the
    output, whatever sector and support are stated. -/
theorem not_derivable_gen_peel_retired (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) (σ : Sector) (S : List Nat) :
    ¬ Derives dMeasure peelChainExample (Ann.gen 1 1 σ S) :=
  not_derivable_gen_of_peeled dMeasure hmono wellFormedContext_peelChainExample
    chain_peelChainExample (i := 0) rfl rfl eval_peel_graftable

/-- `E-PUNCTURE` on `graftableState`: puncture qubit `1`, deleting rows `1`
    and `3` and keeping `2` and `4`. -/
theorem eval_puncture_graftable :
    Eval (Command.puncture 1) graftableState (punctureState graftableState 1) := by
  apply Eval.puncture
  · decide
  · rfl
  · exact (wellFormedBool_iff _).mp (by decide)

def punctureChainExample : List CodeState :=
  [graftableState, punctureState graftableState 1]

theorem chain_punctureChainExample : Chain punctureChainExample :=
  Chain.cons eval_puncture_graftable (Chain.single _)

theorem wellFormedContext_punctureChainExample : WellFormedContext punctureChainExample :=
  chain_punctureChainExample.wellFormedContext (fun s hs => by
    have hs' : graftableState = s := Option.some.inj hs
    exact hs' ▸ encodingWellFormed_graftableState)

/-- Row `2` avoids the punctured qubit `1` and survives unchanged. -/
theorem derives_gen_puncture_kept (dMeasure : Field → CodeState → Nat) :
    Derives dMeasure punctureChainExample (Ann.gen 1 2 Sector.X [0, 2, 3, 4]) :=
  Derives.genPuncture 0 2 Sector.X [0, 2, 3, 4] 1 _ _ rfl rfl eval_puncture_graftable
    (by decide)
    (Derives.genInput 2 Sector.X [0, 2, 3, 4] _ rfl (by simp [graftableState]))

/-- `W13` half for the puncture: the retired row `1` (which contained qubit
    `1`) has no derivable claim for any sector and support (including `[0]`,
    where `1 ∉ [0]`), and no claim whose support contains `1` is derivable. -/
theorem not_derivable_gen_puncture_retired (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) (σ : Sector) (S : List Nat) :
    ¬ Derives dMeasure punctureChainExample (Ann.gen 1 1 σ S) ∧
      ¬ Derives dMeasure punctureChainExample (Ann.gen 1 3 σ S) ∧
      (∀ r, ¬ Derives dMeasure punctureChainExample (Ann.gen 1 r σ [0, 1])) :=
  ⟨not_derivable_gen_of_punctured_id dMeasure hmono wellFormedContext_punctureChainExample
      chain_punctureChainExample (i := 0) rfl rfl eval_puncture_graftable (by decide),
    not_derivable_gen_of_punctured_id dMeasure hmono wellFormedContext_punctureChainExample
      chain_punctureChainExample (i := 0) rfl rfl eval_puncture_graftable (by decide),
    fun _ => not_derivable_gen_of_punctured dMeasure hmono wellFormedContext_punctureChainExample
      chain_punctureChainExample (i := 0) rfl rfl eval_puncture_graftable (by decide)⟩

/-- `E-LOCAL-HADAMARD` on `graftableState` with `T = Q` swaps every sector. -/
theorem eval_hadamard_graftable :
    Eval (Command.hadamard [0, 1, 2, 3, 4]) graftableState
      (hadamardState graftableState [0, 1, 2, 3, 4]) := by
  apply Eval.hadamard
  · exact Or.inl (List.Perm.refl _)
  · rfl
  · exact (wellFormedBool_iff _).mp (by decide)

/-- `E-LOCAL-HADAMARD` on `graftableState` with `T = []` is the identity. -/
theorem eval_hadamard_empty_graftable :
    Eval (Command.hadamard []) graftableState (hadamardState graftableState []) := by
  apply Eval.hadamard
  · exact Or.inr rfl
  · rfl
  · exact encodingWellFormed_graftableState

/-- Under `E-LOCAL-HADAMARD` (`T = Q`), row `1` keeps its id and support and
    swaps sector from `X` to `Z`. -/
theorem derives_gen_hadamard_swapped (dMeasure : Field → CodeState → Nat) :
    Derives dMeasure [graftableState, hadamardState graftableState [0, 1, 2, 3, 4]]
      (Ann.gen 1 1 Sector.Z [0, 1]) :=
  Derives.genHadamard 0 1 Sector.X [0, 1] [0, 1, 2, 3, 4] _ _ rfl rfl eval_hadamard_graftable
    (Or.inl (List.Perm.refl _))
    (Derives.genInput 1 Sector.X [0, 1] _ rfl (by simp [graftableState]))

/-- Under `E-LOCAL-HADAMARD` (`T = []`), row `1` keeps its id, sector, and
    support unchanged. -/
theorem derives_gen_hadamard_empty (dMeasure : Field → CodeState → Nat) :
    Derives dMeasure [graftableState, hadamardState graftableState []]
      (Ann.gen 1 1 Sector.X [0, 1]) :=
  Derives.genHadamard 0 1 Sector.X [0, 1] [] _ _ rfl rfl eval_hadamard_empty_graftable
    (Or.inr rfl)
    (Derives.genInput 1 Sector.X [0, 1] _ rfl (by simp [graftableState]))

/-- `P-REBASE` on `graftableState` in sector `X` with shear `[[1, 1], [0, 1]]`:
    retires rows `1` and `2`, keeps `Z`-rows `3` and `4`, and mints `0`
    (`[1, 2, 3, 4]`) and `5` (`[0, 2, 3, 4]`). -/
theorem eval_rebase_graftable :
    Eval (Command.rebase Sector.X [[1, 1], [0, 1]]) graftableState
      (rebaseState graftableState Sector.X [[1, 1], [0, 1]]) := by
  apply Eval.rebase
  · decide
  · exact ⟨by decide, by decide, by decide⟩
  · rfl
  · exact (wellFormedBool_iff _).mp (by decide)
  · decide

def rebaseChainExample : List CodeState :=
  [graftableState, rebaseState graftableState Sector.X [[1, 1], [0, 1]]]

theorem chain_rebaseChainExample : Chain rebaseChainExample :=
  Chain.cons eval_rebase_graftable (Chain.single _)

theorem wellFormedContext_rebaseChainExample : WellFormedContext rebaseChainExample :=
  chain_rebaseChainExample.wellFormedContext (fun s hs => by
    have hs' : graftableState = s := Option.some.inj hs
    exact hs' ▸ encodingWellFormed_graftableState)

/-- Opposite-sector row `3` survives `P-REBASE` unchanged. -/
theorem derives_gen_rebase_kept (dMeasure : Field → CodeState → Nat) :
    Derives dMeasure rebaseChainExample (Ann.gen 1 3 Sector.Z [0, 1, 2]) :=
  Derives.genRebase 0 3 Sector.Z [0, 1, 2] Sector.X [[1, 1], [0, 1]] _ _ rfl rfl
    eval_rebase_graftable (by decide)
    (Derives.genInput 3 Sector.Z [0, 1, 2] _ rfl (by simp [graftableState]))

/-- Minted row `0` (`X`, `[1, 2, 3, 4]`) is sourced by `Derives.genRebaseMint`. -/
theorem derives_gen_rebase_minted (dMeasure : Field → CodeState → Nat) :
    Derives dMeasure rebaseChainExample (Ann.gen 1 0 Sector.X [1, 2, 3, 4]) :=
  Derives.genRebaseMint 0 Sector.X [[1, 1], [0, 1]] _ _ ⟨0, Sector.X, [1, 2, 3, 4]⟩ rfl rfl
    eval_rebase_graftable (by
      rw [show rebaseMintedRows graftableState Sector.X [[1, 1], [0, 1]] =
        [⟨0, Sector.X, [1, 2, 3, 4]⟩, ⟨5, Sector.X, [0, 2, 3, 4]⟩] from by decide]
      exact List.mem_cons_self)

/-- `W13` half for the rebase: neither retired `X`-row (`1` or `2`) has a
    derivable claim at the rebase's output, whatever sector and support are
    stated. -/
theorem not_derivable_gen_rebase_retired (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) (σ : Sector) (S : List Nat) :
    ¬ Derives dMeasure rebaseChainExample (Ann.gen 1 1 σ S) ∧
      ¬ Derives dMeasure rebaseChainExample (Ann.gen 1 2 σ S) :=
  ⟨not_derivable_gen_of_rebased dMeasure hmono wellFormedContext_rebaseChainExample
      chain_rebaseChainExample (i := 0) rfl rfl eval_rebase_graftable (by decide),
    not_derivable_gen_of_rebased dMeasure hmono wellFormedContext_rebaseChainExample
      chain_rebaseChainExample (i := 0) rfl rfl eval_rebase_graftable (by decide)⟩

/-! ## `W13` half for `E-SPLIT` (admitted 2026-11-25) -/

/-- A cut row's identifier is not in the split's output display. -/
theorem not_mem_rows_deleteAll_of_mem {s : CodeState} {R : List Nat}
    {r : Nat} {σ : Sector} {S : List Nat} (hr : r ∈ R) :
    ({ id := r, sector := σ, support := S } : Row) ∉ (deleteAll s R).rows := by
  intro hmem
  exact ((mem_deleteAll_rows R s _).mp hmem).2 hr

/-- The `W13` half for `E-SPLIT`: a claim that refers to any deleted cut-row
    identifier `r ∈ R` is not derivable at the split's output, whatever sector
    and support it states (`spec/JUDGMENT_LAYER.md` §4). -/
theorem not_derivable_gen_of_split (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) {cs : List CodeState}
    (hctxt : WellFormedContext cs) (hchain : Chain cs)
    {i r : Nat} {QA R : List Nat} {s t : CodeState} {σ : Sector} {S : List Nat}
    (_hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
    (hstep : Eval (Command.split QA R) s t) (hr : r ∈ R) :
    ¬ Derives dMeasure cs (Ann.gen (i + 1) r σ S) := by
  apply not_derivable_of_false dMeasure hmono cs hctxt hchain
  rintro ⟨t', ht', hmem⟩
  have ht : t' = t := Option.some.inj (ht'.symm.trans hj)
  rw [ht, eval_split_eq hstep] at hmem
  exact not_mem_rows_deleteAll_of_mem hr hmem

/-- Worked `E-SPLIT` instance on `graftableState`: split `QA = [0, 1, 2]` vs
    `Q_B = [3, 4]` by deleting the unique crossing row `2` (`X [0, 2, 3, 4]`). -/
theorem eval_split_graftable :
    Eval (Command.split [0, 1, 2] [2]) graftableState
      (deleteAll graftableState [2]) := by
  apply Eval.split
  · decide
  · intro q hq; simp [graftableState] at hq ⊢; omega
  · decide
  · intro r hr
    have hEq : r = 2 := List.mem_singleton.mp hr
    subst hEq
    exact ⟨⟨2, Sector.X, [0, 2, 3, 4]⟩, by simp [graftableState], rfl⟩
  · intro row hrow
    simp only [graftableState, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl
    · left; decide
    · right; right; decide
    · left; decide
    · right; left; decide
  · rfl

def splitChainExample : List CodeState :=
  [graftableState, deleteAll graftableState [2]]

theorem chain_splitChainExample : Chain splitChainExample :=
  Chain.cons eval_split_graftable (Chain.single _)

theorem wellFormedContext_splitChainExample : WellFormedContext splitChainExample :=
  chain_splitChainExample.wellFormedContext (fun s hs => by
    have hs' : graftableState = s := Option.some.inj hs
    exact hs' ▸ encodingWellFormed_graftableState)

/-- Non-cut row `1` survives `E-SPLIT` unchanged. -/
theorem derives_gen_split_kept (dMeasure : Field → CodeState → Nat) :
    Derives dMeasure splitChainExample (Ann.gen 1 1 Sector.X [0, 1]) :=
  Derives.genSplit 0 1 Sector.X [0, 1] [0, 1, 2] [2] _ _ rfl rfl eval_split_graftable
    (by decide) (Derives.genInput 1 Sector.X [0, 1] _ rfl (by simp [graftableState]))

/-- `W13` half for `E-SPLIT` on the worked instance: the deleted cut row `2`
    has no derivable claim at the split's output, whatever sector and support
    are stated. -/
theorem not_derivable_gen_split_retired (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) (σ : Sector) (S : List Nat) :
    ¬ Derives dMeasure splitChainExample (Ann.gen 1 2 σ S) :=
  not_derivable_gen_of_split dMeasure hmono wellFormedContext_splitChainExample
    chain_splitChainExample (i := 0) rfl rfl eval_split_graftable (by decide)

end CodeCalculus
