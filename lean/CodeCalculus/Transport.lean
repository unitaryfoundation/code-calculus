import CodeCalculus.Soundness

namespace CodeCalculus

/-!
# Judgment transport through sequences (`OBL-JUDGMENT-TRANSPORT`)

Mechanized form of the transport half of `spec/OPERATIONAL_SEMANTICS.md` §4.11
("structural judgments compose through valid sequences; a claim that refers to
a deleted generator is not transported automatically"), on the `Chain`,
`Derives`, and `Models` machinery of `Soundness.lean`, together with the
fixed-reference-set invalidation model of §4.15 (review finding disposition) on
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
   (`Derives.shift`). The schema-composition condition of §4.11 is, in this
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

What the slice does not do. The sentence language `Ann` has no claim that
refers to a generator, so the derivation-level `W13` half ("a claim referring
to a deleted generator does not transport") has no instance here beyond its
shape: nothing in `Ann` can mention a generator, deleted or not. Adding such
claims is an assertion-language extension and a release question
(`the design notes` §4, Reading II), not this slice's. The
fixed-reference-set model is mechanized abstractly, over an arbitrary
certificate type, because the context-update table that would fix `Ref` for
concrete certificates is future context (R7 disposition at
`OBL-ORDER-INDEPENDENT-DELETION`), and it is not connected to `Eval`, since
`spec/` does not specify what a non-deletion command does to a context. Every
refutation here is relative to the `Derives` inventory of this development: it
says that no derivation closes, not that none can (F7 disposition, second
cost).
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

/-- Positive half, second segment: a derivation over a chain is a derivation
    over any chain that has it as a suffix, with every position shifted past
    the prefix. -/
theorem Derives.shift {dMeasure : Field → CodeState → Nat} (cs : List CodeState)
    {ds : List CodeState} {a : Ann} (h : Derives dMeasure ds a) :
    Derives dMeasure (cs ++ ds) (a.shift cs.length) := by
  induction h with
  | instSkip i f s t hi hj hstep =>
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instSkip (i + cs.length) f s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instDeleteN i r s t hi hj hstep =>
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instDeleteN (i + cs.length) r s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instAddN i sector support s t hi hj hstep =>
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instAddN (i + cs.length) sector support s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instGraftN i q sector ids s t hi hj hstep =>
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instGraftN (i + cs.length) q sector ids s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instDeleteK i r s t hi hj hstep =>
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instDeleteK (i + cs.length) r s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instDeleteKSub i r s t hi hj hstep =>
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instDeleteKSub (i + cs.length) r s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instAddK i sector support s t hi hj hstep =>
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instAddK (i + cs.length) sector support s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instAddKSub i sector support s t hi hj hstep =>
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instAddKSub (i + cs.length) sector support s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instGraftK i q sector ids s t hi hj hstep =>
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instGraftK (i + cs.length) q sector ids s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instSkipWF i s t hi hj hstep =>
      simp only [Ann.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instSkipWF (i + cs.length) s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instDeleteWF i r s t hi hj hstep =>
      simp only [Ann.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instDeleteWF (i + cs.length) r s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instAddWF i sector support s t hi hj hstep =>
      simp only [Ann.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instAddWF (i + cs.length) sector support s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instGraftWF i q sector ids s t hi hj hstep =>
      simp only [Ann.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instGraftWF (i + cs.length) q sector ids s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instDeleteDX i r s t hi hj hstep =>
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instDeleteDX (i + cs.length) r s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instDeleteDZ i r s t hi hj hstep =>
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instDeleteDZ (i + cs.length) r s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instDeleteD i r s t hi hj hstep =>
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instDeleteD (i + cs.length) r s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instAddDX i sector support s t hi hj hstep =>
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instAddDX (i + cs.length) sector support s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instAddDZ i sector support s t hi hj hstep =>
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instAddDZ (i + cs.length) sector support s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instAddD i sector support s t hi hj hstep =>
      simp only [Ann.shift, AExpr.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact Derives.instAddD (i + cs.length) sector support s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | transit_le_le x y z _ _ ih1 ih2 =>
      simp only [Ann.shift] at ih1 ih2 ⊢
      exact Derives.transit_le_le _ _ _ ih1 ih2
  | transit_le_eq x y z _ _ ih1 ih2 =>
      simp only [Ann.shift] at ih1 ih2 ⊢
      exact Derives.transit_le_eq _ _ _ ih1 ih2
  | transit_eq_le x y z _ _ ih1 ih2 =>
      simp only [Ann.shift] at ih1 ih2 ⊢
      exact Derives.transit_eq_le _ _ _ ih1 ih2
  | transit_eq_eq x y z _ _ ih1 ih2 =>
      simp only [Ann.shift] at ih1 ih2 ⊢
      exact Derives.transit_eq_eq _ _ _ ih1 ih2
  | min_le_left x y hx =>
      simp only [Ann.shift, AExpr.shift]
      exact Derives.min_le_left _ _ (denotes_shift.mpr hx)
  | min_le_right x y hy =>
      simp only [Ann.shift, AExpr.shift]
      exact Derives.min_le_right _ _ (denotes_shift.mpr hy)
  | le_min t x y _ _ ih1 ih2 =>
      simp only [Ann.shift, AExpr.shift] at ih1 ih2 ⊢
      exact Derives.le_min _ _ _ ih1 ih2
  | le_refl x hx =>
      simp only [Ann.shift]
      exact Derives.le_refl _ (denotes_shift.mpr hx)
  | eq_refl x hx =>
      simp only [Ann.shift]
      exact Derives.eq_refl _ (denotes_shift.mpr hx)
  | eq_sym x y _ ih =>
      simp only [Ann.shift] at ih ⊢
      exact Derives.eq_sym _ _ ih

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
    {ds : List CodeState} {s : CodeState} {b : Ann} (h : Derives dMeasure (s :: ds) b) :
    Derives dMeasure (cs ++ s :: ds) (b.shift cs.length) :=
  h.shift cs

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

/-! ## The fixed-reference-set model (§4.15, R7 disposition) -/

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
    | cons _ _ => simp [sectorRows, deleteState, twoDeleteState] at hlen
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
        simp [mixedState, addState, deleteState, twoDeleteState, canonicalMint_twoDelete] at hlen
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
        simp [mixedState, addState, deleteState, twoDeleteState, canonicalMint_twoDelete] at hlen
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
    omega

/-- `measureDown` satisfies the hypothesis as well. -/
theorem measureDown_monotone : MeasureMonotone measureDown where
  delete_le := fun r s t hstep => by
    rw [eval_delete_eq hstep]
    exact ⟨Nat.add_le_add_right (Nat.mul_le_mul_left 2 (List.length_filter_le _ _)) _,
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 (List.length_filter_le _ _)) _⟩
  add_le := fun sector support s t hstep => by
    rw [eval_add_eq hstep]
    simp only [measureDown, addState, List.length_append, List.length_singleton]
    omega

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

end CodeCalculus
