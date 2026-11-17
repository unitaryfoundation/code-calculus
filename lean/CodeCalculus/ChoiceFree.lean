namespace CodeCalculus

/-! ### Choice-free restatements of library facts

Several core-library lemmas the development cited are proved, in Lean core,
by arguments whose axiom footprint includes `Classical.choice`
(`#print axioms` reports it on the pinned toolchain): `List.filter_eq_nil_iff`,
`List.length_erase_of_mem`, `List.Nodup.erase_eq_filter`,
`List.Nodup.mem_erase_iff`, `List.perm_ext_iff_of_nodup`,
`Nat.testBit_two_pow_sub_one`, `Nat.testBit_log2`, `Nat.log2_two_pow`, and the
simp lemmas `Nat.right_eq_add` and `Nat.add_eq_right` that `simp` reaches for
on a length mismatch such as `0 = l.length + 1`. This module restates the
facts the development needs with proofs that stay inside `propext` and
`Quot.sound`, so that `Classical.choice` enters the development only through
the noncomputable denotation (`denoteExpr` and `denote` in `Eval.lean`);
`AxiomAudit.lean` checks that confinement at build time. -/

/-- A filter whose predicate fails on every element is empty
    (`List.filter_eq_nil_iff`, forward direction). -/
theorem filter_eq_nil_of_forall_not {α : Type} {p : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, ¬ p a = true) → l.filter p = []
  | [], _ => rfl
  | a :: l, h => by
      rw [List.filter_cons_of_neg (h a (List.mem_cons_self ..))]
      exact filter_eq_nil_of_forall_not (fun b hb => h b (List.mem_cons_of_mem a hb))

/-- Filtering with the constant `false` predicate yields the empty list. -/
theorem filter_const_false {α : Type} (l : List α) : l.filter (fun _ => false) = [] :=
  filter_eq_nil_of_forall_not (fun _ _ h => Bool.false_ne_true h)

/-- Removing one member of a duplicate-free list by filtering drops exactly one
    entry (`List.length_erase_of_mem` for `erase` written as a filter). -/
theorem length_filter_ne_of_nodup_mem {α : Type} [DecidableEq α] {a : α} :
    ∀ {l : List α}, l.Nodup → a ∈ l → (l.filter (fun x => x ≠ a)).length = l.length - 1
  | [], _, h => absurd h List.not_mem_nil
  | x :: l, hnd, h => by
      rcases List.nodup_cons.mp hnd with ⟨hx, hl⟩
      by_cases hxa : x = a
      · subst hxa
        rw [List.filter_cons_of_neg (fun ht => (of_decide_eq_true ht) rfl), List.length_cons,
          Nat.add_sub_cancel, List.filter_eq_self.mpr]
        intro y hy
        exact decide_eq_true (fun hyx => hx (hyx ▸ hy))
      · have ha : a ∈ l := List.mem_of_ne_of_mem (fun hax => hxa hax.symm) h
        rw [List.filter_cons_of_pos (p := fun y => decide (y ≠ a)) (decide_eq_true hxa),
          List.length_cons, List.length_cons,
          length_filter_ne_of_nodup_mem hl ha]
        have : 0 < l.length := List.length_pos_of_mem ha
        omega

/-- A list of witnesses for a bounded family of existentials, extracted by
    recursion on the bound rather than by `Classical.choose`. -/
theorem exists_list_getD {α : Type} (d₀ : α) {P : Nat → α → Prop} :
    ∀ m : Nat, (∀ i, i < m → ∃ a, P i a) →
      ∃ l : List α, l.length = m ∧ ∀ i, i < m → P i (l.getD i d₀)
  | 0, _ => ⟨[], rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | m + 1, h => by
      obtain ⟨l, hlen, hl⟩ := exists_list_getD d₀ m (fun i hi => h i (Nat.lt_succ_of_lt hi))
      obtain ⟨a, ha⟩ := h m (Nat.lt_succ_self m)
      refine ⟨l ++ [a], by rw [List.length_append, hlen]; rfl, ?_⟩
      intro i hi
      rcases Nat.lt_or_ge i m with hlt | hge
      · have hget : (l ++ [a]).getD i d₀ = l.getD i d₀ := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hlen]; exact hlt),
            List.getD_eq_getElem?_getD]
        rw [hget]
        exact hl i hlt
      · have heq : i = m := Nat.le_antisymm (Nat.lt_succ_iff.mp hi) hge
        subst heq
        have hget : (l ++ [a]).getD i d₀ = a := by
          rw [List.getD_eq_getElem?_getD, ← hlen, List.getElem?_concat_length]
          rfl
        rw [hget]
        exact ha

/-- Bits of `2 ^ n - 1` (`Nat.testBit_two_pow_sub_one`). -/
theorem testBit_two_pow_sub_one_eq : ∀ (n i : Nat), (2 ^ n - 1).testBit i = decide (i < n)
  | 0, i => by
      rw [Nat.pow_zero, Nat.sub_self, Nat.zero_testBit]
      exact (decide_eq_false (Nat.not_lt_zero i)).symm
  | n + 1, 0 => by
      rw [Nat.testBit_zero]
      have hpos := Nat.two_pow_pos n
      have hmod : (2 ^ (n + 1) - 1) % 2 = 1 := by rw [Nat.pow_succ]; omega
      rw [hmod]
      rfl
  | n + 1, i + 1 => by
      rw [Nat.testBit_add_one]
      have hpos := Nat.two_pow_pos n
      have hdiv : (2 ^ (n + 1) - 1) / 2 = 2 ^ n - 1 := by rw [Nat.pow_succ]; omega
      rw [hdiv, testBit_two_pow_sub_one_eq n i]
      exact decide_eq_decide.mpr Nat.succ_lt_succ_iff.symm

/-- The leading bit of a nonzero number is set (`Nat.testBit_log2`). -/
theorem testBit_log2_eq_true {n : Nat} (h : n ≠ 0) : n.testBit n.log2 = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h1 : 1 * 2 ^ n.log2 ≤ n := by rw [Nat.one_mul]; exact Nat.log2_self_le h
  have h2 : n < (1 + 1) * 2 ^ n.log2 := by
    have := @Nat.lt_log2_self n
    rw [Nat.pow_succ] at this
    omega
  rw [Nat.div_eq_of_lt_le h1 h2]
  rfl

/-- `log2` inverts powers of two (`Nat.log2_two_pow`). -/
theorem log2_two_pow_eq (n : Nat) : (2 ^ n).log2 = n :=
  (Nat.log2_eq_iff (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos n))).mpr
    ⟨Nat.le_refl _, by rw [Nat.pow_succ]; have := Nat.two_pow_pos n; omega⟩

/-- `List.pairwise_lt_range` without `Classical.choice`. -/
theorem pairwise_lt_range_cf : ∀ n : Nat, (List.range n).Pairwise (· < ·)
  | 0 => List.Pairwise.nil
  | n + 1 => by
      rw [List.range_succ, List.pairwise_append]
      refine ⟨pairwise_lt_range_cf n, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton.mp hb]
      exact List.mem_range.mp ha

/-- `List.nodup_range` without `Classical.choice`. -/
theorem nodup_range_cf (n : Nat) : (List.range n).Nodup :=
  List.Pairwise.imp (fun h => Nat.ne_of_lt h) (pairwise_lt_range_cf n)

end CodeCalculus
