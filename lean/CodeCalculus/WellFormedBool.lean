import CodeCalculus.State

/-!
# The Bool/Prop bridge for well-formedness (, WP6)

`State.lean` carries two readings of well-formedness: the predicate
`EncodingWellFormed` the theorems quantify over, and the computable test
`wellFormedBool` the fixture replay decides. Until this module nothing
connected the two, so a replayed `wellFormedBool s = true` said nothing about
`EncodingWellFormed s` (review finding RC-3 of ). The bridge is
proved here clause by clause: span membership, the independence test, the
commutation test, and the conjunction.
-/

namespace CodeCalculus

/-- The enumeration of coefficient vectors is exactly the vectors of the
    given length. -/
theorem mem_allBoolLists : ∀ (n : Nat) (cs : List Bool),
    cs ∈ allBoolLists n ↔ cs.length = n
  | 0, cs => by
      simp only [allBoolLists, List.mem_singleton, List.length_eq_zero_iff]
  | n + 1, cs => by
      simp only [allBoolLists, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨bs, hbs, h⟩
        have hlen := (mem_allBoolLists n bs).mp hbs
        rcases h with rfl | rfl <;> simp [hlen]
      · intro h
        cases cs with
        | nil => simp at h
        | cons b bs =>
            refine ⟨bs, (mem_allBoolLists n bs).mpr (by simpa using h), ?_⟩
            cases b <;> simp

/-- The computable span test agrees with the span predicate. -/
theorem inSpanRowsBool_iff (Q : List Nat) (rows : List Row) (target : List Bool) :
    inSpanRowsBool Q rows target = true ↔ inSpanRows Q rows target := by
  simp only [inSpanRowsBool, inSpanRows, List.any_eq_true, beq_iff_eq, mem_allBoolLists]

/-- `Sector`'s derived `==` is the decided equality. -/
theorem sector_beq_eq_decide (a b : Sector) : (a == b) = decide (a = b) := by
  cases a <;> cases b <;> rfl

/-- The two peer filters (Bool-valued and decided) select the same rows. -/
theorem peers_filter_eq (s : CodeState) (row : Row) (r : Nat) :
    s.rows.filter (fun r' => r'.sector == row.sector && r'.id != r)
      = s.rows.filter (fun r' => decide (r'.sector = row.sector ∧ r'.id ≠ r)) := by
  apply List.filter_congr
  intro r' _
  rw [sector_beq_eq_decide]
  by_cases h1 : r'.sector = row.sector <;> by_cases h2 : r'.id = r <;> simp [h1, h2]

/-- The computable independence test agrees with `IndependentGenerator`. -/
theorem independentGeneratorBool_iff (r : Nat) (s : CodeState) :
    independentGeneratorBool r s = true ↔ IndependentGenerator r s := by
  unfold independentGeneratorBool IndependentGenerator
  cases h : rowById s r with
  | none => simp
  | some row =>
      simp only [Bool.not_eq_true', peers_filter_eq]
      rw [← inSpanRowsBool_iff]
      cases inSpanRowsBool s.Q
        (s.rows.filter (fun r' => decide (r'.sector = row.sector ∧ r'.id ≠ r)))
        (rowVector s.Q row) <;> simp

/-- The computable commutation test agrees with `I1`. -/
theorem i1Bool_iff (s : CodeState) : i1Bool s = true ↔ I1 s := by
  unfold i1Bool I1
  simp only [List.all_eq_true]
  constructor
  · intro h rX rZ hX hZ hsX hsZ
    have hc : (rX.sector == Sector.X && rZ.sector == Sector.Z) = true := by
      rw [hsX, hsZ]; rfl
    have := h rX hX rZ hZ
    simp only [hc, ite_true] at this
    exact Nat.eq_of_beq_eq_true this
  · intro h rX hX rZ hZ
    split
    · rename_i hc
      rw [Bool.and_eq_true, sector_beq_eq_decide, sector_beq_eq_decide,
        decide_eq_true_eq, decide_eq_true_eq] at hc
      rw [h rX rZ hX hZ hc.1 hc.2]; rfl
    · rfl

/-- The computable independence test for every displayed row agrees with `I2`. -/
theorem i2Bool_iff (s : CodeState) :
    s.rows.all (fun r => independentGeneratorBool r.id s) = true ↔ I2 s := by
  unfold I2
  simp only [List.all_eq_true, independentGeneratorBool_iff]

/-- The bridge: the fixture replay's Boolean verdict is the predicate the
    theorems quantify over. -/
theorem wellFormedBool_iff (s : CodeState) :
    wellFormedBool s = true ↔ EncodingWellFormed s := by
  unfold wellFormedBool EncodingWellFormed
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  rw [i1Bool_iff, i2Bool_iff, decide_eq_true_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
    refine ⟨h1, h2, h3, h4, ?_, ?_, h7, h8⟩
    · simpa [List.all_eq_true] using h5
    · simpa [List.all_eq_true] using h6
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, ?_⟩, ?_⟩, h7⟩, h8⟩
    · simpa [List.all_eq_true] using h5
    · simpa [List.all_eq_true] using h6

theorem encodingWellFormed_of_bool {s : CodeState} (h : wellFormedBool s = true) :
    EncodingWellFormed s :=
  (wellFormedBool_iff s).mp h

theorem not_encodingWellFormed_of_bool {s : CodeState} (h : wellFormedBool s = false) :
    ¬ EncodingWellFormed s := by
  intro hwf
  have := (wellFormedBool_iff s).mpr hwf
  rw [h] at this
  exact Bool.false_ne_true this

end CodeCalculus
