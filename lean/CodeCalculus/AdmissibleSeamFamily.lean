import CodeCalculus.LogicalWitness
import CodeCalculus.ExactGlueSurvival

/-!
# Admissible seams as a regular family (issue #439)

Mechanizes the family-level guarantee of `LogicalWitness.lean` for the
family of instances whose seams are admissible in the sense of
`spec/JUDGMENT_LAYER.md` §2e.

The §2e seam certificate is a geometric statement: identical move words
over `{U,D,L,R}^*` make the seam checks have even overlap with the
factor minimum-weight logicals, so those logicals survive. That geometric
step is not mechanized here (move words are not in this substrate); it is
the single hypothesis `AdmissibleSeam` below. Everything downstream of it
— survival, `CarriesMin`, the instance-wise equality, and the family
guarantee — is mechanized and machine-checked.
-/

namespace CodeCalculus

/-- An admissible seam (in the sense of `spec/JUDGMENT_LAYER.md` §2e) is
    one for which every minimum-weight factor logical of sector `σ`
    survives. This is the decidable, mechanized content of the §2e
    move-word equality; the geometric proof that move-word equality
    implies it is the remaining gap (not in this substrate). -/
def AdmissibleSeam (a b : CodeState) (seams : List (Sector × List Nat))
    (σ : Sector) : Prop :=
  (∀ u, u.length = a.Q.length → isLogicalBool a σ u = true →
      weight u = exactDistance σ a → SurvivesA a b seams σ u) ∧
  (∀ u, u.length = b.Q.length → isLogicalBool b σ u = true →
      weight u = exactDistance σ b → SurvivesB a b seams σ u)

/-- A minimum-weight `σ`-logical exists in `s` when its logical vectors are
    nonempty. -/
def HasMinLogical (s : CodeState) (σ : Sector) : Prop :=
  logicalVectors s σ ≠ []

/-- Helper: on a nonempty list whose elements have weight below `init`,
    `minWeight_attained` gives a witness. -/
private theorem minWeight_witness (init : Nat) (vs : List (List Bool))
    (hne : vs ≠ [])
    (hbelow : ∀ v ∈ vs, weight v < init) :
    ∃ v ∈ vs, minWeight init vs = weight v := by
  rcases minWeight_attained init vs with hempty | hsome
  · exfalso
    rcases List.exists_mem_of_ne_nil vs hne with ⟨w, hw⟩
    have h1 := minWeight_le_of_mem init vs hw
    have hbeloww : weight w < init := hbelow w hw
    rw [hempty] at h1
    exact absurd hbeloww (Nat.not_lt_of_ge h1)
  · exact hsome

/-- Instance level: an admissible seam with sound, complete, and tight
    factor fields gives `CarriesMin`. -/
theorem admissible_carriesMin (a b : CodeState) (seams : List (Sector × List Nat))
    (σ : Sector) (logA logB : List LogRep)
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (hwfA : EncodingWellFormed a) (hwfB : EncodingWellFormed b)
    (hwf : EncodingWellFormed (glueState a b seams))
    (hA : LogField.Sound a logA) (hB : LogField.Sound b logB)
    (hCA : LogField.Complete a σ logA) (hCB : LogField.Complete b σ logB)
    (hTA : LogField.Tight a logA) (hTB : LogField.Tight b logB)
    (hadm : AdmissibleSeam a b seams σ)
    (hAmin : HasMinLogical a σ) (hBmin : HasMinLogical b σ) :
    CarriesMin a b seams σ logA logB := by
  by_cases hle : exactDistance σ a ≤ exactDistance σ b
  · -- Factor a supplies the entry.
    obtain ⟨u, hu, huw⟩ := minWeight_witness (a.Q.length + 1) (logicalVectors a σ) hAmin (fun v hv => by
      have hvlen := length_of_mem_logicalVectors hv
      have hvw := weight_le_length v
      omega)
    have hu_log : isLogicalBool a σ u = true :=
      (mem_logicalVectors_iff a σ u).mp hu |>.2
    have hu_len : u.length = a.Q.length :=
      (mem_logicalVectors_iff a σ u).mp hu |>.1
    have hu_w : weight u = exactDistance σ a := huw.symm
    have hsurv : SurvivesA a b seams σ u := hadm.1 u hu_len hu_log hu_w
    obtain ⟨e, he, hσe, hmem, hwe⟩ :=
      tight_entry_of_logical σ logA hA hCA hTA u hu_len hu_log (by omega)
    have hse := survivesA_congr a b seams σ u e.vec hwfA hwf hQ hsupB hmem hsurv
    have hmemglue : LogRep.extendA b e ∈ glueLog a b seams logA logB := by
      rw [mem_glueLog_iff_survives a b seams logA logB _ hA hB]
      exact Or.inl ⟨e, he, rfl, by rw [hσe]; exact hse⟩
    refine ⟨LogRep.extendA b e, hmemglue, hσe, ?_⟩
    show weight (LogRep.extendA b e).vec = min (exactDistance σ a) (exactDistance σ b)
    have hext : weight (LogRep.extendA b e).vec = weight e.vec := by
      show weight (e.vec ++ List.replicate b.Q.length false) = weight e.vec
      rw [weight_append_eq, weight_replicate_false, Nat.add_zero]
    rw [hext, hwe, hu_w]
    exact (Nat.min_eq_left hle).symm
  · -- Factor b supplies the entry.
    have hlt : exactDistance σ b < exactDistance σ a := Nat.lt_of_not_le hle
    obtain ⟨u, hu, huw⟩ := minWeight_witness (b.Q.length + 1) (logicalVectors b σ) hBmin (fun v hv => by
      have hvlen := length_of_mem_logicalVectors hv
      have hvw := weight_le_length v
      omega)
    have hu_log : isLogicalBool b σ u = true :=
      (mem_logicalVectors_iff b σ u).mp hu |>.2
    have hu_len : u.length = b.Q.length :=
      (mem_logicalVectors_iff b σ u).mp hu |>.1
    have hu_w : weight u = exactDistance σ b := huw.symm
    have hsurv : SurvivesB a b seams σ u := hadm.2 u hu_len hu_log hu_w
    obtain ⟨e, he, hσe, hmem, hwe⟩ :=
      tight_entry_of_logical σ logB hB hCB hTB u hu_len hu_log (by omega)
    have hse := survivesB_congr a b seams σ u e.vec hwfB hwf hQ hsupA hmem hsurv
    have hmemglue : LogRep.extendB a e ∈ glueLog a b seams logA logB := by
      rw [mem_glueLog_iff_survives a b seams logA logB _ hA hB]
      exact Or.inr ⟨e, he, rfl, by rw [hσe]; exact hse⟩
    refine ⟨LogRep.extendB a e, hmemglue, hσe, ?_⟩
    show weight (LogRep.extendB a e).vec = min (exactDistance σ a) (exactDistance σ b)
    have hext : weight (LogRep.extendB a e).vec = weight e.vec := by
      show weight (List.replicate a.Q.length false ++ e.vec) = weight e.vec
      rw [weight_append_eq, weight_replicate_false, Nat.zero_add]
    rw [hext, hwe, hu_w]
    exact (Nat.min_eq_right (Nat.le_of_lt hlt)).symm

/-- Family level: on a family of regular instances with admissible seams,
    the glued distance equals the minimum of the factor distances on every
    member. -/
theorem admissible_family_exactDistance_eq_min
    (F : GlueInstance → Prop) (σ : Sector)
    (hF : ∀ i, F i → i.Regular σ)
    (hadm : ∀ i, F i → AdmissibleSeam i.a i.b i.seams σ)
    (hAmin : ∀ i, F i → HasMinLogical i.a σ)
    (hBmin : ∀ i, F i → HasMinLogical i.b σ) :
    ∀ i, F i → exactDistance σ (glueState i.a i.b i.seams) =
      min (exactDistance σ i.a) (exactDistance σ i.b) := by
  intro i hi
  obtain ⟨hwfA, hwfB, hwf, hQ, hA, hB, hCA, hCB, hTA, hTB⟩ := hF i hi
  have hsupA := supports_subset_of_wf hwfA
  have hsupB := supports_subset_of_wf hwfB
  have hcarries : CarriesMin i.a i.b i.seams σ i.logA i.logB :=
    admissible_carriesMin i.a i.b i.seams σ i.logA i.logB hQ hsupA hsupB
      hwfA hwfB hwf hA hB hCA hCB hTA hTB (hadm i hi) (hAmin i hi) (hBmin i hi)
  exact glue_exactDistance_eq_min_of_mem_glueLog i.a i.b i.seams σ i.logA i.logB
    hQ hsupA hsupB hA hB hcarries

end CodeCalculus
