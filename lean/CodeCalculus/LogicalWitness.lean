import CodeCalculus.ExactGlueSurvival

/-!
# The logical-witness field under `E-GLUE`

Mechanizes the future-`Π` logical-witness field of `spec/STATE_MODEL.md` §1
as a definition outside `CodeState`, its transport under `E-GLUE`, and the
family-level reading of the §4.31 equality
`d_σ C = min (d_σ a) (d_σ b)` for the glued state `C = glueState a b seams`.

A field is a list of `LogRep`: a vector on the qubits of the state, a
sector, and an eigenvalue sign that no statement here reads. `LogField.Sound`
says every entry is a logical of its sector, `LogField.OnePerClass` that no
two entries represent one class, `LogField.Complete` that every logical
class of a sector has an entry, and `LogField.Tight` that every entry has
the least weight of its class.

* `glueLog` is the transport: the factor entries, extended by zero, that are
  logicals of the glued state. `mem_glueLog_iff_survives` reads its entries
  as the surviving factor entries (`SurvivesA`, `SurvivesB`), and
  `glueLog_sound` shows the transported field is sound.
* `glue_exactDistance_eq_min_of_mem_glueLog` is sufficiency: a transported
  entry of weight `min (d_σ a) (d_σ b)` closes the glued distance there.
* `glueLog_carries_min_of_logical` is necessity for complete and tight
  factor fields: a glued logical of that weight forces a transported entry
  of that weight.
* `glueExact_iff_carriesMin` joins the two, and `family_glueExact_iff` is
  the family-level statement: on any family of glues with sound, complete,
  and tight factor fields, the equality holds on every member iff the
  transported field carries a minimum-weight entry on every member.

The family is an arbitrary predicate. Nothing here models move words or
planarity, so nothing here says that the admissible seams of
`spec/JUDGMENT_LAYER.md` §2e form such a family. The two pinned instances
at the end show that the transport does not preserve `OnePerClass` and that
a well-formed glue can transport no entry.
-/

namespace CodeCalculus

/-- A logical representative: a vector on the qubits of a state, a sector,
    and an eigenvalue sign (`true` for `-1`). -/
structure LogRep where
  vec : List Bool
  sector : Sector
  sign : Bool
  deriving DecidableEq

/-- Every entry is a logical of its sector. -/
def LogField.Sound (s : CodeState) (log : List LogRep) : Prop :=
  ∀ e ∈ log, e.vec.length = s.Q.length ∧ isLogicalBool s e.sector e.vec = true

/-- No two entries of one sector represent the same class. -/
def LogField.OnePerClass (s : CodeState) (log : List LogRep) : Prop :=
  ∀ e ∈ log, ∀ e' ∈ log, e.sector = e'.sector →
    e'.vec ∈ classVectors s e.sector e.vec → e = e'

instance (s : CodeState) (log : List LogRep) : Decidable (LogField.OnePerClass s log) :=
  inferInstanceAs (Decidable (∀ e ∈ log, ∀ e' ∈ log, e.sector = e'.sector →
    e'.vec ∈ classVectors s e.sector e.vec → e = e'))

/-- Every `σ`-logical class has an entry. -/
def LogField.Complete (s : CodeState) (σ : Sector) (log : List LogRep) : Prop :=
  ∀ u : List Bool, u.length = s.Q.length → isLogicalBool s σ u = true →
    ∃ e ∈ log, e.sector = σ ∧ u ∈ classVectors s σ e.vec

/-- Every entry has the least weight of its class. -/
def LogField.Tight (s : CodeState) (log : List LogRep) : Prop :=
  ∀ e ∈ log, weight e.vec = classWeight s e.sector e.vec

/-- Extension by zero of an entry of the factor `a` to the glued qubits. -/
def LogRep.extendA (b : CodeState) (e : LogRep) : LogRep :=
  { e with vec := e.vec ++ List.replicate b.Q.length false }

/-- Extension by zero of an entry of the factor `b` to the glued qubits. -/
def LogRep.extendB (a : CodeState) (e : LogRep) : LogRep :=
  { e with vec := List.replicate a.Q.length false ++ e.vec }

/-- The transport of the field under `E-GLUE`: the factor entries, extended
    by zero, that are logicals of the glued state. -/
def glueLog (a b : CodeState) (seams : List (Sector × List Nat))
    (logA logB : List LogRep) : List LogRep :=
  (logA.map (LogRep.extendA b) ++ logB.map (LogRep.extendB a)).filter
    (fun e => isLogicalBool (glueState a b seams) e.sector e.vec)

/-! ### The transported field -/

theorem mem_glueLog_iff (a b : CodeState) (seams : List (Sector × List Nat))
    (logA logB : List LogRep) (e : LogRep) :
    e ∈ glueLog a b seams logA logB ↔
      ((∃ e0 ∈ logA, e = LogRep.extendA b e0) ∨ (∃ e0 ∈ logB, e = LogRep.extendB a e0)) ∧
        isLogicalBool (glueState a b seams) e.sector e.vec = true := by
  unfold glueLog
  rw [List.mem_filter, List.mem_append, List.mem_map, List.mem_map]
  constructor
  · rintro ⟨h | h, hl⟩
    · obtain ⟨e0, he0, rfl⟩ := h
      exact ⟨Or.inl ⟨e0, he0, rfl⟩, hl⟩
    · obtain ⟨e0, he0, rfl⟩ := h
      exact ⟨Or.inr ⟨e0, he0, rfl⟩, hl⟩
  · rintro ⟨h | h, hl⟩
    · obtain ⟨e0, he0, rfl⟩ := h
      exact ⟨Or.inl ⟨e0, he0, rfl⟩, hl⟩
    · obtain ⟨e0, he0, rfl⟩ := h
      exact ⟨Or.inr ⟨e0, he0, rfl⟩, hl⟩

/-- The entries of the transported field are the surviving factor entries. -/
theorem mem_glueLog_iff_survives (a b : CodeState) (seams : List (Sector × List Nat))
    (logA logB : List LogRep) (e : LogRep)
    (hA : LogField.Sound a logA) (hB : LogField.Sound b logB) :
    e ∈ glueLog a b seams logA logB ↔
      (∃ e0 ∈ logA, e = LogRep.extendA b e0 ∧ SurvivesA a b seams e0.sector e0.vec) ∨
      (∃ e0 ∈ logB, e = LogRep.extendB a e0 ∧ SurvivesB a b seams e0.sector e0.vec) := by
  rw [mem_glueLog_iff]
  constructor
  · rintro ⟨h | h, hl⟩
    · obtain ⟨e0, he0, rfl⟩ := h
      exact Or.inl ⟨e0, he0, rfl, (hA e0 he0).1, (hA e0 he0).2, hl⟩
    · obtain ⟨e0, he0, rfl⟩ := h
      exact Or.inr ⟨e0, he0, rfl, (hB e0 he0).1, (hB e0 he0).2, hl⟩
  · rintro (h | h)
    · obtain ⟨e0, he0, rfl, hs⟩ := h
      exact ⟨Or.inl ⟨e0, he0, rfl⟩, hs.2.2⟩
    · obtain ⟨e0, he0, rfl, hs⟩ := h
      exact ⟨Or.inr ⟨e0, he0, rfl⟩, hs.2.2⟩

/-- The transported field is sound on the glued state. -/
theorem glueLog_sound (a b : CodeState) (seams : List (Sector × List Nat))
    (logA logB : List LogRep)
    (hA : LogField.Sound a logA) (hB : LogField.Sound b logB) :
    LogField.Sound (glueState a b seams) (glueLog a b seams logA logB) := by
  intro e he
  obtain ⟨hsrc, hl⟩ := (mem_glueLog_iff a b seams logA logB e).mp he
  refine ⟨?_, hl⟩
  rcases hsrc with ⟨e0, he0, rfl⟩ | ⟨e0, he0, rfl⟩
  · show (e0.vec ++ List.replicate b.Q.length false).length = (glueState a b seams).Q.length
    rw [glueState_Q, List.length_append, List.length_append, (hA e0 he0).1,
      List.length_replicate]
  · show (List.replicate a.Q.length false ++ e0.vec).length = (glueState a b seams).Q.length
    rw [glueState_Q, List.length_append, List.length_append, (hB e0 he0).1,
      List.length_replicate]

/-! ### Sufficiency -/

/-- A transported entry bounds the glued distance of its sector from above
    by its weight. -/
theorem glue_exactDistance_le_of_mem_glueLog (a b : CodeState)
    (seams : List (Sector × List Nat)) (logA logB : List LogRep) (e : LogRep)
    (hA : LogField.Sound a logA) (hB : LogField.Sound b logB)
    (he : e ∈ glueLog a b seams logA logB) :
    exactDistance e.sector (glueState a b seams) ≤ weight e.vec := by
  have hs := glueLog_sound a b seams logA logB hA hB e he
  exact minWeight_le_of_mem ((glueState a b seams).Q.length + 1) _
    ((mem_logicalVectors_iff _ e.sector e.vec).mpr hs)

/-- The transported field carries a `σ`-entry whose weight is the smaller
    factor distance. -/
def CarriesMin (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (logA logB : List LogRep) : Prop :=
  ∃ e ∈ glueLog a b seams logA logB,
    e.sector = σ ∧ weight e.vec = min (exactDistance σ a) (exactDistance σ b)

/-- The finite form of the §4.31 equality: the glued state has a `σ`-logical
    whose weight is the smaller factor distance. -/
def GlueExact (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector) : Prop :=
  ∃ v ∈ logicalVectors (glueState a b seams) σ,
    weight v = min (exactDistance σ a) (exactDistance σ b)

/-- `GlueExact` is the equality of distances together with the existence of
    a `σ`-logical of the glued state. -/
theorem glueExact_iff (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q) :
    GlueExact a b seams σ ↔
      logicalVectors (glueState a b seams) σ ≠ [] ∧
        exactDistance σ (glueState a b seams) =
          min (exactDistance σ a) (exactDistance σ b) := by
  constructor
  · rintro ⟨v, hv, hw⟩
    refine ⟨fun h => ?_, Nat.le_antisymm ?_ (glue_exactDistance_ge_min a b seams σ hQ hsupA hsupB)⟩
    · rw [h] at hv
      exact absurd hv (List.not_mem_nil)
    · rw [← hw]
      exact minWeight_le_of_mem _ _ hv
  · rintro ⟨hne, heq⟩
    rcases minWeight_attained ((glueState a b seams).Q.length + 1)
        (logicalVectors (glueState a b seams) σ) with h | ⟨v, hv, h⟩
    · exfalso
      cases hl : logicalVectors (glueState a b seams) σ with
      | nil => exact hne hl
      | cons w ws =>
        have hw : w ∈ logicalVectors (glueState a b seams) σ := by
          rw [hl]
          exact List.mem_cons_self ..
        have h1 := minWeight_le_of_mem ((glueState a b seams).Q.length + 1) _ hw
        have h2 := weight_le_length w
        have h3 := length_of_mem_logicalVectors hw
        omega
    · exact ⟨v, hv, by
        have : exactDistance σ (glueState a b seams) = weight v := h
        omega⟩

/-- Sufficiency: a transported entry of the smaller factor distance gives
    the equality. Only soundness of the factor fields is used. -/
theorem glueExact_of_carriesMin (a b : CodeState) (seams : List (Sector × List Nat))
    (σ : Sector) (logA logB : List LogRep)
    (hA : LogField.Sound a logA) (hB : LogField.Sound b logB)
    (h : CarriesMin a b seams σ logA logB) : GlueExact a b seams σ := by
  obtain ⟨e, he, hσ, hw⟩ := h
  have hs := glueLog_sound a b seams logA logB hA hB e he
  rw [hσ] at hs
  exact ⟨e.vec, (mem_logicalVectors_iff _ σ e.vec).mpr hs, hw⟩

theorem glue_exactDistance_eq_min_of_mem_glueLog (a b : CodeState)
    (seams : List (Sector × List Nat)) (σ : Sector) (logA logB : List LogRep)
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (hA : LogField.Sound a logA) (hB : LogField.Sound b logB)
    (h : CarriesMin a b seams σ logA logB) :
    exactDistance σ (glueState a b seams) = min (exactDistance σ a) (exactDistance σ b) :=
  ((glueExact_iff a b seams σ hQ hsupA hsupB).mp
    (glueExact_of_carriesMin a b seams σ logA logB hA hB h)).2

/-! ### Necessity -/

/-- The entry of a complete and tight field in the class of a factor logical
    of weight `m`, when `m` is at most the factor distance, has weight `m`
    and is in the class both ways. -/
theorem tight_entry_of_logical {s : CodeState} (σ : Sector)
    (log : List LogRep) (hS : LogField.Sound s log) (hC : LogField.Complete s σ log)
    (hT : LogField.Tight s log) (u : List Bool) (hu : u.length = s.Q.length)
    (hlog : isLogicalBool s σ u = true) (hle : weight u ≤ exactDistance σ s) :
    ∃ e ∈ log, e.sector = σ ∧ e.vec ∈ classVectors s σ u ∧ weight e.vec = weight u := by
  obtain ⟨e, he, hσ, hcl⟩ := hC u hu hlog
  have hel := (hS e he).1
  have helog := (hS e he).2
  rw [hσ] at helog
  have hmem : e.vec ∈ classVectors s σ u := by
    rw [mem_classVectors_iff] at hcl ⊢
    refine ⟨hel, ?_⟩
    rw [xorVec_comm]
    exact hcl.2
  have h1 : weight e.vec = classWeight s σ e.vec := by
    have := hT e he
    rw [hσ] at this
    exact this
  have h2 : classWeight s σ e.vec ≤ weight u := classWeight_le_of_mem hcl
  have h3 : exactDistance σ s ≤ weight e.vec :=
    minWeight_le_of_mem (s.Q.length + 1) _
      ((mem_logicalVectors_iff s σ e.vec).mpr ⟨hel, helog⟩)
  exact ⟨e, he, hσ, hmem, by omega⟩

/-- Necessity: with sound, complete, and tight factor fields, a glued
    logical of the smaller factor distance forces a transported entry of
    that weight. -/
theorem glueLog_carries_min_of_logical (a b : CodeState) (seams : List (Sector × List Nat))
    (σ : Sector) (logA logB : List LogRep)
    (hwfA : EncodingWellFormed a) (hwfB : EncodingWellFormed b)
    (hwf : EncodingWellFormed (glueState a b seams))
    (hQ : DisjointList a.Q b.Q)
    (hA : LogField.Sound a logA) (hB : LogField.Sound b logB)
    (hCA : LogField.Complete a σ logA) (hCB : LogField.Complete b σ logB)
    (hTA : LogField.Tight a logA) (hTB : LogField.Tight b logB)
    (h : GlueExact a b seams σ) : CarriesMin a b seams σ logA logB := by
  obtain ⟨v, hv, hw⟩ := h
  have hsupA := supports_subset_of_wf hwfA
  have hsupB := supports_subset_of_wf hwfB
  rcases glue_survivor_of_min_logical a b seams σ v hQ hsupA hsupB hv hw with
    ⟨u, hs, hwu, _⟩ | ⟨u, hs, hwu, _⟩
  · have hle : weight u ≤ exactDistance σ a := by
      have := Nat.min_le_left (exactDistance σ a) (exactDistance σ b)
      omega
    obtain ⟨e, he, hσ, hmem, hwe⟩ :=
      tight_entry_of_logical σ logA hA hCA hTA u hs.1 hs.2.1 hle
    have hse := survivesA_congr a b seams σ u e.vec hwfA hwf hQ hsupB hmem hs
    refine ⟨LogRep.extendA b e, ?_, hσ, ?_⟩
    · rw [mem_glueLog_iff_survives a b seams logA logB _ hA hB]
      exact Or.inl ⟨e, he, rfl, by rw [hσ]; exact hse⟩
    · show weight (e.vec ++ List.replicate b.Q.length false) = _
      rw [weight_append_eq, weight_replicate_false]
      omega
  · have hle : weight u ≤ exactDistance σ b := by
      have := Nat.min_le_right (exactDistance σ a) (exactDistance σ b)
      omega
    obtain ⟨e, he, hσ, hmem, hwe⟩ :=
      tight_entry_of_logical σ logB hB hCB hTB u hs.1 hs.2.1 hle
    have hse := survivesB_congr a b seams σ u e.vec hwfB hwf hQ hsupA hmem hs
    refine ⟨LogRep.extendB a e, ?_, hσ, ?_⟩
    · rw [mem_glueLog_iff_survives a b seams logA logB _ hA hB]
      exact Or.inr ⟨e, he, rfl, by rw [hσ]; exact hse⟩
    · show weight (List.replicate a.Q.length false ++ e.vec) = _
      rw [weight_append_eq, weight_replicate_false]
      omega

/-! ### The instance and family statements -/

/-- A glue with its two factor fields. -/
structure GlueInstance where
  a : CodeState
  b : CodeState
  seams : List (Sector × List Nat)
  logA : List LogRep
  logB : List LogRep

/-- The hypotheses under which the transported field decides the equality in
    sector `σ`: the three states are well formed, the factor namespaces are
    disjoint, and the factor fields are sound, complete in `σ`, and tight. -/
def GlueInstance.Regular (i : GlueInstance) (σ : Sector) : Prop :=
  EncodingWellFormed i.a ∧ EncodingWellFormed i.b ∧
    EncodingWellFormed (glueState i.a i.b i.seams) ∧ DisjointList i.a.Q i.b.Q ∧
    LogField.Sound i.a i.logA ∧ LogField.Sound i.b i.logB ∧
    LogField.Complete i.a σ i.logA ∧ LogField.Complete i.b σ i.logB ∧
    LogField.Tight i.a i.logA ∧ LogField.Tight i.b i.logB

/-- On a regular instance the equality holds iff the transported field
    carries an entry of the smaller factor distance. -/
theorem glueExact_iff_carriesMin (i : GlueInstance) (σ : Sector) (h : i.Regular σ) :
    GlueExact i.a i.b i.seams σ ↔ CarriesMin i.a i.b i.seams σ i.logA i.logB := by
  obtain ⟨hwfA, hwfB, hwf, hQ, hA, hB, hCA, hCB, hTA, hTB⟩ := h
  exact ⟨glueLog_carries_min_of_logical i.a i.b i.seams σ i.logA i.logB hwfA hwfB hwf hQ
      hA hB hCA hCB hTA hTB,
    glueExact_of_carriesMin i.a i.b i.seams σ i.logA i.logB hA hB⟩

/-- The family-level statement: on a family of regular instances, the
    equality holds on every member iff the transported field carries a
    minimum-weight entry on every member. The family `F` is arbitrary. -/
theorem family_glueExact_iff (F : GlueInstance → Prop) (σ : Sector)
    (hF : ∀ i, F i → i.Regular σ) :
    (∀ i, F i → GlueExact i.a i.b i.seams σ) ↔
      (∀ i, F i → CarriesMin i.a i.b i.seams σ i.logA i.logB) :=
  ⟨fun h i hi => (glueExact_iff_carriesMin i σ (hF i hi)).mp (h i hi),
    fun h i hi => (glueExact_iff_carriesMin i σ (hF i hi)).mpr (h i hi)⟩

/-- The family-level guarantee as an equality of distances. -/
theorem family_exactDistance_eq_min (F : GlueInstance → Prop) (σ : Sector)
    (hF : ∀ i, F i → i.Regular σ)
    (hC : ∀ i, F i → CarriesMin i.a i.b i.seams σ i.logA i.logB) :
    ∀ i, F i → exactDistance σ (glueState i.a i.b i.seams) =
      min (exactDistance σ i.a) (exactDistance σ i.b) := by
  intro i hi
  obtain ⟨hwfA, hwfB, _, hQ, hA, hB, _⟩ := hF i hi
  exact glue_exactDistance_eq_min_of_mem_glueLog i.a i.b i.seams σ i.logA i.logB hQ
    (supports_subset_of_wf hwfA) (supports_subset_of_wf hwfB) hA hB (hC i hi)

/-! ### Two pinned instances -/

/-- A bare qubit named `q`. -/
def bareQubit (q : Nat) : CodeState := { Q := [q], rows := [], used := [] }

/-- The `Z` logical of a bare qubit. -/
def bareZ : LogRep := { vec := [true], sector := Sector.Z, sign := false }

/-- Two bare qubits joined by one `Z` seam check on both: the two factor
    entries both survive and represent one class of the glued state, so the
    transport does not preserve `OnePerClass`. -/
theorem glueLog_not_onePerClass :
    wellFormedBool (glueState (bareQubit 0) (bareQubit 1) [(Sector.Z, [0, 1])]) = true ∧
      LogField.OnePerClass (bareQubit 0) [bareZ] ∧
      LogField.OnePerClass (bareQubit 1) [bareZ] ∧
      ¬ LogField.OnePerClass
        (glueState (bareQubit 0) (bareQubit 1) [(Sector.Z, [0, 1])])
        (glueLog (bareQubit 0) (bareQubit 1) [(Sector.Z, [0, 1])] [bareZ] [bareZ]) := by
  decide

/-- Two qubits `q` and `q + 1` with one `Z` row on both. -/
def zPair (q id : Nat) : CodeState :=
  { Q := [q, q + 1], rows := [{ id := id, sector := Sector.Z, support := [q, q + 1] }],
    used := [id] }

/-- The weight-one `Z` logical of `zPair`. -/
def zPairLog : LogRep := { vec := [true, false], sector := Sector.Z, sign := false }

/-- The counterexample of §4.33: one `X` seam check on all four qubits of
    two `zPair` factors gives a well-formed glue to which no factor entry is
    transported. -/
theorem glueLog_empty_instance :
    wellFormedBool (glueState (zPair 0 0) (zPair 2 1) [(Sector.X, [0, 1, 2, 3])]) = true ∧
      glueLog (zPair 0 0) (zPair 2 1) [(Sector.X, [0, 1, 2, 3])] [zPairLog] [zPairLog] = [] := by
  decide

end CodeCalculus
