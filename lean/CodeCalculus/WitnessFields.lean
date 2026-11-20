import CodeCalculus.LogicalWitness

/-!
# The logical-witness and boundary-label fields: definition and transport

Mechanizes the definitions of `spec/STATE_MODEL.md` §1a. Both fields stay
outside `CodeState`.

* `LogRep.SameClass` is the class relation on representatives, and
  `normalizeLog` keeps one representative of least weight per class.
  `normalizeLog_spec` is its specification: the result has pairwise
  distinct classes, is a sublist of the input as a set, and holds for every
  input entry an entry of its class of no larger weight.
* `transportLog child cands` is the transport of the logical-witness field
  to a child state from the candidates a transition supplies: the
  candidates that are logicals of the child, normalized. It is sound
  (`transportLog_sound`), has one entry per class
  (`transportLog_onePerClass`), and loses no class and no minimum
  (`transportLog_keeps`), whatever the candidates are.
* `glueField` is the instance for `E-GLUE`. `carriesMin_glueField_iff`
  shows that it carries a minimum-weight entry exactly when the
  unnormalized `glueLog` does, so the statements of `LogicalWitness.lean`
  hold for it.
* `BdLabel` is a boundary label: a segment, a logical representative
  supported in the segment, and an index. `transportBd` keeps the candidate
  labels that are valid in the child, `transportBd_names_class` couples the
  two fields, and `bdLabel_extendA_valid_iff` and its `B` form show that a
  factor label crosses a seam exactly when its representative survives.
-/

namespace CodeCalculus

/-! ### The class relation -/

/-- Two representatives of one sector whose vectors differ by an element of
    the span of the rows of that sector. -/
def LogRep.SameClass (s : CodeState) (a b : LogRep) : Prop :=
  a.sector = b.sector ∧ b.vec ∈ classVectors s a.sector a.vec

instance (s : CodeState) (a b : LogRep) : Decidable (LogRep.SameClass s a b) :=
  inferInstanceAs (Decidable (a.sector = b.sector ∧ b.vec ∈ classVectors s a.sector a.vec))

theorem LogRep.sameClass_refl (s : CodeState) (a : LogRep)
    (ha : a.vec.length = s.Q.length) : LogRep.SameClass s a a :=
  ⟨rfl, self_mem_classVectors s a.sector a.vec ha⟩

theorem LogRep.sameClass_symm {s : CodeState} {a b : LogRep}
    (ha : a.vec.length = s.Q.length) (h : LogRep.SameClass s a b) :
    LogRep.SameClass s b a := by
  obtain ⟨hσ, hm⟩ := h
  rw [mem_classVectors_iff] at hm
  refine ⟨hσ.symm, ?_⟩
  rw [← hσ, mem_classVectors_iff, xorVec_comm]
  exact ⟨ha, hm.2⟩

theorem LogRep.sameClass_trans {s : CodeState} {a b c : LogRep}
    (ha : a.vec.length = s.Q.length)
    (h1 : LogRep.SameClass s a b) (h2 : LogRep.SameClass s b c) :
    LogRep.SameClass s a c := by
  obtain ⟨hσ1, hm1⟩ := h1
  obtain ⟨hσ2, hm2⟩ := h2
  rw [mem_classVectors_iff] at hm1 hm2
  rw [← hσ1] at hm2
  refine ⟨hσ1.trans hσ2, ?_⟩
  rw [mem_classVectors_iff]
  refine ⟨hm2.1, ?_⟩
  have h := inSpanRows_xor s.Q (sectorRows s a.sector) hm2.2 hm1.2
  rw [xorVec_chain c.vec b.vec a.vec (hm2.1.trans hm1.1.symm) (hm1.1.trans ha.symm)] at h
  exact h

/-! ### One representative of least weight per class -/

/-- Insert a representative into a list with one entry per class: it
    replaces the entry of its class when it is strictly lighter, is dropped
    when that entry is at least as light, and is appended otherwise. -/
def insertRep (s : CodeState) (e : LogRep) : List LogRep → List LogRep
  | [] => [e]
  | k :: ks =>
      if LogRep.SameClass s k e then
        (if weight e.vec < weight k.vec then e :: ks else k :: ks)
      else k :: insertRep s e ks

/-- Keep one representative of least weight per class, earlier entries
    winning ties. -/
def normalizeLog (s : CodeState) (log : List LogRep) : List LogRep :=
  log.foldl (fun acc e => insertRep s e acc) []

/-- Every entry has the length of the state's qubit list. -/
def LogField.LenOK (s : CodeState) (log : List LogRep) : Prop :=
  ∀ e ∈ log, e.vec.length = s.Q.length

/-- The entries have pairwise distinct classes. -/
def LogField.Distinct (s : CodeState) (log : List LogRep) : Prop :=
  log.Pairwise (fun a b => ¬ LogRep.SameClass s a b)

theorem mem_insertRep {s : CodeState} {e x : LogRep} :
    ∀ {l : List LogRep}, x ∈ insertRep s e l → x = e ∨ x ∈ l
  | [], h => Or.inl (List.mem_singleton.mp h)
  | k :: ks, h => by
      unfold insertRep at h
      split at h
      · split at h
        · rcases List.mem_cons.mp h with rfl | h'
          · exact Or.inl rfl
          · exact Or.inr (List.mem_cons_of_mem k h')
        · exact Or.inr h
      · rcases List.mem_cons.mp h with rfl | h'
        · exact Or.inr (List.mem_cons_self ..)
        · rcases mem_insertRep h' with rfl | h''
          · exact Or.inl rfl
          · exact Or.inr (List.mem_cons_of_mem k h'')

theorem insertRep_lenOK {s : CodeState} {e : LogRep} {l : List LogRep}
    (hl : LogField.LenOK s l) (he : e.vec.length = s.Q.length) :
    LogField.LenOK s (insertRep s e l) := by
  intro x hx
  rcases mem_insertRep hx with rfl | h
  · exact he
  · exact hl x h

theorem insertRep_distinct {s : CodeState} {e : LogRep} :
    ∀ {l : List LogRep}, LogField.LenOK s l → LogField.Distinct s l →
      LogField.Distinct s (insertRep s e l)
  | [], _, _ => List.pairwise_singleton _ _
  | k :: ks, hl, hd => by
      have hd' := List.pairwise_cons.mp hd
      have hk : k.vec.length = s.Q.length := hl k (List.mem_cons_self ..)
      have hks : LogField.LenOK s ks := fun x hx => hl x (List.mem_cons_of_mem k hx)
      unfold insertRep
      split
      · rename_i hke
        split
        · exact List.pairwise_cons.mpr
            ⟨fun b hb hsc => hd'.1 b hb (LogRep.sameClass_trans hk hke hsc), hd'.2⟩
        · exact hd
      · rename_i hne
        refine List.pairwise_cons.mpr ⟨fun b hb => ?_, insertRep_distinct hks hd'.2⟩
        rcases mem_insertRep hb with rfl | hb'
        · exact hne
        · exact hd'.1 b hb'

/-- The inserted representative has an entry of its class of no larger
    weight. -/
theorem insertRep_has {s : CodeState} {e : LogRep} (he : e.vec.length = s.Q.length) :
    ∀ l : List LogRep, ∃ k ∈ insertRep s e l,
      LogRep.SameClass s k e ∧ weight k.vec ≤ weight e.vec
  | [] => ⟨e, List.mem_singleton.mpr rfl, LogRep.sameClass_refl s e he, Nat.le_refl _⟩
  | k :: ks => by
      unfold insertRep
      split
      · rename_i hke
        split
        · exact ⟨e, List.mem_cons_self .., LogRep.sameClass_refl s e he, Nat.le_refl _⟩
        · rename_i hlt
          exact ⟨k, List.mem_cons_self .., hke, Nat.le_of_not_lt hlt⟩
      · obtain ⟨k', hk', hsc, hw⟩ := insertRep_has he ks
        exact ⟨k', List.mem_cons_of_mem k hk', hsc, hw⟩

/-- Every earlier entry keeps an entry of its class of no larger weight. -/
theorem insertRep_keeps {s : CodeState} {e : LogRep} :
    ∀ {l : List LogRep}, LogField.LenOK s l → ∀ x ∈ l, ∃ k ∈ insertRep s e l,
      LogRep.SameClass s k x ∧ weight k.vec ≤ weight x.vec
  | [], _, x, hx => absurd hx (List.not_mem_nil)
  | k :: ks, hl, x, hx => by
      have hk : k.vec.length = s.Q.length := hl k (List.mem_cons_self ..)
      have hks : LogField.LenOK s ks := fun y hy => hl y (List.mem_cons_of_mem k hy)
      have hxl : x.vec.length = s.Q.length := hl x hx
      unfold insertRep
      split
      · rename_i hke
        split
        · rename_i hlt
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact ⟨e, List.mem_cons_self .., LogRep.sameClass_symm hk hke, Nat.le_of_lt hlt⟩
          · exact ⟨x, List.mem_cons_of_mem e hx', LogRep.sameClass_refl s x hxl,
              Nat.le_refl _⟩
        · exact ⟨x, hx, LogRep.sameClass_refl s x hxl, Nat.le_refl _⟩
      · rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨x, List.mem_cons_self .., LogRep.sameClass_refl s x hxl, Nat.le_refl _⟩
        · obtain ⟨k', hk', hsc, hw⟩ := insertRep_keeps hks x hx'
          exact ⟨k', List.mem_cons_of_mem k hk', hsc, hw⟩

/-- The fold of `insertRep` from an accumulator with distinct classes. -/
theorem foldl_insertRep_spec (s : CodeState) :
    ∀ (log acc : List LogRep), LogField.LenOK s acc → LogField.LenOK s log →
      LogField.Distinct s acc →
      LogField.Distinct s (log.foldl (fun acc e => insertRep s e acc) acc) ∧
      LogField.LenOK s (log.foldl (fun acc e => insertRep s e acc) acc) ∧
      (∀ x ∈ log.foldl (fun acc e => insertRep s e acc) acc, x ∈ acc ∨ x ∈ log) ∧
      (∀ x, x ∈ acc ∨ x ∈ log →
        ∃ k ∈ log.foldl (fun acc e => insertRep s e acc) acc,
          LogRep.SameClass s k x ∧ weight k.vec ≤ weight x.vec)
  | [], acc, hacc, _, hd => by
      refine ⟨hd, hacc, fun x hx => Or.inl hx, fun x hx => ?_⟩
      rcases hx with hx | hx
      · exact ⟨x, hx, LogRep.sameClass_refl s x (hacc x hx), Nat.le_refl _⟩
      · exact absurd hx (List.not_mem_nil)
  | e :: es, acc, hacc, hlog, hd => by
      have he : e.vec.length = s.Q.length := hlog e (List.mem_cons_self ..)
      have hes : LogField.LenOK s es := fun x hx => hlog x (List.mem_cons_of_mem e hx)
      have hacc' := insertRep_lenOK hacc he
      obtain ⟨hD, hL, hM, hK⟩ :=
        foldl_insertRep_spec s es (insertRep s e acc) hacc' hes (insertRep_distinct hacc hd)
      refine ⟨hD, hL, fun x hx => ?_, fun x hx => ?_⟩
      · rcases hM x hx with h | h
        · rcases mem_insertRep h with rfl | h'
          · exact Or.inr (List.mem_cons_self ..)
          · exact Or.inl h'
        · exact Or.inr (List.mem_cons_of_mem e h)
      · have step : ∀ k' ∈ insertRep s e acc,
            LogRep.SameClass s k' x ∧ weight k'.vec ≤ weight x.vec →
            ∃ k ∈ es.foldl (fun acc e => insertRep s e acc) (insertRep s e acc),
              LogRep.SameClass s k x ∧ weight k.vec ≤ weight x.vec := by
          intro k' hk' hx'
          obtain ⟨k, hk, hsc, hw⟩ := hK k' (Or.inl hk')
          exact ⟨k, hk, LogRep.sameClass_trans (hL k hk) hsc hx'.1, Nat.le_trans hw hx'.2⟩
        rcases hx with hx | hx
        · obtain ⟨k', hk', hsc, hw⟩ := insertRep_keeps (e := e) hacc x hx
          exact step k' hk' ⟨hsc, hw⟩
        · rcases List.mem_cons.mp hx with rfl | hx'
          · obtain ⟨k', hk', hsc, hw⟩ := insertRep_has he acc
            exact step k' hk' ⟨hsc, hw⟩
          · exact hK x (Or.inr hx')

/-- The specification of `normalizeLog` on entries of the right length. -/
theorem normalizeLog_spec (s : CodeState) (log : List LogRep) (hl : LogField.LenOK s log) :
    LogField.Distinct s (normalizeLog s log) ∧
      (∀ x ∈ normalizeLog s log, x ∈ log) ∧
      (∀ x ∈ log, ∃ k ∈ normalizeLog s log,
        LogRep.SameClass s k x ∧ weight k.vec ≤ weight x.vec) := by
  obtain ⟨hD, _, hM, hK⟩ := foldl_insertRep_spec s log [] (fun _ h => absurd h (List.not_mem_nil))
    hl List.Pairwise.nil
  refine ⟨hD, fun x hx => ?_, fun x hx => hK x (Or.inr hx)⟩
  rcases hM x hx with h | h
  · exact absurd h (List.not_mem_nil)
  · exact h

/-- Pairwise distinct classes give the one-per-class condition. -/
theorem onePerClass_of_distinct {s : CodeState} :
    ∀ {l : List LogRep}, LogField.LenOK s l → LogField.Distinct s l →
      LogField.OnePerClass s l
  | [], _, _ => fun _ h => absurd h (List.not_mem_nil)
  | x :: xs, hl, hd => by
      have hd' := List.pairwise_cons.mp hd
      have hxs : LogField.LenOK s xs := fun y hy => hl y (List.mem_cons_of_mem x hy)
      have ih := onePerClass_of_distinct hxs hd'.2
      intro e he e' he' hσ hm
      rcases List.mem_cons.mp he with rfl | he1
      · rcases List.mem_cons.mp he' with rfl | he2
        · rfl
        · exact absurd ⟨hσ, hm⟩ (hd'.1 e' he2)
      · rcases List.mem_cons.mp he' with rfl | he2
        · exact absurd (LogRep.sameClass_symm (hxs e he1) ⟨hσ, hm⟩) (hd'.1 e he1)
        · exact ih e he1 e' he2 hσ hm

/-! ### Transport of the logical-witness field -/

/-- A representative is valid in a state: its vector has the length of the
    qubit list and is a logical of its sector. -/
def LogRep.validIn (s : CodeState) (e : LogRep) : Bool :=
  e.vec.length == s.Q.length && isLogicalBool s e.sector e.vec

theorem LogRep.validIn_iff (s : CodeState) (e : LogRep) :
    e.validIn s = true ↔
      e.vec.length = s.Q.length ∧ isLogicalBool s e.sector e.vec = true := by
  unfold LogRep.validIn
  rw [Bool.and_eq_true, beq_iff_eq]

/-- The transport of the field to a child state from the candidates a
    transition supplies: the valid candidates, one of least weight per
    class. -/
def transportLog (child : CodeState) (cands : List LogRep) : List LogRep :=
  normalizeLog child (cands.filter (LogRep.validIn child))

theorem filter_validIn_lenOK (child : CodeState) (cands : List LogRep) :
    LogField.LenOK child (cands.filter (LogRep.validIn child)) := fun e he =>
  ((LogRep.validIn_iff child e).mp (List.mem_filter.mp he).2).1

theorem mem_transportLog {child : CodeState} {cands : List LogRep} {x : LogRep}
    (h : x ∈ transportLog child cands) : x ∈ cands ∧ x.validIn child = true :=
  List.mem_filter.mp ((normalizeLog_spec child _ (filter_validIn_lenOK child cands)).2.1 x h)

/-- The transported field is sound, whatever the candidates are. -/
theorem transportLog_sound (child : CodeState) (cands : List LogRep) :
    LogField.Sound child (transportLog child cands) := fun e he =>
  (LogRep.validIn_iff child e).mp (mem_transportLog he).2

/-- The transported field has at most one entry per class. -/
theorem transportLog_onePerClass (child : CodeState) (cands : List LogRep) :
    LogField.OnePerClass child (transportLog child cands) :=
  onePerClass_of_distinct (fun e he => (transportLog_sound child cands e he).1)
    (normalizeLog_spec child _ (filter_validIn_lenOK child cands)).1

/-- No class and no minimum is lost: every valid candidate has a transported
    entry of its class of no larger weight. -/
theorem transportLog_keeps (child : CodeState) (cands : List LogRep) (e : LogRep)
    (he : e ∈ cands) (hv : e.validIn child = true) :
    ∃ k ∈ transportLog child cands,
      LogRep.SameClass child k e ∧ weight k.vec ≤ weight e.vec :=
  (normalizeLog_spec child _ (filter_validIn_lenOK child cands)).2.2 e
    (List.mem_filter.mpr ⟨he, hv⟩)

/-! ### The `E-GLUE` instance -/

/-- The candidates of `E-GLUE`: the factor entries extended by zero. -/
def glueCands (a b : CodeState) (logA logB : List LogRep) : List LogRep :=
  logA.map (LogRep.extendA b) ++ logB.map (LogRep.extendB a)

/-- The transport of the field under `E-GLUE`. -/
def glueField (a b : CodeState) (seams : List (Sector × List Nat))
    (logA logB : List LogRep) : List LogRep :=
  transportLog (glueState a b seams) (glueCands a b logA logB)

/-- For sound factor fields the valid candidates are the entries of
    `glueLog`. -/
theorem mem_glueLog_iff_valid (a b : CodeState) (seams : List (Sector × List Nat))
    (logA logB : List LogRep) (hA : LogField.Sound a logA) (hB : LogField.Sound b logB)
    (e : LogRep) :
    e ∈ glueLog a b seams logA logB ↔
      e ∈ glueCands a b logA logB ∧ e.validIn (glueState a b seams) = true := by
  constructor
  · intro he
    have hs := glueLog_sound a b seams logA logB hA hB e he
    exact ⟨(List.mem_filter.mp he).1, (LogRep.validIn_iff _ e).mpr hs⟩
  · rintro ⟨hc, hv⟩
    exact List.mem_filter.mpr ⟨hc, ((LogRep.validIn_iff _ e).mp hv).2⟩

/-- The normalized transport carries a minimum-weight entry exactly when
    `glueLog` does. -/
theorem carriesMin_glueField_iff (a b : CodeState) (seams : List (Sector × List Nat))
    (σ : Sector) (logA logB : List LogRep)
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (hA : LogField.Sound a logA) (hB : LogField.Sound b logB) :
    (∃ e ∈ glueField a b seams logA logB,
        e.sector = σ ∧ weight e.vec = min (exactDistance σ a) (exactDistance σ b)) ↔
      CarriesMin a b seams σ logA logB := by
  constructor
  · rintro ⟨e, he, hσ, hw⟩
    obtain ⟨hc, hv⟩ := mem_transportLog he
    exact ⟨e, (mem_glueLog_iff_valid a b seams logA logB hA hB e).mpr ⟨hc, hv⟩, hσ, hw⟩
  · rintro ⟨e, he, hσ, hw⟩
    obtain ⟨hc, hv⟩ := (mem_glueLog_iff_valid a b seams logA logB hA hB e).mp he
    obtain ⟨k, hk, hsc, hwk⟩ := transportLog_keeps _ _ e hc hv
    have hkσ : k.sector = σ := hsc.1.trans hσ
    have hks := transportLog_sound _ _ k hk
    rw [hkσ] at hks
    have h1 : exactDistance σ (glueState a b seams) ≤ weight k.vec :=
      minWeight_le_of_mem ((glueState a b seams).Q.length + 1) _
        ((mem_logicalVectors_iff _ σ k.vec).mpr hks)
    have h2 := glue_exactDistance_ge_min a b seams σ hQ hsupA hsupB
    exact ⟨k, hk, hkσ, by omega⟩

/-- Two bare qubits joined by one `Z` seam check on both: the normalized
    transport holds one entry, where `glueLog` holds two of one class
    (`glueLog_not_onePerClass`). -/
theorem glueField_bare_instance :
    glueField (bareQubit 0) (bareQubit 1) [(Sector.Z, [0, 1])] [bareZ] [bareZ] =
      [LogRep.extendA (bareQubit 1) bareZ] := by
  decide

/-! ### The boundary-label field -/

/-- A boundary label: a segment, a logical representative supported in the
    segment, and the index naming the logical operator. -/
structure BdLabel where
  seg : List Bool
  rep : LogRep
  index : Nat
  deriving DecidableEq

/-- Pointwise inclusion of supports, on the common prefix. -/
def vecSubset (u v : List Bool) : Bool := (u.zip v).all (fun p => !p.1 || p.2)

/-- A label is valid in a state: its segment has the length of the qubit
    list, its representative is valid, and the representative is supported
    in the segment. -/
def BdLabel.validIn (s : CodeState) (l : BdLabel) : Bool :=
  l.seg.length == s.Q.length && l.rep.validIn s && vecSubset l.rep.vec l.seg

/-- Every label is valid. -/
def BdField.Sound (s : CodeState) (bd : List BdLabel) : Prop :=
  ∀ l ∈ bd, l.validIn s = true

/-- Two segments are equal or disjoint. -/
def BdField.Segmented (bd : List BdLabel) : Prop :=
  ∀ l ∈ bd, ∀ l' ∈ bd, l.seg = l'.seg ∨
    (l.seg.zip l'.seg).all (fun p => !(p.1 && p.2)) = true

/-- The transport of the boundary-label field from the candidates a
    transition supplies: the candidates valid in the child. -/
def transportBd (child : CodeState) (cands : List BdLabel) : List BdLabel :=
  cands.filter (BdLabel.validIn child)

theorem transportBd_sound (child : CodeState) (cands : List BdLabel) :
    BdField.Sound child (transportBd child cands) := fun _ hl =>
  (List.mem_filter.mp hl).2

/-- The coupling of the two fields: a transported label names a class of
    the logical-witness field transported from the labels' representatives,
    and that field holds an entry of the class no heavier than the label's
    representative. -/
theorem transportBd_names_class (child : CodeState) (cands : List BdLabel) (l : BdLabel)
    (hl : l ∈ transportBd child cands) :
    ∃ k ∈ transportLog child (cands.map BdLabel.rep),
      LogRep.SameClass child k l.rep ∧ weight k.vec ≤ weight l.rep.vec := by
  obtain ⟨hc, hv⟩ := List.mem_filter.mp hl
  unfold BdLabel.validIn at hv
  rw [Bool.and_eq_true, Bool.and_eq_true] at hv
  exact transportLog_keeps child _ l.rep (List.mem_map.mpr ⟨l, hc, rfl⟩) hv.1.2

/-- Extension by zero of a label of the factor `a`. -/
def BdLabel.extendA (b : CodeState) (l : BdLabel) : BdLabel :=
  { l with seg := l.seg ++ List.replicate b.Q.length false, rep := l.rep.extendA b }

/-- Extension by zero of a label of the factor `b`. -/
def BdLabel.extendB (a : CodeState) (l : BdLabel) : BdLabel :=
  { l with seg := List.replicate a.Q.length false ++ l.seg, rep := l.rep.extendB a }

theorem vecSubset_replicate_false : ∀ n : Nat,
    vecSubset (List.replicate n false) (List.replicate n false) = true
  | 0 => rfl
  | n + 1 => by
      have ih := vecSubset_replicate_false n
      unfold vecSubset at ih ⊢
      rw [List.replicate_succ, List.zip_cons_cons, List.all_cons, ih]
      rfl

theorem vecSubset_append (u v u' v' : List Bool) (h : u.length = v.length) :
    vecSubset (u ++ u') (v ++ v') = (vecSubset u v && vecSubset u' v') := by
  unfold vecSubset
  rw [List.zip_append h, List.all_append]

/-- A label of the factor `a` crosses the seam exactly when its
    representative survives. -/
theorem bdLabel_extendA_valid_iff (a b : CodeState) (seams : List (Sector × List Nat))
    (l : BdLabel) (hl : l.validIn a = true) :
    (l.extendA b).validIn (glueState a b seams) = true ↔
      SurvivesA a b seams l.rep.sector l.rep.vec := by
  unfold BdLabel.validIn at hl
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, LogRep.validIn_iff] at hl
  obtain ⟨⟨hseg, hrl, hlog⟩, hsub⟩ := hl
  have hlen : l.rep.vec.length = l.seg.length := hrl.trans hseg.symm
  unfold BdLabel.validIn
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, LogRep.validIn_iff]
  show ((l.seg ++ List.replicate b.Q.length false).length = (glueState a b seams).Q.length ∧
      (l.rep.vec ++ List.replicate b.Q.length false).length = (glueState a b seams).Q.length ∧
      isLogicalBool (glueState a b seams) l.rep.sector
        (l.rep.vec ++ List.replicate b.Q.length false) = true) ∧
      vecSubset (l.rep.vec ++ List.replicate b.Q.length false)
        (l.seg ++ List.replicate b.Q.length false) = true ↔ _
  rw [vecSubset_append _ _ _ _ hlen, hsub, vecSubset_replicate_false, glueState_Q]
  simp only [List.length_append, List.length_replicate, hseg, hrl, Bool.and_self, and_true,
    true_and]
  exact ⟨fun h => ⟨hrl, hlog, h⟩, fun h => h.2.2⟩

theorem bdLabel_extendB_valid_iff (a b : CodeState) (seams : List (Sector × List Nat))
    (l : BdLabel) (hl : l.validIn b = true) :
    (l.extendB a).validIn (glueState a b seams) = true ↔
      SurvivesB a b seams l.rep.sector l.rep.vec := by
  unfold BdLabel.validIn at hl
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, LogRep.validIn_iff] at hl
  obtain ⟨⟨hseg, hrl, hlog⟩, hsub⟩ := hl
  unfold BdLabel.validIn
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, LogRep.validIn_iff]
  show ((List.replicate a.Q.length false ++ l.seg).length = (glueState a b seams).Q.length ∧
      (List.replicate a.Q.length false ++ l.rep.vec).length = (glueState a b seams).Q.length ∧
      isLogicalBool (glueState a b seams) l.rep.sector
        (List.replicate a.Q.length false ++ l.rep.vec) = true) ∧
      vecSubset (List.replicate a.Q.length false ++ l.rep.vec)
        (List.replicate a.Q.length false ++ l.seg) = true ↔ _
  rw [vecSubset_append _ _ _ _ rfl, hsub, vecSubset_replicate_false, glueState_Q]
  simp only [List.length_append, List.length_replicate, hseg, hrl, Bool.and_self, and_true,
    true_and]
  exact ⟨fun h => ⟨hrl, hlog, h⟩, fun h => h.2.2⟩

end CodeCalculus
