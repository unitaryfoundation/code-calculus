import CodeCalculus.AdmissibleSeamFamily
import CodeCalculus.WitnessFields
import CodeCalculus.Gate6Exact

/-!
# `E-GLUE`: extracted Theorem 4 / Claim 7.4 derivation and transition equivalence (issue #536)

Closes the remaining algebraic and state-soundness gaps in the Lean
mechanization of `spec/OPERATIONAL_SEMANTICS.md` §4.31 and §4.33, and records
the exact boundary between what is mechanized in the CSS state model and the
geometric gap that stays outside it:

1. **Transition equivalence and state soundness (§4.31, `OBL-WELL-FORMEDNESS-PRESERVATION`).**
   `eval_glueCommand_eq_glueState`, `wf_glueState_of_eval_glueCommand`, and
   `evalExpr_glue_iff_evalTerm_glueCommand` prove that the binary state-expression
   constructor `StateExpr.glue` (rule `EvalExpr.glue`) and the closed-term
   decomposition `⟨glueCommand seams, directSum (base a) (base b)⟩` are
   logically equivalent on every pair of well-formed factors, deriving
   `EncodingWellFormed (glueState a b seams)` from step-by-step seam
   admissibility and `stateK (directSumState a b) = stateK (glueState a b seams) + seams.length`.
2. **Re-exposure quantity `w_re = +∞` and Theorem 4 / Claim 7.4 in `Option Nat` (§4.31, §4.33 Claim 1).**
   `reExposedVectors_eq_nil` and `wRe?_eq_none` prove that no re-exposed
   `σ`-logical exists on any admitted glue (`w_re,σ = +∞`), and
   `glue_theorem4_lower_bound` / `glue_exactDistance?_ge_min` mechanize the
   Theorem 4 / Claim 7.4 lower bound in `Option Nat` (handling infinite factor
   distances without the `|Q| + 1` sentinel mismatch across namespaces).
3. **Remaining pieces of §4.33 Claim 2.**
   `phiSeam_congr` and `phiSeam_linear` mechanize Step 1 (well-definedness on
   factor classes modulo the full factor spans and `F₂`-linearity of `φ_t`);
   `glue_exactDistance?_ge_add_of_no_pure_survivor` mechanizes Consequence (iii)
   (when no pure factor logical survives, `d_σ(C) ≥ d_σ(C_A) + d_σ(C_B)`); and
   `glue_universal_min_equality_false` refutes the candidate universal equality
   `d_Z(C) = min(d_Z(C_A), d_Z(C_B))` (issue #398) on the pinned §4.33
   counterexample.
4. **End-to-end `Option Nat` / `glueField` / `Gate6Exact` bridge (§4.31, §4.32).**
   `admissibleSeam_exactDistance?_eq_min` proves
   `exactDistance? σ (glueState a b seams) = minOpt (exactDistance? σ a) (exactDistance? σ b)`
   directly from `AdmissibleSeam` without `HasMinLogical` or `LogField`;
   `admissible_carriesMin_glueField` and `admissible_family_glueField_exact`
   connect `AdmissibleSeam` to the §1a normalized transport `glueField`
   (`WitnessFields.lean`); and `glue_expr_sound_exact_of_admissible` /
   `glue_term_sound_exact_of_admissible` discharge the `hcert` equality premise
   of `Gate6Exact.lean` from `AdmissibleSeam` for `σ = Sector.Z`.

**Recorded gap (substrate boundary, not an unfinished algebra lemma).**
The implication from the geometric §2e seam certificate (identical planar move
words `w(c_A) = w(c_B)` over `{U,D,L,R}^*`) to `AdmissibleSeam` is not
mechanized and is not derivable from the CSS state model `C = (Q, X, Z, pres,
used)`, which carries no lattice geometry or move words (`design/ADMISSIBLE_SEAM_FAMILY.md`
§4, `spec/OPERATIONAL_SEMANTICS.md` §4.31). Likewise, shared-interface Theorem 4
(overlapping qubits where `w_re,σ` may be finite) is outside the admitted
disjoint-namespace `E-GLUE` transition.
-/

namespace CodeCalculus

/-! ## 1. Transition equivalence (`EvalExpr.glue` ↔ `glueCommand`) and state soundness -/

/-- Iterative addition of seam checks to a state, matching `glueCommand`. -/
def addSeamStates (s : CodeState) : List (Sector × List Nat) → CodeState
  | [] => s
  | (σ, sup) :: rest => addSeamStates (addState s σ sup) rest

/-- `glueCommand` uses only `skip`, `addStab`, and `seq`, so it is graft-free. -/
theorem glueCommand_graftFree : ∀ seams : List (Sector × List Nat), GraftFree (glueCommand seams)
  | [] => trivial
  | (_, _) :: rest => ⟨trivial, glueCommand_graftFree rest⟩

theorem addSeamStates_eq : ∀ (seams : List (Sector × List Nat)) (s : CodeState),
    addSeamStates s seams =
      { Q := s.Q
      , rows := s.rows ++ (seams.zip (mintFresh s.used seams.length)).map
          (fun (si, id) => ({ id := id, sector := si.1, support := si.2 } : Row))
      , used := s.used ++ mintFresh s.used seams.length }
  | [], s => by
      simp [addSeamStates, mintFresh]
  | (σ, sup) :: rest, s => by
      simp only [addSeamStates]
      rw [addSeamStates_eq rest (addState s σ sup)]
      simp only [addState, List.length_cons, mintFresh, List.zip_cons_cons, List.map_cons,
        List.append_assoc, List.singleton_append]

/-- Running `addSeamStates` from `directSumState a b` produces `glueState a b seams`. -/
theorem addSeamStates_directSum (a b : CodeState) (seams : List (Sector × List Nat)) :
    addSeamStates (directSumState a b) seams = glueState a b seams := by
  rw [addSeamStates_eq]
  rfl

/-- Evaluating `glueCommand seams` from `s` lands on `addSeamStates s seams`
    and satisfies the capacity premise for all minted seam identifiers. -/
theorem eval_glueCommand_eq_addSeamStates :
    ∀ (seams : List (Sector × List Nat)) {s s' : CodeState},
      Eval (glueCommand seams) s s' →
      s' = addSeamStates s seams ∧ MintsWithinCapacity s.used seams.length
  | [], s, s', h => by
      refine ⟨eval_skip_eq h, ?_⟩
      intro id hid
      simp [mintFresh] at hid
  | (σ, sup) :: rest, s, s', h => by
      cases h with
      | seq h1 h2 =>
          cases h1 with
          | add _ _ _ _ _ hs1 hcap1 =>
              subst hs1
              obtain ⟨heq, hcap2⟩ := eval_glueCommand_eq_addSeamStates rest h2
              refine ⟨heq, ?_⟩
              intro id hid
              simp only [List.length_cons, mintFresh, List.mem_cons] at hid
              rcases hid with rfl | hid'
              · exact hcap1
              · exact hcap2 id hid'

/-- Evaluating `glueCommand seams` from `directSumState a b` yields `glueState a b seams`. -/
theorem eval_glueCommand_eq_glueState {a b s' : CodeState} {seams : List (Sector × List Nat)}
    (h : Eval (glueCommand seams) (directSumState a b) s') :
    s' = glueState a b seams := by
  have heq := (eval_glueCommand_eq_addSeamStates seams h).1
  rw [addSeamStates_directSum] at heq
  exact heq

/-- Output well-formedness of `E-GLUE` derived from well-formed disjoint factors
    and step-by-step seam admissibility (§4.31, `OBL-WELL-FORMEDNESS-PRESERVATION`). -/
theorem wf_glueState_of_eval_glueCommand {a b s' : CodeState}
    {seams : List (Sector × List Nat)}
    (hwfA : EncodingWellFormed a) (hwfB : EncodingWellFormed b)
    (hQ : DisjointList a.Q b.Q) (hU : DisjointList a.used b.used)
    (h : Eval (glueCommand seams) (directSumState a b) s') :
    EncodingWellFormed (glueState a b seams) := by
  have hwf0 := directSum_wellFormed a b hwfA hwfB hQ hU
  have hwf' := wf_of_eval (glueCommand_graftFree seams) h hwf0
  rw [eval_glueCommand_eq_glueState h] at hwf'
  exact hwf'

/-- Forward direction of the transition equivalence: a `glueCommand` evaluation
    on `directSumState a b` yields an `EvalExpr.glue` derivation. -/
theorem evalExpr_glue_of_eval_glueCommand {a b s' : CodeState}
    {seams : List (Sector × List Nat)}
    (hwfA : EncodingWellFormed a) (hwfB : EncodingWellFormed b)
    (hQ : DisjointList a.Q b.Q) (hU : DisjointList a.used b.used)
    (h : Eval (glueCommand seams) (directSumState a b) s') :
    EvalExpr (StateExpr.glue (StateExpr.base a) (StateExpr.base b) seams) s' := by
  have hcap := (eval_glueCommand_eq_addSeamStates seams h).2
  have heq := eval_glueCommand_eq_glueState h
  have hwf := wf_glueState_of_eval_glueCommand hwfA hwfB hQ hU h
  subst heq
  exact EvalExpr.glue hQ hU hwf hcap (EvalExpr.base a) (EvalExpr.base b)

/-- Reverse direction (generalized over any well-formed starting state `s`):
    joint well-formedness of `addSeamStates s seams` plus capacity implies the
    step-by-step `Eval (glueCommand seams)` derivation. -/
theorem eval_glueCommand_of_wf :
    ∀ (seams : List (Sector × List Nat)) (s : CodeState),
      EncodingWellFormed s →
      EncodingWellFormed (addSeamStates s seams) →
      MintsWithinCapacity s.used seams.length →
      Eval (glueCommand seams) s (addSeamStates s seams)
  | [], s, _, _, _ => Eval.skip s
  | (σ, sup) :: rest, s, hwf, hwf', hcap => by
      let t := addSeamStates s ((σ, sup) :: rest)
      let newRow : Row := ⟨canonicalMint s.used, σ, sup⟩
      let tailRows : List Row :=
        (rest.zip (mintFresh (s.used ++ [canonicalMint s.used]) rest.length)).map
          (fun (si, id) => ({ id := id, sector := si.1, support := si.2 } : Row))
      have htQ : t.Q = s.Q := by
        show (addSeamStates s ((σ, sup) :: rest)).Q = s.Q
        rw [addSeamStates_eq]
      have htRows : t.rows = s.rows ++ [newRow] ++ tailRows := by
        show (addSeamStates s ((σ, sup) :: rest)).rows = _
        rw [addSeamStates_eq]
        simp only [List.length_cons, mintFresh, List.zip_cons_cons, List.map_cons,
          newRow, tailRows, List.append_assoc, List.singleton_append]
      have hnewMem : newRow ∈ t.rows := by
        rw [htRows]
        exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))
      have hsMem : ∀ r ∈ s.rows, r ∈ t.rows := fun r hr => by
        rw [htRows]
        exact List.mem_append_left _ (List.mem_append_left _ hr)
      have hsub : supportSubset sup s.Q := by
        intro q hq
        have h1 := List.all_eq_true.mp (List.all_eq_true.mp hwf'.2.2.2.1 newRow hnewMem) q hq
        rw [htQ] at h1
        exact List.contains_iff_mem.mp h1
      have hnodup : sup.Nodup := by
        have h1 := List.all_eq_true.mp hwf'.2.2.2.2.1 newRow hnewMem
        exact of_decide_eq_true h1
      have hsorted : sup.Pairwise (· ≤ ·) := by
        have h1 := List.all_eq_true.mp hwf'.2.2.2.2.2.1 newRow hnewMem
        exact of_decide_eq_true h1
      have hcomm : ∀ row ∈ s.rows, row.sector = oppositeSector σ →
          supportIntersectionSize sup row.support % 2 = 0 := by
        intro row hrow hsec
        have hI1 : I1 t := hwf'.2.2.2.2.2.2.1
        cases hσ : σ with
        | X =>
            rw [hσ] at hsec
            exact hI1 newRow row hnewMem (hsMem row hrow) hσ hsec
        | Z =>
            rw [hσ] at hsec
            have hrowNd : row.support.Nodup :=
              of_decide_eq_true (List.all_eq_true.mp hwf.2.2.2.2.1 row hrow)
            rw [supportIntersectionSize_comm sup row.support hnodup hrowNd]
            exact hI1 row newRow (hsMem row hrow) hnewMem hsec hσ
      have hspan : ¬ inSpanRows s.Q (sectorRows s σ) (rowVector s.Q newRow) := by
        have hI2 : IndependentGenerator newRow.id t := hwf'.2.2.2.2.2.2.2 newRow hnewMem
        have hind := (independentGenerator_iff t hwf'.2.1 newRow hnewMem).mp hI2
        rw [htQ] at hind
        have hcfresh : canonicalMint s.used ∉ s.used :=
          fun hc => canonicalMint_fresh s.used (List.contains_iff_mem.mpr hc)
        have hne : ∀ r ∈ s.rows, r.id ≠ canonicalMint s.used := by
          intro r hr hid
          apply hcfresh
          rw [← hid]
          exact ids_subset_used_of_wf hwf r hr
        have hsub1 : (sectorRows s σ).Sublist
            (s.rows.filter (fun r' => r'.sector = newRow.sector ∧ r'.id ≠ newRow.id)) := by
          apply filter_sublist_filter_of_imp
          intro r hr hsec
          have hsec' : r.sector = σ := of_decide_eq_true hsec
          exact decide_eq_true ⟨hsec', hne r hr⟩
        have hsub2 : (s.rows.filter (fun r' => r'.sector = newRow.sector ∧ r'.id ≠ newRow.id)).Sublist
            (t.rows.filter (fun r' => r'.sector = newRow.sector ∧ r'.id ≠ newRow.id)) := by
          rw [htRows]
          rw [List.filter_append, List.filter_append]
          exact (List.sublist_append_left _ _).trans (List.sublist_append_left _ _)
        intro hin
        exact hind (inSpanRows_of_sublist s.Q (hsub1.trans hsub2) _ hin)
      have hcap1 : canonicalMint s.used < totalIdentifiers := by
        apply hcap (canonicalMint s.used)
        simp [mintFresh]
      have hadd : Eval (Command.addStab σ sup) s (addState s σ sup) :=
        Eval.add hsub hnodup hsorted hcomm hspan rfl hcap1
      have hwf1 : EncodingWellFormed (addState s σ sup) :=
        wf_addState s σ sup hwf hsub hnodup hsorted hcomm hspan
      have hcapRest : MintsWithinCapacity (addState s σ sup).used rest.length := by
        intro id hid
        apply hcap id
        simp only [List.length_cons, mintFresh, List.mem_cons]
        exact Or.inr hid
      have hrest := eval_glueCommand_of_wf rest (addState s σ sup) hwf1 hwf' hcapRest
      exact Eval.seq hadd hrest

/-- Equivalence of the two `E-GLUE` transition representations on every pair of
    well-formed factors: the binary state-expression constructor `StateExpr.glue`
    evaluates to `s'` iff the closed term
    `⟨glueCommand seams, directSum (base a) (base b)⟩` evaluates to `s'`. -/
theorem evalExpr_glue_iff_evalTerm_glueCommand {a b s' : CodeState}
    {seams : List (Sector × List Nat)}
    (hwfA : EncodingWellFormed a) (hwfB : EncodingWellFormed b) :
    EvalExpr (StateExpr.glue (StateExpr.base a) (StateExpr.base b) seams) s' ↔
      EvalTerm { command := glueCommand seams
               , expr := StateExpr.directSum (StateExpr.base a) (StateExpr.base b) } s' := by
  constructor
  · intro h
    cases h with
    | glue hQ hU hwf hcap h1 h2 =>
        cases h1
        cases h2
        have hwf0 := directSum_wellFormed a b hwfA hwfB hQ hU
        have hwf' : EncodingWellFormed (addSeamStates (directSumState a b) seams) := by
          rw [addSeamStates_directSum]
          exact hwf
        have hcmd := eval_glueCommand_of_wf seams (directSumState a b) hwf0 hwf' hcap
        rw [addSeamStates_directSum] at hcmd
        exact EvalTerm.eval (EvalExpr.directSum hQ hU (EvalExpr.base a) (EvalExpr.base b)) hcmd
  · intro h
    cases h with
    | eval hexpr hcmd =>
        cases hexpr with
        | directSum hQ hU h1 h2 =>
            cases h1
            cases h2
            exact evalExpr_glue_of_eval_glueCommand hwfA hwfB hQ hU hcmd

/-- Logical-dimension drop along `glueCommand`: each admitted seam check drops
    `stateK` by 1 (§4.2, §4.31). -/
theorem stateK_addSeamStates :
    ∀ (seams : List (Sector × List Nat)) {s s' : CodeState},
      EncodingWellFormed s →
      Eval (glueCommand seams) s s' →
      stateK s = stateK s' + seams.length
  | [], s, s', _, h => by
      rw [eval_skip_eq h, List.length_nil, Nat.add_zero]
  | (σ, sup) :: rest, s, s', hwf, h => by
      cases h with
      | seq h1 h2 =>
          cases h1 with
          | add hsub hnodup hsorted hcomm hspan hs1 _ =>
              subst hs1
              have hwf1 : EncodingWellFormed (addState s σ sup) :=
                wf_addState s σ sup hwf hsub hnodup hsorted hcomm hspan
              have hk1 : stateK s = stateK (addState s σ sup) + 1 :=
                stateK_addState s hwf.1 σ sup hspan (ranksFit_of_wf _ hwf1)
              have hk2 := stateK_addSeamStates rest hwf1 h2
              rw [hk1, hk2, List.length_cons]
              omega

/-- Exact logical-dimension drop for `E-GLUE` relative to `directSumState a b`:
    `k(a ⊕ b) = k(glueState a b seams) + seams.length`. -/
theorem stateK_glueState_add_seams {a b s' : CodeState}
    {seams : List (Sector × List Nat)}
    (hwfA : EncodingWellFormed a) (hwfB : EncodingWellFormed b)
    (hQ : DisjointList a.Q b.Q) (hU : DisjointList a.used b.used)
    (h : Eval (glueCommand seams) (directSumState a b) s') :
    stateK (directSumState a b) = stateK (glueState a b seams) + seams.length := by
  have hwf0 := directSum_wellFormed a b hwfA hwfB hQ hU
  have hk := stateK_addSeamStates seams hwf0 h
  rw [eval_glueCommand_eq_glueState h] at hk
  exact hk

/-! ## 2. Re-exposure quantity `w_re = +∞` and Theorem 4 / Claim 7.4 in `Option Nat` -/

/-- A `σ`-logical of the glued state is *re-exposed* (§4.33) when both of its
    factor restrictions lie in their respective factor stabilizer spans. -/
def isReExposedBool (a b : CodeState) (seams : List (Sector × List Nat))
    (σ : Sector) (v : List Bool) : Bool :=
  isLogicalBool (glueState a b seams) σ v &&
    inSpanRowsBool a.Q (sectorRows a σ) (v.take a.Q.length) &&
    inSpanRowsBool b.Q (sectorRows b σ) (v.drop a.Q.length)

/-- All re-exposed `σ`-logicals of the glued state. -/
def reExposedVectors (a b : CodeState) (seams : List (Sector × List Nat))
    (σ : Sector) : List (List Bool) :=
  (allBoolLists (glueState a b seams).Q.length).filter (isReExposedBool a b seams σ)

/-- The re-exposure minimum `w_re,σ(C; C_A, C_B)` in `Option Nat` (`none` for `+∞`). -/
def wRe? (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector) : Option Nat :=
  minWeight? (reExposedVectors a b seams σ)

/-- Claim 1 of §4.33: on every admitted glue, no re-exposed `σ`-logical exists. -/
theorem reExposedVectors_eq_nil (a b : CodeState) (seams : List (Sector × List Nat))
    (σ : Sector)
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q) :
    reExposedVectors a b seams σ = [] := by
  cases h : reExposedVectors a b seams σ with
  | nil => rfl
  | cons v vs =>
      exfalso
      have hv : v ∈ reExposedVectors a b seams σ := by
        rw [h]; exact List.mem_cons_self ..
      unfold reExposedVectors isReExposedBool at hv
      rw [List.mem_filter, exact_mem_allBoolLists, Bool.and_eq_true, Bool.and_eq_true] at hv
      obtain ⟨hvlen, ⟨hlog, hspanA⟩, hspanB⟩ := hv
      rcases glue_claim1 a b seams σ v hQ hsupA hsupB hvlen hlog with hlogA | hlogB
      · have hnotA := ((isLogicalBool_iff_prop a σ _).mp hlogA).2
        exact hnotA ((exact_inSpanRowsBool_iff a.Q (sectorRows a σ) _).mp hspanA)
      · have hnotB := ((isLogicalBool_iff_prop b σ _).mp hlogB).2
        exact hnotB ((exact_inSpanRowsBool_iff b.Q (sectorRows b σ) _).mp hspanB)

/-- `w_re,σ(C; C_A, C_B) = +∞` (`none`) on every admitted glue (§4.33 Claim 1,
    `OBL-GLUE-RE-EXPOSURE`). -/
theorem wRe?_eq_none (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q) :
    wRe? a b seams σ = none := by
  unfold wRe?
  rw [reExposedVectors_eq_nil a b seams σ hQ hsupA hsupB]
  rfl

/-- `Option Nat` lower bound (Claim 1 of §4.33 / §4.31 repair):
    `min(d_σ(C_A), d_σ(C_B)) ≤ d_σ(C)` in `Option Nat`, handling `+∞` (`none`)
    faithfully even when one or both factors have no `σ`-logical. -/
theorem glue_exactDistance?_ge_min (a b : CodeState) (seams : List (Sector × List Nat))
    (σ : Sector)
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q) :
    leOpt (minOpt (exactDistance? σ a) (exactDistance? σ b))
      (exactDistance? σ (glueState a b seams)) := by
  cases hC : exactDistance? σ (glueState a b seams) with
  | none => exact leOpt_none _
  | some d =>
      obtain ⟨v, hv, hwv⟩ := minWeight?_attained (logicalVectors (glueState a b seams) σ) d hC
      have hvlen := length_of_mem_logicalVectors hv
      have hlog := ((mem_logicalVectors_iff _ σ v).mp hv).2
      have hsplit : v.take a.Q.length ++ v.drop a.Q.length = v := List.take_append_drop ..
      have hwsum : weight v = weight (v.take a.Q.length) + weight (v.drop a.Q.length) := by
        rw [← weight_append_eq, hsplit]
      rcases glue_claim1 a b seams σ v hQ hsupA hsupB hvlen hlog with hA | hB
      · have hvA : v.take a.Q.length ∈ logicalVectors a σ :=
          (mem_logicalVectors_iff a σ _).mpr
            ⟨by rw [List.length_take, hvlen, glueState_Q, List.length_append]; omega, hA⟩
        obtain ⟨dA, hdA, hleA⟩ := exactDistance?_le_of_mem hvA
        have hleMin : leOpt (minOpt (exactDistance? σ a) (exactDistance? σ b)) (some dA) := by
          rw [hdA]
          cases exactDistance? σ b with
          | none => exact Nat.le_refl dA
          | some dB => exact Nat.min_le_left dA dB
        exact leOpt_trans hleMin (show leOpt (some dA) (some d) by show dA ≤ d; omega)
      · have hvB : v.drop a.Q.length ∈ logicalVectors b σ :=
          (mem_logicalVectors_iff b σ _).mpr
            ⟨by rw [List.length_drop, hvlen, glueState_Q, List.length_append]; omega, hB⟩
        obtain ⟨dB, hdB, hleB⟩ := exactDistance?_le_of_mem hvB
        have hleMin : leOpt (minOpt (exactDistance? σ a) (exactDistance? σ b)) (some dB) := by
          rw [hdB]
          cases exactDistance? σ a with
          | none => exact Nat.le_refl dB
          | some dA => exact Nat.min_le_right dA dB
        exact leOpt_trans hleMin (show leOpt (some dB) (some d) by show dB ≤ d; omega)

/-- Extracted Theorem 4 / Claim 7.4 re-exposure bound in `Option Nat`:
    `min(min(d_σ(C_A), d_σ(C_B)), w_re,σ) ≤ d_σ(C)`, reducing to
    `glue_exactDistance?_ge_min` via `wRe?_eq_none`. -/
theorem glue_theorem4_lower_bound (a b : CodeState) (seams : List (Sector × List Nat))
    (σ : Sector)
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q) :
    leOpt (minOpt (minOpt (exactDistance? σ a) (exactDistance? σ b)) (wRe? a b seams σ))
      (exactDistance? σ (glueState a b seams)) := by
  rw [wRe?_eq_none a b seams σ hQ hsupA hsupB]
  cases h : minOpt (exactDistance? σ a) (exactDistance? σ b) with
  | none =>
      have hge := glue_exactDistance?_ge_min a b seams σ hQ hsupA hsupB
      rw [h] at hge
      exact hge
  | some m =>
      have hge := glue_exactDistance?_ge_min a b seams σ hQ hsupA hsupB
      rw [h] at hge
      exact hge

/-! ## 3. Remaining pieces of §4.33 Claim 2: Step 1 (`φ_t`), Consequence (iii), and #398 refutation -/

/-- The `F₂`-valued seam functional `φ_t(v_A, v_B) = ⟨v_A, t_A⟩ + ⟨v_B, t_B⟩ mod 2`
    of §4.33 Claim 2 Step 1. -/
def phiSeam (a b : CodeState) (t : Row) (vA vB : List Bool) : Nat :=
  (dotPar vA (rowVector a.Q t) + dotPar vB (rowVector b.Q t)) % 2

theorem phiSeam_zero (a b : CodeState) (t : Row) :
    phiSeam a b t (List.replicate a.Q.length false) (List.replicate b.Q.length false) = 0 := by
  unfold phiSeam
  rw [dotPar_replicate_false_left, dotPar_replicate_false_left]

/-- Claim 2 Step 1 (linearity): `φ_t` is linear over `F₂` in its pair argument. -/
theorem phiSeam_linear (a b : CodeState) (t : Row) (uA uB wA wB : List Bool)
    (hA : uA.length = wA.length) (hB : uB.length = wB.length) :
    phiSeam a b t (xorVec uA wA) (xorVec uB wB) =
      (phiSeam a b t uA uB + phiSeam a b t wA wB) % 2 := by
  unfold phiSeam
  have h1 := dotPar_xorVec_left uA wA (rowVector a.Q t) hA
  have h2 := dotPar_xorVec_left uB wB (rowVector b.Q t) hB
  omega

/-- Helper: every factor `σ`-row has even overlap on `a.Q` with every `τ`-seam
    check of a well-formed glued state. -/
private theorem factorA_row_even_seam (a b : CodeState) (seams : List (Sector × List Nat))
    (σ : Sector) (hwf : EncodingWellFormed (glueState a b seams))
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (r : Row) (hr : r ∈ sectorRows a σ)
    (t : Row) (ht : t ∈ seamSectorRows a b seams (oppositeSector σ)) :
    dotPar (rowVector a.Q t) (rowVector a.Q r) % 2 = 0 := by
  have hrMem : r ∈ (glueState a b seams).rows := by
    rw [glueState_rows]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_filter.mp hr).1)
  have htMem : t ∈ (glueState a b seams).rows := by
    rw [glueState_rows]
    exact List.mem_append_right _ (List.mem_filter.mp ht).1
  have hrSec : r.sector = σ := of_decide_eq_true (List.mem_filter.mp hr).2
  have htSec : t.sector = oppositeSector σ := of_decide_eq_true (List.mem_filter.mp ht).2
  have heven := dotPar_rowVector_even_of_wf hwf htMem hrMem (by
    rw [hrSec, htSec, oppositeSector_involutive])
  have hsplit : dotPar (rowVector (glueState a b seams).Q t)
      (rowVector (glueState a b seams).Q r) =
      dotPar (rowVector a.Q t) (rowVector a.Q r) := by
    rw [glueState_Q, rowVector_append a.Q b.Q t, rowVector_append a.Q b.Q r,
      dotPar_append_eq (rowVector a.Q t) (rowVector a.Q r) (rowVector b.Q t) (rowVector b.Q r)
        ((rowVector_length a.Q t).trans (rowVector_length a.Q r).symm),
      rowVector_eq_replicate_of_disjoint b.Q r (factorA_misses_B hQ hsupA σ r hr),
      dotPar_replicate_false, Nat.add_zero]
  rw [← hsplit]
  exact heven

private theorem factorB_row_even_seam (a b : CodeState) (seams : List (Sector × List Nat))
    (σ : Sector) (hwf : EncodingWellFormed (glueState a b seams))
    (hQ : DisjointList a.Q b.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (r : Row) (hr : r ∈ sectorRows b σ)
    (t : Row) (ht : t ∈ seamSectorRows a b seams (oppositeSector σ)) :
    dotPar (rowVector b.Q t) (rowVector b.Q r) % 2 = 0 := by
  have hrMem : r ∈ (glueState a b seams).rows := by
    rw [glueState_rows]
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_filter.mp hr).1)
  have htMem : t ∈ (glueState a b seams).rows := by
    rw [glueState_rows]
    exact List.mem_append_right _ (List.mem_filter.mp ht).1
  have hrSec : r.sector = σ := of_decide_eq_true (List.mem_filter.mp hr).2
  have htSec : t.sector = oppositeSector σ := of_decide_eq_true (List.mem_filter.mp ht).2
  have heven := dotPar_rowVector_even_of_wf hwf htMem hrMem (by
    rw [hrSec, htSec, oppositeSector_involutive])
  have hsplit : dotPar (rowVector (glueState a b seams).Q t)
      (rowVector (glueState a b seams).Q r) =
      dotPar (rowVector b.Q t) (rowVector b.Q r) := by
    rw [glueState_Q, rowVector_append a.Q b.Q t, rowVector_append a.Q b.Q r,
      dotPar_append_eq (rowVector a.Q t) (rowVector a.Q r) (rowVector b.Q t) (rowVector b.Q r)
        ((rowVector_length a.Q t).trans (rowVector_length a.Q r).symm),
      rowVector_eq_replicate_of_disjoint a.Q r (factorB_misses_A hQ hsupB σ r hr),
      dotPar_replicate_false, Nat.zero_add]
  rw [← hsplit]
  exact heven

/-- Claim 2 Step 1 (well-definedness on factor classes): changing either
    representative within its factor class modulo the full factor stabilizer
    span leaves `φ_t` unchanged. -/
theorem phiSeam_congr (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (t : Row) (vA vB uA uB : List Bool)
    (hwf : EncodingWellFormed (glueState a b seams))
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (ht : t ∈ seamSectorRows a b seams (oppositeSector σ))
    (hlA : vA.length = a.Q.length) (hlB : vB.length = b.Q.length)
    (huA : uA ∈ classVectors a σ vA) (huB : uB ∈ classVectors b σ vB) :
    phiSeam a b t uA uB = phiSeam a b t vA vB := by
  rw [mem_classVectors_iff] at huA huB
  have hAeven : dotPar (xorVec uA vA) (rowVector a.Q t) % 2 = 0 := by
    rw [dotPar_comm]
    exact dotPar_even_of_inSpanRows a.Q (sectorRows a σ) (rowVector a.Q t) (xorVec uA vA) huA.2
      (fun r hr => factorA_row_even_seam a b seams σ hwf hQ hsupA r hr t ht)
  have hBeven : dotPar (xorVec uB vB) (rowVector b.Q t) % 2 = 0 := by
    rw [dotPar_comm]
    exact dotPar_even_of_inSpanRows b.Q (sectorRows b σ) (rowVector b.Q t) (xorVec uB vB) huB.2
      (fun r hr => factorB_row_even_seam a b seams σ hwf hQ hsupB r hr t ht)
  have hxA := dotPar_xorVec_left uA vA (rowVector a.Q t) (huA.1.trans hlA.symm)
  have hxB := dotPar_xorVec_left uB vB (rowVector b.Q t) (huB.1.trans hlB.symm)
  unfold phiSeam
  omega

/-- Consequence (iii) of §4.33 (restriction form): when no pure factor logical
    survives, every `σ`-logical of the glued state restricts to a `σ`-logical
    in *both* factors. -/
theorem glue_both_restrictions_logical_of_no_pure_survivor
    (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (v : List Bool)
    (hwf : EncodingWellFormed (glueState a b seams))
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (hnoA : ∀ u, ¬ SurvivesA a b seams σ u)
    (hnoB : ∀ u, ¬ SurvivesB a b seams σ u)
    (hv : v ∈ logicalVectors (glueState a b seams) σ) :
    v.take a.Q.length ∈ logicalVectors a σ ∧ v.drop a.Q.length ∈ logicalVectors b σ := by
  have hvl : v.length = a.Q.length + b.Q.length := by
    rw [length_of_mem_logicalVectors hv, glueState_Q, List.length_append]
  have hlA : (v.take a.Q.length).length = a.Q.length := by
    rw [List.length_take, hvl]; exact Nat.min_eq_left (Nat.le_add_right _ _)
  have hlB : (v.drop a.Q.length).length = b.Q.length := by
    rw [List.length_drop, hvl, Nat.add_sub_cancel_left]
  have hlogC : isLogicalBool (glueState a b seams) σ
      (v.take a.Q.length ++ v.drop a.Q.length) = true := by
    rw [List.take_append_drop]
    exact ((mem_logicalVectors_iff _ σ v).mp hv).2
  have hKW := (glue_logical_iff a b seams σ _ _ hQ hsupA hsupB hlA hlB).mp hlogC
  have hNA := hKW.1.1
  have hNB := hKW.1.2.1
  have hnotW := hKW.2
  have hnotSpanA : ¬ inSpanRows a.Q (sectorRows a σ) (v.take a.Q.length) := by
    intro hspanA
    have hnotSpanB : ¬ inSpanRows b.Q (sectorRows b σ) (v.drop a.Q.length) := fun hspanB =>
      hnotW (glueW_of_factor_span a b seams σ _ _ hspanA hspanB)
    have h0mem : List.replicate a.Q.length false ∈ classVectors a σ (v.take a.Q.length) := by
      rw [mem_classVectors_iff, xorVec_replicate_false_left a.Q.length _ hlA]
      exact ⟨List.length_replicate .., hspanA⟩
    have hKW' := glueKW_congr a b seams σ (v.take a.Q.length) (v.drop a.Q.length)
      (List.replicate a.Q.length false) (v.drop a.Q.length)
      hwf hQ hsupA hsupB hlA hlB h0mem (self_mem_classVectors b σ _ hlB) hKW
    have hlogB : isLogicalBool b σ (v.drop a.Q.length) = true :=
      (isLogicalBool_iff_prop b σ _).mpr ⟨hNB, hnotSpanB⟩
    have hlogC' := (glue_logical_iff a b seams σ _ _ hQ hsupA hsupB
      (List.length_replicate ..) hlB).mpr hKW'
    exact hnoB (v.drop a.Q.length) ⟨hlB, hlogB, hlogC'⟩
  have hnotSpanB : ¬ inSpanRows b.Q (sectorRows b σ) (v.drop a.Q.length) := by
    intro hspanB
    have h0mem : List.replicate b.Q.length false ∈ classVectors b σ (v.drop a.Q.length) := by
      rw [mem_classVectors_iff, xorVec_replicate_false_left b.Q.length _ hlB]
      exact ⟨List.length_replicate .., hspanB⟩
    have hKW' := glueKW_congr a b seams σ (v.take a.Q.length) (v.drop a.Q.length)
      (v.take a.Q.length) (List.replicate b.Q.length false)
      hwf hQ hsupA hsupB hlA hlB (self_mem_classVectors a σ _ hlA) h0mem hKW
    have hlogA : isLogicalBool a σ (v.take a.Q.length) = true :=
      (isLogicalBool_iff_prop a σ _).mpr ⟨hNA, hnotSpanA⟩
    have hlogC' := (glue_logical_iff a b seams σ _ _ hQ hsupA hsupB
      hlA (List.length_replicate ..)).mpr hKW'
    exact hnoA (v.take a.Q.length) ⟨hlA, hlogA, hlogC'⟩
  exact ⟨(mem_logicalVectors_iff a σ _).mpr ⟨hlA, (isLogicalBool_iff_prop a σ _).mpr ⟨hNA, hnotSpanA⟩⟩,
    (mem_logicalVectors_iff b σ _).mpr ⟨hlB, (isLogicalBool_iff_prop b σ _).mpr ⟨hNB, hnotSpanB⟩⟩⟩

/-- Addition on `Option Nat` (`+∞` absorbs). -/
def addOpt : Option Nat → Option Nat → Option Nat
  | some a, some b => some (a + b)
  | _, _ => none

/-- Consequence (iii) of §4.33: when no pure factor logical survives,
    `d_σ(C) ≥ d_σ(C_A) + d_σ(C_B)`. -/
theorem glue_exactDistance?_ge_add_of_no_pure_survivor
    (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (hwf : EncodingWellFormed (glueState a b seams))
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (hnoA : ∀ u, ¬ SurvivesA a b seams σ u)
    (hnoB : ∀ u, ¬ SurvivesB a b seams σ u) :
    leOpt (addOpt (exactDistance? σ a) (exactDistance? σ b))
      (exactDistance? σ (glueState a b seams)) := by
  cases hC : exactDistance? σ (glueState a b seams) with
  | none => exact leOpt_none _
  | some d =>
      obtain ⟨v, hv, hwv⟩ := minWeight?_attained (logicalVectors (glueState a b seams) σ) d hC
      obtain ⟨hvA, hvB⟩ := glue_both_restrictions_logical_of_no_pure_survivor
        a b seams σ v hwf hQ hsupA hsupB hnoA hnoB hv
      obtain ⟨dA, hdA, hleA⟩ := exactDistance?_le_of_mem hvA
      obtain ⟨dB, hdB, hleB⟩ := exactDistance?_le_of_mem hvB
      have hsplit : v.take a.Q.length ++ v.drop a.Q.length = v := List.take_append_drop ..
      have hwsum : weight v = weight (v.take a.Q.length) + weight (v.drop a.Q.length) := by
        rw [← weight_append_eq, hsplit]
      rw [hdA, hdB]
      show dA + dB ≤ d
      omega

/-- Exact distances on the §4.33 / issue #398 counterexample: two one-row
    two-qubit factors glued by a four-qubit `X` seam check satisfy
    `d_Z(A) = 1`, `d_Z(B) = 1`, and `d_Z(glue) = 2`. -/
theorem glue_counterexample_distances :
    exactDistance? Sector.Z (zPair 0 0) = some 1 ∧
      exactDistance? Sector.Z (zPair 2 1) = some 1 ∧
      exactDistance? Sector.Z (glueState (zPair 0 0) (zPair 2 1) [(Sector.X, [0, 1, 2, 3])]) =
        some 2 := by
  decide

/-- Issue #398 settlement in Lean: the universal candidate seam-distance claim
    `d_Z(glue) = min(d_Z(A), d_Z(B))` over all well-formed glues is `false`. -/
theorem glue_universal_min_equality_false :
    ¬ (∀ a b seams,
        EncodingWellFormed a → EncodingWellFormed b →
        DisjointList a.Q b.Q → DisjointList a.used b.used →
        EncodingWellFormed (glueState a b seams) →
        exactDistance? Sector.Z (glueState a b seams) =
          minOpt (exactDistance? Sector.Z a) (exactDistance? Sector.Z b)) := by
  intro hall
  have hA : EncodingWellFormed (zPair 0 0) := (wellFormedBool_iff _).mp (by decide)
  have hB : EncodingWellFormed (zPair 2 1) := (wellFormedBool_iff _).mp (by decide)
  have hQ : DisjointList (zPair 0 0).Q (zPair 2 1).Q := by decide
  have hU : DisjointList (zPair 0 0).used (zPair 2 1).used := by decide
  have hwf : EncodingWellFormed (glueState (zPair 0 0) (zPair 2 1) [(Sector.X, [0, 1, 2, 3])]) :=
    (wellFormedBool_iff _).mp (by decide)
  have heq := hall (zPair 0 0) (zPair 2 1) [(Sector.X, [0, 1, 2, 3])] hA hB hQ hU hwf
  obtain ⟨hdA, hdB, hdC⟩ := glue_counterexample_distances
  rw [hdA, hdB, hdC] at heq
  cases heq

/-! ## 4. `Option Nat` survival, `glueField` bridge, and `Gate6Exact` discharge -/

/-- Instance-wise equality in `Option Nat` from a surviving `a`-logical of
    weight `min(d_σ(a), d_σ(b))`. -/
theorem glue_exactDistance?_eq_min_of_survivesA
    (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector) (u : List Bool)
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (h : SurvivesA a b seams σ u)
    (hw : some (weight u) = minOpt (exactDistance? σ a) (exactDistance? σ b)) :
    exactDistance? σ (glueState a b seams) = minOpt (exactDistance? σ a) (exactDistance? σ b) := by
  obtain ⟨hu, _, hlogC⟩ := h
  have hmem : u ++ List.replicate b.Q.length false ∈ logicalVectors (glueState a b seams) σ :=
    (mem_logicalVectors_iff _ σ _).mpr
      ⟨by rw [glueState_Q, List.length_append, List.length_append, hu, List.length_replicate],
        hlogC⟩
  obtain ⟨m, hm, hle⟩ := exactDistance?_le_of_mem hmem
  rw [weight_append_eq, weight_replicate_false, Nat.add_zero] at hle
  have hge := glue_exactDistance?_ge_min a b seams σ hQ hsupA hsupB
  rw [← hw, hm] at hge ⊢
  exact congrArg some (Nat.le_antisymm hle hge)

/-- Instance-wise equality in `Option Nat` from a surviving `b`-logical of
    weight `min(d_σ(a), d_σ(b))`. -/
theorem glue_exactDistance?_eq_min_of_survivesB
    (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector) (u : List Bool)
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (h : SurvivesB a b seams σ u)
    (hw : some (weight u) = minOpt (exactDistance? σ a) (exactDistance? σ b)) :
    exactDistance? σ (glueState a b seams) = minOpt (exactDistance? σ a) (exactDistance? σ b) := by
  obtain ⟨hu, _, hlogC⟩ := h
  have hmem : List.replicate a.Q.length false ++ u ∈ logicalVectors (glueState a b seams) σ :=
    (mem_logicalVectors_iff _ σ _).mpr
      ⟨by rw [glueState_Q, List.length_append, List.length_append, hu, List.length_replicate],
        hlogC⟩
  obtain ⟨m, hm, hle⟩ := exactDistance?_le_of_mem hmem
  rw [weight_append_eq, weight_replicate_false, Nat.zero_add] at hle
  have hge := glue_exactDistance?_ge_min a b seams σ hQ hsupA hsupB
  rw [← hw, hm] at hge ⊢
  exact congrArg some (Nat.le_antisymm hle hge)

/-- `AdmissibleSeam` gives the exact `Option Nat` distance equality
    `exactDistance? σ (glueState a b seams) = minOpt (exactDistance? σ a) (exactDistance? σ b)`
    directly — with no `HasMinLogical` assumption and no `LogField` premise. -/
theorem admissibleSeam_exactDistance?_eq_min
    (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (hQ : DisjointList a.Q b.Q)
    (hsupA : ∀ row ∈ a.rows, supportSubset row.support a.Q)
    (hsupB : ∀ row ∈ b.rows, supportSubset row.support b.Q)
    (hadm : AdmissibleSeam a b seams σ) :
    exactDistance? σ (glueState a b seams) =
      minOpt (exactDistance? σ a) (exactDistance? σ b) := by
  have hge := glue_exactDistance?_ge_min a b seams σ hQ hsupA hsupB
  cases hA : exactDistance? σ a with
  | none =>
      cases hB : exactDistance? σ b with
      | none =>
          rw [hA, hB] at hge
          cases hC : exactDistance? σ (glueState a b seams) with
          | none => rfl
          | some d => rw [hC] at hge; exact False.elim hge
      | some dB =>
          obtain ⟨u, hu, hwu⟩ := minWeight?_attained (logicalVectors b σ) dB hB
          have huLen := length_of_mem_logicalVectors hu
          have huLog := ((mem_logicalVectors_iff b σ u).mp hu).2
          have hdB : exactDistance σ b = dB := by
            rw [exactDistance_eq_getD, hB]; rfl
          have hsurv := hadm.2 u huLen huLog (hwu.trans hdB.symm)
          have hres := glue_exactDistance?_eq_min_of_survivesB a b seams σ u hQ hsupA hsupB hsurv
            (by rw [hA, hB, hwu]; rfl)
          rw [hA, hB] at hres
          exact hres
  | some dA =>
      cases hB : exactDistance? σ b with
      | none =>
          obtain ⟨u, hu, hwu⟩ := minWeight?_attained (logicalVectors a σ) dA hA
          have huLen := length_of_mem_logicalVectors hu
          have huLog := ((mem_logicalVectors_iff a σ u).mp hu).2
          have hdA : exactDistance σ a = dA := by
            rw [exactDistance_eq_getD, hA]; rfl
          have hsurv := hadm.1 u huLen huLog (hwu.trans hdA.symm)
          have hres := glue_exactDistance?_eq_min_of_survivesA a b seams σ u hQ hsupA hsupB hsurv
            (by rw [hA, hB, hwu]; rfl)
          rw [hA, hB] at hres
          exact hres
      | some dB =>
          rcases Nat.le_total dA dB with hle | hgeAB
          · obtain ⟨u, hu, hwu⟩ := minWeight?_attained (logicalVectors a σ) dA hA
            have huLen := length_of_mem_logicalVectors hu
            have huLog := ((mem_logicalVectors_iff a σ u).mp hu).2
            have hdA : exactDistance σ a = dA := by
              rw [exactDistance_eq_getD, hA]; rfl
            have hsurv := hadm.1 u huLen huLog (hwu.trans hdA.symm)
            have hres := glue_exactDistance?_eq_min_of_survivesA a b seams σ u hQ hsupA hsupB hsurv
              (by rw [hA, hB, hwu]; exact congrArg some (Nat.min_eq_left hle).symm)
            rw [hA, hB] at hres
            exact hres
          · obtain ⟨u, hu, hwu⟩ := minWeight?_attained (logicalVectors b σ) dB hB
            have huLen := length_of_mem_logicalVectors hu
            have huLog := ((mem_logicalVectors_iff b σ u).mp hu).2
            have hdB : exactDistance σ b = dB := by
              rw [exactDistance_eq_getD, hB]; rfl
            have hsurv := hadm.2 u huLen huLog (hwu.trans hdB.symm)
            have hres := glue_exactDistance?_eq_min_of_survivesB a b seams σ u hQ hsupA hsupB hsurv
              (by rw [hA, hB, hwu]; exact congrArg some (Nat.min_eq_right hgeAB).symm)
            rw [hA, hB] at hres
            exact hres

/-- Family-level `Option Nat` equality under `AdmissibleSeam`: needs no
    `HasMinLogical` and no `LogField` hypotheses. -/
theorem admissible_family_exactDistance?_eq_min
    (F : GlueInstance → Prop) (σ : Sector)
    (hQ : ∀ i, F i → DisjointList i.a.Q i.b.Q)
    (hsupA : ∀ i, F i → ∀ row ∈ i.a.rows, supportSubset row.support i.a.Q)
    (hsupB : ∀ i, F i → ∀ row ∈ i.b.rows, supportSubset row.support i.b.Q)
    (hadm : ∀ i, F i → AdmissibleSeam i.a i.b i.seams σ) :
    ∀ i, F i → exactDistance? σ (glueState i.a i.b i.seams) =
      minOpt (exactDistance? σ i.a) (exactDistance? σ i.b) :=
  fun i hi =>
    admissibleSeam_exactDistance?_eq_min i.a i.b i.seams σ
      (hQ i hi) (hsupA i hi) (hsupB i hi) (hadm i hi)

/-- Bridge to the §1a normalized transport `glueField` (`WitnessFields.lean`):
    an admissible seam on regular factors with logicals gives a minimum-weight
    entry in `glueField`. -/
theorem admissible_carriesMin_glueField
    (a b : CodeState) (seams : List (Sector × List Nat)) (σ : Sector)
    (logA logB : List LogRep)
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
    ∃ e ∈ glueField a b seams logA logB,
      e.sector = σ ∧ weight e.vec = min (exactDistance σ a) (exactDistance σ b) :=
  (carriesMin_glueField_iff a b seams σ logA logB hQ hsupA hsupB hA hB).mpr
    (admissible_carriesMin a b seams σ logA logB hQ hsupA hsupB hwfA hwfB hwf
      hA hB hCA hCB hTA hTB hadm hAmin hBmin)

/-- Family-level bridge through the §1a normalized transport `glueField`. -/
theorem admissible_family_glueField_exact
    (F : GlueInstance → Prop) (σ : Sector)
    (hF : ∀ i, F i → i.Regular σ)
    (hadm : ∀ i, F i → AdmissibleSeam i.a i.b i.seams σ)
    (hAmin : ∀ i, F i → HasMinLogical i.a σ)
    (hBmin : ∀ i, F i → HasMinLogical i.b σ) :
    ∀ i, F i →
      (∃ e ∈ glueField i.a i.b i.seams i.logA i.logB,
        e.sector = σ ∧ weight e.vec = min (exactDistance σ i.a) (exactDistance σ i.b)) ∧
      exactDistance? σ (glueState i.a i.b i.seams) =
        minOpt (exactDistance? σ i.a) (exactDistance? σ i.b) := by
  intro i hi
  obtain ⟨hwfA, hwfB, hwf, hQ, hA, hB, hCA, hCB, hTA, hTB⟩ := hF i hi
  have hsupA := supports_subset_of_wf hwfA
  have hsupB := supports_subset_of_wf hwfB
  exact ⟨admissible_carriesMin_glueField i.a i.b i.seams σ i.logA i.logB
      hQ hsupA hsupB hwfA hwfB hwf hA hB hCA hCB hTA hTB (hadm i hi) (hAmin i hi) (hBmin i hi),
    admissibleSeam_exactDistance?_eq_min i.a i.b i.seams σ hQ hsupA hsupB (hadm i hi)⟩

/-- End-to-end discharge of `glue_expr_sound_exact` (`Gate6Exact.lean`) from
    `AdmissibleSeam` for `σ = Sector.Z`: the `hcert` equality premise is proved
    from `AdmissibleSeam`, so the certified `glueLedger` is sound for `exactDist`
    with `AdmissibleSeam` as the single remaining boundary hypothesis. -/
theorem glue_expr_sound_exact_of_admissible
    {sA sB s' : CodeState} {seams : List (Sector × List Nat)}
    (hwfA : EncodingWellFormed sA) (hwfB : EncodingWellFormed sB)
    (h : EvalExpr (StateExpr.glue (StateExpr.base sA) (StateExpr.base sB) seams) s')
    (hadm : AdmissibleSeam sA sB seams Sector.Z)
    (A B : DistanceLedger) (hA : LedgerSound (exactDist sA) A)
    (hB : LedgerSound (exactDist sB) B) :
    LedgerSound (exactDist s') (glueLedger A B true) := by
  have hcert : true = true → (exactDist s').z = minOpt (exactDist sA).z (exactDist sB).z := by
    intro _
    cases h with
    | glue hQ _ _ _ h1 h2 =>
        cases h1
        cases h2
        show exactDistOpt Sector.Z (glueState sA sB seams) =
          minOpt (exactDistOpt Sector.Z sA) (exactDistOpt Sector.Z sB)
        rw [exactDistOpt_eq_exactDistance?, exactDistOpt_eq_exactDistance?,
          exactDistOpt_eq_exactDistance?]
        exact admissibleSeam_exactDistance?_eq_min sA sB seams Sector.Z
          hQ (supports_subset_of_wf hwfA) (supports_subset_of_wf hwfB) hadm
  exact glue_expr_sound_exact hwfA hwfB h A B hA hB true hcert

/-- The same end-to-end discharge on the closed term
    `⟨glueCommand seams, directSum (base sA) (base sB)⟩`. -/
theorem glue_term_sound_exact_of_admissible
    {sA sB s' : CodeState} {seams : List (Sector × List Nat)}
    (hwfA : EncodingWellFormed sA) (hwfB : EncodingWellFormed sB)
    (h : EvalTerm { command := glueCommand seams
                  , expr := StateExpr.directSum (StateExpr.base sA) (StateExpr.base sB) } s')
    (hadm : AdmissibleSeam sA sB seams Sector.Z)
    (A B : DistanceLedger) (hA : LedgerSound (exactDist sA) A)
    (hB : LedgerSound (exactDist sB) B) :
    LedgerSound (exactDist s') (glueLedger A B true) :=
  glue_expr_sound_exact_of_admissible hwfA hwfB
    ((evalExpr_glue_iff_evalTerm_glueCommand hwfA hwfB).mpr h) hadm A B hA hB

end CodeCalculus
