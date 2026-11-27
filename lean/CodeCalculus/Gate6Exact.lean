import CodeCalculus.ExactPeel
import CodeCalculus.ExactGraft
import CodeCalculus.SplitHadamard

namespace CodeCalculus

/-!
# The Gate 6 transformers for the exact distance, and `E-GLUE` as a constructor

`gate6_interval_soundness` (`Gate6Soundness.lean`) proves the §4.32
transformers sound over an uninterpreted distance reading, one hypothesis
per distance relation. This module instantiates it with the exact sector
distance read in `Option Nat` (`exactDist`) and discharges every hypothesis
the development can prove for it:

* the full-distance identity (`exactDist_full`) and the `k = 0` reading
  (`exactDist_k0`, `ExactPeel.lean`);
* the §4.5 and §4.3 laws of deletion and addition (`exactDist_delete`,
  `exactDist_add`), from row-space monotonicity on a fixed namespace
  (`exactDist_le_of_rows_sublist`);
* the §4.26 rebase identity and the §4.27 sector exchange
  (`exactDist_rebaseState`, `exactDist_swapState`);
* the three §4.28 peel relations (`exactDist_peel_relations`).

* the two unpriced §4.13 graft relations (`exactDist_graft_relations`,
  `ExactGraft.lean`);
* the §4.30 addition law of `E-EXTEND` with `Δ = ∅` (`exactDist_extend_nil`):
  the extension appends rows and re-sorts the namespace, and
  the exact distance does not depend on the order of the namespace
  (`exactDist_perm`, `ExactPermute.lean`).

`gate6_interval_soundness_exact` is the result. It has no distance
hypothesis left: its only hypotheses are the priced inputs of `Hyp`.

`E-GLUE` as a constructor. `Gate6Soundness.lean` reads an `E-GLUE`
evaluation as the closed term `⟨glueCommand seams, directSum A B⟩`. The
language also has the constructor `StateExpr.glue` with the rule
`EvalExpr.glue` and the update `glueState`. `glue_state_transformer_sound`
proves `glueLedger` sound on that update for any distance reading that
satisfies the direct-sum law at the two factors and the seam's lower-bound
relation, and `glue_expr_sound` reads it off an `EvalExpr.glue` evaluation.
For the exact distance both are theorems: the seam relation
(`exactDist_glueState_ge`: the glued display contains the direct sum's rows
over the same namespace) and the direct-sum law on well-formed factors with
disjoint namespaces (`exactDist_directSumState`, `ExactDirectSum.lean`).
`glue_expr_sound_exact` therefore keeps two hypotheses, each a
premise by decision and not a missing proof:

* the seam certificate's equality `hcert`, the cell hypothesis of
  `spec/JUDGMENT_LAYER.md` §2e. It is an input of the certified cell, used
  only when `certified = true`, and the derivation attempt recorded at
  `spec/OPERATIONAL_SEMANTICS.md` §4 left it a hypothesis;
* the well-formedness of the two factors. The glued state's own
  well-formedness is a premise of the rule `EvalExpr.glue`
  (`evalExpr_glue_implies_wf`), as the §4.31 card states it, and is not
  derived from the factors.

The direct-sum law is false for the exact distance without disjoint
namespaces and rows supported on their own namespace, so the
measure-generic statements (`directSum_sound`, `glue_transformer_sound`,
`glue_term_sound` of `Gate6Soundness.lean`) keep their unconditional
hypothesis `hdirect`, which no instance for `exactDist` satisfies. The
statements of this module take the law at the two factors instead.

`E-GLUE` as a closed term. `glue_transformer_sound_at` is
`glue_transformer_sound` with the direct-sum law asked at the two factors
only. Its exact-distance instance is `glue_transformer_sound_exact`, read
off the closed term `⟨glueCommand seams, directSum (base A) (base B)⟩` as
`glue_term_sound_exact`: the direct-sum law is `exactDist_directSumState`
on the two well-formed factors with disjoint namespaces, and the addition
law is `exactDist_add`. As for the constructor, the seam certificate's
equality `hcert` stays the cell hypothesis, and the uncertified cell has no
hypothesis about a distance (`glue_term_sound_exact_uncertified`).
-/

/-! ## Row-space monotonicity of `exactDist` on a fixed namespace -/

/-- Fewer displayed rows over the same namespace give no larger exact
    distance, in each sector and in full. -/
theorem exactDist_le_of_rows_sublist {s t : CodeState} (hQ : s.Q = t.Q)
    (hsub : s.rows.Sublist t.rows) :
    leOpt (exactDist s).full (exactDist t).full ∧ leOpt (exactDist s).x (exactDist t).x ∧
      leOpt (exactDist s).z (exactDist t).z := by
  have hsec : ∀ σ, leOpt (exactDistOpt σ s) (exactDistOpt σ t) := by
    intro σ
    apply leOpt_exactDistOpt_of_le (by rw [hQ])
    exact exactDistance_le_of_spanLE t s σ hQ
      (spanLE_of_sublist _ (hsub.filter _)) (spanLE_of_sublist _ (hsub.filter _))
  exact ⟨minOpt_monotone (hsec Sector.X) (hsec Sector.Z), hsec Sector.X, hsec Sector.Z⟩

/-- The §4.5 law for the exact distance: deletion raises no distance. -/
theorem exactDist_delete {r : Nat} {s s' : CodeState} (h : Eval (Command.delete r) s s') :
    leOpt (exactDist s').full (exactDist s).full ∧ leOpt (exactDist s').x (exactDist s).x ∧
      leOpt (exactDist s').z (exactDist s).z := by
  rw [eval_delete_eq h]
  exact exactDist_le_of_rows_sublist rfl List.filter_sublist

/-- The §4.3 law for the exact distance: addition lowers no distance. -/
theorem exactDist_add {sector : Sector} {support : List Nat} {s s' : CodeState}
    (h : Eval (Command.addStab sector support) s s') :
    leOpt (exactDist s).full (exactDist s').full ∧ leOpt (exactDist s).x (exactDist s').x ∧
      leOpt (exactDist s).z (exactDist s').z := by
  rw [eval_add_eq h]
  exact exactDist_le_of_rows_sublist rfl (List.sublist_append_left _ _)

/-! ## `E-EXTEND` with `Δ = ∅` -/

theorem eraseDups_of_nodup : ∀ l : List Nat, l.Nodup → l.eraseDups = l
  | [], _ => rfl
  | a :: as, h => by
      rw [List.nodup_cons] at h
      have hf : as.filter (fun b => !b == a) = as := by
        apply List.filter_eq_self.mpr
        intro b hb
        rw [Bool.not_eq_true', beq_eq_false_iff_ne]
        intro hba
        exact h.1 (by rw [← hba]; exact hb)
      rw [List.eraseDups_cons, hf, eraseDups_of_nodup as h.2]

/-- The §4.30 addition law of `E-EXTEND` with `Δ = ∅` for the exact
    distance: the extension appends rows over a reordering of the
    namespace, so no distance falls. -/
theorem exactDist_extend_nil {adds : List (Sector × List Nat)} {s s' : CodeState}
    (hwf : EncodingWellFormed s) (h : Eval (Command.extend [] adds) s s') :
    leOpt (exactDist s).full (exactDist s').full ∧ leOpt (exactDist s).x (exactDist s').x ∧
      leOpt (exactDist s).z (exactDist s').z := by
  have hs' : s' = extendState s [] adds := by
    cases h with
    | extend _ hs' _ _ => exact hs'
  subst hs'
  have hperm : (extendState s [] adds).Q.Perm s.Q := by
    show (sortNat ((s.Q ++ []).eraseDups)).Perm s.Q
    rw [List.append_nil, eraseDups_of_nodup s.Q hwf.1]
    exact sortNat_perm s.Q
  have hreorder : exactDist
      ({ Q := (extendState s [] adds).Q, rows := s.rows, used := s.used } : CodeState) =
      exactDist s :=
    exactDist_perm (s := s)
      (t := { Q := (extendState s [] adds).Q, rows := s.rows, used := s.used }) rfl hperm hwf.1
  rw [← hreorder]
  exact exactDist_le_of_rows_sublist rfl (List.sublist_append_left _ _)

/-! ## The combined statement for the exact distance -/

/-- `gate6_interval_soundness` for the exact distance. Every distance
    relation is a theorem: the full-distance identity, the `k = 0` reading,
    and the deletion, addition, graft, rebase, Hadamard, peel, and `Δ = ∅`
    extension relations. The priced inputs of `Hyp` are the only hypotheses
    left. -/
theorem gate6_interval_soundness_exact
  (H : Hyp)
  : ∀ (L : DistanceLedger) (s s' : CodeState) (m : Command),
      EncodingWellFormed s →
      Eval m s s' →
      HypTrue exactDist H m s s' →
      LedgerSound (exactDist s) L →
      LedgerSound (exactDist s') (propagateGate6K m s s' L H) :=
  gate6_interval_soundness exactDist exactDist_full exactDist_k0
    (fun _ _ _ _ h => exactDist_delete h)
    (fun _ _ _ _ _ h => exactDist_add h)
    (fun _ _ _ _ _ hwf h => exactDist_graft_relations hwf h)
    (fun σ M s s' hwf h => by
      cases h with
      | rebase _ hok hs' _ =>
          subst hs'
          exact exactDist_rebaseState s σ M hwf.1 hok)
    (fun T s s' _ h hT hp => by
      cases h with
      | hadamardSplit hsub _ _ _ _ _ =>
          exact absurd hp (not_coversQ_of_properSubset hsub)
      | hadamard _ hs' _ =>
          subst hs'
          cases T with
          | nil => exact absurd rfl hT
          | cons a T' => exact exactDist_swapState s)
    (fun T s s' hwf h hT hnc => by
      cases h with
      | hadamard hg _ _ =>
          rcases hg with hp | hn
          · exact absurd (coversQ_of_perm hp) hnc
          · exact absurd hn hT
      | hadamardSplit _ hguard hs' _ _ _ =>
          subst hs'
          exact exactDist_splitHadamardState s hwf.1 T hguard)
    (fun _ _ _ _ _ hwf h => exactDist_peel_relations hwf h)
    (fun _ _ _ hwf h => exactDist_extend_nil hwf h) H

/-! ## `E-GLUE` as the constructor `StateExpr.glue` -/

/-- `directSum_sound` with the direct-sum law taken at the two states, not
    for every pair. -/
theorem directSum_sound_at (δ : CodeState → ExactDist) (A B : DistanceLedger)
    (sA sB : CodeState)
    (hdirect : δ (directSumState sA sB) =
        ExactDist.mk (minOpt (δ sA).full (δ sB).full)
                    (minOpt (δ sA).x (δ sB).x)
                    (minOpt (δ sA).z (δ sB).z))
    (hA : LedgerSound (δ sA) A) (hB : LedgerSound (δ sB) B) :
    LedgerSound (δ (directSumState sA sB)) (directSumLedger A B) := by
  rcases hA with ⟨hAf, hAx, hAz⟩
  rcases hB with ⟨hBf, hBx, hBz⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [congrArg ExactDist.full hdirect]
    exact ⟨minOpt_monotone hAf.1 hBf.1, minOpt_monotone hAf.2 hBf.2⟩
  · rw [congrArg ExactDist.x hdirect]
    exact ⟨minOpt_monotone hAx.1 hBx.1, minOpt_monotone hAx.2 hBx.2⟩
  · rw [congrArg ExactDist.z hdirect]
    exact ⟨minOpt_monotone hAz.1 hBz.1, minOpt_monotone hAz.2 hBz.2⟩

/-- `glueLedger` is sound on the constructor's update `glueState`, for any
    distance reading that satisfies the direct-sum law at the two factors
    and does not fall from the direct sum to the glued state. -/
theorem glue_state_transformer_sound (δ : CodeState → ExactDist)
    {sA sB : CodeState} {seams : List (Sector × List Nat)}
    (hdirect : δ (directSumState sA sB) =
        ExactDist.mk (minOpt (δ sA).full (δ sB).full)
                    (minOpt (δ sA).x (δ sB).x)
                    (minOpt (δ sA).z (δ sB).z))
    (hseam : leOpt (δ (directSumState sA sB)).full (δ (glueState sA sB seams)).full ∧
      leOpt (δ (directSumState sA sB)).x (δ (glueState sA sB seams)).x ∧
      leOpt (δ (directSumState sA sB)).z (δ (glueState sA sB seams)).z)
    (A B : DistanceLedger) (hA : LedgerSound (δ sA) A) (hB : LedgerSound (δ sB) B)
    (certified : Bool)
    (hcert : certified = true →
      (δ (glueState sA sB seams)).z = minOpt (δ sA).z (δ sB).z) :
    LedgerSound (δ (glueState sA sB seams)) (glueLedger A B certified) := by
  obtain ⟨hsf, hsx, hsz⟩ := directSum_sound_at δ A B sA sB hdirect hA hB
  obtain ⟨hf, hx, hz⟩ := hseam
  refine ⟨⟨leOpt_trans hsf.1 hf, leOpt_none _⟩, ⟨leOpt_trans hsx.1 hx, leOpt_none _⟩,
    ⟨leOpt_trans hsz.1 hz, ?_⟩⟩
  cases certified with
  | false => exact leOpt_none _
  | true =>
      show leOpt (δ (glueState sA sB seams)).z (minOpt A.z.upper B.z.upper)
      rw [hcert rfl]
      exact minOpt_monotone hA.2.2.2 hB.2.2.2

/-- The same, read off an `EvalExpr.glue` evaluation of two base factors.
    The direct-sum law is asked of well-formed states on disjoint
    namespaces, which is where the rule's premises put the two factors. -/
theorem glue_expr_sound (δ : CodeState → ExactDist)
    (hdirect : ∀ a b, EncodingWellFormed a → EncodingWellFormed b → DisjointList a.Q b.Q →
      δ (directSumState a b) =
        ExactDist.mk (minOpt (δ a).full (δ b).full)
                    (minOpt (δ a).x (δ b).x)
                    (minOpt (δ a).z (δ b).z))
    (hseam : ∀ a b seams,
      leOpt (δ (directSumState a b)).full (δ (glueState a b seams)).full ∧
      leOpt (δ (directSumState a b)).x (δ (glueState a b seams)).x ∧
      leOpt (δ (directSumState a b)).z (δ (glueState a b seams)).z)
    {sA sB s' : CodeState} {seams : List (Sector × List Nat)}
    (hwfA : EncodingWellFormed sA) (hwfB : EncodingWellFormed sB)
    (h : EvalExpr (StateExpr.glue (StateExpr.base sA) (StateExpr.base sB) seams) s')
    (A B : DistanceLedger) (hA : LedgerSound (δ sA) A) (hB : LedgerSound (δ sB) B)
    (certified : Bool)
    (hcert : certified = true → (δ s').z = minOpt (δ sA).z (δ sB).z) :
    LedgerSound (δ s') (glueLedger A B certified) := by
  cases h with
  | glue hQ hU hwf _hcap h1 h2 =>
      cases h1
      cases h2
      exact glue_state_transformer_sound δ (hdirect sA sB hwfA hwfB hQ) (hseam sA sB seams)
        A B hA hB certified hcert

/-- For the exact distance the seam relation is a theorem: the glued display
    is the direct sum's display with the seam rows appended, over the same
    namespace. -/
theorem exactDist_glueState_ge (a b : CodeState) (seams : List (Sector × List Nat)) :
    leOpt (exactDist (directSumState a b)).full (exactDist (glueState a b seams)).full ∧
      leOpt (exactDist (directSumState a b)).x (exactDist (glueState a b seams)).x ∧
      leOpt (exactDist (directSumState a b)).z (exactDist (glueState a b seams)).z :=
  exactDist_le_of_rows_sublist rfl (List.sublist_append_left _ _)

/-- `E-GLUE` for the exact distance, from an `EvalExpr.glue` evaluation of
    two well-formed factors: the seam relation and the direct-sum law are
    discharged. The seam certificate's equality remains, as the cell
    hypothesis of `JUDGMENT_LAYER.md` §2e, used only when `certified` holds. -/
theorem glue_expr_sound_exact
    {sA sB s' : CodeState} {seams : List (Sector × List Nat)}
    (hwfA : EncodingWellFormed sA) (hwfB : EncodingWellFormed sB)
    (h : EvalExpr (StateExpr.glue (StateExpr.base sA) (StateExpr.base sB) seams) s')
    (A B : DistanceLedger) (hA : LedgerSound (exactDist sA) A)
    (hB : LedgerSound (exactDist sB) B) (certified : Bool)
    (hcert : certified = true → (exactDist s').z = minOpt (exactDist sA).z (exactDist sB).z) :
    LedgerSound (exactDist s') (glueLedger A B certified) :=
  glue_expr_sound exactDist
    (fun _ _ ha hb hQ => exactDist_directSumState (DirectSumCtx.ofWellFormed hQ ha hb))
    exactDist_glueState_ge hwfA hwfB h A B hA hB certified hcert

/-- The uncertified cell needs no hypothesis about a distance: from an
    `EvalExpr.glue` evaluation of two well-formed factors, the glued
    ledger's lower endpoints are sound for the exact distance. -/
theorem glue_expr_sound_exact_uncertified
    {sA sB s' : CodeState} {seams : List (Sector × List Nat)}
    (hwfA : EncodingWellFormed sA) (hwfB : EncodingWellFormed sB)
    (h : EvalExpr (StateExpr.glue (StateExpr.base sA) (StateExpr.base sB) seams) s')
    (A B : DistanceLedger) (hA : LedgerSound (exactDist sA) A)
    (hB : LedgerSound (exactDist sB) B) :
    LedgerSound (exactDist s') (glueLedger A B false) :=
  glue_expr_sound_exact hwfA hwfB h A B hA hB false (fun hc => absurd hc Bool.false_ne_true)

/-! ## `E-GLUE` as a closed term, for the exact distance -/

/-- `glue_transformer_sound` with the direct-sum law taken at the two
    factors, not for every pair of states. -/
theorem glue_transformer_sound_at (δ : CodeState → ExactDist)
    {sA sB s' : CodeState} {seams : List (Sector × List Nat)}
    (hdirect : δ (directSumState sA sB) =
        ExactDist.mk (minOpt (δ sA).full (δ sB).full)
                    (minOpt (δ sA).x (δ sB).x)
                    (minOpt (δ sA).z (δ sB).z))
    (hadd : ∀ sector support s s', EncodingWellFormed s →
      Eval (Command.addStab sector support) s s' →
      leOpt (δ s).full (δ s').full ∧ leOpt (δ s).x (δ s').x ∧ leOpt (δ s).z (δ s').z)
    (hwfA : EncodingWellFormed sA) (hwfB : EncodingWellFormed sB)
    (hQ : DisjointList sA.Q sB.Q) (hU : DisjointList sA.used sB.used)
    (h : Eval (glueCommand seams) (directSumState sA sB) s')
    (A B : DistanceLedger) (hA : LedgerSound (δ sA) A) (hB : LedgerSound (δ sB) B)
    (certified : Bool)
    (hcert : certified = true → (δ s').z = minOpt (δ sA).z (δ sB).z) :
    LedgerSound (δ s') (glueLedger A B certified) := by
  have hwf0 : EncodingWellFormed (directSumState sA sB) :=
    directSum_wellFormed sA sB hwfA hwfB hQ hU
  obtain ⟨hsf, hsx, hsz⟩ := directSum_sound_at δ A B sA sB hdirect hA hB
  obtain ⟨hf, hx, hz⟩ := glue_lower_le δ hadd seams hwf0 h
  refine ⟨⟨leOpt_trans hsf.1 hf, leOpt_none _⟩, ⟨leOpt_trans hsx.1 hx, leOpt_none _⟩,
    ⟨leOpt_trans hsz.1 hz, ?_⟩⟩
  cases certified with
  | false => exact leOpt_none _
  | true =>
      show leOpt (δ s').z (minOpt A.z.upper B.z.upper)
      rw [hcert rfl]
      exact minOpt_monotone hA.2.2.2 hB.2.2.2

/-- The exact-distance instance of `glue_transformer_sound`: the direct-sum
    law holds at two well-formed factors on disjoint namespaces, and no
    exact distance falls along an addition. The seam certificate's equality
    remains, as the cell hypothesis of `JUDGMENT_LAYER.md` §2e, used only
    when `certified` holds. -/
theorem glue_transformer_sound_exact
    {sA sB s' : CodeState} {seams : List (Sector × List Nat)}
    (hwfA : EncodingWellFormed sA) (hwfB : EncodingWellFormed sB)
    (hQ : DisjointList sA.Q sB.Q) (hU : DisjointList sA.used sB.used)
    (h : Eval (glueCommand seams) (directSumState sA sB) s')
    (A B : DistanceLedger) (hA : LedgerSound (exactDist sA) A)
    (hB : LedgerSound (exactDist sB) B) (certified : Bool)
    (hcert : certified = true → (exactDist s').z = minOpt (exactDist sA).z (exactDist sB).z) :
    LedgerSound (exactDist s') (glueLedger A B certified) :=
  glue_transformer_sound_at exactDist
    (exactDist_directSumState (DirectSumCtx.ofWellFormed hQ hwfA hwfB))
    (fun _ _ _ _ _ hadd => exactDist_add hadd)
    hwfA hwfB hQ hU h A B hA hB certified hcert

/-- The same, read off the closed term
    `⟨glueCommand seams, directSum (base A) (base B)⟩`, whose `EvalExpr`
    premises are the disjointness conditions of §4.31. -/
theorem glue_term_sound_exact
    {sA sB s' : CodeState} {seams : List (Sector × List Nat)}
    (hwfA : EncodingWellFormed sA) (hwfB : EncodingWellFormed sB)
    (h : EvalTerm { command := glueCommand seams
                  , expr := StateExpr.directSum (StateExpr.base sA) (StateExpr.base sB) } s')
    (A B : DistanceLedger) (hA : LedgerSound (exactDist sA) A)
    (hB : LedgerSound (exactDist sB) B) (certified : Bool)
    (hcert : certified = true → (exactDist s').z = minOpt (exactDist sA).z (exactDist sB).z) :
    LedgerSound (exactDist s') (glueLedger A B certified) := by
  cases h with
  | eval hexpr heval =>
      cases hexpr with
      | directSum hQ hU h1 h2 =>
          cases h1
          cases h2
          exact glue_transformer_sound_exact hwfA hwfB hQ hU heval A B hA hB certified hcert

/-- The uncertified cell on the closed term needs no hypothesis about a
    distance. -/
theorem glue_term_sound_exact_uncertified
    {sA sB s' : CodeState} {seams : List (Sector × List Nat)}
    (hwfA : EncodingWellFormed sA) (hwfB : EncodingWellFormed sB)
    (h : EvalTerm { command := glueCommand seams
                  , expr := StateExpr.directSum (StateExpr.base sA) (StateExpr.base sB) } s')
    (A B : DistanceLedger) (hA : LedgerSound (exactDist sA) A)
    (hB : LedgerSound (exactDist sB) B) :
    LedgerSound (exactDist s') (glueLedger A B false) :=
  glue_term_sound_exact hwfA hwfB h A B hA hB false (fun hc => absurd hc Bool.false_ne_true)

end CodeCalculus
