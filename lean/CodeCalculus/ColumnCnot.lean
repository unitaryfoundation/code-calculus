import CodeCalculus.ExpandedSoundness

namespace CodeCalculus

/-!
# `C-COLUMN-CNOT` mechanization (`spec/OPERATIONAL_SEMANTICS.md` §4.42; issue #657)

Mechanizes structural properties, positive and refusal instances, skip/sequencing
laws, and a worked `TermModels` soundness derivation for `Command.cnotSwap`
(`C-COLUMN-CNOT`). All theorems are choice-free (`propext`, `Quot.sound` only).

Note: `Eval.cnotSwap` carries `EncodingWellFormed s'` as a premise (matching
the non-rebase Gate 6 transitions), so `wf_of_eval_all` and `instCnotSwapWF`
restate that premise and `eval_cnotSwap_k` relies on it; preservation of I1–I5
under an invertible column map `U` is hand-derived in §4.42 and not mechanized
here.
-/

theorem cnotSwapState_Q (s : CodeState) (U : List (List Bool)) :
    (cnotSwapState s U).Q = s.Q := rfl

theorem cnotSwapState_used (s : CodeState) (U : List (List Bool)) :
    (cnotSwapState s U).used = s.used := rfl

theorem cnotSwapState_rows_length (s : CodeState) (U : List (List Bool)) :
    (cnotSwapState s U).rows.length = s.rows.length := by
  show (s.rows.map (cnotSwapRow s.Q U)).length = s.rows.length
  exact List.length_map _

theorem cnotSwapState_ids (s : CodeState) (U : List (List Bool)) :
    (cnotSwapState s U).rows.map Row.id = s.rows.map Row.id := by
  simp only [cnotSwapState, List.map_map]
  rfl

/-- Primitive determinism (`OBL-PRIMITIVE-DETERMINISM`) for `C-COLUMN-CNOT`. -/
theorem eval_cnotSwap_unique {U : List (List Bool)} {s t1 t2 : CodeState}
    (h1 : Eval (Command.cnotSwap U) s t1) (h2 : Eval (Command.cnotSwap U) s t2) :
    t1 = t2 :=
  eval_unique h1 h2

/-- Left skip identity (`OBL-SKIP-IDENTITY`) for `C-COLUMN-CNOT`. -/
theorem eval_cnotSwap_skip_left {U : List (List Bool)} {s t : CodeState} :
    Eval (Command.seq Command.skip (Command.cnotSwap U)) s t ↔
      Eval (Command.cnotSwap U) s t := by
  constructor
  · intro h
    cases h with
    | seq h1 h2 =>
        cases h1
        exact h2
  · intro h
    exact Eval.seq (Eval.skip s) h

/-- Right skip identity (`OBL-SKIP-IDENTITY`) for `C-COLUMN-CNOT`. -/
theorem eval_cnotSwap_skip_right {U : List (List Bool)} {s t : CodeState} :
    Eval (Command.seq (Command.cnotSwap U) Command.skip) s t ↔
      Eval (Command.cnotSwap U) s t := by
  constructor
  · intro h
    cases h with
    | seq h1 h2 =>
        cases h2
        exact h1
  · intro h
    exact Eval.seq h (Eval.skip t)

/-- Sequence associativity (`OBL-SEQUENCE-ASSOCIATIVITY`) with `C-COLUMN-CNOT`. -/
theorem eval_cnotSwap_seq_assoc (U : List (List Bool)) (m2 m3 : Command)
    (s t : CodeState) :
    Eval (Command.seq (Command.seq (Command.cnotSwap U) m2) m3) s t ↔
      Eval (Command.seq (Command.cnotSwap U) (Command.seq m2 m3)) s t :=
  ⟨seq_assoc_fwd (Command.cnotSwap U) m2 m3 s t,
   seq_assoc_bwd (Command.cnotSwap U) m2 m3 s t⟩

/-! ### Positive and refusal instances (§4.42) -/

/-- A 2×2 invertible CNOT matrix over `F₂`. -/
def cnotMat2 : List (List Bool) :=
  [[true, true], [false, true]]

/-- A 2×2 SWAP permutation matrix over `F₂`. -/
def swapMat2 : List (List Bool) :=
  [[false, true], [true, false]]

/-- A singular 2×2 binary matrix over `F₂`. -/
def singularMat2 : List (List Bool) :=
  [[true, true], [true, true]]

/-- A non-square 2×3 binary matrix. -/
def wrongShapeMat : List (List Bool) :=
  [[true, false, false], [false, true, false]]

/-- Well-formed 2-qubit CSS state with X-row `{0}` and Z-row `{1}`. -/
def cnotExampleState : CodeState :=
  { Q := [0, 1]
  , rows := [⟨1, Sector.X, [0]⟩, ⟨2, Sector.Z, [1]⟩]
  , used := [1, 2] }

theorem cnotExampleState_wf : EncodingWellFormed cnotExampleState :=
  (wellFormedBool_iff _).mp (by decide)

/-- Positive instance: `cnotSwap(cnotMat2)` applies and raises both check
    weights from 1 to 2 while preserving well-formedness, `n`, `k`, and IDs. -/
theorem eval_cnotSwap_example :
    Eval (Command.cnotSwap cnotMat2) cnotExampleState
      (cnotSwapState cnotExampleState cnotMat2) :=
  Eval.cnotSwap (by unfold cnotMatrix_ok; decide) rfl ((wellFormedBool_iff _).mp (by decide))

/-- Positive instance: `cnotSwap(swapMat2)` exchanges qubits 0 and 1. -/
theorem eval_cnotSwap_swap_example :
    Eval (Command.cnotSwap swapMat2) cnotExampleState
      (cnotSwapState cnotExampleState swapMat2) :=
  Eval.cnotSwap (by unfold cnotMatrix_ok; decide) rfl ((wellFormedBool_iff _).mp (by decide))

/-- Inapplicability: a singular square matrix of matching size has no derivation. -/
theorem not_eval_cnotSwap_singular :
    ¬ Eval (Command.cnotSwap singularMat2) cnotExampleState
      (cnotSwapState cnotExampleState singularMat2) := by
  intro h
  cases h with
  | cnotSwap hok _ _ =>
      exact absurd hok (by unfold cnotMatrix_ok; decide)

/-- Inapplicability / malformation: a non-square matrix has no derivation. -/
theorem not_eval_cnotSwap_wrong_shape :
    ¬ Eval (Command.cnotSwap wrongShapeMat) cnotExampleState
      (cnotSwapState cnotExampleState wrongShapeMat) := by
  intro h
  cases h with
  | cnotSwap hok _ _ =>
      exact absurd hok (by unfold cnotMatrix_ok; decide)

/-- Inapplicability / malformation: a square matrix of size ≠ |Q| has no derivation. -/
theorem not_eval_cnotSwap_wrong_size :
    ¬ Eval (Command.cnotSwap [[true]]) cnotExampleState
      (cnotSwapState cnotExampleState [[true]]) := by
  intro h
  cases h with
  | cnotSwap hok _ _ =>
      exact absurd hok (by unfold cnotMatrix_ok; decide)

/-- Worked closed-term soundness derivation for `C-COLUMN-CNOT` via
    `ext_judgment_soundness_of_term_exact_uncertified`: derives `n' = n`,
    `k' = k`, and `wf 1` with zero distance or certificate hypotheses. -/
theorem termModels_cnotSwap_example :
    let term : ClosedTerm := ⟨Command.cnotSwap cnotMat2, StateExpr.base cnotExampleState⟩
    let out : CodeState := cnotSwapState cnotExampleState cnotMat2
    TermModels exactExtMeasure term out
        (ExtAnn.eq (ExtAExpr.atom (.pos 1 Field.n)) (ExtAExpr.atom (.pos 0 Field.n))) ∧
      TermModels exactExtMeasure term out
        (ExtAnn.eq (ExtAExpr.atom (.pos 1 Field.k)) (ExtAExpr.atom (.pos 0 Field.k))) ∧
      TermModels exactExtMeasure term out (ExtAnn.wf 1) := by
  intro term out
  have hterm : EvalTerm term out :=
    EvalTerm.eval (EvalExpr.base cnotExampleState) eval_cnotSwap_example
  obtain ⟨s, cs, hexpr, htrace, hsound⟩ :=
    ext_judgment_soundness_of_term_exact_uncertified hterm cnotExampleState_wf
  cases hexpr
  have htrace0 : Trace (Command.cnotSwap cnotMat2) cnotExampleState [out] out :=
    Trace.step rfl eval_cnotSwap_example
  obtain ⟨hcs, _⟩ := htrace.unique htrace0
  subst hcs
  refine ⟨?_, ?_, ?_⟩
  · exact hsound _ (ExtDerives.instCnotSwapN 0 cnotMat2 cnotExampleState out
      rfl rfl eval_cnotSwap_example)
  · exact hsound _ (ExtDerives.instCnotSwapK 0 cnotMat2 cnotExampleState out
      rfl rfl eval_cnotSwap_example)
  · exact hsound _ (ExtDerives.instCnotSwapWF 0 cnotMat2 cnotExampleState out
      rfl rfl eval_cnotSwap_example)

end CodeCalculus
