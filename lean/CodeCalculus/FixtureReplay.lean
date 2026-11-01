import CodeCalculus.Eval
import CodeCalculus.Fixtures
import CodeCalculus.State

namespace CodeCalculus

theorem fixture_W0_initial_wellFormed : wellFormedBool fixture_W0_initial = true := by
  decide

theorem fixture_W10_initial_wellFormed : wellFormedBool fixture_W10_initial = true := by
  decide

theorem fixture_W11_initial_wellFormed : wellFormedBool fixture_W11_initial = true := by
  decide

theorem fixture_W12_initial_wellFormed : wellFormedBool fixture_W12_initial = true := by
  decide

theorem fixture_W13_initial_wellFormed : wellFormedBool fixture_W13_initial = true := by
  decide

theorem fixture_W14_result_wellFormed : wellFormedBool fixture_W14_result = true := by
  decide

theorem fixture_W16_initial_wellFormed : wellFormedBool fixture_W16_initial = true := by
  decide

theorem fixture_W22_initial_wellFormed : wellFormedBool fixture_W22_initial = true := by
  decide

theorem fixture_W23_initial_wellFormed : wellFormedBool fixture_W23_initial = true := by
  decide

theorem fixture_W23_result_wellFormed : wellFormedBool fixture_W23_result = true := by
  decide

theorem fixture_W3_initial_wellFormed : wellFormedBool fixture_W3_initial = true := by
  decide

theorem fixture_W3_result_wellFormed : wellFormedBool fixture_W3_result = true := by
  decide

theorem fixture_W4_initial_wellFormed : wellFormedBool fixture_W4_initial = true := by
  decide

theorem fixture_W5_initial_wellFormed : wellFormedBool fixture_W5_initial = true := by
  decide

theorem fixture_W5_result_wellFormed : wellFormedBool fixture_W5_result = true := by
  decide

theorem fixture_W6_initial_wellFormed : wellFormedBool fixture_W6_initial = true := by
  decide

theorem fixture_W7_initial_wellFormed : wellFormedBool fixture_W7_initial = true := by
  decide

theorem fixture_W7_result_wellFormed : wellFormedBool fixture_W7_result = true := by
  decide

theorem fixture_W8_initial_wellFormed : wellFormedBool fixture_W8_initial = true := by
  decide

theorem fixture_W9_initial_wellFormed : wellFormedBool fixture_W9_initial = true := by
  decide

-- Malformed cases (optional): not well-formed.
def malformed_dupQ : CodeState := { Q := [1, 1], rows := [], used := [] }

def malformed_badSupport : CodeState := { Q := [1, 2], rows := [ { id := 0, sector := Sector.X, support := [3] } ], used := [0] }

def malformed_dependent : CodeState := {
  Q := [1, 2],
  rows := [ { id := 0, sector := Sector.X, support := [1, 2] },
            { id := 1, sector := Sector.X, support := [1, 2] } ],
  used := [0, 1]
}

theorem malformed_dupQ_not_wellFormed : wellFormedBool malformed_dupQ = false := by
  decide
theorem malformed_badSupport_not_wellFormed : wellFormedBool malformed_badSupport = false := by
  decide
theorem malformed_dependent_not_wellFormed : wellFormedBool malformed_dependent = false := by
  decide



theorem fixture_W1_initial_wellFormed : wellFormedBool fixture_W1_initial = false := by
  decide

theorem fixture_W2_initial_wellFormed : wellFormedBool fixture_W2_initial = false := by
  decide


-- Direct-sum pair fixtures (W14, W15, W21): each summand is individually
-- well-formed; the inapplicable fixtures (W15, W21) additionally replay the
-- *outcome* — no EvalExpr derivation, on the premise whose failure the
-- fixture isolates.

theorem fixture_W14_S_L_wellFormed : wellFormedBool fixture_W14_S_L = true := by
  decide

theorem fixture_W14_S_R_wellFormed : wellFormedBool fixture_W14_S_R = true := by
  decide

theorem fixture_W15_S_L_wellFormed : wellFormedBool fixture_W15_S_L = true := by
  decide

theorem fixture_W15_S_R_prime_wellFormed : wellFormedBool fixture_W15_S_R_prime = true := by
  decide

theorem fixture_W21_S_L_wellFormed : wellFormedBool fixture_W21_S_L = true := by
  decide

theorem fixture_W21_S_R_double_prime_wellFormed :
    wellFormedBool fixture_W21_S_R_double_prime = true := by
  decide

/-- W15: the qubit namespaces overlap at 2, so the C-DIRECT-SUM qubit
    premise fails and no EvalExpr derivation exists. -/
theorem fixture_W15_no_evalExpr (t : CodeState) :
    ¬ EvalExpr (StateExpr.directSum (StateExpr.base fixture_W14_S_L)
        (StateExpr.base fixture_W15_S_R_prime)) t := by
  intro h
  cases h with
  | directSum hQ _hU h1 h2 =>
      cases h1
      cases h2
      exact hQ 2 (by simp [fixture_W14_S_L]) (by simp [fixture_W15_S_R_prime])

/-- W21: both summands minted the same identifier (p1 = 50000), so the
    used-set premise fails and no EvalExpr derivation exists; the qubit
    premise holds. -/
theorem fixture_W21_no_evalExpr (t : CodeState) :
    ¬ EvalExpr (StateExpr.directSum (StateExpr.base fixture_W21_S_L)
        (StateExpr.base fixture_W21_S_R_double_prime)) t := by
  intro h
  cases h with
  | directSum _hQ hU h1 h2 =>
      cases h1
      cases h2
      exact hU 50000 (by simp [fixture_W21_S_L, fixture_W14_S_L])
        (by simp [fixture_W21_S_R_double_prime])

-- Result states added by  (W9, W16), checked by kernel `decide`.
-- The `Eval` replays of every single-step and two-step fixture, positive and
-- negative, are in `FixtureEvalReplay.lean`, together with the Bool/Prop
-- bridge that connects these Boolean verdicts to `EncodingWellFormed`.

theorem fixture_W9_result_wellFormed : wellFormedBool fixture_W9_result = true := by
  decide

theorem fixture_W16_result_wellFormed : wellFormedBool fixture_W16_result = true := by
  decide

end CodeCalculus
