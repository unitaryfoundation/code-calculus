import CodeCalculus.PricedInterval
import CodeCalculus.ExactDistance

namespace CodeCalculus

/-!
# Gate 6 interval-transformer soundness (`OBL-GATE6-CSS-EXTENSIONS`, issue #311)

Mechanized form of `spec/OPERATIONAL_SEMANTICS.md` §4.32: the interval
transformer that `spec/JUDGMENT_LAYER.md` §2b and §2e name for each admitted
Gate 6 cell is sound and monotone under the cell's distance relation
(§4.26 to §4.31). The statements are over the executable ledger of
`PricedInterval.lean` (`DistanceLedger`, `LedgerSound`, `leOpt`) and an
uninterpreted distance reading `δ : CodeState → ExactDist`, in the shape of
`priced_interval_soundness`: the distance relations enter as hypotheses, one
per move, and the theorem proves the interval bookkeeping from them.

Reconciliation with what the development already carried, so that nothing is
proved twice:

- `priced_interval_soundness` gives every Gate 6 move the widened reset
  `[0, +∞]` (the default case of `propagateCmd`). That reset is §4.32's
  transformer for `E-PUNCTURE` and for `E-EXTEND` with `Δ ≠ ∅` only
  (`puncture_transformer_sound`); for `P-REBASE`, `E-LOCAL-HADAMARD`,
  `E-PEEL`, and `E-EXTEND` with `Δ = ∅` it is strictly coarser than the
  §4.32 transformer, and `propagateGate6_refines_propagateCmd` records the
  comparison. `propagateGate6` keeps `propagateCmd`'s transport on every
  other command, and `gate6_interval_soundness` reuses
  `priced_interval_soundness` for those cases rather than re-proving them.
- `propagateCmd_monotone` (§9.4) is the monotone half for the widened
  transports; `propagateGate6_monotone` is the monotone half for the §4.32
  transformers, reusing it on the kernel cases.
- `wf_of_eval` (`WellFormedness.lean`) carries the Gate 6 well-formedness
  cells through the premise their transitions carry; this module adds no
  well-formedness statement.
- `hadamardLedger` (`Judgment.lean`) is the swap transformer of §4.32 and is
  used as such here.
- `E-GLUE` has no unary grammar production and no `Eval` constructor on
  commands; its expression constructor `StateExpr.glue` (rule
  `EvalExpr.glue`, update `glueState`) is handled in `Gate6Exact.lean`
  (`glue_state_transformer_sound`, `glue_expr_sound`, issue #339). Here its
  state update (§4.31) is the direct sum of the two factors followed by the
  seam checks added one at a time, each checked against the factor rows and
  the seam checks admitted before it, which is `EvalExpr.directSum` followed
  by a `C-SEQUENCE` of `C-ADD-CHECK` evaluations. `glueCommand` is that
  sequence, so an `E-GLUE` evaluation is the closed term
  `⟨glueCommand seams, StateExpr.directSum (base A) (base B)⟩` of the
  existing term language (`glue_term_sound`). No constructor is added by
  this module and `denote` is unchanged.

Hypotheses and their discharge. The per-move relations are
`hrebase` (§4.26: every distance unchanged), `hhadamard` (§4.27: the sector
distances exchange), `hpeel` (§4.28: the selected sector does not lose
distance, the opposite sector does not gain and loses at most one, the
2026-11-10 sharpening of issue #331; the two peel prices of
`JUDGMENT_LAYER.md` §2a enter through `HypTrue` as the graft price does),
`hextend` (§4.30 with
`Δ = ∅`: a `C-ADD-CHECK` sequence, no distance falls), and for `E-GLUE` the
direct-sum law `hdirect` and the addition law `hadd` already used by
`directSum_sound` and `priced_interval_soundness`. For the exact sector
distance of `ExactDistance.lean`, read in `Option Nat` by `exactDist`, the
§4.26 and §4.27 relations are proved here with no hypothesis
(`exactDistance_rebaseState`, `exactDistance_swapState`), and the §4.30
relation is proved when the extension leaves the namespace unchanged
(`exactDistance_extendState_le`; `extendState` re-sorts the namespace, so
this is the identity on a sorted, duplicate-free namespace). The §4.28 peel
relations and the `k = 0` reading `hk0` are discharged for `exactDist` in
`ExactPeel.lean` (`exactDist_peel_relations`, `peel_transformer_sound_exact`,
`exactDist_k0`, issue #338). The §4.13 graft relations remain hypotheses for
the exact distance, as they are for `priced_interval_soundness`. The
instance of `gate6_interval_soundness` at `exactDist` is
`gate6_interval_soundness_exact` in `Gate6Exact.lean` (issue #339), which
keeps the graft relations and the `Δ = ∅` extension law as its two
hypotheses; the per-cell instances `rebase_transformer_sound_exact`,
`hadamard_transformer_sound_exact`, `extend_transformer_sound_exact`, and
`peel_transformer_sound_exact` carry none.

What this module does not do. It does not change any cell's evidence status
or ladder rung: the cells remain conditional on their hypotheses (the seam
certificate and the Theorem 4 / claim 7.4 equality for `E-GLUE`'s Z upper
endpoint, which enters as the hypothesis `hcert`), and discharge is not
promotion. It does not state the `E-GLUE` logical-witness prerequisite
(`TAXONOMY.md` §2.10). It proves theorems about the transcribed transformers
and nothing about the calculus beyond them (README *Status*).
-/

/-! ## The §4.32 transformers -/

/-- The reset `[0, +∞]` on every interval: `propagateCmd`'s transport for
    every Gate 6 move, and §4.32's transformer for `E-PUNCTURE` and for
    `E-EXTEND` with `Δ ≠ ∅`. -/
def resetLedger : DistanceLedger :=
  { full := Interval.mk (some 0) none
  , x := Interval.mk (some 0) none
  , z := Interval.mk (some 0) none }

/-- The `k = 0` collapse of `propagateCmdK`: every distance is `+∞`. -/
def infinityLedger : DistanceLedger :=
  { full := Interval.mk none none, x := Interval.mk none none, z := Interval.mk none none }

/-- Carry every lower endpoint and rebuild every upper endpoint from
    witnesses valid in the child: the `C-ADD-CHECK` transport of
    `propagateCmd`, and §4.32's `E-EXTEND` transformer with `Δ = ∅`. -/
def carryLowerLedger (L : DistanceLedger) : DistanceLedger :=
  { full := Interval.mk L.full.lower none
  , x := Interval.mk L.x.lower none
  , z := Interval.mk L.z.lower none }

/-- `n - 1` on `Option Nat`, with `none` (`+∞`) fixed: the opposite-sector
    lower endpoint of the peel transformer (§4.28: `d_σ - 1 ≤ d_σ'`). At
    `some 0` it stays `some 0`, the consumer's floor. -/
def predOpt : Option Nat → Option Nat
  | none => none
  | some n => some (n - 1)

theorem predOpt_monotone {a b : Option Nat} (h : leOpt a b) :
    leOpt (predOpt a) (predOpt b) := by
  cases a <;> cases b <;> simp [leOpt, predOpt] at * <;> omega

/-- The peel's opposite-sector interval (§2b, §4.28, issue #331): unpriced,
    `[L - 1, U]` from `d_σ - 1 ≤ d_σ' ≤ d_σ`; under the exposure price `p`,
    `[min(L, p), min(U, p)]` from `d_σ' = min(d_σ, p)`, as for the graft. -/
def peelOpposite (I : Interval) (price : Option Nat) : Interval :=
  match price with
  | none => Interval.mk (predOpt I.lower) I.upper
  | some p => Interval.mk (minOpt I.lower (some p)) (minOpt I.upper (some p))

/-- The peel's selected-sector interval: unpriced, `[L, +∞]` from
    `d_τ ≤ d_τ'`; under the avoidance minimum `w`, `[w, w]` from
    `d_τ' = w`. -/
def peelSelected (I : Interval) (price : Option Nat) : Interval :=
  match price with
  | none => Interval.mk I.lower none
  | some w => Interval.mk (some w) (some w)

/-- The interval of a minimum of two bounded quantities: both endpoints are
    the minima of the two intervals' endpoints. -/
def minInterval (I J : Interval) : Interval :=
  Interval.mk (minOpt I.lower J.lower) (minOpt I.upper J.upper)

/-- §4.32's `E-PEEL` transformer (issue #295, sharpened 2026-11-10, issue
    #331): the selected sector `τ` is `peelSelected`, the opposite sector is
    `peelOpposite`, and the full distance is the minimum of the two, since
    `d' = min(d_τ', d_σ')`. The prices are the two optional `Hyp` fields. -/
def peelLedger (τ : Sector) (L : DistanceLedger) (expose avoid : Option Nat) :
    DistanceLedger :=
  match τ with
  | Sector.X =>
      { full := minInterval (peelSelected L.x avoid) (peelOpposite L.z expose)
      , x := peelSelected L.x avoid
      , z := peelOpposite L.z expose }
  | Sector.Z =>
      { full := minInterval (peelSelected L.z avoid) (peelOpposite L.x expose)
      , x := peelOpposite L.x expose
      , z := peelSelected L.z avoid }

/-- §4.32's `E-GLUE` transformer (`JUDGMENT_LAYER.md` §2b, §2e): every lower
    endpoint is the minimum of the two factor ledgers' lower endpoints; the
    Z upper endpoint is the minimum of the two factors' Z upper endpoints
    under an admissible seam certificate; the X and full upper endpoints are
    left to witnesses valid in the child. -/
def glueLedger (A B : DistanceLedger) (certified : Bool) : DistanceLedger :=
  { full := Interval.mk (minOpt A.full.lower B.full.lower) none
  , x := Interval.mk (minOpt A.x.lower B.x.lower) none
  , z := Interval.mk (minOpt A.z.lower B.z.lower)
      (if certified then minOpt A.z.upper B.z.upper else none) }

/-- The §4.32 transformers for the five unary Gate 6 moves; every other
    command keeps its `propagateCmd` transport. The `T = ∅` Hadamard is the
    identity on state and ledger (`TERM_LANGUAGE.md` §2, §4.27). -/
def propagateGate6 (m : Command) (s s' : CodeState) (L : DistanceLedger) (H : Hyp) :
    DistanceLedger :=
  match m with
  | Command.rebase _ _ => L
  | Command.hadamard T => if T.isEmpty then L else hadamardLedger L
  | Command.peel _ τ _ => peelLedger τ L H.peelExpose H.peelAvoid
  | Command.puncture _ => resetLedger
  | Command.extend delta _ => if delta.isEmpty then carryLowerLedger L else resetLedger
  | _ => propagateCmd m s s' L H

/-- `propagateGate6` with the `k = 0` collapse of `propagateCmdK`. -/
def propagateGate6K (m : Command) (s s' : CodeState) (L : DistanceLedger) (H : Hyp) :
    DistanceLedger :=
  if stateK s' = 0 then infinityLedger else propagateGate6 m s s' L H

theorem minOpt_comm (a b : Option Nat) : minOpt a b = minOpt b a := by
  cases a <;> cases b <;> simp [minOpt, Nat.min_comm]

/-- The reset contains every distance. -/
theorem reset_sound (δ : CodeState → ExactDist) (s' : CodeState) :
    LedgerSound (δ s') resetLedger :=
  ⟨⟨some_zero_leOpt _, leOpt_none _⟩, ⟨some_zero_leOpt _, leOpt_none _⟩,
    ⟨some_zero_leOpt _, leOpt_none _⟩⟩

/-- Every ledger is at least as precise as the reset. -/
theorem refines_resetLedger (L : DistanceLedger) : L.refines resetLedger :=
  ⟨⟨some_zero_leOpt _, leOpt_none _⟩, ⟨some_zero_leOpt _, leOpt_none _⟩,
    ⟨some_zero_leOpt _, leOpt_none _⟩⟩

/-! ## Soundness, one theorem per cell (§4.32's bullets) -/

/-- `P-REBASE`: the identity transformer is sound under §4.26's distance
    identity (the row spaces are unchanged, so every distance is). -/
theorem rebase_transformer_sound (δ : CodeState → ExactDist) {s s' : CodeState}
    (hδ : δ s' = δ s) (L : DistanceLedger) (hL : LedgerSound (δ s) L) :
    LedgerSound (δ s') L := by
  rw [hδ]
  exact hL

/-- `E-LOCAL-HADAMARD` (`T = Q`): the swap transformer `hadamardLedger` is
    sound under §4.27's exchange `d_X' = d_Z`, `d_Z' = d_X`; the full
    distance `min(d_X, d_Z)` is symmetric. -/
theorem hadamard_transformer_sound (δ : CodeState → ExactDist)
    (hmin : ∀ s, (δ s).full = minOpt (δ s).x (δ s).z) {s s' : CodeState}
    (hx : (δ s').x = (δ s).z) (hz : (δ s').z = (δ s).x)
    (L : DistanceLedger) (hL : LedgerSound (δ s) L) :
    LedgerSound (δ s') (hadamardLedger L) := by
  obtain ⟨hf, hxL, hzL⟩ := hL
  have hfull : (δ s').full = (δ s).full := by
    rw [hmin s', hmin s, hx, hz, minOpt_comm]
  refine ⟨?_, ?_, ?_⟩
  · show Interval.contains L.full (δ s').full
    rw [hfull]
    exact hf
  · show Interval.contains L.z (δ s').x
    rw [hx]
    exact hzL
  · show Interval.contains L.x (δ s').z
    rw [hz]
    exact hxL

/-- The opposite-sector interval contains the child's distance under the
    §4.28 relations `d_σ - 1 ≤ d_σ' ≤ d_σ` and, when the exposure price is
    supplied, `d_σ' = min(d_σ, p)`. -/
theorem peelOpposite_sound {I : Interval} {d d' : Option Nat} (hI : I.contains d)
    (hlow : leOpt (predOpt d) d') (hupp : leOpt d' d) {price : Option Nat}
    (hprice : ∀ p, price = some p → d' = minOpt d (some p)) :
    (peelOpposite I price).contains d' := by
  cases price with
  | none =>
      exact ⟨leOpt_trans (predOpt_monotone hI.1) hlow, leOpt_trans hupp hI.2⟩
  | some p =>
      rw [hprice p rfl]
      exact ⟨minOpt_monotone hI.1 (leOpt_refl _), minOpt_monotone hI.2 (leOpt_refl _)⟩

/-- The selected-sector interval contains the child's distance under
    `d_τ ≤ d_τ'` and, when the avoidance minimum is supplied, `d_τ' = w`. -/
theorem peelSelected_sound {I : Interval} {d d' : Option Nat} (hI : I.contains d)
    (hsel : leOpt d d') {price : Option Nat}
    (hprice : ∀ w, price = some w → d' = some w) :
    (peelSelected I price).contains d' := by
  cases price with
  | none => exact ⟨leOpt_trans hI.1 hsel, leOpt_none _⟩
  | some w =>
      rw [hprice w rfl]
      exact ⟨leOpt_refl _, leOpt_refl _⟩

theorem minInterval_contains {I J : Interval} {d e : Option Nat}
    (hI : I.contains d) (hJ : J.contains e) : (minInterval I J).contains (minOpt d e) :=
  ⟨minOpt_monotone hI.1 hJ.1, minOpt_monotone hI.2 hJ.2⟩

/-- Branch selection for the price premises of `HypTrue` at a fixed sector. -/
theorem hexpose_X {δ : CodeState → ExactDist} {s s' : CodeState} {expose : Option Nat}
    (h : ∀ p, expose = some p →
        (if Sector.X = Sector.X then (δ s').z = minOpt (δ s).z (some p)
         else (δ s').x = minOpt (δ s).x (some p)))
    (p : Nat) (hp : expose = some p) : (δ s').z = minOpt (δ s).z (some p) :=
  Eq.mp (ite_eq_left (rfl : Sector.X = Sector.X)) (h p hp)

theorem hexpose_Z {δ : CodeState → ExactDist} {s s' : CodeState} {expose : Option Nat}
    (h : ∀ p, expose = some p →
        (if Sector.Z = Sector.X then (δ s').z = minOpt (δ s).z (some p)
         else (δ s').x = minOpt (δ s).x (some p)))
    (p : Nat) (hp : expose = some p) : (δ s').x = minOpt (δ s).x (some p) :=
  Eq.mp (ite_eq_right (by decide : Sector.Z ≠ Sector.X)) (h p hp)

theorem hexpose_avoid_X {δ : CodeState → ExactDist} {s' : CodeState} {avoid : Option Nat}
    (h : ∀ w, avoid = some w →
        (if Sector.X = Sector.X then (δ s').x = some w else (δ s').z = some w))
    (w : Nat) (hw : avoid = some w) : (δ s').x = some w :=
  Eq.mp (ite_eq_left (rfl : Sector.X = Sector.X)) (h w hw)

theorem hexpose_avoid_Z {δ : CodeState → ExactDist} {s' : CodeState} {avoid : Option Nat}
    (h : ∀ w, avoid = some w →
        (if Sector.Z = Sector.X then (δ s').x = some w else (δ s').z = some w))
    (w : Nat) (hw : avoid = some w) : (δ s').z = some w :=
  Eq.mp (ite_eq_right (by decide : Sector.Z ≠ Sector.X)) (h w hw)

/-- `E-PEEL` (issue #295, sharpened 2026-11-10, issue #331): `peelLedger` is
    sound under §4.28's three relations, `d_τ' ≥ d_τ` for the selected
    sector and `d_σ - 1 ≤ d_σ' ≤ d_σ` for the opposite sector, and under the
    two price relations when a price is supplied (`HypTrue`): the
    exposure price gives `d_σ' = min(d_σ, w_expose)` and the avoidance
    minimum gives `d_τ' = w_avoid`. The full distance is the minimum of the
    two sector distances (`hmin`). -/
theorem peel_transformer_sound (δ : CodeState → ExactDist)
    (hmin : ∀ s, (δ s).full = minOpt (δ s).x (δ s).z) {s s' : CodeState} (τ : Sector)
    (hsel : if τ = Sector.X then leOpt (δ s).x (δ s').x else leOpt (δ s).z (δ s').z)
    (hopp : if τ = Sector.X then leOpt (δ s').z (δ s).z else leOpt (δ s').x (δ s).x)
    (hlow : if τ = Sector.X then leOpt (predOpt (δ s).z) (δ s').z
            else leOpt (predOpt (δ s).x) (δ s').x)
    {expose avoid : Option Nat}
    (hexpose : ∀ p, expose = some p →
        (if τ = Sector.X then (δ s').z = minOpt (δ s).z (some p)
         else (δ s').x = minOpt (δ s).x (some p)))
    (havoid : ∀ w, avoid = some w →
        (if τ = Sector.X then (δ s').x = some w else (δ s').z = some w))
    (L : DistanceLedger) (hL : LedgerSound (δ s) L) :
    LedgerSound (δ s') (peelLedger τ L expose avoid) := by
  obtain ⟨hf, hx, hz⟩ := hL
  cases τ with
  | X =>
      have hselx : (peelSelected L.x avoid).contains (δ s').x :=
        peelSelected_sound hx hsel (fun w hw => hexpose_avoid_X havoid w hw)
      have hoppz : (peelOpposite L.z expose).contains (δ s').z :=
        peelOpposite_sound hz hlow hopp (fun p hp => hexpose_X hexpose p hp)
      refine ⟨?_, hselx, hoppz⟩
      show (minInterval (peelSelected L.x avoid) (peelOpposite L.z expose)).contains (δ s').full
      rw [hmin s']
      exact minInterval_contains hselx hoppz
  | Z =>
      have hselz : (peelSelected L.z avoid).contains (δ s').z :=
        peelSelected_sound hz hsel (fun w hw => hexpose_avoid_Z havoid w hw)
      have hoppx : (peelOpposite L.x expose).contains (δ s').x :=
        peelOpposite_sound hx hlow hopp (fun p hp => hexpose_Z hexpose p hp)
      refine ⟨?_, hoppx, hselz⟩
      show (minInterval (peelSelected L.z avoid) (peelOpposite L.x expose)).contains (δ s').full
      rw [hmin s', minOpt_comm]
      exact minInterval_contains hselz hoppx

/-- `E-PUNCTURE`: the reset is sound; no carried endpoint is derivable
    (§4.29), and the same transformer serves `E-EXTEND` with `Δ ≠ ∅`
    (§4.30). -/
theorem puncture_transformer_sound (δ : CodeState → ExactDist) (s' : CodeState) :
    LedgerSound (δ s') resetLedger :=
  reset_sound δ s'

/-- `E-EXTEND` with `Δ = ∅`: `carryLowerLedger` is sound when no distance
    falls (§4.30: the move is a `C-ADD-CHECK` sequence over the ambient
    code). -/
theorem extend_transformer_sound (δ : CodeState → ExactDist) {s s' : CodeState}
    (hlow : leOpt (δ s).full (δ s').full ∧ leOpt (δ s).x (δ s').x ∧ leOpt (δ s).z (δ s').z)
    (L : DistanceLedger) (hL : LedgerSound (δ s) L) :
    LedgerSound (δ s') (carryLowerLedger L) :=
  ⟨⟨leOpt_trans hL.1.1 hlow.1, leOpt_none _⟩,
    ⟨leOpt_trans hL.2.1.1 hlow.2.1, leOpt_none _⟩,
    ⟨leOpt_trans hL.2.2.1 hlow.2.2, leOpt_none _⟩⟩

/-! ## `E-GLUE` as a closed term -/

/-- The seam checks of an `E-GLUE`, added one at a time (§4.31): each
    `C-ADD-CHECK` is checked against the factor rows and the seam checks
    admitted before it, by `Eval.add`'s own premises. -/
def glueCommand : List (Sector × List Nat) → Command
  | [] => Command.skip
  | (σ, sup) :: rest => Command.seq (Command.addStab σ sup) (glueCommand rest)

/-- Along a sequence of additions no distance falls (the §4.3 law, taken as
    the hypothesis `hadd` of `priced_interval_soundness`). -/
theorem glue_lower_le (δ : CodeState → ExactDist)
    (hadd : ∀ sector support s s', EncodingWellFormed s →
      Eval (Command.addStab sector support) s s' →
      leOpt (δ s).full (δ s').full ∧ leOpt (δ s).x (δ s').x ∧ leOpt (δ s).z (δ s').z)
    (seams : List (Sector × List Nat)) :
    ∀ {s s' : CodeState}, EncodingWellFormed s → Eval (glueCommand seams) s s' →
      leOpt (δ s).full (δ s').full ∧ leOpt (δ s).x (δ s').x ∧ leOpt (δ s).z (δ s').z := by
  induction seams with
  | nil =>
      intro s s' _ h
      rw [eval_skip_eq h]
      exact ⟨leOpt_refl _, leOpt_refl _, leOpt_refl _⟩
  | cons seam rest ih =>
      intro s s' hwf h
      obtain ⟨σ, sup⟩ := seam
      cases h with
      | seq h1 h2 =>
          obtain ⟨hf1, hx1, hz1⟩ := hadd σ sup _ _ hwf h1
          obtain ⟨hf2, hx2, hz2⟩ := ih (wf_of_eval_all h1 hwf) h2
          exact ⟨leOpt_trans hf1 hf2, leOpt_trans hx1 hx2, leOpt_trans hz1 hz2⟩

/-- `E-GLUE`: `glueLedger` is sound (§4.32). The glued code is the direct
    sum of the factors with the seam checks added: the direct-sum law
    (`hdirect`, as in `directSum_sound`) puts every distance of the sum at
    the factor minimum, and the addition law (`hadd`) keeps every lower
    endpoint valid along the seam sequence. The Z upper endpoint uses the
    seam certificate's equality `d_Z = min(d_A, d_B)` as the hypothesis
    `hcert`, which is the cell hypothesis of `JUDGMENT_LAYER.md` §2e, not a
    theorem of this module. -/
theorem glue_transformer_sound (δ : CodeState → ExactDist)
    (hdirect : ∀ a b, δ (directSumState a b) =
        ExactDist.mk (minOpt (δ a).full (δ b).full)
                    (minOpt (δ a).x (δ b).x)
                    (minOpt (δ a).z (δ b).z))
    (hadd : ∀ sector support s s', EncodingWellFormed s →
      Eval (Command.addStab sector support) s s' →
      leOpt (δ s).full (δ s').full ∧ leOpt (δ s).x (δ s').x ∧ leOpt (δ s).z (δ s').z)
    {sA sB s' : CodeState} {seams : List (Sector × List Nat)}
    (hwfA : EncodingWellFormed sA) (hwfB : EncodingWellFormed sB)
    (hQ : DisjointList sA.Q sB.Q) (hU : DisjointList sA.used sB.used)
    (h : Eval (glueCommand seams) (directSumState sA sB) s')
    (A B : DistanceLedger) (hA : LedgerSound (δ sA) A) (hB : LedgerSound (δ sB) B)
    (certified : Bool)
    (hcert : certified = true → (δ s').z = minOpt (δ sA).z (δ sB).z) :
    LedgerSound (δ s') (glueLedger A B certified) := by
  have hwf0 : EncodingWellFormed (directSumState sA sB) :=
    directSum_wellFormed sA sB hwfA hwfB hQ hU
  obtain ⟨hsf, hsx, hsz⟩ := directSum_sound δ hdirect A B sA sB hA hB
  obtain ⟨hf, hx, hz⟩ := glue_lower_le δ hadd seams hwf0 h
  refine ⟨⟨leOpt_trans hsf.1 hf, leOpt_none _⟩, ⟨leOpt_trans hsx.1 hx, leOpt_none _⟩,
    ⟨leOpt_trans hsz.1 hz, ?_⟩⟩
  cases certified with
  | false => exact leOpt_none _
  | true =>
      show leOpt (δ s').z (minOpt A.z.upper B.z.upper)
      rw [hcert rfl]
      exact minOpt_monotone hA.2.2.2 hB.2.2.2

/-- The same, read off the closed term: an `E-GLUE` evaluation is the term
    `⟨glueCommand seams, directSum (base A) (base B)⟩` of the existing
    language, whose `EvalExpr` premises are the disjointness conditions of
    §4.31. -/
theorem glue_term_sound (δ : CodeState → ExactDist)
    (hdirect : ∀ a b, δ (directSumState a b) =
        ExactDist.mk (minOpt (δ a).full (δ b).full)
                    (minOpt (δ a).x (δ b).x)
                    (minOpt (δ a).z (δ b).z))
    (hadd : ∀ sector support s s', EncodingWellFormed s →
      Eval (Command.addStab sector support) s s' →
      leOpt (δ s).full (δ s').full ∧ leOpt (δ s).x (δ s').x ∧ leOpt (δ s).z (δ s').z)
    {sA sB s' : CodeState} {seams : List (Sector × List Nat)}
    (hwfA : EncodingWellFormed sA) (hwfB : EncodingWellFormed sB)
    (h : EvalTerm { command := glueCommand seams
                  , expr := StateExpr.directSum (StateExpr.base sA) (StateExpr.base sB) } s')
    (A B : DistanceLedger) (hA : LedgerSound (δ sA) A) (hB : LedgerSound (δ sB) B)
    (certified : Bool)
    (hcert : certified = true → (δ s').z = minOpt (δ sA).z (δ sB).z) :
    LedgerSound (δ s') (glueLedger A B certified) := by
  cases h with
  | eval hexpr heval =>
      cases hexpr with
      | directSum hQ hU h1 h2 =>
          cases h1
          cases h2
          exact glue_transformer_sound δ hdirect hadd hwfA hwfB hQ hU heval A B hA hB
            certified hcert

/-! ## The combined statement, in the shape of `priced_interval_soundness` -/

/-- Soundness of the §4.32 transformers for every command: the kernel,
    graft, and sequence cases are `priced_interval_soundness` unchanged, and
    each Gate 6 case is its per-cell theorem above under the cell's
    distance relation. `E-GLUE` is not a `Command`; its statement is
    `glue_transformer_sound`. -/
theorem gate6_interval_soundness
  (δ : CodeState → ExactDist)
  (hmin : ∀ s, (δ s).full = minOpt (δ s).x (δ s).z)
  (hk0 : ∀ s, EncodingWellFormed s → stateK s = 0 →
      (δ s).full = none ∧ (δ s).x = none ∧ (δ s).z = none)
  (hdelete : ∀ r s s', EncodingWellFormed s → Eval (Command.delete r) s s' →
      leOpt (δ s').full (δ s).full ∧ leOpt (δ s').x (δ s).x ∧ leOpt (δ s').z (δ s).z)
  (hadd : ∀ sector support s s', EncodingWellFormed s →
      Eval (Command.addStab sector support) s s' →
      leOpt (δ s).full (δ s').full ∧ leOpt (δ s).x (δ s').x ∧ leOpt (δ s).z (δ s').z)
  (hgraft : ∀ q τ ids s s', EncodingWellFormed s → Eval (Command.graft q τ ids) s s' →
      (if τ = Sector.X then leOpt (δ s).x (δ s').x else leOpt (δ s).z (δ s').z) ∧
      (if τ = Sector.X then leOpt (δ s').z (δ s).z else leOpt (δ s').x (δ s).x))
  (hrebase : ∀ σ M s s', EncodingWellFormed s → Eval (Command.rebase σ M) s s' →
      δ s' = δ s)
  (hhadamard : ∀ T s s', EncodingWellFormed s → Eval (Command.hadamard T) s s' → T ≠ [] →
      (δ s').x = (δ s).z ∧ (δ s').z = (δ s).x)
  (hpeel : ∀ q τ r s s', EncodingWellFormed s → Eval (Command.peel q τ r) s s' →
      (if τ = Sector.X then leOpt (δ s).x (δ s').x else leOpt (δ s).z (δ s').z) ∧
      (if τ = Sector.X then leOpt (δ s').z (δ s).z else leOpt (δ s').x (δ s).x) ∧
      (if τ = Sector.X then leOpt (predOpt (δ s).z) (δ s').z
       else leOpt (predOpt (δ s).x) (δ s').x))
  (hextend : ∀ adds s s', EncodingWellFormed s → Eval (Command.extend [] adds) s s' →
      leOpt (δ s).full (δ s').full ∧ leOpt (δ s).x (δ s').x ∧ leOpt (δ s).z (δ s').z)
  (H : Hyp)
  : ∀ (L : DistanceLedger) (s s' : CodeState) (m : Command),
      EncodingWellFormed s →
      Eval m s s' →
      HypTrue δ H m s s' →
      LedgerSound (δ s) L →
      LedgerSound (δ s') (propagateGate6K m s s' L H) := by
  intro L s s' m hwf hEval hH hSound
  have hwf' : EncodingWellFormed s' := wf_of_eval_all hEval hwf
  by_cases hk : stateK s' = 0
  · obtain ⟨hf, hx, hz⟩ := hk0 s' hwf' hk
    have hprop : propagateGate6K m s s' L H = infinityLedger := by
      simp [propagateGate6K, hk]
    rw [hprop]
    unfold LedgerSound Interval.contains
    rw [hf, hx, hz]
    exact ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩
  · have hprop : propagateGate6K m s s' L H = propagateGate6 m s s' L H := by
      simp [propagateGate6K, hk]
    rw [hprop]
    -- the commands whose transport is `propagateCmd`'s
    have kernel : ∀ m, Eval m s s' → HypTrue δ H m s s' →
        propagateGate6 m s s' L H = propagateCmd m s s' L H →
        LedgerSound (δ s') (propagateGate6 m s s' L H) := by
      intro m hEval hH heq
      have h := priced_interval_soundness δ hmin hk0 hdelete hadd hgraft H L s s' m
        hwf hEval hH hSound
      have hK : propagateCmdK m s s' L H = propagateCmd m s s' L H := by
        simp [propagateCmdK, hk]
      rw [hK] at h
      rw [heq]
      exact h
    cases m with
    | skip => exact kernel _ hEval hH rfl
    | delete r => exact kernel _ hEval hH rfl
    | addStab sector support => exact kernel _ hEval hH rfl
    | graft q τ ids => exact kernel _ hEval hH rfl
    | seq m1 m2 => exact kernel _ hEval hH rfl
    | rebase σ M =>
        exact rebase_transformer_sound δ (hrebase σ M s s' hwf hEval) L hSound
    | hadamard T =>
        cases T with
        | nil =>
            have hs : s' = s := by
              cases hEval with
              | hadamard _ hs' _ => exact hs'
            show LedgerSound (δ s') L
            rw [hs]
            exact hSound
        | cons a T' =>
            obtain ⟨hx, hz⟩ := hhadamard (a :: T') s s' hwf hEval (List.cons_ne_nil a T')
            show LedgerSound (δ s') (hadamardLedger L)
            exact hadamard_transformer_sound δ hmin hx hz L hSound
    | peel q τ r =>
        obtain ⟨hsel, hopp, hlow⟩ := hpeel q τ r s s' hwf hEval
        obtain ⟨hexpose, havoid⟩ := hH
        exact peel_transformer_sound δ hmin τ hsel hopp hlow hexpose havoid L hSound
    | puncture q => exact puncture_transformer_sound δ s'
    | extend delta adds =>
        cases delta with
        | nil =>
            show LedgerSound (δ s') (carryLowerLedger L)
            exact extend_transformer_sound δ (hextend adds s s' hwf hEval) L hSound
        | cons a d =>
            show LedgerSound (δ s') resetLedger
            exact puncture_transformer_sound δ s'

/-- Two steps of the §4.32 transport compose (§8.5), as
    `priced_interval_soundness_seq` does for `propagateCmdK`. -/
theorem gate6_interval_soundness_seq
  (δ : CodeState → ExactDist)
  (hmin : ∀ s, (δ s).full = minOpt (δ s).x (δ s).z)
  (hk0 : ∀ s, EncodingWellFormed s → stateK s = 0 →
      (δ s).full = none ∧ (δ s).x = none ∧ (δ s).z = none)
  (hdelete : ∀ r s s', EncodingWellFormed s → Eval (Command.delete r) s s' →
      leOpt (δ s').full (δ s).full ∧ leOpt (δ s').x (δ s).x ∧ leOpt (δ s').z (δ s).z)
  (hadd : ∀ sector support s s', EncodingWellFormed s →
      Eval (Command.addStab sector support) s s' →
      leOpt (δ s).full (δ s').full ∧ leOpt (δ s).x (δ s').x ∧ leOpt (δ s).z (δ s').z)
  (hgraft : ∀ q τ ids s s', EncodingWellFormed s → Eval (Command.graft q τ ids) s s' →
      (if τ = Sector.X then leOpt (δ s).x (δ s').x else leOpt (δ s).z (δ s').z) ∧
      (if τ = Sector.X then leOpt (δ s').z (δ s).z else leOpt (δ s').x (δ s).x))
  (hrebase : ∀ σ M s s', EncodingWellFormed s → Eval (Command.rebase σ M) s s' →
      δ s' = δ s)
  (hhadamard : ∀ T s s', EncodingWellFormed s → Eval (Command.hadamard T) s s' → T ≠ [] →
      (δ s').x = (δ s).z ∧ (δ s').z = (δ s).x)
  (hpeel : ∀ q τ r s s', EncodingWellFormed s → Eval (Command.peel q τ r) s s' →
      (if τ = Sector.X then leOpt (δ s).x (δ s').x else leOpt (δ s).z (δ s').z) ∧
      (if τ = Sector.X then leOpt (δ s').z (δ s).z else leOpt (δ s').x (δ s).x) ∧
      (if τ = Sector.X then leOpt (predOpt (δ s).z) (δ s').z
       else leOpt (predOpt (δ s).x) (δ s').x))
  (hextend : ∀ adds s s', EncodingWellFormed s → Eval (Command.extend [] adds) s s' →
      leOpt (δ s).full (δ s').full ∧ leOpt (δ s).x (δ s').x ∧ leOpt (δ s).z (δ s').z)
  (H : Hyp)
  {s t u : CodeState} {m1 m2 : Command}
  (hwf : EncodingWellFormed s)
  (h1 : Eval m1 s t) (h2 : Eval m2 t u)
  (hH1 : HypTrue δ H m1 s t) (hH2 : HypTrue δ H m2 t u)
  (L : DistanceLedger) (hL : LedgerSound (δ s) L) :
  LedgerSound (δ u) (propagateGate6K m2 t u (propagateGate6K m1 s t L H) H) := by
  have hstep1 := gate6_interval_soundness δ hmin hk0 hdelete hadd hgraft hrebase hhadamard
    hpeel hextend H L s t m1 hwf h1 hH1 hL
  exact gate6_interval_soundness δ hmin hk0 hdelete hadd hgraft hrebase hhadamard hpeel
    hextend H (propagateGate6K m1 s t L H) t u m2 (wf_of_eval_all h1 hwf) h2 hH2 hstep1

/-! ## Monotonicity (§8.4(2), §9.4) and the comparison with the widened reset -/

theorem peelOpposite_monotone {I J : Interval} (h : I.refines J) (price : Option Nat) :
    (peelOpposite I price).refines (peelOpposite J price) := by
  cases price with
  | none => exact ⟨predOpt_monotone h.1, h.2⟩
  | some p => exact ⟨minOpt_monotone h.1 (leOpt_refl _), minOpt_monotone h.2 (leOpt_refl _)⟩

theorem peelSelected_monotone {I J : Interval} (h : I.refines J) (price : Option Nat) :
    (peelSelected I price).refines (peelSelected J price) := by
  cases price with
  | none => exact ⟨h.1, leOpt_refl none⟩
  | some w => exact ⟨leOpt_refl _, leOpt_refl _⟩

theorem minInterval_monotone {I I' J J' : Interval} (hI : I.refines I') (hJ : J.refines J') :
    (minInterval I J).refines (minInterval I' J') :=
  ⟨minOpt_monotone hI.1 hJ.1, minOpt_monotone hI.2 hJ.2⟩

/-- Every §4.32 transformer is monotone in the precision order: the identity,
    the swap, the carries, and the resets each preserve `refines`
    componentwise, and the kernel cases are `propagateCmd_monotone`. -/
theorem propagateGate6_monotone (m : Command) (s s' : CodeState) (H : Hyp)
    (L1 L2 : DistanceLedger) (h : L1.refines L2) :
    (propagateGate6 m s s' L1 H).refines (propagateGate6 m s s' L2 H) := by
  cases m with
  | skip => exact propagateCmd_monotone _ s s' H L1 L2 h
  | delete r => exact propagateCmd_monotone _ s s' H L1 L2 h
  | addStab sector support => exact propagateCmd_monotone _ s s' H L1 L2 h
  | graft q τ ids => exact propagateCmd_monotone _ s s' H L1 L2 h
  | seq m1 m2 => exact propagateCmd_monotone _ s s' H L1 L2 h
  | rebase σ M => exact h
  | hadamard T =>
      cases T with
      | nil => exact h
      | cons a T' => exact ⟨h.1, h.2.2, h.2.1⟩
  | peel q τ r =>
      cases τ with
      | X => exact ⟨minInterval_monotone (peelSelected_monotone h.2.1 _) (peelOpposite_monotone h.2.2 _),
                   peelSelected_monotone h.2.1 _, peelOpposite_monotone h.2.2 _⟩
      | Z => exact ⟨minInterval_monotone (peelSelected_monotone h.2.2 _) (peelOpposite_monotone h.2.1 _),
                   peelOpposite_monotone h.2.1 _, peelSelected_monotone h.2.2 _⟩
  | puncture q => exact DistanceLedger.refines_refl _
  | extend delta adds =>
      cases delta with
      | nil => exact ⟨⟨h.1.1, leOpt_refl none⟩, ⟨h.2.1.1, leOpt_refl none⟩, ⟨h.2.2.1, leOpt_refl none⟩⟩
      | cons a d => exact DistanceLedger.refines_refl _

/-- The same including the `k = 0` collapse. -/
theorem propagateGate6K_monotone (m : Command) (s s' : CodeState) (H : Hyp)
    (L1 L2 : DistanceLedger) (h : L1.refines L2) :
    (propagateGate6K m s s' L1 H).refines (propagateGate6K m s s' L2 H) := by
  by_cases hk : stateK s' = 0
  · have e1 : propagateGate6K m s s' L1 H = infinityLedger := by simp [propagateGate6K, hk]
    have e2 : propagateGate6K m s s' L2 H = infinityLedger := by simp [propagateGate6K, hk]
    rw [e1, e2]
    exact DistanceLedger.refines_refl _
  · have e1 : propagateGate6K m s s' L1 H = propagateGate6 m s s' L1 H := by
      simp [propagateGate6K, hk]
    have e2 : propagateGate6K m s s' L2 H = propagateGate6 m s s' L2 H := by
      simp [propagateGate6K, hk]
    rw [e1, e2]
    exact propagateGate6_monotone m s s' H L1 L2 h

/-- The `E-GLUE` transformer is monotone in both factor ledgers (§9.4). -/
theorem glueLedger_monotone {A1 A2 B1 B2 : DistanceLedger}
    (hA : A1.refines A2) (hB : B1.refines B2) (certified : Bool) :
    (glueLedger A1 B1 certified).refines (glueLedger A2 B2 certified) := by
  refine ⟨⟨minOpt_monotone hA.1.1 hB.1.1, leOpt_refl none⟩,
    ⟨minOpt_monotone hA.2.1.1 hB.2.1.1, leOpt_refl none⟩,
    ⟨minOpt_monotone hA.2.2.1 hB.2.2.1, ?_⟩⟩
  cases certified with
  | false => exact leOpt_refl none
  | true => exact minOpt_monotone hA.2.2.2 hB.2.2.2

/-- The §4.32 transformers are at least as precise as the widened transport
    of `propagateCmd` on every command: equal on the kernel, the graft, and
    sequences, and a refinement of the reset on the five Gate 6 moves. This
    is the reconciliation of `priced_interval_soundness` with this module:
    the reset it proves sound for the Gate 6 moves is the coarse end of the
    comparison. -/
theorem propagateGate6_refines_propagateCmd (m : Command) (s s' : CodeState)
    (L : DistanceLedger) (H : Hyp) :
    (propagateGate6 m s s' L H).refines (propagateCmd m s s' L H) := by
  cases m with
  | rebase σ M => exact refines_resetLedger _
  | hadamard T => exact refines_resetLedger _
  | peel q τ r => exact refines_resetLedger _
  | puncture q => exact refines_resetLedger _
  | extend delta adds => exact refines_resetLedger _
  | skip => exact DistanceLedger.refines_refl _
  | delete r => exact DistanceLedger.refines_refl _
  | addStab sector support => exact DistanceLedger.refines_refl _
  | graft q τ ids => exact DistanceLedger.refines_refl _
  | seq m1 m2 => exact DistanceLedger.refines_refl _

/-! ## The §4.26, §4.27, and §4.30 relations for the exact distance

`exactDistance` (`ExactDistance.lean`) is the exact sector distance over `F₂`
vectors, with `|Q| + 1` standing for `+∞`. The relations below are the
distance halves of §4.26 (rebase: every distance unchanged), §4.27
(hadamard: the sector distances exchange), and §4.30 with `Δ = ∅` (extend:
no distance falls), proved for it. -/

/-- A list of rows whose every vector lies in a span generates a subspace of
    that span: `inSpanRows` is closed under `xorVec` and contains the zero
    vector. -/
theorem spanLE_of_forall_mem (Q : List Nat) {rows₁ rows₂ : List Row}
    (h : ∀ r ∈ rows₁, inSpanRows Q rows₂ (rowVector Q r)) : SpanLE Q rows₁ rows₂ := by
  intro v hv
  obtain ⟨cs, hlen, hcomb⟩ := hv
  rw [← hcomb]
  clear hcomb
  induction rows₁ generalizing cs with
  | nil =>
      cases cs with
      | nil =>
          show inSpanRows Q rows₂ (List.replicate Q.length false)
          have hzero := combineRows_zero_coeffs Q.length (rows₂.map (rowVector Q))
          rw [List.length_map] at hzero
          exact ⟨List.replicate rows₂.length false, List.length_replicate .., hzero⟩
      | cons _ _ => cases hlen
  | cons r rs ih =>
      cases cs with
      | nil => cases hlen
      | cons c cs' =>
          have hlen' : cs'.length = rs.length := Nat.succ.inj hlen
          have hr : inSpanRows Q rows₂ (rowVector Q r) := h r (List.mem_cons_self ..)
          have hrs : ∀ r' ∈ rs, inSpanRows Q rows₂ (rowVector Q r') :=
            fun r' hr' => h r' (List.mem_cons_of_mem r hr')
          cases c with
          | true =>
              show inSpanRows Q rows₂
                (xorVec (rowVector Q r) (combineRows Q.length (rs.map (rowVector Q)) cs'))
              exact inSpanRows_xor Q rows₂ hr (ih hrs cs' hlen')
          | false =>
              show inSpanRows Q rows₂ (combineRows Q.length (rs.map (rowVector Q)) cs')
              exact ih hrs cs' hlen'

/-- The rebased sector's span lies in the old sector's span, over vectors
    (the mask-level inclusion `rebaseState_spanMasks_sub` through the bridge
    `inSpanRows_iff_inSpanMasks`, which needs a repeat-free namespace). -/
theorem rebaseState_spanLE_sub (s : CodeState) (σ : Sector) (M : List (List Nat))
    (hQ : s.Q.Nodup) (hok : rebaseMatrix_ok M (sectorRows s σ).length) :
    SpanLE s.Q (sectorRows (rebaseState s σ M) σ) (sectorRows s σ) := by
  apply spanLE_of_forall_mem
  intro r hr
  rw [inSpanRows_iff_inSpanMasks s.Q hQ]
  have hmem : rowBitmask s.Q r ∈ (sectorRows (rebaseState s σ M) σ).map (rowBitmask s.Q) :=
    List.mem_map_of_mem hr
  rw [rebaseState_sector_masks] at hmem
  exact rebaseState_spanMasks_sub s σ M hok _ (inSpanMasks_of_mem hmem)

/-- The old sector's span lies in the rebased sector's span, over vectors
    (`rebaseState_spanMasks_sup`, through the same bridge). -/
theorem rebaseState_spanLE_sup (s : CodeState) (σ : Sector) (M : List (List Nat))
    (hQ : s.Q.Nodup) (hok : rebaseMatrix_ok M (sectorRows s σ).length) :
    SpanLE s.Q (sectorRows s σ) (sectorRows (rebaseState s σ M) σ) := by
  apply spanLE_of_forall_mem
  intro r hr
  rw [inSpanRows_iff_inSpanMasks s.Q hQ, rebaseState_sector_masks]
  exact rebaseState_spanMasks_sup s σ M hok _ (inSpanMasks_of_mem (List.mem_map_of_mem hr))

/-- §4.26 for the exact distance: a rebase changes neither sector distance.
    Both sector spans are unchanged (the rebased one by the two inclusions
    above, the other by `sectorRows_rebaseState_other`), and the namespace
    is unchanged, so the σ-logicals are the same vectors. -/
theorem exactDistance_rebaseState (s : CodeState) (σ : Sector) (M : List (List Nat))
    (hQ : s.Q.Nodup) (hok : rebaseMatrix_ok M (sectorRows s σ).length) (τ : Sector) :
    exactDistance τ (rebaseState s σ M) = exactDistance τ s := by
  have hother : ∀ τ', τ' ≠ σ → sectorRows (rebaseState s σ M) τ' = sectorRows s τ' := by
    intro τ' hne
    have hτ' : τ' = oppositeSector σ := by
      cases τ' <;> cases σ <;> first | rfl | exact absurd rfl hne
    rw [hτ']
    exact sectorRows_rebaseState_other s σ M
  have hsub : ∀ τ', SpanLE s.Q (sectorRows (rebaseState s σ M) τ') (sectorRows s τ') := by
    intro τ'
    by_cases hτ : τ' = σ
    · subst hτ
      exact rebaseState_spanLE_sub s τ' M hQ hok
    · rw [hother τ' hτ]
      exact fun v hv => hv
  have hsup : ∀ τ', SpanLE s.Q (sectorRows s τ') (sectorRows (rebaseState s σ M) τ') := by
    intro τ'
    by_cases hτ : τ' = σ
    · subst hτ
      exact rebaseState_spanLE_sup s τ' M hQ hok
    · rw [hother τ' hτ]
      exact fun v hv => hv
  exact Nat.le_antisymm
    (exactDistance_le_of_spanLE s (rebaseState s σ M) τ rfl (hsub τ) (hsub _))
    (exactDistance_le_of_spanLE (rebaseState s σ M) s τ rfl (hsup τ) (hsup _))

/-- `rowVector` reads the support only, so the sector swap does not change
    the row vectors. -/
theorem map_rowVector_swapRow (Q : List Nat) (rows : List Row) :
    (rows.map swapRow).map (rowVector Q) = rows.map (rowVector Q) := by
  rw [List.map_map]
  rfl

/-- The swapped state's σ-display is the original's opposite-sector display
    with the labels moved (`sector_swap_filter`). -/
theorem sectorRows_swapState (s : CodeState) (σ : Sector) :
    sectorRows (swapState s) σ = (sectorRows s (oppositeSector σ)).map swapRow :=
  sector_swap_filter σ s.rows

/-- A σ-logical of the swapped state is an opposite-sector logical of the
    original: orthogonality and span membership read supports only. -/
theorem isLogicalBool_swapState (s : CodeState) (σ : Sector) (v : List Bool) :
    isLogicalBool (swapState s) σ v = isLogicalBool s (oppositeSector σ) v := by
  unfold isLogicalBool
  rw [sectorRows_swapState s (oppositeSector σ), sectorRows_swapState s σ,
    oppositeSector_involutive, List.all_map]
  unfold inSpanRowsBool
  rw [List.length_map, map_rowVector_swapRow]
  rfl

theorem logicalVectors_swapState (s : CodeState) (σ : Sector) :
    logicalVectors (swapState s) σ = logicalVectors s (oppositeSector σ) := by
  have hfun : isLogicalBool (swapState s) σ = isLogicalBool s (oppositeSector σ) :=
    funext (isLogicalBool_swapState s σ)
  unfold logicalVectors
  rw [hfun]
  rfl

/-- §4.27 for the exact distance: the sector exchange exchanges the two
    sector distances. -/
theorem exactDistance_swapState (s : CodeState) (σ : Sector) :
    exactDistance σ (swapState s) = exactDistance (oppositeSector σ) s := by
  unfold exactDistance
  rw [logicalVectors_swapState]
  rfl

/-- The same through the `hadamard` state update, for `T ≠ ∅` (the `T = ∅`
    instance is the identity on the state). -/
theorem exactDistance_hadamardState (s : CodeState) {T : List Nat} (hT : T ≠ []) (σ : Sector) :
    exactDistance σ (hadamardState s T) = exactDistance (oppositeSector σ) s := by
  cases T with
  | nil => exact absurd rfl hT
  | cons a T' => exact exactDistance_swapState s σ

/-- Extension appends rows, so each sector's display grows as a sublist. -/
theorem sectorRows_extendState_sublist (s : CodeState) (delta : List Nat)
    (adds : List (Sector × List Nat)) (τ : Sector) :
    (sectorRows s τ).Sublist (sectorRows (extendState s delta adds) τ) := by
  show (s.rows.filter (fun r => r.sector = τ)).Sublist
    ((s.rows ++ _).filter (fun r => r.sector = τ))
  rw [List.filter_append]
  exact List.sublist_append_left _ _

/-- §4.30 with `Δ = ∅` for the exact distance: adding rows does not lower a
    sector distance, when the namespace is unchanged. `extendState` re-sorts
    the namespace and removes repeats, so the hypothesis holds exactly when
    `s.Q` is sorted and repeat-free, as every fixture state is. -/
theorem exactDistance_extendState_le (s : CodeState) (adds : List (Sector × List Nat))
    (hQ : (extendState s [] adds).Q = s.Q) (σ : Sector) :
    exactDistance σ s ≤ exactDistance σ (extendState s [] adds) :=
  exactDistance_le_of_spanLE (extendState s [] adds) s σ hQ.symm
    (spanLE_of_sublist _ (sectorRows_extendState_sublist s [] adds σ))
    (spanLE_of_sublist _ (sectorRows_extendState_sublist s [] adds (oppositeSector σ)))

/-! ## The exact distance in `Option Nat`, and the per-cell instances -/

/-- The exact sector distance read in `Option Nat`: the sentinel `|Q| + 1`
    of `exactDistance` (no σ-logical) is read as `+∞`. -/
def exactDistOpt (σ : Sector) (s : CodeState) : Option Nat :=
  if exactDistance σ s = s.Q.length + 1 then none else some (exactDistance σ s)

/-- The exact distances of a state as the interval slice reads them. -/
def exactDist (s : CodeState) : ExactDist :=
  { full := minOpt (exactDistOpt Sector.X s) (exactDistOpt Sector.Z s)
  , x := exactDistOpt Sector.X s
  , z := exactDistOpt Sector.Z s }

theorem exactDist_full (s : CodeState) :
    (exactDist s).full = minOpt (exactDist s).x (exactDist s).z := rfl

theorem exactDistOpt_congr {σ σ' : Sector} {s t : CodeState} (hQ : t.Q.length = s.Q.length)
    (h : exactDistance σ t = exactDistance σ' s) : exactDistOpt σ t = exactDistOpt σ' s := by
  unfold exactDistOpt
  rw [hQ, h]

/-- The exact distance is bounded by its sentinel. -/
theorem exactDistance_le_sentinel (σ : Sector) (s : CodeState) :
    exactDistance σ s ≤ s.Q.length + 1 :=
  minWeight_le_init _ _

/-- `≤` on exact distances lifts to `leOpt` on their `Option Nat` readings
    when the two namespaces have the same length. -/
theorem leOpt_exactDistOpt_of_le {σ : Sector} {s t : CodeState} (hQ : t.Q.length = s.Q.length)
    (h : exactDistance σ s ≤ exactDistance σ t) : leOpt (exactDistOpt σ s) (exactDistOpt σ t) := by
  have hsent : exactDistance σ t ≤ s.Q.length + 1 := by
    rw [← hQ]
    exact exactDistance_le_sentinel σ t
  unfold exactDistOpt
  rw [hQ]
  by_cases hs : exactDistance σ s = s.Q.length + 1
  · have ht : exactDistance σ t = s.Q.length + 1 := Nat.le_antisymm hsent (hs ▸ h)
    rw [ite_eq_left hs, ite_eq_left ht]
    exact trivial
  · by_cases ht : exactDistance σ t = s.Q.length + 1
    · rw [ite_eq_right hs, ite_eq_left ht]
      exact trivial
    · rw [ite_eq_right hs, ite_eq_right ht]
      exact h

theorem exactDist_rebaseState (s : CodeState) (σ : Sector) (M : List (List Nat))
    (hQ : s.Q.Nodup) (hok : rebaseMatrix_ok M (sectorRows s σ).length) :
    exactDist (rebaseState s σ M) = exactDist s := by
  have hx : exactDistOpt Sector.X (rebaseState s σ M) = exactDistOpt Sector.X s :=
    exactDistOpt_congr rfl (exactDistance_rebaseState s σ M hQ hok Sector.X)
  have hz : exactDistOpt Sector.Z (rebaseState s σ M) = exactDistOpt Sector.Z s :=
    exactDistOpt_congr rfl (exactDistance_rebaseState s σ M hQ hok Sector.Z)
  unfold exactDist
  rw [hx, hz]

theorem exactDist_swapState (s : CodeState) :
    (exactDist (swapState s)).x = (exactDist s).z ∧ (exactDist (swapState s)).z = (exactDist s).x :=
  ⟨exactDistOpt_congr rfl (exactDistance_swapState s Sector.X),
    exactDistOpt_congr rfl (exactDistance_swapState s Sector.Z)⟩

/-- `P-REBASE` for the exact distance, from the transition's premises: no
    distance hypothesis is left. -/
theorem rebase_transformer_sound_exact {σ : Sector} {M : List (List Nat)} {s s' : CodeState}
    (hQ : s.Q.Nodup) (h : Eval (Command.rebase σ M) s s')
    (L : DistanceLedger) (hL : LedgerSound (exactDist s) L) :
    LedgerSound (exactDist s') L := by
  cases h with
  | rebase _ hok hs' _ =>
      subst hs'
      exact rebase_transformer_sound exactDist (exactDist_rebaseState s σ M hQ hok) L hL

/-- `E-LOCAL-HADAMARD` (`T = Q`) for the exact distance, from the
    transition's premises: no distance hypothesis is left. -/
theorem hadamard_transformer_sound_exact {T : List Nat} {s s' : CodeState} (hT : T ≠ [])
    (h : Eval (Command.hadamard T) s s')
    (L : DistanceLedger) (hL : LedgerSound (exactDist s) L) :
    LedgerSound (exactDist s') (hadamardLedger L) := by
  cases h with
  | hadamard _ hs' _ =>
      subst hs'
      cases T with
      | nil => exact absurd rfl hT
      | cons a T' =>
          obtain ⟨hx, hz⟩ := exactDist_swapState s
          exact hadamard_transformer_sound exactDist exactDist_full hx hz L hL

/-- `E-EXTEND` with `Δ = ∅` for the exact distance, on an unchanged
    namespace: no distance hypothesis is left. -/
theorem extend_transformer_sound_exact {adds : List (Sector × List Nat)} {s s' : CodeState}
    (hQ : (extendState s [] adds).Q = s.Q) (h : Eval (Command.extend [] adds) s s')
    (L : DistanceLedger) (hL : LedgerSound (exactDist s) L) :
    LedgerSound (exactDist s') (carryLowerLedger L) := by
  cases h with
  | extend _ hs' _ =>
      subst hs'
      have hlen : (extendState s [] adds).Q.length = s.Q.length := by rw [hQ]
      have hx : leOpt (exactDist s).x (exactDist (extendState s [] adds)).x :=
        leOpt_exactDistOpt_of_le hlen (exactDistance_extendState_le s adds hQ Sector.X)
      have hz : leOpt (exactDist s).z (exactDist (extendState s [] adds)).z :=
        leOpt_exactDistOpt_of_le hlen (exactDistance_extendState_le s adds hQ Sector.Z)
      exact extend_transformer_sound exactDist ⟨minOpt_monotone hx hz, hx, hz⟩ L hL

end CodeCalculus
