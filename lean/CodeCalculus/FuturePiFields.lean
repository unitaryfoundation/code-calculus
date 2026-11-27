import CodeCalculus.WitnessFields
import CodeCalculus.Gate6Soundness

/-!
# Candidate future-`Π` field sketches: construction record and logical frame

Mechanizes the two sketch-refinement candidates cataloged in
`design/FUTURE_PI_FIELDS.md` (§2.5 and §2.8, issue #544), strictly outside
`CodeState` (`C = (Q, X, Z, pres, used)` is unchanged; neither field is read
by state equality `≡`, minted, or admitted to `spec/STATE_MODEL.md` §1a by
this module):

* **Construction record (`ConstructionRecord`, Row 5):** an optional closed
  construction term `Option ClosedTerm` recording how a state was obtained.
  `ConstructionRecord.Valid s rec` asserts that a present record evaluates to
  `s` (`EvalTerm`). `ConstructionRecord.transportCmd` transports any record
  along every admitted command (`constructionRecord_transportCmd_valid`),
  while `ConstructionRecord.transportCmdPure` enforces a pure-expression
  policy that drops on non-`skip` commands. Expression constructors lift pure
  records (`transportDirectSum`, `transportGlue`, `transportConcat`,
  `transportProduct`, `transportDouble`, `transportPpScale`) and drop
  deformed ones at the `StateExpr`/`ClosedTerm` boundary.
* **Logical frame (`LogicalFrame`, Row 8):** a list of paired `X`- and
  `Z`-logical representatives (`FramePair`) satisfying validity `(F1)` and
  canonical symplectic pairing `(F2)` (`LogicalFrame.Dual`: paired
  representatives overlap oddly, distinct pairs overlap evenly). Projecting a
  well-formed frame yields a sound, one-per-class `LogField`
  (`frame_xField_sound`, `frame_zField_sound`, `frame_toLogField_sound`,
  `frame_xField_onePerClass`, `frame_zField_onePerClass`,
  `frame_toLogField_onePerClass`), coupling directly to `WitnessFields.lean`.
  `transportFrame` filters candidate pairs to those valid in the child while
  preserving `(F2)` (`transportFrame_wellFormed_of_dual`), yielding sound
  transport theorems for `C-SKIP`, `C-DELETE-CHECK`, `C-ADD-CHECK`,
  `P-REBASE`, `E-LOCAL-HADAMARD` (`T = Q`), `C-DIRECT-SUM`, and `E-GLUE`.
-/

namespace CodeCalculus

/-! ## Part 1: Construction record (Row 5 sketch-refinement candidate) -/

/-- A construction record held beside a state: `none` when unrecorded or
    dropped, or `some t` for a closed construction term `t`. -/
abbrev ConstructionRecord := Option ClosedTerm

/-- A construction record is valid on `s` when, if present, its term evaluates
    to `s`. -/
def ConstructionRecord.Valid (s : CodeState) : ConstructionRecord → Prop
  | none => True
  | some t => EvalTerm t s

/-- A construction record holds an unmodified state expression (no nontrivial
    command applied after the constructor expression). -/
def ConstructionRecord.IsPureExpr : ConstructionRecord → Prop
  | some ⟨Command.skip, _⟩ => True
  | _ => False

/-- Extracts the underlying `StateExpr` of a pure-expression construction
    record, returning `none` if unrecorded or deformed by a command. -/
def ConstructionRecord.pureExpr? : ConstructionRecord → Option StateExpr
  | some ⟨Command.skip, e⟩ => some e
  | _ => none

/-- Initial construction record for a state evaluated from an expression `e`. -/
def ConstructionRecord.ofExpr (e : StateExpr) : ConstructionRecord :=
  some ⟨Command.skip, e⟩

theorem constructionRecord_none_valid (s : CodeState) :
    ConstructionRecord.Valid s none := trivial

theorem constructionRecord_ofExpr_valid {e : StateExpr} {s : CodeState}
    (he : EvalExpr e s) :
    ConstructionRecord.Valid s (ConstructionRecord.ofExpr e) :=
  EvalTerm.eval he (Eval.skip s)

theorem constructionRecord_ofExpr_isPure (e : StateExpr) :
    ConstructionRecord.IsPureExpr (ConstructionRecord.ofExpr e) := trivial

theorem constructionRecord_pureExpr?_valid {s : CodeState} {rec : ConstructionRecord}
    {e : StateExpr} (hv : ConstructionRecord.Valid s rec)
    (hp : ConstructionRecord.pureExpr? rec = some e) :
    EvalExpr e s := by
  cases rec with
  | none => exact nomatch hp
  | some t =>
      cases t with
      | mk m e' =>
          cases m with
          | skip =>
              cases hp
              cases hv with
              | eval he hm =>
                  cases hm
                  exact he
          | delete _ => exact nomatch hp
          | addStab _ _ => exact nomatch hp
          | graft _ _ _ => exact nomatch hp
          | peel _ _ _ => exact nomatch hp
          | puncture _ => exact nomatch hp
          | extend _ _ => exact nomatch hp
          | hadamard _ => exact nomatch hp
          | rebase _ _ => exact nomatch hp
          | cnotSwap _ => exact nomatch hp
          | split _ _ => exact nomatch hp
          | seq _ _ => exact nomatch hp

/-- Command transport (provenance-preserving): appends `m` to the recorded
    closed term, absorbing a leading `skip`. Holds for every admitted command. -/
def ConstructionRecord.transportCmd (m : Command) : ConstructionRecord → ConstructionRecord
  | none => none
  | some ⟨Command.skip, e⟩ => some ⟨m, e⟩
  | some ⟨m0, e⟩ => some ⟨Command.seq m0 m, e⟩

/-- Soundness of command transport for every admitted command `m`. -/
theorem constructionRecord_transportCmd_valid {m : Command} {s s' : CodeState}
    {rec : ConstructionRecord} (hv : ConstructionRecord.Valid s rec)
    (heval : Eval m s s') :
    ConstructionRecord.Valid s' (ConstructionRecord.transportCmd m rec) := by
  cases rec with
  | none => trivial
  | some t =>
      cases t with
      | mk m0 e =>
          cases hv with
          | eval hex hm0 =>
              cases m0 with
              | skip =>
                  cases hm0
                  exact EvalTerm.eval hex heval
              | delete _ => exact EvalTerm.eval hex (Eval.seq hm0 heval)
              | addStab _ _ => exact EvalTerm.eval hex (Eval.seq hm0 heval)
              | graft _ _ _ => exact EvalTerm.eval hex (Eval.seq hm0 heval)
              | peel _ _ _ => exact EvalTerm.eval hex (Eval.seq hm0 heval)
              | puncture _ => exact EvalTerm.eval hex (Eval.seq hm0 heval)
              | extend _ _ => exact EvalTerm.eval hex (Eval.seq hm0 heval)
              | hadamard _ => exact EvalTerm.eval hex (Eval.seq hm0 heval)
              | rebase _ _ => exact EvalTerm.eval hex (Eval.seq hm0 heval)
              | cnotSwap _ => exact EvalTerm.eval hex (Eval.seq hm0 heval)
              | split _ _ => exact EvalTerm.eval hex (Eval.seq hm0 heval)
              | seq _ _ => exact EvalTerm.eval hex (Eval.seq hm0 heval)

/-- Strict pure-expression command transport: preserves the record on `skip`
    and drops it to `none` on any state-modifying command. -/
def ConstructionRecord.transportCmdPure : Command → ConstructionRecord → ConstructionRecord
  | Command.skip, rec => rec
  | _, _ => none

theorem constructionRecord_transportCmdPure_valid {m : Command} {s s' : CodeState}
    {rec : ConstructionRecord} (hv : ConstructionRecord.Valid s rec)
    (heval : Eval m s s') :
    ConstructionRecord.Valid s' (ConstructionRecord.transportCmdPure m rec) := by
  cases m with
  | skip =>
      cases heval
      exact hv
  | delete _ => trivial
  | addStab _ _ => trivial
  | graft _ _ _ => trivial
  | peel _ _ _ => trivial
  | puncture _ => trivial
  | extend _ _ => trivial
  | hadamard _ => trivial
  | rebase _ _ => trivial
  | cnotSwap _ => trivial
  | split _ _ => trivial
  | seq _ _ => trivial

/-- Lifting a binary state-expression constructor across two construction
    records: keeps a pure-expression record when both factors are pure
    expressions, and drops to `none` otherwise (the `StateExpr`/`ClosedTerm`
    syntactic boundary). -/
def ConstructionRecord.liftBinary (ctor : StateExpr → StateExpr → StateExpr)
    (r1 r2 : ConstructionRecord) : ConstructionRecord :=
  match ConstructionRecord.pureExpr? r1, ConstructionRecord.pureExpr? r2 with
  | some e1, some e2 => ConstructionRecord.ofExpr (ctor e1 e2)
  | _, _ => none

/-- Lifting a unary state-expression constructor across one construction
    record. -/
def ConstructionRecord.liftUnary (ctor : StateExpr → StateExpr)
    (r : ConstructionRecord) : ConstructionRecord :=
  match ConstructionRecord.pureExpr? r with
  | some e => ConstructionRecord.ofExpr (ctor e)
  | none => none

theorem constructionRecord_liftBinary_valid {ctor : StateExpr → StateExpr → StateExpr}
    {s1 s2 s : CodeState} {r1 r2 : ConstructionRecord}
    (hv1 : ConstructionRecord.Valid s1 r1) (hv2 : ConstructionRecord.Valid s2 r2)
    (hstep : ∀ e1 e2, EvalExpr e1 s1 → EvalExpr e2 s2 → EvalExpr (ctor e1 e2) s) :
    ConstructionRecord.Valid s (ConstructionRecord.liftBinary ctor r1 r2) := by
  unfold ConstructionRecord.liftBinary
  cases h1 : ConstructionRecord.pureExpr? r1 with
  | none => trivial
  | some e1 =>
      cases h2 : ConstructionRecord.pureExpr? r2 with
      | none => trivial
      | some e2 =>
          exact constructionRecord_ofExpr_valid
            (hstep e1 e2 (constructionRecord_pureExpr?_valid hv1 h1)
              (constructionRecord_pureExpr?_valid hv2 h2))

theorem constructionRecord_liftUnary_valid {ctor : StateExpr → StateExpr}
    {s1 s : CodeState} {r : ConstructionRecord}
    (hv : ConstructionRecord.Valid s1 r)
    (hstep : ∀ e, EvalExpr e s1 → EvalExpr (ctor e) s) :
    ConstructionRecord.Valid s (ConstructionRecord.liftUnary ctor r) := by
  unfold ConstructionRecord.liftUnary
  cases h1 : ConstructionRecord.pureExpr? r with
  | none => trivial
  | some e =>
      exact constructionRecord_ofExpr_valid
        (hstep e (constructionRecord_pureExpr?_valid hv h1))

/-- Direct-sum transport for construction records. -/
theorem constructionRecord_directSum_valid {s1 s2 : CodeState} {r1 r2 : ConstructionRecord}
    (hv1 : ConstructionRecord.Valid s1 r1) (hv2 : ConstructionRecord.Valid s2 r2)
    (hQ : DisjointList s1.Q s2.Q) (hU : DisjointList s1.used s2.used) :
    ConstructionRecord.Valid (directSumState s1 s2)
      (ConstructionRecord.liftBinary StateExpr.directSum r1 r2) :=
  constructionRecord_liftBinary_valid hv1 hv2
    (fun _ _ h1 h2 => EvalExpr.directSum hQ hU h1 h2)

/-- `E-GLUE` transport for construction records. -/
theorem constructionRecord_glue_valid {s1 s2 : CodeState} {seams : List (Sector × List Nat)}
    {r1 r2 : ConstructionRecord}
    (hv1 : ConstructionRecord.Valid s1 r1) (hv2 : ConstructionRecord.Valid s2 r2)
    (hQ : DisjointList s1.Q s2.Q) (hU : DisjointList s1.used s2.used)
    (hwf : EncodingWellFormed (glueState s1 s2 seams))
    (hcap : MintsWithinCapacity (s1.used ++ s2.used) seams.length) :
    ConstructionRecord.Valid (glueState s1 s2 seams)
      (ConstructionRecord.liftBinary (fun e1 e2 => StateExpr.glue e1 e2 seams) r1 r2) :=
  constructionRecord_liftBinary_valid hv1 hv2
    (fun _ _ h1 h2 => EvalExpr.glue hQ hU hwf hcap h1 h2)

/-- `A-CONCAT` transport for construction records. -/
theorem constructionRecord_concat_valid {sO sI : CodeState}
    {blocks repsX repsZ : List (List Nat)} {rO rI : ConstructionRecord}
    (hvO : ConstructionRecord.Valid sO rO) (hvI : ConstructionRecord.Valid sI rI)
    (hO : EncodingWellFormed sO) (hI : EncodingWellFormed sI)
    (hty : concatTyped sO sI blocks repsX repsZ = true)
    (hcap : MintsWithinCapacity [] (concatState sO sI blocks repsX repsZ).rows.length) :
    ConstructionRecord.Valid (concatState sO sI blocks repsX repsZ)
      (ConstructionRecord.liftBinary (fun eO eI => StateExpr.concat eO eI blocks repsX repsZ)
        rO rI) :=
  constructionRecord_liftBinary_valid hvO hvI
    (fun _ _ h1 h2 => EvalExpr.concat hO hI hty hcap h1 h2)

/-- `A-PRODUCT` transport for construction records. -/
theorem constructionRecord_product_valid {sA sB : CodeState} {rA rB : ConstructionRecord}
    (hvA : ConstructionRecord.Valid sA rA) (hvB : ConstructionRecord.Valid sB rB)
    (hA : EncodingWellFormed sA) (hB : EncodingWellFormed sB)
    (hcap : MintsWithinCapacity [] (productState sA sB).rows.length) :
    ConstructionRecord.Valid (productState sA sB)
      (ConstructionRecord.liftBinary StateExpr.product rA rB) :=
  constructionRecord_liftBinary_valid hvA hvB
    (fun _ _ h1 h2 => EvalExpr.product hA hB hcap h1 h2)

/-- `A-DOUBLE` transport for construction records. -/
theorem constructionRecord_double_valid {sC : CodeState} {wiring : List (Nat × List Nat)}
    {conj : Bool} {rC : ConstructionRecord}
    (hvC : ConstructionRecord.Valid sC rC) (hC : EncodingWellFormed sC)
    (hty : doubleTyped sC wiring = true)
    (hcomm : naturalCommuteBool (naturalRows (doubleQubits sC)
      (doubleVectors sC wiring conj)) = true)
    (hcap : MintsWithinCapacity [] (doubleState sC wiring conj).rows.length) :
    ConstructionRecord.Valid (doubleState sC wiring conj)
      (ConstructionRecord.liftUnary (fun e => StateExpr.double e wiring conj) rC) :=
  constructionRecord_liftUnary_valid hvC
    (fun _ h1 => EvalExpr.double hC hty hcomm hcap h1)

/-- `PP-SCALE` transport for construction records. -/
theorem constructionRecord_ppScale_valid {s : CodeState} {P : Nat}
    {BX BZ : List (List (Nat × Nat))} {r : ConstructionRecord}
    (hv : ConstructionRecord.Valid s r) (hC : EncodingWellFormed s)
    (hty : ppScaleTyped s P BX BZ = true)
    (hcomm : naturalCommuteBool (naturalRows (pairPartitionQubits P BX)
      (pairPartitionVectors P BX BZ)) = true)
    (hcap : MintsWithinCapacity s.used (ppScaleState s P BX BZ).rows.length) :
    ConstructionRecord.Valid (ppScaleState s P BX BZ)
      (ConstructionRecord.liftUnary (fun e => StateExpr.ppScale e P BX BZ) r) :=
  constructionRecord_liftUnary_valid hv
    (fun _ h1 => EvalExpr.ppScale hC hty hcomm hcap h1)

/-! ## Part 2: Logical frame (Row 8 sketch-refinement candidate) -/

/-- One symplectic logical pair: an `X`-sector representative paired with a
    `Z`-sector representative, each carrying its eigenvalue sign bit. -/
structure FramePair where
  xVec : List Bool
  zVec : List Bool
  xSign : Bool
  zSign : Bool
  deriving DecidableEq

/-- The `X`-sector `LogRep` projected from a frame pair. -/
def FramePair.xRep (p : FramePair) : LogRep :=
  { vec := p.xVec, sector := Sector.X, sign := p.xSign }

/-- The `Z`-sector `LogRep` projected from a frame pair. -/
def FramePair.zRep (p : FramePair) : LogRep :=
  { vec := p.zVec, sector := Sector.Z, sign := p.zSign }

/-- A frame pair is valid in `s` when both its `X` and `Z` representatives
    are valid logicals of `s`. -/
def FramePair.validIn (s : CodeState) (p : FramePair) : Bool :=
  p.xRep.validIn s && p.zRep.validIn s

theorem FramePair.validIn_iff (s : CodeState) (p : FramePair) :
    p.validIn s = true ↔
      (p.xVec.length = s.Q.length ∧ isLogicalBool s Sector.X p.xVec = true) ∧
      (p.zVec.length = s.Q.length ∧ isLogicalBool s Sector.Z p.zVec = true) := by
  unfold FramePair.validIn FramePair.xRep FramePair.zRep
  rw [Bool.and_eq_true, LogRep.validIn_iff, LogRep.validIn_iff]

/-- Canonical symplectic pairing `(F2)` on a list of logical pairs: every pair
    anticommutes with itself (odd overlap) and commutes (even overlap) with
    every distinct pair. -/
def LogicalFrame.Dual : List FramePair → Prop
  | [] => True
  | p :: ps =>
      dotPar p.xVec p.zVec % 2 = 1 ∧
      (∀ q ∈ ps, dotPar p.xVec q.zVec % 2 = 0 ∧ dotPar q.xVec p.zVec % 2 = 0) ∧
      LogicalFrame.Dual ps

def LogicalFrame.decDual : (frame : List FramePair) → Decidable (LogicalFrame.Dual frame)
  | [] => isTrue trivial
  | p :: ps =>
      letI : Decidable (LogicalFrame.Dual ps) := LogicalFrame.decDual ps
      inferInstanceAs (Decidable (dotPar p.xVec p.zVec % 2 = 1 ∧
        (∀ q ∈ ps, dotPar p.xVec q.zVec % 2 = 0 ∧ dotPar q.xVec p.zVec % 2 = 0) ∧
        LogicalFrame.Dual ps))

instance (frame : List FramePair) : Decidable (LogicalFrame.Dual frame) :=
  LogicalFrame.decDual frame

/-- `(F1)` Validity of every pair in a logical frame. -/
def LogicalFrame.Sound (s : CodeState) (frame : List FramePair) : Prop :=
  ∀ p ∈ frame, p.validIn s = true

instance (s : CodeState) (frame : List FramePair) : Decidable (LogicalFrame.Sound s frame) :=
  inferInstanceAs (Decidable (∀ p ∈ frame, p.validIn s = true))

/-- Well-formedness of a logical frame on `s`: `(F1)` every pair consists of
    valid `X` and `Z` logicals of `s`, and `(F2)` the pairs satisfy canonical
    symplectic duality. -/
def LogicalFrame.WellFormed (s : CodeState) (frame : List FramePair) : Prop :=
  LogicalFrame.Sound s frame ∧ LogicalFrame.Dual frame

instance (s : CodeState) (frame : List FramePair) : Decidable (LogicalFrame.WellFormed s frame) :=
  inferInstanceAs (Decidable (LogicalFrame.Sound s frame ∧ LogicalFrame.Dual frame))

/-- Projection of the `X` representatives of a frame to a `LogField`. -/
def LogicalFrame.xField (frame : List FramePair) : List LogRep :=
  frame.map FramePair.xRep

/-- Projection of the `Z` representatives of a frame to a `LogField`. -/
def LogicalFrame.zField (frame : List FramePair) : List LogRep :=
  frame.map FramePair.zRep

/-- Projection of all representatives of a frame to a single `LogField`. -/
def LogicalFrame.toLogField (frame : List FramePair) : List LogRep :=
  LogicalFrame.xField frame ++ LogicalFrame.zField frame

/-! ### Coupling to `WitnessFields.lean`: soundness and automatic `OnePerClass` -/

theorem frame_xField_sound {s : CodeState} {frame : List FramePair}
    (h : LogicalFrame.Sound s frame) :
    LogField.Sound s (LogicalFrame.xField frame) := by
  intro e he
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
  exact ((FramePair.validIn_iff s p).mp (h p hp)).1

theorem frame_zField_sound {s : CodeState} {frame : List FramePair}
    (h : LogicalFrame.Sound s frame) :
    LogField.Sound s (LogicalFrame.zField frame) := by
  intro e he
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
  exact ((FramePair.validIn_iff s p).mp (h p hp)).2

theorem frame_toLogField_sound {s : CodeState} {frame : List FramePair}
    (h : LogicalFrame.Sound s frame) :
    LogField.Sound s (LogicalFrame.toLogField frame) := by
  intro e he
  rcases List.mem_append.mp he with hx | hz
  · exact frame_xField_sound h e hx
  · exact frame_zField_sound h e hz

/-- Two vectors in the same `σ`-class have the same overlap parity with any
    opposite-sector logical. -/
theorem dotPar_eq_of_mem_classVectors {s : CodeState} {σ : Sector} {u v w : List Bool}
    (hu : u.length = s.Q.length) (hw : isLogicalBool s (oppositeSector σ) w = true)
    (hcls : v ∈ classVectors s σ u) :
    dotPar v w % 2 = dotPar u w % 2 := by
  obtain ⟨hv, hspan⟩ := (mem_classVectors_iff s σ u v).mp hcls
  have hw_orth := ((isLogicalBool_iff_prop s (oppositeSector σ) w).mp hw).1
  rw [oppositeSector_involutive] at hw_orth
  have hev : dotPar w (xorVec v u) % 2 = 0 :=
    dotPar_even_of_inSpanRows s.Q (sectorRows s σ) w (xorVec v u) hspan hw_orth
  have hxor := dotPar_xorVec w v u (hv.trans hu.symm)
  rw [dotPar_comm w v, dotPar_comm w u] at hxor
  omega

/-- No two distinct pairs in a well-formed frame share an `X`-logical class. -/
theorem frame_x_distinct_of_wf {s : CodeState} :
    ∀ {frame : List FramePair}, LogicalFrame.WellFormed s frame →
      ∀ p ∈ frame, ∀ q ∈ frame, q.xVec ∈ classVectors s Sector.X p.xVec → p = q
  | [], _, _, hp, _, _, _ => absurd hp List.not_mem_nil
  | a :: ps, ⟨hsound, hself, hcross, hdual⟩, p, hp, q, hq, hcls => by
      have ha := (FramePair.validIn_iff s a).mp (hsound a (List.mem_cons_self ..))
      have hwf' : LogicalFrame.WellFormed s ps :=
        ⟨fun x hx => hsound x (List.mem_cons_of_mem a hx), hdual⟩
      rcases List.mem_cons.mp hp with rfl | hp'
      · rcases List.mem_cons.mp hq with rfl | hq'
        · rfl
        · have heq := dotPar_eq_of_mem_classVectors (σ := Sector.X) ha.1.1 ha.2.2 hcls
          have h0 := (hcross q hq').2
          omega
      · rcases List.mem_cons.mp hq with rfl | hq'
        · have hpp := (FramePair.validIn_iff s p).mp (hsound p (List.mem_cons_of_mem q hp'))
          have heq := dotPar_eq_of_mem_classVectors (σ := Sector.X) hpp.1.1 ha.2.2 hcls
          have h0 := (hcross p hp').2
          omega
        · exact frame_x_distinct_of_wf hwf' p hp' q hq' hcls

/-- No two distinct pairs in a well-formed frame share a `Z`-logical class. -/
theorem frame_z_distinct_of_wf {s : CodeState} :
    ∀ {frame : List FramePair}, LogicalFrame.WellFormed s frame →
      ∀ p ∈ frame, ∀ q ∈ frame, q.zVec ∈ classVectors s Sector.Z p.zVec → p = q
  | [], _, _, hp, _, _, _ => absurd hp List.not_mem_nil
  | a :: ps, ⟨hsound, hself, hcross, hdual⟩, p, hp, q, hq, hcls => by
      have ha := (FramePair.validIn_iff s a).mp (hsound a (List.mem_cons_self ..))
      have hwf' : LogicalFrame.WellFormed s ps :=
        ⟨fun x hx => hsound x (List.mem_cons_of_mem a hx), hdual⟩
      rcases List.mem_cons.mp hp with rfl | hp'
      · rcases List.mem_cons.mp hq with rfl | hq'
        · rfl
        · have heq := dotPar_eq_of_mem_classVectors (σ := Sector.Z) ha.2.1 ha.1.2 hcls
          rw [dotPar_comm q.zVec p.xVec, dotPar_comm p.zVec p.xVec] at heq
          have h0 := (hcross q hq').1
          omega
      · rcases List.mem_cons.mp hq with rfl | hq'
        · have hpp := (FramePair.validIn_iff s p).mp (hsound p (List.mem_cons_of_mem q hp'))
          have heq := dotPar_eq_of_mem_classVectors (σ := Sector.Z) hpp.2.1 ha.1.2 hcls
          rw [dotPar_comm q.zVec q.xVec, dotPar_comm p.zVec q.xVec] at heq
          have h0 := (hcross p hp').1
          omega
        · exact frame_z_distinct_of_wf hwf' p hp' q hq' hcls

/-- Every well-formed logical frame automatically gives one-per-class `X`
    representatives. -/
theorem frame_xField_onePerClass {s : CodeState} {frame : List FramePair}
    (hwf : LogicalFrame.WellFormed s frame) :
    LogField.OnePerClass s (LogicalFrame.xField frame) := by
  intro e he e' he' _ hcls
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he'
  have hpq := frame_x_distinct_of_wf hwf p hp q hq hcls
  rw [hpq]

/-- Every well-formed logical frame automatically gives one-per-class `Z`
    representatives. -/
theorem frame_zField_onePerClass {s : CodeState} {frame : List FramePair}
    (hwf : LogicalFrame.WellFormed s frame) :
    LogField.OnePerClass s (LogicalFrame.zField frame) := by
  intro e he e' he' _ hcls
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he'
  have hpq := frame_z_distinct_of_wf hwf p hp q hq hcls
  rw [hpq]

/-- Every well-formed logical frame projects to a one-per-class `LogField`. -/
theorem frame_toLogField_onePerClass {s : CodeState} {frame : List FramePair}
    (hwf : LogicalFrame.WellFormed s frame) :
    LogField.OnePerClass s (LogicalFrame.toLogField frame) := by
  intro e he e' he' hsec hcls
  rcases List.mem_append.mp he with hx | hz
  · rcases List.mem_append.mp he' with hx' | hz'
    · exact frame_xField_onePerClass hwf e hx e' hx' hsec hcls
    · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hz'
      exact nomatch hsec
  · rcases List.mem_append.mp he' with hx' | hz'
    · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hz
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx'
      exact nomatch hsec
    · exact frame_zField_onePerClass hwf e hz e' hz' hsec hcls

/-! ### Generic frame transport and algebraic closure of `LogicalFrame.Dual` -/

/-- Filtering a list of pairs preserves canonical symplectic duality. -/
theorem dual_filter (pred : FramePair → Bool) :
    ∀ {frame : List FramePair}, LogicalFrame.Dual frame →
      LogicalFrame.Dual (frame.filter pred)
  | [], _ => trivial
  | p :: ps, ⟨hself, hcross, hdual⟩ => by
      cases hp : pred p with
      | true =>
          rw [List.filter_cons_of_pos hp]
          refine ⟨hself, fun q hq => hcross q (List.mem_filter.mp hq).1, dual_filter pred hdual⟩
      | false =>
          rw [List.filter_cons_of_neg (by rw [hp]; exact Bool.false_ne_true)]
          exact dual_filter pred hdual

/-- Concatenating two mutually orthogonal dual lists yields a dual list. -/
theorem dual_append :
    ∀ {A B : List FramePair}, LogicalFrame.Dual A → LogicalFrame.Dual B →
      (∀ a ∈ A, ∀ b ∈ B, dotPar a.xVec b.zVec % 2 = 0 ∧ dotPar b.xVec a.zVec % 2 = 0) →
      LogicalFrame.Dual (A ++ B)
  | [], _, _, hB, _ => hB
  | a :: A, B, ⟨hself, hcross, hA⟩, hB, hAB => by
      rw [List.cons_append]
      refine ⟨hself, fun q hq => ?_,
        dual_append hA hB (fun x hx => hAB x (List.mem_cons_of_mem a hx))⟩
      rcases List.mem_append.mp hq with hqA | hqB
      · exact hcross q hqA
      · exact hAB a (List.mem_cons_self ..) q hqB

/-- Generic transport of a logical frame to a child state: keep the candidate
    pairs whose `X` and `Z` representatives are both valid logicals of the
    child. -/
def transportFrame (child : CodeState) (cands : List FramePair) : List FramePair :=
  cands.filter (FramePair.validIn child)

theorem transportFrame_sound (child : CodeState) (cands : List FramePair) :
    LogicalFrame.Sound child (transportFrame child cands) := fun _ hp =>
  (List.mem_filter.mp hp).2

/-- If candidate pairs satisfy `(F2)`, their transported frame is well-formed
    on `child` (both `(F1)` and `(F2)` hold). -/
theorem transportFrame_wellFormed_of_dual (child : CodeState) (cands : List FramePair)
    (hdual : LogicalFrame.Dual cands) :
    LogicalFrame.WellFormed child (transportFrame child cands) :=
  ⟨transportFrame_sound child cands, dual_filter (FramePair.validIn child) hdual⟩

/-! ### Transition transport theorems for `LogicalFrame` -/

/-- `C-SKIP`: the frame is unchanged. -/
theorem frame_wellFormed_skip {s : CodeState} {frame : List FramePair}
    (hwf : LogicalFrame.WellFormed s frame) :
    LogicalFrame.WellFormed s frame := hwf

/-- `C-DELETE-CHECK`: every pair survives unchanged (deleting a check shrinks
    one sector's span and drops one constraint on the other, without changing
    `Q` or pairwise overlaps). -/
theorem frame_wellFormed_deleteState {s : CodeState} {r : Nat} {frame : List FramePair}
    (hwf : LogicalFrame.WellFormed s frame) :
    LogicalFrame.WellFormed (deleteState s r) frame := by
  refine ⟨fun p hp => ?_, hwf.2⟩
  have hv := (FramePair.validIn_iff s p).mp (hwf.1 p hp)
  apply (FramePair.validIn_iff (deleteState s r) p).mpr
  refine ⟨⟨hv.1.1, isLogical_mono s (deleteState s r) Sector.X rfl
    (spanLE_of_sublist _ (sectorRows_deleteState_sublist s r Sector.X))
    (spanLE_of_sublist _ (sectorRows_deleteState_sublist s r Sector.Z)) p.xVec hv.1.2⟩,
    ⟨hv.2.1, isLogical_mono s (deleteState s r) Sector.Z rfl
    (spanLE_of_sublist _ (sectorRows_deleteState_sublist s r Sector.Z))
    (spanLE_of_sublist _ (sectorRows_deleteState_sublist s r Sector.X)) p.zVec hv.2.2⟩⟩

/-- `C-ADD-CHECK`: keeping surviving pairs yields a well-formed frame. -/
theorem frame_wellFormed_addState {s : CodeState} {sec : Sector} {sup : List Nat}
    {frame : List FramePair} (hwf : LogicalFrame.WellFormed s frame) :
    LogicalFrame.WellFormed (addState s sec sup) (transportFrame (addState s sec sup) frame) :=
  transportFrame_wellFormed_of_dual (addState s sec sup) frame hwf.2

/-- `P-REBASE`: every pair survives unchanged (both sector spans and `Q` are
    unchanged). -/
theorem frame_wellFormed_rebaseState {s : CodeState} {σ : Sector} {M : List (List Nat)}
    {frame : List FramePair} (hQ : s.Q.Nodup)
    (hok : rebaseMatrix_ok M (sectorRows s σ).length)
    (hwf : LogicalFrame.WellFormed s frame) :
    LogicalFrame.WellFormed (rebaseState s σ M) frame := by
  have hsub : ∀ τ, SpanLE s.Q (sectorRows (rebaseState s σ M) τ) (sectorRows s τ) := by
    intro τ
    cases σ with
    | X =>
        cases τ with
        | X => exact rebaseState_spanLE_sub s Sector.X M hQ hok
        | Z =>
            show SpanLE s.Q (sectorRows (rebaseState s Sector.X M) (oppositeSector Sector.X))
              (sectorRows s (oppositeSector Sector.X))
            rw [sectorRows_rebaseState_other s Sector.X M]
            exact fun _ hv => hv
    | Z =>
        cases τ with
        | X =>
            show SpanLE s.Q (sectorRows (rebaseState s Sector.Z M) (oppositeSector Sector.Z))
              (sectorRows s (oppositeSector Sector.Z))
            rw [sectorRows_rebaseState_other s Sector.Z M]
            exact fun _ hv => hv
        | Z => exact rebaseState_spanLE_sub s Sector.Z M hQ hok
  refine ⟨fun p hp => ?_, hwf.2⟩
  have hv := (FramePair.validIn_iff s p).mp (hwf.1 p hp)
  apply (FramePair.validIn_iff (rebaseState s σ M) p).mpr
  refine ⟨⟨hv.1.1, isLogical_mono s (rebaseState s σ M) Sector.X rfl
      (hsub Sector.X) (hsub Sector.Z) p.xVec hv.1.2⟩,
    ⟨hv.2.1, isLogical_mono s (rebaseState s σ M) Sector.Z rfl
      (hsub Sector.Z) (hsub Sector.X) p.zVec hv.2.2⟩⟩

/-- Sector swap of a frame pair for `E-LOCAL-HADAMARD` (`T = Q`). -/
def FramePair.swap (p : FramePair) : FramePair :=
  { xVec := p.zVec, zVec := p.xVec, xSign := p.zSign, zSign := p.xSign }

theorem dual_map_swap :
    ∀ {frame : List FramePair}, LogicalFrame.Dual frame →
      LogicalFrame.Dual (frame.map FramePair.swap)
  | [], _ => trivial
  | p :: ps, ⟨hself, hcross, hdual⟩ => by
      rw [List.map_cons]
      refine ⟨by unfold FramePair.swap; rw [dotPar_comm]; exact hself, ?_,
        dual_map_swap hdual⟩
      intro q hq
      obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
      unfold FramePair.swap
      rw [dotPar_comm p.zVec q0.xVec, dotPar_comm q0.zVec p.xVec]
      exact ⟨(hcross q0 hq0).2, (hcross q0 hq0).1⟩

/-- `E-LOCAL-HADAMARD` (`T = Q`, i.e., `swapState`): swapping each pair's `X`
    and `Z` components preserves every pair and keeps the frame well-formed. -/
theorem frame_wellFormed_swapState {s : CodeState} {frame : List FramePair}
    (hwf : LogicalFrame.WellFormed s frame) :
    LogicalFrame.WellFormed (swapState s) (frame.map FramePair.swap) := by
  refine ⟨fun p hp => ?_, dual_map_swap hwf.2⟩
  obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hp
  have hv := (FramePair.validIn_iff s p0).mp (hwf.1 p0 hp0)
  apply (FramePair.validIn_iff (swapState s) p0.swap).mpr
  unfold FramePair.swap
  rw [isLogicalBool_swapState, isLogicalBool_swapState]
  exact ⟨hv.2, hv.1⟩

/-- Zero-extension of a frame pair from factor `a` to `a ⊕ b` / `glue a b`. -/
def FramePair.extendA (b : CodeState) (p : FramePair) : FramePair :=
  { p with
    xVec := p.xVec ++ List.replicate b.Q.length false,
    zVec := p.zVec ++ List.replicate b.Q.length false }

/-- Zero-extension of a frame pair from factor `b` to `a ⊕ b` / `glue a b`. -/
def FramePair.extendB (a : CodeState) (p : FramePair) : FramePair :=
  { p with
    xVec := List.replicate a.Q.length false ++ p.xVec,
    zVec := List.replicate a.Q.length false ++ p.zVec }

/-- Combined zero-extended frame candidates for `C-DIRECT-SUM` and `E-GLUE`. -/
def combineFrameCands (a b : CodeState) (frameA frameB : List FramePair) : List FramePair :=
  frameA.map (FramePair.extendA b) ++ frameB.map (FramePair.extendB a)

theorem dotPar_extendA (b : CodeState) (u v : List Bool) (h : u.length = v.length) :
    dotPar (u ++ List.replicate b.Q.length false) (v ++ List.replicate b.Q.length false) =
      dotPar u v := by
  rw [dotPar_append_eq u v _ _ h, dotPar_replicate_false, Nat.add_zero]

theorem dotPar_extendB (a : CodeState) (u v : List Bool) :
    dotPar (List.replicate a.Q.length false ++ u) (List.replicate a.Q.length false ++ v) =
      dotPar u v := by
  rw [dotPar_append_eq _ _ u v rfl, dotPar_replicate_false, Nat.zero_add]

theorem dotPar_extendA_extendB (a b : CodeState) (u v : List Bool)
    (hu : u.length = a.Q.length) :
    dotPar (u ++ List.replicate b.Q.length false) (List.replicate a.Q.length false ++ v) = 0 := by
  rw [dotPar_append_eq u (List.replicate a.Q.length false) _ v (by rw [hu, List.length_replicate]),
    dotPar_replicate_false, dotPar_comm, dotPar_replicate_false]

theorem dual_map_extendA (a b : CodeState) :
    ∀ {frame : List FramePair},
      (∀ p ∈ frame, p.xVec.length = a.Q.length ∧ p.zVec.length = a.Q.length) →
      LogicalFrame.Dual frame →
      LogicalFrame.Dual (frame.map (FramePair.extendA b))
  | [], _, _ => trivial
  | p :: ps, hlen, ⟨hself, hcross, hdual⟩ => by
      have hp := hlen p (List.mem_cons_self ..)
      rw [List.map_cons]
      refine ⟨by unfold FramePair.extendA
                 rw [dotPar_extendA b p.xVec p.zVec (hp.1.trans hp.2.symm)]
                 exact hself, ?_,
        dual_map_extendA a b (fun x hx => hlen x (List.mem_cons_of_mem p hx)) hdual⟩
      intro q hq
      obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
      have hqlen := hlen q0 (List.mem_cons_of_mem p hq0)
      unfold FramePair.extendA
      rw [dotPar_extendA b p.xVec q0.zVec (hp.1.trans hqlen.2.symm),
        dotPar_extendA b q0.xVec p.zVec (hqlen.1.trans hp.2.symm)]
      exact hcross q0 hq0

theorem dual_map_extendB (a : CodeState) :
    ∀ {frame : List FramePair}, LogicalFrame.Dual frame →
      LogicalFrame.Dual (frame.map (FramePair.extendB a))
  | [], _ => trivial
  | p :: ps, ⟨hself, hcross, hdual⟩ => by
      rw [List.map_cons]
      refine ⟨by unfold FramePair.extendB; rw [dotPar_extendB a p.xVec p.zVec]; exact hself, ?_,
        dual_map_extendB a hdual⟩
      intro q hq
      obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
      unfold FramePair.extendB
      rw [dotPar_extendB a p.xVec q0.zVec, dotPar_extendB a q0.xVec p.zVec]
      exact hcross q0 hq0

theorem dual_combineFrameCands {a b : CodeState} {frameA frameB : List FramePair}
    (hA : LogicalFrame.WellFormed a frameA) (hB : LogicalFrame.WellFormed b frameB) :
    LogicalFrame.Dual (combineFrameCands a b frameA frameB) := by
  have hlenA : ∀ p ∈ frameA, p.xVec.length = a.Q.length ∧ p.zVec.length = a.Q.length := by
    intro p hp
    have hv := (FramePair.validIn_iff a p).mp (hA.1 p hp)
    exact ⟨hv.1.1, hv.2.1⟩
  unfold combineFrameCands
  apply dual_append (dual_map_extendA a b hlenA hA.2) (dual_map_extendB a hB.2)
  intro x hx y hy
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
  have hpv := hlenA p hp
  unfold FramePair.extendA FramePair.extendB
  constructor
  · rw [dotPar_extendA_extendB a b p.xVec q.zVec hpv.1]
  · rw [dotPar_comm, dotPar_extendA_extendB a b p.zVec q.xVec hpv.2]

/-- `C-DIRECT-SUM`: extending both factor frames by zero and concatenating
    preserves every pair and yields a well-formed frame on `A ⊕ B`. -/
theorem frame_wellFormed_directSumState {a b : CodeState} {frameA frameB : List FramePair}
    (hQ : DisjointList a.Q b.Q) (hwfA : EncodingWellFormed a) (hwfB : EncodingWellFormed b)
    (hA : LogicalFrame.WellFormed a frameA) (hB : LogicalFrame.WellFormed b frameB) :
    LogicalFrame.WellFormed (directSumState a b) (combineFrameCands a b frameA frameB) := by
  let C := DirectSumCtx.ofWellFormed hQ hwfA hwfB
  refine ⟨fun p hp => ?_, dual_combineFrameCands hA hB⟩
  rcases List.mem_append.mp hp with hpA | hpB
  · obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hpA
    have hv := (FramePair.validIn_iff a p0).mp (hA.1 p0 hp0)
    apply (FramePair.validIn_iff (directSumState a b) (p0.extendA b)).mpr
    unfold FramePair.extendA
    have hqlen : (directSumState a b).Q.length = a.Q.length + b.Q.length := by
      rw [directSumState_Q, List.length_append]
    refine ⟨⟨by rw [List.length_append, List.length_replicate, hv.1.1, hqlen], ?_⟩,
      ⟨by rw [List.length_append, List.length_replicate, hv.2.1, hqlen], ?_⟩⟩
    · rw [C.isLogical_iff Sector.X p0.xVec (List.replicate b.Q.length false) hv.1.1]
      have hX := (isLogicalBool_iff_prop a Sector.X p0.xVec).mp hv.1.2
      exact ⟨⟨hX.1, fun r _ => by rw [dotPar_comm, dotPar_replicate_false]⟩, fun h => hX.2 h.1⟩
    · rw [C.isLogical_iff Sector.Z p0.zVec (List.replicate b.Q.length false) hv.2.1]
      have hZ := (isLogicalBool_iff_prop a Sector.Z p0.zVec).mp hv.2.2
      exact ⟨⟨hZ.1, fun r _ => by rw [dotPar_comm, dotPar_replicate_false]⟩, fun h => hZ.2 h.1⟩
  · obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hpB
    have hv := (FramePair.validIn_iff b p0).mp (hB.1 p0 hp0)
    apply (FramePair.validIn_iff (directSumState a b) (p0.extendB a)).mpr
    unfold FramePair.extendB
    have hqlen : (directSumState a b).Q.length = a.Q.length + b.Q.length := by
      rw [directSumState_Q, List.length_append]
    refine ⟨⟨by rw [List.length_append, List.length_replicate, hv.1.1, hqlen], ?_⟩,
      ⟨by rw [List.length_append, List.length_replicate, hv.2.1, hqlen], ?_⟩⟩
    · rw [C.isLogical_iff Sector.X (List.replicate a.Q.length false) p0.xVec List.length_replicate]
      have hX := (isLogicalBool_iff_prop b Sector.X p0.xVec).mp hv.1.2
      exact ⟨⟨fun r _ => by rw [dotPar_comm, dotPar_replicate_false], hX.1⟩, fun h => hX.2 h.2⟩
    · rw [C.isLogical_iff Sector.Z (List.replicate a.Q.length false) p0.zVec List.length_replicate]
      have hZ := (isLogicalBool_iff_prop b Sector.Z p0.zVec).mp hv.2.2
      exact ⟨⟨fun r _ => by rw [dotPar_comm, dotPar_replicate_false], hZ.1⟩, fun h => hZ.2 h.2⟩

/-- `E-GLUE` frame transport: keep the zero-extended factor pairs whose `X`
    and `Z` representatives both survive the seam. -/
def glueFrame (a b : CodeState) (seams : List (Sector × List Nat))
    (frameA frameB : List FramePair) : List FramePair :=
  transportFrame (glueState a b seams) (combineFrameCands a b frameA frameB)

/-- `E-GLUE`: `glueFrame` is well-formed whenever both factor frames are
    well-formed. -/
theorem frame_wellFormed_glueState {a b : CodeState} {seams : List (Sector × List Nat)}
    {frameA frameB : List FramePair}
    (hA : LogicalFrame.WellFormed a frameA) (hB : LogicalFrame.WellFormed b frameB) :
    LogicalFrame.WellFormed (glueState a b seams) (glueFrame a b seams frameA frameB) :=
  transportFrame_wellFormed_of_dual (glueState a b seams) _ (dual_combineFrameCands hA hB)

/-! ### Kernel-checked worked instance on `[[4, 2, 2]]` -/

/-- The `[[4, 2, 2]]` CSS code on qubits `[0, 1, 2, 3]` with full-weight `X`
    and `Z` checks. -/
private def code422 : CodeState :=
  { Q := [0, 1, 2, 3]
    rows := [{ id := 0, sector := Sector.X, support := [0, 1, 2, 3] },
             { id := 1, sector := Sector.Z, support := [0, 1, 2, 3] }]
    used := [0, 1] }

/-- A complete 2-pair logical frame for `[[4, 2, 2]]`:
    `(X₀X₁, Z₀Z₂)` and `(X₀X₂, Z₀Z₁)`. -/
def frame422 : List FramePair :=
  [{ xVec := [true, true, false, false], zVec := [true, false, true, false],
     xSign := false, zSign := false },
   { xVec := [true, false, true, false], zVec := [true, true, false, false],
     xSign := false, zSign := false }]

theorem frame422_wellFormed : LogicalFrame.WellFormed code422 frame422 := by
  decide

theorem frame422_toLogField_onePerClass :
    LogField.OnePerClass code422 (LogicalFrame.toLogField frame422) :=
  frame_toLogField_onePerClass frame422_wellFormed

theorem constructionRecord_422_skip_valid :
    ConstructionRecord.Valid code422 (ConstructionRecord.ofExpr (StateExpr.base code422)) :=
  constructionRecord_ofExpr_valid (EvalExpr.base code422)

end CodeCalculus
