import CodeCalculus.Eval
import CodeCalculus.WellFormedness
import CodeCalculus.GraftWellFormedness

namespace CodeCalculus

/-!
# Annotated-judgment soundness (the models predicate)

Mechanized form of the hand derivation at `spec/OPERATIONAL_SEMANTICS.md` §4.11
(`OBL-JUDGMENT-SOUNDNESS`): *every derivable annotation is true of the
evaluation it denotes*.

`judgment_soundness` proves the `⊨` half for a supplied well-formed evaluation
chain: it takes `Chain cs` and `WellFormedContext cs` as hypotheses and returns
`Models dMeasure cs a`, whose `evalChain` field is that hypothesis unchanged.
The `Eval` conjunct of the spec's statement is assumed here, not proved; the
chain hypothesis cannot be dropped (`le_refl` and the pure order rows are
derivable over any list of states).

The pieces, in dependency order:

- `Field` — the carry-table cell families of §4.11's satisfaction clause
  (`n`, `k`, `d`, `dX`, `dZ`).
- `Ann` — the sentence language: atoms (`Atom`, a field value at one chain
  position), numeric/opaque/derived terms (`AExpr`, with `sub` for the graft's
  `n - 1` and `minOf` for `MIN-ORDER`), and `≲` ranging over `{≤, =}`.
- `AnnTrue` — satisfaction, read by claim shape: for each cell property `P`, an
  evaluation satisfies `P` iff `P` holds of the denoted evaluation.
- `Chain` — the chain of states a closed command unfolds through; this is the
  "same closed term" that `TRANSITIVITY` is derivation-wide over.
- `Derives` — `Γ ⊢ … : R`, the L3 rule inventory of
  `the archived notes` §3.4 and §3.4.1:
  instantiation, `TRANSITIVITY`, `MIN-ORDER`, and the ambient order theory.
- `Models`, `judgment_soundness` — the models predicate, and the metatheorem.

Scope, mirrored at `spec/OBLIGATIONS.md` (`OBL-JUDGMENT-SOUNDNESS`, intended
mechanization status): the instantiation cell set carries skip's identity on
**every** field of §4.11's list (input and output state coincide, so any
reading works), the `n` cells of deletion, addition, and the graft (`n' = n - 1`,
the §4.12 dimension count, under the FD1 well-formedness context), the `k`
cells of deletion, addition, and the graft (deletion `k' = k + 1`, addition
`k' = k - 1`, graft `k' = k`), the distance monotonicity and bounds cells of
deletion and addition (`d_X`, `d_Z`, and `d` non-increasing under deletion and
non-decreasing under addition), and the output well-formedness cells of skip,
deletion, addition, and the graft (the sentence `Ann.wf`). The `k` cells of
deletion and addition are discharged by the rank-decrease lemmas of
`WellFormedness.lean` (`stateK_delete_of_eval`, `stateK_add_of_eval`) from the
transition's own independence premise, under `RanksFit`, the dimension bound
`rank X + rank Z ≤ |Q|`, which `ranksFit_of_wf` (`RanksFit.lean`, )
derives from the context's well-formedness. The graft's `k` cell is the
transition's own premise. The well-formedness cells of skip, deletion, and
addition are discharged by `wf_of_eval`; the graft's is discharged by
`wf_graft_of_eval` (`GraftWellFormedness.lean`, §4.12). The distance rows carry
no premise of their own (): the metatheorem takes, once, the
hypothesis `MeasureMonotone dMeasure`, the §4.3 and §4.5 monotonicity laws
stated over the uninterpreted measure (deletion does not raise a sector
distance, addition does not lower one), and discharges the six rows from it.
The measure stays uninterpreted and no rule computes a distance (D2);
`SpanMonotone` states the same laws as a property of the measure alone, over
the row-space inclusions of §4.3 and §4.5, and
`measureMonotone_of_spanMonotone` derives the hypothesis from it through the
inclusions `sectorRows_deleteState_sublist` and `sectorRows_addState_sublist`,
which are proved here. Discharging the hypothesis for a concrete distance
measure is `ExactDistance.lean` (): `exactMeasure`, the exact sector
distance over `F₂` vectors with `|Q| + 1` standing for `+∞`, is span-monotone
(`spanMonotone_exactMeasure`), and `judgment_soundness_exact` instantiates the
metatheorem with no measure hypothesis left.
`OBL-JUDGMENT-TRANSPORT` is mechanized in `Transport.lean` (). The
distance fields `dX` and `dZ` are read through the supplied `dMeasure`, and `d`
is defined as their minimum, so no cell derived here constrains the measure
beyond skip's identity and the stated hypothesis; the metatheorem holds for
every measure satisfying it, and `measureMonotone_const` and
`measureMonotone_rowCount` show the hypothesis is not vacuous.

`WellFormedContext` assumes every state of the chain well-formed. On any
chain, `judgment_soundness_of_head` derives that context from the
well-formedness of the input state alone, through `wf_of_eval_all`, so the
chain hypothesis reduces to FD1's hypothesis on the input.

Encoding notes (the last three recorded for , review findings RG-10
and RC-21). First, an atom whose chain position is beyond the chain
denotes `none`; `MIN-ORDER`'s first two rules and the reflexivity rows carry an
explicit denotation side condition, so the metatheorem is honest about that
artifact of the list encoding. The alternative — a strict `min` — would make
`AnnTrue` imply that every atom denotes, which is closer to the spec's reading
of atoms at evaluation sites, but it would also add premises to those two rules;
the absorbing encoding keeps the rules as §3.4.1 states them. A consequence,
recorded rather than repaired: a sentence true over a chain can become false
over an extension of it when a `min` argument that did not denote begins to
(`an archived note`, `rg_optMin_breaks_chain_monotonicity`); the transport
lemmas of `Transport.lean` are stated on `denotes`, not on values, for that
reason. Second, `sub` is strict in `none` and is used by the graft's `n - 1`
schema and by the truncated readings of the two `k` cells; `add` is its exact
counterpart. The `k` cells of deletion and addition are each stated twice: in
the exact form the spec writes (`k_{i+1} = k_i + 1` and `k_i = k_{i+1} + 1`,
rows `instDeleteK` and `instAddK`) and in the truncated `Nat` reading
(`k_i = k_{i+1} ∸ 1` and `k_{i+1} = k_i ∸ 1`, rows `instDeleteKSub` and
`instAddKSub`), which the exact form implies. Before 2026-10-29 only the
truncated forms were rows; they are weaker than the spec's cell (`0 = 0 ∸ 1`
holds), though derivable only where the exact form is proved. Both forms are
kept because `TRANSITIVITY` composes two-step `k` chains only through a shared
middle term: delete-then-add composes through `k_1 ∸ 1` and add-then-delete
through `k_1 + 1` (`FixtureEvalReplay.lean`, `fixture_W7_k_restored` and
`addThenDelete_k_restored`); the inventory has no arithmetic or congruence
rule, so a two-graft `n` chain (`n_2 = n_0 ∸ 2`) is not derivable, a limit of
§4.11's L3 inventory rather than of this slice. Third, the measure is
`Nat`-valued, so `+∞` at `k = 0` is not expressible in the sentence language;
the interval slice (`PricedInterval.lean`) reads distances in `Option Nat` and
handles `k = 0` through its `hk0` hypothesis, guarded by well-formedness, and
lifting `dMeasure` to `Option Nat` here is recorded as a limit, not done. One
further exclusion is deliberate:
congruence of `≡` on states reads a state and stays out of the derivation
system (2026-10-09 decision,  review round 5).

Gate 6 CSS-level soundness () is not a `judgment_soundness` row.
The five Gate 6 moves that have Lean transitions (`P-REBASE`, `E-PEEL`,
`E-PUNCTURE`, `E-EXTEND`, `E-LOCAL-HADAMARD`) get only the widened
`[0, +∞]` reset in `propagateCmd` (PricedInterval.lean), whose soundness
`priced_interval_soundness` proves; their well-formedness preservation is a
premise of their transitions, not a proof (`wf_of_eval` returns `hwf'`).
`E-GLUE` has no `Eval` transition in Lean at all (no `glue` constructor;
`EvalExpr` has only `base` and `directSum`), so neither theorem covers it.
The hand derivation is `spec/OPERATIONAL_SEMANTICS.md` §4.32
(`OBL-GATE6-CSS-EXTENSIONS`, `proved`); `hadamardState_stateK`,
`stateK_swap`, and `peelEval_Q_length` are facts about the transitions, not a
soundness discharge. This file (Ann-level soundness) does not duplicate them.
-/

/-- One field per carry-table cell family (§4.11). Output well-formedness is
    the separate sentence `Ann.wf`. -/
inductive Field : Type where
  | n
  | k
  | d
  | dX
  | dZ
  deriving Repr, DecidableEq

/-- An atom: a field value at one position of the evaluation chain. -/
structure Atom where
  pos : Nat
  field : Field
  deriving Repr, DecidableEq

/-- The term language of a sentence: constants, atoms, and the derived terms —
    truncated subtraction (the graft's `n - 1` generation schema) and `min`
    (`MIN-ORDER`'s subject). -/
inductive AExpr : Type where
  | const : Nat → AExpr
  | atom : Atom → AExpr
  | sub : AExpr → AExpr → AExpr
  | add : AExpr → AExpr → AExpr
  | minOf : AExpr → AExpr → AExpr
  deriving Repr, DecidableEq

/-- A sentence: `≲` ranges over `{≤, =}`. `≥` is notation for a turned `≤`,
    not a rule; the equality orientation clause is `Derives.eq_sym`. `wf i`
    is §4.11's output well-formedness cell: the state at chain position `i`
    satisfies I1–I5 (`EncodingWellFormed`); at the evaluation site `(i, i + 1)`
    the cell is `wf (i + 1)`. -/
inductive Ann : Type where
  | le : AExpr → AExpr → Ann
  | eq : AExpr → AExpr → Ann
  | wf : Nat → Ann
  deriving Repr, DecidableEq

/-- The metric of a field. `n` and `k` read the state structurally; `dX` and
    `dZ` read through the supplied exact-distance measure, which is a parameter
    of this whole development; `d` is *defined* as `min (dX, dZ)`, the §4.11
    `TRANSITIVITY` reading (`d(C)` unfolds to `min(d_X(C), d_Z(C))`), so the
    three distance fields are not independent. §4.11's instantiation base
    assigns the distance atoms only through card cells, and this slice derives
    none of them outside skip's identity. -/
def fieldValue (dMeasure : Field → CodeState → Nat) : Field → CodeState → Nat
  | .n, s => s.Q.length
  | .k, s => stateK s
  | .d, s => min (dMeasure .dX s) (dMeasure .dZ s)
  | f, s => dMeasure f s

/-- The definitional unfolding §4.11's `TRANSITIVITY` argument relies on. -/
theorem fieldValue_d (dMeasure : Field → CodeState → Nat) (s : CodeState) :
    fieldValue dMeasure .d s = min (fieldValue dMeasure .dX s) (fieldValue dMeasure .dZ s) :=
  rfl

/-- Minimum on optional values, with `none` (+∞) absorbed: this is the value of
    `min(t₁, t₂)` when one argument does not denote in this chain. -/
def optMin : Option Nat → Option Nat → Option Nat
  | none, none => none
  | none, some b => some b
  | some a, none => some a
  | some a, some b => some (min a b)

/-- The value of an atom at a chain: its position's state read through the
    field's metric. -/
def atomValue (dMeasure : Field → CodeState → Nat) (cs : List CodeState)
    (a : Atom) : Option Nat :=
  (cs[a.pos]?).map (fieldValue dMeasure a.field)

/-- The value of a term at a chain. `sub` and `add` are strict in `none`
    (`sub` is used by the graft's `n - 1` schema and by the truncated readings
    of the `k` cells, `add` by their exact readings; in every use both sides
    denote); `minOf` absorbs `none` per `optMin`. -/
def aexprValue (dMeasure : Field → CodeState → Nat) (cs : List CodeState) :
    AExpr → Option Nat
  | .const v => some v
  | .atom a => atomValue dMeasure cs a
  | .sub e1 e2 =>
      match aexprValue dMeasure cs e1, aexprValue dMeasure cs e2 with
      | some a, some b => some (a - b)
      | _, _ => none
  | .add e1 e2 =>
      match aexprValue dMeasure cs e1, aexprValue dMeasure cs e2 with
      | some a, some b => some (a + b)
      | _, _ => none
  | .minOf e1 e2 => optMin (aexprValue dMeasure cs e1) (aexprValue dMeasure cs e2)

/-- A term denotes in the chain when its value is defined. This is the side
    condition of the premise-free rules of the ambient order theory and of
    `MIN-ORDER`'s first two rules. -/
def denotes (dMeasure : Field → CodeState → Nat) (cs : List CodeState)
    (x : AExpr) : Prop :=
  ∃ v, aexprValue dMeasure cs x = some v

/-- A defined term's value is unique — term values are functions of the
    chain. -/
theorem aexprValue_determinism {dMeasure : Field → CodeState → Nat}
    {cs : List CodeState} {x : AExpr} {v w : Nat}
    (h1 : aexprValue dMeasure cs x = some v) (h2 : aexprValue dMeasure cs x = some w) :
    v = w :=
  Option.some.inj (h1.symm.trans h2)

/-- Satisfaction of a sentence at a chain: both sides denote and compare as
    stated. This is §4.11's `⊨`, read by claim shape; `Chain` supplies the
    denoted evaluation. -/
def AnnTrue (dMeasure : Field → CodeState → Nat) (cs : List CodeState) :
    Ann → Prop
  | .le x y =>
      ∃ v w, aexprValue dMeasure cs x = some v ∧ aexprValue dMeasure cs y = some w ∧ v ≤ w
  | .eq x y => ∃ v, aexprValue dMeasure cs x = some v ∧ aexprValue dMeasure cs y = some v
  | .wf i => ∃ s, cs[i]? = some s ∧ EncodingWellFormed s

/-- A defined term's witness. -/
theorem exists_aexprValue {dMeasure : Field → CodeState → Nat} {cs : List CodeState}
    {x : AExpr} (h : denotes dMeasure cs x) :
    ∃ v, aexprValue dMeasure cs x = some v := h

/-- The chain of states a closed command unfolds through, in evaluation order:
    the head is the input, and each consecutive pair is one evaluation of some
    command. -/
inductive Chain : List CodeState → Prop where
  | single (s : CodeState) : Chain [s]
  | cons {m : Command} {s t : CodeState} {cs : List CodeState}
      (hstep : Eval m s t) (hrest : Chain (t :: cs)) : Chain (s :: t :: cs)

/-- A chain position names a member of the chain. -/
theorem mem_of_getElem? {cs : List CodeState} {i : Nat} {s : CodeState}
    (h : cs[i]? = some s) : s ∈ cs := by
  induction cs generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero =>
      have hx : x = s := by
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        exact h
      exact List.mem_cons.mpr (Or.inl hx.symm)
    | succ i =>
      have h' : xs[i]? = some s := by
        simpa only [List.getElem?_cons_succ] using h
      exact List.mem_cons_of_mem x (ih h')

/-- The FD1 context of §4.11: the derivation context contains only
    well-formedness assumptions, which hold of the states by hypothesis. This
    is `EncodingWellFormed` of `State.lean`, the spec's hypothesis; the graft's
    `n` generation cell reads its qubit-namespace nonduplication conjunct. -/
abbrev WellFormedContext (cs : List CodeState) : Prop :=
  ∀ s, s ∈ cs → EncodingWellFormed s

/-- The filter of a list drops no entry when every entry differs from the
    filtered-out value. -/
theorem length_filter_neq_of_all_ne (q : Nat) : ∀ xs : List Nat,
    (∀ y, y ∈ xs → y ≠ q) → (xs.filter (fun y => y ≠ q)).length = xs.length := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro hall
    have hx : x ≠ q := hall x List.mem_cons_self
    have hpx : decide (x ≠ q) = true := by simp [hx]
    have hrest := ih (fun y hy => hall y (List.mem_cons_of_mem x hy))
    show (List.filter (fun y => decide (y ≠ q)) (x :: xs)).length = (x :: xs).length
    rw [List.filter_cons_of_pos (p := fun y => decide (y ≠ q)) hpx]
    simp only [List.length_cons]
    exact congrArg (fun n => n + 1) hrest

/-- The filter of a qubit-namespace list at a member drops exactly one entry
    when the list has no duplicates. -/
theorem length_filter_neq (q : Nat) : ∀ xs : List Nat, xs.Nodup → q ∈ xs →
    (xs.filter (fun y => y ≠ q)).length + 1 = xs.length := by
  intro xs
  induction xs with
  | nil => intro _ hmem; exact absurd hmem List.not_mem_nil
  | cons x xs ih =>
    intro hnod hmem
    rcases List.mem_cons.mp hmem with hqx | hmem'
    · -- the head is the member: the filter drops it and keeps the rest
      subst hqx
      have hnotin : q ∉ xs := (List.nodup_cons.mp hnod).1
      have hall : ∀ y, y ∈ xs → y ≠ q := by
        intro y hy hyq
        rw [hyq] at hy
        exact hnotin hy
      have hrest := length_filter_neq_of_all_ne q xs hall
      show (List.filter (fun y => decide (y ≠ q)) (q :: xs)).length + 1 =
          (q :: xs).length
      rw [List.filter_cons_of_neg (p := fun y => decide (y ≠ q))
        (show ¬(decide (q ≠ q) = true) from by simp)]
      simp only [List.length_cons]
      exact congrArg (fun n => n + 1) hrest
    · -- the head is not the member: the filter keeps it
      have hnotin : x ∉ xs := (List.nodup_cons.mp hnod).1
      have hne : x ≠ q := by
        intro hcon
        rw [← hcon] at hmem'
        exact hnotin hmem'
      have hrest := ih (List.nodup_cons.mp hnod).2 hmem'
      show (List.filter (fun y => decide (y ≠ q)) (x :: xs)).length + 1 =
          (x :: xs).length
      rw [List.filter_cons_of_pos (p := fun y => decide (y ≠ q))
        (decide_eq_true hne)]
      simp only [List.length_cons]
      exact congrArg (fun n => n + 1) hrest

/-- The graft's qubit namespace is the input namespace at the grafted qubit. -/
theorem graftState_Q (s : CodeState) (q : Nat) (sector : Sector) (ids : List Nat) :
    (graftState s q sector ids).Q = s.Q.filter (fun x => x ≠ q) := rfl

/-- A skip evaluation leaves the state unchanged. -/
theorem eval_skip_eq {s t : CodeState} (h : Eval Command.skip s t) : t = s := by
  cases h with
  | skip s' => rfl

/-- A deletion evaluation produces the deletion update. -/
theorem eval_delete_eq {r : Nat} {s t : CodeState}
    (h : Eval (Command.delete r) s t) : t = deleteState s r := by
  cases h with
  | delete _ _ hst => exact hst

/-- An addition evaluation produces the add update. -/
theorem eval_add_eq {sector : Sector} {support : List Nat} {s t : CodeState}
    (h : Eval (Command.addStab sector support) s t) : t = addState s sector support := by
  cases h with
  | add _ _ _ _ _ hst => exact hst

/-- The grafted qubit of a graft evaluation is displayed in the input. -/
theorem eval_graft_mem {q : Nat} {sector : Sector} {ids : List Nat} {s t : CodeState}
    (h : Eval (Command.graft q sector ids) s t) : q ∈ s.Q := by
  cases h with
  | graft hqin _ _ _ _ _ _ _ _ => exact hqin

/-- A graft evaluation produces the graft update. -/
theorem eval_graft_eq {q : Nat} {sector : Sector} {ids : List Nat} {s t : CodeState}
    (h : Eval (Command.graft q sector ids) s t) : t = graftState s q sector ids := by
  cases h with
  | graft _ _ _ _ _ _ _ _ hst => exact hst

/-! ## The measure-monotonicity hypothesis ()

The distance fields are read through an uninterpreted measure, so the
soundness of the §4.3 and §4.5 cells (deletion does not raise a sector
distance, addition does not lower one) cannot be proved here; it is the one
hypothesis the metatheorem takes about the measure. `MeasureMonotone` states
it once, over the two kernel transitions; `SpanMonotone` states the same laws
as a property of the measure alone, over the row-space inclusions the two
transitions produce, and `measureMonotone_of_spanMonotone` connects the two
through the inclusions proved below. No distance is computed and no measure is
interpreted (D2); the hypothesis is discharged for the exact sector distance in
`ExactDistance.lean` (). -/

/-- The F₂-span of `rows₁` over `Q` lies inside the span of `rows₂`. -/
def SpanLE (Q : List Nat) (rows₁ rows₂ : List Row) : Prop :=
  ∀ v, inSpanRows Q rows₁ v → inSpanRows Q rows₂ v

theorem spanLE_of_sublist (Q : List Nat) {rows₁ rows₂ : List Row}
    (h : rows₁.Sublist rows₂) : SpanLE Q rows₁ rows₂ :=
  fun v hv => inSpanRows_of_sublist Q h v hv

/-- Deletion shrinks each sector's display (§4.5's inclusion `X' ⊆ X`, and
    the untouched sector unchanged), as a sublist. -/
theorem sectorRows_deleteState_sublist (s : CodeState) (r : Nat) (σ : Sector) :
    (sectorRows (deleteState s r) σ).Sublist (sectorRows s σ) := by
  unfold sectorRows deleteState
  exact List.Sublist.filter _ List.filter_sublist

/-- Addition grows each sector's display (§4.3's inclusion `X ⊆ X'`, and the
    untouched sector unchanged), as a sublist. -/
theorem sectorRows_addState_sublist (s : CodeState) (sector : Sector)
    (support : List Nat) (σ : Sector) :
    (sectorRows s σ).Sublist (sectorRows (addState s sector support) σ) := by
  unfold sectorRows addState
  simp only [List.filter_append]
  exact List.sublist_append_left _ _

/-- The §4.3 and §4.5 laws over the uninterpreted measure, stated once: a
    deletion does not raise either sector distance and an addition does not
    lower either. The full distance `d = min(dX, dZ)` follows. -/
structure MeasureMonotone (dMeasure : Field → CodeState → Nat) : Prop where
  delete_le : ∀ (r : Nat) (s t : CodeState), Eval (Command.delete r) s t →
    dMeasure Field.dX t ≤ dMeasure Field.dX s ∧ dMeasure Field.dZ t ≤ dMeasure Field.dZ s
  add_le : ∀ (sector : Sector) (support : List Nat) (s t : CodeState),
    Eval (Command.addStab sector support) s t →
    dMeasure Field.dX s ≤ dMeasure Field.dX t ∧ dMeasure Field.dZ s ≤ dMeasure Field.dZ t

/-- The same laws as a property of the measure alone: on a fixed namespace,
    shrinking both sector spans does not raise either sector distance. This is
    what §4.3 and §4.5 prove for the exact distance from set inclusion. -/
def SpanMonotone (dMeasure : Field → CodeState → Nat) : Prop :=
  ∀ s t : CodeState, t.Q = s.Q →
    SpanLE s.Q (sectorRows t Sector.X) (sectorRows s Sector.X) →
    SpanLE s.Q (sectorRows t Sector.Z) (sectorRows s Sector.Z) →
    dMeasure Field.dX t ≤ dMeasure Field.dX s ∧ dMeasure Field.dZ t ≤ dMeasure Field.dZ s

/-- A span-monotone measure satisfies the hypothesis: deletion and addition
    produce the inclusions. -/
theorem measureMonotone_of_spanMonotone {dMeasure : Field → CodeState → Nat}
    (h : SpanMonotone dMeasure) : MeasureMonotone dMeasure where
  delete_le := fun r s t hstep => by
    have ht := eval_delete_eq hstep
    subst ht
    exact h s (deleteState s r) rfl
      (spanLE_of_sublist _ (sectorRows_deleteState_sublist s r Sector.X))
      (spanLE_of_sublist _ (sectorRows_deleteState_sublist s r Sector.Z))
  add_le := fun sector support s t hstep => by
    have ht := eval_add_eq hstep
    subst ht
    exact h (addState s sector support) s rfl
      (spanLE_of_sublist _ (sectorRows_addState_sublist s sector support Sector.X))
      (spanLE_of_sublist _ (sectorRows_addState_sublist s sector support Sector.Z))

/-- The hypothesis is not vacuous: every constant measure satisfies it. -/
theorem measureMonotone_const (c : Nat) : MeasureMonotone (fun _ _ => c) where
  delete_le := fun _ _ _ _ => ⟨Nat.le_refl c, Nat.le_refl c⟩
  add_le := fun _ _ _ _ _ => ⟨Nat.le_refl c, Nat.le_refl c⟩

/-- The display size is a monotone measure: deletion drops a row, addition
    appends one. It is not a distance; it shows the hypothesis has models that
    separate the two directions. -/
theorem measureMonotone_rowCount : MeasureMonotone (fun _ s => s.rows.length) where
  delete_le := fun r s t hstep => by
    rw [eval_delete_eq hstep]
    exact ⟨List.length_filter_le _ _, List.length_filter_le _ _⟩
  add_le := fun sector support s t hstep => by
    rw [eval_add_eq hstep]
    simp only [addState, List.length_append, List.length_singleton]
    exact ⟨Nat.le_succ _, Nat.le_succ _⟩

/-- Derivability of an annotation in the derivation of the chain as one closed
    term: the L3 rule inventory of
    `the archived notes` §3.4/§3.4.1.

The `inst*` rows are §3.4's instantiation — "at every evaluation of an
operation, each claim schema that the operation's card records as `included`
holds at that evaluation's own input/output pair" — one premise per card cell
mechanized: skip on every field; `n` for delete/add/graft; `k` for
delete/add/graft (deletion `k' = k + 1`, addition `k' = k - 1`, graft
`k' = k`); the distance monotonicity and bounds cells of deletion and addition
(`d_X`, `d_Z`, and `d`); and output well-formedness for skip/delete/add/graft.
The `k` rows of deletion and addition are discharged from the transition's
premises by the rank-decrease lemmas under the dimension bound
`rank X + rank Z ≤ |Q|`, which `ranksFit_of_wf` supplies from the context's
well-formedness; the graft's well-formedness row is discharged by
`wf_graft_of_eval`. The distance rows carry no
premise: they are L3's instantiation of the §4.3 and §4.5 cells, and their
truth is established by `judgment_soundness` from its `MeasureMonotone`
hypothesis, stated once for the whole derivation rather than at each row
().

The four `transit*` rows are `TRANSITIVITY` with `≲` over `{≤, =}` and the
mixed chains stated; `eq_sym` is the equality orientation clause. The `min*`
rows are `MIN-ORDER`'s three rules; `le_refl`/`eq_refl` are the ambient order
theory. The two `min*` premise-free rows and both reflexivity rows carry the
denotation side condition (see module note); the third `min` rule needs none,
since its premises already establish the denotations. -/
inductive Derives (dMeasure : Field → CodeState → Nat) (cs : List CodeState) : Ann → Prop where
  | instSkip (i : Nat) (f : Field) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval Command.skip s t) :
      Derives dMeasure cs (Ann.eq (AExpr.atom ⟨i + 1, f⟩) (AExpr.atom ⟨i, f⟩))
  | instDeleteN (i r : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.delete r) s t) :
      Derives dMeasure cs (Ann.eq (AExpr.atom ⟨i + 1, Field.n⟩) (AExpr.atom ⟨i, Field.n⟩))
  | instAddN (i : Nat) (sector : Sector) (support : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.addStab sector support) s t) :
      Derives dMeasure cs (Ann.eq (AExpr.atom ⟨i + 1, Field.n⟩) (AExpr.atom ⟨i, Field.n⟩))
  | instGraftN (i q : Nat) (sector : Sector) (ids : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.graft q sector ids) s t) :
      Derives dMeasure cs (Ann.eq (AExpr.atom ⟨i + 1, Field.n⟩)
        (AExpr.sub (AExpr.atom ⟨i, Field.n⟩) (AExpr.const 1)))
  -- k cells (per-primitive rank bookkeeping, discharged by the rank-decrease
  -- lemmas of `WellFormedness.lean` under the dimension bound `RanksFit`,
  -- which `ranksFit_of_wf` derives from the context's well-formedness). Each
  -- cell has an exact additive row (`k' = k + 1`, `k = k' + 1`, the spec's
  -- form) and a truncated row (`k = k' ∸ 1`, `k' = k ∸ 1`), the latter a
  -- consequence of the former in `Nat`; both are kept because two-step `k`
  -- compositions by `TRANSITIVITY` need a shared middle term (;
  -- module note).
  | instDeleteK (i r : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.delete r) s t) :
      Derives dMeasure cs (Ann.eq (AExpr.atom ⟨i + 1, Field.k⟩)
        (AExpr.add (AExpr.atom ⟨i, Field.k⟩) (AExpr.const 1)))
  | instDeleteKSub (i r : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.delete r) s t) :
      Derives dMeasure cs (Ann.eq (AExpr.atom ⟨i, Field.k⟩)
        (AExpr.sub (AExpr.atom ⟨i + 1, Field.k⟩) (AExpr.const 1)))
  | instAddK (i : Nat) (sector : Sector) (support : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.addStab sector support) s t) :
      Derives dMeasure cs (Ann.eq (AExpr.atom ⟨i, Field.k⟩)
        (AExpr.add (AExpr.atom ⟨i + 1, Field.k⟩) (AExpr.const 1)))
  | instAddKSub (i : Nat) (sector : Sector) (support : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.addStab sector support) s t) :
      Derives dMeasure cs (Ann.eq (AExpr.atom ⟨i + 1, Field.k⟩)
        (AExpr.sub (AExpr.atom ⟨i, Field.k⟩) (AExpr.const 1)))
  | instGraftK (i q : Nat) (sector : Sector) (ids : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.graft q sector ids) s t) :
      Derives dMeasure cs (Ann.eq (AExpr.atom ⟨i + 1, Field.k⟩)
        (AExpr.atom ⟨i, Field.k⟩))
  -- output well-formedness cells: §4.7's instances for skip, deletion, and
  -- addition through `wf_of_eval`; the graft's through `wf_graft_of_eval`.
  | instSkipWF (i : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval Command.skip s t) :
      Derives dMeasure cs (Ann.wf (i + 1))
  | instDeleteWF (i r : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.delete r) s t) :
      Derives dMeasure cs (Ann.wf (i + 1))
  | instAddWF (i : Nat) (sector : Sector) (support : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.addStab sector support) s t) :
      Derives dMeasure cs (Ann.wf (i + 1))
  | instGraftWF (i q : Nat) (sector : Sector) (ids : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.graft q sector ids) s t) :
      Derives dMeasure cs (Ann.wf (i + 1))
  -- distance bounds for deletion and addition (sector and full): the §4.3 and
  -- §4.5 cells, discharged by `judgment_soundness` from `MeasureMonotone`.
  | instDeleteDX (i r : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.delete r) s t) :
      Derives dMeasure cs (Ann.le (AExpr.atom ⟨i + 1, Field.dX⟩)
        (AExpr.atom ⟨i, Field.dX⟩))
  | instDeleteDZ (i r : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.delete r) s t) :
      Derives dMeasure cs (Ann.le (AExpr.atom ⟨i + 1, Field.dZ⟩)
        (AExpr.atom ⟨i, Field.dZ⟩))
  | instDeleteD (i r : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.delete r) s t) :
      Derives dMeasure cs (Ann.le (AExpr.atom ⟨i + 1, Field.d⟩)
        (AExpr.atom ⟨i, Field.d⟩))
  | instAddDX (i : Nat) (sector : Sector) (support : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.addStab sector support) s t) :
      Derives dMeasure cs (Ann.le (AExpr.atom ⟨i, Field.dX⟩)
        (AExpr.atom ⟨i + 1, Field.dX⟩))
  | instAddDZ (i : Nat) (sector : Sector) (support : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.addStab sector support) s t) :
      Derives dMeasure cs (Ann.le (AExpr.atom ⟨i, Field.dZ⟩)
        (AExpr.atom ⟨i + 1, Field.dZ⟩))
  | instAddD (i : Nat) (sector : Sector) (support : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.addStab sector support) s t) :
      Derives dMeasure cs (Ann.le (AExpr.atom ⟨i, Field.d⟩)
        (AExpr.atom ⟨i + 1, Field.d⟩))
  | transit_le_le (x y z : AExpr)
      (h1 : Derives dMeasure cs (Ann.le x y)) (h2 : Derives dMeasure cs (Ann.le y z)) :
      Derives dMeasure cs (Ann.le x z)
  | transit_le_eq (x y z : AExpr)
      (h1 : Derives dMeasure cs (Ann.le x y)) (h2 : Derives dMeasure cs (Ann.eq y z)) :
      Derives dMeasure cs (Ann.le x z)
  | transit_eq_le (x y z : AExpr)
      (h1 : Derives dMeasure cs (Ann.eq x y)) (h2 : Derives dMeasure cs (Ann.le y z)) :
      Derives dMeasure cs (Ann.le x z)
  | transit_eq_eq (x y z : AExpr)
      (h1 : Derives dMeasure cs (Ann.eq x y)) (h2 : Derives dMeasure cs (Ann.eq y z)) :
      Derives dMeasure cs (Ann.eq x z)
  | min_le_left (x y : AExpr) (hx : denotes dMeasure cs x) :
      Derives dMeasure cs (Ann.le (AExpr.minOf x y) x)
  | min_le_right (x y : AExpr) (hy : denotes dMeasure cs y) :
      Derives dMeasure cs (Ann.le (AExpr.minOf x y) y)
  | le_min (t x y : AExpr)
      (h1 : Derives dMeasure cs (Ann.le t x)) (h2 : Derives dMeasure cs (Ann.le t y)) :
      Derives dMeasure cs (Ann.le t (AExpr.minOf x y))
  | le_refl (x : AExpr) (hx : denotes dMeasure cs x) :
      Derives dMeasure cs (Ann.le x x)
  | eq_refl (x : AExpr) (hx : denotes dMeasure cs x) :
      Derives dMeasure cs (Ann.eq x x)
  | eq_sym (x y : AExpr) (h : Derives dMeasure cs (Ann.eq x y)) :
      Derives dMeasure cs (Ann.eq y x)

/-- Satisfaction `(S, m, S') ⊨ R` of §4.11, on the chain a closed command
    unfolds through: the chain evaluates and the annotation holds of it. A
    single-step evaluation `Eval m s s'` is the two-element chain `[s, s']`. -/
structure Models (dMeasure : Field → CodeState → Nat) (cs : List CodeState) (a : Ann) :
    Prop where
  evalChain : Chain cs
  truth : AnnTrue dMeasure cs a

theorem eval_graft_k {q : Nat} {sector : Sector} {ids : List Nat} {s s' : CodeState}
    (h : Eval (Command.graft q sector ids) s s') : stateK s' = stateK s := by
  cases h with
  | graft _ _ _ _ _ _ _ hk heq => rw [heq]; exact hk

/-- Soundness (§4.11): every derivable annotation is true of the evaluation it
    denotes. By induction on a derivation: the instantiation rows discharge
    against the per-primitive lemmas where those have landed (`eval_skip_eq`
    with input and output coinciding; `eval_delete_eq`, `eval_add_eq` keeping
    the qubit namespace; `eval_graft_eq` with the FD1 nonduplication via
    `length_filter_neq`; the `k` rows of deletion and addition through
    `stateK_delete_of_eval` and `stateK_add_of_eval` from the context's
    well-formedness, with the dimension bound from `ranksFit_of_wf`; the
    well-formedness rows of skip, deletion, and addition through `wf_of_eval`
    and the graft's through `wf_graft_of_eval`; the distance rows through the
    `MeasureMonotone` hypothesis), and
    the order-theoretic rows discharge against the term semantics, which is a
    function of the chain. Stated for every exact-distance measure satisfying
    `MeasureMonotone`, the §4.3 and §4.5 laws taken once as a hypothesis: the
    distance rows discharge against it, and no other derivable cell constrains
    the measure except skip's identity, where input and output state
    coincide. -/
theorem judgment_soundness (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) (cs : List CodeState)
    (hctxt : WellFormedContext cs) (hchain : Chain cs) : ∀ a, Derives dMeasure cs a →
    Models dMeasure cs a := by
  intro a h
  refine ⟨hchain, ?_⟩
  induction h with
  | instSkip i f s t hi hj hstep =>
      have hinv := eval_skip_eq hstep
      subst hinv
      show ∃ v, aexprValue dMeasure cs (AExpr.atom ⟨i + 1, f⟩) = some v ∧
          aexprValue dMeasure cs (AExpr.atom ⟨i, f⟩) = some v
      simp only [aexprValue, atomValue, hj, hi, Option.map_some]
      exact ⟨_, rfl, rfl⟩
  | instDeleteN i r s t hi hj hstep =>
      have hinv := eval_delete_eq hstep
      subst hinv
      show ∃ v, aexprValue dMeasure cs (AExpr.atom ⟨i + 1, Field.n⟩) = some v ∧
          aexprValue dMeasure cs (AExpr.atom ⟨i, Field.n⟩) = some v
      simp only [aexprValue, atomValue, hj, hi, Option.map_some, fieldValue, deleteState]
      exact ⟨_, rfl, rfl⟩
  | instAddN i sector support s t hi hj hstep =>
      have hinv := eval_add_eq hstep
      subst hinv
      show ∃ v, aexprValue dMeasure cs (AExpr.atom ⟨i + 1, Field.n⟩) = some v ∧
          aexprValue dMeasure cs (AExpr.atom ⟨i, Field.n⟩) = some v
      simp only [aexprValue, atomValue, hj, hi, Option.map_some, fieldValue, addState]
      exact ⟨_, rfl, rfl⟩
  | instGraftN i q sector ids s t hi hj hstep =>
      have hmem : s ∈ cs := mem_of_getElem? hi
      have hnodup := (hctxt s hmem).1
      have hqin := eval_graft_mem hstep
      have hlen := length_filter_neq q s.Q hnodup hqin
      have hinv := eval_graft_eq hstep
      subst hinv
      show ∃ v, aexprValue dMeasure cs (AExpr.atom ⟨i + 1, Field.n⟩) = some v ∧
          aexprValue dMeasure cs (AExpr.sub (AExpr.atom ⟨i, Field.n⟩) (AExpr.const 1)) =
            some v
      refine ⟨(s.Q.filter (fun x => x ≠ q)).length, ?_, ?_⟩
      · simp only [aexprValue, atomValue, hj, Option.map_some, fieldValue]
        rw [graftState_Q]
      · simp only [aexprValue, atomValue, hi, Option.map_some, fieldValue]
        exact congrArg Option.some (by omega)
  | instDeleteK i r s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hk : stateK t = stateK s + 1 :=
        stateK_delete_of_eval hstep hwfs (ranksFit_of_wf s hwfs)
      show ∃ v, aexprValue dMeasure cs (AExpr.atom ⟨i + 1, Field.k⟩) = some v ∧
          aexprValue dMeasure cs (AExpr.add (AExpr.atom ⟨i, Field.k⟩)
            (AExpr.const 1)) = some v
      refine ⟨stateK t, ?_, ?_⟩
      · simp only [aexprValue, atomValue, hj, Option.map_some, fieldValue]
      · simp only [aexprValue, atomValue, hi, Option.map_some, fieldValue]
        exact congrArg Option.some (by omega)
  | instDeleteKSub i r s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hk : stateK t = stateK s + 1 :=
        stateK_delete_of_eval hstep hwfs (ranksFit_of_wf s hwfs)
      show ∃ v, aexprValue dMeasure cs (AExpr.atom ⟨i, Field.k⟩) = some v ∧
          aexprValue dMeasure cs (AExpr.sub (AExpr.atom ⟨i + 1, Field.k⟩)
            (AExpr.const 1)) = some v
      refine ⟨stateK s, ?_, ?_⟩
      · simp only [aexprValue, atomValue, hi, Option.map_some, fieldValue]
      · simp only [aexprValue, atomValue, hj, Option.map_some, fieldValue]
        exact congrArg Option.some (by omega)
  | instAddK i sector support s t hi hj hstep =>
      have hk : stateK s = stateK t + 1 :=
        stateK_add_of_eval hstep (hctxt s (mem_of_getElem? hi))
          (ranksFit_of_wf t (hctxt t (mem_of_getElem? hj)))
      show ∃ v, aexprValue dMeasure cs (AExpr.atom ⟨i, Field.k⟩) = some v ∧
          aexprValue dMeasure cs (AExpr.add (AExpr.atom ⟨i + 1, Field.k⟩)
            (AExpr.const 1)) = some v
      refine ⟨stateK s, ?_, ?_⟩
      · simp only [aexprValue, atomValue, hi, Option.map_some, fieldValue]
      · simp only [aexprValue, atomValue, hj, Option.map_some, fieldValue]
        exact congrArg Option.some (by omega)
  | instAddKSub i sector support s t hi hj hstep =>
      have hk : stateK s = stateK t + 1 :=
        stateK_add_of_eval hstep (hctxt s (mem_of_getElem? hi))
          (ranksFit_of_wf t (hctxt t (mem_of_getElem? hj)))
      show ∃ v, aexprValue dMeasure cs (AExpr.atom ⟨i + 1, Field.k⟩) = some v ∧
          aexprValue dMeasure cs (AExpr.sub (AExpr.atom ⟨i, Field.k⟩)
            (AExpr.const 1)) = some v
      refine ⟨stateK t, ?_, ?_⟩
      · simp only [aexprValue, atomValue, hj, Option.map_some, fieldValue]
      · simp only [aexprValue, atomValue, hi, Option.map_some, fieldValue]
        exact congrArg Option.some (by omega)
  | instGraftK i q sector ids s t hi hj hstep =>
      have hk : stateK t = stateK s := eval_graft_k hstep
      show ∃ v, aexprValue dMeasure cs (AExpr.atom ⟨i + 1, Field.k⟩) = some v ∧
          aexprValue dMeasure cs (AExpr.atom ⟨i, Field.k⟩) = some v
      refine ⟨stateK s, ?_, ?_⟩
      · simp only [aexprValue, atomValue, hj, Option.map_some, fieldValue]
        rw [hk]
      · simp only [aexprValue, atomValue, hi, Option.map_some, fieldValue]
  | instSkipWF i s t hi hj hstep =>
      have hinv := eval_skip_eq hstep
      subst hinv
      show ∃ s', cs[i + 1]? = some s' ∧ EncodingWellFormed s'
      exact ⟨_, hj, hctxt _ (mem_of_getElem? hi)⟩
  | instDeleteWF i r s t hi hj hstep =>
      show ∃ s', cs[i + 1]? = some s' ∧ EncodingWellFormed s'
      exact ⟨t, hj, wf_of_eval (by trivial) hstep (hctxt s (mem_of_getElem? hi))⟩
  | instAddWF i sector support s t hi hj hstep =>
      show ∃ s', cs[i + 1]? = some s' ∧ EncodingWellFormed s'
      exact ⟨t, hj, wf_of_eval (by trivial) hstep (hctxt s (mem_of_getElem? hi))⟩
  | instGraftWF i q sector ids s t hi hj hstep =>
      show ∃ s', cs[i + 1]? = some s' ∧ EncodingWellFormed s'
      exact ⟨t, hj, wf_graft_of_eval hstep (hctxt s (mem_of_getElem? hi))⟩
  | instDeleteDX i r s t hi hj hstep =>
      show ∃ v w, aexprValue dMeasure cs (AExpr.atom ⟨i + 1, Field.dX⟩) = some v ∧
          aexprValue dMeasure cs (AExpr.atom ⟨i, Field.dX⟩) = some w ∧ v ≤ w
      refine ⟨dMeasure Field.dX t, dMeasure Field.dX s, ?_, ?_,
        (hmono.delete_le r s t hstep).1⟩
      · simp only [aexprValue, atomValue, hj, Option.map_some, fieldValue]
      · simp only [aexprValue, atomValue, hi, Option.map_some, fieldValue]
  | instDeleteDZ i r s t hi hj hstep =>
      show ∃ v w, aexprValue dMeasure cs (AExpr.atom ⟨i + 1, Field.dZ⟩) = some v ∧
          aexprValue dMeasure cs (AExpr.atom ⟨i, Field.dZ⟩) = some w ∧ v ≤ w
      refine ⟨dMeasure Field.dZ t, dMeasure Field.dZ s, ?_, ?_,
        (hmono.delete_le r s t hstep).2⟩
      · simp only [aexprValue, atomValue, hj, Option.map_some, fieldValue]
      · simp only [aexprValue, atomValue, hi, Option.map_some, fieldValue]
  | instDeleteD i r s t hi hj hstep =>
      show ∃ v w, aexprValue dMeasure cs (AExpr.atom ⟨i + 1, Field.d⟩) = some v ∧
          aexprValue dMeasure cs (AExpr.atom ⟨i, Field.d⟩) = some w ∧ v ≤ w
      have hd := hmono.delete_le r s t hstep
      refine ⟨min (dMeasure Field.dX t) (dMeasure Field.dZ t),
              min (dMeasure Field.dX s) (dMeasure Field.dZ s), ?_, ?_, by omega⟩
      · simp only [aexprValue, atomValue, hj, Option.map_some, fieldValue]
      · simp only [aexprValue, atomValue, hi, Option.map_some, fieldValue]
  | instAddDX i sector support s t hi hj hstep =>
      show ∃ v w, aexprValue dMeasure cs (AExpr.atom ⟨i, Field.dX⟩) = some v ∧
          aexprValue dMeasure cs (AExpr.atom ⟨i + 1, Field.dX⟩) = some w ∧ v ≤ w
      refine ⟨dMeasure Field.dX s, dMeasure Field.dX t, ?_, ?_,
        (hmono.add_le sector support s t hstep).1⟩
      · simp only [aexprValue, atomValue, hi, Option.map_some, fieldValue]
      · simp only [aexprValue, atomValue, hj, Option.map_some, fieldValue]
  | instAddDZ i sector support s t hi hj hstep =>
      show ∃ v w, aexprValue dMeasure cs (AExpr.atom ⟨i, Field.dZ⟩) = some v ∧
          aexprValue dMeasure cs (AExpr.atom ⟨i + 1, Field.dZ⟩) = some w ∧ v ≤ w
      refine ⟨dMeasure Field.dZ s, dMeasure Field.dZ t, ?_, ?_,
        (hmono.add_le sector support s t hstep).2⟩
      · simp only [aexprValue, atomValue, hi, Option.map_some, fieldValue]
      · simp only [aexprValue, atomValue, hj, Option.map_some, fieldValue]
  | instAddD i sector support s t hi hj hstep =>
      show ∃ v w, aexprValue dMeasure cs (AExpr.atom ⟨i, Field.d⟩) = some v ∧
          aexprValue dMeasure cs (AExpr.atom ⟨i + 1, Field.d⟩) = some w ∧ v ≤ w
      have hd := hmono.add_le sector support s t hstep
      refine ⟨min (dMeasure Field.dX s) (dMeasure Field.dZ s),
              min (dMeasure Field.dX t) (dMeasure Field.dZ t), ?_, ?_, by omega⟩
      · simp only [aexprValue, atomValue, hi, Option.map_some, fieldValue]
      · simp only [aexprValue, atomValue, hj, Option.map_some, fieldValue]
  | transit_le_le x y z h1 h2 ih1 ih2 =>
      obtain ⟨v, w, hxv, hyw, hvw⟩ := ih1
      obtain ⟨w2, u, hyw2, hzu, hw2u⟩ := ih2
      have hw : w = w2 := aexprValue_determinism hyw hyw2
      refine ⟨v, u, hxv, hzu, ?_⟩
      omega
  | transit_le_eq x y z h1 h2 ih1 ih2 =>
      obtain ⟨v, w, hxv, hyw, hvw⟩ := ih1
      obtain ⟨v2, hyv2, hzv2⟩ := ih2
      have hw : w = v2 := aexprValue_determinism hyw hyv2
      refine ⟨v, v2, hxv, hzv2, ?_⟩
      omega
  | transit_eq_le x y z h1 h2 ih1 ih2 =>
      obtain ⟨v, hxv, hyw⟩ := ih1
      obtain ⟨v2, w2, hyv2, hzv2, hv2w2⟩ := ih2
      have hv : v = v2 := aexprValue_determinism hyw hyv2
      refine ⟨v, w2, hxv, hzv2, ?_⟩
      omega
  | transit_eq_eq x y z h1 h2 ih1 ih2 =>
      obtain ⟨v, hxv, hyw⟩ := ih1
      obtain ⟨v2, hyv2, hzv2⟩ := ih2
      have hv : v = v2 := aexprValue_determinism hyw hyv2
      refine ⟨v, hxv, ?_⟩
      rw [hzv2, ← hv]
  | min_le_left x y hx =>
      obtain ⟨v, hxv⟩ := exists_aexprValue hx
      cases hyv : aexprValue dMeasure cs y with
      | none =>
        refine ⟨v, v, ?_, hxv, Nat.le_refl v⟩
        simp only [aexprValue, optMin, hxv, hyv]
      | some w =>
        refine ⟨min v w, v, ?_, hxv, Nat.min_le_left v w⟩
        simp only [aexprValue, optMin, hxv, hyv]
  | min_le_right x y hy =>
      obtain ⟨w, hyw⟩ := exists_aexprValue hy
      cases hxv : aexprValue dMeasure cs x with
      | none =>
        refine ⟨w, w, ?_, hyw, Nat.le_refl w⟩
        simp only [aexprValue, optMin, hxv, hyw]
      | some v =>
        refine ⟨min v w, w, ?_, hyw, ?_⟩
        · simp only [aexprValue, optMin, hxv, hyw]
        · omega
  | le_min t x y h1 h2 ih1 ih2 =>
      obtain ⟨vt, vx, htv, hxv, hle1⟩ := ih1
      obtain ⟨v2, vy, htv2, hyv, hle2⟩ := ih2
      have heq : vt = v2 := aexprValue_determinism htv htv2
      refine ⟨vt, min vx vy, htv, ?_, ?_⟩
      · simp only [aexprValue, optMin, hxv, hyv]
      · omega
  | le_refl x hx =>
      obtain ⟨v, hxv⟩ := exists_aexprValue hx
      simp only [AnnTrue]
      exact ⟨v, v, hxv, hxv, Nat.le_refl v⟩
  | eq_refl x hx =>
      obtain ⟨v, hxv⟩ := exists_aexprValue hx
      simp only [AnnTrue]
      exact ⟨v, hxv, hxv⟩
  | eq_sym x y h ih =>
      obtain ⟨v, hxv, hyv⟩ := ih
      simp only [AnnTrue]
      exact ⟨v, hyv, hxv⟩

/-! ## Deriving the context from the input state -/

/-- A chain whose every step is a graft-free command (`GraftFree`): the
    well-formedness of its states follows from that of its head through
    `wf_of_eval`. -/
inductive GraftFreeChain : List CodeState → Prop where
  | single (s : CodeState) : GraftFreeChain [s]
  | cons {m : Command} {s t : CodeState} {cs : List CodeState}
      (hm : GraftFree m) (hstep : Eval m s t) (hrest : GraftFreeChain (t :: cs)) :
      GraftFreeChain (s :: t :: cs)

theorem GraftFreeChain.toChain {cs : List CodeState} (h : GraftFreeChain cs) : Chain cs := by
  induction h with
  | single s => exact Chain.single s
  | cons _ hstep _ ih => exact Chain.cons hstep ih

/-- The FD1 context of §4.11 from the input state alone, on any chain,
    through `wf_of_eval_all`. -/
theorem Chain.wellFormedContext {cs : List CodeState} (h : Chain cs)
    (hhead : ∀ s, cs.head? = some s → EncodingWellFormed s) : WellFormedContext cs := by
  induction h with
  | single s =>
    intro x hx
    rw [List.mem_singleton] at hx
    rw [hx]
    exact hhead s rfl
  | @cons m s t cs' hstep _ ih =>
    have hs : EncodingWellFormed s := hhead s rfl
    have ht : EncodingWellFormed t := wf_of_eval_all hstep hs
    have ih' := ih (fun x hx => by
      rw [← Option.some.inj hx]
      exact ht)
    intro x hx
    rcases List.mem_cons.mp hx with hxs | hx'
    · rw [hxs]
      exact hs
    · exact ih' x hx'

/-- The graft-free special case, kept for the worked example. -/
theorem GraftFreeChain.wellFormedContext {cs : List CodeState} (h : GraftFreeChain cs)
    (hhead : ∀ s, cs.head? = some s → EncodingWellFormed s) : WellFormedContext cs :=
  h.toChain.wellFormedContext hhead

/-- Soundness from the input state's well-formedness alone, on any chain: the
    chain hypothesis of `judgment_soundness` is then FD1's hypothesis on the
    input, and every later state's well-formedness is derived rather than
    assumed. -/
theorem judgment_soundness_of_head (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) (cs : List CodeState)
    (hchain : Chain cs) (hhead : ∀ s, cs.head? = some s → EncodingWellFormed s) :
    ∀ a, Derives dMeasure cs a → Models dMeasure cs a :=
  judgment_soundness dMeasure hmono cs (hchain.wellFormedContext hhead) hchain

/-!
## A worked example: two instantiations compose across one evaluation site

The derivation the `TRANSITIVITY` rule was added for (§3.4.1's motivating
case, transposed to an invariant field). In the chain of the two-deletion
closed term, two instantiation cells at consecutive evaluation sites share the
middle atom and compose into one sentence about the outer pair; by
`judgment_soundness` the composed sentence is true of the chain.
-/

/-- Two independent X lines on the two qubits. -/
def twoDeleteState : CodeState :=
  { Q := [0, 1]
  , rows := [⟨1, Sector.X, [0]⟩, ⟨2, Sector.X, [1]⟩]
  , used := [1, 2] }

theorem displayed_1_twoDeleteState : DisplayedGenerator 1 twoDeleteState :=
  ⟨⟨1, Sector.X, [0]⟩, by simp [twoDeleteState], rfl⟩

theorem displayed_2_twoDeleteState : DisplayedGenerator 2 twoDeleteState :=
  ⟨⟨2, Sector.X, [1]⟩, by simp [twoDeleteState], rfl⟩

theorem displayed_2_of_deleteState :
    DisplayedGenerator 2 (deleteState twoDeleteState 1) :=
  ⟨⟨2, Sector.X, [1]⟩, by simp [twoDeleteState, deleteState], rfl⟩

theorem independent_1_twoDeleteState : IndependentGenerator 1 twoDeleteState := by
  show ¬ inSpanRows twoDeleteState.Q
    (twoDeleteState.rows.filter (fun r' => r'.sector = Sector.X ∧ r'.id ≠ 1))
    (rowVector twoDeleteState.Q ⟨1, Sector.X, [0]⟩)
  intro hspan
  rcases hspan with ⟨coeffs, hlen, hcomb⟩
  cases coeffs with
  | nil => simp [twoDeleteState] at hlen
  | cons c0 tl =>
    cases tl with
    | cons _ _ => simp [twoDeleteState] at hlen
    | nil =>
      cases c0 <;>
        simp [combineRows, xorVec, rowVector, twoDeleteState] at hcomb

theorem independent_2_twoDeleteState : IndependentGenerator 2 twoDeleteState := by
  show ¬ inSpanRows twoDeleteState.Q
    (twoDeleteState.rows.filter (fun r' => r'.sector = Sector.X ∧ r'.id ≠ 2))
    (rowVector twoDeleteState.Q ⟨2, Sector.X, [1]⟩)
  intro hspan
  rcases hspan with ⟨coeffs, hlen, hcomb⟩
  cases coeffs with
  | nil => simp [twoDeleteState] at hlen
  | cons c0 tl =>
    cases tl with
    | cons _ _ => simp [twoDeleteState] at hlen
    | nil =>
      cases c0 <;>
        simp [combineRows, xorVec, rowVector, twoDeleteState] at hcomb

theorem independent_2_of_deleteState :
    IndependentGenerator 2 (deleteState twoDeleteState 1) := by
  show ¬ inSpanRows (deleteState twoDeleteState 1).Q
    ((deleteState twoDeleteState 1).rows.filter
      (fun r' => r'.sector = Sector.X ∧ r'.id ≠ 2))
    (rowVector (deleteState twoDeleteState 1).Q ⟨2, Sector.X, [1]⟩)
  intro hspan
  rcases hspan with ⟨coeffs, _, hcomb⟩
  simp [combineRows, rowVector, twoDeleteState, deleteState] at hcomb

theorem encodingWellFormed_twoDeleteState : EncodingWellFormed twoDeleteState := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro rX rZ hX hZ hsecX hsecZ
    simp [twoDeleteState] at hX hZ
    rcases hX with rfl | rfl <;> rcases hZ with rfl | rfl <;>
      simp_all
  · intro r hr
    simp only [twoDeleteState, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact independent_1_twoDeleteState
    · exact independent_2_twoDeleteState

theorem encodingWellFormed_deleteState_1 :
    EncodingWellFormed (deleteState twoDeleteState 1) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro rX rZ hX hZ hsecX hsecZ
    simp [deleteState, twoDeleteState] at hX hZ
    rcases hX with rfl
    rcases hZ with rfl
    simp_all
  · intro r hr
    simp [deleteState, twoDeleteState] at hr
    rcases hr with rfl
    exact independent_2_of_deleteState

theorem encodingWellFormed_deleteState_2 :
    EncodingWellFormed (deleteState (deleteState twoDeleteState 1) 2) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro rX rZ hX hZ hsecX hsecZ
    simp [deleteState, twoDeleteState] at hX
  · intro r hr
    simp [deleteState, twoDeleteState] at hr

theorem eval_delete_1_twoDeleteState :
    Eval (Command.delete 1) twoDeleteState (deleteState twoDeleteState 1) :=
  Eval.delete displayed_1_twoDeleteState independent_1_twoDeleteState rfl

theorem eval_delete_2_of_deleteState :
    Eval (Command.delete 2) (deleteState twoDeleteState 1)
      (deleteState (deleteState twoDeleteState 1) 2) :=
  Eval.delete displayed_2_of_deleteState independent_2_of_deleteState rfl

theorem chain_twoDeletes :
    Chain [twoDeleteState, deleteState twoDeleteState 1,
      deleteState (deleteState twoDeleteState 1) 2] :=
  Chain.cons eval_delete_1_twoDeleteState
    (Chain.cons eval_delete_2_of_deleteState (Chain.single _))

/-- The composite derivation: two instantiation rows at consecutive
    evaluation sites, composed by `TRANSITIVITY` into a sentence about the
    outer pair. -/
theorem derives_two_step_n (dMeasure : Field → CodeState → Nat) :
    Derives dMeasure [twoDeleteState, deleteState twoDeleteState 1,
      deleteState (deleteState twoDeleteState 1) 2]
      (Ann.eq (AExpr.atom ⟨2, Field.n⟩) (AExpr.atom ⟨0, Field.n⟩)) :=
  Derives.transit_eq_eq _ _ _
    (Derives.instDeleteN 1 2 _ _ rfl rfl eval_delete_2_of_deleteState)
    (Derives.instDeleteN 0 1 _ _ rfl rfl eval_delete_1_twoDeleteState)

/-- The composed sentence is true of the two-deletion evaluation chain, for
    every monotone exact-distance measure. -/
theorem models_two_step_n (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) :
    Models dMeasure [twoDeleteState, deleteState twoDeleteState 1,
      deleteState (deleteState twoDeleteState 1) 2]
      (Ann.eq (AExpr.atom ⟨2, Field.n⟩) (AExpr.atom ⟨0, Field.n⟩)) := by
  have hctxt : WellFormedContext [twoDeleteState, deleteState twoDeleteState 1,
      deleteState (deleteState twoDeleteState 1) 2] := by
    intro s hs
    rcases List.mem_cons.mp hs with h0 | h1
    · cases h0
      exact encodingWellFormed_twoDeleteState
    rcases List.mem_cons.mp h1 with h2 | h3
    · cases h2
      exact encodingWellFormed_deleteState_1
    rcases List.mem_cons.mp h3 with h4 | hnil
    · cases h4
      exact encodingWellFormed_deleteState_2
    · cases hnil
  exact judgment_soundness dMeasure hmono _ hctxt chain_twoDeletes _
    (derives_two_step_n dMeasure)

/-- The same chain as a graft-free chain. -/
theorem graftFreeChain_twoDeletes :
    GraftFreeChain [twoDeleteState, deleteState twoDeleteState 1,
      deleteState (deleteState twoDeleteState 1) 2] :=
  GraftFreeChain.cons (by trivial) eval_delete_1_twoDeleteState
    (GraftFreeChain.cons (by trivial) eval_delete_2_of_deleteState (GraftFreeChain.single _))

/-- The two well-formedness cells at the two evaluation sites, and the
    composed `n` sentence, from the input state's well-formedness alone: the
    intermediate and final states' well-formedness is derived by
    `wf_of_eval`, not supplied. -/
theorem models_two_step_of_head (dMeasure : Field → CodeState → Nat)
    (hmono : MeasureMonotone dMeasure) :
    Models dMeasure [twoDeleteState, deleteState twoDeleteState 1,
      deleteState (deleteState twoDeleteState 1) 2]
      (Ann.eq (AExpr.atom ⟨2, Field.n⟩) (AExpr.atom ⟨0, Field.n⟩)) ∧
    Models dMeasure [twoDeleteState, deleteState twoDeleteState 1,
      deleteState (deleteState twoDeleteState 1) 2] (Ann.wf 2) := by
  have hhead : ∀ s, [twoDeleteState, deleteState twoDeleteState 1,
      deleteState (deleteState twoDeleteState 1) 2].head? = some s → EncodingWellFormed s := by
    intro s hs
    rw [← Option.some.inj hs]
    exact encodingWellFormed_twoDeleteState
  refine ⟨?_, ?_⟩
  · exact judgment_soundness_of_head dMeasure hmono _ graftFreeChain_twoDeletes.toChain hhead _
      (derives_two_step_n dMeasure)
  · exact judgment_soundness_of_head dMeasure hmono _ graftFreeChain_twoDeletes.toChain hhead _
      (Derives.instDeleteWF 1 2 _ _ rfl rfl eval_delete_2_of_deleteState)

end CodeCalculus
