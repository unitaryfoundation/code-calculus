import CodeCalculus.Invariants
import CodeCalculus.State
import CodeCalculus.Term
import CodeCalculus.Eval

namespace CodeCalculus

/-!
# Kernel obligation mechanization (slice, )

Kernel obligation lemmas for `spec/OPERATIONAL_SEMANTICS.md` §4.8–§4.10:
primitive determinism, sequence associativity, the direct-sum laws up to list
permutation, both partial-inverse clauses, both clauses of the frame law (the
addition clause under its allocation-compatibility premise, ), and
cross-sector permutation. The later-layer well-formedness instance of  is
not here ().
-/

/-- Primitive determinism (OBL-PRIMITIVE-DETERMINISM): a command's evaluation is
    functional in its input state. -/
theorem eval_deterministic : ∀ (m : Command) (s t1 t2 : CodeState),
    Eval m s t1 → Eval m s t2 → t1 = t2 := by
  intro m
  induction m with
  | skip =>
      intro s t1 t2 h1 h2
      cases h1; cases h2; rfl
  | delete r =>
      intro s t1 t2 h1 h2
      cases h1 with
      | delete _ _ heq1 =>
        cases h2 with
        | delete _ _ heq2 =>
          rw [heq1, heq2]
  | addStab sector support =>
      intro s t1 t2 h1 h2
      cases h1 with
      | add _ _ _ _ _ heq1 =>
        cases h2 with
        | add _ _ _ _ _ heq2 =>
          rw [heq1, heq2]
  | graft qubit sector orderedIds =>
      intro s t1 t2 h1 h2
      cases h1 with
      | graft _ _ _ _ _ _ _ _ heq1 =>
        cases h2 with
        | graft _ _ _ _ _ _ _ _ heq2 =>
          rw [heq1, heq2]
  | rebase sector matrix =>
      intro s t1 t2 h1 h2
      cases h1 with
      | rebase _ _ heq1 _ =>
        cases h2 with
        | rebase _ _ heq2 _ =>
          rw [heq1, heq2]
  | hadamard T =>
      intro s t1 t2 h1 h2
      cases h1 with
      | hadamard _ heq1 _ =>
        cases h2 with
        | hadamard _ heq2 _ =>
          rw [heq1, heq2]
  | peel q tau r_id =>
      intro s t1 t2 h1 h2
      cases h1 with
      | peel _ _ _ _ heq1 _ =>
        cases h2 with
        | peel _ _ _ _ heq2 _ =>
          rw [heq1, heq2]
  | puncture q =>
      intro s t1 t2 h1 h2
      cases h1 with
      | puncture _ heq1 _ =>
        cases h2 with
        | puncture _ heq2 _ =>
          rw [heq1, heq2]
  | extend delta adds =>
      intro s t1 t2 h1 h2
      cases h1 with
      | extend _ heq1 _ =>
        cases h2 with
        | extend _ heq2 _ =>
          rw [heq1, heq2]
  | seq m1 m2 ih1 ih2 =>
      intro s t1 t2 h1 h2
      cases h1 with
      | seq h1a h1b =>
        cases h2 with
        | seq h2a h2b =>
          have ha := ih1 s _ _ h1a h2a
          subst ha
          exact ih2 _ t1 t2 h1b h2b

/-- Sequence associativity (OBL-SEQUENCE-ASSOCIATIVITY), left-to-right. -/
theorem seq_assoc_fwd (m1 m2 m3 : Command) (s s' : CodeState)
    (h : Eval (Command.seq (Command.seq m1 m2) m3) s s') :
    Eval (Command.seq m1 (Command.seq m2 m3)) s s' := by
  cases h with
  | seq h12 h3 =>
    cases h12 with
    | seq h1 h2 =>
      exact Eval.seq h1 (Eval.seq h2 h3)

/-- Sequence associativity (OBL-SEQUENCE-ASSOCIATIVITY), right-to-left. -/
theorem seq_assoc_bwd (m1 m2 m3 : Command) (s s' : CodeState)
    (h : Eval (Command.seq m1 (Command.seq m2 m3)) s s') :
    Eval (Command.seq (Command.seq m1 m2) m3) s s' := by
  cases h with
  | seq h1 h23 =>
    cases h23 with
    | seq h2 h3 =>
      exact Eval.seq (Eval.seq h1 h2) h3

/-- Direct sum is associative at the state level (OBL-DIRECT-SUM-LAWS). -/
theorem directSum_assoc (a b c : CodeState) :
    directSumState (directSumState a b) c = directSumState a (directSumState b c) := by
  unfold directSumState
  cases a; cases b; cases c
  simp [List.append_assoc]

/-- Direct sum laws: commutativity up to list permutation of each field
    (OBL-DIRECT-SUM-LAWS). The Lean encoding uses list append, so literal
    equality would require ordered summands; the spec's literal equality is
    the corresponding permutation. -/
theorem directSum_comm_perm_Q (a b : CodeState) :
    (directSumState a b).Q.Perm (directSumState b a).Q := by
  unfold directSumState
  simp [List.perm_append_comm]

theorem directSum_comm_perm_rows (a b : CodeState) :
    (directSumState a b).rows.Perm (directSumState b a).rows := by
  unfold directSumState
  simp [List.perm_append_comm]

theorem directSum_comm_perm_used (a b : CodeState) :
    (directSumState a b).used.Perm (directSumState b a).used := by
  unfold directSumState
  simp [List.perm_append_comm]

/-- Commutativity up to `≡` (`OBL-DIRECT-SUM-LAWS`): the three permutations
    above give the three set equalities, the namespace clause included. -/
theorem directSum_comm_equiv (a b : CodeState) :
    directSumState a b ≡ directSumState b a :=
  ⟨fun q => by rw [(directSum_comm_perm_Q a b).contains_eq],
   fun r => by rw [(directSum_comm_perm_rows a b).contains_eq],
   fun x => by rw [(directSum_comm_perm_used a b).contains_eq]⟩

/-- Associativity up to `≡`, from the literal equality. -/
theorem directSum_assoc_equiv (a b c : CodeState) :
    directSumState (directSumState a b) c ≡ directSumState a (directSumState b c) :=
  codeStateEquiv_of_eq (directSum_assoc a b c)

/-- Add-then-delete partial inverse (OBL-PARTIAL-INVERSE-LAWS): deleting the
    canonically minted row of an add restores the displayed rows, under the
    hypothesis that no existing row already carries that (fresh) identifier. -/
theorem add_then_delete_rows (s : CodeState) (sector : Sector) (support : List Nat)
    (hrows : ∀ row ∈ s.rows, row.id ≠ canonicalMint s.used) :
    (deleteState (addState s sector support) (canonicalMint s.used)).rows = s.rows := by
  unfold deleteState addState
  -- The appended row is filtered out (its id is the minted one).
  have hsingle : ([Row.mk (canonicalMint s.used) sector support].filter
      (fun row => row.id ≠ canonicalMint s.used)) = [] := by
    simp [List.filter_cons]
  -- The original rows are unchanged by the filter, by the freshness hypothesis.
  have horig : (s.rows.filter (fun row => row.id ≠ canonicalMint s.used)) = s.rows := by
    exact List.filter_eq_self.mpr (fun row hr =>
      decide_eq_true (hrows row hr))
  rw [List.filter_append, horig, hsingle]
  simp

/-- The used set strictly grows under add-then-delete. -/
theorem add_then_delete_used (s : CodeState) (sector : Sector) (support : List Nat) :
    (deleteState (addState s sector support) (canonicalMint s.used)).used =
      s.used ++ [canonicalMint s.used] := by
  unfold deleteState addState
  rfl

/-- Delete-then-add (OBL-PARTIAL-INVERSE-LAWS): the used set after deleting `r`
    and re-adding `support` is the original used set plus one fresh identifier. -/
theorem delete_then_add_used (s : CodeState) (r : Nat) (sector : Sector) (support : List Nat) :
    (addState (deleteState s r) sector support).used = s.used ++ [canonicalMint s.used] := by
  unfold addState deleteState
  rfl

/-- Delete-then-add: the re-added row carries the supplied support. -/
theorem delete_then_add_rows (s : CodeState) (r : Nat) (sector : Sector) (support : List Nat) :
    (addState (deleteState s r) sector support).rows =
      (s.rows.filter (fun row => row.id ≠ r)) ++ [Row.mk (canonicalMint s.used) sector support] := by
  unfold addState deleteState
  rfl

/-- Helper: filtering a row list by a predicate that holds of every row is the
    identity. -/
theorem filter_rows_not_id (rows : List Row) (r : Nat)
    (h : ∀ row ∈ rows, row.id ≠ r) :
    rows.filter (fun row => row.id ≠ r) = rows := by
  apply List.filter_eq_self.mpr
  intro row hr
  exact decide_eq_true (h row hr)

/-- Frame law, deletion clause (OBL-FRAME-LAW): deleting `r` from the direct sum
    of two states equals deleting `r` from the summand that contains it, when `r`
    is displayed in the left summand and not the right. -/
theorem frame_law_delete_left (a b : CodeState) (r : Nat)
    (hrA : ∃ row ∈ a.rows, row.id = r)
    (hrB : ¬ (∃ row ∈ b.rows, row.id = r)) :
    deleteState (directSumState a b) r = directSumState (deleteState a r) b := by
  unfold deleteState directSumState
  have hb : b.rows.filter (fun row => row.id ≠ r) = b.rows := by
    apply filter_rows_not_id
    intro row hr h
    exact hrB ⟨row, hr, h⟩
  -- Row equality follows from filter_append + hb; Q and used are definitional.
  have hrows : (a.rows ++ b.rows).filter (fun row => row.id ≠ r) =
      a.rows.filter (fun row => row.id ≠ r) ++ b.rows := by
    rw [List.filter_append, hb]
  -- Rewrite the row field using hrows; Q and used are definitional.
  rw [hrows]

/-- Frame law, deletion clause (symmetric case). -/
theorem frame_law_delete_right (a b : CodeState) (r : Nat)
    (hrA : ¬ (∃ row ∈ a.rows, row.id = r))
    (hrB : ∃ row ∈ b.rows, row.id = r) :
    deleteState (directSumState a b) r = directSumState a (deleteState b r) := by
  unfold deleteState directSumState
  have ha : a.rows.filter (fun row => row.id ≠ r) = a.rows := by
    apply filter_rows_not_id
    intro row hr h
    exact hrA ⟨row, hr, h⟩
  have hrows : (a.rows ++ b.rows).filter (fun row => row.id ≠ r) =
      a.rows ++ b.rows.filter (fun row => row.id ≠ r) := by
    rw [List.filter_append, ha]
  rw [hrows]

/-- Delete-delete cross-sector permutation: deleting two generators commutes. -/
theorem delete_delete_comm (s : CodeState) (r1 r2 : Nat) :
    deleteState (deleteState s r1) r2 = deleteState (deleteState s r2) r1 := by
  unfold deleteState
  simp [List.filter_filter, Bool.and_comm]

/-- Delete-add cross-sector permutation: deleting `r` and adding a check commute
    when `r` is not the minted identifier. -/
theorem delete_add_comm (s : CodeState) (r : Nat) (sector : Sector) (support : List Nat)
    (hr : r ≠ canonicalMint s.used) :
    deleteState (addState s sector support) r = addState (deleteState s r) sector support := by
  unfold deleteState addState
  have hnew : (Row.mk (canonicalMint s.used) sector support).id ≠ r := hr.symm
  have hfilter : ([Row.mk (canonicalMint s.used) sector support].filter
      (fun row => row.id ≠ r)) = [Row.mk (canonicalMint s.used) sector support] := by
    simp [List.filter_cons, hnew]
  have hrows : (s.rows ++ [Row.mk (canonicalMint s.used) sector support]).filter
      (fun row => row.id ≠ r) =
      s.rows.filter (fun row => row.id ≠ r) ++ [Row.mk (canonicalMint s.used) sector support] := by
    rw [List.filter_append, hfilter]
  rw [hrows]

/-- Add-add cross-sector permutation: two adds of distinct sectors yield distinct
    states (the identifier-to-sector assignment swaps). -/
theorem add_add_ne (s : CodeState) (sx sz : Sector) (sxsupp szsupp : List Nat)
    (hsec : sx ≠ sz) :
    ¬ (addState (addState s sx sxsupp) sz szsupp =
       addState (addState s sz szsupp) sx sxsupp) := by
  intro h
  have hrows := congrArg CodeState.rows h
  have hdropL : (addState (addState s sx sxsupp) sz szsupp).rows.drop s.rows.length =
      [Row.mk (canonicalMint s.used) sx sxsupp,
       Row.mk (canonicalMint (s.used ++ [canonicalMint s.used])) sz szsupp] := by
    simp [addState, List.drop_append]
  have hdropR : (addState (addState s sz szsupp) sx sxsupp).rows.drop s.rows.length =
      [Row.mk (canonicalMint s.used) sz szsupp,
       Row.mk (canonicalMint (s.used ++ [canonicalMint s.used])) sx sxsupp] := by
    simp [addState, List.drop_append]
  have hdropEq := congrArg (fun xs => xs.drop s.rows.length) hrows
  rw [hdropL, hdropR] at hdropEq
  have hfirst : Row.mk (canonicalMint s.used) sx sxsupp =
                Row.mk (canonicalMint s.used) sz szsupp := by
    cases hdropEq
    rfl
  exact hsec (congrArg Row.sector hfirst)

/-! ## Frame law, addition clause (OBL-FRAME-LAW, )

`spec/OPERATIONAL_SEMANTICS.md` §4.9, addition clause: for a direct sum
`A ⊕ B` and a candidate row with support inside `Q_A`,

1. `addStab` is applicable on `A ⊕ B` iff it is applicable on `A`
   (`frame_law_add_applicable_iff`), because the opposite-sector commutation
   and same-sector independence premises split per block; and
2. under the allocation-compatibility premise
   `canonicalMint (A.used ++ B.used) = canonicalMint A.used`, the result is
   `A' ⊕ B` up to the order of rows and of `used`
   (`frame_law_add_rows_perm`, `frame_law_add_used_perm`,
   `frame_law_add_equiv`), and `A' ⊕ B` is itself a direct sum whose
   `C-DIRECT-SUM` premises hold (`frame_law_add_directSum_evalExpr`).

The premise is characterized exactly: it holds iff `canonicalMint A.used` is
not in `B.used` (`canonicalMint_append_eq_iff`). Without it the clause fails
(`frame_law_add_needs_mint_premise`).

Hypotheses: the `C-DIRECT-SUM` qubit-disjointness premise, and that the
displayed supports of each summand lie in that summand's namespace. The latter
is the fourth conjunct of `EncodingWellFormed`; it is taken on its own so the
theorems do not assume I1 or I2 of the summands.
-/

/-! ### Vectors over a concatenated qubit list -/

theorem xorVec_length (a b : List Bool) (h : a.length = b.length) :
    (xorVec a b).length = a.length := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons _ _ => simp at h
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      simp only [xorVec, List.length_cons] at *
      rw [ih ys (by omega)]

theorem xorVec_append (a1 b1 a2 b2 : List Bool) (h : a1.length = b1.length) :
    xorVec (a1 ++ a2) (b1 ++ b2) = xorVec a1 b1 ++ xorVec a2 b2 := by
  induction a1 generalizing b1 with
  | nil =>
    cases b1 with
    | nil => rfl
    | cons _ _ => simp at h
  | cons x xs ih =>
    cases b1 with
    | nil => simp at h
    | cons y ys =>
      simp only [List.cons_append, xorVec, List.length_cons] at *
      rw [ih ys (by omega)]

theorem xorVec_replicate_false_left (n : Nat) (b : List Bool) (h : b.length = n) :
    xorVec (List.replicate n false) b = b := by
  subst h
  induction b with
  | nil => rfl
  | cons y ys ih =>
    rw [List.length_cons, List.replicate_succ]
    simp only [xorVec]
    rw [ih]
    cases y <;> rfl

theorem combineRows_length (n : Nat) (vs : List (List Bool)) (cs : List Bool)
    (h : ∀ v ∈ vs, v.length = n) : (combineRows n vs cs).length = n := by
  induction vs generalizing cs with
  | nil =>
    show (List.replicate n false).length = n
    simp
  | cons v vs ih =>
    cases cs with
    | nil =>
      show (List.replicate n false).length = n
      simp
    | cons c cs =>
      have hv := h v (List.mem_cons.mpr (Or.inl rfl))
      have hrest := ih cs (fun v' hv' => h v' (List.mem_cons.mpr (Or.inr hv')))
      cases c with
      | true =>
        simp only [combineRows]
        rw [xorVec_length v _ (by rw [hv, hrest]), hv]
      | false =>
        simp only [combineRows]
        exact hrest

theorem combineRows_zero_coeffs (n : Nat) (vs : List (List Bool)) :
    combineRows n vs (List.replicate vs.length false) = List.replicate n false := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [List.length_cons, List.replicate_succ]
    simp only [combineRows]
    exact ih

/-- Combining vectors that are zero on a left block leaves that block zero. -/
theorem combineRows_padLeft (nA nB : Nat) (vs : List (List Bool)) (cs : List Bool)
    (hv : ∀ v ∈ vs, v.length = nB) (hcs : cs.length = vs.length) :
    combineRows (nA + nB) (vs.map (fun v => List.replicate nA false ++ v)) cs =
      List.replicate nA false ++ combineRows nB vs cs := by
  induction vs generalizing cs with
  | nil =>
    cases cs with
    | nil =>
      show List.replicate (nA + nB) false = List.replicate nA false ++ List.replicate nB false
      exact List.replicate_append_replicate.symm
    | cons _ _ => simp at hcs
  | cons v vs ih =>
    cases cs with
    | nil => simp at hcs
    | cons c cs =>
      have hv' : ∀ v' ∈ vs, v'.length = nB :=
        fun v' h => hv v' (List.mem_cons.mpr (Or.inr h))
      have hcs' : cs.length = vs.length := by
        simp only [List.length_cons] at hcs
        omega
      cases c with
      | true =>
        simp only [List.map_cons, combineRows]
        rw [ih cs hv' hcs',
          xorVec_append (List.replicate nA false) (List.replicate nA false) v
            (combineRows nB vs cs) rfl,
          xorVec_replicate_false_left nA (List.replicate nA false) (by simp)]
      | false =>
        simp only [List.map_cons, combineRows]
        exact ih cs hv' hcs'

/-- A combination over a concatenated qubit list splits into one combination
    per block when every vector is supported in one block. -/
theorem combineRows_split (nA nB : Nat) (vsA vsB : List (List Bool)) (csA csB : List Bool)
    (hvA : ∀ v ∈ vsA, v.length = nA) (hvB : ∀ v ∈ vsB, v.length = nB)
    (hcsA : csA.length = vsA.length) (hcsB : csB.length = vsB.length) :
    combineRows (nA + nB)
        (vsA.map (fun v => v ++ List.replicate nB false) ++
          vsB.map (fun v => List.replicate nA false ++ v))
        (csA ++ csB) =
      combineRows nA vsA csA ++ combineRows nB vsB csB := by
  induction vsA generalizing csA with
  | nil =>
    cases csA with
    | nil =>
      simp only [List.map_nil, List.nil_append]
      show combineRows (nA + nB) (vsB.map (fun v => List.replicate nA false ++ v)) csB =
        List.replicate nA false ++ combineRows nB vsB csB
      exact combineRows_padLeft nA nB vsB csB hvB hcsB
    | cons _ _ => simp at hcsA
  | cons v vsA ih =>
    cases csA with
    | nil => simp at hcsA
    | cons c csA =>
      have hv0 := hvA v (List.mem_cons.mpr (Or.inl rfl))
      have hvA' : ∀ v' ∈ vsA, v'.length = nA :=
        fun v' h => hvA v' (List.mem_cons.mpr (Or.inr h))
      have hcsA' : csA.length = vsA.length := by
        simp only [List.length_cons] at hcsA
        omega
      cases c with
      | true =>
        simp only [List.map_cons, List.cons_append, combineRows]
        rw [ih csA hvA' hcsA',
          xorVec_append v (combineRows nA vsA csA) (List.replicate nB false)
            (combineRows nB vsB csB) (by rw [hv0, combineRows_length nA vsA csA hvA']),
          xorVec_replicate_false_left nB _ (combineRows_length nB vsB csB hvB)]
      | false =>
        simp only [List.map_cons, List.cons_append, combineRows]
        exact ih csA hvA' hcsA'

theorem rowVector_length (Q : List Nat) (r : Row) : (rowVector Q r).length = Q.length := by
  simp [rowVector]

theorem rowVector_append (QA QB : List Nat) (r : Row) :
    rowVector (QA ++ QB) r = rowVector QA r ++ rowVector QB r := by
  simp [rowVector, List.map_append]

/-- A row whose support misses every qubit of `Q` has the zero vector over `Q`. -/
theorem rowVector_eq_replicate_of_disjoint (Q : List Nat) (r : Row)
    (h : ∀ q ∈ Q, q ∉ r.support) :
    rowVector Q r = List.replicate Q.length false := by
  unfold rowVector
  induction Q with
  | nil => rfl
  | cons q qs ih =>
    rw [List.map_cons, List.length_cons, List.replicate_succ]
    have hq : r.support.contains q = false := by
      cases hc : r.support.contains q with
      | false => rfl
      | true =>
        exact absurd (List.contains_iff_mem.mp hc) (h q (List.mem_cons.mpr (Or.inl rfl)))
    rw [hq, ih (fun q' hq' => h q' (List.mem_cons.mpr (Or.inr hq')))]

/-- Span membership over a direct sum, for a target supported in the left block:
    it holds iff it holds in the left block alone. The right-block rows
    contribute only to the right block, where the target is zero. -/
theorem inSpanRows_directSum_iff (QA QB : List Nat) (rowsA rowsB : List Row) (tA : List Bool)
    (hA : ∀ r ∈ rowsA, ∀ q ∈ QB, q ∉ r.support)
    (hB : ∀ r ∈ rowsB, ∀ q ∈ QA, q ∉ r.support)
    (ht : tA.length = QA.length) :
    inSpanRows (QA ++ QB) (rowsA ++ rowsB) (tA ++ List.replicate QB.length false) ↔
      inSpanRows QA rowsA tA := by
  have hmapA : rowsA.map (rowVector (QA ++ QB)) =
      (rowsA.map (rowVector QA)).map (fun v => v ++ List.replicate QB.length false) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro r hr
    show rowVector (QA ++ QB) r = rowVector QA r ++ List.replicate QB.length false
    rw [rowVector_append, rowVector_eq_replicate_of_disjoint QB r (hA r hr)]
  have hmapB : rowsB.map (rowVector (QA ++ QB)) =
      (rowsB.map (rowVector QB)).map (fun v => List.replicate QA.length false ++ v) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro r hr
    show rowVector (QA ++ QB) r = List.replicate QA.length false ++ rowVector QB r
    rw [rowVector_append, rowVector_eq_replicate_of_disjoint QA r (hB r hr)]
  have hvA : ∀ v ∈ rowsA.map (rowVector QA), v.length = QA.length := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨r, _, rfl⟩
    exact rowVector_length QA r
  have hvB : ∀ v ∈ rowsB.map (rowVector QB), v.length = QB.length := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨r, _, rfl⟩
    exact rowVector_length QB r
  unfold inSpanRows
  rw [List.map_append, hmapA, hmapB]
  simp only [List.length_append]
  constructor
  · rintro ⟨cs, hlen, heq⟩
    have h1 : (cs.take rowsA.length).length = (rowsA.map (rowVector QA)).length := by
      rw [List.length_take, List.length_map]
      omega
    have h2 : (cs.drop rowsA.length).length = (rowsB.map (rowVector QB)).length := by
      rw [List.length_drop, List.length_map]
      omega
    refine ⟨cs.take rowsA.length, ?_, ?_⟩
    · rw [h1, List.length_map]
    · rw [← List.take_append_drop rowsA.length cs,
        combineRows_split QA.length QB.length _ _ _ _ hvA hvB h1 h2] at heq
      have hl : (combineRows QA.length (rowsA.map (rowVector QA))
          (cs.take rowsA.length)).length = tA.length := by
        rw [combineRows_length _ _ _ hvA, ht]
      exact (List.append_inj heq hl).1
  · rintro ⟨cs, hlen, heq⟩
    have h1 : cs.length = (rowsA.map (rowVector QA)).length := by
      rw [List.length_map]
      exact hlen
    have h2 : (List.replicate rowsB.length false).length = (rowsB.map (rowVector QB)).length := by
      rw [List.length_replicate, List.length_map]
    refine ⟨cs ++ List.replicate rowsB.length false, ?_, ?_⟩
    · rw [List.length_append, List.length_replicate, hlen]
    · rw [combineRows_split QA.length QB.length _ _ _ _ hvA hvB h1 h2, heq]
      have h3 : List.replicate rowsB.length false =
          List.replicate (rowsB.map (rowVector QB)).length false := by
        rw [List.length_map]
      rw [h3, combineRows_zero_coeffs]

/-! ### Per-block splitting of the `addStab` premises -/

theorem sectorRows_directSum (A B : CodeState) (sector : Sector) :
    sectorRows (directSumState A B) sector = sectorRows A sector ++ sectorRows B sector := by
  show List.filter _ (A.rows ++ B.rows) = _
  rw [List.filter_append]
  rfl

/-- Two supports with no common qubit have intersection size zero. -/
theorem supportIntersectionSize_eq_zero (a b : List Nat) (h : ∀ q ∈ a, q ∉ b) :
    supportIntersectionSize a b = 0 := by
  unfold supportIntersectionSize
  suffices hgen : ∀ acc, a.foldl (fun n q => if b.contains q then n + 1 else n) acc = acc from
    hgen 0
  induction a with
  | nil => intro acc; rfl
  | cons q qs ih =>
    intro acc
    rw [List.foldl_cons]
    have hq : b.contains q = false := by
      cases hc : b.contains q with
      | false => rfl
      | true =>
        exact absurd (List.contains_iff_mem.mp hc) (h q (List.mem_cons.mpr (Or.inl rfl)))
    simp only [hq, Bool.false_eq_true, ↓reduceIte]
    exact ih (fun q' hq' => h q' (List.mem_cons.mpr (Or.inr hq'))) acc

/-- The same-sector independence premise of `addStab` on `A ⊕ B` reduces to the
    premise on `A` when the candidate support lies in `Q_A`. The minted
    identifiers (`cS` on the sum, `cA` on the summand) do not enter the vector. -/
theorem inSpanRows_add_directSum_iff (A B : CodeState) (sector : Sector) (support : List Nat)
    (hQ : DisjointList A.Q B.Q)
    (hsupA : ∀ row ∈ A.rows, supportSubset row.support A.Q)
    (hsupB : ∀ row ∈ B.rows, supportSubset row.support B.Q)
    (hloc : supportSubset support A.Q) (cS cA : Nat) :
    inSpanRows (directSumState A B).Q (sectorRows (directSumState A B) sector)
        (rowVector (directSumState A B).Q ⟨cS, sector, support⟩) ↔
      inSpanRows A.Q (sectorRows A sector) (rowVector A.Q ⟨cA, sector, support⟩) := by
  have hdisj : ∀ q ∈ B.Q, q ∉ (⟨cS, sector, support⟩ : Row).support :=
    fun q hqB hqs => hQ q (hloc q hqs) hqB
  have hA : ∀ r ∈ sectorRows A sector, ∀ q ∈ B.Q, q ∉ r.support := by
    intro r hr q hqB hqs
    exact hQ q (hsupA r (List.mem_filter.mp hr).1 q hqs) hqB
  have hB : ∀ r ∈ sectorRows B sector, ∀ q ∈ A.Q, q ∉ r.support := by
    intro r hr q hqA hqs
    exact hQ q hqA (hsupB r (List.mem_filter.mp hr).1 q hqs)
  have hvec : rowVector A.Q ⟨cS, sector, support⟩ = rowVector A.Q ⟨cA, sector, support⟩ := rfl
  show inSpanRows (A.Q ++ B.Q) (sectorRows (directSumState A B) sector)
      (rowVector (A.Q ++ B.Q) ⟨cS, sector, support⟩) ↔ _
  rw [sectorRows_directSum, rowVector_append,
    rowVector_eq_replicate_of_disjoint B.Q _ hdisj, hvec]
  exact inSpanRows_directSum_iff A.Q B.Q _ _ _ hA hB (rowVector_length A.Q _)

/-- Frame law, addition clause, applicability (sum to summand): an `addStab`
    derivable on `A ⊕ B` with support in `Q_A` is derivable on `A`. -/
theorem frame_law_add_to_summand (A B : CodeState) (sector : Sector) (support : List Nat)
    (s' : CodeState)
    (hQ : DisjointList A.Q B.Q)
    (hsupA : ∀ row ∈ A.rows, supportSubset row.support A.Q)
    (hsupB : ∀ row ∈ B.rows, supportSubset row.support B.Q)
    (hloc : supportSubset support A.Q)
    (h : Eval (Command.addStab sector support) (directSumState A B) s') :
    Eval (Command.addStab sector support) A (addState A sector support) := by
  cases h with
  | add _ hNodup hSort hComm hSpan _ =>
    refine Eval.add hloc hNodup hSort ?_ ?_ rfl
    · intro row hrow hsec
      exact hComm row (List.mem_append_left _ hrow) hsec
    · intro hspanA
      exact hSpan ((inSpanRows_add_directSum_iff A B sector support hQ hsupA hsupB hloc
        _ _).mpr hspanA)

/-- Frame law, addition clause, applicability (summand to sum): an `addStab`
    derivable on `A` is derivable on `A ⊕ B`, with the sum's canonical mint. -/
theorem frame_law_add_of_summand (A B : CodeState) (sector : Sector) (support : List Nat)
    (sA' : CodeState)
    (hQ : DisjointList A.Q B.Q)
    (hsupA : ∀ row ∈ A.rows, supportSubset row.support A.Q)
    (hsupB : ∀ row ∈ B.rows, supportSubset row.support B.Q)
    (hloc : supportSubset support A.Q)
    (h : Eval (Command.addStab sector support) A sA') :
    Eval (Command.addStab sector support) (directSumState A B)
      (addState (directSumState A B) sector support) := by
  cases h with
  | add _ hNodup hSort hComm hSpan _ =>
    refine Eval.add ?_ hNodup hSort ?_ ?_ rfl
    · intro q hq
      exact List.mem_append_left _ (hloc q hq)
    · intro row hrow hsec
      rcases List.mem_append.mp hrow with hrA | hrB
      · exact hComm row hrA hsec
      · rw [supportIntersectionSize_eq_zero support row.support
          (fun q hq hq' => hQ q (hloc q hq) (hsupB row hrB q hq'))]
    · intro hspan
      exact hSpan ((inSpanRows_add_directSum_iff A B sector support hQ hsupA hsupB hloc
        _ _).mp hspan)

/-- Frame law, addition clause: applicability splits per block. -/
theorem frame_law_add_applicable_iff (A B : CodeState) (sector : Sector) (support : List Nat)
    (hQ : DisjointList A.Q B.Q)
    (hsupA : ∀ row ∈ A.rows, supportSubset row.support A.Q)
    (hsupB : ∀ row ∈ B.rows, supportSubset row.support B.Q)
    (hloc : supportSubset support A.Q) :
    (∃ s', Eval (Command.addStab sector support) (directSumState A B) s') ↔
      ∃ s', Eval (Command.addStab sector support) A s' :=
  ⟨fun ⟨s', h⟩ => ⟨_, frame_law_add_to_summand A B sector support s' hQ hsupA hsupB hloc h⟩,
   fun ⟨sA', h⟩ => ⟨_, frame_law_add_of_summand A B sector support sA' hQ hsupA hsupB hloc h⟩⟩

/-! ### The allocation-compatibility premise -/

/-- The canonical mint is the unique least identifier outside `used`. -/
theorem canonicalMint_eq_of_fresh_least (used : List Nat) (m : Nat)
    (hfresh : m ∉ used) (hleast : ∀ n, n < m → n ∈ used) : canonicalMint used = m := by
  rcases Nat.lt_trichotomy (canonicalMint used) m with hlt | heq | hgt
  · exact absurd (List.contains_iff_mem.mpr (hleast _ hlt)) (canonicalMint_fresh used)
  · exact heq
  · exact absurd (List.contains_iff_mem.mp (canonicalMint_least used m hgt)) hfresh

/-- The allocation-compatibility premise of §4.9 holds iff the summand's mint is
    not among the other summand's identifiers. -/
theorem canonicalMint_append_eq_iff (uA uB : List Nat) :
    canonicalMint (uA ++ uB) = canonicalMint uA ↔ canonicalMint uA ∉ uB := by
  constructor
  · intro h hmem
    apply canonicalMint_fresh (uA ++ uB)
    rw [h]
    exact List.contains_iff_mem.mpr (List.mem_append_right _ hmem)
  · intro h
    apply canonicalMint_eq_of_fresh_least
    · intro hmem
      rcases List.mem_append.mp hmem with hA | hB
      · exact canonicalMint_fresh uA (List.contains_iff_mem.mpr hA)
      · exact h hB
    · intro n hn
      exact List.mem_append_left _ (List.contains_iff_mem.mp (canonicalMint_least uA n hn))

/-! ### The result `A' ⊕ B` -/

theorem frame_law_add_Q (A B : CodeState) (sector : Sector) (support : List Nat) :
    (addState (directSumState A B) sector support).Q =
      (directSumState (addState A sector support) B).Q := rfl

/-- Under the allocation-compatibility premise, adding to the sum displays the
    same rows as adding to the left summand and then summing. -/
theorem frame_law_add_rows_perm (A B : CodeState) (sector : Sector) (support : List Nat)
    (hmint : canonicalMint (A.used ++ B.used) = canonicalMint A.used) :
    (addState (directSumState A B) sector support).rows.Perm
      (directSumState (addState A sector support) B).rows := by
  show ((A.rows ++ B.rows) ++ [Row.mk (canonicalMint (A.used ++ B.used)) sector support]).Perm
    ((A.rows ++ [Row.mk (canonicalMint A.used) sector support]) ++ B.rows)
  rw [hmint, List.append_assoc, List.append_assoc]
  exact List.Perm.append_left A.rows List.perm_append_comm

theorem frame_law_add_used_perm (A B : CodeState) (sector : Sector) (support : List Nat)
    (hmint : canonicalMint (A.used ++ B.used) = canonicalMint A.used) :
    (addState (directSumState A B) sector support).used.Perm
      (directSumState (addState A sector support) B).used := by
  show ((A.used ++ B.used) ++ [canonicalMint (A.used ++ B.used)]).Perm
    ((A.used ++ [canonicalMint A.used]) ++ B.used)
  rw [hmint, List.append_assoc, List.append_assoc]
  exact List.Perm.append_left A.used List.perm_append_comm

/-- State-level addition clause: `≡` holds under the premise. -/
theorem frame_law_add_equiv (A B : CodeState) (sector : Sector) (support : List Nat)
    (hmint : canonicalMint (A.used ++ B.used) = canonicalMint A.used) :
    addState (directSumState A B) sector support ≡
      directSumState (addState A sector support) B := by
  refine ⟨fun q => Iff.rfl, fun r => ?_, fun x => ?_⟩
  · rw [(frame_law_add_rows_perm A B sector support hmint).contains_eq]
  · rw [(frame_law_add_used_perm A B sector support hmint).contains_eq]

/-- The right-hand sum satisfies the `C-DIRECT-SUM` identifier premise. -/
theorem frame_law_add_used_disjoint (A B : CodeState) (sector : Sector) (support : List Nat)
    (hU : DisjointList A.used B.used)
    (hmint : canonicalMint (A.used ++ B.used) = canonicalMint A.used) :
    DisjointList (addState A sector support).used B.used := by
  intro x hx
  have hx' : x ∈ A.used ++ [canonicalMint A.used] := hx
  rcases List.mem_append.mp hx' with hA | hc
  · exact hU x hA
  · have hxc := List.mem_singleton.mp hc
    subst hxc
    exact (canonicalMint_append_eq_iff A.used B.used).mp hmint

/-- `A' ⊕ B` is a derivable direct sum. -/
theorem frame_law_add_directSum_evalExpr (A B : CodeState) (sector : Sector) (support : List Nat)
    (hQ : DisjointList A.Q B.Q) (hU : DisjointList A.used B.used)
    (hmint : canonicalMint (A.used ++ B.used) = canonicalMint A.used) :
    EvalExpr (StateExpr.directSum (StateExpr.base (addState A sector support)) (StateExpr.base B))
      (directSumState (addState A sector support) B) :=
  EvalExpr.directSum hQ (frame_law_add_used_disjoint A B sector support hU hmint)
    (EvalExpr.base _) (EvalExpr.base _)

/-- Frame law, addition clause (OBL-FRAME-LAW): an `addStab` on `A ⊕ B` with
    support in `Q_A` is an `addStab` on `A`, and under the
    allocation-compatibility premise its result is `A' ⊕ B` up to `≡`. -/
theorem frame_law_add (A B : CodeState) (sector : Sector) (support : List Nat) (s' : CodeState)
    (hQ : DisjointList A.Q B.Q)
    (hsupA : ∀ row ∈ A.rows, supportSubset row.support A.Q)
    (hsupB : ∀ row ∈ B.rows, supportSubset row.support B.Q)
    (hloc : supportSubset support A.Q)
    (hmint : canonicalMint (A.used ++ B.used) = canonicalMint A.used)
    (h : Eval (Command.addStab sector support) (directSumState A B) s') :
    Eval (Command.addStab sector support) A (addState A sector support) ∧
      (s' ≡ directSumState (addState A sector support) B) := by
  refine ⟨frame_law_add_to_summand A B sector support s' hQ hsupA hsupB hloc h, ?_⟩
  have hs' : s' = addState (directSumState A B) sector support := by
    cases h with
    | add _ _ _ _ _ hs' => exact hs'
  rw [hs']
  exact frame_law_add_equiv A B sector support hmint

/-! ### Why the premise is a hypothesis -/

/-- Left summand of the allocation-incompatibility witness: one qubit, no
    rows, identifier `0` retired. -/
def mintWitnessA : CodeState := { Q := [0], rows := [], used := [0] }

/-- Right summand: one qubit, no rows, identifier `1` retired. The summands
    satisfy both `C-DIRECT-SUM` premises, and `canonicalMint [0] = 1 ∈ [1]`. -/
def mintWitnessB : CodeState := { Q := [1], rows := [], used := [1] }

theorem mintWitness_mint_ne :
    canonicalMint (mintWitnessA.used ++ mintWitnessB.used) ≠ canonicalMint mintWitnessA.used := by
  decide

/-- Without the premise the addition clause fails: the row added on the sum is
    minted `2`, the row added on the summand is minted `1`. -/
theorem frame_law_add_needs_mint_premise :
    ¬ (addState (directSumState mintWitnessA mintWitnessB) Sector.X [0] ≡
        directSumState (addState mintWitnessA Sector.X [0]) mintWitnessB) := by
  intro h
  have hmem := (h.2.1 ⟨2, Sector.X, [0]⟩).mp (by decide)
  exact absurd hmem (by decide)

/-! ### The namespace clause of `≡` ()

Before 2026-10-29 the equality read labeled rows and `used` only, so two
well-formed states that differ in a bare qubit were equal while differing in
`n`, `k`, and applicability. The witness below is the acceptance condition of
: the same two states are now distinguished. -/

/-- Two qubits, no rows, nothing minted. -/
def namespaceWitnessA : CodeState := { Q := [0, 1], rows := [], used := [] }

/-- Three qubits, no rows, nothing minted. -/
def namespaceWitnessB : CodeState := { Q := [0, 1, 2], rows := [], used := [] }

theorem namespaceWitnessA_wf : EncodingWellFormed namespaceWitnessA := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro rX _ hX; cases hX
  · intro r hr; cases hr

theorem namespaceWitnessB_wf : EncodingWellFormed namespaceWitnessB := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro rX _ hX; cases hX
  · intro r hr; cases hr

/-- The two states agree on the rows and on `used`, the two clauses the
    equality read before . -/
theorem namespaceWitness_rows_used_agree :
    (∀ r, namespaceWitnessA.rows.contains r ↔ namespaceWitnessB.rows.contains r) ∧
    (∀ x, namespaceWitnessA.used.contains x ↔ namespaceWitnessB.used.contains x) :=
  ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩

/-- They are not `≡`: the namespaces differ. -/
theorem namespaceWitness_not_equiv : ¬ (namespaceWitnessA ≡ namespaceWitnessB) := by
  intro h
  exact absurd ((h.1 2).mpr (by decide)) (by decide)

/-- They differ in `n` and in `k`, which is what the clause protects. -/
theorem namespaceWitness_n_k_differ :
    namespaceWitnessA.Q.length ≠ namespaceWitnessB.Q.length ∧
    stateK namespaceWitnessA ≠ stateK namespaceWitnessB := by
  decide

/-- Map a membership predicate to the all-false vector. -/
theorem pr199_map_contains_eq_replicate (l : List Nat) (support : List Nat)
    (h : ∀ q ∈ l, support.contains q = false) :
    l.map (fun q => support.contains q) = List.replicate l.length false := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.length]
      rw [h x List.mem_cons_self,
        ih (fun q hq => h q (List.mem_cons_of_mem _ hq)),
        List.replicate_succ]

/-- A row vector over `Q` has the length of `Q`. -/
theorem pr199_rowVector_length (Q : List Nat) (r : Row) :
    (rowVector Q r).length = Q.length := by
  unfold rowVector
  simp

/-- Row vector over a concatenation of disjoint namespaces, left block: the
    right-block coordinates are all false. -/
theorem pr199_rowVector_append_left (a b : CodeState) (r : Row)
    (hsub : ∀ q ∈ r.support, q ∈ a.Q) (hdisj : DisjointList a.Q b.Q) :
    rowVector (a.Q ++ b.Q) r = rowVector a.Q r ++ List.replicate b.Q.length false := by
  unfold rowVector
  have hzero : b.Q.map (fun q => r.support.contains q)
      = List.replicate b.Q.length false := by
    apply pr199_map_contains_eq_replicate
    intro q hq
    cases hc : r.support.contains q with
    | false => rfl
    | true =>
        have hqs : q ∈ r.support := List.contains_iff_mem.mp hc
        exact (hdisj q (hsub q hqs) hq).elim
  rw [List.map_append, hzero]

/-- Row vector over a concatenation of disjoint namespaces, right block: the
    left-block coordinates are all false. -/
theorem pr199_rowVector_append_right (a b : CodeState) (r : Row)
    (hsub : ∀ q ∈ r.support, q ∈ b.Q) (hdisj : DisjointList a.Q b.Q) :
    rowVector (a.Q ++ b.Q) r = List.replicate a.Q.length false ++ rowVector b.Q r := by
  unfold rowVector
  have hzero : a.Q.map (fun q => r.support.contains q)
      = List.replicate a.Q.length false := by
    apply pr199_map_contains_eq_replicate
    intro q hq
    cases hc : r.support.contains q with
    | false => rfl
    | true =>
        have hqs : q ∈ r.support := List.contains_iff_mem.mp hc
        exact (hdisj q hq (hsub q hqs)).elim
  rw [List.map_append, hzero]



/-- `xorVec` distributes over append of equal-length components. -/
theorem pr199_xorVec_append (a b c d : List Bool)
    (hab : a.length = c.length) :
    xorVec (a ++ b) (c ++ d) = xorVec a c ++ xorVec b d := by
  induction a generalizing c with
  | nil =>
      cases c with
      | nil => rfl
      | cons _ _ => simp [List.length] at hab
  | cons x xs ih =>
      cases c with
      | nil => simp [List.length] at hab
      | cons y cs =>
          have hlen : xs.length = cs.length := by
            simp only [List.length] at hab
            omega
          simp only [List.cons_append, xorVec]
          rw [ih cs hlen]

/-- XOR with an all-false vector of the same length is the identity (left). -/
theorem pr199_xorVec_false_left (n : Nat) (v : List Bool) (hv : v.length = n) :
    xorVec (List.replicate n false) v = v := by
  induction n generalizing v with
  | zero =>
      cases v with
      | nil => rfl
      | cons _ _ => simp [List.length] at hv
  | succ n ih =>
      cases v with
      | nil => simp [List.length] at hv
      | cons x xs =>
          have hxs : xs.length = n := by
            simp only [List.length] at hv
            omega
          simp only [List.replicate_succ, xorVec]
          cases x <;> simp [ih xs hxs]

/-- XOR with an all-false vector of the same length is the identity (right). -/
theorem pr199_xorVec_false_right (n : Nat) (v : List Bool) (hv : v.length = n) :
    xorVec v (List.replicate n false) = v := by
  induction n generalizing v with
  | zero =>
      cases v with
      | nil => rfl
      | cons _ _ => simp [List.length] at hv
  | succ n ih =>
      cases v with
      | nil => simp [List.length] at hv
      | cons x xs =>
          have hxs : xs.length = n := by
            simp only [List.length] at hv
            omega
          simp only [List.replicate_succ, xorVec]
          cases x <;> simp [ih xs hxs]

/-- `xorVec` of two length-`n` vectors has length `n`. -/
theorem pr199_xorVec_length (n : Nat) (a b : List Bool)
    (ha : a.length = n) (hb : b.length = n) :
    (xorVec a b).length = n := by
  induction n generalizing a b with
  | zero =>
      obtain rfl : a = [] := List.eq_nil_of_length_eq_zero ha
      obtain rfl : b = [] := List.eq_nil_of_length_eq_zero hb
      simp [xorVec]
  | succ n ih =>
      cases a with
      | nil => simp [List.length] at ha
      | cons x xs =>
          cases b with
          | nil => simp [List.length] at hb
          | cons y ys =>
              have hxs : xs.length = n := by
                simp only [List.length] at ha
                omega
              have hys : ys.length = n := by
                simp only [List.length] at hb
                omega
              simp only [List.length, xorVec]
              rw [ih xs ys hxs hys]

/-- `combineRows n vs cs` has length `n` when every vector in `vs` does. -/
theorem pr199_combineRows_length (n : Nat) (vs : List (List Bool)) (cs : List Bool)
    (hvs : ∀ v ∈ vs, v.length = n) :
    (combineRows n vs cs).length = n := by
  induction vs generalizing cs with
  | nil => simp [combineRows, List.length_replicate]
  | cons v vs ih =>
      cases cs with
      | nil => simp [combineRows, List.length_replicate]
      | cons c cs =>
          cases c with
          | true =>
              have hv : v.length = n := hvs v List.mem_cons_self
              have htail : (combineRows n vs cs).length = n :=
                ih cs (fun w hw => hvs w (List.mem_cons_of_mem _ hw))
              simp only [combineRows]
              exact pr199_xorVec_length n v (combineRows n vs cs) hv htail
          | false =>
              simp only [combineRows]
              exact ih cs (fun w hw => hvs w (List.mem_cons_of_mem _ hw))

/-- Block decomposition of `combineRows`: a coefficient list split along a
    split of the row list (with vectors zero-extended into the other block)
    combines blockwise. This is the I2 "block independence" step
    (`spec/OPERATIONAL_SEMANTICS.md` §4.7, `C-DIRECT-SUM`, I2 clause). -/
theorem pr199_combineRows_block_split (na nb : Nat)
    (xs ys : List (List Bool)) (cx cy : List Bool)
    (hcx : cx.length = xs.length) (hcy : cy.length = ys.length)
    (hxs : ∀ v ∈ xs, v.length = na) (hys : ∀ v ∈ ys, v.length = nb) :
    combineRows (na + nb)
      (xs.map (fun v => v ++ List.replicate nb false) ++
       ys.map (fun v => List.replicate na false ++ v))
      (cx ++ cy)
    = combineRows na xs cx ++ combineRows nb ys cy := by
  induction xs generalizing cx ys cy with
  | nil =>
      obtain rfl : cx = [] := List.eq_nil_of_length_eq_zero (by simpa using hcx)
      simp only [List.map_nil, List.nil_append, combineRows]
      induction ys generalizing cy with
      | nil =>
          obtain rfl : cy = [] := List.eq_nil_of_length_eq_zero (by simpa using hcy)
          simp [combineRows]
      | cons y ys ih2 =>
          cases cy with
          | nil => simp [List.length] at hcy
          | cons c cs =>
              have hcy' : cs.length = ys.length := by
                simp only [List.length] at hcy
                omega
              have hys' : ∀ v ∈ ys, v.length = nb :=
                fun v hv => hys v (List.mem_cons_of_mem _ hv)
              cases c with
              | true =>
                  simp only [List.map_cons, combineRows]
                  rw [ih2 cs hcy' hys']
                  rw [pr199_xorVec_append (List.replicate na false) y
                    (List.replicate na false) (combineRows nb ys cs) rfl]
                  rw [pr199_xorVec_false_left na (List.replicate na false)
                    List.length_replicate]
              | false =>
                  simp only [List.map_cons, combineRows]
                  rw [ih2 cs hcy' hys']
  | cons x xs ih =>
      cases cx with
      | nil => simp [List.length] at hcx
      | cons c cs =>
          have hcx' : cs.length = xs.length := by
            simp only [List.length] at hcx
            omega
          have hxs' : ∀ v ∈ xs, v.length = na :=
            fun v hv => hxs v (List.mem_cons_of_mem _ hv)
          simp only [List.map_cons, List.cons_append]
          have hlenA : x.length = (combineRows na xs cs).length := by
            rw [pr199_combineRows_length na xs cs hxs']
            exact hxs x List.mem_cons_self
          cases c with
          | true =>
              simp only [combineRows]
              rw [ih ys cs cy hcx' hcy hxs' hys]
              rw [pr199_xorVec_append x (List.replicate nb false)
                (combineRows na xs cs) (combineRows nb ys cy) hlenA]
              rw [pr199_xorVec_false_left nb (combineRows nb ys cy)
                (pr199_combineRows_length nb ys cy hys)]
          | false =>
              simp only [combineRows]
              rw [ih ys cs cy hcx' hcy hxs' hys]

/-- Map extensionality for lists. -/
theorem map_ext {α β : Type} {f g : α → β} (l : List α)
    (h : ∀ x ∈ l, f x = g x) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp [h x List.mem_cons_self,
        ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- `DisjointList` is symmetric. -/
theorem disjointList_symm {α : Type} [DecidableEq α] (xs ys : List α) :
    DisjointList xs ys → DisjointList ys xs := by
  intro h
  unfold DisjointList
  intro x hx hy
  exact h x hy hx

/-- The intersection size of two disjoint supports is zero: the I1
    cross-summand step (disjoint supports meet in zero qubits, hence in an
    even number). -/
theorem pr199_supportIntersectionSize_zero_of_disjoint (xs ys : List Nat)
    (h : DisjointList xs ys) :
    supportIntersectionSize xs ys = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx : ys.contains x = false := by
        cases hyc : ys.contains x with
        | false => rfl
        | true =>
            have : x ∈ ys := List.contains_iff_mem.mp hyc
            exact False.elim (h x (by simp) this)
      have hxs : DisjointList xs ys := fun q hq hy => h q (by simp [hq]) hy
      have hstep : supportIntersectionSize (x :: xs) ys = supportIntersectionSize xs ys := by
        unfold supportIntersectionSize
        have hxmem : x ∉ ys := h x (by simp)
        simp [hxmem]
      rw [hstep]
      exact ih hxs

/-- Cross-summand supports are disjoint when the qubit namespaces are. -/
theorem support_disjoint_of_disjoint_Q {a b : CodeState} {rA rB : Row}
    (hQ : DisjointList a.Q b.Q)
    (hsubA : ∀ q ∈ rA.support, q ∈ a.Q)
    (hsubB : ∀ q ∈ rB.support, q ∈ b.Q) :
    DisjointList rA.support rB.support := by
  intro q hqA hqB
  exact hQ q (hsubA q hqA) (hsubB q hqB)

/-- Well-formedness: a displayed row's support lies in `Q`. -/
theorem support_subset_of_wf {s : CodeState}
    (h : s.rows.all (fun r => r.support.all (fun q => s.Q.contains q)) = true)
    (r : Row) (hr : r ∈ s.rows) : ∀ q ∈ r.support, q ∈ s.Q := by
  have hrow : r.support.all (fun q => s.Q.contains q) = true :=
    List.all_eq_true.mp h r hr
  intro q hq
  exact List.contains_iff_mem.mp (List.all_eq_true.mp hrow q hq)

/-- Well-formedness: a displayed row's identifier is in `used`. -/
theorem rowId_in_used {s : CodeState}
    (h : (s.rows.map Row.id).all (fun id => s.used.contains id) = true)
    (r : Row) (hr : r ∈ s.rows) : r.id ∈ s.used := by
  have hall := List.all_eq_true.mp h r.id (List.mem_map_of_mem hr)
  exact List.contains_iff_mem.mp hall

/-- Unfold the independence premise carried by `IndependentGenerator`. -/
theorem not_inSpan_of_independentGenerator {s : CodeState} {r : Nat} {row : Row}
    (hfind : rowById s r = some row)
    (h : IndependentGenerator r s) :
    ¬ inSpanRows s.Q
      (s.rows.filter (fun r' => r'.sector = row.sector ∧ r'.id ≠ r))
      (rowVector s.Q row) := by
  unfold IndependentGenerator at h
  rw [hfind] at h
  exact h

/-- Build `IndependentGenerator` from its unfolded premise. -/
theorem independentGenerator_of_not_inSpan (s : CodeState) (r : Nat) (row : Row)
    (hfind : rowById s r = some row)
    (h : ¬ inSpanRows s.Q
      (s.rows.filter (fun r' => r'.sector = row.sector ∧ r'.id ≠ r))
      (rowVector s.Q row)) :
    IndependentGenerator r s := by
  unfold IndependentGenerator
  rw [hfind]
  exact h

/-- Every vector in the image of `rowVector Q` has length `Q.length`. -/
theorem rowVector_length_map {l : List Row} (Q : List Nat) :
    ∀ v ∈ l.map (rowVector Q), v.length = Q.length := by
  intro v hv
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
  exact pr199_rowVector_length Q p

/-- I1 (X/Z commutation) is preserved by a disjoint direct sum: cross-block
    supports are disjoint, so cross-block intersection sizes are zero and
    even; within-block commutation is inherited from the summands. -/
theorem directSum_I1 (a b : CodeState)
    (hWFa : EncodingWellFormed a) (hWFb : EncodingWellFormed b)
    (hQ : DisjointList a.Q b.Q) :
    I1 (directSumState a b) := by
  simp only [I1, directSumState]
  intro rX rZ hrX hrZ hsecX hsecZ
  rcases List.mem_append.mp hrX with hrXA | hrXB <;>
    rcases List.mem_append.mp hrZ with hrZA | hrZB
  · exact hWFa.2.2.2.2.2.2.1 rX rZ hrXA hrZA hsecX hsecZ
  · have hsubX := support_subset_of_wf hWFa.2.2.2.1 rX hrXA
    have hsubZ := support_subset_of_wf hWFb.2.2.2.1 rZ hrZB
    have hd := support_disjoint_of_disjoint_Q hQ hsubX hsubZ
    rw [pr199_supportIntersectionSize_zero_of_disjoint rX.support rZ.support hd]
  · have hsubX := support_subset_of_wf hWFb.2.2.2.1 rX hrXB
    have hsubZ := support_subset_of_wf hWFa.2.2.2.1 rZ hrZA
    have hd := support_disjoint_of_disjoint_Q
      (disjointList_symm a.Q b.Q hQ) hsubX hsubZ
    rw [pr199_supportIntersectionSize_zero_of_disjoint rX.support rZ.support hd]
  · exact hWFb.2.2.2.2.2.2.1 rX rZ hrXB hrZB hsecX hsecZ

/-- I2 (displayed independence) is preserved by a disjoint direct sum: a span
    certificate over the concatenated display splits along the row split
    (`pr199_combineRows_block_split`), so a certificate for a left-summand row would
    contradict its independence in the left summand, and symmetrically on the
    right. -/
theorem directSum_I2 (a b : CodeState)
    (hWFa : EncodingWellFormed a) (hWFb : EncodingWellFormed b)
    (hQ : DisjointList a.Q b.Q) (hU : DisjointList a.used b.used) :
    I2 (directSumState a b) := by
  simp only [I2, directSumState]
  intro r hr
  rcases List.mem_append.mp hr with hrA | hrB
  · -- the row is displayed in the left summand
    have hgen : IndependentGenerator r.id a := hWFa.2.2.2.2.2.2.2 r hrA
    cases hrow : rowById a r.id with
    | none =>
        unfold IndependentGenerator at hgen
        rw [hrow] at hgen
        exact False.elim hgen
    | some ra =>
        have hnotin : ¬ inSpanRows a.Q
            (a.rows.filter (fun r' => r'.sector = ra.sector ∧ r'.id ≠ r.id))
            (rowVector a.Q ra) :=
          not_inSpan_of_independentGenerator hrow hgen
        have hra : ra ∈ a.rows := List.mem_of_find?_eq_some
          (show a.rows.find? (fun row => row.id = r.id) = some ra from hrow)
        have hfindD : rowById (directSumState a b) r.id = some ra := by
          unfold rowById at hrow ⊢
          simp only [directSumState]
          rw [List.find?_append]
          simp [hrow]
        refine independentGenerator_of_not_inSpan _ _ _ hfindD ?_
        show ¬ inSpanRows (a.Q ++ b.Q)
          ((a.rows ++ b.rows).filter
            (fun r' => r'.sector = ra.sector ∧ r'.id ≠ r.id))
          (rowVector (a.Q ++ b.Q) ra)
        intro hspan
        unfold inSpanRows at hspan
        rcases hspan with ⟨coeffs, hlen, hcomb⟩
        have hpeers : (a.rows ++ b.rows).filter
            (fun r' => r'.sector = ra.sector ∧ r'.id ≠ r.id)
            = a.rows.filter (fun r' => r'.sector = ra.sector ∧ r'.id ≠ r.id)
              ++ b.rows.filter (fun r' => r'.sector = ra.sector ∧ r'.id ≠ r.id) :=
          List.filter_append a.rows b.rows
        rw [hpeers] at hlen hcomb
        rw [List.map_append] at hcomb
        simp only [List.length_append] at hlen
        have hmapL :
            (a.rows.filter (fun r' => r'.sector = ra.sector ∧ r'.id ≠ r.id)).map
                (rowVector (a.Q ++ b.Q))
            = ((a.rows.filter (fun r' => r'.sector = ra.sector ∧ r'.id ≠ r.id)).map
                (rowVector a.Q)).map
                (fun v => v ++ List.replicate b.Q.length false) := by
          rw [List.map_map]
          apply map_ext
          intro p hp
          exact pr199_rowVector_append_left a b p
            (support_subset_of_wf hWFa.2.2.2.1 p (List.mem_filter.mp hp).1) hQ
        rw [hmapL] at hcomb
        have hmapR :
            (b.rows.filter (fun r' => r'.sector = ra.sector ∧ r'.id ≠ r.id)).map
                (rowVector (a.Q ++ b.Q))
            = ((b.rows.filter (fun r' => r'.sector = ra.sector ∧ r'.id ≠ r.id)).map
                (rowVector b.Q)).map
                (fun v => List.replicate a.Q.length false ++ v) := by
          rw [List.map_map]
          apply map_ext
          intro p hp
          exact pr199_rowVector_append_right a b p
            (support_subset_of_wf hWFb.2.2.2.1 p (List.mem_filter.mp hp).1) hQ
        rw [hmapR] at hcomb
        simp only [List.length_append] at hcomb
        rw [← List.take_append_drop
          (a.rows.filter (fun r' => r'.sector = ra.sector ∧ r'.id ≠ r.id)).length
          coeffs] at hcomb
        have hsplit := pr199_combineRows_block_split a.Q.length b.Q.length
          ((a.rows.filter (fun r' => r'.sector = ra.sector ∧ r'.id ≠ r.id)).map
            (rowVector a.Q))
          ((b.rows.filter (fun r' => r'.sector = ra.sector ∧ r'.id ≠ r.id)).map
            (rowVector b.Q))
          (coeffs.take
            (a.rows.filter (fun r' => r'.sector = ra.sector ∧ r'.id ≠ r.id)).length)
          (coeffs.drop
            (a.rows.filter (fun r' => r'.sector = ra.sector ∧ r'.id ≠ r.id)).length)
          (by rw [List.length_take, List.length_map, hlen]; omega)
          (by rw [List.length_drop, List.length_map, hlen]; omega)
          (rowVector_length_map a.Q)
          (rowVector_length_map b.Q)
        rw [hsplit] at hcomb
        rw [pr199_rowVector_append_left a b ra
          (support_subset_of_wf hWFa.2.2.2.1 ra hra) hQ] at hcomb
        have hlenL :
            (combineRows a.Q.length
              ((a.rows.filter (fun r' => r'.sector = ra.sector ∧ r'.id ≠ r.id)).map
                (rowVector a.Q))
              (coeffs.take
                (a.rows.filter (fun r' => r'.sector = ra.sector ∧ r'.id ≠ r.id)).length)).length
            = a.Q.length :=
          pr199_combineRows_length a.Q.length _ _ (rowVector_length_map a.Q)
        have hparts := List.append_inj hcomb (by rw [hlenL, pr199_rowVector_length])
        exact hnotin ⟨coeffs.take
          (a.rows.filter (fun r' => r'.sector = ra.sector ∧ r'.id ≠ r.id)).length,
          (by rw [List.length_take, hlen]; omega), hparts.1⟩
  · -- the row is displayed in the right summand
    have hgen : IndependentGenerator r.id b := hWFb.2.2.2.2.2.2.2 r hrB
    cases hrow : rowById b r.id with
    | none =>
        unfold IndependentGenerator at hgen
        rw [hrow] at hgen
        exact False.elim hgen
    | some rb =>
        have hnotin : ¬ inSpanRows b.Q
            (b.rows.filter (fun r' => r'.sector = rb.sector ∧ r'.id ≠ r.id))
            (rowVector b.Q rb) :=
          not_inSpan_of_independentGenerator hrow hgen
        have hrb : rb ∈ b.rows := List.mem_of_find?_eq_some
          (show b.rows.find? (fun row => row.id = r.id) = some rb from hrow)
        have hnoneA : rowById a r.id = none := by
          cases hna : rowById a r.id with
          | some ra =>
              exfalso
              have hfind : a.rows.find? (fun row => row.id = r.id) = some ra := hna
              have hra : ra ∈ a.rows := List.mem_of_find?_eq_some hfind
              have hid : ra.id = r.id := by
                simpa using List.find?_some hfind
              have hau : ra.id ∈ a.used := rowId_in_used hWFa.2.2.1 ra hra
              have hbu : r.id ∈ b.used := rowId_in_used hWFb.2.2.1 r hrB
              rw [hid] at hau
              exact hU r.id hau hbu
          | none => rfl
        have hfindD : rowById (directSumState a b) r.id = some rb := by
          unfold rowById at hrow hnoneA ⊢
          simp only [directSumState]
          rw [List.find?_append]
          simp [hnoneA, hrow]
        refine independentGenerator_of_not_inSpan _ _ _ hfindD ?_
        show ¬ inSpanRows (a.Q ++ b.Q)
          ((a.rows ++ b.rows).filter
            (fun r' => r'.sector = rb.sector ∧ r'.id ≠ r.id))
          (rowVector (a.Q ++ b.Q) rb)
        intro hspan
        unfold inSpanRows at hspan
        rcases hspan with ⟨coeffs, hlen, hcomb⟩
        have hpeers : (a.rows ++ b.rows).filter
            (fun r' => r'.sector = rb.sector ∧ r'.id ≠ r.id)
            = a.rows.filter (fun r' => r'.sector = rb.sector ∧ r'.id ≠ r.id)
              ++ b.rows.filter (fun r' => r'.sector = rb.sector ∧ r'.id ≠ r.id) :=
          List.filter_append a.rows b.rows
        rw [hpeers] at hlen hcomb
        rw [List.map_append] at hcomb
        simp only [List.length_append] at hlen
        have hmapL :
            (a.rows.filter (fun r' => r'.sector = rb.sector ∧ r'.id ≠ r.id)).map
                (rowVector (a.Q ++ b.Q))
            = ((a.rows.filter (fun r' => r'.sector = rb.sector ∧ r'.id ≠ r.id)).map
                (rowVector a.Q)).map
                (fun v => v ++ List.replicate b.Q.length false) := by
          rw [List.map_map]
          apply map_ext
          intro p hp
          exact pr199_rowVector_append_left a b p
            (support_subset_of_wf hWFa.2.2.2.1 p (List.mem_filter.mp hp).1) hQ
        rw [hmapL] at hcomb
        have hmapR :
            (b.rows.filter (fun r' => r'.sector = rb.sector ∧ r'.id ≠ r.id)).map
                (rowVector (a.Q ++ b.Q))
            = ((b.rows.filter (fun r' => r'.sector = rb.sector ∧ r'.id ≠ r.id)).map
                (rowVector b.Q)).map
                (fun v => List.replicate a.Q.length false ++ v) := by
          rw [List.map_map]
          apply map_ext
          intro p hp
          exact pr199_rowVector_append_right a b p
            (support_subset_of_wf hWFb.2.2.2.1 p (List.mem_filter.mp hp).1) hQ
        rw [hmapR] at hcomb
        simp only [List.length_append] at hcomb
        rw [← List.take_append_drop
          (a.rows.filter (fun r' => r'.sector = rb.sector ∧ r'.id ≠ r.id)).length
          coeffs] at hcomb
        have hsplit := pr199_combineRows_block_split a.Q.length b.Q.length
          ((a.rows.filter (fun r' => r'.sector = rb.sector ∧ r'.id ≠ r.id)).map
            (rowVector a.Q))
          ((b.rows.filter (fun r' => r'.sector = rb.sector ∧ r'.id ≠ r.id)).map
            (rowVector b.Q))
          (coeffs.take
            (a.rows.filter (fun r' => r'.sector = rb.sector ∧ r'.id ≠ r.id)).length)
          (coeffs.drop
            (a.rows.filter (fun r' => r'.sector = rb.sector ∧ r'.id ≠ r.id)).length)
          (by rw [List.length_take, List.length_map, hlen]; omega)
          (by rw [List.length_drop, List.length_map, hlen]; omega)
          (rowVector_length_map a.Q)
          (rowVector_length_map b.Q)
        rw [hsplit] at hcomb
        rw [pr199_rowVector_append_right a b rb
          (support_subset_of_wf hWFb.2.2.2.1 rb hrb) hQ] at hcomb
        have hlenL :
            (combineRows a.Q.length
              ((a.rows.filter (fun r' => r'.sector = rb.sector ∧ r'.id ≠ r.id)).map
                (rowVector a.Q))
              (coeffs.take
                (a.rows.filter (fun r' => r'.sector = rb.sector ∧ r'.id ≠ r.id)).length)).length
            = a.Q.length :=
          pr199_combineRows_length a.Q.length _ _ (rowVector_length_map a.Q)
        have hparts := List.append_inj hcomb
          (by rw [hlenL, List.length_replicate])
        exact hnotin ⟨coeffs.drop
          (a.rows.filter (fun r' => r'.sector = rb.sector ∧ r'.id ≠ r.id)).length,
          (by rw [List.length_drop, hlen]; omega), hparts.2⟩

/-- I3 (identifier discipline) is preserved by a disjoint direct sum: row
    identifiers stay injective because `used` sets are disjoint, and every
    displayed identifier stays in the union of the `used` sets. -/
theorem directSum_I3 (a b : CodeState)
    (hWFa : EncodingWellFormed a) (hWFb : EncodingWellFormed b)
    (hU : DisjointList a.used b.used) : I3 (directSumState a b) := by
  simp only [I3, directSumState, List.map_append]
  refine ⟨?_, ?_⟩
  · apply List.nodup_append.mpr
    refine ⟨hWFa.2.1, hWFb.2.1, ?_⟩
    intro x hx y hy heq
    rcases List.mem_map.mp hx with ⟨ra, hra, rfl⟩
    rcases List.mem_map.mp hy with ⟨rb, hrb, rfl⟩
    -- `heq : ra.id = rb.id`
    have hbu := rowId_in_used hWFb.2.2.1 rb hrb
    rw [← heq] at hbu
    exact hU ra.id (rowId_in_used hWFa.2.2.1 ra hra) hbu
  · apply List.all_eq_true.mpr
    intro r hr
    rcases List.mem_append.mp hr with hra | hrb
    · exact List.contains_iff_mem.mpr
        (List.mem_append_left b.used (rowId_in_used hWFa.2.2.1 r hra))
    · exact List.contains_iff_mem.mpr
        (List.mem_append_right a.used (rowId_in_used hWFb.2.2.1 r hrb))

/-- I4 (sector typing) is preserved by a disjoint direct sum: it holds for
    every state (`i4_trivial`), so in particular for the sum. -/
theorem directSum_I4 (a b : CodeState) : I4 (directSumState a b) :=
  i4_trivial (directSumState a b)

/-- I5 (valid provenance) is preserved by a disjoint direct sum: it holds for
    every state (`i5_trivial`), so in particular for the sum. -/
theorem directSum_I5 (a b : CodeState) : I5 (directSumState a b) :=
  i5_trivial (directSumState a b)

/-- The `C-DIRECT-SUM` clause of `spec/OPERATIONAL_SEMANTICS.md` §4.7
    (`OBL-WELL-FORMEDNESS-PRESERVATION`): the sum of two well-formed states
    with disjoint qubit namespaces and disjoint `used` sets is well formed. -/
theorem directSum_wellFormed (a b : CodeState)
    (hWFa : EncodingWellFormed a) (hWFb : EncodingWellFormed b)
    (hQ : DisjointList a.Q b.Q) (hU : DisjointList a.used b.used) :
    EncodingWellFormed (directSumState a b) := by
  simp only [EncodingWellFormed, directSumState, List.map_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `Q` stays nodup
    apply List.nodup_append.mpr
    refine ⟨hWFa.1, hWFb.1, ?_⟩
    intro x hx y hy heq
    subst heq
    exact hQ _ hx hy
  · -- row identifiers stay nodup
    apply List.nodup_append.mpr
    refine ⟨hWFa.2.1, hWFb.2.1, ?_⟩
    intro x hx y hy heq
    rcases List.mem_map.mp hx with ⟨ra, hra, rfl⟩
    rcases List.mem_map.mp hy with ⟨rb, hrb, rfl⟩
    -- `heq : ra.id = rb.id`
    have hbu := rowId_in_used hWFb.2.2.1 rb hrb
    rw [← heq] at hbu
    exact hU ra.id (rowId_in_used hWFa.2.2.1 ra hra) hbu
  · -- every displayed identifier stays in `used`
    apply List.all_eq_true.mpr
    intro id hid
    rcases List.mem_append.mp hid with hida | hidb
    · obtain ⟨ra, hra, rfl⟩ := List.mem_map.mp hida
      exact List.contains_iff_mem.mpr
        (List.mem_append_left b.used (rowId_in_used hWFa.2.2.1 ra hra))
    · obtain ⟨rb, hrb, rfl⟩ := List.mem_map.mp hidb
      exact List.contains_iff_mem.mpr
        (List.mem_append_right a.used (rowId_in_used hWFb.2.2.1 rb hrb))
  · -- supports stay inside `Q`
    apply List.all_eq_true.mpr
    intro r hr
    rcases List.mem_append.mp hr with hra | hrb
    · apply List.all_eq_true.mpr
      intro q hq
      have hsub := support_subset_of_wf hWFa.2.2.2.1 r hra
      exact List.contains_iff_mem.mpr (List.mem_append_left b.Q (hsub q hq))
    · apply List.all_eq_true.mpr
      intro q hq
      have hsub := support_subset_of_wf hWFb.2.2.2.1 r hrb
      exact List.contains_iff_mem.mpr (List.mem_append_right a.Q (hsub q hq))
  · -- supports stay duplicate-free
    apply List.all_eq_true.mpr
    intro r hr
    rcases List.mem_append.mp hr with hra | hrb
    · exact List.all_eq_true.mp hWFa.2.2.2.2.1 r hra
    · exact List.all_eq_true.mp hWFb.2.2.2.2.1 r hrb
  · -- supports stay sorted
    apply List.all_eq_true.mpr
    intro r hr
    rcases List.mem_append.mp hr with hra | hrb
    · exact List.all_eq_true.mp hWFa.2.2.2.2.2.1 r hra
    · exact List.all_eq_true.mp hWFb.2.2.2.2.2.1 r hrb
  · exact directSum_I1 a b hWFa hWFb hQ
  · exact directSum_I2 a b hWFa hWFb hQ hU



end CodeCalculus
