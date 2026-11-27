import CodeCalculus.TermSoundness
import CodeCalculus.SeamChains
import CodeCalculus.Gate6Exact
import CodeCalculus.AdmissibleSeamFamily
import CodeCalculus.RebaseWellFormedness
import CodeCalculus.ConstructorAssembly
import CodeCalculus.ConstructorOverlap
import CodeCalculus.ConcatRetention
import CodeCalculus.BalancedOverlap
import CodeCalculus.ConstructorRankNatural

namespace CodeCalculus

/-!
# Annotated-term soundness over the expanded operation set (Item 10)

Completes the Lean mechanization of `spec/OPERATIONAL_SEMANTICS.md` §4.11
(`OBL-JUDGMENT-SOUNDNESS`) across the expanded operation set:

* **All ten `Command` constructors:** the kernel commands (`skip`, `delete`,
  `addStab`, `seq`), the admitted conditional graft (`graft`), and all five
  unary Gate 6 CSS-level extensions (`rebase`, `hadamard`, `peel`, `puncture`,
  `extend`).
* **All thirteen `StateExpr` constructors:** `base`, `C-DIRECT-SUM`, `E-GLUE`,
  and the ten admitted typed constructors (`hgp`, `lift`, `twoblock`, `concat`,
  `product`, `double`, `balanced`, `tanner`, `tile`, `nested`).
* **Extended-natural distance domain (`ExtNat = ℕ ∪ {+∞}`):** `Soundness.lean`
  keeps its `Nat`-valued distance measure (with sentinel `|Q| + 1`) because its
  distance rows only compare states on one fixed namespace. Over
  the expanded operation set, `E-GRAFT`, `E-PEEL`, `C-DIRECT-SUM`, and `E-GLUE`
  relate states of different namespace sizes `|Q|`, where a `|Q| + 1` sentinel
  is not order-faithful at `k = 0` (`+∞`). Lifting the sentence language to
  `Option ExtNat` separates out-of-bounds chain positions (`none`) from `+∞`
  (`some ExtNat.inf`), makes `minOf` strict in `none` (eliminating the chain
  non-monotonicity recorded in `Soundness.lean`), and lets every distance law
  of the expanded operation set discharge unconditionally for `exactExtMeasure`.
* **Exact-distance discharge:** `ExtMeasureLaws` collects all nine distance
  laws of the expanded operation set (`delete`, `addStab`, `graft`, `rebase`,
  `hadamard`, `peel`, `extend` with `Δ = ∅`, `directSum`, and the uncertified
  `E-GLUE` lower bound). `extMeasureLaws_exact` discharges every one of them
  for `exactExtMeasure` (reading `exactDistanceExt`), leaving no distance
  hypothesis. `E-PUNCTURE` (§4.29), `E-EXTEND` with `Δ ≠ ∅` (§4.30), and the
  ten typed constructors (§2g) deliberately have no distance instantiation rows.
* **Seam-certificate equality handling (`spec/JUDGMENT_LAYER.md` §2e):**
  `E-GLUE`'s certified equality `d_Z(glue) = min(d_Z(A), d_Z(B))` is governed
  by an explicit cell policy `seamCert` whose soundness hypothesis is
  `SeamCertSound dMeasure seamCert`.
  - For an arbitrary external/geometric seam certificate (such as §2e's planar
    move-word equality `w(c_A) = w(c_B)` over `{U,D,L,R}^*`, which lives
    outside `CodeState` because states carry no planar layout or move words),
    `SeamCertSound` is explicitly retained as the cell hypothesis.
  - For the uncertified policy (`fun _ _ _ => False`), `seamCertSound_none`
    discharges it trivially, yielding `ext_judgment_soundness_of_term_exact_uncertified`
    with zero distance or certificate hypotheses.
  - For the survival-based policy `AdmissibleSeam · · · Sector.Z`
    (`AdmissibleSeamFamily.lean`), `seamCertSound_admissibleSeam` proves
    `SeamCertSound exactExtMeasure` unconditionally across all finite and `+∞`
    cases, yielding `ext_judgment_soundness_of_term_exact_admissible` with zero
    remaining distance or certificate hypotheses.

* **Two derivation systems.** `Soundness.lean` / `TermSoundness.lean`
  mechanize §4.11 over the kernel commands on a fixed namespace with a
  `Nat`-valued distance (sentinel `|Q| + 1`); they are retained because their
  distance rows compare states of one namespace and their transport lemmas are
  stated over that reading. `ExpandedSoundness.lean` is the mechanization of
  §4.11 over the expanded operation set (`ExtDerives` over
  `ExtNat = ℕ ∪ {+∞}`), covering cross-namespace rows and the `+∞` value.
  No formal translation theorem between the two is mechanized; the kernel
  rows of `Derives` correspond row-for-row to the kernel rows of
  `ExtDerives`.

The main closed-term models predicate is `TermModels dMeasure term t a`: it
packages `EvalExpr term.expr init`, `Trace term.command init trace t`, and
`ExtAnnTrue dMeasure (init :: trace) a`, with `init` and `trace` uniquely
determined by `term` (`TermModels.unique_trace`). The soundness metatheorems
(`ext_judgment_soundness`, `ext_judgment_soundness_of_eval`,
`ext_judgment_soundness_of_term`, and their `_exact`, `_exact_uncertified`,
and `_exact_admissible` instances) depend only on `propext` and `Quot.sound`
(no `sorry`, no `Classical.choice`, no new axioms).
-/

/-! ## Section 1: Extended-natural arithmetic, order, and `Option Nat` bridge -/

/-- Addition on `ExtNat = ℕ ∪ {+∞}`, absorbing `+∞`. -/
def ExtNat.add : ExtNat → ExtNat → ExtNat
  | .finite a, .finite b => .finite (a + b)
  | _, .inf => .inf
  | .inf, _ => .inf

/-- Truncated subtraction on `ExtNat = ℕ ∪ {+∞}`: `+∞ - n = +∞` (matching
    `predOpt` for `E-PEEL` when `n = 1`), and `x - +∞ = 0`. -/
def ExtNat.sub : ExtNat → ExtNat → ExtNat
  | .finite a, .finite b => .finite (a - b)
  | .inf, .finite _ => .inf
  | _, .inf => .finite 0

theorem ExtNat.le_refl (a : ExtNat) : a ≤ a := by
  cases a with
  | finite n => exact Nat.le_refl n
  | inf => trivial

theorem ExtNat.le_inf (a : ExtNat) : a ≤ ExtNat.inf := by
  cases a <;> trivial

theorem ExtNat.le_trans {a b c : ExtNat} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  cases a with
  | finite na =>
      cases b with
      | finite nb =>
          cases c with
          | finite nc => exact Nat.le_trans h1 h2
          | inf => trivial
      | inf =>
          cases c with
          | finite _ => exact False.elim h2
          | inf => trivial
  | inf =>
      cases b with
      | finite _ => exact False.elim h1
      | inf => exact h2

theorem ExtNat.le_antisymm {a b : ExtNat} (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  cases a with
  | finite na =>
      cases b with
      | finite nb => exact congrArg ExtNat.finite (Nat.le_antisymm h1 h2)
      | inf => exact False.elim h2
  | inf =>
      cases b with
      | finite _ => exact False.elim h1
      | inf => rfl

theorem ExtNat.min_comm (a b : ExtNat) : ExtNat.min a b = ExtNat.min b a := by
  cases a <;> cases b <;> simp [ExtNat.min, Nat.min_comm]

theorem ExtNat.le_min {t a b : ExtNat} (h1 : t ≤ a) (h2 : t ≤ b) :
    t ≤ ExtNat.min a b := by
  cases t with
  | finite nt =>
      cases a with
      | finite na =>
          cases b with
          | finite nb => exact Nat.le_min.mpr ⟨h1, h2⟩
          | inf => exact h1
      | inf =>
          cases b with
          | finite nb => exact h2
          | inf => trivial
  | inf =>
      cases a with
      | finite _ => exact False.elim h1
      | inf =>
          cases b with
          | finite _ => exact False.elim h2
          | inf => trivial

theorem ExtNat.min_monotone {a a' b b' : ExtNat} (ha : a ≤ a') (hb : b ≤ b') :
    ExtNat.min a b ≤ ExtNat.min a' b' :=
  ExtNat.le_min
    (ExtNat.le_trans (ExtNat.min_le_left a b) ha)
    (ExtNat.le_trans (ExtNat.min_le_right a b) hb)

theorem ExtNat.sub_one_le (a : ExtNat) : ExtNat.sub a (ExtNat.finite 1) ≤ a := by
  cases a with
  | finite n => show n - 1 ≤ n; omega
  | inf => trivial

/-- `min(a, b) - 1 ≤ min(a', b')` when `a ≤ a'` and `b - 1 ≤ b'`
    (the full-distance lower bound of `E-PEEL`, §4.28). -/
theorem ExtNat.sub_one_min_le {a b a' b' : ExtNat}
    (ha : a ≤ a') (hb : ExtNat.sub b (ExtNat.finite 1) ≤ b') :
    ExtNat.sub (ExtNat.min a b) (ExtNat.finite 1) ≤ ExtNat.min a' b' := by
  have hsub_mono : ∀ x y : ExtNat, x ≤ y →
      ExtNat.sub x (ExtNat.finite 1) ≤ ExtNat.sub y (ExtNat.finite 1) := by
    intro x y hxy
    cases x with
    | finite nx =>
        cases y with
        | finite ny => show nx - 1 ≤ ny - 1; have : nx ≤ ny := hxy; omega
        | inf => trivial
    | inf =>
        cases y with
        | finite _ => exact False.elim hxy
        | inf => trivial
  exact ExtNat.le_min
    (ExtNat.le_trans (ExtNat.le_trans (ExtNat.sub_one_le _) (ExtNat.min_le_left a b)) ha)
    (ExtNat.le_trans (hsub_mono _ _ (ExtNat.min_le_right a b)) hb)

theorem extNat_le_of_leOpt {a b : Option Nat} (h : leOpt a b) :
    ExtNat.ofOption a ≤ ExtNat.ofOption b := by
  cases a with
  | none =>
      cases b with
      | none => trivial
      | some _ => exact False.elim h
  | some na =>
      cases b with
      | none => trivial
      | some nb => exact h

theorem extNat_ofOption_minOpt (a b : Option Nat) :
    ExtNat.ofOption (minOpt a b) = ExtNat.min (ExtNat.ofOption a) (ExtNat.ofOption b) := by
  cases a <;> cases b <;> rfl

theorem extNat_ofOption_predOpt (a : Option Nat) :
    ExtNat.ofOption (predOpt a) = ExtNat.sub (ExtNat.ofOption a) (ExtNat.finite 1) := by
  cases a <;> rfl

theorem extNat_ofOption_exactDist_x (s : CodeState) :
    ExtNat.ofOption (exactDist s).x = exactDistanceExt Sector.X s := by
  show ExtNat.ofOption (exactDistOpt Sector.X s) = ExtNat.ofOption (exactDistance? Sector.X s)
  rw [exactDistOpt_eq_exactDistance?]

theorem extNat_ofOption_exactDist_z (s : CodeState) :
    ExtNat.ofOption (exactDist s).z = exactDistanceExt Sector.Z s := by
  show ExtNat.ofOption (exactDistOpt Sector.Z s) = ExtNat.ofOption (exactDistance? Sector.Z s)
  rw [exactDistOpt_eq_exactDistance?]

/-! ## Section 2: Structural `n`, `k`, determinism, and `EvalExpr` well-formedness -/

/-- Exact additive `k` identity on any well-formed state:
    `k + |rows| = |Q|`. -/
theorem stateK_add_rows_length (s : CodeState) (hwf : EncodingWellFormed s) :
    stateK s + s.rows.length = s.Q.length := by
  have hk := stateK_of_wf_rows s hwf
  have hfit := ranksFit_of_wf s hwf
  obtain ⟨hQ, hids, _, _, _, _, _, hI2⟩ := hwf
  have hrx := sectorRank_eq_length_of_I2 s hQ hids hI2 Sector.X
  have hrz := sectorRank_eq_length_of_I2 s hQ hids hI2 Sector.Z
  have hsum := length_sectorRows_add s
  unfold RanksFit at hfit
  rw [hrx, hrz] at hfit
  omega

/-- Direct sum `k` additivity (§4.4): for well-formed disjoint summands,
    `k(A ⊕ B) = k(A) + k(B)`. -/
theorem stateK_directSum {a b : CodeState}
    (hwfA : EncodingWellFormed a) (hwfB : EncodingWellFormed b)
    (hQ : DisjointList a.Q b.Q) (hU : DisjointList a.used b.used) :
    stateK (directSumState a b) = stateK a + stateK b := by
  have hwfS : EncodingWellFormed (directSumState a b) :=
    directSum_wellFormed a b hwfA hwfB hQ hU
  have hA := stateK_add_rows_length a hwfA
  have hB := stateK_add_rows_length b hwfB
  have hS := stateK_add_rows_length (directSumState a b) hwfS
  have hlenQ : (directSumState a b).Q.length = a.Q.length + b.Q.length :=
    List.length_append
  have hlenR : (directSumState a b).rows.length = a.rows.length + b.rows.length :=
    List.length_append
  omega

/-- `E-GLUE` namespace count: `n(glue(A, B; seams)) = n(A) + n(B)`. -/
theorem glueState_Q_length (a b : CodeState) (seams : List (Sector × List Nat)) :
    (glueState a b seams).Q.length = a.Q.length + b.Q.length :=
  List.length_append

/-- `E-GLUE` row count: `|rows(glue)| = |rows(A)| + |rows(B)| + |seams|`. -/
theorem glueState_rows_length (a b : CodeState) (seams : List (Sector × List Nat)) :
    (glueState a b seams).rows.length = a.rows.length + b.rows.length + seams.length := by
  unfold glueState
  simp only [List.length_append, List.length_map, List.length_zip, mintFresh_length, Nat.min_self]

/-- `E-GLUE` logical-dimension bookkeeping: for well-formed factors and a
    well-formed glued state, `k(glue) + |seams| = k(A) + k(B)`. -/
theorem stateK_glueState {a b : CodeState} {seams : List (Sector × List Nat)}
    (hwfA : EncodingWellFormed a) (hwfB : EncodingWellFormed b)
    (hwfG : EncodingWellFormed (glueState a b seams)) :
    stateK (glueState a b seams) + seams.length = stateK a + stateK b := by
  have hA := stateK_add_rows_length a hwfA
  have hB := stateK_add_rows_length b hwfB
  have hG := stateK_add_rows_length (glueState a b seams) hwfG
  rw [glueState_Q_length, glueState_rows_length] at hG
  omega

/-- Filtering a row list by `row.id ≠ r_id` drops exactly one row when row
    identifiers are duplicate-free and `r_id` is displayed. -/
theorem length_filter_row_id_ne (r_id : Nat) (rows : List Row)
    (hnd : (rows.map Row.id).Nodup) (hex : ∃ row ∈ rows, row.id = r_id) :
    (rows.filter (fun row => row.id ≠ r_id)).length + 1 = rows.length := by
  obtain ⟨r, hr, he⟩ := hex
  have hmem : r_id ∈ rows.map Row.id := List.mem_map.mpr ⟨r, hr, he⟩
  have h := length_filter_ne_of_nodup_mem hnd hmem
  rw [List.filter_map, List.length_map, List.length_map] at h
  have h2 : (rows.filter (fun row => row.id ≠ r_id)).length = rows.length - 1 := h
  have h3 : 0 < rows.length := List.length_pos_of_mem hr
  omega

/-- Complementary boolean filters partition list length. -/
theorem length_filter_add_not {α : Type} (p : α → Bool) :
    ∀ xs : List α,
      (xs.filter (fun x => !p x)).length + (xs.filter p).length = xs.length
  | [] => rfl
  | x :: xs => by
      have ih := length_filter_add_not p xs
      cases hx : p x with
      | true =>
          rw [List.filter_cons_of_neg (by simp [hx]),
            List.filter_cons_of_pos hx, List.length_cons, List.length_cons]
          omega
      | false =>
          rw [List.filter_cons_of_pos (by simp [hx]),
            List.filter_cons_of_neg (by simp [hx]), List.length_cons, List.length_cons]
          omega

/-- `P-REBASE` preserves `n`. -/
theorem eval_rebase_n {σ : Sector} {M : List (List Nat)} {s t : CodeState}
    (h : Eval (Command.rebase σ M) s t) : t.Q.length = s.Q.length := by
  rw [eval_rebase_eq h]
  rfl

/-- `P-REBASE` preserves `k` (§4.26). -/
theorem eval_rebase_k {σ : Sector} {M : List (List Nat)} {s t : CodeState}
    (h : Eval (Command.rebase σ M) s t) : stateK t = stateK s := by
  cases h with
  | rebase _ hok hs' _ _ =>
      rw [hs']
      exact stateK_rebaseState s σ M hok

/-- `E-LOCAL-HADAMARD` preserves `n` (§4.27). -/
theorem eval_hadamard_n {T : List Nat} {s t : CodeState}
    (h : Eval (Command.hadamard T) s t) : t.Q.length = s.Q.length := by
  rcases eval_hadamard_cases h with ⟨hg, hst⟩ | ⟨_, _, hst, _⟩
  · rw [hst]
    unfold hadamardState
    split <;> rfl
  · rw [hst]
    rfl

/-- `E-LOCAL-HADAMARD` preserves `k` (§4.27). -/
theorem eval_hadamard_k {T : List Nat} {s t : CodeState}
    (h : Eval (Command.hadamard T) s t) : stateK t = stateK s := by
  rcases eval_hadamard_cases h with ⟨hg, hst⟩ | ⟨_, _, _, hk⟩
  · rw [hst]
    unfold hadamardState
    split
    · rfl
    · exact stateK_swap s
  · exact hk

/-- `E-PEEL` preserves `k` (§4.28): `k' = k` exactly, from the well-formedness
    of input and output and the unique retirement of `r_id` and `q`. -/
theorem eval_peel_k {q : Nat} {τ : Sector} {r_id : Nat} {s t : CodeState}
    (h : Eval (Command.peel q τ r_id) s t) (hwf : EncodingWellFormed s) :
    stateK t = stateK s := by
  cases h with
  | peel hq hrow _ _ hs' hwf' =>
      subst hs'
      have hQ : (peelState s q r_id).Q.length + 1 = s.Q.length :=
        length_filter_neq q s.Q hwf.1 hq
      have hR : (peelState s q r_id).rows.length + 1 = s.rows.length := by
        show ((s.rows.filter (fun row => row.id ≠ r_id)).map (shortenRow q)).length + 1 =
          s.rows.length
        rw [List.length_map]
        rcases hrow with ⟨row, hmem, hid, _, _⟩
        exact length_filter_row_id_ne r_id s.rows hwf.2.1 ⟨row, hmem, hid⟩
      have hs := stateK_add_rows_length s hwf
      have ht := stateK_add_rows_length (peelState s q r_id) hwf'
      have hs' : stateK s = s.Q.length - s.rows.length := Nat.eq_sub_of_add_eq hs
      have ht' : stateK (peelState s q r_id) =
          (peelState s q r_id).Q.length - (peelState s q r_id).rows.length :=
        Nat.eq_sub_of_add_eq ht
      rw [ht', hs', ← hQ, ← hR]
      exact (Nat.succ_sub_succ (peelState s q r_id).Q.length
        (peelState s q r_id).rows.length).symm

/-- The number of displayed rows deleted by `E-PUNCTURE` at `q`:
    `t_X + t_Z` of `spec/OPERATIONAL_SEMANTICS.md` §4.29. -/
def punctureDeletedCount (s : CodeState) (q : Nat) : Nat :=
  (s.rows.filter (fun row => row.support.contains q)).length

theorem punctureDeletedCount_eq_sectors (s : CodeState) (q : Nat) :
    punctureDeletedCount s q =
      (touchingRows s Sector.X q).length + (touchingRows s Sector.Z q).length := by
  unfold punctureDeletedCount touchingRows
  induction s.rows with
  | nil => rfl
  | cons r rs ih =>
      cases hq : r.support.contains q with
      | false =>
          simp only [List.filter_cons, hq, Bool.false_eq_true, and_false, decide_false,
            ↓reduceIte]
          exact ih
      | true =>
          cases hs : r.sector with
          | X =>
              simp only [List.filter_cons, hq, hs, and_self, decide_true, ↓reduceIte,
                reduceCtorEq, false_and, decide_false, List.length_cons]
              omega
          | Z =>
              simp only [List.filter_cons, hq, hs, and_self, decide_true, ↓reduceIte,
                reduceCtorEq, false_and, decide_false, List.length_cons]
              omega

/-- `E-PUNCTURE` decreases `n` by one (§4.29). -/
theorem eval_puncture_n {q : Nat} {s t : CodeState}
    (h : Eval (Command.puncture q) s t) (hwf : EncodingWellFormed s) :
    t.Q.length = s.Q.length - 1 := by
  cases h with
  | puncture hq hs' _ =>
      subst hs'
      have hlen := length_filter_neq q s.Q hwf.1 hq
      show (s.Q.filter (fun qa => qa ≠ q)).length = s.Q.length - 1
      omega

/-- `E-PUNCTURE` exact `k` bookkeeping (§4.29): `k' + 1 = k + t_X + t_Z`. -/
theorem eval_puncture_k {q : Nat} {s t : CodeState}
    (h : Eval (Command.puncture q) s t) (hwf : EncodingWellFormed s) :
    stateK t + 1 = stateK s + punctureDeletedCount s q := by
  cases h with
  | puncture hq hs' hwf' =>
      subst hs'
      have hQ : (punctureState s q).Q.length + 1 = s.Q.length :=
        length_filter_neq q s.Q hwf.1 hq
      have hR : (punctureState s q).rows.length + punctureDeletedCount s q = s.rows.length := by
        unfold punctureState punctureDeletedCount
        have hpart := length_filter_add_not (fun row : Row => row.support.contains q) s.rows
        have heq : s.rows.filter (fun row => decide (¬ row.support.contains q = true)) =
            s.rows.filter (fun row => !row.support.contains q) := by
          apply List.filter_congr
          intro row _
          cases row.support.contains q <;> rfl
        rw [heq]
        exact hpart
      have hs := stateK_add_rows_length s hwf
      have ht := stateK_add_rows_length (punctureState s q) hwf'
      omega

/-- `E-EXTEND` increases `n` by `|Δ|` (§4.30). -/
theorem eval_extend_n {delta : List Nat} {adds : List (Sector × List Nat)}
    {s t : CodeState} (h : Eval (Command.extend delta adds) s t)
    (hwf : EncodingWellFormed s) :
    t.Q.length = s.Q.length + delta.length := by
  cases h with
  | extend hok hs' _ _ =>
      subst hs'
      obtain ⟨hdisj, hndDelta, _, _⟩ := hok
      have hndApp : (s.Q ++ delta).Nodup := by
        rw [List.nodup_append]
        refine ⟨hwf.1, hndDelta, fun x hx y hy hxy => ?_⟩
        subst hxy
        exact hdisj x hy (List.contains_iff_mem.mpr hx)
      show (sortNat ((s.Q ++ delta).eraseDups)).length = s.Q.length + delta.length
      rw [eraseDups_of_nodup _ hndApp, (sortNat_perm _).length_eq, List.length_append]

/-- `E-EXTEND` exact `k` bookkeeping (§4.30): `k' + |adds| = k + |Δ|`. -/
theorem eval_extend_k {delta : List Nat} {adds : List (Sector × List Nat)}
    {s t : CodeState} (h : Eval (Command.extend delta adds) s t)
    (hwf : EncodingWellFormed s) :
    stateK t + adds.length = stateK s + delta.length := by
  have hQ := eval_extend_n h hwf
  cases h with
  | extend _ hs' hwf' _ =>
      subst hs'
      have hR : (extendState s delta adds).rows.length = s.rows.length + adds.length := by
        unfold extendState extendMintedRows
        simp only [List.length_append, List.length_map, List.length_zip, mintFresh_length,
          Nat.min_self]
      have hs := stateK_add_rows_length s hwf
      have ht := stateK_add_rows_length (extendState s delta adds) hwf'
      omega

/-- `C-COLUMN-CNOT` preserves `n` (§4.42). -/
theorem eval_cnotSwap_n {U : List (List Bool)} {s t : CodeState}
    (h : Eval (Command.cnotSwap U) s t) : t.Q.length = s.Q.length := by
  rw [eval_cnotSwap_eq h]
  rfl

/-- `C-COLUMN-CNOT` preserves `k` (§4.42): `Q` and displayed row count are
    unchanged, and both input and output states are well-formed (relying on
    the `EncodingWellFormed s'` premise carried by `Eval.cnotSwap`). -/
theorem eval_cnotSwap_k {U : List (List Bool)} {s t : CodeState}
    (h : Eval (Command.cnotSwap U) s t) (hwf : EncodingWellFormed s) :
    stateK t = stateK s := by
  cases h with
  | cnotSwap _ hs' hwf' =>
      subst hs'
      have hQ : (cnotSwapState s U).Q.length = s.Q.length := rfl
      have hR : (cnotSwapState s U).rows.length = s.rows.length := by
        show (s.rows.map (cnotSwapRow s.Q U)).length = s.rows.length
        exact List.length_map _
      have hs := stateK_add_rows_length s hwf
      have ht := stateK_add_rows_length (cnotSwapState s U) hwf'
      omega

/-- `E-SPLIT` preserves `n` (§4.48). -/
theorem eval_split_n {QA R : List Nat} {s t : CodeState}
    (h : Eval (Command.split QA R) s t) : t.Q.length = s.Q.length := by
  rw [eval_split_eq h, deleteAll_Q]

/-- Iterated `k` increase for `deleteAll` on distinct displayed rows of a
    well-formed state (§4.48): `k' = k + |R|`. -/
theorem stateK_deleteAll (R : List Nat) :
    ∀ {s : CodeState}, EncodingWellFormed s → R.Nodup →
      (∀ r ∈ R, DisplayedGenerator r s) →
      stateK (deleteAll s R) = stateK s + R.length := by
  induction R with
  | nil =>
      intro s _ _ _
      rfl
  | cons r rest ih =>
      intro s hwf hnd hdisp
      obtain ⟨row, hmem, hid⟩ := hdisp r List.mem_cons_self
      have hind : IndependentGenerator r s := hid ▸ hwf.2.2.2.2.2.2.2 row hmem
      have h1 : Eval (Command.delete r) s (deleteState s r) :=
        Eval.delete ⟨row, hmem, hid⟩ hind rfl
      have hk1 := stateK_delete_of_eval h1 hwf (ranksFit_of_wf s hwf)
      have hnd' := List.nodup_cons.mp hnd
      have hk2 := ih (wf_deleteState s r hwf) hnd'.2 (fun r' hr' => by
        obtain ⟨row', hmem', hid'⟩ := hdisp r' (List.mem_cons_of_mem _ hr')
        refine ⟨row', ?_, hid'⟩
        show row' ∈ s.rows.filter (fun row => row.id ≠ r)
        exact List.mem_filter.mpr ⟨hmem', decide_eq_true (fun h =>
          hnd'.1 (by rw [← h, hid']; exact hr'))⟩)
      show stateK (deleteAll (deleteState s r) rest) = stateK s + (r :: rest).length
      rw [hk2, hk1, List.length_cons]
      omega

/-- `E-SPLIT` exact `k` bookkeeping (§4.48): `k' = k + |R|`. -/
theorem eval_split_k {QA R : List Nat} {s t : CodeState}
    (h : Eval (Command.split QA R) s t) (hwf : EncodingWellFormed s) :
    stateK t = stateK s + R.length := by
  cases h with
  | split _ _ hRnd hRdisp _ hs' =>
      subst hs'
      exact stateK_deleteAll R hwf hRnd hRdisp

/-- Determinism of `EvalExpr` across all thirteen state-expression constructors,
    choice-free (no `Classical.choice`). -/
def exprSize : StateExpr → Nat
  | .base _ => 1
  | .directSum e1 e2 => 1 + exprSize e1 + exprSize e2
  | .glue e1 e2 _ => 1 + exprSize e1 + exprSize e2
  | .concat eO eI _ _ _ => 1 + exprSize eO + exprSize eI
  | .product eA eB => 1 + exprSize eA + exprSize eB
  | .double e _ _ => 1 + exprSize e
  | .hgp _ _ => 1
  | .lift _ _ _ => 1
  | .twoblock _ _ _ => 1
  | .balanced _ _ _ _ _ _ _ => 1
  | .tanner _ _ _ _ _ => 1
  | .tile _ _ _ _ => 1
  | .nested _ _ => 1
  | .cone _ _ _ _ => 1
  | .empty => 1
  | .free _ => 1
  | .pullback e1 e2 eI _ _ => 1 + exprSize e1 + exprSize e2 + exprSize eI
  | .pushout e1 e2 eS _ _ => 1 + exprSize e1 + exprSize e2 + exprSize eS
  | .liftTable _ _ _ => 1
  | .twoblockTable _ _ _ => 1
  | .balancedTable _ _ _ _ _ _ _ => 1
  | .pairPartition _ _ _ => 1
  | .ppScale e0 _ _ _ => 1 + exprSize e0

theorem evalExpr_unique {e : StateExpr} {s1 s2 : CodeState}
    (h1 : EvalExpr e s1) (h2 : EvalExpr e s2) : s1 = s2 := by
  induction h1 generalizing s2 with
  | base _ => cases h2; rfl
  | directSum _ _ _ _ ih1 ih2 =>
      cases h2 with
      | directSum _ _ h2a h2b =>
          rw [ih1 h2a, ih2 h2b]
  | glue _ _ _ _ _ _ ih1 ih2 =>
      cases h2 with
      | glue _ _ _ _ h2a h2b =>
          rw [ih1 h2a, ih2 h2b]
  | hgp _ _ _ => cases h2; rfl
  | lift _ _ _ _ => cases h2; rfl
  | twoblock _ _ _ _ => cases h2; rfl
  | concat _ _ _ _ _ _ ih1 ih2 =>
      cases h2 with
      | concat _ _ _ _ h2a h2b =>
          rw [ih1 h2a, ih2 h2b]
  | product _ _ _ _ _ ih1 ih2 =>
      cases h2 with
      | product _ _ _ h2a h2b =>
          rw [ih1 h2a, ih2 h2b]
  | double _ _ _ _ _ ih =>
      cases h2 with
      | double _ _ _ _ h2a =>
          rw [ih h2a]
  | balanced _ _ => cases h2; rfl
  | tanner _ _ _ => cases h2; rfl
  | tile _ _ _ => cases h2; rfl
  | nested _ _ _ => cases h2; rfl
  | cone _ _ _ => cases h2; rfl
  | empty => cases h2; rfl
  | free _ => cases h2; rfl
  | pullback _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 ih3 =>
      cases h2 with
      | pullback _ _ _ _ _ _ _ _ h2a h2b h2c =>
          rw [ih1 h2a, ih2 h2b]
  | pushout _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 ih3 =>
      cases h2 with
      | pushout _ _ _ _ _ _ _ _ h2a h2b h2c =>
          rw [ih1 h2a, ih2 h2b, ih3 h2c]
  | liftTable _ _ _ _ => cases h2; rfl
  | twoblockTable _ _ _ _ => cases h2; rfl
  | balancedTable _ _ => cases h2; rfl
  | pairPartition _ _ _ => cases h2; rfl
  | ppScale _ _ _ _ _ ih0 =>
      cases h2 with
      | ppScale _ _ _ _ h2a =>
          rw [ih0 h2a]

/-- Determinism of `EvalTerm`: a closed term evaluates to at most one state. -/
theorem evalTerm_unique {term : ClosedTerm} {t1 t2 : CodeState}
    (h1 : EvalTerm term t1) (h2 : EvalTerm term t2) : t1 = t2 := by
  cases h1 with
  | eval he1 hc1 =>
      cases h2 with
      | eval he2 hc2 =>
          have hs := evalExpr_unique he1 he2
          subst hs
          exact eval_unique hc1 hc2

/-- Every `StateExpr.base` embedded inside a state expression is well-formed
    (FD1's input-state hypothesis lifted to arbitrary `StateExpr`; vacuous for
    nullary constructor expressions). -/
def ExprBaseWF : StateExpr → Prop
  | .base s => EncodingWellFormed s
  | .directSum e1 e2 => ExprBaseWF e1 ∧ ExprBaseWF e2
  | .glue e1 e2 _ => ExprBaseWF e1 ∧ ExprBaseWF e2
  | .concat eO eI _ _ _ => ExprBaseWF eO ∧ ExprBaseWF eI
  | .product eA eB => ExprBaseWF eA ∧ ExprBaseWF eB
  | .double e _ _ => ExprBaseWF e
  | .pullback e1 e2 eI _ _ => ExprBaseWF e1 ∧ ExprBaseWF e2 ∧ ExprBaseWF eI
  | .pushout e1 e2 eS _ _ => ExprBaseWF e1 ∧ ExprBaseWF e2 ∧ ExprBaseWF eS
  | .ppScale e0 _ _ _ => ExprBaseWF e0
  | _ => True

/-- Every evaluation of a state expression whose embedded base states are
    well-formed yields a well-formed state, across all thirteen constructors. -/
theorem wf_of_evalExpr {e : StateExpr} {s : CodeState}
    (h : EvalExpr e s) (hbase : ExprBaseWF e) : EncodingWellFormed s := by
  induction h with
  | base _ => exact hbase
  | directSum hQ hU _ _ ih1 ih2 =>
      exact directSum_wellFormed _ _ (ih1 hbase.1) (ih2 hbase.2) hQ hU
  | glue _ _ hwf _ _ _ _ _ => exact hwf
  | hgp h1 h2 hcap => exact evalExpr_hgp_wf (EvalExpr.hgp h1 h2 hcap)
  | lift hG hA hB hcap => exact evalExpr_lift_wf (EvalExpr.lift hG hA hB hcap)
  | twoblock hG ha hb hcap => exact evalExpr_twoblock_wf (EvalExpr.twoblock hG ha hb hcap)
  | concat hO hI hty hcap heO heI _ _ =>
      exact evalExpr_concat_wf (EvalExpr.concat hO hI hty hcap heO heI)
  | product hA hB _ _ _ _ _ =>
      exact wf_constructedState _ _ (product_naturalOrthogonal _ _ hA hB)
  | double hC hty hcomm hcap he _ =>
      exact evalExpr_double_wf (EvalExpr.double hC hty hcomm hcap he)
  | balanced hty hcap =>
      exact evalExpr_balanced_wellFormed (EvalExpr.balanced hty hcap)
  | tanner hty hcomm hcap =>
      exact evalExpr_tanner_wf (EvalExpr.tanner hty hcomm hcap)
  | tile hty hcomm hcap =>
      exact evalExpr_tile_wf (EvalExpr.tile hty hcomm hcap)
  | nested hty hcomm hcap =>
      exact evalExpr_nested_wf (EvalExpr.nested hty hcomm hcap)
  | cone hty hcomm hcap =>
      exact evalExpr_cone_wf (EvalExpr.cone hty hcomm hcap)
  | empty =>
      exact evalExpr_empty_wf EvalExpr.empty
  | free hty =>
      exact evalExpr_free_wf (EvalExpr.free hty)
  | pullback h1 h2 hI hty hm1 hm2 hcomm hcap he1 he2 heI =>
      exact evalExpr_pullback_wf (EvalExpr.pullback h1 h2 hI hty hm1 hm2 hcomm hcap he1 he2 heI)
  | pushout h1 h2 hS hty hm1 hm2 hcomm hcap he1 he2 heS =>
      exact evalExpr_pushout_wf (EvalExpr.pushout h1 h2 hS hty hm1 hm2 hcomm hcap he1 he2 heS)
  | liftTable hG hA hB hcap =>
      exact evalExpr_liftTable_wf (EvalExpr.liftTable hG hA hB hcap)
  | twoblockTable hG ha hb hcap =>
      exact evalExpr_twoblockTable_wf (EvalExpr.twoblockTable hG ha hb hcap)
  | balancedTable hty hcap =>
      exact evalExpr_balancedTable_wf (EvalExpr.balancedTable hty hcap)
  | pairPartition hty hcomm hcap =>
      exact evalExpr_pairPartition_wf (EvalExpr.pairPartition hty hcomm hcap)
  | ppScale h0 hty hcomm hcap he0 =>
      exact evalExpr_ppScale_wf (EvalExpr.ppScale h0 hty hcomm hcap he0)

/-- General `n` lemma for `A-CONCAT` on arbitrary sub-expressions. -/
theorem evalExpr_concat_n_gen {eO eI : StateExpr} {blocks repsX repsZ : List (List Nat)}
    {sO sI s : CodeState}
    (hO : EvalExpr eO sO) (hI : EvalExpr eI sI)
    (h : EvalExpr (StateExpr.concat eO eI blocks repsX repsZ) s) :
    s.Q.length = sI.Q.length * blocks.length := by
  cases h with
  | concat _ _ _ _ heO heI =>
      have h1 := evalExpr_unique hO heO
      have h2 := evalExpr_unique hI heI
      subst h1; subst h2
      exact concatState_n sO sI blocks repsX repsZ

/-- General `n` lemma for `A-PRODUCT` on arbitrary sub-expressions. -/
theorem evalExpr_product_n_gen {eA eB : StateExpr} {sA sB s : CodeState}
    (hA : EvalExpr eA sA) (hB : EvalExpr eB sB)
    (h : EvalExpr (StateExpr.product eA eB) s) :
    s.Q.length =
      (sectorRows sA Sector.Z).length * (sectorRows sB Sector.X).length +
        sA.Q.length * sB.Q.length +
        (sectorRows sA Sector.X).length * (sectorRows sB Sector.Z).length := by
  cases h with
  | product _ _ _ heA heB =>
      have h1 := evalExpr_unique heA hA
      have h2 := evalExpr_unique heB hB
      subst h1; subst h2
      show (constructedState _ _).Q.length = _
      rw [constructedState_n]
      unfold productQubits sectorMatrix sectorRows
      rw [List.length_map, List.length_map, List.length_map, List.length_map]

/-- General `n` lemma for `A-DOUBLE` on arbitrary sub-expressions. -/
theorem evalExpr_double_n_gen {e : StateExpr} {wiring : List (Nat × List Nat)}
    {conj : Bool} {sC s : CodeState}
    (hC : EvalExpr e sC) (h : EvalExpr (StateExpr.double e wiring conj) s) :
    s.Q.length = 2 * sC.Q.length := by
  cases h with
  | double _ _ _ _ he =>
      have h1 := evalExpr_unique he hC
      subst h1
      exact constructedState_n _ _

/-- `k = 0` for `L-EMPTY` (§4.43). -/
theorem evalExpr_empty_k {s : CodeState} (h : EvalExpr StateExpr.empty s) :
    stateK s = 0 := by
  cases h
  rfl

/-- `k = |Q|` for `L-FREE` (§4.43). -/
theorem evalExpr_free_k {qs : List Nat} {s : CodeState}
    (h : EvalExpr (StateExpr.free qs) s) :
    stateK s = qs.length := by
  cases h
  rfl

/-- General `n` lemma for `A-PULLBACK` on arbitrary sub-expressions (§4.43). -/
theorem evalExpr_pullback_n_gen {e1 e2 eI : StateExpr}
    {phi1 phi2 : List (Nat × Nat)} {s1 s2 sI s : CodeState}
    (h1 : EvalExpr e1 s1) (h2 : EvalExpr e2 s2) (hI : EvalExpr eI sI)
    (h : EvalExpr (StateExpr.pullback e1 e2 eI phi1 phi2) s) :
    s.Q.length = (pullbackPairs s1 s2 phi1 phi2).length := by
  cases h with
  | pullback _ _ _ _ _ _ _ _ he1 he2 heI =>
      have h1' := evalExpr_unique he1 h1
      have h2' := evalExpr_unique he2 h2
      have hI' := evalExpr_unique heI hI
      subst h1'; subst h2'; subst hI'
      exact constructedState_n _ _

/-- General `n` lemma for `A-PUSHOUT` on arbitrary sub-expressions (§4.43). -/
theorem evalExpr_pushout_n_gen {e1 e2 eS : StateExpr}
    {psi1 psi2 : List (Nat × Nat)} {s1 s2 sS s : CodeState}
    (h1 : EvalExpr e1 s1) (h2 : EvalExpr e2 s2) (hS : EvalExpr eS sS)
    (h : EvalExpr (StateExpr.pushout e1 e2 eS psi1 psi2) s) :
    s.Q.length = (pushoutClasses s1 s2 sS psi1 psi2).length := by
  cases h with
  | pushout _ _ _ _ _ _ _ _ he1 he2 heS =>
      have h1' := evalExpr_unique he1 h1
      have h2' := evalExpr_unique he2 h2
      have hS' := evalExpr_unique heS hS
      subst h1'; subst h2'; subst hS'
      exact constructedState_n _ _

/-! ## Section 3: Exact-distance discharge & seam-certificate equality bridge -/

/-- The sector-distance field corresponding to a sector. -/
def sectorField : Sector → Field
  | Sector.X => Field.dX
  | Sector.Z => Field.dZ

/-- An uninterpreted distance measure valued in `ExtNat = ℕ ∪ {+∞}`. -/
abbrev ExtMeasure : Type := Field → CodeState → ExtNat

/-- The concrete exact sector distance in `ExtNat = ℕ ∪ {+∞}`. -/
def exactExtMeasure : ExtMeasure
  | Field.dX, s => exactDistanceExt Sector.X s
  | Field.dZ, s => exactDistanceExt Sector.Z s
  | _, _ => ExtNat.finite 0

/-- The distance-measure laws of the expanded operation set over
    `ExtNat = ℕ ∪ {+∞}`: kernel monotonicity (§4.3, §4.5), direct-sum exactness
    (§4.4), graft sector bounds (§4.13), `P-REBASE` invariance (§4.26),
    `E-LOCAL-HADAMARD` sector exchange (§4.27), `E-PEEL` sector bounds (§4.28),
    `E-EXTEND` with `Δ = ∅` monotonicity (§4.30), and the uncertified `E-GLUE`
    lower bound (§4.31). -/
structure ExtMeasureLaws (dMeasure : ExtMeasure) : Prop where
  delete_le : ∀ (r : Nat) (s t : CodeState), EncodingWellFormed s →
    Eval (Command.delete r) s t →
    dMeasure Field.dX t ≤ dMeasure Field.dX s ∧
    dMeasure Field.dZ t ≤ dMeasure Field.dZ s
  add_le : ∀ (sector : Sector) (support : List Nat) (s t : CodeState),
    EncodingWellFormed s →
    Eval (Command.addStab sector support) s t →
    dMeasure Field.dX s ≤ dMeasure Field.dX t ∧
    dMeasure Field.dZ s ≤ dMeasure Field.dZ t
  graft_rel : ∀ (q : Nat) (τ : Sector) (ids : List Nat) (s t : CodeState),
    EncodingWellFormed s →
    Eval (Command.graft q τ ids) s t →
    dMeasure (sectorField τ) s ≤ dMeasure (sectorField τ) t ∧
    dMeasure (sectorField (oppositeSector τ)) t ≤
      dMeasure (sectorField (oppositeSector τ)) s
  rebase_eq : ∀ (σ : Sector) (M : List (List Nat)) (s t : CodeState),
    EncodingWellFormed s →
    Eval (Command.rebase σ M) s t →
    dMeasure Field.dX t = dMeasure Field.dX s ∧
    dMeasure Field.dZ t = dMeasure Field.dZ s
  hadamard_swap : ∀ (T : List Nat) (s t : CodeState),
    EncodingWellFormed s →
    Eval (Command.hadamard T) s t →
    T.isEmpty = false →
    CoversQ T s.Q →
    dMeasure Field.dX t = dMeasure Field.dZ s ∧
    dMeasure Field.dZ t = dMeasure Field.dX s
  peel_rel : ∀ (q : Nat) (τ : Sector) (r_id : Nat) (s t : CodeState),
    EncodingWellFormed s →
    Eval (Command.peel q τ r_id) s t →
    dMeasure (sectorField τ) s ≤ dMeasure (sectorField τ) t ∧
    dMeasure (sectorField (oppositeSector τ)) t ≤
      dMeasure (sectorField (oppositeSector τ)) s ∧
    ExtNat.sub (dMeasure (sectorField (oppositeSector τ)) s) (ExtNat.finite 1) ≤
      dMeasure (sectorField (oppositeSector τ)) t
  extend_nil_le : ∀ (adds : List (Sector × List Nat)) (s t : CodeState),
    EncodingWellFormed s →
    Eval (Command.extend [] adds) s t →
    dMeasure Field.dX s ≤ dMeasure Field.dX t ∧
    dMeasure Field.dZ s ≤ dMeasure Field.dZ t
  directSum_eq : ∀ (a b : CodeState),
    EncodingWellFormed a → EncodingWellFormed b →
    DisjointList a.Q b.Q → DisjointList a.used b.used →
    dMeasure Field.dX (directSumState a b) =
      ExtNat.min (dMeasure Field.dX a) (dMeasure Field.dX b) ∧
    dMeasure Field.dZ (directSumState a b) =
      ExtNat.min (dMeasure Field.dZ a) (dMeasure Field.dZ b)
  glue_ge : ∀ (a b : CodeState) (seams : List (Sector × List Nat)),
    EncodingWellFormed a → EncodingWellFormed b →
    DisjointList a.Q b.Q → DisjointList a.used b.used →
    EncodingWellFormed (glueState a b seams) →
    ExtNat.min (dMeasure Field.dX a) (dMeasure Field.dX b) ≤
      dMeasure Field.dX (glueState a b seams) ∧
    ExtNat.min (dMeasure Field.dZ a) (dMeasure Field.dZ b) ≤
      dMeasure Field.dZ (glueState a b seams)

/-- Non-vacuity: every constant `ExtNat` measure (including `+∞`) satisfies
    all nine laws of `ExtMeasureLaws`. -/
theorem extMeasureLaws_const (c : ExtNat) : ExtMeasureLaws (fun _ _ => c) where
  delete_le := fun _ _ _ _ _ => ⟨ExtNat.le_refl c, ExtNat.le_refl c⟩
  add_le := fun _ _ _ _ _ _ => ⟨ExtNat.le_refl c, ExtNat.le_refl c⟩
  graft_rel := fun _ _ _ _ _ _ _ => ⟨ExtNat.le_refl c, ExtNat.le_refl c⟩
  rebase_eq := fun _ _ _ _ _ _ => ⟨rfl, rfl⟩
  hadamard_swap := fun _ _ _ _ _ _ _ => ⟨rfl, rfl⟩
  peel_rel := fun _ _ _ _ _ _ _ =>
    ⟨ExtNat.le_refl c, ExtNat.le_refl c, ExtNat.sub_one_le c⟩
  extend_nil_le := fun _ _ _ _ _ => ⟨ExtNat.le_refl c, ExtNat.le_refl c⟩
  directSum_eq := fun _ _ _ _ _ _ => by
    have hmin : ExtNat.min c c = c := by
      cases c with
      | finite n => simp [ExtNat.min]
      | inf => rfl
    exact ⟨hmin.symm, hmin.symm⟩
  glue_ge := fun _ _ _ _ _ _ _ _ => ⟨ExtNat.min_le_left c c, ExtNat.min_le_left c c⟩

/-- Full exact-distance discharge: `exactExtMeasure` satisfies all nine
    distance laws of the expanded operation set with no remaining distance
    hypothesis. -/
theorem extMeasureLaws_exact : ExtMeasureLaws exactExtMeasure where
  delete_le := fun _ _ _ _ h =>
    ⟨exactDistanceExt_delete_le h Sector.X, exactDistanceExt_delete_le h Sector.Z⟩
  add_le := fun _ _ _ _ _ h =>
    ⟨exactDistanceExt_add_le h Sector.X, exactDistanceExt_add_le h Sector.Z⟩
  graft_rel := fun _ τ _ s t hwf h => by
    obtain ⟨hsel, hopp⟩ := exactDist_graft_relations hwf h
    cases τ with
    | X =>
        rw [ite_eq_left rfl] at hsel hopp
        refine ⟨?_, ?_⟩
        · show exactDistanceExt Sector.X s ≤ exactDistanceExt Sector.X t
          rw [← extNat_ofOption_exactDist_x, ← extNat_ofOption_exactDist_x]
          exact extNat_le_of_leOpt hsel
        · show exactDistanceExt Sector.Z t ≤ exactDistanceExt Sector.Z s
          rw [← extNat_ofOption_exactDist_z, ← extNat_ofOption_exactDist_z]
          exact extNat_le_of_leOpt hopp
    | Z =>
        have hne : ¬ (Sector.Z = Sector.X) := by decide
        rw [ite_eq_right hne] at hsel hopp
        refine ⟨?_, ?_⟩
        · show exactDistanceExt Sector.Z s ≤ exactDistanceExt Sector.Z t
          rw [← extNat_ofOption_exactDist_z, ← extNat_ofOption_exactDist_z]
          exact extNat_le_of_leOpt hsel
        · show exactDistanceExt Sector.X t ≤ exactDistanceExt Sector.X s
          rw [← extNat_ofOption_exactDist_x, ← extNat_ofOption_exactDist_x]
          exact extNat_le_of_leOpt hopp
  rebase_eq := fun σ M s t hwf h => by
    cases h with
    | rebase _ hok hs' _ _ =>
        subst hs'
        have hd := exactDist_rebaseState s σ M hwf.1 hok
        refine ⟨?_, ?_⟩
        · show exactDistanceExt Sector.X (rebaseState s σ M) = exactDistanceExt Sector.X s
          rw [← extNat_ofOption_exactDist_x, ← extNat_ofOption_exactDist_x, hd]
        · show exactDistanceExt Sector.Z (rebaseState s σ M) = exactDistanceExt Sector.Z s
          rw [← extNat_ofOption_exactDist_z, ← extNat_ofOption_exactDist_z, hd]
  hadamard_swap := fun T s t _ h hne hp => by
    cases h with
    | hadamardSplit hsub _ _ _ _ _ =>
        exact absurd hp (not_coversQ_of_properSubset hsub)
    | hadamard _ hs' _ =>
        subst hs'
        have hswap : hadamardState s T = swapState s := by
          unfold hadamardState
          rw [hne]
          rfl
        rw [hswap]
        obtain ⟨hx, hz⟩ := exactDist_swapState s
        refine ⟨?_, ?_⟩
        · show exactDistanceExt Sector.X (swapState s) = exactDistanceExt Sector.Z s
          rw [← extNat_ofOption_exactDist_x, ← extNat_ofOption_exactDist_z, hx]
        · show exactDistanceExt Sector.Z (swapState s) = exactDistanceExt Sector.X s
          rw [← extNat_ofOption_exactDist_z, ← extNat_ofOption_exactDist_x, hz]
  peel_rel := fun _ τ _ s t hwf h => by
    obtain ⟨hsel, hopp, hlow⟩ := exactDist_peel_relations hwf h
    cases τ with
    | X =>
        rw [ite_eq_left rfl] at hsel hopp hlow
        refine ⟨?_, ?_, ?_⟩
        · show exactDistanceExt Sector.X s ≤ exactDistanceExt Sector.X t
          rw [← extNat_ofOption_exactDist_x, ← extNat_ofOption_exactDist_x]
          exact extNat_le_of_leOpt hsel
        · show exactDistanceExt Sector.Z t ≤ exactDistanceExt Sector.Z s
          rw [← extNat_ofOption_exactDist_z, ← extNat_ofOption_exactDist_z]
          exact extNat_le_of_leOpt hopp
        · show ExtNat.sub (exactDistanceExt Sector.Z s) (ExtNat.finite 1) ≤
              exactDistanceExt Sector.Z t
          rw [← extNat_ofOption_exactDist_z, ← extNat_ofOption_exactDist_z,
            ← extNat_ofOption_predOpt]
          exact extNat_le_of_leOpt hlow
    | Z =>
        have hne : ¬ (Sector.Z = Sector.X) := by decide
        rw [ite_eq_right hne] at hsel hopp hlow
        refine ⟨?_, ?_, ?_⟩
        · show exactDistanceExt Sector.Z s ≤ exactDistanceExt Sector.Z t
          rw [← extNat_ofOption_exactDist_z, ← extNat_ofOption_exactDist_z]
          exact extNat_le_of_leOpt hsel
        · show exactDistanceExt Sector.X t ≤ exactDistanceExt Sector.X s
          rw [← extNat_ofOption_exactDist_x, ← extNat_ofOption_exactDist_x]
          exact extNat_le_of_leOpt hopp
        · show ExtNat.sub (exactDistanceExt Sector.X s) (ExtNat.finite 1) ≤
              exactDistanceExt Sector.X t
          rw [← extNat_ofOption_exactDist_x, ← extNat_ofOption_exactDist_x,
            ← extNat_ofOption_predOpt]
          exact extNat_le_of_leOpt hlow
  extend_nil_le := fun _ s t hwf h => by
    obtain ⟨_, hx, hz⟩ := exactDist_extend_nil hwf h
    refine ⟨?_, ?_⟩
    · show exactDistanceExt Sector.X s ≤ exactDistanceExt Sector.X t
      rw [← extNat_ofOption_exactDist_x, ← extNat_ofOption_exactDist_x]
      exact extNat_le_of_leOpt hx
    · show exactDistanceExt Sector.Z s ≤ exactDistanceExt Sector.Z t
      rw [← extNat_ofOption_exactDist_z, ← extNat_ofOption_exactDist_z]
      exact extNat_le_of_leOpt hz
  directSum_eq := fun a b hwfA hwfB hQ _ => by
    have hd := exactDist_directSumState (DirectSumCtx.ofWellFormed hQ hwfA hwfB)
    refine ⟨?_, ?_⟩
    · show exactDistanceExt Sector.X (directSumState a b) =
        ExtNat.min (exactDistanceExt Sector.X a) (exactDistanceExt Sector.X b)
      rw [← extNat_ofOption_exactDist_x, ← extNat_ofOption_exactDist_x,
        ← extNat_ofOption_exactDist_x, congrArg ExactDist.x hd, extNat_ofOption_minOpt]
    · show exactDistanceExt Sector.Z (directSumState a b) =
        ExtNat.min (exactDistanceExt Sector.Z a) (exactDistanceExt Sector.Z b)
      rw [← extNat_ofOption_exactDist_z, ← extNat_ofOption_exactDist_z,
        ← extNat_ofOption_exactDist_z, congrArg ExactDist.z hd, extNat_ofOption_minOpt]
  glue_ge := fun a b seams hwfA hwfB hQ _ _ => by
    have hd := exactDist_directSumState (DirectSumCtx.ofWellFormed hQ hwfA hwfB)
    have hdx : (exactDist (directSumState a b)).x = minOpt (exactDist a).x (exactDist b).x :=
      congrArg ExactDist.x hd
    have hdz : (exactDist (directSumState a b)).z = minOpt (exactDist a).z (exactDist b).z :=
      congrArg ExactDist.z hd
    obtain ⟨_, hx, hz⟩ := exactDist_glueState_ge a b seams
    refine ⟨?_, ?_⟩
    · show ExtNat.min (exactDistanceExt Sector.X a) (exactDistanceExt Sector.X b) ≤
        exactDistanceExt Sector.X (glueState a b seams)
      rw [← extNat_ofOption_exactDist_x, ← extNat_ofOption_exactDist_x,
        ← extNat_ofOption_exactDist_x, ← extNat_ofOption_minOpt, ← hdx]
      exact extNat_le_of_leOpt hx
    · show ExtNat.min (exactDistanceExt Sector.Z a) (exactDistanceExt Sector.Z b) ≤
        exactDistanceExt Sector.Z (glueState a b seams)
      rw [← extNat_ofOption_exactDist_z, ← extNat_ofOption_exactDist_z,
        ← extNat_ofOption_exactDist_z, ← extNat_ofOption_minOpt, ← hdz]
      exact extNat_le_of_leOpt hz

/-! ### Seam-certificate equality policy (`spec/JUDGMENT_LAYER.md` §2e) -/

/-- A seam-certificate policy decides which `(a, b, seams)` tuples carry the
    certified `E-GLUE` equality `d_Z(glue) = min(d_Z(a), d_Z(b))`. -/
abbrev SeamCertPolicy : Type := CodeState → CodeState → List (Sector × List Nat) → Prop

/-- Soundness of a seam-certificate policy for `dMeasure`: every certified
    well-formed glue satisfies `d_Z(glue) = min(d_Z(a), d_Z(b))`.

    In `spec/JUDGMENT_LAYER.md` §2e, acceptance is move-word equality
    `w(c_A) = w(c_B)` over `{U,D,L,R}^*`. Move words and planar layouts are
    not part of `CodeState`, so the geometric implication stays an explicit
    cell hypothesis (`SeamCertSound`). For `exactExtMeasure`, the algebraic
    survival predicate `AdmissibleSeam · · · Sector.Z` discharges
    `SeamCertSound` unconditionally (`seamCertSound_admissibleSeam`). -/
def SeamCertSound (dMeasure : ExtMeasure) (seamCert : SeamCertPolicy) : Prop :=
  ∀ a b seams,
    EncodingWellFormed a → EncodingWellFormed b →
    DisjointList a.Q b.Q → DisjointList a.used b.used →
    EncodingWellFormed (glueState a b seams) →
    seamCert a b seams →
    dMeasure Field.dZ (glueState a b seams) =
      ExtNat.min (dMeasure Field.dZ a) (dMeasure Field.dZ b)

/-- The uncertified policy accepts no seam certificate and is trivially sound
    for every measure. -/
def noSeamCert : SeamCertPolicy := fun _ _ _ => False

theorem seamCertSound_none (dMeasure : ExtMeasure) :
    SeamCertSound dMeasure noSeamCert :=
  fun _ _ _ _ _ _ _ _ h => False.elim h

/-- Helper: a surviving `σ`-logical of factor `a` upper-bounds
    `exactDistanceExt σ (glueState a b seams)` by its weight. -/
theorem exactDistanceExt_glue_le_of_survivesA {a b : CodeState}
    {seams : List (Sector × List Nat)} {σ : Sector} {u : List Bool}
    (h : SurvivesA a b seams σ u) :
    exactDistanceExt σ (glueState a b seams) ≤ ExtNat.finite (weight u) := by
  obtain ⟨hu, _, hlogC⟩ := h
  have hmem : u ++ List.replicate b.Q.length false ∈ logicalVectors (glueState a b seams) σ := by
    rw [mem_logicalVectors_iff]
    refine ⟨?_, hlogC⟩
    rw [List.length_append, hu, List.length_replicate, glueState_Q_length]
  obtain ⟨mc, hmc, hle⟩ := exactDistance?_le_of_mem hmem
  rw [weight_append_eq, weight_replicate_false, Nat.add_zero] at hle
  unfold exactDistanceExt
  rw [hmc]
  exact hle

/-- Helper: a surviving `σ`-logical of factor `b` upper-bounds
    `exactDistanceExt σ (glueState a b seams)` by its weight. -/
theorem exactDistanceExt_glue_le_of_survivesB {a b : CodeState}
    {seams : List (Sector × List Nat)} {σ : Sector} {u : List Bool}
    (h : SurvivesB a b seams σ u) :
    exactDistanceExt σ (glueState a b seams) ≤ ExtNat.finite (weight u) := by
  obtain ⟨hu, _, hlogC⟩ := h
  have hmem : List.replicate a.Q.length false ++ u ∈ logicalVectors (glueState a b seams) σ := by
    rw [mem_logicalVectors_iff]
    refine ⟨?_, hlogC⟩
    rw [List.length_append, List.length_replicate, hu, glueState_Q_length]
  obtain ⟨mc, hmc, hle⟩ := exactDistance?_le_of_mem hmem
  rw [weight_append_eq, weight_replicate_false, Nat.zero_add] at hle
  unfold exactDistanceExt
  rw [hmc]
  exact hle

/-- Unconditional `ExtNat` discharge of the `E-GLUE` exact-distance equality
    under `AdmissibleSeam`: holds across all four finite / `+∞` combinations
    without `HasMinLogical` or `LogField` hypotheses. -/
theorem exactDistanceExt_glue_eq_min_of_admissibleSeam
    {a b : CodeState} {seams : List (Sector × List Nat)} {σ : Sector}
    (hwfA : EncodingWellFormed a) (hwfB : EncodingWellFormed b)
    (hQ : DisjointList a.Q b.Q) (hU : DisjointList a.used b.used)
    (hwfG : EncodingWellFormed (glueState a b seams))
    (hadm : AdmissibleSeam a b seams σ) :
    exactDistanceExt σ (glueState a b seams) =
      ExtNat.min (exactDistanceExt σ a) (exactDistanceExt σ b) := by
  have hge : ExtNat.min (exactDistanceExt σ a) (exactDistanceExt σ b) ≤
      exactDistanceExt σ (glueState a b seams) := by
    cases σ with
    | X => exact (extMeasureLaws_exact.glue_ge a b seams hwfA hwfB hQ hU hwfG).1
    | Z => exact (extMeasureLaws_exact.glue_ge a b seams hwfA hwfB hQ hU hwfG).2
  apply ExtNat.le_antisymm _ hge
  have hA_step : ∀ da, exactDistance? σ a = some da →
      exactDistanceExt σ (glueState a b seams) ≤ ExtNat.finite da := by
    intro da hda
    obtain ⟨u, hu, hw⟩ := minWeight?_attained _ da hda
    obtain ⟨hlen, hlog⟩ := (mem_logicalVectors_iff a σ u).mp hu
    have hnat : exactDistance σ a = da := by
      rw [exactDistance_eq_getD, hda]
      rfl
    have hsurv := hadm.1 u hlen hlog (hw.trans hnat.symm)
    rw [← hw]
    exact exactDistanceExt_glue_le_of_survivesA hsurv
  have hB_step : ∀ db, exactDistance? σ b = some db →
      exactDistanceExt σ (glueState a b seams) ≤ ExtNat.finite db := by
    intro db hdb
    obtain ⟨u, hu, hw⟩ := minWeight?_attained _ db hdb
    obtain ⟨hlen, hlog⟩ := (mem_logicalVectors_iff b σ u).mp hu
    have hnat : exactDistance σ b = db := by
      rw [exactDistance_eq_getD, hdb]
      rfl
    have hsurv := hadm.2 u hlen hlog (hw.trans hnat.symm)
    rw [← hw]
    exact exactDistanceExt_glue_le_of_survivesB hsurv
  unfold exactDistanceExt
  cases ha : exactDistance? σ a with
  | none =>
      cases hb : exactDistance? σ b with
      | none => exact ExtNat.le_inf _
      | some db => exact hB_step db hb
  | some da =>
      cases hb : exactDistance? σ b with
      | none => exact hA_step da ha
      | some db =>
          show exactDistanceExt σ (glueState a b seams) ≤ ExtNat.finite (min da db)
          rcases Nat.le_total da db with hle | hge'
          · rw [Nat.min_eq_left hle]; exact hA_step da ha
          · rw [Nat.min_eq_right hge']; exact hB_step db hb

/-- The survival-based seam-certificate policy (`AdmissibleSeam` on `Sector.Z`)
    is unconditionally sound for `exactExtMeasure`. -/
def admissibleSeamCert : SeamCertPolicy :=
  fun a b seams => AdmissibleSeam a b seams Sector.Z

theorem seamCertSound_admissibleSeam :
    SeamCertSound exactExtMeasure admissibleSeamCert :=
  fun _ _ _ hwfA hwfB hQ hU hwfG hadm =>
    exactDistanceExt_glue_eq_min_of_admissibleSeam hwfA hwfB hQ hU hwfG hadm

/-! ## Section 4: Expanded sentence language, `ExtAnnTrue`, `ExtDerives`, and `ExtModels` -/

/-- An atom of the expanded sentence language: either a field at a position of
    the command evaluation chain, or a field of a concrete state (such as a
    factor state evaluated by `EvalExpr`). -/
inductive ExtAtom : Type where
  | pos : Nat → Field → ExtAtom
  | state : CodeState → Field → ExtAtom
  deriving Repr, DecidableEq

/-- Terms of the expanded sentence language over `ExtNat = ℕ ∪ {+∞}`. -/
inductive ExtAExpr : Type where
  | const : Nat → ExtAExpr
  | inf : ExtAExpr
  | atom : ExtAtom → ExtAExpr
  | sub : ExtAExpr → ExtAExpr → ExtAExpr
  | add : ExtAExpr → ExtAExpr → ExtAExpr
  | minOf : ExtAExpr → ExtAExpr → ExtAExpr
  deriving Repr, DecidableEq

/-- Sentences of the expanded judgment layer: inequalities, equalities,
    chain-position well-formedness, state well-formedness, and
    generator-referencing claims. -/
inductive ExtAnn : Type where
  | le : ExtAExpr → ExtAExpr → ExtAnn
  | eq : ExtAExpr → ExtAExpr → ExtAnn
  | wf : Nat → ExtAnn
  | wfState : CodeState → ExtAnn
  | gen : Nat → Nat → Sector → List Nat → ExtAnn
  deriving Repr, DecidableEq

/-- Value of a carry-table field on a state in `ExtNat`. `d` unfolds to
    `ExtNat.min (dMeasure .dX s) (dMeasure .dZ s)`. -/
def extFieldValue (dMeasure : ExtMeasure) : Field → CodeState → ExtNat
  | .n, s => ExtNat.finite s.Q.length
  | .k, s => ExtNat.finite (stateK s)
  | .d, s => ExtNat.min (dMeasure .dX s) (dMeasure .dZ s)
  | .dX, s => dMeasure .dX s
  | .dZ, s => dMeasure .dZ s

theorem extFieldValue_d (dMeasure : ExtMeasure) (s : CodeState) :
    extFieldValue dMeasure .d s =
      ExtNat.min (extFieldValue dMeasure .dX s) (extFieldValue dMeasure .dZ s) :=
  rfl

theorem extFieldValue_sectorField (dMeasure : ExtMeasure) (σ : Sector) (s : CodeState) :
    extFieldValue dMeasure (sectorField σ) s = dMeasure (sectorField σ) s := by
  cases σ <;> rfl

/-- Value of an `ExtAtom` over a chain: `none` iff the atom is a chain
    position beyond the chain. -/
def extAtomValue (dMeasure : ExtMeasure) (cs : List CodeState) :
    ExtAtom → Option ExtNat
  | .pos i f => (cs[i]?).map (extFieldValue dMeasure f)
  | .state s f => some (extFieldValue dMeasure f s)

/-- Value of an `ExtAExpr` over a chain: strict in `none` across `sub`, `add`,
    and `minOf`, so `+∞` (`some ExtNat.inf`) is distinct from an out-of-bounds
    position (`none`) and every defined value is invariant under chain
    extension (`extAexprValue_append_of_some`). -/
def extAexprValue (dMeasure : ExtMeasure) (cs : List CodeState) :
    ExtAExpr → Option ExtNat
  | .const v => some (ExtNat.finite v)
  | .inf => some ExtNat.inf
  | .atom a => extAtomValue dMeasure cs a
  | .sub e1 e2 =>
      match extAexprValue dMeasure cs e1, extAexprValue dMeasure cs e2 with
      | some a, some b => some (ExtNat.sub a b)
      | _, _ => none
  | .add e1 e2 =>
      match extAexprValue dMeasure cs e1, extAexprValue dMeasure cs e2 with
      | some a, some b => some (ExtNat.add a b)
      | _, _ => none
  | .minOf e1 e2 =>
      match extAexprValue dMeasure cs e1, extAexprValue dMeasure cs e2 with
      | some a, some b => some (ExtNat.min a b)
      | _, _ => none

/-- A term denotes in the chain when its `Option ExtNat` value is `some _`. -/
def extDenotes (dMeasure : ExtMeasure) (cs : List CodeState) (x : ExtAExpr) : Prop :=
  ∃ v, extAexprValue dMeasure cs x = some v

theorem extAexprValue_determinism {dMeasure : ExtMeasure} {cs : List CodeState}
    {x : ExtAExpr} {v w : ExtNat}
    (h1 : extAexprValue dMeasure cs x = some v)
    (h2 : extAexprValue dMeasure cs x = some w) : v = w :=
  Option.some.inj (h1.symm.trans h2)

/-- Satisfaction of an expanded sentence at a chain (`⊨` of §4.11). -/
def ExtAnnTrue (dMeasure : ExtMeasure) (cs : List CodeState) : ExtAnn → Prop
  | .le x y =>
      ∃ v w, extAexprValue dMeasure cs x = some v ∧
        extAexprValue dMeasure cs y = some w ∧ v ≤ w
  | .eq x y =>
      ∃ v, extAexprValue dMeasure cs x = some v ∧
        extAexprValue dMeasure cs y = some v
  | .wf i => ∃ s, cs[i]? = some s ∧ EncodingWellFormed s
  | .wfState s => EncodingWellFormed s
  | .gen i r σ S =>
      ∃ s, cs[i]? = some s ∧ ({ id := r, sector := σ, support := S } : Row) ∈ s.rows

/-- The expanded derivation system `Γ ⊢ … : R` covering every command of the
    expanded operation set (kernel, `E-GRAFT`, and all five unary Gate 6 moves)
    and every state expression (`C-DIRECT-SUM`, `E-GLUE` uncertified and
    certified under `seamCert`, and the ten admitted typed constructors),
    together with L3 order theory, `MIN-ORDER`, and generator-referencing
    transport / `W13` rows.

    Deliberately absent (unavailable / open / not yet defined):
    * the conditional priced cells of `spec/JUDGMENT_LAYER.md` §2a — priced
      deletion, strict improvement, the gauging price, and the two `E-PEEL`
      prices — which are not rows of `ExtDerives`; they are mechanized in
      `PricedInterval.lean` and `Gate6Exact.lean`;
    * unpriced post-deletion distance lower bounds or equalities;
    * `E-PUNCTURE` distance rows (§4.29);
    * `E-EXTEND` with `Δ ≠ ∅` distance rows (§4.30);
    * `E-GRAFT` spliced-sector upper bound and opposite-sector lower bound;
    * `E-PEEL` selected-sector upper bound;
    * `E-GLUE` X-sector or full-distance upper bounds, and Z-sector upper bound
      outside `seamCert`;
    * distance rows for any of the ten admitted constructors (§2g);
    * `k` rows for `L-HGP` and `A-PRODUCT` (whose closed forms are theorems
      of `ClosedK.lean` and are not rules of this relation). -/
inductive ExtDerives (dMeasure : ExtMeasure) (seamCert : SeamCertPolicy)
    (cs : List CodeState) : ExtAnn → Prop where
  -- Bridge between chain positions and concrete states (connects `EvalExpr`
  -- annotations at position 0 to command-chain derivations).
  | instChainState (i : Nat) (f : Field) (s : CodeState)
      (hi : cs[i]? = some s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.pos i f)) (ExtAExpr.atom (.state s f)))
  -- Kernel: C-SKIP
  | instSkip (i : Nat) (f : Field) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval Command.skip s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.pos (i + 1) f)) (ExtAExpr.atom (.pos i f)))
  | instSkipWF (i : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval Command.skip s t) :
      ExtDerives dMeasure seamCert cs (ExtAnn.wf (i + 1))
  -- Kernel: C-DELETE-CHECK
  | instDeleteN (i r : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.delete r) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.pos (i + 1) Field.n)) (ExtAExpr.atom (.pos i Field.n)))
  | instDeleteK (i r : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.delete r) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.pos (i + 1) Field.k))
          (ExtAExpr.add (ExtAExpr.atom (.pos i Field.k)) (ExtAExpr.const 1)))
  | instDeleteKSub (i r : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.delete r) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.pos i Field.k))
          (ExtAExpr.sub (ExtAExpr.atom (.pos (i + 1) Field.k)) (ExtAExpr.const 1)))
  | instDeleteWF (i r : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.delete r) s t) :
      ExtDerives dMeasure seamCert cs (ExtAnn.wf (i + 1))
  | instDeleteDX (i r : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.delete r) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.le (ExtAExpr.atom (.pos (i + 1) Field.dX)) (ExtAExpr.atom (.pos i Field.dX)))
  | instDeleteDZ (i r : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.delete r) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.le (ExtAExpr.atom (.pos (i + 1) Field.dZ)) (ExtAExpr.atom (.pos i Field.dZ)))
  | instDeleteD (i r : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.delete r) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.le (ExtAExpr.atom (.pos (i + 1) Field.d)) (ExtAExpr.atom (.pos i Field.d)))
  -- Kernel: C-ADD-CHECK
  | instAddN (i : Nat) (sector : Sector) (support : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.addStab sector support) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.pos (i + 1) Field.n)) (ExtAExpr.atom (.pos i Field.n)))
  | instAddK (i : Nat) (sector : Sector) (support : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.addStab sector support) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.pos i Field.k))
          (ExtAExpr.add (ExtAExpr.atom (.pos (i + 1) Field.k)) (ExtAExpr.const 1)))
  | instAddKSub (i : Nat) (sector : Sector) (support : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.addStab sector support) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.pos (i + 1) Field.k))
          (ExtAExpr.sub (ExtAExpr.atom (.pos i Field.k)) (ExtAExpr.const 1)))
  | instAddWF (i : Nat) (sector : Sector) (support : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.addStab sector support) s t) :
      ExtDerives dMeasure seamCert cs (ExtAnn.wf (i + 1))
  | instAddDX (i : Nat) (sector : Sector) (support : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.addStab sector support) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.le (ExtAExpr.atom (.pos i Field.dX)) (ExtAExpr.atom (.pos (i + 1) Field.dX)))
  | instAddDZ (i : Nat) (sector : Sector) (support : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.addStab sector support) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.le (ExtAExpr.atom (.pos i Field.dZ)) (ExtAExpr.atom (.pos (i + 1) Field.dZ)))
  | instAddD (i : Nat) (sector : Sector) (support : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.addStab sector support) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.le (ExtAExpr.atom (.pos i Field.d)) (ExtAExpr.atom (.pos (i + 1) Field.d)))
  -- Admitted conditional move: E-GRAFT (§4.12, §4.13)
  | instGraftN (i q : Nat) (sector : Sector) (ids : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.graft q sector ids) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.pos (i + 1) Field.n))
          (ExtAExpr.sub (ExtAExpr.atom (.pos i Field.n)) (ExtAExpr.const 1)))
  | instGraftK (i q : Nat) (sector : Sector) (ids : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.graft q sector ids) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.pos (i + 1) Field.k)) (ExtAExpr.atom (.pos i Field.k)))
  | instGraftWF (i q : Nat) (sector : Sector) (ids : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.graft q sector ids) s t) :
      ExtDerives dMeasure seamCert cs (ExtAnn.wf (i + 1))
  | instGraftSpliced (i q : Nat) (sector : Sector) (ids : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.graft q sector ids) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.le (ExtAExpr.atom (.pos i (sectorField sector)))
          (ExtAExpr.atom (.pos (i + 1) (sectorField sector))))
  | instGraftOpp (i q : Nat) (sector : Sector) (ids : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.graft q sector ids) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.le (ExtAExpr.atom (.pos (i + 1) (sectorField (oppositeSector sector))))
          (ExtAExpr.atom (.pos i (sectorField (oppositeSector sector)))))
  | instGraftFullUpper (i q : Nat) (sector : Sector) (ids : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.graft q sector ids) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.le (ExtAExpr.atom (.pos (i + 1) Field.d))
          (ExtAExpr.atom (.pos i (sectorField (oppositeSector sector)))))
  -- Gate 6: P-REBASE (§4.26)
  | instRebase (i : Nat) (f : Field) (sector : Sector) (matrix : List (List Nat))
      (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.rebase sector matrix) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.pos (i + 1) f)) (ExtAExpr.atom (.pos i f)))
  | instRebaseWF (i : Nat) (sector : Sector) (matrix : List (List Nat)) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.rebase sector matrix) s t) :
      ExtDerives dMeasure seamCert cs (ExtAnn.wf (i + 1))
  -- Gate 6: E-LOCAL-HADAMARD (§4.27)
  | instHadamardN (i : Nat) (T : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.hadamard T) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.pos (i + 1) Field.n)) (ExtAExpr.atom (.pos i Field.n)))
  | instHadamardK (i : Nat) (T : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.hadamard T) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.pos (i + 1) Field.k)) (ExtAExpr.atom (.pos i Field.k)))
  | instHadamardD (i : Nat) (T : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.hadamard T) s t) (hg : T.Perm s.Q ∨ T = []) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.pos (i + 1) Field.d)) (ExtAExpr.atom (.pos i Field.d)))
  | instHadamardWF (i : Nat) (T : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.hadamard T) s t) :
      ExtDerives dMeasure seamCert cs (ExtAnn.wf (i + 1))
  | instHadamardEmpty (i : Nat) (f : Field) (T : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.hadamard T) s t) (hT : T.isEmpty = true) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.pos (i + 1) f)) (ExtAExpr.atom (.pos i f)))
  | instHadamardSwapDX (i : Nat) (T : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.hadamard T) s t) (hT : CoversQ T s.Q ∧ T.isEmpty = false) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.pos (i + 1) Field.dX)) (ExtAExpr.atom (.pos i Field.dZ)))
  | instHadamardSwapDZ (i : Nat) (T : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.hadamard T) s t) (hT : CoversQ T s.Q ∧ T.isEmpty = false) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.pos (i + 1) Field.dZ)) (ExtAExpr.atom (.pos i Field.dX)))
  -- Gate 6: E-PEEL (§4.28)
  | instPeelN (i q : Nat) (τ : Sector) (r_id : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.peel q τ r_id) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.pos (i + 1) Field.n))
          (ExtAExpr.sub (ExtAExpr.atom (.pos i Field.n)) (ExtAExpr.const 1)))
  | instPeelK (i q : Nat) (τ : Sector) (r_id : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.peel q τ r_id) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.pos (i + 1) Field.k)) (ExtAExpr.atom (.pos i Field.k)))
  | instPeelWF (i q : Nat) (τ : Sector) (r_id : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.peel q τ r_id) s t) :
      ExtDerives dMeasure seamCert cs (ExtAnn.wf (i + 1))
  | instPeelSpliced (i q : Nat) (τ : Sector) (r_id : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.peel q τ r_id) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.le (ExtAExpr.atom (.pos i (sectorField τ)))
          (ExtAExpr.atom (.pos (i + 1) (sectorField τ))))
  | instPeelOppUpper (i q : Nat) (τ : Sector) (r_id : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.peel q τ r_id) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.le (ExtAExpr.atom (.pos (i + 1) (sectorField (oppositeSector τ))))
          (ExtAExpr.atom (.pos i (sectorField (oppositeSector τ)))))
  | instPeelOppLower (i q : Nat) (τ : Sector) (r_id : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.peel q τ r_id) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.le
          (ExtAExpr.sub (ExtAExpr.atom (.pos i (sectorField (oppositeSector τ))))
            (ExtAExpr.const 1))
          (ExtAExpr.atom (.pos (i + 1) (sectorField (oppositeSector τ)))))
  | instPeelFullLower (i q : Nat) (τ : Sector) (r_id : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.peel q τ r_id) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.le (ExtAExpr.sub (ExtAExpr.atom (.pos i Field.d)) (ExtAExpr.const 1))
          (ExtAExpr.atom (.pos (i + 1) Field.d)))
  | instPeelFullUpper (i q : Nat) (τ : Sector) (r_id : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.peel q τ r_id) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.le (ExtAExpr.atom (.pos (i + 1) Field.d))
          (ExtAExpr.atom (.pos i (sectorField (oppositeSector τ)))))
  -- Gate 6: E-PUNCTURE (§4.29; no distance rows — unavailable)
  | instPunctureN (i q : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.puncture q) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.pos (i + 1) Field.n))
          (ExtAExpr.sub (ExtAExpr.atom (.pos i Field.n)) (ExtAExpr.const 1)))
  | instPunctureK (i q : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.puncture q) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq
          (ExtAExpr.add (ExtAExpr.atom (.pos (i + 1) Field.k)) (ExtAExpr.const 1))
          (ExtAExpr.add (ExtAExpr.atom (.pos i Field.k))
            (ExtAExpr.const (punctureDeletedCount s q))))
  | instPunctureWF (i q : Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.puncture q) s t) :
      ExtDerives dMeasure seamCert cs (ExtAnn.wf (i + 1))
  -- Gate 6: E-EXTEND (§4.30; distance rows for Δ = ∅ only)
  | instExtendN (i : Nat) (delta : List Nat) (adds : List (Sector × List Nat))
      (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.extend delta adds) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.pos (i + 1) Field.n))
          (ExtAExpr.add (ExtAExpr.atom (.pos i Field.n)) (ExtAExpr.const delta.length)))
  | instExtendK (i : Nat) (delta : List Nat) (adds : List (Sector × List Nat))
      (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.extend delta adds) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq
          (ExtAExpr.add (ExtAExpr.atom (.pos (i + 1) Field.k)) (ExtAExpr.const adds.length))
          (ExtAExpr.add (ExtAExpr.atom (.pos i Field.k)) (ExtAExpr.const delta.length)))
  | instExtendWF (i : Nat) (delta : List Nat) (adds : List (Sector × List Nat))
      (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.extend delta adds) s t) :
      ExtDerives dMeasure seamCert cs (ExtAnn.wf (i + 1))
  | instExtendNilDX (i : Nat) (adds : List (Sector × List Nat)) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.extend [] adds) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.le (ExtAExpr.atom (.pos i Field.dX)) (ExtAExpr.atom (.pos (i + 1) Field.dX)))
  | instExtendNilDZ (i : Nat) (adds : List (Sector × List Nat)) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.extend [] adds) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.le (ExtAExpr.atom (.pos i Field.dZ)) (ExtAExpr.atom (.pos (i + 1) Field.dZ)))
  | instExtendNilD (i : Nat) (adds : List (Sector × List Nat)) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.extend [] adds) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.le (ExtAExpr.atom (.pos i Field.d)) (ExtAExpr.atom (.pos (i + 1) Field.d)))
  -- Admitted command: C-COLUMN-CNOT (§4.42; distance window is §2k / matrix-norm conditional)
  | instCnotSwapN (i : Nat) (U : List (List Bool)) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.cnotSwap U) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.pos (i + 1) Field.n)) (ExtAExpr.atom (.pos i Field.n)))
  | instCnotSwapK (i : Nat) (U : List (List Bool)) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.cnotSwap U) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.pos (i + 1) Field.k)) (ExtAExpr.atom (.pos i Field.k)))
  | instCnotSwapWF (i : Nat) (U : List (List Bool)) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.cnotSwap U) s t) :
      ExtDerives dMeasure seamCert cs (ExtAnn.wf (i + 1))
  -- Admitted 2026-11-25: E-SPLIT (§4.48; separating deletion factors into deletions)
  | instSplitN (i : Nat) (QA R : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.split QA R) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.pos (i + 1) Field.n)) (ExtAExpr.atom (.pos i Field.n)))
  | instSplitK (i : Nat) (QA R : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.split QA R) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.pos (i + 1) Field.k))
          (ExtAExpr.add (ExtAExpr.atom (.pos i Field.k)) (ExtAExpr.const R.length)))
  | instSplitWF (i : Nat) (QA R : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.split QA R) s t) :
      ExtDerives dMeasure seamCert cs (ExtAnn.wf (i + 1))
  | instSplitDX (i : Nat) (QA R : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.split QA R) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.le (ExtAExpr.atom (.pos (i + 1) Field.dX)) (ExtAExpr.atom (.pos i Field.dX)))
  | instSplitDZ (i : Nat) (QA R : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.split QA R) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.le (ExtAExpr.atom (.pos (i + 1) Field.dZ)) (ExtAExpr.atom (.pos i Field.dZ)))
  | instSplitD (i : Nat) (QA R : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.split QA R) s t) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.le (ExtAExpr.atom (.pos (i + 1) Field.d)) (ExtAExpr.atom (.pos i Field.d)))
  -- State expressions: uniform well-formedness across all 13 constructors
  | instExprWF (e : StateExpr) (s : CodeState)
      (he : EvalExpr e s) (hbase : ExprBaseWF e) :
      ExtDerives dMeasure seamCert cs (ExtAnn.wfState s)
  -- State expression: C-DIRECT-SUM (§4.4)
  | instDirectSumN (e1 e2 : StateExpr) (s1 s2 s : CodeState)
      (h1 : EvalExpr e1 s1) (h2 : EvalExpr e2 s2)
      (hsum : EvalExpr (StateExpr.directSum e1 e2) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.n))
          (ExtAExpr.add (ExtAExpr.atom (.state s1 Field.n))
            (ExtAExpr.atom (.state s2 Field.n))))
  | instDirectSumK (e1 e2 : StateExpr) (s1 s2 s : CodeState)
      (h1 : EvalExpr e1 s1) (h2 : EvalExpr e2 s2)
      (hsum : EvalExpr (StateExpr.directSum e1 e2) s)
      (hbase1 : ExprBaseWF e1) (hbase2 : ExprBaseWF e2) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.k))
          (ExtAExpr.add (ExtAExpr.atom (.state s1 Field.k))
            (ExtAExpr.atom (.state s2 Field.k))))
  | instDirectSumDX (e1 e2 : StateExpr) (s1 s2 s : CodeState)
      (h1 : EvalExpr e1 s1) (h2 : EvalExpr e2 s2)
      (hsum : EvalExpr (StateExpr.directSum e1 e2) s)
      (hbase1 : ExprBaseWF e1) (hbase2 : ExprBaseWF e2) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.dX))
          (ExtAExpr.minOf (ExtAExpr.atom (.state s1 Field.dX))
            (ExtAExpr.atom (.state s2 Field.dX))))
  | instDirectSumDZ (e1 e2 : StateExpr) (s1 s2 s : CodeState)
      (h1 : EvalExpr e1 s1) (h2 : EvalExpr e2 s2)
      (hsum : EvalExpr (StateExpr.directSum e1 e2) s)
      (hbase1 : ExprBaseWF e1) (hbase2 : ExprBaseWF e2) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.dZ))
          (ExtAExpr.minOf (ExtAExpr.atom (.state s1 Field.dZ))
            (ExtAExpr.atom (.state s2 Field.dZ))))
  | instDirectSumD (e1 e2 : StateExpr) (s1 s2 s : CodeState)
      (h1 : EvalExpr e1 s1) (h2 : EvalExpr e2 s2)
      (hsum : EvalExpr (StateExpr.directSum e1 e2) s)
      (hbase1 : ExprBaseWF e1) (hbase2 : ExprBaseWF e2) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.d))
          (ExtAExpr.minOf (ExtAExpr.atom (.state s1 Field.d))
            (ExtAExpr.atom (.state s2 Field.d))))
  -- State expression: E-GLUE (§4.31, §2e)
  | instGlueN (e1 e2 : StateExpr) (seams : List (Sector × List Nat))
      (s1 s2 s : CodeState)
      (h1 : EvalExpr e1 s1) (h2 : EvalExpr e2 s2)
      (hglue : EvalExpr (StateExpr.glue e1 e2 seams) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.n))
          (ExtAExpr.add (ExtAExpr.atom (.state s1 Field.n))
            (ExtAExpr.atom (.state s2 Field.n))))
  | instGlueK (e1 e2 : StateExpr) (seams : List (Sector × List Nat))
      (s1 s2 s : CodeState)
      (h1 : EvalExpr e1 s1) (h2 : EvalExpr e2 s2)
      (hglue : EvalExpr (StateExpr.glue e1 e2 seams) s)
      (hbase1 : ExprBaseWF e1) (hbase2 : ExprBaseWF e2) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq
          (ExtAExpr.add (ExtAExpr.atom (.state s Field.k)) (ExtAExpr.const seams.length))
          (ExtAExpr.add (ExtAExpr.atom (.state s1 Field.k))
            (ExtAExpr.atom (.state s2 Field.k))))
  | instGlueDX (e1 e2 : StateExpr) (seams : List (Sector × List Nat))
      (s1 s2 s : CodeState)
      (h1 : EvalExpr e1 s1) (h2 : EvalExpr e2 s2)
      (hglue : EvalExpr (StateExpr.glue e1 e2 seams) s)
      (hbase1 : ExprBaseWF e1) (hbase2 : ExprBaseWF e2) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.le
          (ExtAExpr.minOf (ExtAExpr.atom (.state s1 Field.dX))
            (ExtAExpr.atom (.state s2 Field.dX)))
          (ExtAExpr.atom (.state s Field.dX)))
  | instGlueDZ (e1 e2 : StateExpr) (seams : List (Sector × List Nat))
      (s1 s2 s : CodeState)
      (h1 : EvalExpr e1 s1) (h2 : EvalExpr e2 s2)
      (hglue : EvalExpr (StateExpr.glue e1 e2 seams) s)
      (hbase1 : ExprBaseWF e1) (hbase2 : ExprBaseWF e2) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.le
          (ExtAExpr.minOf (ExtAExpr.atom (.state s1 Field.dZ))
            (ExtAExpr.atom (.state s2 Field.dZ)))
          (ExtAExpr.atom (.state s Field.dZ)))
  | instGlueD (e1 e2 : StateExpr) (seams : List (Sector × List Nat))
      (s1 s2 s : CodeState)
      (h1 : EvalExpr e1 s1) (h2 : EvalExpr e2 s2)
      (hglue : EvalExpr (StateExpr.glue e1 e2 seams) s)
      (hbase1 : ExprBaseWF e1) (hbase2 : ExprBaseWF e2) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.le
          (ExtAExpr.minOf (ExtAExpr.atom (.state s1 Field.d))
            (ExtAExpr.atom (.state s2 Field.d)))
          (ExtAExpr.atom (.state s Field.d)))
  | instGlueCertDZ (e1 e2 : StateExpr) (seams : List (Sector × List Nat))
      (s1 s2 s : CodeState)
      (h1 : EvalExpr e1 s1) (h2 : EvalExpr e2 s2)
      (hglue : EvalExpr (StateExpr.glue e1 e2 seams) s)
      (hbase1 : ExprBaseWF e1) (hbase2 : ExprBaseWF e2)
      (hcert : seamCert s1 s2 seams) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.dZ))
          (ExtAExpr.minOf (ExtAExpr.atom (.state s1 Field.dZ))
            (ExtAExpr.atom (.state s2 Field.dZ))))
  -- State expressions: the ten admitted typed constructors (§4.34–§4.36; no
  -- distance rows, and no axiom-backed `k` rows for L-HGP / A-PRODUCT).
  | instHgpN (H1 H2 : List (List Bool)) (s : CodeState)
      (h : EvalExpr (StateExpr.hgp H1 H2) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.n))
          (ExtAExpr.const (matCols H1 * matCols H2 + H1.length * H2.length)))
  | instLiftN (orders : List Nat) (A B : List (List (List (List Nat)))) (s : CodeState)
      (h : EvalExpr (StateExpr.lift orders A B) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.n))
          (ExtAExpr.const ((groupElements orders).length *
            (matCols A * matCols B + A.length * B.length))))
  | instTwoblockN (orders : List Nat) (a b : List (List Nat)) (s : CodeState)
      (h : EvalExpr (StateExpr.twoblock orders a b) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.n))
          (ExtAExpr.const (2 * (groupElements orders).length)))
  | instTwoblockK (orders : List Nat) (a b : List (List Nat)) (s : CodeState)
      (h : EvalExpr (StateExpr.twoblock orders a b) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.k))
          (ExtAExpr.const (2 * ((groupElements orders).length -
            rankBitmasks ((groupElements orders).map (twoblockRowMask orders a b))))))
  | instConcatN (eO eI : StateExpr) (blocks repsX repsZ : List (List Nat))
      (sO sI s : CodeState)
      (hO : EvalExpr eO sO) (hI : EvalExpr eI sI)
      (h : EvalExpr (StateExpr.concat eO eI blocks repsX repsZ) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.n))
          (ExtAExpr.const (sI.Q.length * blocks.length)))
  | instConcatK (eO eI : StateExpr) (blocks repsX repsZ : List (List Nat))
      (sO s : CodeState)
      (hO : EvalExpr eO sO)
      (h : EvalExpr (StateExpr.concat eO eI blocks repsX repsZ) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.k))
          (ExtAExpr.atom (.state sO Field.k)))
  | instProductN (eA eB : StateExpr) (sA sB s : CodeState)
      (hA : EvalExpr eA sA) (hB : EvalExpr eB sB)
      (h : EvalExpr (StateExpr.product eA eB) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.n))
          (ExtAExpr.const
            ((sectorRows sA Sector.Z).length * (sectorRows sB Sector.X).length +
              sA.Q.length * sB.Q.length +
              (sectorRows sA Sector.X).length * (sectorRows sB Sector.Z).length)))
  | instDoubleN (e : StateExpr) (wiring : List (Nat × List Nat)) (conj : Bool)
      (sC s : CodeState)
      (hC : EvalExpr e sC)
      (h : EvalExpr (StateExpr.double e wiring conj) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.n))
          (ExtAExpr.add (ExtAExpr.atom (.state sC Field.n))
            (ExtAExpr.atom (.state sC Field.n))))
  | instDoubleEmptyK (e : StateExpr) (conj : Bool) (sC s : CodeState)
      (hC : EvalExpr e sC)
      (h : EvalExpr (StateExpr.double e [] conj) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.k))
          (ExtAExpr.add (ExtAExpr.atom (.state sC Field.k))
            (ExtAExpr.atom (.state sC Field.k))))
  | instBalancedN (orders : List Nat) (H1 H2 : List (List Bool))
      (rows1 cols1 rows2 cols2 : List (List Nat)) (s : CodeState)
      (h : EvalExpr (StateExpr.balanced orders H1 rows1 cols1 H2 rows2 cols2) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.n))
          (ExtAExpr.const
            ((orbitReps orders cols1 cols2 (matCols H1) (matCols H2)).length +
              (orbitReps orders rows1 rows2 H1.length H2.length).length)))
  | instBalancedK (orders : List Nat) (H1 H2 : List (List Bool))
      (rows1 cols1 rows2 cols2 : List (List Nat)) (s : CodeState)
      (h : EvalExpr (StateExpr.balanced orders H1 rows1 cols1 H2 rows2 cols2) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.k))
          (ExtAExpr.const
            (balancedQubits orders H1 rows1 cols1 H2 rows2 cols2 -
              rankBitmasks ((orbitReps orders rows1 cols2 H1.length (matCols H2)).map (fun c =>
                boolsToMask (balancedXVector orders H1 rows1 cols1 H2 rows2 cols2 c))) -
              rankBitmasks ((orbitReps orders cols1 rows2 (matCols H1) H2.length).map (fun c =>
                boolsToMask (balancedZVector orders H1 rows1 cols1 H2 rows2 cols2 c))))))
  -- The three group constructors over a group given by its multiplication
  -- table (§4.44): `n` only. No `k` row: over a nonabelian group the
  -- two-block formula `2 (|G| - rank)` fails (§4.44, the `D₄` instance).
  | instLiftTableN (t : List (List Nat)) (A B : List (List (List Nat))) (s : CodeState)
      (h : EvalExpr (StateExpr.liftTable t A B) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.n))
          (ExtAExpr.const (t.length *
            (cayleyMatCols A * cayleyMatCols B + A.length * B.length))))
  | instTwoblockTableN (t : List (List Nat)) (a b : List Nat) (s : CodeState)
      (h : EvalExpr (StateExpr.twoblockTable t a b) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.n))
          (ExtAExpr.const (2 * t.length)))
  | instBalancedTableN (t : List (List Nat)) (H1 H2 : List (List Bool))
      (rows1 cols1 rows2 cols2 : List (List Nat)) (s : CodeState)
      (h : EvalExpr (StateExpr.balancedTable t H1 rows1 cols1 H2 rows2 cols2) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.n))
          (ExtAExpr.const (tableBalancedQubits t H1 rows1 cols1 H2 rows2 cols2)))
  | instTannerN (n : Nat) (LX LZ : List (List Bool))
      (viewsX viewsZ : List (List Nat)) (s : CodeState)
      (h : EvalExpr (StateExpr.tanner n LX LZ viewsX viewsZ) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.n)) (ExtAExpr.const n))
  | instTannerK (n : Nat) (LX LZ : List (List Bool))
      (viewsX viewsZ : List (List Nat)) (s : CodeState)
      (h : EvalExpr (StateExpr.tanner n LX LZ viewsX viewsZ) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.k))
          (ExtAExpr.const
            (n - rankBitmasks (viewsX.flatMap (fun v =>
                  LX.map (fun l => boolsToMask (tannerRow n v l)))) -
              rankBitmasks (viewsZ.flatMap (fun v =>
                  LZ.map (fun l => boolsToMask (tannerRow n v l)))))))
  | instTileN (tiles : List (Nat × List (List Nat) × List (List Nat)))
      (placements : List (Nat × List Nat)) (idents : List (Nat × Nat))
      (removed : List (Nat × Sector × Nat)) (s : CodeState)
      (h : EvalExpr (StateExpr.tile tiles placements idents removed) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.n))
          (ExtAExpr.const (tileClasses placements idents).length))
  | instTileK (tiles : List (Nat × List (List Nat) × List (List Nat)))
      (placements : List (Nat × List Nat)) (idents : List (Nat × Nat))
      (removed : List (Nat × Sector × Nat)) (s : CodeState)
      (h : EvalExpr (StateExpr.tile tiles placements idents removed) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.k))
          (ExtAExpr.const
            (tileQubits placements idents -
              rankBitmasks ((List.range placements.length).flatMap (fun pos =>
                (tileRowIdxs tiles placements removed pos Sector.X).map (fun idx =>
                  boolsToMask (tileRowVector tiles placements idents pos Sector.X idx)))) -
              rankBitmasks ((List.range placements.length).flatMap (fun pos =>
                (tileRowIdxs tiles placements removed pos Sector.Z).map (fun idx =>
                  boolsToMask (tileRowVector tiles placements idents pos Sector.Z idx)))))))
  | instNestedN (HX HZ : List (List Bool)) (s : CodeState)
      (h : EvalExpr (StateExpr.nested HX HZ) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.n)) (ExtAExpr.const (matCols HX)))
  -- State expressions: the v0.3.x stdCSS-3 inventory (§4.41, §4.43, §4.46, §4.47;
  -- structural carry rows, no automatic distance rules)
  | instConeN (DA DB F1 F0 : List (List Bool)) (s : CodeState)
      (h : EvalExpr (StateExpr.cone DA DB F1 F0) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.n))
          (ExtAExpr.const (matCols DA + DB.length)))
  | instConeK (DA DB F1 F0 : List (List Bool)) (s : CodeState)
      (h : EvalExpr (StateExpr.cone DA DB F1 F0) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.k))
          (ExtAExpr.const
            (coneN DA DB F1 F0 -
              rankBitmasks (naturalMasks (coneN DA DB F1 F0) (coneVectors DA DB F1 F0) Sector.X) -
              rankBitmasks (naturalMasks (coneN DA DB F1 F0) (coneVectors DA DB F1 F0) Sector.Z))))
  | instEmptyN (s : CodeState)
      (h : EvalExpr StateExpr.empty s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.n)) (ExtAExpr.const 0))
  | instEmptyK (s : CodeState)
      (h : EvalExpr StateExpr.empty s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.k)) (ExtAExpr.const 0))
  | instFreeN (qs : List Nat) (s : CodeState)
      (h : EvalExpr (StateExpr.free qs) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.n)) (ExtAExpr.const qs.length))
  | instFreeK (qs : List Nat) (s : CodeState)
      (h : EvalExpr (StateExpr.free qs) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.k)) (ExtAExpr.const qs.length))
  | instPullbackN (e1 e2 eI : StateExpr) (phi1 phi2 : List (Nat × Nat))
      (s1 s2 sI s : CodeState)
      (h1 : EvalExpr e1 s1) (h2 : EvalExpr e2 s2) (hI : EvalExpr eI sI)
      (h : EvalExpr (StateExpr.pullback e1 e2 eI phi1 phi2) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.n))
          (ExtAExpr.const (pullbackPairs s1 s2 phi1 phi2).length))
  | instPushoutN (e1 e2 eS : StateExpr) (psi1 psi2 : List (Nat × Nat))
      (s1 s2 sS s : CodeState)
      (h1 : EvalExpr e1 s1) (h2 : EvalExpr e2 s2) (hS : EvalExpr eS sS)
      (h : EvalExpr (StateExpr.pushout e1 e2 eS psi1 psi2) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.n))
          (ExtAExpr.const (pushoutClasses s1 s2 sS psi1 psi2).length))
  | instPairPartitionN (p : Nat) (BX BZ : List (List (Nat × Nat))) (s : CodeState)
      (h : EvalExpr (StateExpr.pairPartition p BX BZ) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.n))
          (ExtAExpr.const (matCols BX * p)))
  | instPpScaleN (e0 : StateExpr) (P : Nat) (BX BZ : List (List (Nat × Nat))) (s : CodeState)
      (h : EvalExpr (StateExpr.ppScale e0 P BX BZ) s) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.eq (ExtAExpr.atom (.state s Field.n))
          (ExtAExpr.const (matCols BX * P)))
  -- L3 order theory & MIN-ORDER on `ExtNat = ℕ ∪ {+∞}`
  | transit_le_le (x y z : ExtAExpr)
      (h1 : ExtDerives dMeasure seamCert cs (ExtAnn.le x y))
      (h2 : ExtDerives dMeasure seamCert cs (ExtAnn.le y z)) :
      ExtDerives dMeasure seamCert cs (ExtAnn.le x z)
  | transit_le_eq (x y z : ExtAExpr)
      (h1 : ExtDerives dMeasure seamCert cs (ExtAnn.le x y))
      (h2 : ExtDerives dMeasure seamCert cs (ExtAnn.eq y z)) :
      ExtDerives dMeasure seamCert cs (ExtAnn.le x z)
  | transit_eq_le (x y z : ExtAExpr)
      (h1 : ExtDerives dMeasure seamCert cs (ExtAnn.eq x y))
      (h2 : ExtDerives dMeasure seamCert cs (ExtAnn.le y z)) :
      ExtDerives dMeasure seamCert cs (ExtAnn.le x z)
  | transit_eq_eq (x y z : ExtAExpr)
      (h1 : ExtDerives dMeasure seamCert cs (ExtAnn.eq x y))
      (h2 : ExtDerives dMeasure seamCert cs (ExtAnn.eq y z)) :
      ExtDerives dMeasure seamCert cs (ExtAnn.eq x z)
  | min_le_left (x y : ExtAExpr)
      (hx : extDenotes dMeasure cs x) (hy : extDenotes dMeasure cs y) :
      ExtDerives dMeasure seamCert cs (ExtAnn.le (ExtAExpr.minOf x y) x)
  | min_le_right (x y : ExtAExpr)
      (hx : extDenotes dMeasure cs x) (hy : extDenotes dMeasure cs y) :
      ExtDerives dMeasure seamCert cs (ExtAnn.le (ExtAExpr.minOf x y) y)
  | le_min (t x y : ExtAExpr)
      (h1 : ExtDerives dMeasure seamCert cs (ExtAnn.le t x))
      (h2 : ExtDerives dMeasure seamCert cs (ExtAnn.le t y)) :
      ExtDerives dMeasure seamCert cs (ExtAnn.le t (ExtAExpr.minOf x y))
  | le_refl (x : ExtAExpr) (hx : extDenotes dMeasure cs x) :
      ExtDerives dMeasure seamCert cs (ExtAnn.le x x)
  | eq_refl (x : ExtAExpr) (hx : extDenotes dMeasure cs x) :
      ExtDerives dMeasure seamCert cs (ExtAnn.eq x x)
  | eq_sym (x y : ExtAExpr)
      (h : ExtDerives dMeasure seamCert cs (ExtAnn.eq x y)) :
      ExtDerives dMeasure seamCert cs (ExtAnn.eq y x)
  -- Generator-referencing rows (all kernel, graft, and Gate 6 commands)
  | genInput (r : Nat) (σ : Sector) (S : List Nat) (s : CodeState)
      (h0 : cs[0]? = some s)
      (hrow : ({ id := r, sector := σ, support := S } : Row) ∈ s.rows) :
      ExtDerives dMeasure seamCert cs (ExtAnn.gen 0 r σ S)
  | genMint (i : Nat) (sector : Sector) (support : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.addStab sector support) s t) :
      ExtDerives dMeasure seamCert cs (ExtAnn.gen (i + 1) (canonicalMint s.used) sector support)
  | genSkip (i r : Nat) (σ : Sector) (S : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval Command.skip s t)
      (h : ExtDerives dMeasure seamCert cs (ExtAnn.gen i r σ S)) :
      ExtDerives dMeasure seamCert cs (ExtAnn.gen (i + 1) r σ S)
  | genDelete (i r r' : Nat) (σ : Sector) (S : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.delete r') s t) (hsurvives : r ≠ r')
      (h : ExtDerives dMeasure seamCert cs (ExtAnn.gen i r σ S)) :
      ExtDerives dMeasure seamCert cs (ExtAnn.gen (i + 1) r σ S)
  | genAdd (i r : Nat) (σ : Sector) (S : List Nat) (sector : Sector) (support : List Nat)
      (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.addStab sector support) s t)
      (h : ExtDerives dMeasure seamCert cs (ExtAnn.gen i r σ S)) :
      ExtDerives dMeasure seamCert cs (ExtAnn.gen (i + 1) r σ S)
  | genGraft (i r : Nat) (σ : Sector) (S : List Nat) (q : Nat) (sector : Sector)
      (ids : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.graft q sector ids) s t) (hsurvives : r ∉ ids)
      (h : ExtDerives dMeasure seamCert cs (ExtAnn.gen i r σ S)) :
      ExtDerives dMeasure seamCert cs (ExtAnn.gen (i + 1) r σ (graftSupport q sector σ S))
  | genGraftMint (i q : Nat) (sector : Sector) (ids : List Nat) (s t : CodeState) (row : Row)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.graft q sector ids) s t)
      (hrow : row ∈ graftMintedRows s q sector ids) :
      ExtDerives dMeasure seamCert cs (ExtAnn.gen (i + 1) row.id row.sector row.support)
  | genExtend (i r : Nat) (σ : Sector) (S : List Nat) (delta : List Nat)
      (adds : List (Sector × List Nat)) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.extend delta adds) s t)
      (h : ExtDerives dMeasure seamCert cs (ExtAnn.gen i r σ S)) :
      ExtDerives dMeasure seamCert cs (ExtAnn.gen (i + 1) r σ S)
  | genExtendMint (i : Nat) (delta : List Nat) (adds : List (Sector × List Nat))
      (s t : CodeState) (row : Row)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.extend delta adds) s t)
      (hrow : row ∈ extendMintedRows s adds) :
      ExtDerives dMeasure seamCert cs (ExtAnn.gen (i + 1) row.id row.sector row.support)
  | genPeel (i r r_id : Nat) (σ : Sector) (S : List Nat) (q : Nat) (tau : Sector)
      (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.peel q tau r_id) s t) (hsurvives : r ≠ r_id)
      (h : ExtDerives dMeasure seamCert cs (ExtAnn.gen i r σ S)) :
      ExtDerives dMeasure seamCert cs (ExtAnn.gen (i + 1) r σ (peelSupport q S))
  | genPuncture (i r : Nat) (σ : Sector) (S : List Nat) (q : Nat)
      (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.puncture q) s t) (hsurvives : ¬ S.contains q)
      (h : ExtDerives dMeasure seamCert cs (ExtAnn.gen i r σ S)) :
      ExtDerives dMeasure seamCert cs (ExtAnn.gen (i + 1) r σ S)
  | genHadamard (i r : Nat) (σ : Sector) (S : List Nat) (T : List Nat)
      (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.hadamard T) s t)
      (hglobal : T.Perm s.Q ∨ T = [])
      (h : ExtDerives dMeasure seamCert cs (ExtAnn.gen i r σ S)) :
      ExtDerives dMeasure seamCert cs (ExtAnn.gen (i + 1) r
        (if T.isEmpty then σ else oppositeSector σ) S)
  | genRebase (i r : Nat) (σ : Sector) (S : List Nat) (sector : Sector)
      (matrix : List (List Nat)) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.rebase sector matrix) s t) (hsurvives : σ ≠ sector)
      (h : ExtDerives dMeasure seamCert cs (ExtAnn.gen i r σ S)) :
      ExtDerives dMeasure seamCert cs (ExtAnn.gen (i + 1) r σ S)
  | genHadamardSplit (i : Nat) (T : List Nat) (s t : CodeState) (row : Row)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.hadamard T) s t)
      (hsplit : ProperSubset T s.Q)
      (hrow : row ∈ (splitHadamardState s T).rows) :
      ExtDerives dMeasure seamCert cs (ExtAnn.gen (i + 1) row.id row.sector row.support)
  | genRebaseMint (i : Nat) (sector : Sector) (matrix : List (List Nat))
      (s t : CodeState) (row : Row)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.rebase sector matrix) s t)
      (hrow : row ∈ rebaseMintedRows s sector matrix) :
      ExtDerives dMeasure seamCert cs (ExtAnn.gen (i + 1) row.id row.sector row.support)
  | genCnotSwap (i r : Nat) (σ : Sector) (S : List Nat) (U : List (List Bool))
      (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.cnotSwap U) s t)
      (h : ExtDerives dMeasure seamCert cs (ExtAnn.gen i r σ S)) :
      ExtDerives dMeasure seamCert cs
        (ExtAnn.gen (i + 1) r σ (cnotSwapSupport s.Q U σ S))
  | genSplit (i r : Nat) (σ : Sector) (S : List Nat) (QA R : List Nat) (s t : CodeState)
      (hi : cs[i]? = some s) (hj : cs[i + 1]? = some t)
      (hstep : Eval (Command.split QA R) s t) (hsurvives : r ∉ R)
      (h : ExtDerives dMeasure seamCert cs (ExtAnn.gen i r σ S)) :
      ExtDerives dMeasure seamCert cs (ExtAnn.gen (i + 1) r σ S)

/-- Chain-level models predicate for the expanded operation set. -/
structure ExtModels (dMeasure : ExtMeasure) (cs : List CodeState) (a : ExtAnn) : Prop where
  evalChain : Chain cs
  truth : ExtAnnTrue dMeasure cs a

/-- Closed-term models predicate `(e, m, t) ⊨ a`: the term's expression
    evaluates to `init`, its command unfolds along the unique trace `trace`
    from `init` to `t`, and `a` holds of the chain `init :: trace`. -/
def TermModels (dMeasure : ExtMeasure) (term : ClosedTerm)
    (t : CodeState) (a : ExtAnn) : Prop :=
  ∃ (init : CodeState) (trace : List CodeState),
    EvalExpr term.expr init ∧ Trace term.command init trace t ∧
      ExtAnnTrue dMeasure (init :: trace) a

/-- A `TermModels` witness certifies the evaluation `EvalTerm term t` itself
    (the `Eval` conjunct of §4.11). -/
theorem TermModels.evalTerm {dMeasure : ExtMeasure} {term : ClosedTerm}
    {t : CodeState} {a : ExtAnn} (h : TermModels dMeasure term t a) :
    EvalTerm term t := by
  obtain ⟨_, _, hexpr, htrace, _⟩ := h
  cases term with
  | mk _ _ => exact EvalTerm.eval hexpr htrace.eval

/-- The underlying evaluation trace of `TermModels` is uniquely determined by
    the closed term. -/
theorem TermModels.unique_trace {term : ClosedTerm} {i1 i2 t1 t2 : CodeState}
    {tr1 tr2 : List CodeState}
    (he1 : EvalExpr term.expr i1) (ht1 : Trace term.command i1 tr1 t1)
    (he2 : EvalExpr term.expr i2) (ht2 : Trace term.command i2 tr2 t2) :
    i1 = i2 ∧ tr1 = tr2 ∧ t1 = t2 := by
  have hinit : i1 = i2 := evalExpr_unique he1 he2
  subst hinit
  obtain ⟨htr, ht⟩ := Trace.unique ht1 ht2
  exact ⟨rfl, htr, ht⟩

/-! ## Section 5: Annotated-term soundness over the expanded operation set -/

private theorem extNat_min_interchange (a b c d : ExtNat) :
    ExtNat.min (ExtNat.min a b) (ExtNat.min c d) =
      ExtNat.min (ExtNat.min a c) (ExtNat.min b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp only [ExtNat.min, Nat.min_def] <;> split <;> (try split) <;> (try split) <;>
    (try split) <;> (try split) <;> (try split) <;> (try rfl) <;>
    exact congrArg ExtNat.finite (by omega)

/-- Chain-level soundness (§4.11) for the expanded operation set: every
    derivable annotation is true of the evaluation chain it denotes. -/
theorem ext_judgment_soundness (dMeasure : ExtMeasure)
    (hlaws : ExtMeasureLaws dMeasure)
    (seamCert : SeamCertPolicy) (hcert : SeamCertSound dMeasure seamCert)
    (cs : List CodeState) (hctxt : WellFormedContext cs) (hchain : Chain cs) :
    ∀ a, ExtDerives dMeasure seamCert cs a → ExtModels dMeasure cs a := by
  intro a h
  refine ⟨hchain, ?_⟩
  induction h with
  | instChainState i f s hi =>
      refine ⟨extFieldValue dMeasure f s, ?_, rfl⟩
      simp only [extAexprValue, extAtomValue, hi, Option.map_some]
  | instSkip i f s t hi hj hstep =>
      have heq := eval_skip_eq hstep
      rw [heq] at hj
      refine ⟨extFieldValue dMeasure f s, ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some]
  | instSkipWF i s t hi hj hstep =>
      have heq := eval_skip_eq hstep
      rw [heq] at hj
      exact ⟨s, hj, hctxt s (mem_of_getElem? hi)⟩
  | instDeleteN i r s t hi hj hstep =>
      have heq := eval_delete_eq hstep
      subst heq
      refine ⟨ExtNat.finite s.Q.length, ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue, deleteState]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
  | instDeleteK i r s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hk := stateK_delete_of_eval hstep hwfs (ranksFit_of_wf s hwfs)
      refine ⟨ExtNat.finite (stateK t), ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue, ExtNat.add]
        exact congrArg (Option.some ∘ ExtNat.finite) (by omega)
  | instDeleteKSub i r s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hk := stateK_delete_of_eval hstep hwfs (ranksFit_of_wf s hwfs)
      refine ⟨ExtNat.finite (stateK s), ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue, ExtNat.sub]
        exact congrArg (Option.some ∘ ExtNat.finite) (by omega)
  | instDeleteWF i r s t hi hj hstep =>
      exact ⟨t, hj, wf_of_eval (by trivial) hstep (hctxt s (mem_of_getElem? hi))⟩
  | instDeleteDX i r s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      refine ⟨dMeasure .dX t, dMeasure .dX s, ?_, ?_, (hlaws.delete_le r s t hwfs hstep).1⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
  | instDeleteDZ i r s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      refine ⟨dMeasure .dZ t, dMeasure .dZ s, ?_, ?_, (hlaws.delete_le r s t hwfs hstep).2⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
  | instDeleteD i r s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hd := hlaws.delete_le r s t hwfs hstep
      refine ⟨ExtNat.min (dMeasure .dX t) (dMeasure .dZ t),
        ExtNat.min (dMeasure .dX s) (dMeasure .dZ s), ?_, ?_,
        ExtNat.min_monotone hd.1 hd.2⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
  | instAddN i sector support s t hi hj hstep =>
      have heq := eval_add_eq hstep
      subst heq
      refine ⟨ExtNat.finite s.Q.length, ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue, addState]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
  | instAddK i sector support s t hi hj hstep =>
      have hk := stateK_add_of_eval hstep (hctxt s (mem_of_getElem? hi))
        (ranksFit_of_wf t (hctxt t (mem_of_getElem? hj)))
      refine ⟨ExtNat.finite (stateK s), ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue, ExtNat.add]
        exact congrArg (Option.some ∘ ExtNat.finite) (by omega)
  | instAddKSub i sector support s t hi hj hstep =>
      have hk := stateK_add_of_eval hstep (hctxt s (mem_of_getElem? hi))
        (ranksFit_of_wf t (hctxt t (mem_of_getElem? hj)))
      refine ⟨ExtNat.finite (stateK t), ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue, ExtNat.sub]
        exact congrArg (Option.some ∘ ExtNat.finite) (by omega)
  | instAddWF i sector support s t hi hj hstep =>
      exact ⟨t, hj, wf_of_eval (by trivial) hstep (hctxt s (mem_of_getElem? hi))⟩
  | instAddDX i sector support s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      refine ⟨dMeasure .dX s, dMeasure .dX t, ?_, ?_,
        (hlaws.add_le sector support s t hwfs hstep).1⟩
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue]
  | instAddDZ i sector support s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      refine ⟨dMeasure .dZ s, dMeasure .dZ t, ?_, ?_,
        (hlaws.add_le sector support s t hwfs hstep).2⟩
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue]
  | instAddD i sector support s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hd := hlaws.add_le sector support s t hwfs hstep
      refine ⟨ExtNat.min (dMeasure .dX s) (dMeasure .dZ s),
        ExtNat.min (dMeasure .dX t) (dMeasure .dZ t), ?_, ?_,
        ExtNat.min_monotone hd.1 hd.2⟩
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue]
  | instGraftN i q sector ids s t hi hj hstep =>
      have hnodup := (hctxt s (mem_of_getElem? hi)).1
      have hlen := length_filter_neq q s.Q hnodup (eval_graft_mem hstep)
      have heq := eval_graft_eq hstep
      subst heq
      refine ⟨ExtNat.finite (s.Q.filter (fun x => x ≠ q)).length, ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue, graftState_Q]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue, ExtNat.sub]
        exact congrArg (Option.some ∘ ExtNat.finite) (by omega)
  | instGraftK i q sector ids s t hi hj hstep =>
      have hk := eval_graft_k hstep
      refine ⟨ExtNat.finite (stateK s), ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue, hk]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
  | instGraftWF i q sector ids s t hi hj hstep =>
      exact ⟨t, hj, wf_graft_of_eval hstep (hctxt s (mem_of_getElem? hi))⟩
  | instGraftSpliced i q sector ids s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hrel := (hlaws.graft_rel q sector ids s t hwfs hstep).1
      refine ⟨dMeasure (sectorField sector) s, dMeasure (sectorField sector) t, ?_, ?_, hrel⟩
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue_sectorField]
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue_sectorField]
  | instGraftOpp i q sector ids s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hrel := (hlaws.graft_rel q sector ids s t hwfs hstep).2
      refine ⟨dMeasure (sectorField (oppositeSector sector)) t,
        dMeasure (sectorField (oppositeSector sector)) s, ?_, ?_, hrel⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue_sectorField]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue_sectorField]
  | instGraftFullUpper i q sector ids s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hopp := (hlaws.graft_rel q sector ids s t hwfs hstep).2
      have hle : ExtNat.min (dMeasure .dX t) (dMeasure .dZ t) ≤
          dMeasure (sectorField (oppositeSector sector)) s := by
        cases sector with
        | X => exact ExtNat.le_trans (ExtNat.min_le_right _ _) hopp
        | Z => exact ExtNat.le_trans (ExtNat.min_le_left _ _) hopp
      refine ⟨ExtNat.min (dMeasure .dX t) (dMeasure .dZ t),
        dMeasure (sectorField (oppositeSector sector)) s, ?_, ?_, hle⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue_sectorField]
  | instRebase i f sector matrix s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hval : extFieldValue dMeasure f t = extFieldValue dMeasure f s := by
        cases f with
        | n => exact congrArg ExtNat.finite (eval_rebase_n hstep)
        | k => exact congrArg ExtNat.finite (eval_rebase_k hstep)
        | dX => exact (hlaws.rebase_eq sector matrix s t hwfs hstep).1
        | dZ => exact (hlaws.rebase_eq sector matrix s t hwfs hstep).2
        | d =>
            obtain ⟨hx, hz⟩ := hlaws.rebase_eq sector matrix s t hwfs hstep
            show ExtNat.min (dMeasure .dX t) (dMeasure .dZ t) =
              ExtNat.min (dMeasure .dX s) (dMeasure .dZ s)
            rw [hx, hz]
      refine ⟨extFieldValue dMeasure f s, ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, hval]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some]
  | instRebaseWF i sector matrix s t hi hj hstep =>
      exact ⟨t, hj, wf_of_eval_all hstep (hctxt s (mem_of_getElem? hi))⟩
  | instHadamardN i T s t hi hj hstep =>
      refine ⟨ExtNat.finite s.Q.length, ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue,
          eval_hadamard_n hstep]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
  | instHadamardK i T s t hi hj hstep =>
      refine ⟨ExtNat.finite (stateK s), ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue,
          eval_hadamard_k hstep]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
  | instHadamardD i T s t hi hj hstep hg =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hd : ExtNat.min (dMeasure .dX t) (dMeasure .dZ t) =
          ExtNat.min (dMeasure .dX s) (dMeasure .dZ s) := by
        cases hT : T.isEmpty with
        | true =>
            have hst : t = s := by
              rw [eval_hadamard_eq hstep hg]
              unfold hadamardState
              rw [hT]
              rfl
            rw [hst]
        | false =>
            have hp : CoversQ T s.Q := coversQ_of_perm
              (hg.resolve_right (fun hn => by rw [hn] at hT; exact absurd hT (by decide)))
            obtain ⟨hx, hz⟩ := hlaws.hadamard_swap T s t hwfs hstep hT hp
            rw [hx, hz, ExtNat.min_comm]
      refine ⟨ExtNat.min (dMeasure .dX s) (dMeasure .dZ s), ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue, hd]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
  | instHadamardWF i T s t hi hj hstep =>
      exact ⟨t, hj, wf_of_eval_all hstep (hctxt s (mem_of_getElem? hi))⟩
  | instHadamardEmpty i f T s t hi hj hstep hT =>
      have hst : t = s := by
        rw [eval_hadamard_eq hstep (Or.inr (List.isEmpty_iff.mp hT))]
        unfold hadamardState
        rw [hT]
        rfl
      rw [hst] at hj
      refine ⟨extFieldValue dMeasure f s, ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some]
  | instHadamardSwapDX i T s t hi hj hstep hT =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hx := (hlaws.hadamard_swap T s t hwfs hstep hT.2 hT.1).1
      refine ⟨dMeasure .dZ s, ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue, hx]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
  | instHadamardSwapDZ i T s t hi hj hstep hT =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hz := (hlaws.hadamard_swap T s t hwfs hstep hT.2 hT.1).2
      refine ⟨dMeasure .dX s, ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue, hz]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
  | instPeelN i q τ r_id s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hn := peelEval_Q_length hstep hwfs
      refine ⟨ExtNat.finite (s.Q.length - 1), ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue, hn]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue, ExtNat.sub]
  | instPeelK i q τ r_id s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hk := eval_peel_k hstep hwfs
      refine ⟨ExtNat.finite (stateK s), ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue, hk]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
  | instPeelWF i q τ r_id s t hi hj hstep =>
      exact ⟨t, hj, wf_of_eval_all hstep (hctxt s (mem_of_getElem? hi))⟩
  | instPeelSpliced i q τ r_id s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hsel := (hlaws.peel_rel q τ r_id s t hwfs hstep).1
      refine ⟨dMeasure (sectorField τ) s, dMeasure (sectorField τ) t, ?_, ?_, hsel⟩
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue_sectorField]
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue_sectorField]
  | instPeelOppUpper i q τ r_id s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hopp := (hlaws.peel_rel q τ r_id s t hwfs hstep).2.1
      refine ⟨dMeasure (sectorField (oppositeSector τ)) t,
        dMeasure (sectorField (oppositeSector τ)) s, ?_, ?_, hopp⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue_sectorField]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue_sectorField]
  | instPeelOppLower i q τ r_id s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hlow := (hlaws.peel_rel q τ r_id s t hwfs hstep).2.2
      refine ⟨ExtNat.sub (dMeasure (sectorField (oppositeSector τ)) s) (ExtNat.finite 1),
        dMeasure (sectorField (oppositeSector τ)) t, ?_, ?_, hlow⟩
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue_sectorField]
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue_sectorField]
  | instPeelFullLower i q τ r_id s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      obtain ⟨hsel, _, hlow⟩ := hlaws.peel_rel q τ r_id s t hwfs hstep
      have hle : ExtNat.sub (ExtNat.min (dMeasure .dX s) (dMeasure .dZ s)) (ExtNat.finite 1) ≤
          ExtNat.min (dMeasure .dX t) (dMeasure .dZ t) := by
        cases τ with
        | X => exact ExtNat.sub_one_min_le hsel hlow
        | Z =>
            rw [ExtNat.min_comm (dMeasure .dX s), ExtNat.min_comm (dMeasure .dX t)]
            exact ExtNat.sub_one_min_le hsel hlow
      refine ⟨ExtNat.sub (ExtNat.min (dMeasure .dX s) (dMeasure .dZ s)) (ExtNat.finite 1),
        ExtNat.min (dMeasure .dX t) (dMeasure .dZ t), ?_, ?_, hle⟩
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue]
  | instPeelFullUpper i q τ r_id s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hopp := (hlaws.peel_rel q τ r_id s t hwfs hstep).2.1
      have hle : ExtNat.min (dMeasure .dX t) (dMeasure .dZ t) ≤
          dMeasure (sectorField (oppositeSector τ)) s := by
        cases τ with
        | X => exact ExtNat.le_trans (ExtNat.min_le_right _ _) hopp
        | Z => exact ExtNat.le_trans (ExtNat.min_le_left _ _) hopp
      refine ⟨ExtNat.min (dMeasure .dX t) (dMeasure .dZ t),
        dMeasure (sectorField (oppositeSector τ)) s, ?_, ?_, hle⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue_sectorField]
  | instPunctureN i q s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hn := eval_puncture_n hstep hwfs
      refine ⟨ExtNat.finite (s.Q.length - 1), ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue, hn]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue, ExtNat.sub]
  | instPunctureK i q s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hk := eval_puncture_k hstep hwfs
      refine ⟨ExtNat.finite (stateK t + 1), ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue, ExtNat.add]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue, ExtNat.add, hk]
  | instPunctureWF i q s t hi hj hstep =>
      exact ⟨t, hj, wf_of_eval_all hstep (hctxt s (mem_of_getElem? hi))⟩
  | instExtendN i delta adds s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hn := eval_extend_n hstep hwfs
      refine ⟨ExtNat.finite (s.Q.length + delta.length), ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue, hn]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue, ExtNat.add]
  | instExtendK i delta adds s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hk := eval_extend_k hstep hwfs
      refine ⟨ExtNat.finite (stateK t + adds.length), ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue, ExtNat.add]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue, ExtNat.add, hk]
  | instExtendWF i delta adds s t hi hj hstep =>
      exact ⟨t, hj, wf_of_eval_all hstep (hctxt s (mem_of_getElem? hi))⟩
  | instExtendNilDX i adds s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      refine ⟨dMeasure .dX s, dMeasure .dX t, ?_, ?_,
        (hlaws.extend_nil_le adds s t hwfs hstep).1⟩
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue]
  | instExtendNilDZ i adds s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      refine ⟨dMeasure .dZ s, dMeasure .dZ t, ?_, ?_,
        (hlaws.extend_nil_le adds s t hwfs hstep).2⟩
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue]
  | instExtendNilD i adds s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hd := hlaws.extend_nil_le adds s t hwfs hstep
      refine ⟨ExtNat.min (dMeasure .dX s) (dMeasure .dZ s),
        ExtNat.min (dMeasure .dX t) (dMeasure .dZ t), ?_, ?_,
        ExtNat.min_monotone hd.1 hd.2⟩
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue]
  | instCnotSwapN i U s t hi hj hstep =>
      have hn := eval_cnotSwap_n hstep
      refine ⟨ExtNat.finite s.Q.length, ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue, hn]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
  | instCnotSwapK i U s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hk := eval_cnotSwap_k hstep hwfs
      refine ⟨ExtNat.finite (stateK s), ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue, hk]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
  | instCnotSwapWF i U s t hi hj hstep =>
      exact ⟨t, hj, wf_of_eval_all hstep (hctxt s (mem_of_getElem? hi))⟩
  | instSplitN i QA R s t hi hj hstep =>
      refine ⟨ExtNat.finite s.Q.length, ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue,
          eval_split_n hstep]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
  | instSplitK i QA R s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hk := eval_split_k hstep hwfs
      refine ⟨ExtNat.finite (stateK s + R.length), ?_, ?_⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue, hk]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue, ExtNat.add]
  | instSplitWF i QA R s t hi hj hstep =>
      exact ⟨t, hj, wf_of_eval_all hstep (hctxt s (mem_of_getElem? hi))⟩
  | instSplitDX i QA R s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hd : dMeasure .dX t ≤ dMeasure .dX s ∧ dMeasure .dZ t ≤ dMeasure .dZ s := by
        cases hstep with
        | split _ _ hRnd hRdisp _ hs' =>
            subst hs'
            have hloop : ∀ (Rs : List Nat) (u : CodeState),
                EncodingWellFormed u → Rs.Nodup → (∀ r ∈ Rs, DisplayedGenerator r u) →
                dMeasure .dX (deleteAll u Rs) ≤ dMeasure .dX u ∧
                dMeasure .dZ (deleteAll u Rs) ≤ dMeasure .dZ u := by
              intro Rs
              induction Rs with
              | nil => intro u _ _ _; exact ⟨ExtNat.le_refl _, ExtNat.le_refl _⟩
              | cons r rest ih =>
                  intro u hwfU hndU hdispU
                  obtain ⟨row, hmem, hid⟩ := hdispU r List.mem_cons_self
                  have hind : IndependentGenerator r u := hid ▸ hwfU.2.2.2.2.2.2.2 row hmem
                  have h1 : Eval (Command.delete r) u (deleteState u r) :=
                    Eval.delete ⟨row, hmem, hid⟩ hind rfl
                  obtain ⟨hx1, hz1⟩ := hlaws.delete_le r u (deleteState u r) hwfU h1
                  have hnd' := List.nodup_cons.mp hndU
                  obtain ⟨hx2, hz2⟩ := ih (deleteState u r) (wf_deleteState u r hwfU) hnd'.2
                    (fun r' hr' => by
                      obtain ⟨row', hmem', hid'⟩ := hdispU r' (List.mem_cons_of_mem _ hr')
                      refine ⟨row', ?_, hid'⟩
                      show row' ∈ u.rows.filter (fun row => row.id ≠ r)
                      exact List.mem_filter.mpr ⟨hmem', decide_eq_true (fun h =>
                        hnd'.1 (by rw [← h, hid']; exact hr'))⟩)
                  exact ⟨ExtNat.le_trans hx2 hx1, ExtNat.le_trans hz2 hz1⟩
            exact hloop R s hwfs hRnd hRdisp
      refine ⟨dMeasure .dX t, dMeasure .dX s, ?_, ?_, hd.1⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
  | instSplitDZ i QA R s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hd : dMeasure .dX t ≤ dMeasure .dX s ∧ dMeasure .dZ t ≤ dMeasure .dZ s := by
        cases hstep with
        | split _ _ hRnd hRdisp _ hs' =>
            subst hs'
            have hloop : ∀ (Rs : List Nat) (u : CodeState),
                EncodingWellFormed u → Rs.Nodup → (∀ r ∈ Rs, DisplayedGenerator r u) →
                dMeasure .dX (deleteAll u Rs) ≤ dMeasure .dX u ∧
                dMeasure .dZ (deleteAll u Rs) ≤ dMeasure .dZ u := by
              intro Rs
              induction Rs with
              | nil => intro u _ _ _; exact ⟨ExtNat.le_refl _, ExtNat.le_refl _⟩
              | cons r rest ih =>
                  intro u hwfU hndU hdispU
                  obtain ⟨row, hmem, hid⟩ := hdispU r List.mem_cons_self
                  have hind : IndependentGenerator r u := hid ▸ hwfU.2.2.2.2.2.2.2 row hmem
                  have h1 : Eval (Command.delete r) u (deleteState u r) :=
                    Eval.delete ⟨row, hmem, hid⟩ hind rfl
                  obtain ⟨hx1, hz1⟩ := hlaws.delete_le r u (deleteState u r) hwfU h1
                  have hnd' := List.nodup_cons.mp hndU
                  obtain ⟨hx2, hz2⟩ := ih (deleteState u r) (wf_deleteState u r hwfU) hnd'.2
                    (fun r' hr' => by
                      obtain ⟨row', hmem', hid'⟩ := hdispU r' (List.mem_cons_of_mem _ hr')
                      refine ⟨row', ?_, hid'⟩
                      show row' ∈ u.rows.filter (fun row => row.id ≠ r)
                      exact List.mem_filter.mpr ⟨hmem', decide_eq_true (fun h =>
                        hnd'.1 (by rw [← h, hid']; exact hr'))⟩)
                  exact ⟨ExtNat.le_trans hx2 hx1, ExtNat.le_trans hz2 hz1⟩
            exact hloop R s hwfs hRnd hRdisp
      refine ⟨dMeasure .dZ t, dMeasure .dZ s, ?_, ?_, hd.2⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
  | instSplitD i QA R s t hi hj hstep =>
      have hwfs := hctxt s (mem_of_getElem? hi)
      have hd : dMeasure .dX t ≤ dMeasure .dX s ∧ dMeasure .dZ t ≤ dMeasure .dZ s := by
        cases hstep with
        | split _ _ hRnd hRdisp _ hs' =>
            subst hs'
            have hloop : ∀ (Rs : List Nat) (u : CodeState),
                EncodingWellFormed u → Rs.Nodup → (∀ r ∈ Rs, DisplayedGenerator r u) →
                dMeasure .dX (deleteAll u Rs) ≤ dMeasure .dX u ∧
                dMeasure .dZ (deleteAll u Rs) ≤ dMeasure .dZ u := by
              intro Rs
              induction Rs with
              | nil => intro u _ _ _; exact ⟨ExtNat.le_refl _, ExtNat.le_refl _⟩
              | cons r rest ih =>
                  intro u hwfU hndU hdispU
                  obtain ⟨row, hmem, hid⟩ := hdispU r List.mem_cons_self
                  have hind : IndependentGenerator r u := hid ▸ hwfU.2.2.2.2.2.2.2 row hmem
                  have h1 : Eval (Command.delete r) u (deleteState u r) :=
                    Eval.delete ⟨row, hmem, hid⟩ hind rfl
                  obtain ⟨hx1, hz1⟩ := hlaws.delete_le r u (deleteState u r) hwfU h1
                  have hnd' := List.nodup_cons.mp hndU
                  obtain ⟨hx2, hz2⟩ := ih (deleteState u r) (wf_deleteState u r hwfU) hnd'.2
                    (fun r' hr' => by
                      obtain ⟨row', hmem', hid'⟩ := hdispU r' (List.mem_cons_of_mem _ hr')
                      refine ⟨row', ?_, hid'⟩
                      show row' ∈ u.rows.filter (fun row => row.id ≠ r)
                      exact List.mem_filter.mpr ⟨hmem', decide_eq_true (fun h =>
                        hnd'.1 (by rw [← h, hid']; exact hr'))⟩)
                  exact ⟨ExtNat.le_trans hx2 hx1, ExtNat.le_trans hz2 hz1⟩
            exact hloop R s hwfs hRnd hRdisp
      refine ⟨ExtNat.min (dMeasure .dX t) (dMeasure .dZ t),
        ExtNat.min (dMeasure .dX s) (dMeasure .dZ s), ?_, ?_,
        ExtNat.min_monotone hd.1 hd.2⟩
      · simp only [extAexprValue, extAtomValue, hj, Option.map_some, extFieldValue]
      · simp only [extAexprValue, extAtomValue, hi, Option.map_some, extFieldValue]
  | instExprWF e s he hbase =>
      exact wf_of_evalExpr he hbase
  | instDirectSumN e1 e2 s1 s2 s h1 h2 hsum =>
      cases hsum with
      | directSum _ _ he1 he2 =>
          have h1' := evalExpr_unique h1 he1
          have h2' := evalExpr_unique h2 he2
          subst h1'; subst h2'
          refine ⟨ExtNat.finite (s1.Q.length + s2.Q.length), ?_, rfl⟩
          simp only [extAexprValue, extAtomValue, extFieldValue, directSumState, List.length_append]
  | instDirectSumK e1 e2 s1 s2 s h1 h2 hsum hbase1 hbase2 =>
      cases hsum with
      | directSum hQ hU he1 he2 =>
          have h1' := evalExpr_unique h1 he1
          have h2' := evalExpr_unique h2 he2
          subst h1'; subst h2'
          have hk := stateK_directSum (wf_of_evalExpr h1 hbase1) (wf_of_evalExpr h2 hbase2) hQ hU
          refine ⟨ExtNat.finite (stateK s1 + stateK s2), ?_, rfl⟩
          simp only [extAexprValue, extAtomValue, extFieldValue, hk]
  | instDirectSumDX e1 e2 s1 s2 s h1 h2 hsum hbase1 hbase2 =>
      cases hsum with
      | directSum hQ hU he1 he2 =>
          have h1' := evalExpr_unique h1 he1
          have h2' := evalExpr_unique h2 he2
          subst h1'; subst h2'
          have hx := (hlaws.directSum_eq s1 s2 (wf_of_evalExpr h1 hbase1)
            (wf_of_evalExpr h2 hbase2) hQ hU).1
          refine ⟨ExtNat.min (dMeasure .dX s1) (dMeasure .dX s2), ?_, rfl⟩
          simp only [extAexprValue, extAtomValue, extFieldValue, hx]
  | instDirectSumDZ e1 e2 s1 s2 s h1 h2 hsum hbase1 hbase2 =>
      cases hsum with
      | directSum hQ hU he1 he2 =>
          have h1' := evalExpr_unique h1 he1
          have h2' := evalExpr_unique h2 he2
          subst h1'; subst h2'
          have hz := (hlaws.directSum_eq s1 s2 (wf_of_evalExpr h1 hbase1)
            (wf_of_evalExpr h2 hbase2) hQ hU).2
          refine ⟨ExtNat.min (dMeasure .dZ s1) (dMeasure .dZ s2), ?_, rfl⟩
          simp only [extAexprValue, extAtomValue, extFieldValue, hz]
  | instDirectSumD e1 e2 s1 s2 s h1 h2 hsum hbase1 hbase2 =>
      cases hsum with
      | directSum hQ hU he1 he2 =>
          have h1' := evalExpr_unique h1 he1
          have h2' := evalExpr_unique h2 he2
          subst h1'; subst h2'
          obtain ⟨hx, hz⟩ := hlaws.directSum_eq s1 s2 (wf_of_evalExpr h1 hbase1)
            (wf_of_evalExpr h2 hbase2) hQ hU
          refine ⟨ExtNat.min (ExtNat.min (dMeasure .dX s1) (dMeasure .dZ s1))
            (ExtNat.min (dMeasure .dX s2) (dMeasure .dZ s2)), ?_, rfl⟩
          simp only [extAexprValue, extAtomValue, extFieldValue, hx, hz, extNat_min_interchange]
  | instGlueN e1 e2 seams s1 s2 s h1 h2 hglue =>
      cases hglue with
      | glue _ _ _ _ he1 he2 =>
          have h1' := evalExpr_unique h1 he1
          have h2' := evalExpr_unique h2 he2
          subst h1'; subst h2'
          refine ⟨ExtNat.finite (s1.Q.length + s2.Q.length), ?_, rfl⟩
          simp only [extAexprValue, extAtomValue, extFieldValue, glueState_Q_length]
  | instGlueK e1 e2 seams s1 s2 s h1 h2 hglue hbase1 hbase2 =>
      cases hglue with
      | glue _ _ hwfG _ he1 he2 =>
          have h1' := evalExpr_unique h1 he1
          have h2' := evalExpr_unique h2 he2
          subst h1'; subst h2'
          have hk := stateK_glueState (wf_of_evalExpr h1 hbase1) (wf_of_evalExpr h2 hbase2) hwfG
          refine ⟨ExtNat.finite (stateK s1 + stateK s2), ?_, rfl⟩
          simp only [extAexprValue, extAtomValue, extFieldValue, ExtNat.add, hk]
  | instGlueDX e1 e2 seams s1 s2 s h1 h2 hglue hbase1 hbase2 =>
      cases hglue with
      | glue hQ hU hwfG _ he1 he2 =>
          have h1' := evalExpr_unique h1 he1
          have h2' := evalExpr_unique h2 he2
          subst h1'; subst h2'
          have hx := (hlaws.glue_ge s1 s2 seams (wf_of_evalExpr h1 hbase1)
            (wf_of_evalExpr h2 hbase2) hQ hU hwfG).1
          exact ⟨ExtNat.min (dMeasure .dX s1) (dMeasure .dX s2),
            dMeasure .dX (glueState s1 s2 seams), rfl, rfl, hx⟩
  | instGlueDZ e1 e2 seams s1 s2 s h1 h2 hglue hbase1 hbase2 =>
      cases hglue with
      | glue hQ hU hwfG _ he1 he2 =>
          have h1' := evalExpr_unique h1 he1
          have h2' := evalExpr_unique h2 he2
          subst h1'; subst h2'
          have hz := (hlaws.glue_ge s1 s2 seams (wf_of_evalExpr h1 hbase1)
            (wf_of_evalExpr h2 hbase2) hQ hU hwfG).2
          exact ⟨ExtNat.min (dMeasure .dZ s1) (dMeasure .dZ s2),
            dMeasure .dZ (glueState s1 s2 seams), rfl, rfl, hz⟩
  | instGlueD e1 e2 seams s1 s2 s h1 h2 hglue hbase1 hbase2 =>
      cases hglue with
      | glue hQ hU hwfG _ he1 he2 =>
          have h1' := evalExpr_unique h1 he1
          have h2' := evalExpr_unique h2 he2
          subst h1'; subst h2'
          obtain ⟨hx, hz⟩ := hlaws.glue_ge s1 s2 seams (wf_of_evalExpr h1 hbase1)
            (wf_of_evalExpr h2 hbase2) hQ hU hwfG
          have hd : ExtNat.min (ExtNat.min (dMeasure .dX s1) (dMeasure .dZ s1))
              (ExtNat.min (dMeasure .dX s2) (dMeasure .dZ s2)) ≤
              ExtNat.min (dMeasure .dX (glueState s1 s2 seams))
                (dMeasure .dZ (glueState s1 s2 seams)) := by
            rw [extNat_min_interchange]
            exact ExtNat.min_monotone hx hz
          exact ⟨ExtNat.min (ExtNat.min (dMeasure .dX s1) (dMeasure .dZ s1))
            (ExtNat.min (dMeasure .dX s2) (dMeasure .dZ s2)),
            ExtNat.min (dMeasure .dX (glueState s1 s2 seams))
              (dMeasure .dZ (glueState s1 s2 seams)), rfl, rfl, hd⟩
  | instGlueCertDZ e1 e2 seams s1 s2 s h1 h2 hglue hbase1 hbase2 hsc =>
      cases hglue with
      | glue hQ hU hwfG _ he1 he2 =>
          have h1' := evalExpr_unique h1 he1
          have h2' := evalExpr_unique h2 he2
          subst h1'; subst h2'
          have heq := hcert s1 s2 seams (wf_of_evalExpr h1 hbase1)
            (wf_of_evalExpr h2 hbase2) hQ hU hwfG hsc
          refine ⟨ExtNat.min (dMeasure .dZ s1) (dMeasure .dZ s2), ?_, rfl⟩
          simp only [extAexprValue, extAtomValue, extFieldValue, heq]
  | instHgpN H1 H2 s h =>
      refine ⟨ExtNat.finite s.Q.length, rfl, ?_⟩
      simp only [extAexprValue, evalExpr_hgp_n h]
  | instLiftN orders A B s h =>
      refine ⟨ExtNat.finite s.Q.length, rfl, ?_⟩
      simp only [extAexprValue, evalExpr_lift_n h]
  | instTwoblockN orders a b s h =>
      refine ⟨ExtNat.finite s.Q.length, rfl, ?_⟩
      simp only [extAexprValue, evalExpr_twoblock_n h]
  | instTwoblockK orders a b s h =>
      refine ⟨ExtNat.finite (stateK s), rfl, ?_⟩
      simp only [extAexprValue, evalExpr_twoblock_k h]
  | instConcatN eO eI blocks repsX repsZ sO sI s hO hI h =>
      refine ⟨ExtNat.finite s.Q.length, rfl, ?_⟩
      simp only [extAexprValue, evalExpr_concat_n_gen hO hI h]
  | instConcatK eO eI blocks repsX repsZ sO s hO h =>
      obtain ⟨sO', hO', hk⟩ := evalExpr_concat_k h
      have hsO := evalExpr_unique hO hO'
      subst hsO
      refine ⟨ExtNat.finite (stateK sO), ?_, rfl⟩
      simp only [extAexprValue, extAtomValue, extFieldValue, hk]
  | instProductN eA eB sA sB s hA hB h =>
      refine ⟨ExtNat.finite s.Q.length, rfl, ?_⟩
      simp only [extAexprValue, evalExpr_product_n_gen hA hB h]
  | instDoubleN e wiring conj sC s hC h =>
      have hn := evalExpr_double_n_gen hC h
      refine ⟨ExtNat.finite (sC.Q.length + sC.Q.length), ?_, rfl⟩
      simp only [extAexprValue, extAtomValue, extFieldValue]
      exact congrArg (Option.some ∘ ExtNat.finite) (by omega)
  | instDoubleEmptyK e conj sC s hC h =>
      obtain ⟨sC', hC', hk⟩ := evalExpr_double_empty_k h
      have hsC := evalExpr_unique hC hC'
      subst hsC
      refine ⟨ExtNat.finite (stateK sC + stateK sC), ?_, rfl⟩
      simp only [extAexprValue, extAtomValue, extFieldValue]
      exact congrArg (Option.some ∘ ExtNat.finite) (by omega)
  | instBalancedN orders H1 H2 rows1 cols1 rows2 cols2 s h =>
      refine ⟨ExtNat.finite s.Q.length, rfl, ?_⟩
      simp only [extAexprValue, evalExpr_balanced_n h]
  | instBalancedK orders H1 H2 rows1 cols1 rows2 cols2 s h =>
      refine ⟨ExtNat.finite (stateK s), rfl, ?_⟩
      simp only [extAexprValue, evalExpr_balanced_k h]
  | instLiftTableN t A B s h =>
      refine ⟨ExtNat.finite s.Q.length, rfl, ?_⟩
      simp only [extAexprValue, evalExpr_liftTable_n h]
  | instTwoblockTableN t a b s h =>
      refine ⟨ExtNat.finite s.Q.length, rfl, ?_⟩
      simp only [extAexprValue, evalExpr_twoblockTable_n h]
  | instBalancedTableN t H1 H2 rows1 cols1 rows2 cols2 s h =>
      refine ⟨ExtNat.finite s.Q.length, rfl, ?_⟩
      simp only [extAexprValue, evalExpr_balancedTable_n h]
  | instTannerN n LX LZ viewsX viewsZ s h =>
      refine ⟨ExtNat.finite s.Q.length, rfl, ?_⟩
      simp only [extAexprValue, evalExpr_tanner_n h]
  | instTannerK n LX LZ viewsX viewsZ s h =>
      refine ⟨ExtNat.finite (stateK s), rfl, ?_⟩
      simp only [extAexprValue, evalExpr_tanner_k h]
  | instTileN tiles placements idents removed s h =>
      refine ⟨ExtNat.finite s.Q.length, rfl, ?_⟩
      simp only [extAexprValue, evalExpr_tile_n h]
  | instTileK tiles placements idents removed s h =>
      refine ⟨ExtNat.finite (stateK s), rfl, ?_⟩
      simp only [extAexprValue, evalExpr_tile_k h]
  | instNestedN HX HZ s h =>
      refine ⟨ExtNat.finite s.Q.length, rfl, ?_⟩
      simp only [extAexprValue, evalExpr_nested_n h]
  | instConeN DA DB F1 F0 s h =>
      refine ⟨ExtNat.finite s.Q.length, rfl, ?_⟩
      simp only [extAexprValue, evalExpr_cone_n h]
  | instConeK DA DB F1 F0 s h =>
      refine ⟨ExtNat.finite (stateK s), rfl, ?_⟩
      simp only [extAexprValue, evalExpr_cone_k h]
  | instEmptyN s h =>
      refine ⟨ExtNat.finite s.Q.length, rfl, ?_⟩
      simp only [extAexprValue, evalExpr_empty_n h]
  | instEmptyK s h =>
      refine ⟨ExtNat.finite (stateK s), rfl, ?_⟩
      simp only [extAexprValue, evalExpr_empty_k h]
  | instFreeN qs s h =>
      refine ⟨ExtNat.finite s.Q.length, rfl, ?_⟩
      simp only [extAexprValue, evalExpr_free_n h]
  | instFreeK qs s h =>
      refine ⟨ExtNat.finite (stateK s), rfl, ?_⟩
      simp only [extAexprValue, evalExpr_free_k h]
  | instPullbackN e1 e2 eI phi1 phi2 s1 s2 sI s h1 h2 hI h =>
      refine ⟨ExtNat.finite s.Q.length, rfl, ?_⟩
      simp only [extAexprValue, evalExpr_pullback_n_gen h1 h2 hI h]
  | instPushoutN e1 e2 eS psi1 psi2 s1 s2 sS s h1 h2 hS h =>
      refine ⟨ExtNat.finite s.Q.length, rfl, ?_⟩
      simp only [extAexprValue, evalExpr_pushout_n_gen h1 h2 hS h]
  | instPairPartitionN p BX BZ s h =>
      refine ⟨ExtNat.finite s.Q.length, rfl, ?_⟩
      simp only [extAexprValue, evalExpr_pairPartition_n h]
  | instPpScaleN e0 P BX BZ s h =>
      refine ⟨ExtNat.finite s.Q.length, rfl, ?_⟩
      simp only [extAexprValue, evalExpr_ppScale_n h]
  | transit_le_le _ _ _ _ _ ih1 ih2 =>
      obtain ⟨v, w, hxv, hyw, hvw⟩ := ih1
      obtain ⟨w2, u, hyw2, hzu, hw2u⟩ := ih2
      have hw := extAexprValue_determinism hyw hyw2
      subst hw
      exact ⟨v, u, hxv, hzu, ExtNat.le_trans hvw hw2u⟩
  | transit_le_eq _ _ _ _ _ ih1 ih2 =>
      obtain ⟨v, w, hxv, hyw, hvw⟩ := ih1
      obtain ⟨v2, hyv2, hzv2⟩ := ih2
      have hw := extAexprValue_determinism hyw hyv2
      subst hw
      exact ⟨v, w, hxv, hzv2, hvw⟩
  | transit_eq_le _ _ _ _ _ ih1 ih2 =>
      obtain ⟨v, hxv, hyv⟩ := ih1
      obtain ⟨v2, w2, hyv2, hzv2, hv2w2⟩ := ih2
      have hv := extAexprValue_determinism hyv hyv2
      subst hv
      exact ⟨v, w2, hxv, hzv2, hv2w2⟩
  | transit_eq_eq _ _ _ _ _ ih1 ih2 =>
      obtain ⟨v, hxv, hyv⟩ := ih1
      obtain ⟨v2, hyv2, hzv2⟩ := ih2
      have hv := extAexprValue_determinism hyv hyv2
      subst hv
      exact ⟨v, hxv, hzv2⟩
  | min_le_left _ _ hx hy =>
      obtain ⟨v, hxv⟩ := hx
      obtain ⟨w, hyw⟩ := hy
      refine ⟨ExtNat.min v w, v, ?_, hxv, ExtNat.min_le_left v w⟩
      simp only [extAexprValue, hxv, hyw]
  | min_le_right _ _ hx hy =>
      obtain ⟨v, hxv⟩ := hx
      obtain ⟨w, hyw⟩ := hy
      refine ⟨ExtNat.min v w, w, ?_, hyw, ExtNat.min_le_right v w⟩
      simp only [extAexprValue, hxv, hyw]
  | le_min _ _ _ _ _ ih1 ih2 =>
      obtain ⟨vt, vx, htv, hxv, hle1⟩ := ih1
      obtain ⟨v2, vy, htv2, hyv, hle2⟩ := ih2
      have heq := extAexprValue_determinism htv htv2
      subst heq
      refine ⟨vt, ExtNat.min vx vy, htv, ?_, ExtNat.le_min hle1 hle2⟩
      simp only [extAexprValue, hxv, hyv]
  | le_refl _ hx =>
      obtain ⟨v, hxv⟩ := hx
      exact ⟨v, v, hxv, hxv, ExtNat.le_refl v⟩
  | eq_refl _ hx =>
      obtain ⟨v, hxv⟩ := hx
      exact ⟨v, hxv, hxv⟩
  | eq_sym _ _ _ ih =>
      obtain ⟨v, hxv, hyv⟩ := ih
      exact ⟨v, hyv, hxv⟩
  | genInput _ _ _ s h0 hrow => exact ⟨s, h0, hrow⟩
  | genMint _ _ _ _ t _ hj hstep =>
      refine ⟨t, hj, ?_⟩
      rw [eval_add_eq hstep]
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  | genSkip _ _ _ _ s t hi hj hstep _ ih =>
      obtain ⟨s0, hs0, hmem⟩ := ih
      have hs : s0 = s := Option.some.inj (hs0.symm.trans hi)
      refine ⟨t, hj, ?_⟩
      rw [eval_skip_eq hstep, ← hs]
      exact hmem
  | genDelete _ _ _ _ _ s t hi hj hstep hsurvives _ ih =>
      obtain ⟨s0, hs0, hmem⟩ := ih
      have hs : s0 = s := Option.some.inj (hs0.symm.trans hi)
      refine ⟨t, hj, ?_⟩
      rw [eval_delete_eq hstep, ← hs]
      exact List.mem_filter.mpr ⟨hmem, decide_eq_true hsurvives⟩
  | genAdd _ _ _ _ _ _ s t hi hj hstep _ ih =>
      obtain ⟨s0, hs0, hmem⟩ := ih
      have hs : s0 = s := Option.some.inj (hs0.symm.trans hi)
      refine ⟨t, hj, ?_⟩
      rw [eval_add_eq hstep, ← hs]
      exact List.mem_append_left _ hmem
  | genGraft _ _ _ _ _ _ _ s t hi hj hstep hsurvives _ ih =>
      obtain ⟨s0, hs0, hmem⟩ := ih
      have hs : s0 = s := Option.some.inj (hs0.symm.trans hi)
      refine ⟨t, hj, ?_⟩
      rw [eval_graft_eq hstep, ← hs]
      exact mem_graftState_of_survives hmem hsurvives
  | genGraftMint _ _ _ _ _ t _ _ hj hstep hrow =>
      refine ⟨t, hj, ?_⟩
      rw [eval_graft_eq hstep]
      exact mem_graftState_of_minted hrow
  | genExtend _ _ _ _ _ _ s t hi hj hstep _ ih =>
      obtain ⟨s0, hs0, hmem⟩ := ih
      have hs : s0 = s := Option.some.inj (hs0.symm.trans hi)
      refine ⟨t, hj, ?_⟩
      rw [eval_extend_eq hstep, ← hs]
      exact List.mem_append_left _ hmem
  | genExtendMint _ _ _ _ t _ _ hj hstep hrow =>
      refine ⟨t, hj, ?_⟩
      rw [eval_extend_eq hstep]
      exact List.mem_append_right _ hrow
  | genPeel _ r r_id σ S q _ s t hi hj hstep hsurvives _ ih =>
      obtain ⟨s0, hs0, hmem⟩ := ih
      have hs : s0 = s := Option.some.inj (hs0.symm.trans hi)
      refine ⟨t, hj, ?_⟩
      rw [eval_peel_eq hstep]
      have htr : shortenRow q { id := r, sector := σ, support := S } ∈
          (s.rows.filter (fun row => row.id ≠ r_id)).map (shortenRow q) :=
        List.mem_map.mpr ⟨{ id := r, sector := σ, support := S },
          ⟨List.mem_filter.mpr ⟨hs ▸ hmem, decide_eq_true hsurvives⟩, rfl⟩⟩
      have heq : shortenRow q { id := r, sector := σ, support := S } =
          { id := r, sector := σ, support := peelSupport q S } := by
        unfold shortenRow peelSupport
        split <;> rfl
      rw [heq] at htr
      exact htr
  | genPuncture _ _ _ _ _ s t hi hj hstep hsurvives _ ih =>
      obtain ⟨s0, hs0, hmem⟩ := ih
      have hs : s0 = s := Option.some.inj (hs0.symm.trans hi)
      refine ⟨t, hj, ?_⟩
      rw [eval_puncture_eq hstep]
      exact List.mem_filter.mpr ⟨hs ▸ hmem, decide_eq_true hsurvives⟩
  | genHadamard _ r σ S T s t hi hj hstep hg _ ih =>
      obtain ⟨s0, hs0, hmem⟩ := ih
      have hs : s0 = s := Option.some.inj (hs0.symm.trans hi)
      refine ⟨t, hj, ?_⟩
      rw [eval_hadamard_eq hstep hg]
      cases hT : T.isEmpty with
      | true =>
          have ht : hadamardState s T = s := by simp [hadamardState, hT]
          rw [ht, ← hs]
          simpa [hT] using hmem
      | false =>
          have ht : hadamardState s T = swapState s := by simp [hadamardState, hT]
          rw [ht]
          exact List.mem_map.mpr
            ⟨{ id := r, sector := σ, support := S }, hs ▸ hmem, by simp [swapRow]⟩
  | genRebase _ _ _ _ _ _ s t hi hj hstep hsurvives _ ih =>
      obtain ⟨s0, hs0, hmem⟩ := ih
      have hs : s0 = s := Option.some.inj (hs0.symm.trans hi)
      refine ⟨t, hj, ?_⟩
      rw [eval_rebase_eq hstep]
      exact List.mem_append_left _ (List.mem_filter.mpr ⟨hs ▸ hmem, decide_eq_true hsurvives⟩)
  | genHadamardSplit _ T s t _ _ hj hstep hsplit hrow =>
      refine ⟨t, hj, ?_⟩
      rw [eval_hadamardSplit_eq hstep hsplit]
      exact hrow
  | genRebaseMint _ _ _ _ t _ _ hj hstep hrow =>
      refine ⟨t, hj, ?_⟩
      rw [eval_rebase_eq hstep]
      exact List.mem_append_right _ hrow
  | genCnotSwap _ r σ S U s t hi hj hstep _ ih =>
      obtain ⟨s0, hs0, hmem⟩ := ih
      have hs : s0 = s := Option.some.inj (hs0.symm.trans hi)
      refine ⟨t, hj, ?_⟩
      rw [eval_cnotSwap_eq hstep]
      exact List.mem_map.mpr
        ⟨{ id := r, sector := σ, support := S }, hs ▸ hmem, rfl⟩
  | genSplit _ _ _ _ _ R s t hi hj hstep hsurvives _ ih =>
      obtain ⟨s0, hs0, hmem⟩ := ih
      have hs : s0 = s := Option.some.inj (hs0.symm.trans hi)
      refine ⟨t, hj, ?_⟩
      rw [eval_split_eq hstep]
      exact (mem_deleteAll_rows R s _).mpr ⟨hs ▸ hmem, hsurvives⟩

/-- Soundness from the head state's well-formedness alone. -/
theorem ext_judgment_soundness_of_head (dMeasure : ExtMeasure)
    (hlaws : ExtMeasureLaws dMeasure)
    (seamCert : SeamCertPolicy) (hcert : SeamCertSound dMeasure seamCert)
    (cs : List CodeState) (hchain : Chain cs)
    (hhead : ∀ s, cs.head? = some s → EncodingWellFormed s) :
    ∀ a, ExtDerives dMeasure seamCert cs a → ExtModels dMeasure cs a :=
  ext_judgment_soundness dMeasure hlaws seamCert hcert cs
    (hchain.wellFormedContext hhead) hchain

/-- Soundness over the trace of an evaluation: no chain hypothesis. -/
theorem ext_judgment_soundness_of_trace (dMeasure : ExtMeasure)
    (hlaws : ExtMeasureLaws dMeasure)
    (seamCert : SeamCertPolicy) (hcert : SeamCertSound dMeasure seamCert)
    {m : Command} {s t : CodeState} {cs : List CodeState}
    (htrace : Trace m s cs t) (hwf : EncodingWellFormed s) :
    ∀ a, ExtDerives dMeasure seamCert (s :: cs) a → ExtModels dMeasure (s :: cs) a :=
  ext_judgment_soundness_of_head dMeasure hlaws seamCert hcert (s :: cs) htrace.chain
    (fun x hx => by
      have hxs : s = x := Option.some.inj hx
      rw [← hxs]
      exact hwf)

/-- Soundness from a command evaluation `Eval m s t`. -/
theorem ext_judgment_soundness_of_eval (dMeasure : ExtMeasure)
    (hlaws : ExtMeasureLaws dMeasure)
    (seamCert : SeamCertPolicy) (hcert : SeamCertSound dMeasure seamCert)
    {m : Command} {s t : CodeState}
    (heval : Eval m s t) (hwf : EncodingWellFormed s) :
    ∃ cs, Trace m s cs t ∧
      ∀ a, ExtDerives dMeasure seamCert (s :: cs) a → ExtModels dMeasure (s :: cs) a := by
  obtain ⟨cs, hcs⟩ := trace_of_eval m heval
  exact ⟨cs, hcs, ext_judgment_soundness_of_trace dMeasure hlaws seamCert hcert hcs hwf⟩

/-- Soundness (§4.11) for a closed term over the expanded operation set:
    takes only `EvalTerm term t` and `ExprBaseWF term.expr` (vacuous for
    constructor-built terms), and concludes `TermModels` for every annotation
    derivable over the term's unique evaluation trace. -/
theorem ext_judgment_soundness_of_term (dMeasure : ExtMeasure)
    (hlaws : ExtMeasureLaws dMeasure)
    (seamCert : SeamCertPolicy) (hcert : SeamCertSound dMeasure seamCert)
    {term : ClosedTerm} {t : CodeState}
    (heval : EvalTerm term t) (hbase : ExprBaseWF term.expr) :
    ∃ s cs, EvalExpr term.expr s ∧ Trace term.command s cs t ∧
      ∀ a, ExtDerives dMeasure seamCert (s :: cs) a →
        TermModels dMeasure term t a := by
  cases heval with
  | eval hexpr hcmd =>
      have hwfs : EncodingWellFormed _ := wf_of_evalExpr hexpr hbase
      obtain ⟨cs, hcs, hsound⟩ :=
        ext_judgment_soundness_of_eval dMeasure hlaws seamCert hcert hcmd hwfs
      exact ⟨_, cs, hexpr, hcs, fun a ha => ⟨_, cs, hexpr, hcs, (hsound a ha).truth⟩⟩

/-! ### Exact-distance instances (no distance hypothesis remaining) -/

/-- Chain-level soundness for the exact distance, keeping an explicit
    seam-certificate cell hypothesis `hcert`. -/
theorem ext_judgment_soundness_exact (seamCert : SeamCertPolicy)
    (hcert : SeamCertSound exactExtMeasure seamCert)
    (cs : List CodeState) (hctxt : WellFormedContext cs) (hchain : Chain cs) :
    ∀ a, ExtDerives exactExtMeasure seamCert cs a → ExtModels exactExtMeasure cs a :=
  ext_judgment_soundness exactExtMeasure extMeasureLaws_exact seamCert hcert cs hctxt hchain

/-- Closed-term soundness for the exact distance with an explicit
    seam-certificate cell hypothesis `hcert` (the form for geometric §2e
    certificates outside `CodeState`). -/
theorem ext_judgment_soundness_of_term_exact (seamCert : SeamCertPolicy)
    (hcert : SeamCertSound exactExtMeasure seamCert)
    {term : ClosedTerm} {t : CodeState}
    (heval : EvalTerm term t) (hbase : ExprBaseWF term.expr) :
    ∃ s cs, EvalExpr term.expr s ∧ Trace term.command s cs t ∧
      ∀ a, ExtDerives exactExtMeasure seamCert (s :: cs) a →
        TermModels exactExtMeasure term t a :=
  ext_judgment_soundness_of_term exactExtMeasure extMeasureLaws_exact seamCert hcert heval hbase

/-- Closed-term soundness for the exact distance, uncertified policy: zero
    distance hypotheses and zero seam-certificate hypotheses. -/
theorem ext_judgment_soundness_of_term_exact_uncertified
    {term : ClosedTerm} {t : CodeState}
    (heval : EvalTerm term t) (hbase : ExprBaseWF term.expr) :
    ∃ s cs, EvalExpr term.expr s ∧ Trace term.command s cs t ∧
      ∀ a, ExtDerives exactExtMeasure noSeamCert (s :: cs) a →
        TermModels exactExtMeasure term t a :=
  ext_judgment_soundness_of_term_exact noSeamCert (seamCertSound_none exactExtMeasure) heval hbase

/-- Closed-term soundness for the exact distance with the survival-based
    `AdmissibleSeam` seam-certificate policy discharged: zero distance
    hypotheses and zero seam-certificate hypotheses remain. -/
theorem ext_judgment_soundness_of_term_exact_admissible
    {term : ClosedTerm} {t : CodeState}
    (heval : EvalTerm term t) (hbase : ExprBaseWF term.expr) :
    ∃ s cs, EvalExpr term.expr s ∧ Trace term.command s cs t ∧
      ∀ a, ExtDerives exactExtMeasure admissibleSeamCert (s :: cs) a →
        TermModels exactExtMeasure term t a :=
  ext_judgment_soundness_of_term_exact admissibleSeamCert seamCertSound_admissibleSeam heval hbase

/-! ## Section 6: Chain-extension invariance, transport, seam condition, and `W13` -/

/-- Because `extAexprValue` is strict in `none` (separating `+∞` from an
    out-of-bounds position), every defined term keeps its exact value under
    chain extension (resolving the `optMin` non-monotonicity of `Soundness.lean`). -/
theorem extAexprValue_append_of_some {dMeasure : ExtMeasure} {cs ds : List CodeState} :
    ∀ {x : ExtAExpr} {v : ExtNat},
      extAexprValue dMeasure cs x = some v →
      extAexprValue dMeasure (cs ++ ds) x = some v
  | .const _, _, h => h
  | .inf, _, h => h
  | .atom (.state _ _), _, h => h
  | .atom (.pos i f), v, h => by
      simp only [extAexprValue, extAtomValue] at h ⊢
      cases hcs : cs[i]? with
      | none => rw [hcs] at h; cases h
      | some s =>
          rw [hcs] at h
          rw [getElem?_append_of_some hcs]
          exact h
  | .sub x y, v, h => by
      simp only [extAexprValue] at h ⊢
      cases hx : extAexprValue dMeasure cs x with
      | none => rw [hx] at h; cases h
      | some a =>
          cases hy : extAexprValue dMeasure cs y with
          | none => rw [hx, hy] at h; cases h
          | some b =>
              rw [hx, hy] at h
              rw [extAexprValue_append_of_some hx, extAexprValue_append_of_some hy]
              exact h
  | .add x y, v, h => by
      simp only [extAexprValue] at h ⊢
      cases hx : extAexprValue dMeasure cs x with
      | none => rw [hx] at h; cases h
      | some a =>
          cases hy : extAexprValue dMeasure cs y with
          | none => rw [hx, hy] at h; cases h
          | some b =>
              rw [hx, hy] at h
              rw [extAexprValue_append_of_some hx, extAexprValue_append_of_some hy]
              exact h
  | .minOf x y, v, h => by
      simp only [extAexprValue] at h ⊢
      cases hx : extAexprValue dMeasure cs x with
      | none => rw [hx] at h; cases h
      | some a =>
          cases hy : extAexprValue dMeasure cs y with
          | none => rw [hx, hy] at h; cases h
          | some b =>
              rw [hx, hy] at h
              rw [extAexprValue_append_of_some hx, extAexprValue_append_of_some hy]
              exact h

theorem extDenotes_append {dMeasure : ExtMeasure} {cs ds : List CodeState} {x : ExtAExpr}
    (h : extDenotes dMeasure cs x) : extDenotes dMeasure (cs ++ ds) x :=
  let ⟨v, hv⟩ := h
  ⟨v, extAexprValue_append_of_some hv⟩

/-- Truth of an expanded sentence is monotone under chain extension. -/
theorem extAnnTrue_weaken {dMeasure : ExtMeasure} {cs ds : List CodeState} {a : ExtAnn}
    (h : ExtAnnTrue dMeasure cs a) : ExtAnnTrue dMeasure (cs ++ ds) a := by
  cases a with
  | le x y =>
      obtain ⟨v, w, hv, hw, hle⟩ := h
      exact ⟨v, w, extAexprValue_append_of_some hv, extAexprValue_append_of_some hw, hle⟩
  | eq x y =>
      obtain ⟨v, hv, hw⟩ := h
      exact ⟨v, extAexprValue_append_of_some hv, extAexprValue_append_of_some hw⟩
  | wf i =>
      obtain ⟨s, hi, hwf⟩ := h
      exact ⟨s, getElem?_append_of_some hi, hwf⟩
  | wfState s => exact h
  | gen i r σ S =>
      obtain ⟨s, hi, hmem⟩ := h
      exact ⟨s, getElem?_append_of_some hi, hmem⟩

/-- Shift chain-position atoms by `k`, leaving concrete state atoms fixed. -/
def ExtAtom.shift (k : Nat) : ExtAtom → ExtAtom
  | .pos i f => .pos (i + k) f
  | .state s f => .state s f

def ExtAExpr.shift (k : Nat) : ExtAExpr → ExtAExpr
  | .const v => .const v
  | .inf => .inf
  | .atom a => .atom (a.shift k)
  | .sub x y => .sub (x.shift k) (y.shift k)
  | .add x y => .add (x.shift k) (y.shift k)
  | .minOf x y => .minOf (x.shift k) (y.shift k)

def ExtAnn.shift (k : Nat) : ExtAnn → ExtAnn
  | .le x y => .le (x.shift k) (y.shift k)
  | .eq x y => .eq (x.shift k) (y.shift k)
  | .wf i => .wf (i + k)
  | .wfState s => .wfState s
  | .gen i r σ S => .gen (i + k) r σ S

def ExtAnn.isGen : ExtAnn → Bool
  | .gen _ _ _ _ => true
  | _ => false

theorem extAexprValue_shift (dMeasure : ExtMeasure) (cs ds : List CodeState) :
    ∀ x : ExtAExpr,
      extAexprValue dMeasure (cs ++ ds) (x.shift cs.length) = extAexprValue dMeasure ds x
  | .const _ => rfl
  | .inf => rfl
  | .atom (.state _ _) => rfl
  | .atom (.pos i f) => by
      simp only [ExtAExpr.shift, ExtAtom.shift, extAexprValue, extAtomValue]
      rw [getElem?_append_shift]
  | .sub x y => by
      simp only [ExtAExpr.shift, extAexprValue]
      rw [extAexprValue_shift dMeasure cs ds x, extAexprValue_shift dMeasure cs ds y]
  | .add x y => by
      simp only [ExtAExpr.shift, extAexprValue]
      rw [extAexprValue_shift dMeasure cs ds x, extAexprValue_shift dMeasure cs ds y]
  | .minOf x y => by
      simp only [ExtAExpr.shift, extAexprValue]
      rw [extAexprValue_shift dMeasure cs ds x, extAexprValue_shift dMeasure cs ds y]

theorem extDenotes_shift {dMeasure : ExtMeasure} {cs ds : List CodeState} {x : ExtAExpr} :
    extDenotes dMeasure (cs ++ ds) (x.shift cs.length) ↔ extDenotes dMeasure ds x := by
  unfold extDenotes
  rw [extAexprValue_shift]

/-- Weakening for `ExtDerives`: a derivation over `cs` holds over `cs ++ ds`. -/
theorem ExtDerives.weaken {dMeasure : ExtMeasure} {seamCert : SeamCertPolicy}
    {cs : List CodeState} (ds : List CodeState) {a : ExtAnn}
    (h : ExtDerives dMeasure seamCert cs a) :
    ExtDerives dMeasure seamCert (cs ++ ds) a := by
  induction h with
  | instChainState i f s hi =>
      exact ExtDerives.instChainState i f s (getElem?_append_of_some hi)
  | instSkip i f s t hi hj hstep =>
      exact ExtDerives.instSkip i f s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instSkipWF i s t hi hj hstep =>
      exact ExtDerives.instSkipWF i s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instDeleteN i r s t hi hj hstep =>
      exact ExtDerives.instDeleteN i r s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instDeleteK i r s t hi hj hstep =>
      exact ExtDerives.instDeleteK i r s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instDeleteKSub i r s t hi hj hstep =>
      exact ExtDerives.instDeleteKSub i r s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instDeleteWF i r s t hi hj hstep =>
      exact ExtDerives.instDeleteWF i r s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instDeleteDX i r s t hi hj hstep =>
      exact ExtDerives.instDeleteDX i r s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instDeleteDZ i r s t hi hj hstep =>
      exact ExtDerives.instDeleteDZ i r s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instDeleteD i r s t hi hj hstep =>
      exact ExtDerives.instDeleteD i r s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instAddN i sector support s t hi hj hstep =>
      exact ExtDerives.instAddN i sector support s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instAddK i sector support s t hi hj hstep =>
      exact ExtDerives.instAddK i sector support s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instAddKSub i sector support s t hi hj hstep =>
      exact ExtDerives.instAddKSub i sector support s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instAddWF i sector support s t hi hj hstep =>
      exact ExtDerives.instAddWF i sector support s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instAddDX i sector support s t hi hj hstep =>
      exact ExtDerives.instAddDX i sector support s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instAddDZ i sector support s t hi hj hstep =>
      exact ExtDerives.instAddDZ i sector support s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instAddD i sector support s t hi hj hstep =>
      exact ExtDerives.instAddD i sector support s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instGraftN i q sector ids s t hi hj hstep =>
      exact ExtDerives.instGraftN i q sector ids s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instGraftK i q sector ids s t hi hj hstep =>
      exact ExtDerives.instGraftK i q sector ids s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instGraftWF i q sector ids s t hi hj hstep =>
      exact ExtDerives.instGraftWF i q sector ids s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instGraftSpliced i q sector ids s t hi hj hstep =>
      exact ExtDerives.instGraftSpliced i q sector ids s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instGraftOpp i q sector ids s t hi hj hstep =>
      exact ExtDerives.instGraftOpp i q sector ids s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instGraftFullUpper i q sector ids s t hi hj hstep =>
      exact ExtDerives.instGraftFullUpper i q sector ids s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instRebase i f sector matrix s t hi hj hstep =>
      exact ExtDerives.instRebase i f sector matrix s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instRebaseWF i sector matrix s t hi hj hstep =>
      exact ExtDerives.instRebaseWF i sector matrix s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instHadamardN i T s t hi hj hstep =>
      exact ExtDerives.instHadamardN i T s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instHadamardK i T s t hi hj hstep =>
      exact ExtDerives.instHadamardK i T s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instHadamardD i T s t hi hj hstep hg =>
      exact ExtDerives.instHadamardD i T s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hg
  | instHadamardWF i T s t hi hj hstep =>
      exact ExtDerives.instHadamardWF i T s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instHadamardEmpty i f T s t hi hj hstep hT =>
      exact ExtDerives.instHadamardEmpty i f T s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hT
  | instHadamardSwapDX i T s t hi hj hstep hT =>
      exact ExtDerives.instHadamardSwapDX i T s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hT
  | instHadamardSwapDZ i T s t hi hj hstep hT =>
      exact ExtDerives.instHadamardSwapDZ i T s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hT
  | instPeelN i q τ r_id s t hi hj hstep =>
      exact ExtDerives.instPeelN i q τ r_id s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instPeelK i q τ r_id s t hi hj hstep =>
      exact ExtDerives.instPeelK i q τ r_id s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instPeelWF i q τ r_id s t hi hj hstep =>
      exact ExtDerives.instPeelWF i q τ r_id s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instPeelSpliced i q τ r_id s t hi hj hstep =>
      exact ExtDerives.instPeelSpliced i q τ r_id s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instPeelOppUpper i q τ r_id s t hi hj hstep =>
      exact ExtDerives.instPeelOppUpper i q τ r_id s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instPeelOppLower i q τ r_id s t hi hj hstep =>
      exact ExtDerives.instPeelOppLower i q τ r_id s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instPeelFullLower i q τ r_id s t hi hj hstep =>
      exact ExtDerives.instPeelFullLower i q τ r_id s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instPeelFullUpper i q τ r_id s t hi hj hstep =>
      exact ExtDerives.instPeelFullUpper i q τ r_id s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instPunctureN i q s t hi hj hstep =>
      exact ExtDerives.instPunctureN i q s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instPunctureK i q s t hi hj hstep =>
      exact ExtDerives.instPunctureK i q s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instPunctureWF i q s t hi hj hstep =>
      exact ExtDerives.instPunctureWF i q s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instExtendN i delta adds s t hi hj hstep =>
      exact ExtDerives.instExtendN i delta adds s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instExtendK i delta adds s t hi hj hstep =>
      exact ExtDerives.instExtendK i delta adds s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instExtendWF i delta adds s t hi hj hstep =>
      exact ExtDerives.instExtendWF i delta adds s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instExtendNilDX i adds s t hi hj hstep =>
      exact ExtDerives.instExtendNilDX i adds s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instExtendNilDZ i adds s t hi hj hstep =>
      exact ExtDerives.instExtendNilDZ i adds s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instExtendNilD i adds s t hi hj hstep =>
      exact ExtDerives.instExtendNilD i adds s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instCnotSwapN i U s t hi hj hstep =>
      exact ExtDerives.instCnotSwapN i U s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instCnotSwapK i U s t hi hj hstep =>
      exact ExtDerives.instCnotSwapK i U s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instCnotSwapWF i U s t hi hj hstep =>
      exact ExtDerives.instCnotSwapWF i U s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instSplitN i QA R s t hi hj hstep =>
      exact ExtDerives.instSplitN i QA R s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instSplitK i QA R s t hi hj hstep =>
      exact ExtDerives.instSplitK i QA R s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instSplitWF i QA R s t hi hj hstep =>
      exact ExtDerives.instSplitWF i QA R s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instSplitDX i QA R s t hi hj hstep =>
      exact ExtDerives.instSplitDX i QA R s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instSplitDZ i QA R s t hi hj hstep =>
      exact ExtDerives.instSplitDZ i QA R s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instSplitD i QA R s t hi hj hstep =>
      exact ExtDerives.instSplitD i QA R s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | instExprWF e s he hbase => exact ExtDerives.instExprWF e s he hbase
  | instDirectSumN e1 e2 s1 s2 s h1 h2 hsum =>
      exact ExtDerives.instDirectSumN e1 e2 s1 s2 s h1 h2 hsum
  | instDirectSumK e1 e2 s1 s2 s h1 h2 hsum hbase1 hbase2 =>
      exact ExtDerives.instDirectSumK e1 e2 s1 s2 s h1 h2 hsum hbase1 hbase2
  | instDirectSumDX e1 e2 s1 s2 s h1 h2 hsum hbase1 hbase2 =>
      exact ExtDerives.instDirectSumDX e1 e2 s1 s2 s h1 h2 hsum hbase1 hbase2
  | instDirectSumDZ e1 e2 s1 s2 s h1 h2 hsum hbase1 hbase2 =>
      exact ExtDerives.instDirectSumDZ e1 e2 s1 s2 s h1 h2 hsum hbase1 hbase2
  | instDirectSumD e1 e2 s1 s2 s h1 h2 hsum hbase1 hbase2 =>
      exact ExtDerives.instDirectSumD e1 e2 s1 s2 s h1 h2 hsum hbase1 hbase2
  | instGlueN e1 e2 seams s1 s2 s h1 h2 hglue =>
      exact ExtDerives.instGlueN e1 e2 seams s1 s2 s h1 h2 hglue
  | instGlueK e1 e2 seams s1 s2 s h1 h2 hglue hbase1 hbase2 =>
      exact ExtDerives.instGlueK e1 e2 seams s1 s2 s h1 h2 hglue hbase1 hbase2
  | instGlueDX e1 e2 seams s1 s2 s h1 h2 hglue hbase1 hbase2 =>
      exact ExtDerives.instGlueDX e1 e2 seams s1 s2 s h1 h2 hglue hbase1 hbase2
  | instGlueDZ e1 e2 seams s1 s2 s h1 h2 hglue hbase1 hbase2 =>
      exact ExtDerives.instGlueDZ e1 e2 seams s1 s2 s h1 h2 hglue hbase1 hbase2
  | instGlueD e1 e2 seams s1 s2 s h1 h2 hglue hbase1 hbase2 =>
      exact ExtDerives.instGlueD e1 e2 seams s1 s2 s h1 h2 hglue hbase1 hbase2
  | instGlueCertDZ e1 e2 seams s1 s2 s h1 h2 hglue hbase1 hbase2 hsc =>
      exact ExtDerives.instGlueCertDZ e1 e2 seams s1 s2 s h1 h2 hglue hbase1 hbase2 hsc
  | instHgpN H1 H2 s h => exact ExtDerives.instHgpN H1 H2 s h
  | instLiftN orders A B s h => exact ExtDerives.instLiftN orders A B s h
  | instTwoblockN orders a b s h => exact ExtDerives.instTwoblockN orders a b s h
  | instTwoblockK orders a b s h => exact ExtDerives.instTwoblockK orders a b s h
  | instConcatN eO eI blocks repsX repsZ sO sI s hO hI h =>
      exact ExtDerives.instConcatN eO eI blocks repsX repsZ sO sI s hO hI h
  | instConcatK eO eI blocks repsX repsZ sO s hO h =>
      exact ExtDerives.instConcatK eO eI blocks repsX repsZ sO s hO h
  | instProductN eA eB sA sB s hA hB h =>
      exact ExtDerives.instProductN eA eB sA sB s hA hB h
  | instDoubleN e wiring conj sC s hC h =>
      exact ExtDerives.instDoubleN e wiring conj sC s hC h
  | instDoubleEmptyK e conj sC s hC h =>
      exact ExtDerives.instDoubleEmptyK e conj sC s hC h
  | instBalancedN orders H1 H2 rows1 cols1 rows2 cols2 s h =>
      exact ExtDerives.instBalancedN orders H1 H2 rows1 cols1 rows2 cols2 s h
  | instBalancedK orders H1 H2 rows1 cols1 rows2 cols2 s h =>
      exact ExtDerives.instBalancedK orders H1 H2 rows1 cols1 rows2 cols2 s h
  | instLiftTableN t A B s h => exact ExtDerives.instLiftTableN t A B s h
  | instTwoblockTableN t a b s h => exact ExtDerives.instTwoblockTableN t a b s h
  | instBalancedTableN t H1 H2 rows1 cols1 rows2 cols2 s h =>
      exact ExtDerives.instBalancedTableN t H1 H2 rows1 cols1 rows2 cols2 s h
  | instTannerN n LX LZ viewsX viewsZ s h =>
      exact ExtDerives.instTannerN n LX LZ viewsX viewsZ s h
  | instTannerK n LX LZ viewsX viewsZ s h =>
      exact ExtDerives.instTannerK n LX LZ viewsX viewsZ s h
  | instTileN tiles placements idents removed s h =>
      exact ExtDerives.instTileN tiles placements idents removed s h
  | instTileK tiles placements idents removed s h =>
      exact ExtDerives.instTileK tiles placements idents removed s h
  | instNestedN HX HZ s h => exact ExtDerives.instNestedN HX HZ s h
  | instConeN DA DB F1 F0 s h => exact ExtDerives.instConeN DA DB F1 F0 s h
  | instConeK DA DB F1 F0 s h => exact ExtDerives.instConeK DA DB F1 F0 s h
  | instEmptyN s h => exact ExtDerives.instEmptyN s h
  | instEmptyK s h => exact ExtDerives.instEmptyK s h
  | instFreeN qs s h => exact ExtDerives.instFreeN qs s h
  | instFreeK qs s h => exact ExtDerives.instFreeK qs s h
  | instPullbackN e1 e2 eI phi1 phi2 s1 s2 sI s h1 h2 hI h =>
      exact ExtDerives.instPullbackN e1 e2 eI phi1 phi2 s1 s2 sI s h1 h2 hI h
  | instPushoutN e1 e2 eS psi1 psi2 s1 s2 sS s h1 h2 hS h =>
      exact ExtDerives.instPushoutN e1 e2 eS psi1 psi2 s1 s2 sS s h1 h2 hS h
  | instPairPartitionN p BX BZ s h => exact ExtDerives.instPairPartitionN p BX BZ s h
  | instPpScaleN e0 P BX BZ s h => exact ExtDerives.instPpScaleN e0 P BX BZ s h
  | transit_le_le x y z _ _ ih1 ih2 => exact ExtDerives.transit_le_le x y z ih1 ih2
  | transit_le_eq x y z _ _ ih1 ih2 => exact ExtDerives.transit_le_eq x y z ih1 ih2
  | transit_eq_le x y z _ _ ih1 ih2 => exact ExtDerives.transit_eq_le x y z ih1 ih2
  | transit_eq_eq x y z _ _ ih1 ih2 => exact ExtDerives.transit_eq_eq x y z ih1 ih2
  | min_le_left x y hx hy =>
      exact ExtDerives.min_le_left x y (extDenotes_append hx) (extDenotes_append hy)
  | min_le_right x y hx hy =>
      exact ExtDerives.min_le_right x y (extDenotes_append hx) (extDenotes_append hy)
  | le_min t x y _ _ ih1 ih2 => exact ExtDerives.le_min t x y ih1 ih2
  | le_refl x hx => exact ExtDerives.le_refl x (extDenotes_append hx)
  | eq_refl x hx => exact ExtDerives.eq_refl x (extDenotes_append hx)
  | eq_sym x y _ ih => exact ExtDerives.eq_sym x y ih
  | genInput r σ S s h0 hrow =>
      exact ExtDerives.genInput r σ S s (getElem?_append_of_some h0) hrow
  | genMint i sector support s t hi hj hstep =>
      exact ExtDerives.genMint i sector support s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep
  | genSkip i r σ S s t hi hj hstep _ ih =>
      exact ExtDerives.genSkip i r σ S s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep ih
  | genDelete i r r' σ S s t hi hj hstep hsurvives _ ih =>
      exact ExtDerives.genDelete i r r' σ S s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hsurvives ih
  | genAdd i r σ S sector support s t hi hj hstep _ ih =>
      exact ExtDerives.genAdd i r σ S sector support s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep ih
  | genGraft i r σ S q sector ids s t hi hj hstep hsurvives _ ih =>
      exact ExtDerives.genGraft i r σ S q sector ids s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hsurvives ih
  | genGraftMint i q sector ids s t row hi hj hstep hrow =>
      exact ExtDerives.genGraftMint i q sector ids s t row (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hrow
  | genExtend i r σ S delta adds s t hi hj hstep _ ih =>
      exact ExtDerives.genExtend i r σ S delta adds s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep ih
  | genExtendMint i delta adds s t row hi hj hstep hrow =>
      exact ExtDerives.genExtendMint i delta adds s t row (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hrow
  | genPeel i r r_id σ S q tau s t hi hj hstep hsurvives _ ih =>
      exact ExtDerives.genPeel i r r_id σ S q tau s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hsurvives ih
  | genPuncture i r σ S q s t hi hj hstep hsurvives _ ih =>
      exact ExtDerives.genPuncture i r σ S q s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hsurvives ih
  | genHadamard i r σ S T s t hi hj hstep hg _ ih =>
      exact ExtDerives.genHadamard i r σ S T s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hg ih
  | genHadamardSplit i T s t row hi hj hstep hsplit hrow =>
      exact ExtDerives.genHadamardSplit i T s t row (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hsplit hrow
  | genRebase i r σ S sector matrix s t hi hj hstep hsurvives _ ih =>
      exact ExtDerives.genRebase i r σ S sector matrix s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hsurvives ih
  | genRebaseMint i sector matrix s t row hi hj hstep hrow =>
      exact ExtDerives.genRebaseMint i sector matrix s t row (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hrow
  | genCnotSwap i r σ S U s t hi hj hstep _ ih =>
      exact ExtDerives.genCnotSwap i r σ S U s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep ih
  | genSplit i r σ S QA R s t hi hj hstep hsurvives _ ih =>
      exact ExtDerives.genSplit i r σ S QA R s t (getElem?_append_of_some hi)
        (getElem?_append_of_some hj) hstep hsurvives ih

/-- Seam condition for generator-referencing claims in `ExtDerives`. -/
def ExtSeamRowsDerived (dMeasure : ExtMeasure) (seamCert : SeamCertPolicy)
    (cs ds : List CodeState) : Prop :=
  ∀ (r : Nat) (σ : Sector) (S : List Nat) (s : CodeState), ds[0]? = some s →
    ({ id := r, sector := σ, support := S } : Row) ∈ s.rows →
    ExtDerives dMeasure seamCert (cs ++ ds) (ExtAnn.gen cs.length r σ S)

/-- Shifting a derivation over the second segment `ds` into `cs ++ ds`,
    requiring `ExtSeamRowsDerived` only for generator-referencing claims. -/
theorem ExtDerives.shift_cond {dMeasure : ExtMeasure} {seamCert : SeamCertPolicy}
    (cs : List CodeState) {ds : List CodeState} {a : ExtAnn}
    (h : ExtDerives dMeasure seamCert ds a) :
    (a.isGen = true → ExtSeamRowsDerived dMeasure seamCert cs ds) →
    ExtDerives dMeasure seamCert (cs ++ ds) (a.shift cs.length) := by
  induction h with
  | instChainState i f s hi =>
      intro _
      exact ExtDerives.instChainState (i + cs.length) f s (getElem?_shift_of_some hi)
  | instSkip i f s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instSkip (i + cs.length) f s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instSkipWF i s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instSkipWF (i + cs.length) s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instDeleteN i r s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instDeleteN (i + cs.length) r s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instDeleteK i r s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instDeleteK (i + cs.length) r s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instDeleteKSub i r s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instDeleteKSub (i + cs.length) r s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instDeleteWF i r s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instDeleteWF (i + cs.length) r s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instDeleteDX i r s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instDeleteDX (i + cs.length) r s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instDeleteDZ i r s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instDeleteDZ (i + cs.length) r s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instDeleteD i r s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instDeleteD (i + cs.length) r s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instAddN i sector support s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instAddN (i + cs.length) sector support s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instAddK i sector support s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instAddK (i + cs.length) sector support s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instAddKSub i sector support s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instAddKSub (i + cs.length) sector support s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instAddWF i sector support s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instAddWF (i + cs.length) sector support s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instAddDX i sector support s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instAddDX (i + cs.length) sector support s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instAddDZ i sector support s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instAddDZ (i + cs.length) sector support s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instAddD i sector support s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instAddD (i + cs.length) sector support s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instGraftN i q sector ids s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instGraftN (i + cs.length) q sector ids s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instGraftK i q sector ids s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instGraftK (i + cs.length) q sector ids s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instGraftWF i q sector ids s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instGraftWF (i + cs.length) q sector ids s t (getElem?_shift_of_some hi)
        (getElem?_shift_succ_of_some hj) hstep
  | instGraftSpliced i q sector ids s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instGraftSpliced (i + cs.length) q sector ids s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instGraftOpp i q sector ids s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instGraftOpp (i + cs.length) q sector ids s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instGraftFullUpper i q sector ids s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instGraftFullUpper (i + cs.length) q sector ids s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instRebase i f sector matrix s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instRebase (i + cs.length) f sector matrix s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instRebaseWF i sector matrix s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instRebaseWF (i + cs.length) sector matrix s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instHadamardN i T s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instHadamardN (i + cs.length) T s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instHadamardK i T s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instHadamardK (i + cs.length) T s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instHadamardD i T s t hi hj hstep hg =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instHadamardD (i + cs.length) T s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep hg
  | instHadamardWF i T s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instHadamardWF (i + cs.length) T s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instHadamardEmpty i f T s t hi hj hstep hT =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instHadamardEmpty (i + cs.length) f T s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep hT
  | instHadamardSwapDX i T s t hi hj hstep hT =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instHadamardSwapDX (i + cs.length) T s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep hT
  | instHadamardSwapDZ i T s t hi hj hstep hT =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instHadamardSwapDZ (i + cs.length) T s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep hT
  | instPeelN i q τ r_id s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instPeelN (i + cs.length) q τ r_id s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instPeelK i q τ r_id s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instPeelK (i + cs.length) q τ r_id s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instPeelWF i q τ r_id s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instPeelWF (i + cs.length) q τ r_id s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instPeelSpliced i q τ r_id s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instPeelSpliced (i + cs.length) q τ r_id s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instPeelOppUpper i q τ r_id s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instPeelOppUpper (i + cs.length) q τ r_id s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instPeelOppLower i q τ r_id s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instPeelOppLower (i + cs.length) q τ r_id s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instPeelFullLower i q τ r_id s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instPeelFullLower (i + cs.length) q τ r_id s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instPeelFullUpper i q τ r_id s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instPeelFullUpper (i + cs.length) q τ r_id s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instPunctureN i q s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instPunctureN (i + cs.length) q s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instPunctureK i q s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instPunctureK (i + cs.length) q s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instPunctureWF i q s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instPunctureWF (i + cs.length) q s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instExtendN i delta adds s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instExtendN (i + cs.length) delta adds s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instExtendK i delta adds s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instExtendK (i + cs.length) delta adds s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instExtendWF i delta adds s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instExtendWF (i + cs.length) delta adds s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instExtendNilDX i adds s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instExtendNilDX (i + cs.length) adds s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instExtendNilDZ i adds s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instExtendNilDZ (i + cs.length) adds s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instExtendNilD i adds s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instExtendNilD (i + cs.length) adds s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instCnotSwapN i U s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instCnotSwapN (i + cs.length) U s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instCnotSwapK i U s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instCnotSwapK (i + cs.length) U s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instCnotSwapWF i U s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instCnotSwapWF (i + cs.length) U s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instSplitN i QA R s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instSplitN (i + cs.length) QA R s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instSplitK i QA R s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instSplitK (i + cs.length) QA R s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instSplitWF i QA R s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instSplitWF (i + cs.length) QA R s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instSplitDX i QA R s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instSplitDX (i + cs.length) QA R s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instSplitDZ i QA R s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instSplitDZ (i + cs.length) QA R s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instSplitD i QA R s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift, ExtAExpr.shift, ExtAtom.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.instSplitD (i + cs.length) QA R s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | instExprWF e s he hbase => intro _; exact ExtDerives.instExprWF e s he hbase
  | instDirectSumN e1 e2 s1 s2 s h1 h2 hsum =>
      intro _; exact ExtDerives.instDirectSumN e1 e2 s1 s2 s h1 h2 hsum
  | instDirectSumK e1 e2 s1 s2 s h1 h2 hsum hbase1 hbase2 =>
      intro _; exact ExtDerives.instDirectSumK e1 e2 s1 s2 s h1 h2 hsum hbase1 hbase2
  | instDirectSumDX e1 e2 s1 s2 s h1 h2 hsum hbase1 hbase2 =>
      intro _; exact ExtDerives.instDirectSumDX e1 e2 s1 s2 s h1 h2 hsum hbase1 hbase2
  | instDirectSumDZ e1 e2 s1 s2 s h1 h2 hsum hbase1 hbase2 =>
      intro _; exact ExtDerives.instDirectSumDZ e1 e2 s1 s2 s h1 h2 hsum hbase1 hbase2
  | instDirectSumD e1 e2 s1 s2 s h1 h2 hsum hbase1 hbase2 =>
      intro _; exact ExtDerives.instDirectSumD e1 e2 s1 s2 s h1 h2 hsum hbase1 hbase2
  | instGlueN e1 e2 seams s1 s2 s h1 h2 hglue =>
      intro _; exact ExtDerives.instGlueN e1 e2 seams s1 s2 s h1 h2 hglue
  | instGlueK e1 e2 seams s1 s2 s h1 h2 hglue hbase1 hbase2 =>
      intro _; exact ExtDerives.instGlueK e1 e2 seams s1 s2 s h1 h2 hglue hbase1 hbase2
  | instGlueDX e1 e2 seams s1 s2 s h1 h2 hglue hbase1 hbase2 =>
      intro _; exact ExtDerives.instGlueDX e1 e2 seams s1 s2 s h1 h2 hglue hbase1 hbase2
  | instGlueDZ e1 e2 seams s1 s2 s h1 h2 hglue hbase1 hbase2 =>
      intro _; exact ExtDerives.instGlueDZ e1 e2 seams s1 s2 s h1 h2 hglue hbase1 hbase2
  | instGlueD e1 e2 seams s1 s2 s h1 h2 hglue hbase1 hbase2 =>
      intro _; exact ExtDerives.instGlueD e1 e2 seams s1 s2 s h1 h2 hglue hbase1 hbase2
  | instGlueCertDZ e1 e2 seams s1 s2 s h1 h2 hglue hbase1 hbase2 hsc =>
      intro _; exact ExtDerives.instGlueCertDZ e1 e2 seams s1 s2 s h1 h2 hglue hbase1 hbase2 hsc
  | instHgpN H1 H2 s h => intro _; exact ExtDerives.instHgpN H1 H2 s h
  | instLiftN orders A B s h => intro _; exact ExtDerives.instLiftN orders A B s h
  | instTwoblockN orders a b s h => intro _; exact ExtDerives.instTwoblockN orders a b s h
  | instTwoblockK orders a b s h => intro _; exact ExtDerives.instTwoblockK orders a b s h
  | instConcatN eO eI blocks repsX repsZ sO sI s hO hI h =>
      intro _; exact ExtDerives.instConcatN eO eI blocks repsX repsZ sO sI s hO hI h
  | instConcatK eO eI blocks repsX repsZ sO s hO h =>
      intro _; exact ExtDerives.instConcatK eO eI blocks repsX repsZ sO s hO h
  | instProductN eA eB sA sB s hA hB h =>
      intro _; exact ExtDerives.instProductN eA eB sA sB s hA hB h
  | instDoubleN e wiring conj sC s hC h =>
      intro _; exact ExtDerives.instDoubleN e wiring conj sC s hC h
  | instDoubleEmptyK e conj sC s hC h =>
      intro _; exact ExtDerives.instDoubleEmptyK e conj sC s hC h
  | instBalancedN orders H1 H2 rows1 cols1 rows2 cols2 s h =>
      intro _; exact ExtDerives.instBalancedN orders H1 H2 rows1 cols1 rows2 cols2 s h
  | instBalancedK orders H1 H2 rows1 cols1 rows2 cols2 s h =>
      intro _; exact ExtDerives.instBalancedK orders H1 H2 rows1 cols1 rows2 cols2 s h
  | instLiftTableN t A B s h => intro _; exact ExtDerives.instLiftTableN t A B s h
  | instTwoblockTableN t a b s h =>
      intro _; exact ExtDerives.instTwoblockTableN t a b s h
  | instBalancedTableN t H1 H2 rows1 cols1 rows2 cols2 s h =>
      intro _; exact ExtDerives.instBalancedTableN t H1 H2 rows1 cols1 rows2 cols2 s h
  | instTannerN n LX LZ viewsX viewsZ s h =>
      intro _; exact ExtDerives.instTannerN n LX LZ viewsX viewsZ s h
  | instTannerK n LX LZ viewsX viewsZ s h =>
      intro _; exact ExtDerives.instTannerK n LX LZ viewsX viewsZ s h
  | instTileN tiles placements idents removed s h =>
      intro _; exact ExtDerives.instTileN tiles placements idents removed s h
  | instTileK tiles placements idents removed s h =>
      intro _; exact ExtDerives.instTileK tiles placements idents removed s h
  | instNestedN HX HZ s h => intro _; exact ExtDerives.instNestedN HX HZ s h
  | instConeN DA DB F1 F0 s h => intro _; exact ExtDerives.instConeN DA DB F1 F0 s h
  | instConeK DA DB F1 F0 s h => intro _; exact ExtDerives.instConeK DA DB F1 F0 s h
  | instEmptyN s h => intro _; exact ExtDerives.instEmptyN s h
  | instEmptyK s h => intro _; exact ExtDerives.instEmptyK s h
  | instFreeN qs s h => intro _; exact ExtDerives.instFreeN qs s h
  | instFreeK qs s h => intro _; exact ExtDerives.instFreeK qs s h
  | instPullbackN e1 e2 eI phi1 phi2 s1 s2 sI s h1 h2 hI h =>
      intro _; exact ExtDerives.instPullbackN e1 e2 eI phi1 phi2 s1 s2 sI s h1 h2 hI h
  | instPushoutN e1 e2 eS psi1 psi2 s1 s2 sS s h1 h2 hS h =>
      intro _; exact ExtDerives.instPushoutN e1 e2 eS psi1 psi2 s1 s2 sS s h1 h2 hS h
  | instPairPartitionN p BX BZ s h => intro _; exact ExtDerives.instPairPartitionN p BX BZ s h
  | instPpScaleN e0 P BX BZ s h => intro _; exact ExtDerives.instPpScaleN e0 P BX BZ s h
  | transit_le_le _ _ _ _ _ ih1 ih2 =>
      intro _
      exact ExtDerives.transit_le_le _ _ _
        (ih1 (fun h => absurd h Bool.false_ne_true))
        (ih2 (fun h => absurd h Bool.false_ne_true))
  | transit_le_eq _ _ _ _ _ ih1 ih2 =>
      intro _
      exact ExtDerives.transit_le_eq _ _ _
        (ih1 (fun h => absurd h Bool.false_ne_true))
        (ih2 (fun h => absurd h Bool.false_ne_true))
  | transit_eq_le _ _ _ _ _ ih1 ih2 =>
      intro _
      exact ExtDerives.transit_eq_le _ _ _
        (ih1 (fun h => absurd h Bool.false_ne_true))
        (ih2 (fun h => absurd h Bool.false_ne_true))
  | transit_eq_eq _ _ _ _ _ ih1 ih2 =>
      intro _
      exact ExtDerives.transit_eq_eq _ _ _
        (ih1 (fun h => absurd h Bool.false_ne_true))
        (ih2 (fun h => absurd h Bool.false_ne_true))
  | min_le_left _ _ hx hy =>
      intro _
      exact ExtDerives.min_le_left _ _ (extDenotes_shift.mpr hx) (extDenotes_shift.mpr hy)
  | min_le_right _ _ hx hy =>
      intro _
      exact ExtDerives.min_le_right _ _ (extDenotes_shift.mpr hx) (extDenotes_shift.mpr hy)
  | le_min _ _ _ _ _ ih1 ih2 =>
      intro _
      exact ExtDerives.le_min _ _ _
        (ih1 (fun h => absurd h Bool.false_ne_true))
        (ih2 (fun h => absurd h Bool.false_ne_true))
  | le_refl _ hx =>
      intro _
      exact ExtDerives.le_refl _ (extDenotes_shift.mpr hx)
  | eq_refl _ hx =>
      intro _
      exact ExtDerives.eq_refl _ (extDenotes_shift.mpr hx)
  | eq_sym _ _ _ ih =>
      intro _
      exact ExtDerives.eq_sym _ _ (ih (fun h => absurd h Bool.false_ne_true))
  | genInput r σ S s h0 hrow =>
      intro hsrc
      simp only [ExtAnn.shift]
      rw [Nat.zero_add]
      exact hsrc rfl r σ S s h0 hrow
  | genMint i sector support s t hi hj hstep =>
      intro _
      simp only [ExtAnn.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.genMint (i + cs.length) sector support s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep
  | genSkip i r σ S s t hi hj hstep _ ih =>
      intro hsrc
      have ih := ih (fun _ => hsrc rfl)
      simp only [ExtAnn.shift] at ih ⊢
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.genSkip (i + cs.length) r σ S s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep ih
  | genDelete i r r' σ S s t hi hj hstep hsurvives _ ih =>
      intro hsrc
      have ih := ih (fun _ => hsrc rfl)
      simp only [ExtAnn.shift] at ih ⊢
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.genDelete (i + cs.length) r r' σ S s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep hsurvives ih
  | genAdd i r σ S sector support s t hi hj hstep _ ih =>
      intro hsrc
      have ih := ih (fun _ => hsrc rfl)
      simp only [ExtAnn.shift] at ih ⊢
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.genAdd (i + cs.length) r σ S sector support s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep ih
  | genGraft i r σ S q sector ids s t hi hj hstep hsurvives _ ih =>
      intro hsrc
      have ih := ih (fun _ => hsrc rfl)
      simp only [ExtAnn.shift] at ih ⊢
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.genGraft (i + cs.length) r σ S q sector ids s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep hsurvives ih
  | genGraftMint i q sector ids s t row hi hj hstep hrow =>
      intro _
      simp only [ExtAnn.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.genGraftMint (i + cs.length) q sector ids s t row
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep hrow
  | genExtend i r σ S delta adds s t hi hj hstep _ ih =>
      intro hsrc
      have ih := ih (fun _ => hsrc rfl)
      simp only [ExtAnn.shift] at ih ⊢
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.genExtend (i + cs.length) r σ S delta adds s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep ih
  | genExtendMint i delta adds s t row hi hj hstep hrow =>
      intro _
      simp only [ExtAnn.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.genExtendMint (i + cs.length) delta adds s t row
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep hrow
  | genPeel i r r_id σ S q tau s t hi hj hstep hsurvives _ ih =>
      intro hsrc
      have ih := ih (fun _ => hsrc rfl)
      simp only [ExtAnn.shift] at ih ⊢
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.genPeel (i + cs.length) r r_id σ S q tau s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep hsurvives ih
  | genPuncture i r σ S q s t hi hj hstep hsurvives _ ih =>
      intro hsrc
      have ih := ih (fun _ => hsrc rfl)
      simp only [ExtAnn.shift] at ih ⊢
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.genPuncture (i + cs.length) r σ S q s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep hsurvives ih
  | genHadamard i r σ S T s t hi hj hstep hg _ ih =>
      intro hsrc
      have ih := ih (fun _ => hsrc rfl)
      simp only [ExtAnn.shift] at ih ⊢
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.genHadamard (i + cs.length) r σ S T s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep hg ih
  | genHadamardSplit i T s t row hi hj hstep hsplit hrow =>
      intro _
      simp only [ExtAnn.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.genHadamardSplit (i + cs.length) T s t row
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep hsplit hrow
  | genRebase i r σ S sector matrix s t hi hj hstep hsurvives _ ih =>
      intro hsrc
      have ih := ih (fun _ => hsrc rfl)
      simp only [ExtAnn.shift] at ih ⊢
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.genRebase (i + cs.length) r σ S sector matrix s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep hsurvives ih
  | genRebaseMint i sector matrix s t row hi hj hstep hrow =>
      intro _
      simp only [ExtAnn.shift]
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.genRebaseMint (i + cs.length) sector matrix s t row
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep hrow
  | genCnotSwap i r σ S U s t hi hj hstep _ ih =>
      intro hsrc
      have ih := ih (fun _ => hsrc rfl)
      simp only [ExtAnn.shift] at ih ⊢
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.genCnotSwap (i + cs.length) r σ S U s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep ih
  | genSplit i r σ S QA R s t hi hj hstep hsurvives _ ih =>
      intro hsrc
      have ih := ih (fun _ => hsrc rfl)
      simp only [ExtAnn.shift] at ih ⊢
      rw [Nat.add_right_comm i 1 cs.length]
      exact ExtDerives.genSplit (i + cs.length) r σ S QA R s t
        (getElem?_shift_of_some hi) (getElem?_shift_succ_of_some hj) hstep hsurvives ih

theorem ExtDerives.shift {dMeasure : ExtMeasure} {seamCert : SeamCertPolicy}
    (cs : List CodeState) {ds : List CodeState} {a : ExtAnn}
    (h : ExtDerives dMeasure seamCert ds a) (ha : a.isGen = false := by rfl) :
    ExtDerives dMeasure seamCert (cs ++ ds) (a.shift cs.length) :=
  h.shift_cond cs (fun hg => absurd (ha.symm.trans hg) Bool.false_ne_true)

theorem ExtDerives.shift_gen {dMeasure : ExtMeasure} {seamCert : SeamCertPolicy}
    (cs : List CodeState) {ds : List CodeState} {a : ExtAnn}
    (h : ExtDerives dMeasure seamCert ds a)
    (hsrc : ExtSeamRowsDerived dMeasure seamCert cs ds) :
    ExtDerives dMeasure seamCert (cs ++ ds) (a.shift cs.length) :=
  h.shift_cond cs (fun _ => hsrc)

/-- Completeness of the generator rows of `ExtDerives` on any chain of single
    steps (`StepChain`, covering kernel, graft, and all five Gate 6 moves). -/
theorem ext_derives_gen_of_displayed (dMeasure : ExtMeasure) (seamCert : SeamCertPolicy)
    {cs : List CodeState} (hchain : StepChain cs) :
    ∀ (i : Nat) (t : CodeState), cs[i]? = some t →
      ∀ (r : Nat) (σ : Sector) (S : List Nat),
        ({ id := r, sector := σ, support := S } : Row) ∈ t.rows →
        ExtDerives dMeasure seamCert cs (ExtAnn.gen i r σ S) := by
  intro i
  induction i with
  | zero =>
      intro t ht r σ S hrow
      exact ExtDerives.genInput r σ S t ht hrow
  | succ i ih =>
      intro t ht r σ S hrow
      have hlt : i < cs.length := by
        have := (List.getElem?_eq_some_iff.mp ht).1
        omega
      obtain ⟨s, hs⟩ : ∃ s, cs[i]? = some s := ⟨cs[i], List.getElem?_eq_getElem hlt⟩
      obtain ⟨m, hm, hstep⟩ := hchain.step hs ht
      cases m with
      | skip =>
          have hts := eval_skip_eq hstep
          subst hts
          exact ExtDerives.genSkip i r σ S _ _ hs ht hstep (ih _ hs r σ S hrow)
      | delete r' =>
          have hts := eval_delete_eq hstep
          subst hts
          have hmem := List.mem_filter.mp hrow
          have hne : r ≠ r' := of_decide_eq_true hmem.2
          exact ExtDerives.genDelete i r r' σ S _ _ hs ht hstep hne (ih _ hs r σ S hmem.1)
      | addStab sector support =>
          have hts := eval_add_eq hstep
          subst hts
          rcases List.mem_append.mp hrow with hold | hnew
          · exact ExtDerives.genAdd i r σ S sector support _ _ hs ht hstep (ih _ hs r σ S hold)
          · have hrow' := List.mem_singleton.mp hnew
            have hr : r = canonicalMint s.used := congrArg Row.id hrow'
            have hσ : σ = sector := congrArg Row.sector hrow'
            have hS : S = support := congrArg Row.support hrow'
            subst hr; subst hσ; subst hS
            exact ExtDerives.genMint i σ S _ _ hs ht hstep
      | graft q sector ids =>
          have hts := eval_graft_eq hstep
          subst hts
          rcases mem_graftState_rows hrow with ⟨row0, hrow0, hshort⟩ | hminted
          · rw [graftShorten_eq] at hshort
            have hr : r = row0.id := congrArg Row.id hshort
            have hσ : σ = row0.sector := congrArg Row.sector hshort
            have hS : S = graftSupport q sector row0.sector row0.support :=
              congrArg Row.support hshort
            subst hr; subst hσ; subst hS
            have hfilter := List.mem_filter.mp hrow0
            have hnot : row0.id ∉ ids := by
              intro hc
              exact of_decide_eq_true hfilter.2 (List.contains_iff_mem.mpr hc)
            exact ExtDerives.genGraft i row0.id row0.sector row0.support q sector ids _ _ hs ht
              hstep hnot (ih _ hs row0.id row0.sector row0.support hfilter.1)
          · exact ExtDerives.genGraftMint i q sector ids _ _ _ hs ht hstep hminted
      | peel q tau r_id =>
          have hts := eval_peel_eq hstep
          subst hts
          obtain ⟨row0, hrow0, hshort⟩ := List.mem_map.mp hrow
          have hrow0' := List.mem_filter.mp hrow0
          have hid : (shortenRow q row0).id = row0.id := by
            unfold shortenRow; cases row0.support.contains q <;> rfl
          have hsec : (shortenRow q row0).sector = row0.sector := by
            unfold shortenRow; cases row0.support.contains q <;> rfl
          have hsup : (shortenRow q row0).support = peelSupport q row0.support := by
            unfold shortenRow peelSupport; cases row0.support.contains q <;> rfl
          have hr : row0.id = r := hid.symm.trans (congrArg Row.id hshort)
          have hσ : row0.sector = σ := hsec.symm.trans (congrArg Row.sector hshort)
          have hS : peelSupport q row0.support = S := hsup.symm.trans (congrArg Row.support hshort)
          rw [← hr, ← hσ, ← hS]
          have hnot : row0.id ≠ r_id := of_decide_eq_true hrow0'.2
          exact ExtDerives.genPeel i row0.id r_id row0.sector row0.support q tau _ _ hs ht hstep
            hnot (ih _ hs row0.id row0.sector row0.support hrow0'.1)
      | puncture q =>
          have hts := eval_puncture_eq hstep
          subst hts
          have hmem := List.mem_filter.mp hrow
          have hsurvives : ¬ S.contains q := of_decide_eq_true hmem.2
          exact ExtDerives.genPuncture i r σ S q _ _ hs ht hstep hsurvives (ih _ hs r σ S hmem.1)
      | extend delta adds =>
          have hts := eval_extend_eq hstep
          subst hts
          rcases List.mem_append.mp hrow with hold | hnew
          · exact ExtDerives.genExtend i r σ S delta adds _ _ hs ht hstep (ih _ hs r σ S hold)
          · exact ExtDerives.genExtendMint i delta adds _ _ ({ id := r, sector := σ, support := S })
              hs ht hstep hnew
      | hadamard T =>
          rcases eval_hadamard_cases hstep with ⟨hg, _⟩ | ⟨hsplit, _, hts0, _⟩
          · have hts := eval_hadamard_eq hstep hg
            cases hT : T.isEmpty with
            | true =>
                have hrow' : { id := r, sector := σ, support := S } ∈ s.rows := by
                  rw [hts] at hrow
                  simp [hadamardState, hT] at hrow
                  exact hrow
                have heq : ExtAnn.gen (i + 1) r (if T.isEmpty = true then σ else oppositeSector σ) S =
                    ExtAnn.gen (i + 1) r σ S := by simp [hT]
                rw [← heq]
                exact ExtDerives.genHadamard i r σ S T _ _ hs ht hstep hg (ih _ hs r σ S hrow')
            | false =>
                have hrow' : { id := r, sector := σ, support := S } ∈ t.rows := hrow
                rw [hts] at hrow'
                simp [hadamardState, hT] at hrow'
                obtain ⟨row0, hrow0, hswap⟩ := List.mem_map.mp hrow'
                have hr : row0.id = r := congrArg Row.id hswap
                have hσ : oppositeSector row0.sector = σ := congrArg Row.sector hswap
                have hS : row0.support = S := congrArg Row.support hswap
                have heq : ExtAnn.gen (i + 1) row0.id
                    (if T.isEmpty = true then row0.sector else oppositeSector row0.sector)
                    row0.support = ExtAnn.gen (i + 1) r σ S := by
                  simp [hT, hr, hσ, hS]
                rw [← heq]
                exact ExtDerives.genHadamard i row0.id row0.sector row0.support T _ _ hs ht hstep hg
                  (ih _ hs row0.id row0.sector row0.support hrow0)
          · have hrow' : ({ id := r, sector := σ, support := S } : Row) ∈
                (splitHadamardState s T).rows := by
              rw [← hts0]; exact hrow
            exact ExtDerives.genHadamardSplit i T _ _ _ hs ht hstep hsplit hrow'
      | rebase sector matrix =>
          have hts := eval_rebase_eq hstep
          subst hts
          rcases List.mem_append.mp hrow with hold | hnew
          · have hmem := List.mem_filter.mp hold
            have hsurvives : σ ≠ sector := of_decide_eq_true hmem.2
            exact ExtDerives.genRebase i r σ S sector matrix _ _ hs ht hstep hsurvives
              (ih _ hs r σ S hmem.1)
          · exact ExtDerives.genRebaseMint i sector matrix _ _
              ({ id := r, sector := σ, support := S }) hs ht hstep hnew
      | cnotSwap U =>
          have hts := eval_cnotSwap_eq hstep
          subst hts
          obtain ⟨row0, hrow0, htr⟩ := List.mem_map.mp hrow
          have hr : row0.id = r := congrArg Row.id htr
          have hσ : row0.sector = σ := congrArg Row.sector htr
          have hS : cnotSwapSupport s.Q U row0.sector row0.support = S :=
            congrArg Row.support htr
          have heq : ExtAnn.gen (i + 1) row0.id row0.sector
              (cnotSwapSupport s.Q U row0.sector row0.support) = ExtAnn.gen (i + 1) r σ S := by
            rw [hS, hr, hσ]
          rw [← heq]
          exact ExtDerives.genCnotSwap i row0.id row0.sector row0.support U _ _ hs ht hstep
            (ih _ hs row0.id row0.sector row0.support hrow0)
      | split QA R =>
          have hts := eval_split_eq hstep
          subst hts
          obtain ⟨hmem, hnot⟩ := (mem_deleteAll_rows R s _).mp hrow
          exact ExtDerives.genSplit i r σ S QA R _ _ hs ht hstep hnot (ih _ hs r σ S hmem)
      | seq _ _ => cases hm

theorem ext_seamRowsDerived_of_stepChain (dMeasure : ExtMeasure) (seamCert : SeamCertPolicy)
    {cs ds : List CodeState} (hchain : StepChain (cs ++ ds)) :
    ExtSeamRowsDerived dMeasure seamCert cs ds := by
  intro r σ S s h0 hrow
  have hpos : (cs ++ ds)[cs.length]? = some s := by
    have h := getElem?_shift_of_some (cs := cs) h0
    rwa [Nat.zero_add] at h
  exact ext_derives_gen_of_displayed dMeasure seamCert hchain cs.length s hpos r σ S hrow

/-- `W13` refutation shape for `ExtDerives`: any sentence false of a
    well-formed evaluation chain is underivable. -/
theorem ext_not_derivable_of_false (dMeasure : ExtMeasure)
    (hlaws : ExtMeasureLaws dMeasure)
    (seamCert : SeamCertPolicy) (hcert : SeamCertSound dMeasure seamCert)
    (cs : List CodeState) (hctxt : WellFormedContext cs) (hchain : Chain cs)
    {a : ExtAnn} (hfalse : ¬ ExtAnnTrue dMeasure cs a) :
    ¬ ExtDerives dMeasure seamCert cs a :=
  fun h => hfalse (ext_judgment_soundness dMeasure hlaws seamCert hcert cs hctxt hchain a h).truth

/-! ## Section 7: Worked closed-term derivations over the expanded operation set -/

/-- Worked example 1: `E-GLUE` as the closed term
    `⟨addStab Z [0,1,2,3], directSum (base glueExampleA) (base glueExampleB)⟩`.
    Derives `min(d_X(A), d_X(B)) ≤ d_X(pos 1)` across the expression-to-command
    boundary and concludes `TermModels` for `exactExtMeasure` with zero distance
    or seam-certificate hypotheses. -/
theorem glueExampleA_wf : EncodingWellFormed glueExampleA :=
  (wellFormedBool_iff _).mp (by decide)

theorem glueExampleB_wf : EncodingWellFormed glueExampleB :=
  (wellFormedBool_iff _).mp (by decide)

theorem eval_add_glueExample_seam :
    Eval (Command.addStab Sector.Z [0, 1, 2, 3])
      (directSumState glueExampleA glueExampleB)
      (addState (directSumState glueExampleA glueExampleB) Sector.Z [0, 1, 2, 3]) := by
  refine Eval.add ?_ (by decide) (by decide) ?_ ?_ rfl (by decide)
  · intro q hq
    simp [directSumState, glueExampleA, glueExampleB] at hq ⊢
    omega
  · intro row hrow hsec
    simp [directSumState, glueExampleA, glueExampleB] at hrow
    rcases hrow with rfl | rfl <;> decide
  · intro hspan
    have hb := (exact_inSpanRowsBool_iff _ _ _).mpr hspan
    exact Bool.false_ne_true (Eq.trans (by decide :
      inSpanRowsBool (directSumState glueExampleA glueExampleB).Q
        (sectorRows (directSumState glueExampleA glueExampleB) Sector.Z)
        (rowVector (directSumState glueExampleA glueExampleB).Q
          ⟨canonicalMint (directSumState glueExampleA glueExampleB).used,
            Sector.Z, [0, 1, 2, 3]⟩) = false).symm hb)

theorem worked_directSum_then_add_termModels :
    TermModels exactExtMeasure
      { command := Command.addStab Sector.Z [0, 1, 2, 3]
      , expr := StateExpr.directSum (StateExpr.base glueExampleA) (StateExpr.base glueExampleB) }
      (addState (directSumState glueExampleA glueExampleB) Sector.Z [0, 1, 2, 3])
      (ExtAnn.le
        (ExtAExpr.minOf (ExtAExpr.atom (.state glueExampleA Field.dX))
          (ExtAExpr.atom (.state glueExampleB Field.dX)))
        (ExtAExpr.atom (.pos 1 Field.dX))) := by
  let e := StateExpr.directSum (StateExpr.base glueExampleA) (StateExpr.base glueExampleB)
  let s0 := directSumState glueExampleA glueExampleB
  let s1 := addState s0 Sector.Z [0, 1, 2, 3]
  have he : EvalExpr e s0 :=
    EvalExpr.directSum (by decide) (by decide) (EvalExpr.base _) (EvalExpr.base _)
  have hterm : EvalTerm { command := Command.addStab Sector.Z [0, 1, 2, 3], expr := e } s1 :=
    EvalTerm.eval he eval_add_glueExample_seam
  have hbase : ExprBaseWF e := ⟨glueExampleA_wf, glueExampleB_wf⟩
  obtain ⟨s, cs, hs, htr, hsound⟩ :=
    ext_judgment_soundness_of_term_exact_uncertified hterm hbase
  have hseq : s = s0 := evalExpr_unique hs he
  subst hseq
  have htreq : cs = [s1] :=
    (Trace.unique htr (Trace.step rfl eval_add_glueExample_seam)).1
  subst htreq
  apply hsound
  have hds := ExtDerives.instDirectSumDX (dMeasure := exactExtMeasure) (seamCert := noSeamCert)
    (cs := [s0, s1]) (StateExpr.base glueExampleA) (StateExpr.base glueExampleB)
    glueExampleA glueExampleB s0 (EvalExpr.base _) (EvalExpr.base _) he
    glueExampleA_wf glueExampleB_wf
  have hroot := ExtDerives.instChainState (dMeasure := exactExtMeasure) (seamCert := noSeamCert)
    (cs := [s0, s1]) 0 Field.dX s0 rfl
  have hadd := ExtDerives.instAddDX (dMeasure := exactExtMeasure) (seamCert := noSeamCert)
    (cs := [s0, s1]) 0 Sector.Z [0, 1, 2, 3] s0 s1 rfl rfl eval_add_glueExample_seam
  exact ExtDerives.transit_eq_le _ _ _
    (ExtDerives.eq_sym _ _ (ExtDerives.transit_eq_eq _ _ _ hroot hds)) hadd

/-- Worked example 2: `E-GLUE` expression (`evalExpr_glue_example`) followed by
    `E-LOCAL-HADAMARD` (`T = Q`), deriving `min(d_Z(A), d_Z(B)) ≤ d_X(pos 1)`
    across the uncertified `E-GLUE` expression and the Gate 6 sector swap. -/
theorem eval_hadamard_glueExample :
    Eval (Command.hadamard (glueState glueExampleA glueExampleB glueExampleSeams).Q)
      (glueState glueExampleA glueExampleB glueExampleSeams)
      (hadamardState (glueState glueExampleA glueExampleB glueExampleSeams)
        (glueState glueExampleA glueExampleB glueExampleSeams).Q) :=
  Eval.hadamard (Or.inl (List.Perm.refl _)) rfl ((wellFormedBool_iff _).mp (by decide))

theorem worked_glue_then_hadamard_termModels :
    TermModels exactExtMeasure
      { command := Command.hadamard (glueState glueExampleA glueExampleB glueExampleSeams).Q
      , expr := StateExpr.glue (StateExpr.base glueExampleA) (StateExpr.base glueExampleB)
          glueExampleSeams }
      (hadamardState (glueState glueExampleA glueExampleB glueExampleSeams)
        (glueState glueExampleA glueExampleB glueExampleSeams).Q)
      (ExtAnn.le
        (ExtAExpr.minOf (ExtAExpr.atom (.state glueExampleA Field.dZ))
          (ExtAExpr.atom (.state glueExampleB Field.dZ)))
        (ExtAExpr.atom (.pos 1 Field.dX))) := by
  let e := StateExpr.glue (StateExpr.base glueExampleA) (StateExpr.base glueExampleB)
    glueExampleSeams
  let s0 := glueState glueExampleA glueExampleB glueExampleSeams
  let s1 := hadamardState s0 s0.Q
  have hterm : EvalTerm { command := Command.hadamard s0.Q, expr := e } s1 :=
    EvalTerm.eval evalExpr_glue_example eval_hadamard_glueExample
  have hbase : ExprBaseWF e := ⟨glueExampleA_wf, glueExampleB_wf⟩
  obtain ⟨s, cs, hs, htr, hsound⟩ :=
    ext_judgment_soundness_of_term_exact_uncertified hterm hbase
  have hseq : s = s0 := evalExpr_unique hs evalExpr_glue_example
  subst hseq
  have htreq : cs = [s1] :=
    (Trace.unique htr (Trace.step rfl eval_hadamard_glueExample)).1
  subst htreq
  apply hsound
  have hglue := ExtDerives.instGlueDZ (dMeasure := exactExtMeasure) (seamCert := noSeamCert)
    (cs := [s0, s1]) (StateExpr.base glueExampleA) (StateExpr.base glueExampleB)
    glueExampleSeams glueExampleA glueExampleB s0 (EvalExpr.base _) (EvalExpr.base _)
    evalExpr_glue_example glueExampleA_wf glueExampleB_wf
  have hroot := ExtDerives.instChainState (dMeasure := exactExtMeasure) (seamCert := noSeamCert)
    (cs := [s0, s1]) 0 Field.dZ s0 rfl
  have hhad := ExtDerives.instHadamardSwapDX (dMeasure := exactExtMeasure) (seamCert := noSeamCert)
    (cs := [s0, s1]) 0 s0.Q s0 s1 rfl rfl eval_hadamard_glueExample (by decide)
  exact ExtDerives.transit_le_eq _ _ _ hglue
    (ExtDerives.eq_sym _ _ (ExtDerives.transit_eq_eq _ _ _ hhad hroot))

/-- Worked example 3: certified `E-GLUE` equality via `admissibleSeamCert`
    (discharged for `exactExtMeasure` by `seamCertSound_admissibleSeam`):
    on `glueExampleA` and `glueExampleB` with `glueExampleSeams`, every
    minimum-weight Z-logical of each factor survives the Z seam check
    `[0, 1, 2, 3]` (Z-logicals commute with Z checks and are not spanned by
    the single Z seam check), so `d_Z(pos 0) = min(d_Z(A), d_Z(B))` holds in
    `TermModels` with zero remaining hypotheses. -/
theorem admissibleSeam_glueExample_Z :
    admissibleSeamCert glueExampleA glueExampleB glueExampleSeams := by
  have hcheckA : (logicalVectors glueExampleA Sector.Z).all (fun u =>
      !decide (weight u = exactDistance Sector.Z glueExampleA) ||
      isLogicalBool (glueState glueExampleA glueExampleB glueExampleSeams) Sector.Z
        (u ++ List.replicate glueExampleB.Q.length false)) = true := by decide
  have hcheckB : (logicalVectors glueExampleB Sector.Z).all (fun u =>
      !decide (weight u = exactDistance Sector.Z glueExampleB) ||
      isLogicalBool (glueState glueExampleA glueExampleB glueExampleSeams) Sector.Z
        (List.replicate glueExampleA.Q.length false ++ u)) = true := by decide
  constructor
  · intro u hlen hlog hw
    have hmem : u ∈ logicalVectors glueExampleA Sector.Z :=
      (mem_logicalVectors_iff glueExampleA Sector.Z u).mpr ⟨hlen, hlog⟩
    have hcond := List.all_eq_true.mp hcheckA u hmem
    rw [Bool.or_eq_true] at hcond
    rcases hcond with hneg | hsurv
    · rw [Bool.not_eq_true', decide_eq_false_iff_not] at hneg
      exact absurd hw hneg
    · exact ⟨hlen, hlog, hsurv⟩
  · intro u hlen hlog hw
    have hmem : u ∈ logicalVectors glueExampleB Sector.Z :=
      (mem_logicalVectors_iff glueExampleB Sector.Z u).mpr ⟨hlen, hlog⟩
    have hcond := List.all_eq_true.mp hcheckB u hmem
    rw [Bool.or_eq_true] at hcond
    rcases hcond with hneg | hsurv
    · rw [Bool.not_eq_true', decide_eq_false_iff_not] at hneg
      exact absurd hw hneg
    · exact ⟨hlen, hlog, hsurv⟩

theorem worked_glue_certified_termModels :
    TermModels exactExtMeasure
      { command := Command.skip
      , expr := StateExpr.glue (StateExpr.base glueExampleA) (StateExpr.base glueExampleB)
          glueExampleSeams }
      (glueState glueExampleA glueExampleB glueExampleSeams)
      (ExtAnn.eq
        (ExtAExpr.atom (.pos 0 Field.dZ))
        (ExtAExpr.minOf (ExtAExpr.atom (.state glueExampleA Field.dZ))
          (ExtAExpr.atom (.state glueExampleB Field.dZ)))) := by
  let e := StateExpr.glue (StateExpr.base glueExampleA) (StateExpr.base glueExampleB)
    glueExampleSeams
  let s0 := glueState glueExampleA glueExampleB glueExampleSeams
  have hterm : EvalTerm { command := Command.skip, expr := e } s0 :=
    EvalTerm.eval evalExpr_glue_example (Eval.skip s0)
  have hbase : ExprBaseWF e := ⟨glueExampleA_wf, glueExampleB_wf⟩
  obtain ⟨s, cs, hs, htr, hsound⟩ :=
    ext_judgment_soundness_of_term_exact_admissible hterm hbase
  have hseq : s = s0 := evalExpr_unique hs evalExpr_glue_example
  subst hseq
  have htreq : cs = [s0] :=
    (Trace.unique htr (Trace.step rfl (Eval.skip s0))).1
  subst htreq
  apply hsound
  have hcert := ExtDerives.instGlueCertDZ (dMeasure := exactExtMeasure)
    (seamCert := admissibleSeamCert) (cs := [s0, s0])
    (StateExpr.base glueExampleA) (StateExpr.base glueExampleB) glueExampleSeams
    glueExampleA glueExampleB s0 (EvalExpr.base _) (EvalExpr.base _)
    evalExpr_glue_example glueExampleA_wf glueExampleB_wf admissibleSeam_glueExample_Z
  have hroot := ExtDerives.instChainState (dMeasure := exactExtMeasure)
    (seamCert := admissibleSeamCert) (cs := [s0, s0]) 0 Field.dZ s0 rfl
  exact ExtDerives.transit_eq_eq _ _ _ hroot hcert

end CodeCalculus
