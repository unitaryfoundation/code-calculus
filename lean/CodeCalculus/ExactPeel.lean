import CodeCalculus.Gate6Soundness
import CodeCalculus.RanksFit

namespace CodeCalculus

/-!
# The §4.28 peel relations and the `k = 0` reading for the exact distance

`gate6_interval_soundness` (`Gate6Soundness.lean`) takes the three §4.28
relations of `E-PEEL` as the hypothesis `hpeel`, and `priced_interval_soundness`
takes the `k = 0` reading as `hk0`: a well-formed state with no logical qubit
has no logical operator, so every exact distance is `+∞`. This module
discharges both for the exact sector distance of `ExactDistance.lean`, read
in `Option Nat` by `exactDist`.

The peel relations follow the three maps of `spec/OPERATIONAL_SEMANTICS.md`
§4.28. The peeled qubit `q` sits at position `i = |Q1|` of the parent's
namespace `Q = Q1 ++ q :: Q2`, the peeled row `r` is the only row of the
selected sector `τ` through `q`, and `σ` is the opposite sector.

* Padding a child `τ`-logical with `false` at `i` gives a parent `τ`-logical
  of the same weight (`isLogical_insertAt_false`), so `d_τ ≤ d_τ'`.
* Restricting a parent `σ`-logical at `i` gives a child `σ`-logical of no
  larger weight (`isLogical_dropAt`), so `d_σ' ≤ d_σ`.
* Lifting a child `σ`-logical with the parity bit that makes it orthogonal to
  `r` gives a parent `σ`-logical of weight at most one more
  (`isLogical_insertAt_parity`), so `d_σ - 1 ≤ d_σ'`.

`exactDist_peel_relations` packages the three in the shape of `hpeel`, and
`peel_transformer_sound_exact` is the per-cell instance of
`peel_transformer_sound`.

The `k = 0` reading is the addition argument (`exactDist_k0`): a `σ`-logical
of a well-formed state is the support of an applicable `C-ADD-CHECK` (it
commutes with the opposite sector and lies outside the `σ`-span), the output
is well-formed (`wf_addState`), its ranks fit (`ranksFit_of_wf`), and
`stateK_addState` then reads `stateK s = stateK s' + 1`.

Everything is stated over `List Bool` vectors, as `ExactDistance.lean` is.
The positional operations `dropAt`, `insertAt`, and `entryAt` are defined
here so that their lemmas have the shapes the proofs need.
-/

/-! ## Positional operations on boolean vectors -/

/-- Remove the entry at position `i` (identity past the end). -/
def dropAt : Nat → List Bool → List Bool
  | _, [] => []
  | 0, _ :: xs => xs
  | i + 1, x :: xs => x :: dropAt i xs

/-- Insert `b` at position `i` (appended past the end). -/
def insertAt : Nat → Bool → List Bool → List Bool
  | 0, b, xs => b :: xs
  | _ + 1, b, [] => [b]
  | i + 1, b, x :: xs => x :: insertAt i b xs

/-- The entry at position `i`, `false` past the end. -/
def entryAt : Nat → List Bool → Bool
  | _, [] => false
  | 0, x :: _ => x
  | i + 1, _ :: xs => entryAt i xs

theorem dropAt_nil (i : Nat) : dropAt i [] = [] := by cases i <;> rfl

theorem entryAt_nil (i : Nat) : entryAt i [] = false := by cases i <;> rfl

theorem xorVec_nil_left : ∀ l : List Bool, xorVec [] l = []
  | [] => rfl
  | _ :: _ => rfl

theorem xorVec_nil_right : ∀ l : List Bool, xorVec l [] = []
  | [] => rfl
  | _ :: _ => rfl

theorem xorVec_cons (x y : Bool) (xs ys : List Bool) :
    xorVec (x :: xs) (y :: ys) = (x != y) :: xorVec xs ys := rfl

theorem dotPar_nil_left (b : List Bool) : dotPar [] b = 0 := by cases b <;> rfl

theorem dotPar_nil_right (a : List Bool) : dotPar a [] = 0 := by cases a <;> rfl

theorem dotPar_cons (x y : Bool) (xs ys : List Bool) :
    dotPar (x :: xs) (y :: ys) = (if x && y then 1 else 0) + dotPar xs ys := rfl

theorem dotPar_comm : ∀ (a b : List Bool), dotPar a b = dotPar b a
  | [], b => by rw [dotPar_nil_left, dotPar_nil_right]
  | _ :: _, [] => by rw [dotPar_nil_left, dotPar_nil_right]
  | x :: xs, y :: ys => by rw [dotPar_cons, dotPar_cons, dotPar_comm xs ys, Bool.and_comm]

theorem length_dropAt : ∀ (i : Nat) (a : List Bool), i < a.length →
    (dropAt i a).length = a.length - 1
  | _, [], h => absurd h (by rw [List.length_nil]; exact Nat.not_lt_zero _)
  | 0, _ :: xs, _ => by show xs.length = xs.length + 1 - 1; omega
  | i + 1, x :: xs, h => by
      show (x :: dropAt i xs).length = (x :: xs).length - 1
      rw [List.length_cons] at h
      rw [List.length_cons, List.length_cons, length_dropAt i xs (by omega)]
      omega

theorem length_insertAt : ∀ (i : Nat) (b : Bool) (a : List Bool), i ≤ a.length →
    (insertAt i b a).length = a.length + 1
  | 0, _, _, _ => rfl
  | i + 1, _, [], h => absurd h (by rw [List.length_nil]; omega)
  | i + 1, b, x :: xs, h => by
      show (x :: insertAt i b xs).length = (x :: xs).length + 1
      rw [List.length_cons] at h
      rw [List.length_cons, List.length_cons, length_insertAt i b xs (by omega)]

theorem dropAt_insertAt : ∀ (i : Nat) (b : Bool) (a : List Bool), i ≤ a.length →
    dropAt i (insertAt i b a) = a
  | 0, _, _, _ => rfl
  | i + 1, _, [], h => absurd h (by rw [List.length_nil]; omega)
  | i + 1, b, x :: xs, h => by
      show x :: dropAt i (insertAt i b xs) = x :: xs
      rw [List.length_cons] at h
      rw [dropAt_insertAt i b xs (by omega)]

theorem entryAt_insertAt : ∀ (i : Nat) (b : Bool) (a : List Bool), i ≤ a.length →
    entryAt i (insertAt i b a) = b
  | 0, _, _, _ => rfl
  | i + 1, _, [], h => absurd h (by rw [List.length_nil]; omega)
  | i + 1, b, x :: xs, h => by
      show entryAt i (insertAt i b xs) = b
      rw [List.length_cons] at h
      exact entryAt_insertAt i b xs (by omega)

theorem insertAt_entryAt_dropAt : ∀ (i : Nat) (a : List Bool), i < a.length →
    insertAt i (entryAt i a) (dropAt i a) = a
  | _, [], h => absurd h (by rw [List.length_nil]; exact Nat.not_lt_zero _)
  | 0, _ :: _, _ => rfl
  | i + 1, x :: xs, h => by
      show x :: insertAt i (entryAt i xs) (dropAt i xs) = x :: xs
      rw [List.length_cons] at h
      rw [insertAt_entryAt_dropAt i xs (by omega)]

theorem dropAt_xorVec : ∀ (i : Nat) (a b : List Bool),
    dropAt i (xorVec a b) = xorVec (dropAt i a) (dropAt i b)
  | _, [], _ => by rw [xorVec_nil_left, dropAt_nil, xorVec_nil_left]
  | _, _ :: _, [] => by rw [xorVec_nil_right, dropAt_nil, xorVec_nil_right]
  | 0, _ :: _, _ :: _ => by rw [xorVec_cons]; rfl
  | i + 1, x :: xs, y :: ys => by
      rw [xorVec_cons]
      show (x != y) :: dropAt i (xorVec xs ys) = xorVec (x :: dropAt i xs) (y :: dropAt i ys)
      rw [xorVec_cons, dropAt_xorVec i xs ys]

theorem dropAt_replicate_succ : ∀ (i m : Nat), i ≤ m →
    dropAt i (List.replicate (m + 1) false) = List.replicate m false
  | 0, _, _ => by rw [List.replicate_succ]; rfl
  | i + 1, 0, h => absurd h (by omega)
  | i + 1, m + 1, h => by
      rw [List.replicate_succ]
      show false :: dropAt i (List.replicate (m + 1) false) = List.replicate (m + 1) false
      rw [dropAt_replicate_succ i m (by omega)]
      rfl

theorem entryAt_replicate : ∀ (i n : Nat), entryAt i (List.replicate n false) = false
  | i, 0 => by rw [List.replicate_zero]; exact entryAt_nil i
  | 0, _ + 1 => by rw [List.replicate_succ]; rfl
  | i + 1, n + 1 => by rw [List.replicate_succ]; exact entryAt_replicate i n

theorem entryAt_xorVec : ∀ (i : Nat) (a b : List Bool), a.length = b.length →
    entryAt i (xorVec a b) = (entryAt i a != entryAt i b)
  | i, [], [], _ => by rw [xorVec_nil_left, entryAt_nil]; rfl
  | _, [], _ :: _, h => absurd h (by rw [List.length_nil, List.length_cons]; omega)
  | _, _ :: _, [], h => absurd h (by rw [List.length_nil, List.length_cons]; omega)
  | 0, _ :: _, _ :: _, _ => rfl
  | i + 1, x :: xs, y :: ys, h => by
      rw [xorVec_cons]
      show entryAt i (xorVec xs ys) = (entryAt i xs != entryAt i ys)
      rw [List.length_cons, List.length_cons] at h
      exact entryAt_xorVec i xs ys (by omega)

theorem combineRows_dropAt (i m : Nat) (hi : i ≤ m) :
    ∀ (vs : List (List Bool)) (cs : List Bool), (∀ v ∈ vs, v.length = m + 1) →
      dropAt i (combineRows (m + 1) vs cs) = combineRows m (vs.map (dropAt i)) cs
  | [], _, _ => by
      show dropAt i (List.replicate (m + 1) false) = List.replicate m false
      exact dropAt_replicate_succ i m hi
  | _ :: _, [], _ => by
      show dropAt i (List.replicate (m + 1) false) = List.replicate m false
      exact dropAt_replicate_succ i m hi
  | v :: vs, true :: cs, hv => by
      show dropAt i (xorVec v (combineRows (m + 1) vs cs)) =
        xorVec (dropAt i v) (combineRows m (vs.map (dropAt i)) cs)
      rw [dropAt_xorVec,
        combineRows_dropAt i m hi vs cs (fun u hu => hv u (List.mem_cons_of_mem v hu))]
  | v :: vs, false :: cs, hv => by
      show dropAt i (combineRows (m + 1) vs cs) = combineRows m (vs.map (dropAt i)) cs
      exact combineRows_dropAt i m hi vs cs (fun u hu => hv u (List.mem_cons_of_mem v hu))

theorem entryAt_combineRows_false (i n : Nat) :
    ∀ (vs : List (List Bool)) (cs : List Bool), (∀ v ∈ vs, v.length = n) →
      (∀ v ∈ vs, entryAt i v = false) → entryAt i (combineRows n vs cs) = false
  | [], _, _, _ => by
      show entryAt i (List.replicate n false) = false
      exact entryAt_replicate i n
  | _ :: _, [], _, _ => by
      show entryAt i (List.replicate n false) = false
      exact entryAt_replicate i n
  | v :: vs, true :: cs, hlen, h => by
      show entryAt i (xorVec v (combineRows n vs cs)) = false
      have hrest : ∀ u ∈ vs, u.length = n := fun u hu => hlen u (List.mem_cons_of_mem v hu)
      rw [entryAt_xorVec i v _
          (by rw [hlen v (List.mem_cons_self ..), combineRows_length n vs cs hrest]),
        h v (List.mem_cons_self ..),
        entryAt_combineRows_false i n vs cs hrest (fun u hu => h u (List.mem_cons_of_mem v hu))]
      rfl
  | v :: vs, false :: cs, hlen, h => by
      show entryAt i (combineRows n vs cs) = false
      exact entryAt_combineRows_false i n vs cs (fun u hu => hlen u (List.mem_cons_of_mem v hu))
        (fun u hu => h u (List.mem_cons_of_mem v hu))

theorem dotPar_insertAt : ∀ (i : Nat) (b : Bool) (a c : List Bool), i ≤ a.length → i < c.length →
    dotPar (insertAt i b a) c = (if b && entryAt i c then 1 else 0) + dotPar a (dropAt i c)
  | _, _, _, [], _, h => absurd h (by rw [List.length_nil]; exact Nat.not_lt_zero _)
  | 0, _, _, _ :: _, _, _ => rfl
  | i + 1, _, [], _ :: _, ha, _ => absurd ha (by rw [List.length_nil]; omega)
  | i + 1, b, x :: xs, y :: ys, ha, hc => by
      show dotPar (x :: insertAt i b xs) (y :: ys) =
        (if b && entryAt i ys then 1 else 0) + dotPar (x :: xs) (y :: dropAt i ys)
      rw [List.length_cons] at ha hc
      rw [dotPar_cons, dotPar_cons, dotPar_insertAt i b xs ys (by omega) (by omega),
        Nat.add_left_comm]

theorem dotPar_dropAt_dropAt : ∀ (i : Nat) (a b : List Bool), i < a.length → i < b.length →
    dotPar a b = (if entryAt i a && entryAt i b then 1 else 0) + dotPar (dropAt i a) (dropAt i b)
  | _, [], _, h, _ => absurd h (by rw [List.length_nil]; exact Nat.not_lt_zero _)
  | _, _ :: _, [], _, h => absurd h (by rw [List.length_nil]; exact Nat.not_lt_zero _)
  | 0, _ :: _, _ :: _, _, _ => rfl
  | i + 1, x :: xs, y :: ys, ha, hb => by
      show dotPar (x :: xs) (y :: ys) =
        (if entryAt i xs && entryAt i ys then 1 else 0) +
          dotPar (x :: dropAt i xs) (y :: dropAt i ys)
      rw [List.length_cons] at ha hb
      rw [dotPar_cons, dotPar_cons, dotPar_dropAt_dropAt i xs ys (by omega) (by omega),
        Nat.add_left_comm]

theorem dotPar_insertAt_false (i : Nat) (a c : List Bool) (ha : i ≤ a.length) (hc : i < c.length) :
    dotPar (insertAt i false a) c = dotPar a (dropAt i c) := by
  rw [dotPar_insertAt i false a c ha hc, Bool.false_and]
  show 0 + _ = _
  rw [Nat.zero_add]

theorem dotPar_dropAt_of_entry_false (i : Nat) (a c : List Bool) (ha : i < a.length)
    (hc : i < c.length) (h : entryAt i c = false) :
    dotPar (dropAt i a) (dropAt i c) = dotPar a c := by
  rw [dotPar_dropAt_dropAt i a c ha hc, h, Bool.and_false]
  show _ = 0 + _
  rw [Nat.zero_add]

theorem weight_cons (x : Bool) (xs : List Bool) :
    weight (x :: xs) = weight xs + (if x then 1 else 0) := by
  unfold weight
  rw [List.count_cons]
  cases x <;> rfl

theorem weight_dropAt_le : ∀ (i : Nat) (a : List Bool), weight (dropAt i a) ≤ weight a
  | i, [] => by rw [dropAt_nil]; exact Nat.le_refl _
  | 0, x :: xs => by
      show weight xs ≤ weight (x :: xs)
      rw [weight_cons]
      exact Nat.le_add_right _ _
  | i + 1, x :: xs => by
      show weight (x :: dropAt i xs) ≤ weight (x :: xs)
      rw [weight_cons, weight_cons]
      exact Nat.add_le_add_right (weight_dropAt_le i xs) _

theorem weight_insertAt : ∀ (i : Nat) (b : Bool) (a : List Bool), i ≤ a.length →
    weight (insertAt i b a) = weight a + (if b then 1 else 0)
  | 0, b, a, _ => by show weight (b :: a) = _; rw [weight_cons]
  | i + 1, _, [], h => absurd h (by rw [List.length_nil]; omega)
  | i + 1, b, x :: xs, h => by
      show weight (x :: insertAt i b xs) = weight (x :: xs) + (if b then 1 else 0)
      rw [List.length_cons] at h
      rw [weight_cons, weight_cons, weight_insertAt i b xs (by omega)]
      omega

theorem dropAt_append_length {α : Type} (f : α → Bool) :
    ∀ (l1 : List α) (x : α) (l2 : List α),
      dropAt l1.length ((l1 ++ x :: l2).map f) = (l1 ++ l2).map f
  | [], x, l2 => by rw [List.nil_append, List.map_cons, List.length_nil, List.nil_append]; rfl
  | a :: l1, x, l2 => by
      rw [List.cons_append, List.map_cons, List.length_cons, List.cons_append, List.map_cons]
      show f a :: dropAt l1.length ((l1 ++ x :: l2).map f) = f a :: (l1 ++ l2).map f
      rw [dropAt_append_length f l1 x l2]

theorem entryAt_append_length {α : Type} (f : α → Bool) :
    ∀ (l1 : List α) (x : α) (l2 : List α), entryAt l1.length ((l1 ++ x :: l2).map f) = f x
  | [], x, l2 => by rw [List.nil_append, List.map_cons, List.length_nil]; rfl
  | a :: l1, x, l2 => by
      rw [List.cons_append, List.map_cons, List.length_cons]
      show entryAt l1.length ((l1 ++ x :: l2).map f) = f x
      exact entryAt_append_length f l1 x l2

/-! ## Overlap parity through row vectors -/

theorem dotPar_map_map (f g : Nat → Bool) : ∀ Q : List Nat,
    dotPar (Q.map f) (Q.map g) = (Q.filter (fun x => f x && g x)).length
  | [] => rfl
  | x :: Q => by
      rw [List.map_cons, List.map_cons, dotPar_cons, dotPar_map_map f g Q]
      cases h : (f x && g x) with
      | true =>
          rw [List.filter_cons_of_pos (p := fun x => f x && g x) h, List.length_cons]
          show 1 + _ = _ + 1
          omega
      | false =>
          rw [List.filter_cons_of_neg (p := fun x => f x && g x) (by rw [h]; exact Bool.false_ne_true)]
          show 0 + _ = _
          rw [Nat.zero_add]

/-- The intersection size of two supports is the overlap parity count of
    their vectors over a duplicate-free namespace containing the first. -/
theorem supportIntersectionSize_eq_dotPar (Q a b : List Nat) (hQ : Q.Nodup) (ha : a.Nodup)
    (hsub : ∀ x ∈ a, x ∈ Q) :
    supportIntersectionSize a b =
      dotPar (Q.map (fun x => a.contains x)) (Q.map (fun x => b.contains x)) := by
  rw [supportIntersectionSize_eq_count Q a b hQ ha hsub, dotPar_map_map]

theorem supportIntersectionSize_eq_dotPar_rowVector (Q : List Nat) (a b : Row) (hQ : Q.Nodup)
    (ha : a.support.Nodup) (hsub : ∀ x ∈ a.support, x ∈ Q) :
    supportIntersectionSize a.support b.support = dotPar (rowVector Q a) (rowVector Q b) := by
  unfold rowVector
  exact supportIntersectionSize_eq_dotPar Q a.support b.support hQ ha hsub

theorem support_nodup_of_wf {s : CodeState} (hwf : EncodingWellFormed s) {row : Row}
    (hrow : row ∈ s.rows) : row.support.Nodup :=
  of_decide_eq_true (List.all_eq_true.mp hwf.2.2.2.2.1 row hrow)

/-- I1 read on row vectors: an X-row and a Z-row have even overlap. -/
theorem dotPar_rowVector_even_of_wf {s : CodeState} (hwf : EncodingWellFormed s) {a b : Row}
    (ha : a ∈ s.rows) (hb : b ∈ s.rows) (hab : b.sector = oppositeSector a.sector) :
    dotPar (rowVector s.Q a) (rowVector s.Q b) % 2 = 0 := by
  rw [← supportIntersectionSize_eq_dotPar_rowVector s.Q a b hwf.1 (support_nodup_of_wf hwf ha)
    (supports_subset_of_wf hwf a ha)]
  have hI1 : I1 s := hwf.2.2.2.2.2.2.1
  cases hsa : a.sector with
  | X =>
      rw [hsa] at hab
      exact hI1 a b ha hb hsa hab
  | Z =>
      rw [hsa] at hab
      rw [supportIntersectionSize_comm _ _ (support_nodup_of_wf hwf ha) (support_nodup_of_wf hwf hb)]
      exact hI1 b a hb ha hab hsa

/-! ## Rows, shortened rows, and the peeled display -/

theorem eq_of_id_eq_of_nodup : ∀ {rows : List Row}, (rows.map Row.id).Nodup →
    ∀ {a b : Row}, a ∈ rows → b ∈ rows → a.id = b.id → a = b
  | [], _, _, _, ha, _, _ => absurd ha (by simp)
  | x :: rest, hnd, a, b, ha, hb, h => by
      rw [List.map_cons] at hnd
      obtain ⟨hx, hrest⟩ := List.nodup_cons.mp hnd
      rcases List.mem_cons.mp ha with rfl | ha'
      · rcases List.mem_cons.mp hb with rfl | hb'
        · rfl
        · exact absurd (by rw [h]; exact List.mem_map_of_mem hb') hx
      · rcases List.mem_cons.mp hb with rfl | hb'
        · exact absurd (by rw [← h]; exact List.mem_map_of_mem ha') hx
        · exact eq_of_id_eq_of_nodup hrest ha' hb' h

theorem mem_sectorRows_iff (s : CodeState) (σ : Sector) (w : Row) :
    w ∈ sectorRows s σ ↔ w ∈ s.rows ∧ w.sector = σ := by
  simp only [sectorRows, List.mem_filter, decide_eq_true_eq]

theorem shortenRow_sector (q : Nat) (w : Row) : (shortenRow q w).sector = w.sector := by
  unfold shortenRow
  split <;> rfl

theorem shortenRow_contains (q x : Nat) (w : Row) (hx : x ≠ q) :
    (shortenRow q w).support.contains x = w.support.contains x := by
  unfold shortenRow
  split
  · rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_filter]
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, by simpa using hx⟩
  · rfl

/-- `Q = Q1 ++ q :: Q2` with `q` nowhere else, from membership and `Nodup`. -/
theorem split_of_mem_nodup {Q : List Nat} {q : Nat} (hq : q ∈ Q) (hnd : Q.Nodup) :
    ∃ Q1 Q2, Q = Q1 ++ q :: Q2 ∧ q ∉ Q1 ∧ q ∉ Q2 := by
  obtain ⟨Q1, Q2, heq⟩ := List.append_of_mem hq
  rw [heq] at hnd
  obtain ⟨_, hnd2, hdisj⟩ := List.nodup_append.mp hnd
  exact ⟨Q1, Q2, heq, fun h1 => hdisj q h1 q (List.mem_cons_self ..) rfl,
    (List.nodup_cons.mp hnd2).1⟩

theorem filter_ne_split (Q1 Q2 : List Nat) (q : Nat) (h1 : q ∉ Q1) (h2 : q ∉ Q2) :
    (Q1 ++ q :: Q2).filter (fun qa => qa ≠ q) = Q1 ++ Q2 := by
  rw [List.filter_append, List.filter_cons_of_neg (p := fun qa => decide (qa ≠ q)) (by simp)]
  have hQ1 : Q1.filter (fun qa => qa ≠ q) = Q1 := List.filter_eq_self.mpr (by
    intro a ha
    apply decide_eq_true
    intro h
    exact h1 (h ▸ ha))
  have hQ2 : Q2.filter (fun qa => qa ≠ q) = Q2 := List.filter_eq_self.mpr (by
    intro a ha
    apply decide_eq_true
    intro h
    exact h2 (h ▸ ha))
  rw [hQ1, hQ2]

/-- The vector of a shortened row over the peeled namespace is the parent
    vector with the peeled position removed. -/
theorem rowVector_shortenRow (Q1 Q2 : List Nat) (q : Nat) (h1 : q ∉ Q1) (h2 : q ∉ Q2) (w : Row) :
    rowVector (Q1 ++ Q2) (shortenRow q w) = dropAt Q1.length (rowVector (Q1 ++ q :: Q2) w) := by
  unfold rowVector
  rw [dropAt_append_length]
  apply List.map_congr_left
  intro x hx
  apply shortenRow_contains
  intro hxq
  rcases List.mem_append.mp hx with hl | hr
  · exact h1 (hxq ▸ hl)
  · exact h2 (hxq ▸ hr)

theorem filter_map_filter_comm (q r_id : Nat) (σ : Sector) : ∀ rows : List Row,
    ((rows.filter (fun row => row.id ≠ r_id)).map (shortenRow q)).filter (fun r => r.sector = σ) =
      ((rows.filter (fun r => r.sector = σ)).filter (fun row => row.id ≠ r_id)).map (shortenRow q)
  | [] => rfl
  | w :: rows => by
      by_cases hid : w.id = r_id
      · have hid' : ¬ (decide (w.id ≠ r_id) = true) := by simp [hid]
        rw [List.filter_cons_of_neg (p := fun row : Row => decide (row.id ≠ r_id)) hid']
        by_cases hsec : w.sector = σ
        · rw [List.filter_cons_of_pos (p := fun r : Row => decide (r.sector = σ)) (by simp [hsec]),
            List.filter_cons_of_neg (p := fun row : Row => decide (row.id ≠ r_id)) hid']
          exact filter_map_filter_comm q r_id σ rows
        · rw [List.filter_cons_of_neg (p := fun r : Row => decide (r.sector = σ)) (by simp [hsec])]
          exact filter_map_filter_comm q r_id σ rows
      · have hid' : decide (w.id ≠ r_id) = true := by simp [hid]
        rw [List.filter_cons_of_pos (p := fun row : Row => decide (row.id ≠ r_id)) hid', List.map_cons]
        by_cases hsec : w.sector = σ
        · rw [List.filter_cons_of_pos (p := fun r : Row => decide (r.sector = σ))
              (by simp [shortenRow_sector, hsec]),
            List.filter_cons_of_pos (p := fun r : Row => decide (r.sector = σ)) (by simp [hsec]),
            List.filter_cons_of_pos (p := fun row : Row => decide (row.id ≠ r_id)) hid', List.map_cons,
            filter_map_filter_comm q r_id σ rows]
        · rw [List.filter_cons_of_neg (p := fun r : Row => decide (r.sector = σ))
              (by simp [shortenRow_sector, hsec]),
            List.filter_cons_of_neg (p := fun r : Row => decide (r.sector = σ)) (by simp [hsec])]
          exact filter_map_filter_comm q r_id σ rows

/-- The displayed rows of a sector after the peel: the parent's rows of that
    sector other than the peeled row, shortened at `q`. -/
theorem sectorRows_peelState (s : CodeState) (q r_id : Nat) (σ : Sector) :
    sectorRows (peelState s q r_id) σ =
      ((sectorRows s σ).filter (fun row => row.id ≠ r_id)).map (shortenRow q) :=
  filter_map_filter_comm q r_id σ s.rows

/-- The peel's uniqueness premise: every selected-sector row through `q` is
    the peeled row. -/
theorem touching_unique {s : CodeState} {τ : Sector} {q : Nat} {r : Row}
    (hr : r ∈ s.rows) (hrτ : r.sector = τ) (hrq : r.support.contains q = true)
    (hlen1 : (touchingRows s τ q).length = 1) :
    ∀ w ∈ s.rows, w.sector = τ → w.support.contains q = true → w = r := by
  intro w hw hwτ hwq
  have hmem : ∀ x ∈ s.rows, x.sector = τ → x.support.contains q = true →
      x ∈ touchingRows s τ q := by
    intro x hx hxτ hxq
    unfold touchingRows
    rw [List.mem_filter]
    exact ⟨hx, decide_eq_true ⟨hxτ, hxq⟩⟩
  obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp hlen1
  have hw' := hmem w hw hwτ hwq
  have hr' := hmem r hr hrτ hrq
  rw [hy, List.mem_singleton] at hw' hr'
  rw [hw', hr']

theorem length_of_inSpanRows {Q : List Nat} {rows : List Row} {z : List Bool}
    (h : inSpanRows Q rows z) : z.length = Q.length := by
  obtain ⟨_, _, hcomb⟩ := h
  rw [← hcomb]
  exact combineRows_length _ _ _ (rowVectors_length Q rows)

/-! ## One peel, as a context -/

/-- The data of one admitted peel: `r` is the only `τ`-row through `q`, and
    `q` sits at position `|Q1|` of the parent namespace. -/
structure PeelCtx (s : CodeState) (q : Nat) (τ : Sector) (r : Row) (Q1 Q2 : List Nat) : Prop where
  wf : EncodingWellFormed s
  hr : r ∈ s.rows
  hrτ : r.sector = τ
  hrq : r.support.contains q = true
  uniq : ∀ w ∈ s.rows, w.sector = τ → w.support.contains q = true → w = r
  heq : s.Q = Q1 ++ q :: Q2
  h1 : q ∉ Q1
  h2 : q ∉ Q2

namespace PeelCtx

variable {s : CodeState} {q : Nat} {τ : Sector} {r : Row} {Q1 Q2 : List Nat}

theorem Q_length (P : PeelCtx s q τ r Q1 Q2) : s.Q.length = Q1.length + Q2.length + 1 := by
  rw [P.heq, List.length_append, List.length_cons]
  omega

theorem peel_Q (P : PeelCtx s q τ r Q1 Q2) : (peelState s q r.id).Q = Q1 ++ Q2 := by
  show s.Q.filter (fun qa => qa ≠ q) = Q1 ++ Q2
  rw [P.heq]
  exact filter_ne_split Q1 Q2 q P.h1 P.h2

theorem rowVector_peel (P : PeelCtx s q τ r Q1 Q2) (w : Row) :
    rowVector (peelState s q r.id).Q (shortenRow q w) = dropAt Q1.length (rowVector s.Q w) := by
  rw [P.peel_Q, P.heq]
  exact rowVector_shortenRow Q1 Q2 q P.h1 P.h2 w

theorem map_rowVector_peel (P : PeelCtx s q τ r Q1 Q2) (rows : List Row) :
    (rows.map (shortenRow q)).map (rowVector (peelState s q r.id).Q) =
      (rows.map (rowVector s.Q)).map (dropAt Q1.length) := by
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro w _
  exact P.rowVector_peel w

theorem entryAt_rowVector (P : PeelCtx s q τ r Q1 Q2) (w : Row) :
    entryAt Q1.length (rowVector s.Q w) = w.support.contains q := by
  rw [P.heq]
  unfold rowVector
  exact entryAt_append_length _ Q1 q Q2

theorem rowVector_lt (P : PeelCtx s q τ r Q1 Q2) (w : Row) :
    Q1.length < (rowVector s.Q w).length := by
  rw [rowVector_length, P.Q_length]
  omega

theorem entryAt_r (P : PeelCtx s q τ r Q1 Q2) : entryAt Q1.length (rowVector s.Q r) = true := by
  rw [P.entryAt_rowVector]
  exact P.hrq

/-- A `τ`-row other than `r` does not touch `q`. -/
theorem qfree (P : PeelCtx s q τ r Q1 Q2) {w : Row} (hw : w ∈ s.rows) (hwτ : w.sector = τ)
    (hwid : w.id ≠ r.id) : w.support.contains q = false := by
  cases hc : w.support.contains q with
  | false => rfl
  | true => exact absurd (congrArg Row.id (P.uniq w hw hwτ hc)) hwid

/-- An opposite-sector row is not `r`. -/
theorem opp_ne (P : PeelCtx s q τ r Q1 Q2) {w : Row} (hw : w ∈ s.rows)
    (hwσ : w.sector = oppositeSector τ) : w.id ≠ r.id := by
  intro hwid
  have hw' := eq_of_id_eq_of_nodup P.wf.2.1 hw P.hr hwid
  rw [hw', P.hrτ] at hwσ
  exact oppositeSector_ne τ hwσ.symm

/-- The opposite sector keeps every row through the peel, shortened. -/
theorem sectorRows_opp (P : PeelCtx s q τ r Q1 Q2) :
    sectorRows (peelState s q r.id) (oppositeSector τ) =
      (sectorRows s (oppositeSector τ)).map (shortenRow q) := by
  rw [sectorRows_peelState]
  have hself : (sectorRows s (oppositeSector τ)).filter (fun row => row.id ≠ r.id) =
      sectorRows s (oppositeSector τ) := List.filter_eq_self.mpr (by
    intro w hw
    obtain ⟨hw_rows, hwσ⟩ := (mem_sectorRows_iff s _ w).mp hw
    exact decide_eq_true (P.opp_ne hw_rows hwσ))
  rw [hself]

/-- The selected sector splits around `r`, and the peel removes exactly `r`. -/
theorem sectorRows_split (P : PeelCtx s q τ r Q1 Q2) : ∃ T1 T2, sectorRows s τ = T1 ++ r :: T2 ∧
    (sectorRows s τ).filter (fun row => row.id ≠ r.id) = T1 ++ T2 := by
  have hrT : r ∈ sectorRows s τ := (mem_sectorRows_iff s τ r).mpr ⟨P.hr, P.hrτ⟩
  obtain ⟨T1, T2, hT⟩ := List.append_of_mem hrT
  have hTnd : ((sectorRows s τ).map Row.id).Nodup := by
    unfold sectorRows
    exact List.Nodup.sublist (List.Sublist.map Row.id List.filter_sublist) P.wf.2.1
  rw [hT, List.map_append, List.map_cons] at hTnd
  obtain ⟨_, hnd2, hdisj⟩ := List.nodup_append.mp hTnd
  obtain ⟨hrnot2, _⟩ := List.nodup_cons.mp hnd2
  refine ⟨T1, T2, hT, ?_⟩
  have hT1 : T1.filter (fun row => row.id ≠ r.id) = T1 := List.filter_eq_self.mpr (by
    intro w hw
    apply decide_eq_true
    intro hwid
    exact hdisj w.id (List.mem_map_of_mem hw) r.id (List.mem_cons_self ..) hwid)
  have hT2 : T2.filter (fun row => row.id ≠ r.id) = T2 := List.filter_eq_self.mpr (by
    intro w hw
    apply decide_eq_true
    intro hwid
    apply hrnot2
    rw [← hwid]
    exact List.mem_map_of_mem hw)
  rw [hT, List.filter_append,
    List.filter_cons_of_neg (p := fun row : Row => decide (row.id ≠ r.id)) (by simp), hT1, hT2]

/-- Span membership restricts through the peel. -/
theorem inSpanRows_dropAt (P : PeelCtx s q τ r Q1 Q2) (rows : List Row) {z : List Bool}
    (hz : inSpanRows s.Q rows z) :
    inSpanRows (peelState s q r.id).Q (rows.map (shortenRow q)) (dropAt Q1.length z) := by
  obtain ⟨cs, hcs, hcomb⟩ := hz
  refine ⟨cs, by rw [hcs, List.length_map], ?_⟩
  rw [P.map_rowVector_peel, P.peel_Q, List.length_append]
  have hmlen : ∀ u ∈ rows.map (rowVector s.Q), u.length = Q1.length + Q2.length + 1 := by
    intro u hu
    rw [← P.Q_length]
    exact rowVectors_length _ _ u hu
  rw [← combineRows_dropAt Q1.length (Q1.length + Q2.length) (Nat.le_add_right _ _) _ _ hmlen,
    ← P.Q_length, hcomb]

/-- A child span member lifts to a parent span member with the same
    restriction. -/
theorem span_lift (P : PeelCtx s q τ r Q1 Q2) (rows : List Row) {y : List Bool}
    (hy : inSpanRows (peelState s q r.id).Q (rows.map (shortenRow q)) y) :
    ∃ z, inSpanRows s.Q rows z ∧ dropAt Q1.length z = y := by
  obtain ⟨cs, hcs, hcomb⟩ := hy
  rw [List.length_map] at hcs
  refine ⟨combineRows s.Q.length (rows.map (rowVector s.Q)) cs, ⟨cs, hcs, rfl⟩, ?_⟩
  rw [← hcomb, P.map_rowVector_peel, P.peel_Q, List.length_append, P.Q_length]
  have hmlen : ∀ u ∈ rows.map (rowVector s.Q), u.length = Q1.length + Q2.length + 1 := by
    intro u hu
    rw [← P.Q_length]
    exact rowVectors_length _ _ u hu
  exact combineRows_dropAt Q1.length (Q1.length + Q2.length) (Nat.le_add_right _ _) _ _ hmlen

/-! ### The three maps of §4.28 -/

/-- Padding a child `τ`-logical with `false` at the peeled position gives a
    parent `τ`-logical. -/
theorem isLogical_insertAt_false (P : PeelCtx s q τ r Q1 Q2)
    (v' : List Bool) (hlen : v'.length = Q1.length + Q2.length)
    (hv' : isLogicalBool (peelState s q r.id) τ v' = true) :
    isLogicalBool s τ (insertAt Q1.length false v') = true := by
  have hi : Q1.length ≤ v'.length := by rw [hlen]; exact Nat.le_add_right _ _
  unfold isLogicalBool at hv' ⊢
  rw [Bool.and_eq_true, List.all_eq_true] at hv' ⊢
  obtain ⟨horth, hspan⟩ := hv'
  refine ⟨?_, ?_⟩
  · intro w hw
    have hw' : shortenRow q w ∈ sectorRows (peelState s q r.id) (oppositeSector τ) := by
      rw [P.sectorRows_opp]
      exact List.mem_map_of_mem hw
    have h0 := horth _ hw'
    rw [P.rowVector_peel] at h0
    rw [dotPar_insertAt_false _ _ _ hi (P.rowVector_lt w)]
    exact h0
  · rw [Bool.not_eq_true'] at hspan ⊢
    cases hb : inSpanRowsBool s.Q (sectorRows s τ) (insertAt Q1.length false v') with
    | false => rfl
    | true =>
        exfalso
        have hin := (exact_inSpanRowsBool_iff _ _ _).mp hb
        obtain ⟨T1, T2, hT, hfilter⟩ := P.sectorRows_split
        -- every row of T1 ++ T2 is a τ-row other than r, hence q-free
        have hfree : ∀ w ∈ T1 ++ T2, entryAt Q1.length (rowVector s.Q w) = false := by
          intro w hw
          have hwf' : w ∈ (sectorRows s τ).filter (fun row => row.id ≠ r.id) := by
            rw [hfilter]
            exact hw
          obtain ⟨hwT, hwid⟩ := List.mem_filter.mp hwf'
          obtain ⟨hw_rows, hwτ⟩ := (mem_sectorRows_iff s τ w).mp hwT
          rw [P.entryAt_rowVector]
          exact P.qfree hw_rows hwτ (of_decide_eq_true hwid)
        have hT1free : ∀ u ∈ T1.map (rowVector s.Q), entryAt Q1.length u = false := by
          intro u hu
          obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hu
          exact hfree w (List.mem_append_left _ hw)
        have hT2free : ∀ u ∈ T2.map (rowVector s.Q), entryAt Q1.length u = false := by
          intro u hu
          obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hu
          exact hfree w (List.mem_append_right _ hw)
        have hT1len : ∀ u ∈ T1.map (rowVector s.Q), u.length = s.Q.length := rowVectors_length _ _
        have hT2len : ∀ u ∈ T2.map (rowVector s.Q), u.length = s.Q.length := rowVectors_length _ _
        have hrT2len : ∀ u ∈ (r :: T2).map (rowVector s.Q), u.length = s.Q.length :=
          rowVectors_length _ _
        -- split the coefficients around r
        obtain ⟨cs, hcs, hcomb⟩ := hin
        rw [hT, List.length_append, List.length_cons] at hcs
        have hcs_split : cs = cs.take T1.length ++ cs.drop T1.length :=
          (List.take_append_drop _ _).symm
        have hlt : (cs.take T1.length).length = T1.length := by rw [List.length_take]; omega
        obtain ⟨c, cs2, hd, hcs2⟩ : ∃ c cs2, cs.drop T1.length = c :: cs2 ∧ cs2.length = T2.length := by
          have hld : (cs.drop T1.length).length = T2.length + 1 := by rw [List.length_drop]; omega
          cases hdd : cs.drop T1.length with
          | nil =>
              exfalso
              rw [hdd, List.length_nil] at hld
              exact Nat.succ_ne_zero _ hld.symm
          | cons c cs2 =>
              refine ⟨c, cs2, rfl, ?_⟩
              rw [hdd, List.length_cons] at hld
              omega
        rw [hT, List.map_append, hcs_split, hd,
          combineRows_append s.Q.length _ _ _ _ hT1len hrT2len (by rw [hlt, List.length_map])
            (by rw [List.length_cons, hcs2, List.map_cons, List.length_cons, List.length_map])]
          at hcomb
        have hlen1 : (combineRows s.Q.length (T1.map (rowVector s.Q)) (cs.take T1.length)).length =
            s.Q.length := combineRows_length _ _ _ hT1len
        have hlen2 : (combineRows s.Q.length ((r :: T2).map (rowVector s.Q)) (c :: cs2)).length =
            s.Q.length := combineRows_length _ _ _ hrT2len
        -- the coefficient on r is false: the padded vector is zero at q, the
        -- other rows are zero there, and r is one there
        have hentry : entryAt Q1.length (insertAt Q1.length false v') = false :=
          entryAt_insertAt _ _ _ hi
        have hc : c = false := by
          cases c with
          | false => rfl
          | true =>
              exfalso
              have hxor : combineRows s.Q.length ((r :: T2).map (rowVector s.Q)) (true :: cs2) =
                  xorVec (rowVector s.Q r) (combineRows s.Q.length (T2.map (rowVector s.Q)) cs2) :=
                rfl
              rw [← hcomb, entryAt_xorVec _ _ _ (by rw [hlen1, hlen2]),
                entryAt_combineRows_false _ _ _ _ hT1len hT1free, hxor,
                entryAt_xorVec _ _ _ (by rw [rowVector_length, combineRows_length _ _ _ hT2len]),
                P.entryAt_r, entryAt_combineRows_false _ _ _ _ hT2len hT2free] at hentry
              exact absurd hentry (by decide)
        subst hc
        -- the padded vector is in the span of T1 ++ T2, so v' is in the child span
        have hcomb' : combineRows s.Q.length ((T1 ++ T2).map (rowVector s.Q))
            (cs.take T1.length ++ cs2) = insertAt Q1.length false v' := by
          rw [List.map_append, combineRows_append s.Q.length _ _ _ _ hT1len hT2len
            (by rw [hlt, List.length_map]) (by rw [hcs2, List.length_map]), ← hcomb]
          rfl
        have hpar : inSpanRows s.Q (T1 ++ T2) (insertAt Q1.length false v') :=
          ⟨cs.take T1.length ++ cs2,
            by rw [List.length_append, List.length_append, hlt, hcs2], hcomb'⟩
        have hchild := P.inSpanRows_dropAt (T1 ++ T2) hpar
        rw [dropAt_insertAt _ _ _ hi, ← hfilter, ← sectorRows_peelState] at hchild
        have := (exact_inSpanRowsBool_iff _ _ _).mpr hchild
        rw [hspan] at this
        exact Bool.false_ne_true this

/-- Restricting a parent `σ`-logical at the peeled position gives a child
    `σ`-logical, where `σ` is the sector opposite the peel's. -/
theorem isLogical_dropAt (P : PeelCtx s q τ r Q1 Q2)
    (u : List Bool) (hlen : u.length = s.Q.length)
    (hu : isLogicalBool s (oppositeSector τ) u = true) :
    isLogicalBool (peelState s q r.id) (oppositeSector τ) (dropAt Q1.length u) = true := by
  have hi : Q1.length < u.length := by rw [hlen, P.Q_length]; omega
  unfold isLogicalBool at hu ⊢
  rw [Bool.and_eq_true, List.all_eq_true] at hu ⊢
  obtain ⟨horth, hspan⟩ := hu
  rw [oppositeSector_involutive] at horth ⊢
  refine ⟨?_, ?_⟩
  · intro w' hw'
    rw [sectorRows_peelState] at hw'
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hw'
    obtain ⟨hwT, hwid⟩ := List.mem_filter.mp hw
    obtain ⟨hw_rows, hwτ⟩ := (mem_sectorRows_iff s τ w).mp hwT
    have hfree : entryAt Q1.length (rowVector s.Q w) = false := by
      rw [P.entryAt_rowVector]
      exact P.qfree hw_rows hwτ (of_decide_eq_true hwid)
    have h0 := horth w hwT
    rw [P.rowVector_peel, dotPar_dropAt_of_entry_false _ _ _ hi (P.rowVector_lt w) hfree]
    exact h0
  · rw [Bool.not_eq_true'] at hspan ⊢
    cases hb : inSpanRowsBool (peelState s q r.id).Q
        (sectorRows (peelState s q r.id) (oppositeSector τ)) (dropAt Q1.length u) with
    | false => rfl
    | true =>
        exfalso
        have hin := (exact_inSpanRowsBool_iff _ _ _).mp hb
        rw [P.sectorRows_opp] at hin
        obtain ⟨z, hz, hdz⟩ := P.span_lift _ hin
        have hiz : Q1.length < z.length := by rw [length_of_inSpanRows hz, P.Q_length]; omega
        -- both u and z have even overlap with r
        have hrT : r ∈ sectorRows s τ := (mem_sectorRows_iff s τ r).mpr ⟨P.hr, P.hrτ⟩
        have hur : dotPar u (rowVector s.Q r) % 2 = 0 := beq_iff_eq.mp (horth r hrT)
        have hzr : dotPar z (rowVector s.Q r) % 2 = 0 := by
          rw [dotPar_comm]
          apply dotPar_even_of_inSpanRows s.Q _ _ _ hz
          intro w hw
          obtain ⟨hw_rows, hwσ⟩ := (mem_sectorRows_iff s _ w).mp hw
          exact dotPar_rowVector_even_of_wf P.wf P.hr hw_rows (by rw [P.hrτ]; exact hwσ)
        rw [dotPar_dropAt_dropAt _ _ _ hi (P.rowVector_lt r), P.entryAt_r] at hur
        rw [dotPar_dropAt_dropAt _ _ _ hiz (P.rowVector_lt r), P.entryAt_r, hdz] at hzr
        -- so their entries at q agree, and they are equal
        have hent : entryAt Q1.length u = entryAt Q1.length z := by
          cases hu' : entryAt Q1.length u <;> cases hz' : entryAt Q1.length z
          · rfl
          · exfalso
            rw [hu'] at hur
            rw [hz'] at hzr
            simp at hur hzr <;> omega
          · exfalso
            rw [hu'] at hur
            rw [hz'] at hzr
            simp at hur hzr <;> omega
          · rfl
        have huz : u = z := by
          rw [← insertAt_entryAt_dropAt Q1.length u hi, ← insertAt_entryAt_dropAt Q1.length z hiz,
            hent, hdz]
        have hsu : inSpanRows s.Q (sectorRows s (oppositeSector τ)) u := by
          rw [huz]
          exact hz
        have := (exact_inSpanRowsBool_iff _ _ _).mpr hsu
        rw [hspan] at this
        exact Bool.false_ne_true this

/-- Lifting a child `σ`-logical with a bit of the right parity against `r`
    gives a parent `σ`-logical. -/
theorem isLogical_insertAt_of_parity (P : PeelCtx s q τ r Q1 Q2)
    (y : List Bool) (hlen : y.length = Q1.length + Q2.length)
    (hy : isLogicalBool (peelState s q r.id) (oppositeSector τ) y = true) (b : Bool)
    (hb : ((if b then 1 else 0) + dotPar y (dropAt Q1.length (rowVector s.Q r))) % 2 = 0) :
    isLogicalBool s (oppositeSector τ) (insertAt Q1.length b y) = true := by
  have hi : Q1.length ≤ y.length := by rw [hlen]; exact Nat.le_add_right _ _
  unfold isLogicalBool at hy ⊢
  rw [Bool.and_eq_true, List.all_eq_true] at hy ⊢
  obtain ⟨horth, hspan⟩ := hy
  rw [oppositeSector_involutive] at horth ⊢
  refine ⟨?_, ?_⟩
  · intro w hw
    obtain ⟨hw_rows, hwτ⟩ := (mem_sectorRows_iff s τ w).mp hw
    rw [dotPar_insertAt _ _ _ _ hi (P.rowVector_lt w)]
    by_cases hwr : w.id = r.id
    · have hwr' : w = r := eq_of_id_eq_of_nodup P.wf.2.1 hw_rows P.hr hwr
      subst hwr'
      rw [P.entryAt_r, Bool.and_true]
      exact beq_iff_eq.mpr hb
    · have hfree : entryAt Q1.length (rowVector s.Q w) = false := by
        rw [P.entryAt_rowVector]
        exact P.qfree hw_rows hwτ hwr
      rw [hfree, Bool.and_false]
      show ((0 + dotPar y (dropAt Q1.length (rowVector s.Q w))) % 2 == 0) = true
      rw [Nat.zero_add]
      have hw' : shortenRow q w ∈ sectorRows (peelState s q r.id) τ := by
        rw [sectorRows_peelState]
        apply List.mem_map_of_mem
        rw [List.mem_filter]
        exact ⟨hw, decide_eq_true hwr⟩
      have h0 := horth _ hw'
      rw [P.rowVector_peel] at h0
      exact h0
  · rw [Bool.not_eq_true'] at hspan ⊢
    cases hb' : inSpanRowsBool s.Q (sectorRows s (oppositeSector τ)) (insertAt Q1.length b y) with
    | false => rfl
    | true =>
        exfalso
        have hin := (exact_inSpanRowsBool_iff _ _ _).mp hb'
        have hchild := P.inSpanRows_dropAt _ hin
        rw [dropAt_insertAt _ _ _ hi, ← P.sectorRows_opp] at hchild
        have := (exact_inSpanRowsBool_iff _ _ _).mpr hchild
        rw [hspan] at this
        exact Bool.false_ne_true this

/-- The lift of §4.28: a child `σ`-logical has a parent `σ`-logical of weight
    at most one more. -/
theorem isLogical_insertAt_parity (P : PeelCtx s q τ r Q1 Q2)
    (y : List Bool) (hlen : y.length = Q1.length + Q2.length)
    (hy : isLogicalBool (peelState s q r.id) (oppositeSector τ) y = true) :
    ∃ v, isLogicalBool s (oppositeSector τ) v = true ∧ weight v ≤ weight y + 1 ∧
      v.length = s.Q.length := by
  have hi : Q1.length ≤ y.length := by rw [hlen]; exact Nat.le_add_right _ _
  rcases Nat.mod_two_eq_zero_or_one (dotPar y (dropAt Q1.length (rowVector s.Q r))) with h0 | h1
  · refine ⟨insertAt Q1.length false y, P.isLogical_insertAt_of_parity y hlen hy false ?_, ?_, ?_⟩
    · show (0 + dotPar y (dropAt Q1.length (rowVector s.Q r))) % 2 = 0
      rw [Nat.zero_add]
      exact h0
    · rw [weight_insertAt _ _ _ hi]
      show weight y + 0 ≤ weight y + 1
      omega
    · rw [length_insertAt _ _ _ hi, hlen, P.Q_length]
  · refine ⟨insertAt Q1.length true y, P.isLogical_insertAt_of_parity y hlen hy true ?_, ?_, ?_⟩
    · show (1 + dotPar y (dropAt Q1.length (rowVector s.Q r))) % 2 = 0
      omega
    · rw [weight_insertAt _ _ _ hi]
      show weight y + 1 ≤ weight y + 1
      exact Nat.le_refl _
    · rw [length_insertAt _ _ _ hi, hlen, P.Q_length]

end PeelCtx

/-! ## From logicals to distances -/

theorem mem_logicalVectors_iff (s : CodeState) (σ : Sector) (v : List Bool) :
    v ∈ logicalVectors s σ ↔ v.length = s.Q.length ∧ isLogicalBool s σ v = true := by
  unfold logicalVectors
  rw [List.mem_filter, exact_mem_allBoolLists]

theorem exactDistance?_le_of_mem {s : CodeState} {σ : Sector} {v : List Bool}
    (hv : v ∈ logicalVectors s σ) : ∃ m, exactDistance? σ s = some m ∧ m ≤ weight v := by
  cases h : exactDistance? σ s with
  | none =>
      exfalso
      have hnil := (exactDistance?_eq_none_iff σ s).mp h
      rw [hnil] at hv
      simp at hv
  | some m =>
      refine ⟨m, rfl, ?_⟩
      have h1 := exactDistance_eq_getD σ s
      rw [h] at h1
      have h2 : exactDistance σ s ≤ weight v :=
        minWeight_le_of_mem (s.Q.length + 1) (logicalVectors s σ) hv
      have h3 : exactDistance σ s = m := h1
      rw [← h3]
      exact h2

/-- A weight-nonincreasing map from the `σ'`-logicals of `t` into the
    `σ`-logicals of `s` bounds the exact distance of `s` by that of `t`. -/
theorem leOpt_exactDistance?_of_map {s t : CodeState} {σ σ' : Sector}
    (h : ∀ v' ∈ logicalVectors t σ', ∃ v ∈ logicalVectors s σ, weight v ≤ weight v') :
    leOpt (exactDistance? σ s) (exactDistance? σ' t) := by
  cases ht : exactDistance? σ' t with
  | none => exact leOpt_none _
  | some m =>
      obtain ⟨v', hv', hw'⟩ := minWeight?_attained (logicalVectors t σ') m ht
      obtain ⟨v, hv, hle⟩ := h v' hv'
      obtain ⟨m0, hm0, hle0⟩ := exactDistance?_le_of_mem hv
      rw [hm0]
      show m0 ≤ m
      omega

/-- The same with a weight increase of at most one: the predecessor of the
    exact distance of `s` is bounded by that of `t`. -/
theorem leOpt_predOpt_exactDistance?_of_map {s t : CodeState} {σ σ' : Sector}
    (h : ∀ v' ∈ logicalVectors t σ', ∃ v ∈ logicalVectors s σ, weight v ≤ weight v' + 1) :
    leOpt (predOpt (exactDistance? σ s)) (exactDistance? σ' t) := by
  cases ht : exactDistance? σ' t with
  | none => exact leOpt_none _
  | some m =>
      obtain ⟨v', hv', hw'⟩ := minWeight?_attained (logicalVectors t σ') m ht
      obtain ⟨v, hv, hle⟩ := h v' hv'
      obtain ⟨m0, hm0, hle0⟩ := exactDistance?_le_of_mem hv
      rw [hm0]
      show m0 - 1 ≤ m
      omega

/-- The `Option Nat` reading of `Gate6Soundness.lean` is `exactDistance?`. -/
theorem exactDistOpt_eq_exactDistance? (σ : Sector) (s : CodeState) :
    exactDistOpt σ s = exactDistance? σ s := by
  unfold exactDistOpt
  rw [exactDistance_eq_getD]
  cases h : exactDistance? σ s with
  | none => simp
  | some d =>
      have hd := le_Q_length_of_exactDistance?_eq_some h
      have hne : d ≠ s.Q.length + 1 := by omega
      simp [hne]

/-! ## The §4.28 relations for `exactDist` -/

/-- The three §4.28 relations of `E-PEEL` for the exact distance, in the
    shape of the hypothesis `hpeel` of `gate6_interval_soundness`. -/
theorem exactDist_peel_relations {q : Nat} {τ : Sector} {r_id : Nat} {s s' : CodeState}
    (hwf : EncodingWellFormed s) (hEval : Eval (Command.peel q τ r_id) s s') :
    (if τ = Sector.X then leOpt (exactDist s).x (exactDist s').x
      else leOpt (exactDist s).z (exactDist s').z) ∧
    (if τ = Sector.X then leOpt (exactDist s').z (exactDist s).z
      else leOpt (exactDist s').x (exactDist s).x) ∧
    (if τ = Sector.X then leOpt (predOpt (exactDist s).z) (exactDist s').z
      else leOpt (predOpt (exactDist s).x) (exactDist s').x) := by
  have hpre : q ∈ s.Q ∧
      (∃ row, row ∈ s.rows ∧ row.id = r_id ∧ row.sector = τ ∧ row.support.contains q = true) ∧
      (touchingRows s τ q).length = 1 ∧ s' = peelState s q r_id := by
    cases hEval with
    | peel hq hrow hlen _ hs' _ => exact ⟨hq, hrow, hlen, hs'⟩
  obtain ⟨hq, ⟨r, hr, hrid, hrτ, hrq⟩, hlen1, hs'⟩ := hpre
  subst hrid
  subst hs'
  obtain ⟨Q1, Q2, heq, h1, h2⟩ := split_of_mem_nodup hq hwf.1
  have P : PeelCtx s q τ r Q1 Q2 :=
    ⟨hwf, hr, hrτ, hrq, touching_unique hr hrτ hrq hlen1, heq, h1, h2⟩
  have hsel : leOpt (exactDistOpt τ s) (exactDistOpt τ (peelState s q r.id)) := by
    rw [exactDistOpt_eq_exactDistance?, exactDistOpt_eq_exactDistance?]
    apply leOpt_exactDistance?_of_map
    intro v' hv'
    obtain ⟨hlen', hlog'⟩ := (mem_logicalVectors_iff _ _ _).mp hv'
    rw [P.peel_Q, List.length_append] at hlen'
    have hi : Q1.length ≤ v'.length := by rw [hlen']; exact Nat.le_add_right _ _
    refine ⟨insertAt Q1.length false v', ?_, ?_⟩
    · rw [mem_logicalVectors_iff]
      refine ⟨?_, P.isLogical_insertAt_false v' hlen' hlog'⟩
      rw [length_insertAt _ _ _ hi, hlen', P.Q_length]
    · rw [weight_insertAt _ _ _ hi]
      show weight v' + 0 ≤ weight v'
      omega
  have hopp : leOpt (exactDistOpt (oppositeSector τ) (peelState s q r.id))
      (exactDistOpt (oppositeSector τ) s) := by
    rw [exactDistOpt_eq_exactDistance?, exactDistOpt_eq_exactDistance?]
    apply leOpt_exactDistance?_of_map
    intro u hu
    obtain ⟨hlen, hlog⟩ := (mem_logicalVectors_iff _ _ _).mp hu
    refine ⟨dropAt Q1.length u, ?_, weight_dropAt_le _ _⟩
    rw [mem_logicalVectors_iff]
    refine ⟨?_, P.isLogical_dropAt u hlen hlog⟩
    rw [length_dropAt _ _ (by rw [hlen, P.Q_length]; omega), hlen, P.Q_length, P.peel_Q,
      List.length_append]
    omega
  have hlow : leOpt (predOpt (exactDistOpt (oppositeSector τ) s))
      (exactDistOpt (oppositeSector τ) (peelState s q r.id)) := by
    rw [exactDistOpt_eq_exactDistance?, exactDistOpt_eq_exactDistance?]
    apply leOpt_predOpt_exactDistance?_of_map
    intro y hy
    obtain ⟨hlen, hlog⟩ := (mem_logicalVectors_iff _ _ _).mp hy
    rw [P.peel_Q, List.length_append] at hlen
    obtain ⟨v, hv, hwv, hlenv⟩ := P.isLogical_insertAt_parity y hlen hlog
    exact ⟨v, (mem_logicalVectors_iff _ _ _).mpr ⟨hlenv, hv⟩, hwv⟩
  cases τ with
  | X =>
      rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl]
      exact ⟨hsel, hopp, hlow⟩
  | Z =>
      have hne : ¬ (Sector.Z = Sector.X) := by decide
      rw [ite_eq_right hne, ite_eq_right hne, ite_eq_right hne]
      exact ⟨hsel, hopp, hlow⟩

/-- `E-PEEL` for the exact distance, from the transition's premises: the
    §4.28 relations are discharged, and only the two optional prices of
    `JUDGMENT_LAYER.md` §2a remain as hypotheses, as in
    `peel_transformer_sound`. -/
theorem peel_transformer_sound_exact {q : Nat} {τ : Sector} {r_id : Nat} {s s' : CodeState}
    (hwf : EncodingWellFormed s) (hEval : Eval (Command.peel q τ r_id) s s')
    {expose avoid : Option Nat}
    (hexpose : ∀ p, expose = some p →
      if τ = Sector.X then (exactDist s').z = minOpt (exactDist s).z (some p)
      else (exactDist s').x = minOpt (exactDist s).x (some p))
    (havoid : ∀ w, avoid = some w →
      if τ = Sector.X then (exactDist s').x = some w else (exactDist s').z = some w)
    (L : DistanceLedger) (hL : LedgerSound (exactDist s) L) :
    LedgerSound (exactDist s') (peelLedger τ L expose avoid) := by
  obtain ⟨hsel, hopp, hlow⟩ := exactDist_peel_relations hwf hEval
  exact peel_transformer_sound exactDist exactDist_full τ hsel hopp hlow hexpose havoid L hL

/-! ## The `k = 0` reading for `exactDist` -/

/-- The qubits at which a vector over `Q` is `true`, in the order of `Q`. -/
def supportOf : List Nat → List Bool → List Nat
  | x :: Q, true :: v => x :: supportOf Q v
  | _ :: Q, false :: v => supportOf Q v
  | _, _ => []

theorem supportOf_cons_true (x : Nat) (Q : List Nat) (v : List Bool) :
    supportOf (x :: Q) (true :: v) = x :: supportOf Q v := rfl

theorem supportOf_cons_false (x : Nat) (Q : List Nat) (v : List Bool) :
    supportOf (x :: Q) (false :: v) = supportOf Q v := rfl

theorem supportOf_sublist : ∀ (Q : List Nat) (v : List Bool), (supportOf Q v).Sublist Q
  | [], [] => List.Sublist.refl _
  | [], _ :: _ => List.Sublist.refl _
  | _ :: _, [] => List.nil_sublist _
  | x :: Q, true :: v => List.Sublist.cons_cons x (supportOf_sublist Q v)
  | x :: Q, false :: v => List.Sublist.cons x (supportOf_sublist Q v)

theorem supportOf_subset {Q : List Nat} {v : List Bool} {x : Nat} (h : x ∈ supportOf Q v) : x ∈ Q :=
  (supportOf_sublist Q v).subset h

/-- The vector is recovered from its support over a duplicate-free namespace. -/
theorem contains_supportOf : ∀ (Q : List Nat) (v : List Bool), Q.Nodup → v.length = Q.length →
    Q.map (fun x => (supportOf Q v).contains x) = v
  | [], [], _, _ => rfl
  | [], _ :: _, _, h =>
      absurd h (by rw [List.length_cons, List.length_nil]; exact Nat.succ_ne_zero _)
  | _ :: _, [], _, h =>
      absurd h (by rw [List.length_cons, List.length_nil]; exact fun h' => Nat.succ_ne_zero _ h'.symm)
  | x :: Q, b :: v, hnd, hlen => by
      obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
      have hlen' : v.length = Q.length := by
        rw [List.length_cons, List.length_cons] at hlen
        omega
      have ih := contains_supportOf Q v hnd' hlen'
      cases b with
      | true =>
          rw [supportOf_cons_true, List.map_cons]
          have hhead : (x :: supportOf Q v).contains x = true := by simp
          have htail : Q.map (fun y => (x :: supportOf Q v).contains y) = v := by
            calc Q.map (fun y => (x :: supportOf Q v).contains y)
                = Q.map (fun y => (supportOf Q v).contains y) := by
                    apply List.map_congr_left
                    intro y hy
                    have hyx : y ≠ x := fun h => hx (h ▸ hy)
                    simp [hyx]
              _ = v := ih
          rw [hhead, htail]
      | false =>
          rw [supportOf_cons_false, List.map_cons, ih]
          have hhead : (supportOf Q v).contains x = false := by
            cases hc : (supportOf Q v).contains x with
            | false => rfl
            | true => exact absurd (supportOf_subset (List.contains_iff_mem.mp hc)) hx
          rw [hhead]

/-- A `σ`-logical of a well-formed state is the support of an applicable
    `C-ADD-CHECK`, so the state has a logical qubit. -/
theorem stateK_ne_zero_of_logical {s : CodeState} (hwf : EncodingWellFormed s) {σ : Sector}
    {v : List Bool} (hv : v ∈ logicalVectors s σ) : stateK s ≠ 0 := by
  obtain ⟨hlen, hlog⟩ := (mem_logicalVectors_iff _ _ _).mp hv
  unfold isLogicalBool at hlog
  rw [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hlog
  obtain ⟨horth, hspan⟩ := hlog
  have hQ : s.Q.Nodup := hwf.1
  obtain ⟨S, hS⟩ : ∃ S, S = sortNat (supportOf s.Q v) := ⟨_, rfl⟩
  have hperm : S.Perm (supportOf s.Q v) := by rw [hS]; exact sortNat_perm _
  have hsorted : List.Pairwise (fun x1 x2 => x1 ≤ x2) S := by rw [hS]; exact sortNat_sorted _
  have hsub : supportSubset S s.Q := fun x hx => supportOf_subset (hperm.mem_iff.mp hx)
  have hnd : S.Nodup := hperm.nodup_iff.mpr (List.Nodup.sublist (supportOf_sublist _ _) hQ)
  have hvec : rowVector s.Q (addRow s σ S) = v := by
    unfold rowVector addRow
    refine Eq.trans ?_ (contains_supportOf s.Q v hQ hlen)
    apply List.map_congr_left
    intro x _
    show S.contains x = (supportOf s.Q v).contains x
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
    exact hperm.mem_iff
  have hcomm : ∀ row ∈ s.rows, row.sector = oppositeSector σ →
      supportIntersectionSize S row.support % 2 = 0 := by
    intro row hrow hsec
    rw [supportIntersectionSize_eq_dotPar s.Q S row.support hQ hnd hsub]
    have h0 := horth row ((mem_sectorRows_iff s _ row).mpr ⟨hrow, hsec⟩)
    have hv' : s.Q.map (fun x => S.contains x) = v := hvec
    rw [hv']
    exact beq_iff_eq.mp h0
  have hnotspan : ¬inSpanRows s.Q (sectorRows s σ) (rowVector s.Q (addRow s σ S)) := by
    intro h
    rw [hvec] at h
    have := (exact_inSpanRowsBool_iff _ _ _).mpr h
    rw [hspan] at this
    exact Bool.false_ne_true this
  have hwf' := wf_addState s σ S hwf hsub hnd hsorted hcomm hnotspan
  have hk := stateK_addState s hQ σ S hnotspan (ranksFit_of_wf _ hwf')
  rw [hk]
  exact Nat.succ_ne_zero _

theorem logicalVectors_eq_nil_of_stateK_zero {s : CodeState} (hwf : EncodingWellFormed s)
    (hk : stateK s = 0) (σ : Sector) : logicalVectors s σ = [] := by
  cases h : logicalVectors s σ with
  | nil => rfl
  | cons v vs =>
      exfalso
      apply stateK_ne_zero_of_logical hwf (σ := σ) (v := v) _ hk
      rw [h]
      exact List.mem_cons_self ..

/-- The `k = 0` reading for the exact distance: a well-formed state with no
    logical qubit has no logical operator in either sector, so every exact
    distance is `+∞`. This is the hypothesis `hk0` of
    `priced_interval_soundness` and `gate6_interval_soundness`. -/
theorem exactDist_k0 (s : CodeState) (hwf : EncodingWellFormed s) (hk : stateK s = 0) :
    (exactDist s).full = none ∧ (exactDist s).x = none ∧ (exactDist s).z = none := by
  have hopt : ∀ σ, exactDistOpt σ s = none := by
    intro σ
    rw [exactDistOpt_eq_exactDistance?, exactDistance?_eq_none_iff]
    exact logicalVectors_eq_nil_of_stateK_zero hwf hk σ
  refine ⟨?_, hopt Sector.X, hopt Sector.Z⟩
  show minOpt (exactDistOpt Sector.X s) (exactDistOpt Sector.Z s) = none
  rw [hopt, hopt]
  rfl

end CodeCalculus
