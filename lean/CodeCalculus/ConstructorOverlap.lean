import CodeCalculus.ConstructorAssembly

/-!
# Pairwise even overlap for `L-LIFTED`, `L-GROUP-ALGEBRA`, and `A-CONCAT`

The §4.34 arguments of `spec/OPERATIONAL_SEMANTICS.md` for the three typed
constructors whose overlap was a hypothesis of their well-formedness
theorems.

* `L-GROUP-ALGEBRA`: `twoblock_naturalOrthogonal`, for every list of cyclic
  orders and every pair of algebra elements. The two blocks of an `X`-row
  and a `Z`-row pair to the same count (`dotPar_regRow_swap`), which is
  commutativity of the group algebra read through the reflection
  `g ↦ h - (g - h')` of the group (`reflect_count`).
* `L-LIFTED`: `lift_naturalOrthogonal`, for every list of cyclic orders and
  every pair of matrices. An `X`-row `(a, j, h)` and a `Z`-row `(i, b, h')`
  meet on the left block `(i, j)` and the right block `(a, b)`, in the same
  number of qubits (`dotPar_regRow_inv_inv`).
* `A-CONCAT`: `concat_naturalOrthogonal`, for well-formed factors and typed
  blocks and representatives (`concatTyped`). Inner rows meet on one copy,
  where the inner state's I1 applies. An inner row and a lifted outer row
  meet on one copy, where the lift is a combination of representatives that
  commute with the inner row. Two lifted outer rows pair, block by block, as
  their coefficient vectors do (`dotPar_combineRows_dual`), so their overlap
  has the parity of the overlap of the two outer rows.

No theorem here uses the typing of the group or of the algebra elements: a
term of the wrong length contributes to no coefficient on either side.
Every evaluation of the three constructors therefore yields a well-formed
state (`evalExpr_lift_wf`, `evalExpr_twoblock_wf`, `evalExpr_concat_wf`),
with no hypothesis. `L-BALANCED` is not covered here: its overlap is proved
in `BalancedOverlap.lean`.
-/

namespace CodeCalculus

/-! ## Lists -/

theorem filter_ne_of_not_mem {α : Type} [DecidableEq α] (a : α) :
    ∀ L : List α, a ∉ L → L.filter (fun x => decide (x ≠ a)) = L
  | [], _ => rfl
  | x :: L, h => by
      have hx : x ≠ a := fun hxa => h (hxa ▸ List.mem_cons_self ..)
      rw [List.filter_cons_of_pos (p := fun x => decide (x ≠ a)) (decide_eq_true hx),
        filter_ne_of_not_mem a L (fun hm => h (List.mem_cons_of_mem x hm))]

theorem length_filter_ne_gen {α : Type} [DecidableEq α] (a : α) :
    ∀ L : List α, L.Nodup → a ∈ L → (L.filter (fun x => decide (x ≠ a))).length + 1 = L.length
  | [], _, h => nomatch h
  | x :: L, hnd, hmem => by
      rw [List.nodup_cons] at hnd
      rcases Decidable.em (x = a) with hxa | hxa
      · subst hxa
        rw [List.filter_cons_of_neg (p := fun y => decide (y ≠ x)) (by
          rw [decide_eq_false (fun h => h rfl)]
          exact Bool.false_ne_true), filter_ne_of_not_mem x L hnd.1, List.length_cons]
      · have haL : a ∈ L := by
          rcases List.mem_cons.mp hmem with h | h
          · exact absurd h.symm hxa
          · exact h
        rw [List.filter_cons_of_pos (p := fun x => decide (x ≠ a)) (decide_eq_true hxa),
          List.length_cons, List.length_cons,
          length_filter_ne_gen a L hnd.2 haL]

theorem nodup_filter_cf {α : Type} (p : α → Bool) : ∀ (l : List α), l.Nodup → (l.filter p).Nodup
  | [], _ => List.nodup_nil
  | a :: l, hnd => by
      rw [List.nodup_cons] at hnd
      cases h : p a with
      | true =>
          rw [List.filter_cons_of_pos h, List.nodup_cons]
          exact ⟨fun hm => hnd.1 (List.mem_filter.mp hm).1, nodup_filter_cf p l hnd.2⟩
      | false =>
          rw [List.filter_cons_of_neg (by rw [h]; exact Bool.false_ne_true)]
          exact nodup_filter_cf p l hnd.2

theorem length_le_of_nodup_subset_gen {α : Type} [DecidableEq α] :
    ∀ (l1 l2 : List α), l1.Nodup → l2.Nodup → (∀ x ∈ l1, x ∈ l2) → l1.length ≤ l2.length
  | [], _, _, _, _ => Nat.zero_le _
  | a :: l1, l2, hnd, hnd2, hsub => by
      rw [List.nodup_cons] at hnd
      have ha : a ∈ l2 := hsub a (List.mem_cons_self ..)
      have hsub' : ∀ x ∈ l1, x ∈ l2.filter (fun x => decide (x ≠ a)) := by
        intro x hx
        have hne : x ≠ a := fun h => hnd.1 (h ▸ hx)
        exact List.mem_filter.mpr ⟨hsub x (List.mem_cons_of_mem a hx), decide_eq_true hne⟩
      have ih := length_le_of_nodup_subset_gen l1 _ hnd.2 (nodup_filter_cf _ l2 hnd2) hsub'
      have hlen := length_filter_ne_gen a l2 hnd2 ha
      rw [List.length_cons]
      omega

theorem nodup_map_of_inj_on {α : Type} (φ : α → α) :
    ∀ (l : List α), l.Nodup → (∀ x ∈ l, ∀ y ∈ l, φ x = φ y → x = y) → (l.map φ).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hnd, hinj => by
      rw [List.nodup_cons] at hnd
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, nodup_map_of_inj_on φ l hnd.2 (fun x hx y hy h =>
        hinj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) h)⟩
      intro hmem
      obtain ⟨b, hb, hφ⟩ := List.mem_map.mp hmem
      have : b = a := hinj b (List.mem_cons_of_mem a hb) a (List.mem_cons_self ..) hφ
      exact hnd.1 (this ▸ hb)

theorem filter_length_le_of_involution {α : Type} [DecidableEq α] (L : List α) (hnd : L.Nodup)
    (φ : α → α) (hmap : ∀ x ∈ L, φ x ∈ L) (hinv : ∀ x ∈ L, φ (φ x) = x) (F : α → Bool) :
    (L.filter (fun x => F (φ x))).length ≤ (L.filter F).length := by
  have h1 : ((L.filter (fun x => F (φ x))).map φ).Nodup := by
    apply nodup_map_of_inj_on φ _ (nodup_filter_cf _ L hnd)
    intro x hx y hy hxy
    have hx' := (List.mem_filter.mp hx).1
    have hy' := (List.mem_filter.mp hy).1
    rw [← hinv x hx', ← hinv y hy', hxy]
  have h2 : ∀ z ∈ (L.filter (fun x => F (φ x))).map φ, z ∈ L.filter F := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    have hx' := List.mem_filter.mp hx
    exact List.mem_filter.mpr ⟨hmap x hx'.1, hx'.2⟩
  have := length_le_of_nodup_subset_gen _ _ h1 (nodup_filter_cf _ L hnd) h2
  rw [List.length_map] at this
  exact this

/-- Counting over a repeat-free list is invariant under an involution of it. -/
theorem filter_length_involution {α : Type} [DecidableEq α] (L : List α) (hnd : L.Nodup)
    (φ : α → α) (hmap : ∀ x ∈ L, φ x ∈ L) (hinv : ∀ x ∈ L, φ (φ x) = x) (F : α → Bool) :
    (L.filter (fun x => F (φ x))).length = (L.filter F).length := by
  apply Nat.le_antisymm (filter_length_le_of_involution L hnd φ hmap hinv F)
  have h := filter_length_le_of_involution L hnd φ hmap hinv (fun x => F (φ x))
  have hc : L.filter (fun x => F (φ (φ x))) = L.filter F :=
    List.filter_congr (fun x hx => by rw [hinv x hx])
  rw [hc] at h
  exact h

/-! ## The group `Z_{o₁} × ⋯ × Z_{o_r}` -/

/-- Membership in the group: one exponent below each order. -/
def InGroup : List Nat → List Nat → Prop
  | [], [] => True
  | o :: os, x :: xs => x < o ∧ InGroup os xs
  | _, _ => False

theorem mem_groupElements : ∀ (os g : List Nat), g ∈ groupElements os ↔ InGroup os g
  | [], [] => ⟨fun _ => trivial, fun _ => List.mem_singleton.mpr rfl⟩
  | [], x :: xs => ⟨fun h => (nomatch List.mem_singleton.mp h), fun h => (nomatch h)⟩
  | o :: os, [] => by
      constructor
      · intro h
        obtain ⟨e, _, hm⟩ := List.mem_flatMap.mp h
        obtain ⟨g, _, hg⟩ := List.mem_map.mp hm
        cases hg
      · intro h
        exact nomatch h
  | o :: os, x :: xs => by
      constructor
      · intro h
        obtain ⟨e, he, hm⟩ := List.mem_flatMap.mp h
        obtain ⟨g, hg, heq⟩ := List.mem_map.mp hm
        cases heq
        exact ⟨List.mem_range.mp he, (mem_groupElements os xs).mp hg⟩
      · intro h
        exact List.mem_flatMap.mpr ⟨x, List.mem_range.mpr h.1,
          List.mem_map.mpr ⟨xs, (mem_groupElements os xs).mpr h.2, rfl⟩⟩

theorem nodup_map_cons (e : Nat) : ∀ l : List (List Nat), l.Nodup →
    (l.map (fun g => e :: g)).Nodup
  | [], _ => List.nodup_nil
  | b :: l, h => by
      rw [List.nodup_cons] at h
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, nodup_map_cons e l h.2⟩
      intro hmem
      obtain ⟨b', hb', heq⟩ := List.mem_map.mp hmem
      exact h.1 ((List.cons.inj heq).2 ▸ hb')

theorem nodup_consOf (M : List (List Nat)) (hM : M.Nodup) : ∀ l : List Nat, l.Nodup →
    (l.flatMap (fun e => M.map (fun g => e :: g))).Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
      rw [List.nodup_cons] at h
      rw [List.flatMap_cons, List.nodup_append]
      refine ⟨nodup_map_cons a M hM, nodup_consOf M hM l h.2, ?_⟩
      intro x hx y hy hxy
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨a', ha', hmem⟩ := List.mem_flatMap.mp hy
      obtain ⟨b', _, rfl⟩ := List.mem_map.mp hmem
      have : a = a' := (List.cons.inj hxy).1
      exact h.1 (this ▸ ha')

theorem nodup_groupElements : ∀ os : List Nat, (groupElements os).Nodup
  | [] => List.nodup_cons.mpr ⟨fun h => (nomatch h), List.nodup_nil⟩
  | o :: os => nodup_consOf _ (nodup_groupElements os) _ (nodup_range_cf o)

/-! ### Subtraction modulo one order -/

/-- `x - y` modulo `o`, as `groupSub` computes it on one component. -/
def subm (o x y : Nat) : Nat := (x % o + (o - y % o)) % o

theorem subm_eq {o x y : Nat} (hx : x < o) (hy : y < o) :
    subm o x y = if y ≤ x then x - y else x + o - y := by
  unfold subm
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  split
  · rename_i h
    have : x + (o - y) = (x - y) + o := by omega
    rw [this, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  · rename_i h
    have : x + (o - y) = x + o - y := by omega
    rw [this]
    exact Nat.mod_eq_of_lt (by omega)

theorem subm_lt {o x y : Nat} (hx : x < o) : subm o x y < o :=
  Nat.mod_lt _ (by omega)

theorem subm_subm_self {o x y : Nat} (hx : x < o) (hy : y < o) :
    subm o x (subm o x y) = y := by
  have h1 := subm_eq hx hy
  have h2 := subm_eq hx (subm_lt (y := y) hx)
  rw [h2, h1]
  split <;> split <;> omega

theorem subm_refl2 {o g h h' : Nat} (hg : g < o) (hh : h < o) (hh' : h' < o) :
    subm o (subm o h (subm o g h')) h' = subm o h g := by
  have a := subm_eq hg hh'
  have hb : subm o g h' < o := subm_lt hg
  have b := subm_eq hh hb
  have hc : subm o h (subm o g h') < o := subm_lt hh
  have c := subm_eq hc hh'
  have d := subm_eq hh hg
  rw [c, b, a, d]
  split <;> split <;> split <;> split <;> omega

theorem subm_refl3 {o g h h' : Nat} (hg : g < o) (hh : h < o) (hh' : h' < o) :
    subm o (subm o h (subm o g h')) h = subm o h' g := by
  have a := subm_eq hg hh'
  have hb : subm o g h' < o := subm_lt hg
  have b := subm_eq hh hb
  have hc : subm o h (subm o g h') < o := subm_lt hh
  have c := subm_eq hc hh
  have d := subm_eq hh' hg
  rw [c, b, a, d]
  split <;> split <;> split <;> split <;> omega

theorem negm_iff {o c a b : Nat} (hc : c < o) (ha : a < o) (hb : b < o) :
    ((o - c) % o) % o = subm o a b ↔ c = subm o b a := by
  have e1 : ((o - c) % o) % o = if c = 0 then 0 else o - c := by
    split
    · rename_i h
      subst h
      rw [Nat.sub_zero, Nat.mod_self, Nat.zero_mod]
    · rename_i h
      rw [Nat.mod_mod]
      exact Nat.mod_eq_of_lt (by omega)
  rw [e1, subm_eq ha hb, subm_eq hb ha]
  constructor
  · intro h
    split at h <;> split at h <;> split <;> omega
  · intro h
    split at h <;> split <;> split <;> omega

/-! ### Subtraction in the group -/

theorem groupSub_cons (o : Nat) (os : List Nat) (x : Nat) (xs : List Nat) (y : Nat)
    (ys : List Nat) :
    groupSub (o :: os) (x :: xs) (y :: ys) = subm o x y :: groupSub os xs ys := rfl

theorem inGroup_sub : ∀ (os u v : List Nat), InGroup os u → InGroup os v →
    InGroup os (groupSub os u v)
  | [], [], [], _, _ => trivial
  | [], [], _ :: _, _, h => nomatch h
  | [], _ :: _, _, h, _ => nomatch h
  | _ :: _, [], _, h, _ => nomatch h
  | _ :: _, _ :: _, [], _, h => nomatch h
  | _ :: os, _ :: xs, _ :: ys, hu, hv =>
      ⟨subm_lt hu.1, inGroup_sub os xs ys hu.2 hv.2⟩

theorem groupSub_sub_self : ∀ (os u v : List Nat), InGroup os u → InGroup os v →
    groupSub os u (groupSub os u v) = v
  | [], [], [], _, _ => rfl
  | [], [], _ :: _, _, h => nomatch h
  | [], _ :: _, _, h, _ => nomatch h
  | _ :: _, [], _, h, _ => nomatch h
  | _ :: _, _ :: _, [], _, h => nomatch h
  | o :: os, x :: xs, y :: ys, hu, hv => by
      rw [groupSub_cons, groupSub_cons, subm_subm_self hu.1 hv.1,
        groupSub_sub_self os xs ys hu.2 hv.2]

theorem groupSub_refl2 : ∀ (os g h h' : List Nat), InGroup os g → InGroup os h →
    InGroup os h' →
    groupSub os (groupSub os h (groupSub os g h')) h' = groupSub os h g
  | [], [], [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h, _, _ => nomatch h
  | [], [], _ :: _, _, _, h, _ => nomatch h
  | [], [], [], _ :: _, _, _, h => nomatch h
  | _ :: _, [], _, _, h, _, _ => nomatch h
  | _ :: _, _ :: _, [], _, _, h, _ => nomatch h
  | _ :: _, _ :: _, _ :: _, [], _, _, h => nomatch h
  | o :: os, x :: xs, y :: ys, z :: zs, hg, hh, hh' => by
      rw [groupSub_cons, groupSub_cons, groupSub_cons, groupSub_cons,
        subm_refl2 hg.1 hh.1 hh'.1, groupSub_refl2 os xs ys zs hg.2 hh.2 hh'.2]

theorem groupSub_refl3 : ∀ (os g h h' : List Nat), InGroup os g → InGroup os h →
    InGroup os h' →
    groupSub os (groupSub os h (groupSub os g h')) h = groupSub os h' g
  | [], [], [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h, _, _ => nomatch h
  | [], [], _ :: _, _, _, h, _ => nomatch h
  | [], [], [], _ :: _, _, _, h => nomatch h
  | _ :: _, [], _, _, h, _, _ => nomatch h
  | _ :: _, _ :: _, [], _, _, h, _ => nomatch h
  | _ :: _, _ :: _, _ :: _, [], _, _, h => nomatch h
  | o :: os, x :: xs, y :: ys, z :: zs, hg, hh, hh' => by
      rw [groupSub_cons, groupSub_cons, groupSub_cons, groupSub_cons,
        subm_refl3 hg.1 hh.1 hh'.1, groupSub_refl3 os xs ys zs hg.2 hh.2 hh'.2]

/-- The negated term has the coefficient position `u - v` exactly when the
    term has the position `v - u`. -/
theorem groupNorm_neg_iff : ∀ (os t u v : List Nat), InGroup os u → InGroup os v →
    (groupNorm os (groupNeg os t) = groupSub os u v ↔ groupNorm os t = groupSub os v u)
  | [], [], [], [], _, _ => ⟨fun _ => rfl, fun _ => rfl⟩
  | [], _ :: _, [], [], _, _ => ⟨fun _ => rfl, fun _ => rfl⟩
  | [], _, [], _ :: _, _, h => nomatch h
  | [], _, _ :: _, _, h, _ => nomatch h
  | _ :: _, _, [], _, h, _ => nomatch h
  | _ :: _, _, _ :: _, [], _, h => nomatch h
  | o :: os, [], a :: us, b :: vs, _, _ =>
      ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | o :: os, x :: xs, a :: us, b :: vs, hu, hv => by
      have ih := groupNorm_neg_iff os xs us vs hu.2 hv.2
      have hx : x % o < o := Nat.mod_lt _ (by have := hu.1; omega)
      have hd := negm_iff hx hu.1 hv.1
      show ((o - x % o) % o) % o :: groupNorm os (groupNeg os xs) =
          subm o a b :: groupSub os us vs ↔
        x % o :: groupNorm os xs = subm o b a :: groupSub os vs us
      constructor
      · intro h
        obtain ⟨h1, h2⟩ := List.cons.inj h
        rw [hd.mp h1, ih.mp h2]
      · intro h
        obtain ⟨h1, h2⟩ := List.cons.inj h
        rw [hd.mpr h1, ih.mpr h2]

theorem beq_congr_of_iff {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    [DecidableEq α] {a b : α} {c d : β} (h : a = b ↔ c = d) : (a == b) = (c == d) := by
  rcases Decidable.em (a = b) with e | e
  · rw [beq_iff_eq.mpr e, beq_iff_eq.mpr (h.mp e)]
  · rw [beq_eq_false_iff_ne.mpr e, beq_eq_false_iff_ne.mpr (fun hcd => e (h.mpr hcd))]

/-- The coefficient of `u - v` in `x*` is the coefficient of `v - u` in `x`. -/
theorem algCoeff_inv (os : List Nat) (x : List (List Nat)) (u v : List Nat)
    (hu : InGroup os u) (hv : InGroup os v) :
    algCoeff os (algInv os x) (groupSub os u v) = algCoeff os x (groupSub os v u) := by
  unfold algCoeff algInv
  rw [List.filter_map, List.length_map]
  have hc : x.filter ((fun t => groupNorm os t == groupSub os u v) ∘ groupNeg os) =
      x.filter (fun t => groupNorm os t == groupSub os v u) :=
    List.filter_congr (fun t _ => beq_congr_of_iff (groupNorm_neg_iff os t u v hu hv))
  rw [hc]

/-! ### Overlaps of rows of the regular representation -/

theorem dotPar_regRow (os : List Nat) (x y : List (List Nat)) (h h' : List Nat) :
    dotPar (regRow os x h) (regRow os y h') =
      ((groupElements os).filter (fun g =>
        algCoeff os x (groupSub os h g) && algCoeff os y (groupSub os h' g))).length := by
  unfold regRow
  exact dotPar_map_map_gen _ _ _

/-- The reflection `g ↦ h - (g - h')` is an involution of the group. -/
theorem reflect_count (os : List Nat) (h h' : List Nat) (hh : InGroup os h)
    (hh' : InGroup os h') (F : List Nat → Bool) :
    ((groupElements os).filter
        (fun g => F (groupSub os h (groupSub os g h')))).length =
      ((groupElements os).filter F).length := by
  apply filter_length_involution _ (nodup_groupElements os)
    (fun g => groupSub os h (groupSub os g h'))
  · intro g hg
    have hg' := (mem_groupElements os g).mp hg
    exact (mem_groupElements os _).mpr (inGroup_sub os _ _ hh (inGroup_sub os _ _ hg' hh'))
  · intro g hg
    have hg' := (mem_groupElements os g).mp hg
    show groupSub os h (groupSub os (groupSub os h (groupSub os g h')) h') = g
    rw [groupSub_refl2 os g h h' hg' hh hh', groupSub_sub_self os h g hh hg']

/-- `⟨L(y*)_h, L(x*)_{h'}⟩ = ⟨L(x)_h, L(y)_{h'}⟩`: the two blocks of a lifted
    product pair to the same count. -/
theorem dotPar_regRow_inv_inv (os : List Nat) (x y : List (List Nat)) (h h' : List Nat)
    (hh : InGroup os h) (hh' : InGroup os h') :
    dotPar (regRow os (algInv os y) h) (regRow os (algInv os x) h') =
      dotPar (regRow os x h) (regRow os y h') := by
  rw [dotPar_regRow, dotPar_regRow]
  have h1 : (groupElements os).filter (fun g =>
      algCoeff os (algInv os y) (groupSub os h g) &&
        algCoeff os (algInv os x) (groupSub os h' g)) =
      (groupElements os).filter (fun g =>
        algCoeff os y (groupSub os g h) && algCoeff os x (groupSub os g h')) :=
    List.filter_congr (fun g hg => by
      have hg' := (mem_groupElements os g).mp hg
      rw [algCoeff_inv os y h g hh hg', algCoeff_inv os x h' g hh' hg'])
  rw [h1, ← reflect_count os h h' hh hh'
    (fun g => algCoeff os y (groupSub os g h) && algCoeff os x (groupSub os g h'))]
  exact congrArg List.length (List.filter_congr (fun g hg => by
    have hg' := (mem_groupElements os g).mp hg
    show (algCoeff os y (groupSub os (groupSub os h (groupSub os g h')) h) &&
      algCoeff os x (groupSub os (groupSub os h (groupSub os g h')) h')) = _
    rw [groupSub_refl3 os g h h' hg' hh hh', groupSub_refl2 os g h h' hg' hh hh',
      Bool.and_comm]))

/-- `⟨L(x)_h, L(y*)_{h'}⟩ = ⟨L(y)_h, L(x*)_{h'}⟩`: commutativity of the group
    algebra, read on the two blocks of a two-block code. -/
theorem dotPar_regRow_swap (os : List Nat) (x y : List (List Nat)) (h h' : List Nat)
    (hh : InGroup os h) (hh' : InGroup os h') :
    dotPar (regRow os x h) (regRow os (algInv os y) h') =
      dotPar (regRow os y h) (regRow os (algInv os x) h') := by
  rw [dotPar_regRow, dotPar_regRow]
  have h1 : (groupElements os).filter (fun g =>
      algCoeff os x (groupSub os h g) && algCoeff os (algInv os y) (groupSub os h' g)) =
      (groupElements os).filter (fun g =>
        algCoeff os x (groupSub os h g) && algCoeff os y (groupSub os g h')) :=
    List.filter_congr (fun g hg => by
      have hg' := (mem_groupElements os g).mp hg
      rw [algCoeff_inv os y h' g hh' hg'])
  have h2 : (groupElements os).filter (fun g =>
      algCoeff os y (groupSub os h g) && algCoeff os (algInv os x) (groupSub os h' g)) =
      (groupElements os).filter (fun g =>
        algCoeff os y (groupSub os h g) && algCoeff os x (groupSub os g h')) :=
    List.filter_congr (fun g hg => by
      have hg' := (mem_groupElements os g).mp hg
      rw [algCoeff_inv os x h' g hh' hg'])
  rw [h1, h2, ← reflect_count os h h' hh hh'
    (fun g => algCoeff os y (groupSub os h g) && algCoeff os x (groupSub os g h'))]
  exact congrArg List.length (List.filter_congr (fun g hg => by
    have hg' := (mem_groupElements os g).mp hg
    show _ = (algCoeff os y (groupSub os h (groupSub os h (groupSub os g h'))) &&
      algCoeff os x (groupSub os (groupSub os h (groupSub os g h')) h'))
    rw [groupSub_sub_self os h _ hh (inGroup_sub os g h' hg' hh'),
      groupSub_refl2 os g h h' hg' hh hh', Bool.and_comm]))

/-! ## Vectors given block by block -/

theorem dotPar_flatMap {α : Type} (f g : α → List Bool) : ∀ L : List α,
    (∀ p ∈ L, (f p).length = (g p).length) →
    dotPar (L.flatMap f) (L.flatMap g) = (L.map (fun p => dotPar (f p) (g p))).sum
  | [], _ => rfl
  | p :: L, h => by
      rw [List.flatMap_cons, List.flatMap_cons,
        dotPar_append _ _ _ _ (h p (List.mem_cons_self ..)),
        dotPar_flatMap f g L (fun q hq => h q (List.mem_cons_of_mem p hq)),
        List.map_cons, List.sum_cons]

theorem length_flatMap_const {α : Type} (f : α → List Bool) (ℓ : Nat) : ∀ L : List α,
    (∀ p ∈ L, (f p).length = ℓ) → (L.flatMap f).length = L.length * ℓ
  | [], _ => by rw [List.flatMap_nil, List.length_nil, List.length_nil, Nat.zero_mul]
  | p :: L, h => by
      rw [List.flatMap_cons, List.length_append, h p (List.mem_cons_self ..),
        length_flatMap_const f ℓ L (fun q hq => h q (List.mem_cons_of_mem p hq)),
        List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem sum_map_zero {α : Type} (t : α → Nat) : ∀ L : List α, (∀ p ∈ L, t p = 0) →
    (L.map t).sum = 0
  | [], _ => rfl
  | p :: L, h => by
      rw [List.map_cons, List.sum_cons, h p (List.mem_cons_self ..),
        sum_map_zero t L (fun q hq => h q (List.mem_cons_of_mem p hq))]

/-- A sum whose terms vanish away from one point of a repeat-free list. -/
theorem sum_map_point {α : Type} [DecidableEq α] (c : α) (v : Nat) (t : α → Nat) :
    ∀ L : List α, L.Nodup → c ∈ L → (∀ p ∈ L, t p = if p = c then v else 0) →
      (L.map t).sum = v
  | [], _, h, _ => nomatch h
  | x :: L, hnd, hc, ht => by
      rw [List.nodup_cons] at hnd
      have hx := ht x (List.mem_cons_self ..)
      have hL : ∀ p ∈ L, t p = if p = c then v else 0 :=
        fun p hp => ht p (List.mem_cons_of_mem x hp)
      rw [List.map_cons, List.sum_cons]
      rcases Decidable.em (x = c) with hxc | hxc
      · rw [hx, if_pos hxc]
        have hz : ∀ p ∈ L, t p = 0 := by
          intro p hp
          rw [hL p hp, if_neg (fun (hpc : p = c) => hnd.1 (by rw [hxc, ← hpc]; exact hp))]
        rw [sum_map_zero t L hz, Nat.add_zero]
      · have hcL : c ∈ L := by
          rcases List.mem_cons.mp hc with h | h
          · exact absurd h.symm hxc
          · exact h
        rw [hx, if_neg hxc, Nat.zero_add]
        exact sum_map_point c v t L hnd.2 hcL hL

theorem length_regRow (os : List Nat) (x : List (List Nat)) (h : List Nat) :
    (regRow os x h).length = (groupElements os).length := by
  unfold regRow
  rw [List.length_map]

/-! ## `L-GROUP-ALGEBRA` -/

/-- The natural rows of `twoblock_G(a, b)` have pairwise even overlap across
    the sectors, for every group and every pair of algebra elements. -/
theorem twoblock_naturalOrthogonal (os : List Nat) (a b : List (List Nat)) :
    NaturalOrthogonal (naturalRows (twoblockQubits os) (twoblockVectors os a b)) := by
  have heq : twoblockVectors os a b =
      ((groupElements os).map (fun h => regRow os a h ++ regRow os b h)).map
        (fun v => (Sector.X, v)) ++
      ((groupElements os).map (fun h =>
        regRow os (algInv os b) h ++ regRow os (algInv os a) h)).map
        (fun v => (Sector.Z, v)) := by
    rw [List.map_map, List.map_map]
    rfl
  rw [heq]
  apply naturalOrthogonal_of_cross
  · intro v hv
    obtain ⟨h, _, rfl⟩ := List.mem_map.mp hv
    unfold twoblockQubits
    rw [List.length_append, length_regRow, length_regRow, Nat.two_mul]
  · intro v hv
    obtain ⟨h, _, rfl⟩ := List.mem_map.mp hv
    unfold twoblockQubits
    rw [List.length_append, length_regRow, length_regRow, Nat.two_mul]
  · intro vx hvx vz hvz
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hvx
    obtain ⟨h', hh', rfl⟩ := List.mem_map.mp hvz
    rw [dotPar_append _ _ _ _ (by rw [length_regRow, length_regRow]),
      dotPar_regRow_swap os a b h h' ((mem_groupElements os h).mp hh)
        ((mem_groupElements os h').mp hh')]
    omega

/-- The output of `L-GROUP-ALGEBRA` is well-formed. -/
theorem wf_twoblockState (os : List Nat) (a b : List (List Nat)) :
    EncodingWellFormed (twoblockState os a b) :=
  wf_constructedState _ _ (twoblock_naturalOrthogonal os a b)

/-! ## `L-LIFTED` -/

/-- The natural `X`-row `(a, j, h)` of `lift_G(A, B)`. -/
def liftXVector (os : List Nat) (A B : List (List (List (List Nat)))) (aj : Nat × Nat)
    (h : List Nat) : List Bool :=
  (indexPairs (matCols A) (matCols B)).flatMap (fun ij =>
    if ij.2 = aj.2 then regRow os (algEntry A aj.1 ij.1) h
    else List.replicate (groupElements os).length false) ++
  (indexPairs A.length B.length).flatMap (fun ab =>
    if ab.1 = aj.1 then regRow os (algInv os (algEntry B ab.2 aj.2)) h
    else List.replicate (groupElements os).length false)

/-- The natural `Z`-row `(i, b, h)` of `lift_G(A, B)`. -/
def liftZVector (os : List Nat) (A B : List (List (List (List Nat)))) (ib : Nat × Nat)
    (h : List Nat) : List Bool :=
  (indexPairs (matCols A) (matCols B)).flatMap (fun ij =>
    if ij.1 = ib.1 then regRow os (algEntry B ib.2 ij.2) h
    else List.replicate (groupElements os).length false) ++
  (indexPairs A.length B.length).flatMap (fun ab =>
    if ab.2 = ib.2 then regRow os (algInv os (algEntry A ab.1 ib.1)) h
    else List.replicate (groupElements os).length false)

theorem liftVectors_eq (os : List Nat) (A B : List (List (List (List Nat)))) :
    liftVectors os A B =
      ((indexPairs A.length (matCols B)).flatMap (fun aj =>
        (groupElements os).map (liftXVector os A B aj))).map (fun v => (Sector.X, v)) ++
      ((indexPairs (matCols A) B.length).flatMap (fun ib =>
        (groupElements os).map (liftZVector os A B ib))).map (fun v => (Sector.Z, v)) := by
  rw [List.map_flatMap, List.map_flatMap]
  have hX : ∀ aj : Nat × Nat,
      ((groupElements os).map (liftXVector os A B aj)).map (fun v => (Sector.X, v)) =
        (groupElements os).map (fun h => (Sector.X, liftXVector os A B aj h)) :=
    fun aj => List.map_map ..
  have hZ : ∀ ib : Nat × Nat,
      ((groupElements os).map (liftZVector os A B ib)).map (fun v => (Sector.Z, v)) =
        (groupElements os).map (fun h => (Sector.Z, liftZVector os A B ib h)) :=
    fun ib => List.map_map ..
  rw [funext hX, funext hZ]
  rfl

theorem length_liftBlock (os : List Nat) (m n : Nat) (f : Nat × Nat → List Bool)
    (hf : ∀ p, (f p).length = (groupElements os).length) :
    ((indexPairs m n).flatMap f).length = m * n * (groupElements os).length := by
  rw [length_flatMap_const f _ _ (fun p _ => hf p), length_indexPairs]

theorem length_ite_regRow (os : List Nat) (c : Prop) [Decidable c] (x : List (List Nat))
    (h : List Nat) :
    (if c then regRow os x h else List.replicate (groupElements os).length false).length =
      (groupElements os).length := by
  split
  · exact length_regRow os x h
  · exact List.length_replicate

theorem length_liftXVector (os : List Nat) (A B : List (List (List (List Nat))))
    (aj : Nat × Nat) (h : List Nat) :
    (liftXVector os A B aj h).length = liftQubits os A B := by
  unfold liftXVector liftQubits
  rw [List.length_append, length_liftBlock os _ _ _ (fun _ => length_ite_regRow ..),
    length_liftBlock os _ _ _ (fun _ => length_ite_regRow ..), ← Nat.add_mul, Nat.mul_comm]

theorem length_liftZVector (os : List Nat) (A B : List (List (List (List Nat))))
    (ib : Nat × Nat) (h : List Nat) :
    (liftZVector os A B ib h).length = liftQubits os A B := by
  unfold liftZVector liftQubits
  rw [List.length_append, length_liftBlock os _ _ _ (fun _ => length_ite_regRow ..),
    length_liftBlock os _ _ _ (fun _ => length_ite_regRow ..), ← Nat.add_mul, Nat.mul_comm]

/-- Two blocks that are each one row of a regular representation at one
    index pair and zero elsewhere meet in the overlap of the two rows at the
    common pair. -/
theorem dotPar_point_blocks (ℓ : Nat) (m n : Nat) (c : Nat × Nat)
    (hc : c ∈ indexPairs m n) (P Q : Nat × Nat → Prop) [DecidablePred P] [DecidablePred Q]
    (u w : Nat × Nat → List Bool) (hu : ∀ p, (u p).length = ℓ) (hw : ∀ p, (w p).length = ℓ)
    (hPQ : ∀ p, (P p ∧ Q p) ↔ p = c) :
    dotPar ((indexPairs m n).flatMap (fun p => if P p then u p else List.replicate ℓ false))
        ((indexPairs m n).flatMap (fun p => if Q p then w p else List.replicate ℓ false)) =
      dotPar (u c) (w c) := by
  rw [dotPar_flatMap _ _ _ (fun p _ => by
    have h1 : (if P p then u p else List.replicate ℓ false).length = ℓ := by
      split
      · exact hu p
      · exact List.length_replicate
    have h2 : (if Q p then w p else List.replicate ℓ false).length = ℓ := by
      split
      · exact hw p
      · exact List.length_replicate
    rw [h1, h2])]
  apply sum_map_point c _ _ _ (nodup_indexPairs m n) hc
  intro p _
  rcases Decidable.em (P p) with hP | hP
  · rcases Decidable.em (Q p) with hQ | hQ
    · have hpc : p = c := (hPQ p).mp ⟨hP, hQ⟩
      rw [if_pos hP, if_pos hQ, if_pos hpc, hpc]
    · rw [if_pos hP, if_neg hQ, if_neg (fun hpc => hQ ((hPQ p).mpr hpc).2),
        dotPar_replicate_false]
  · rw [if_neg hP, if_neg (fun hpc => hP ((hPQ p).mpr hpc).1), dotPar_comm,
      dotPar_replicate_false]

/-- §4.34 for `L-LIFTED`: the `X`-row `(a, j, h)` and the `Z`-row
    `(i, b, h')` meet on the left block `(i, j)` and on the right block
    `(a, b)`, in the same number of qubits. -/
theorem lift_overlap (os : List Nat) (A B : List (List (List (List Nat))))
    (aj ib : Nat × Nat) (h h' : List Nat)
    (haj : aj ∈ indexPairs A.length (matCols B))
    (hib : ib ∈ indexPairs (matCols A) B.length)
    (hh : InGroup os h) (hh' : InGroup os h') :
    dotPar (liftXVector os A B aj h) (liftZVector os A B ib h') % 2 = 0 := by
  obtain ⟨a, j⟩ := aj
  obtain ⟨i, b⟩ := ib
  have haj' := mem_indexPairs.mp haj
  have hib' := mem_indexPairs.mp hib
  unfold liftXVector liftZVector
  rw [dotPar_append _ _ _ _ (by
    rw [length_liftBlock os _ _ _ (fun _ => length_ite_regRow ..),
      length_liftBlock os _ _ _ (fun _ => length_ite_regRow ..)])]
  rw [dotPar_point_blocks (groupElements os).length _ _ (i, j)
      (mem_indexPairs.mpr ⟨hib'.1, haj'.2⟩) (fun ij => ij.2 = j) (fun ij => ij.1 = i)
      (fun ij => regRow os (algEntry A a ij.1) h) (fun ij => regRow os (algEntry B b ij.2) h')
      (fun _ => length_regRow ..) (fun _ => length_regRow ..)
      (fun p => ⟨fun hp => Prod.ext hp.2 hp.1, fun hp => by rw [hp]; exact ⟨rfl, rfl⟩⟩),
    dotPar_point_blocks (groupElements os).length _ _ (a, b)
      (mem_indexPairs.mpr ⟨haj'.1, hib'.2⟩) (fun ab => ab.1 = a) (fun ab => ab.2 = b)
      (fun ab => regRow os (algInv os (algEntry B ab.2 j)) h)
      (fun ab => regRow os (algInv os (algEntry A ab.1 i)) h')
      (fun _ => length_regRow ..) (fun _ => length_regRow ..)
      (fun p => ⟨fun hp => Prod.ext hp.1 hp.2, fun hp => by rw [hp]; exact ⟨rfl, rfl⟩⟩),
    dotPar_regRow_inv_inv os (algEntry A a i) (algEntry B b j) h h' hh hh']
  show (dotPar (regRow os (algEntry A a i) h) (regRow os (algEntry B b j) h') +
    dotPar (regRow os (algEntry A a i) h) (regRow os (algEntry B b j) h')) % 2 = 0
  omega

/-- The natural rows of `lift_G(A, B)` have pairwise even overlap across the
    sectors, for every group and every pair of matrices over its algebra. -/
theorem lift_naturalOrthogonal (os : List Nat) (A B : List (List (List (List Nat)))) :
    NaturalOrthogonal (naturalRows (liftQubits os A B) (liftVectors os A B)) := by
  rw [liftVectors_eq]
  apply naturalOrthogonal_of_cross
  · intro v hv
    obtain ⟨aj, _, hm⟩ := List.mem_flatMap.mp hv
    obtain ⟨h, _, rfl⟩ := List.mem_map.mp hm
    exact length_liftXVector os A B aj h
  · intro v hv
    obtain ⟨ib, _, hm⟩ := List.mem_flatMap.mp hv
    obtain ⟨h, _, rfl⟩ := List.mem_map.mp hm
    exact length_liftZVector os A B ib h
  · intro vx hvx vz hvz
    obtain ⟨aj, haj, hm⟩ := List.mem_flatMap.mp hvx
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hm
    obtain ⟨ib, hib, hm'⟩ := List.mem_flatMap.mp hvz
    obtain ⟨h', hh', rfl⟩ := List.mem_map.mp hm'
    exact lift_overlap os A B aj ib h h' haj hib ((mem_groupElements os h).mp hh)
      ((mem_groupElements os h').mp hh')

/-- The output of `L-LIFTED` is well-formed. -/
theorem wf_liftState (os : List Nat) (A B : List (List (List (List Nat)))) :
    EncodingWellFormed (liftState os A B) :=
  wf_constructedState _ _ (lift_naturalOrthogonal os A B)

/-! ## `A-CONCAT` -/

theorem sum_map_even {α : Type} (t : α → Nat) : ∀ L : List α, (∀ p ∈ L, t p % 2 = 0) →
    (L.map t).sum % 2 = 0
  | [], _ => rfl
  | p :: L, h => by
      have h1 := h p (List.mem_cons_self ..)
      have h2 := sum_map_even t L (fun q hq => h q (List.mem_cons_of_mem p hq))
      rw [List.map_cons, List.sum_cons]
      omega

theorem sum_map_congr_mod2 {α : Type} (t t' : α → Nat) : ∀ L : List α,
    (∀ p ∈ L, t p % 2 = t' p % 2) → (L.map t).sum % 2 = (L.map t').sum % 2
  | [], _ => rfl
  | p :: L, h => by
      have h1 := h p (List.mem_cons_self ..)
      have h2 := sum_map_congr_mod2 t t' L (fun q hq => h q (List.mem_cons_of_mem p hq))
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
      omega

/-- The block-by-block overlap of two indicator vectors is their overlap
    over the flattened list. -/
theorem sum_blocks_dotPar (f g : Nat → Bool) : ∀ blocks : List (List Nat),
    (blocks.map (fun B => dotPar (B.map f) (B.map g))).sum =
      (blocks.flatten.filter (fun q => f q && g q)).length
  | [] => rfl
  | B :: blocks => by
      rw [List.map_cons, List.sum_cons, sum_blocks_dotPar f g blocks, List.flatten_cons,
        List.filter_append, List.length_append, dotPar_map_map_gen]

theorem map_getD_range_gen {α : Type} (d : α) (L : List α) :
    (List.range L.length).map (fun i => L.getD i d) = L := by
  apply List.ext_getElem
  · rw [List.length_map, List.length_range]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2]
    rfl

theorem flatMap_range_getD {α β : Type} (d : α) (F : α → List β) (L : List α) :
    L.flatMap F = (List.range L.length).flatMap (fun i => F (L.getD i d)) := by
  have h : L.flatMap F = ((List.range L.length).map (fun i => L.getD i d)).flatMap F := by
    rw [map_getD_range_gen d L]
  rw [h, List.flatMap_map]

theorem mem_getD {α : Type} (d : α) : ∀ (l : List α) (w : α), w ∈ l →
    ∃ i, i < l.length ∧ l.getD i d = w
  | [], _, h => nomatch h
  | a :: l, w, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨0, Nat.zero_lt_succ _, rfl⟩
      · obtain ⟨i, hi, hw⟩ := mem_getD d l w h'
        exact ⟨i + 1, Nat.succ_lt_succ hi, hw⟩

theorem getD_mem {α : Type} (d : α) : ∀ (l : List α) (i : Nat), i < l.length →
    l.getD i d ∈ l
  | [], _, h => nomatch h
  | a :: l, 0, _ => List.mem_cons_self ..
  | a :: l, i + 1, h => List.mem_cons_of_mem a (getD_mem d l i (Nat.lt_of_succ_lt_succ h))

theorem getD_map_lt {α β : Type} (f : α → β) (d : α) (e : β) : ∀ (l : List α) (i : Nat),
    i < l.length → (l.map f).getD i e = f (l.getD i d)
  | [], _, h => nomatch h
  | a :: l, 0, _ => rfl
  | a :: l, i + 1, h => getD_map_lt f d e l i (Nat.lt_of_succ_lt_succ h)

/-- Two lists of vectors of length `n` that pair to the identity: the heads
    have odd overlap, each head has even overlap with the other tail, and
    the tails are dual. -/
def DualLists (n : Nat) : List (List Bool) → List (List Bool) → Prop
  | [], [] => True
  | x :: xs, z :: zs =>
      x.length = n ∧ z.length = n ∧ dotPar x z % 2 = 1 ∧
        (∀ w ∈ zs, dotPar x w % 2 = 0) ∧ (∀ w ∈ xs, dotPar z w % 2 = 0) ∧ DualLists n xs zs
  | _, _ => False

theorem dualLists_lengths (n : Nat) : ∀ (xs zs : List (List Bool)), DualLists n xs zs →
    (∀ w ∈ xs, w.length = n) ∧ (∀ w ∈ zs, w.length = n)
  | [], [], _ => ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | x :: xs, z :: zs, h => by
      obtain ⟨hx, hz, _, _, _, hd⟩ := h
      have ih := dualLists_lengths n xs zs hd
      constructor
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw'
        · exact hx
        · exact ih.1 w hw'
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw'
        · exact hz
        · exact ih.2 w hw'

/-- Lists that pair to the identity entry by entry are dual. -/
theorem dualLists_of_indexed (n : Nat) : ∀ (xs zs : List (List Bool)),
    xs.length = zs.length → (∀ w ∈ xs, w.length = n) → (∀ w ∈ zs, w.length = n) →
    (∀ p p', p < xs.length → p' < xs.length →
      dotPar (xs.getD p []) (zs.getD p' []) % 2 = if p = p' then 1 else 0) →
    DualLists n xs zs
  | [], [], _, _, _, _ => trivial
  | [], _ :: _, h, _, _, _ => nomatch h
  | _ :: _, [], h, _, _, _ => nomatch h
  | x :: xs, z :: zs, hlen, hx, hz, hd => by
      have hlen' : xs.length = zs.length := Nat.succ.inj hlen
      refine ⟨hx x (List.mem_cons_self ..), hz z (List.mem_cons_self ..), ?_, ?_, ?_, ?_⟩
      · exact hd 0 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
      · intro w hw
        obtain ⟨i, hi, rfl⟩ := mem_getD [] zs w hw
        have := hd 0 (i + 1) (Nat.zero_lt_succ _) (by
          rw [List.length_cons, hlen']
          exact Nat.succ_lt_succ hi)
        rw [if_neg (by omega)] at this
        exact this
      · intro w hw
        obtain ⟨i, hi, rfl⟩ := mem_getD [] xs w hw
        have := hd (i + 1) 0 (Nat.succ_lt_succ hi) (Nat.zero_lt_succ _)
        rw [if_neg (by omega)] at this
        rw [dotPar_comm]
        exact this
      · apply dualLists_of_indexed n xs zs hlen'
          (fun w hw => hx w (List.mem_cons_of_mem x hw))
          (fun w hw => hz w (List.mem_cons_of_mem z hw))
        intro p p' hp hp'
        have := hd (p + 1) (p' + 1) (Nat.succ_lt_succ hp) (Nat.succ_lt_succ hp')
        rcases Decidable.em (p = p') with e | e
        · rw [if_pos (by omega)] at this
          rw [if_pos e]
          exact this
        · rw [if_neg (by omega)] at this
          rw [if_neg e]
          exact this

theorem dotPar_xorVec_left' (u w r : List Bool) (h : u.length = w.length) :
    dotPar (xorVec u w) r % 2 = (dotPar u r + dotPar w r) % 2 := by
  rw [dotPar_comm, dotPar_xorVec r u w h, dotPar_comm r u, dotPar_comm r w]

/-- The dual-basis pairing: combinations of dual lists pair as their
    coefficient vectors do. -/
theorem dotPar_combineRows_dual (n : Nat) : ∀ (xs zs : List (List Bool)) (c c' : List Bool),
    DualLists n xs zs → c.length = xs.length → c'.length = zs.length →
    dotPar (combineRows n xs c) (combineRows n zs c') % 2 = dotPar c c' % 2
  | [], [], [], [], _, _, _ => by
      show dotPar (List.replicate n false) (List.replicate n false) % 2 = 0
      rw [dotPar_replicate_false]
  | [], [], _ :: _, _, _, h, _ => nomatch h
  | [], [], [], _ :: _, _, _, h => nomatch h
  | [], _ :: _, _, _, h, _, _ => nomatch h
  | _ :: _, [], _, _, h, _, _ => nomatch h
  | _ :: _, _ :: _, [], _, _, h, _ => nomatch h
  | _ :: _, _ :: _, _ :: _, [], _, _, h => nomatch h
  | x :: xs, z :: zs, b :: cs, b' :: cs', hd, hc, hc' => by
      obtain ⟨hx, hz, hxz, hxzs, hzxs, hdual⟩ := hd
      have hl := dualLists_lengths n xs zs hdual
      have lX : (combineRows n xs cs).length = n := combineRows_length n xs cs hl.1
      have lZ : (combineRows n zs cs').length = n := combineRows_length n zs cs' hl.2
      have e1 : dotPar x (combineRows n zs cs') % 2 = 0 :=
        dotPar_combineRows_even n x zs cs' hl.2 hxzs
      have e2 : dotPar (combineRows n xs cs) z % 2 = 0 := by
        rw [dotPar_comm]
        exact dotPar_combineRows_even n z xs cs hl.1 hzxs
      have e3 := dotPar_combineRows_dual n xs zs cs cs' hdual (Nat.succ.inj hc)
        (Nat.succ.inj hc')
      cases b with
      | true =>
          cases b' with
          | true =>
              show dotPar (xorVec x (combineRows n xs cs)) (xorVec z (combineRows n zs cs')) % 2 =
                (1 + dotPar cs cs') % 2
              have a1 := dotPar_xorVec_left' x (combineRows n xs cs)
                (xorVec z (combineRows n zs cs')) (by rw [hx, lX])
              have a2 := dotPar_xorVec x z (combineRows n zs cs') (by rw [hz, lZ])
              have a3 := dotPar_xorVec (combineRows n xs cs) z (combineRows n zs cs')
                (by rw [hz, lZ])
              omega
          | false =>
              show dotPar (xorVec x (combineRows n xs cs)) (combineRows n zs cs') % 2 =
                (0 + dotPar cs cs') % 2
              have a1 := dotPar_xorVec_left' x (combineRows n xs cs)
                (combineRows n zs cs') (by rw [hx, lX])
              omega
      | false =>
          cases b' with
          | true =>
              show dotPar (combineRows n xs cs) (xorVec z (combineRows n zs cs')) % 2 =
                (0 + dotPar cs cs') % 2
              have a3 := dotPar_xorVec (combineRows n xs cs) z (combineRows n zs cs')
                (by rw [hz, lZ])
              omega
          | false =>
              show dotPar (combineRows n xs cs) (combineRows n zs cs') % 2 =
                (0 + dotPar cs cs') % 2
              omega

/-- The representatives of one sector. -/
def concatReps (repsX repsZ : List (List Nat)) : Sector → List (List Nat)
  | Sector.X => repsX
  | Sector.Z => repsZ

/-- The representatives as vectors over the inner labels. -/
def repVecs (I : CodeState) (reps : List (List Nat)) : List (List Bool) :=
  reps.map (fun (sup : List Nat) => I.Q.map (fun q => sup.contains q))

/-- The natural row of `concat` that carries the inner row `r` on copy `j`. -/
def concatInner (I : CodeState) (nb j : Nat) (r : Row) : List Bool :=
  (List.range nb).flatMap (fun j' =>
    if j' = j then rowVector I.Q r else List.replicate I.Q.length false)

/-- The natural row of `concat` that lifts the outer row `r` through the
    representatives `reps`. -/
def concatOuter (I : CodeState) (blocks reps : List (List Nat)) (r : Row) : List Bool :=
  blocks.flatMap (fun B =>
    combineRows I.Q.length (repVecs I reps) (B.map (fun q => r.support.contains q)))

theorem concatVectors_eq (O I : CodeState) (blocks repsX repsZ : List (List Nat)) :
    concatVectors O I blocks repsX repsZ =
      (List.range blocks.length).flatMap (fun j => I.rows.map (fun r =>
        (r.sector, concatInner I blocks.length j r))) ++
      O.rows.map (fun r =>
        (r.sector, concatOuter I blocks (concatReps repsX repsZ r.sector) r)) := by
  rfl

theorem length_repVecs (I : CodeState) (reps : List (List Nat)) :
    ∀ v ∈ repVecs I reps, v.length = I.Q.length := by
  intro v hv
  obtain ⟨sup, _, rfl⟩ := List.mem_map.mp hv
  rw [List.length_map]

theorem length_concatInner (I : CodeState) (nb j : Nat) (r : Row) :
    (concatInner I nb j r).length = nb * I.Q.length := by
  unfold concatInner
  rw [length_flatMap_const _ I.Q.length _ (fun j' _ => by
    split
    · unfold rowVector
      rw [List.length_map]
    · exact List.length_replicate), List.length_range]

theorem length_concatOuter (I : CodeState) (blocks reps : List (List Nat)) (r : Row) :
    (concatOuter I blocks reps r).length = blocks.length * I.Q.length := by
  unfold concatOuter
  rw [length_flatMap_const _ I.Q.length _ (fun B _ =>
    combineRows_length _ _ _ (length_repVecs I reps))]

/-- Inner rows of opposite sectors: disjoint on different copies, and the
    overlap of the two inner rows on one copy. -/
theorem concat_inner_inner (I : CodeState) (hI : EncodingWellFormed I) (nb j j2 : Nat)
    (r r2 : Row) (hr : r ∈ I.rows) (hr2 : r2 ∈ I.rows)
    (hs : r2.sector = oppositeSector r.sector) :
    dotPar (concatInner I nb j r) (concatInner I nb j2 r2) % 2 = 0 := by
  have hlenRow : ∀ (c : Prop) [Decidable c] (ρ : Row),
      (if c then rowVector I.Q ρ else List.replicate I.Q.length false).length = I.Q.length := by
    intro c _ ρ
    split
    · unfold rowVector
      rw [List.length_map]
    · exact List.length_replicate
  unfold concatInner
  rw [dotPar_flatMap _ _ _ (fun j' _ => by rw [hlenRow, hlenRow])]
  apply sum_map_even
  intro j' _
  show dotPar (if j' = j then rowVector I.Q r else List.replicate I.Q.length false)
    (if j' = j2 then rowVector I.Q r2 else List.replicate I.Q.length false) % 2 = 0
  rcases Decidable.em (j' = j) with h1 | h1
  · rcases Decidable.em (j' = j2) with h2 | h2
    · rw [if_pos h1, if_pos h2]
      exact dotPar_rowVector_even_of_wf hI hr hr2 hs
    · rw [if_neg h2, dotPar_replicate_false]
  · rw [if_neg h1, dotPar_comm, dotPar_replicate_false]

/-- An inner row and a lifted outer row: on the one copy where they meet,
    the lift is a combination of representatives that commute with the
    inner row. -/
theorem concat_inner_outer (I : CodeState) (hI : EncodingWellFormed I)
    (blocks reps : List (List Nat)) (j : Nat) (r r' : Row)
    (hreps : ∀ sup ∈ reps, sup.Nodup ∧ (∀ q ∈ sup, q ∈ I.Q) ∧
      supportIntersectionSize sup r.support % 2 = 0) :
    dotPar (concatInner I blocks.length j r) (concatOuter I blocks reps r') % 2 = 0 := by
  unfold concatInner concatOuter
  rw [flatMap_range_getD [] (fun B =>
    combineRows I.Q.length (repVecs I reps) (B.map (fun q => r'.support.contains q))) blocks]
  rw [dotPar_flatMap _ _ _ (fun j' _ => by
    rw [combineRows_length _ _ _ (length_repVecs I reps)]
    split
    · unfold rowVector
      rw [List.length_map]
    · exact List.length_replicate)]
  apply sum_map_even
  intro j' _
  show dotPar (if j' = j then rowVector I.Q r else List.replicate I.Q.length false)
    (combineRows I.Q.length (repVecs I reps)
      ((blocks.getD j' []).map (fun q => r'.support.contains q))) % 2 = 0
  rcases Decidable.em (j' = j) with h1 | h1
  · rw [if_pos h1]
    apply dotPar_combineRows_even _ _ _ _ (length_repVecs I reps)
    intro u hu
    obtain ⟨sup, hsup, rfl⟩ := List.mem_map.mp hu
    obtain ⟨hnd, hsub, hev⟩ := hreps sup hsup
    rw [dotPar_comm]
    show dotPar (I.Q.map (fun q => sup.contains q))
      (I.Q.map (fun q => r.support.contains q)) % 2 = 0
    rw [← supportIntersectionSize_eq_dotPar I.Q sup r.support hI.1 hnd hsub]
    exact hev
  · rw [if_neg h1, dotPar_comm, dotPar_replicate_false]

/-- Two lifted outer rows of opposite sectors: block by block the dual
    representatives pair as the coefficients do, so the overlap has the
    parity of the overlap of the two outer rows. -/
theorem concat_outer_outer (O I : CodeState) (hO : EncodingWellFormed O)
    (hI : EncodingWellFormed I) (blocks repsX repsZ : List (List Nat))
    (hk : repsZ.length = repsX.length) (hB : ∀ B ∈ blocks, B.length = repsX.length)
    (hnd : blocks.flatten.Nodup) (hsub : ∀ q ∈ O.Q, q ∈ blocks.flatten)
    (hX : ∀ sup ∈ repsX, sup.Nodup ∧ ∀ q ∈ sup, q ∈ I.Q)
    (hdual : ∀ p p', p < repsX.length → p' < repsX.length →
      supportIntersectionSize (repsX.getD p []) (repsZ.getD p' []) % 2 =
        if p = p' then 1 else 0)
    (r r' : Row) (hr : r ∈ O.rows) (hr' : r' ∈ O.rows) (hsX : r.sector = Sector.X)
    (hsZ : r'.sector = Sector.Z) :
    dotPar (concatOuter I blocks repsX r) (concatOuter I blocks repsZ r') % 2 = 0 := by
  have hD : DualLists I.Q.length (repVecs I repsX) (repVecs I repsZ) := by
    apply dualLists_of_indexed _ _ _ (by
      unfold repVecs
      rw [List.length_map, List.length_map, hk]) (length_repVecs I repsX) (length_repVecs I repsZ)
    intro p p' hp hp'
    have hp1 : p < repsX.length := by
      unfold repVecs at hp
      rw [List.length_map] at hp
      exact hp
    have hp1' : p' < repsX.length := by
      unfold repVecs at hp'
      rw [List.length_map] at hp'
      exact hp'
    unfold repVecs
    rw [getD_map_lt _ [] [] repsX p hp1, getD_map_lt _ [] [] repsZ p' (by rw [hk]; exact hp1')]
    have hx := hX _ (getD_mem [] repsX p hp1)
    rw [← supportIntersectionSize_eq_dotPar I.Q _ _ hI.1 hx.1 hx.2]
    exact hdual p p' hp1 hp1'
  unfold concatOuter
  rw [dotPar_flatMap _ _ _ (fun B _ => by
    rw [combineRows_length _ _ _ (length_repVecs I repsX),
      combineRows_length _ _ _ (length_repVecs I repsZ)])]
  have hterm : ∀ B ∈ blocks,
      dotPar (combineRows I.Q.length (repVecs I repsX) (B.map (fun q => r.support.contains q)))
        (combineRows I.Q.length (repVecs I repsZ) (B.map (fun q => r'.support.contains q))) % 2 =
      dotPar (B.map (fun q => r.support.contains q))
        (B.map (fun q => r'.support.contains q)) % 2 := by
    intro B hBm
    apply dotPar_combineRows_dual _ _ _ _ _ hD
    · unfold repVecs
      rw [List.length_map, List.length_map, hB B hBm]
    · unfold repVecs
      rw [List.length_map, List.length_map, hB B hBm, hk]
  rw [sum_map_congr_mod2 _ _ blocks hterm, sum_blocks_dotPar]
  have hs := supportIntersectionSize_eq_dotPar blocks.flatten r.support r'.support hnd
    (support_nodup_of_wf hO hr) (fun q hq => hsub q (supports_subset_of_wf hO r hr q hq))
  rw [dotPar_map_map] at hs
  rw [← hs]
  exact hO.2.2.2.2.2.2.1 r r' hr hr' hsX hsZ

theorem oppositeSector_symm {a b : Sector} (h : b = oppositeSector a) :
    a = oppositeSector b := by
  cases a <;> cases b <;> first | rfl | cases h

/-- The natural rows of `concat` have pairwise even overlap across the
    sectors, for well-formed factors and typed blocks and representatives. -/
theorem concat_naturalOrthogonal (O I : CodeState) (blocks repsX repsZ : List (List Nat))
    (hO : EncodingWellFormed O) (hI : EncodingWellFormed I)
    (hty : concatTyped O I blocks repsX repsZ = true) :
    NaturalOrthogonal (naturalRows (concatQubits I blocks)
      (concatVectors O I blocks repsX repsZ)) := by
  simp only [concatTyped, Bool.and_eq_true] at hty
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, t2⟩, _⟩, t4⟩, t5⟩, _⟩, t7⟩, t8⟩, t9⟩, t10⟩, t11⟩ := hty
  have hk : repsZ.length = repsX.length := Nat.eq_of_beq_eq_true t2
  have hB : ∀ B ∈ blocks, B.length = repsX.length :=
    fun B hBm => Nat.eq_of_beq_eq_true (List.all_eq_true.mp t4 B hBm)
  have hnd : blocks.flatten.Nodup := of_decide_eq_true t5
  have hsub : ∀ q ∈ O.Q, q ∈ blocks.flatten :=
    fun q hq => List.contains_iff_mem.mp (List.all_eq_true.mp t7 q hq)
  have hreps : ∀ sup ∈ repsX ++ repsZ, sup.Nodup ∧ ∀ q ∈ sup, q ∈ I.Q := by
    intro sup hsup
    have h := List.all_eq_true.mp t8 sup hsup
    rw [Bool.and_eq_true] at h
    exact ⟨of_decide_eq_true h.1,
      fun q hq => List.contains_iff_mem.mp (List.all_eq_true.mp h.2 q hq)⟩
  have hcX : ∀ sup ∈ repsX, ∀ ρ ∈ I.rows, ρ.sector = Sector.Z →
      supportIntersectionSize sup ρ.support % 2 = 0 := by
    intro sup hsup ρ hρ hsec
    have h := List.all_eq_true.mp (List.all_eq_true.mp t9 sup hsup) ρ hρ
    rw [hsec, Bool.or_eq_true] at h
    rcases h with h | h
    · exact absurd h (by decide)
    · exact Nat.eq_of_beq_eq_true h
  have hcZ : ∀ sup ∈ repsZ, ∀ ρ ∈ I.rows, ρ.sector = Sector.X →
      supportIntersectionSize sup ρ.support % 2 = 0 := by
    intro sup hsup ρ hρ hsec
    have h := List.all_eq_true.mp (List.all_eq_true.mp t10 sup hsup) ρ hρ
    rw [hsec, Bool.or_eq_true] at h
    rcases h with h | h
    · exact absurd h (by decide)
    · exact Nat.eq_of_beq_eq_true h
  have hdual : ∀ p p', p < repsX.length → p' < repsX.length →
      supportIntersectionSize (repsX.getD p []) (repsZ.getD p' []) % 2 =
        if p = p' then 1 else 0 := by
    intro p p' hp hp'
    have h := List.all_eq_true.mp (List.all_eq_true.mp t11 p (List.mem_range.mpr hp)) p'
      (List.mem_range.mpr hp')
    have h' := eq_of_beq h
    rcases Decidable.em (p = p') with e | e
    · rw [if_pos e]
      rw [beq_iff_eq.mpr e] at h'
      exact Nat.eq_of_beq_eq_true h'
    · rw [if_neg e]
      rw [beq_eq_false_iff_ne.mpr e] at h'
      have hne := beq_eq_false_iff_ne.mp h'
      omega
  have hfor : ∀ (σ : Sector) (ρ : Row), ρ ∈ I.rows → ρ.sector = oppositeSector σ →
      ∀ sup ∈ concatReps repsX repsZ σ, sup.Nodup ∧ (∀ q ∈ sup, q ∈ I.Q) ∧
        supportIntersectionSize sup ρ.support % 2 = 0 := by
    intro σ ρ hρ hsec sup hsup
    cases σ with
    | X =>
        have hr := hreps sup (List.mem_append_left _ hsup)
        exact ⟨hr.1, hr.2, hcX sup hsup ρ hρ hsec⟩
    | Z =>
        have hr := hreps sup (List.mem_append_right _ hsup)
        exact ⟨hr.1, hr.2, hcZ sup hsup ρ hρ hsec⟩
  rw [concatVectors_eq]
  have hlen : ∀ v ∈ (List.range blocks.length).flatMap (fun j => I.rows.map (fun r =>
        (r.sector, concatInner I blocks.length j r))) ++
      O.rows.map (fun r =>
        (r.sector, concatOuter I blocks (concatReps repsX repsZ r.sector) r)),
      v.2.length = concatQubits I blocks := by
    intro v hv
    unfold concatQubits
    rcases List.mem_append.mp hv with h1 | h1
    · obtain ⟨j, _, hm⟩ := List.mem_flatMap.mp h1
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hm
      rw [Nat.mul_comm]
      exact length_concatInner I _ j r
    · obtain ⟨r, _, rfl⟩ := List.mem_map.mp h1
      rw [Nat.mul_comm]
      exact length_concatOuter I blocks _ r
  intro x hx y hy hsec
  unfold naturalRows at hx hy
  obtain ⟨vx, hvx, rfl⟩ := List.mem_map.mp hx
  obtain ⟨vy, hvy, rfl⟩ := List.mem_map.mp hy
  show supportIntersectionSize (supportOfVector _ vx.2) (supportOfVector _ vy.2) % 2 = 0
  rw [overlap_supportOfVector _ _ _ (hlen vx hvx) (hlen vy hvy)]
  have hsec' : vy.1 = oppositeSector vx.1 := hsec
  rcases List.mem_append.mp hvx with h1 | h1
  · obtain ⟨j, _, hm⟩ := List.mem_flatMap.mp h1
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
    rcases List.mem_append.mp hvy with h2 | h2
    · obtain ⟨j2, _, hm2⟩ := List.mem_flatMap.mp h2
      obtain ⟨r2, hr2, rfl⟩ := List.mem_map.mp hm2
      exact concat_inner_inner I hI _ j j2 r r2 hr hr2 hsec'
    · obtain ⟨r', _, rfl⟩ := List.mem_map.mp h2
      exact concat_inner_outer I hI blocks _ j r r'
        (hfor r'.sector r hr (oppositeSector_symm hsec'))
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h1
    rcases List.mem_append.mp hvy with h2 | h2
    · obtain ⟨j2, _, hm2⟩ := List.mem_flatMap.mp h2
      obtain ⟨r2, hr2, rfl⟩ := List.mem_map.mp hm2
      rw [dotPar_comm]
      exact concat_inner_outer I hI blocks _ j2 r2 r (hfor r.sector r2 hr2 hsec')
    · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp h2
      have hsec'' : r'.sector = oppositeSector r.sector := hsec'
      show dotPar (concatOuter I blocks (concatReps repsX repsZ r.sector) r)
        (concatOuter I blocks (concatReps repsX repsZ r'.sector) r') % 2 = 0
      cases hs : r.sector with
      | X =>
          rw [hs] at hsec''
          rw [hsec'']
          exact concat_outer_outer O I hO hI blocks repsX repsZ hk hB hnd hsub
            (fun sup hsup => hreps sup (List.mem_append_left _ hsup)) hdual r r' hr hr' hs
            hsec''
      | Z =>
          rw [hs] at hsec''
          rw [hsec'', dotPar_comm]
          exact concat_outer_outer O I hO hI blocks repsX repsZ hk hB hnd hsub
            (fun sup hsup => hreps sup (List.mem_append_left _ hsup)) hdual r' r hr' hr
            hsec'' hs

/-- The output of `A-CONCAT` is well-formed. -/
theorem wf_concatState (O I : CodeState) (blocks repsX repsZ : List (List Nat))
    (hO : EncodingWellFormed O) (hI : EncodingWellFormed I)
    (hty : concatTyped O I blocks repsX repsZ = true) :
    EncodingWellFormed (concatState O I blocks repsX repsZ) :=
  wf_constructedState _ _ (concat_naturalOrthogonal O I blocks repsX repsZ hO hI hty)

/-! ## Evaluations -/

/-- Every evaluation of `lift_G(A, B)` yields a well-formed state. -/
theorem evalExpr_lift_wf {orders : List Nat} {A B : List (List (List (List Nat)))}
    {s : CodeState} (h : EvalExpr (StateExpr.lift orders A B) s) :
    EncodingWellFormed s := by
  cases h
  exact wf_liftState orders A B

/-- Every evaluation of `twoblock_G(a, b)` yields a well-formed state. -/
theorem evalExpr_twoblock_wf {orders : List Nat} {a b : List (List Nat)} {s : CodeState}
    (h : EvalExpr (StateExpr.twoblock orders a b) s) : EncodingWellFormed s := by
  cases h
  exact wf_twoblockState orders a b

/-- Every evaluation of `concat(e_O, e_I; blocks)` yields a well-formed
    state. -/
theorem evalExpr_concat_wf {eO eI : StateExpr} {blocks repsX repsZ : List (List Nat)}
    {s : CodeState} (h : EvalExpr (StateExpr.concat eO eI blocks repsX repsZ) s) :
    EncodingWellFormed s := by
  cases h with
  | concat hO hI hty _ _ _ => exact wf_concatState _ _ blocks repsX repsZ hO hI hty

end CodeCalculus
