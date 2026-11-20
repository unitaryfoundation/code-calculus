import CodeCalculus.ConstructorWellFormedness
import CodeCalculus.GraftWellFormedness
import CodeCalculus.ExactPeel

/-!
# Constructor well-formedness and the parameter bookkeeping

The per-constructor half of `spec/OPERATIONAL_SEMANTICS.md` §4.34.

* `L-HGP`: the natural rows have pairwise even overlap for every pair of
  matrices (`hgp_naturalOrthogonal`), so every evaluation of `hgp(H₁, H₂)`
  yields a well-formed state (`evalExpr_hgp_wf`), with no hypothesis.
* `L-LIFTED`, `L-GROUP-ALGEBRA`, `A-CONCAT`: the overlap and the
  well-formedness theorems are in `ConstructorOverlap.lean`.
* `k`: on a well-formed state, `k` is `n` minus the two displayed row counts
  (`stateK_of_wf`), which is the rank bookkeeping the cards name. The closed
  forms of §4.34 (`k₁k₂ + k₁ᵀk₂ᵀ` for `L-HGP`, `2(ℓ - rank[L(a) | L(b)])`
  for `L-GROUP-ALGEBRA`, `k_O` for `A-CONCAT`) are not mechanized.
-/

namespace CodeCalculus

/-! ## Overlap of vectors -/

theorem dotPar_append : ∀ (a b c d : List Bool), a.length = b.length →
    dotPar (a ++ c) (b ++ d) = dotPar a b + dotPar c d
  | [], [], c, d, _ => by
      rw [List.nil_append, List.nil_append, dotPar_nil_left, Nat.zero_add]
  | x :: a, y :: b, c, d, h => by
      rw [List.cons_append, List.cons_append, dotPar_cons, dotPar_cons,
        dotPar_append a b c d (Nat.succ.inj h)]
      omega
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h

theorem dotPar_map_map_gen {α : Type} (f g : α → Bool) : ∀ L : List α,
    dotPar (L.map f) (L.map g) = (L.filter (fun x => f x && g x)).length
  | [] => rfl
  | x :: L => by
      rw [List.map_cons, List.map_cons, dotPar_cons, dotPar_map_map_gen f g L]
      cases h : (f x && g x) with
      | true =>
          rw [List.filter_cons_of_pos (p := fun x => f x && g x) h, List.length_cons]
          show 1 + _ = _ + 1
          omega
      | false =>
          rw [List.filter_cons_of_neg (p := fun x => f x && g x)
            (by rw [h]; exact Bool.false_ne_true)]
          show 0 + _ = _
          rw [Nat.zero_add]

theorem map_getD_range (v : List Bool) :
    (List.range v.length).map (fun q => v.getD q false) = v := by
  apply List.ext_getElem
  · rw [List.length_map, List.length_range]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2]
    rfl

theorem contains_supportOfVector (n : Nat) (v : List Bool) (q : Nat) (hq : q < n) :
    (supportOfVector n v).contains q = v.getD q false := by
  cases hv : v.getD q false with
  | true =>
      rw [List.contains_iff_mem]
      exact List.mem_filter.mpr ⟨List.mem_range.mpr hq, hv⟩
  | false =>
      cases hc : (supportOfVector n v).contains q with
      | false => rfl
      | true =>
          have hmem := (List.mem_filter.mp (List.contains_iff_mem.mp hc)).2
          rw [hv] at hmem
          exact absurd hmem Bool.false_ne_true

/-- The overlap of two natural rows is the overlap count of their vectors. -/
theorem overlap_supportOfVector (n : Nat) (v w : List Bool) (hv : v.length = n)
    (hw : w.length = n) :
    supportIntersectionSize (supportOfVector n v) (supportOfVector n w) = dotPar v w := by
  rw [supportIntersectionSize_eq_dotPar (List.range n) _ _ (nodup_range_cf _)
    (supportOfVector_nodup n v) (supportOfVector_subset n v)]
  have key : ∀ u : List Bool, u.length = n →
      (List.range n).map (fun x => (supportOfVector n u).contains x) = u := by
    intro u hu
    have h1 : (List.range n).map (fun x => (supportOfVector n u).contains x) =
        (List.range n).map (fun q => u.getD q false) :=
      List.map_congr_left (fun q hq => contains_supportOfVector n u q (List.mem_range.mp hq))
    rw [h1, ← hu]
    exact map_getD_range u
  rw [key v hv, key w hw]

/-! ## Index pairs -/

theorem mem_indexPairs {m n a b : Nat} : (a, b) ∈ indexPairs m n ↔ a < m ∧ b < n := by
  unfold indexPairs
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨a', ha', hmem⟩
    obtain ⟨b', hb', heq⟩ := List.mem_map.mp hmem
    cases heq
    exact ⟨List.mem_range.mp ha', List.mem_range.mp hb'⟩
  · rintro ⟨ha, hb⟩
    exact ⟨a, List.mem_range.mpr ha, List.mem_map.mpr ⟨b, List.mem_range.mpr hb, rfl⟩⟩

theorem length_pairsOf (n : Nat) : ∀ l : List Nat,
    (l.flatMap (fun a => (List.range n).map (fun b => (a, b)))).length = l.length * n
  | [] => by rw [List.flatMap_nil, List.length_nil, List.length_nil, Nat.zero_mul]
  | a :: l => by
      rw [List.flatMap_cons, List.length_append, length_pairsOf n l, List.length_map,
        List.length_range, List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem length_indexPairs (m n : Nat) : (indexPairs m n).length = m * n := by
  unfold indexPairs
  rw [length_pairsOf, List.length_range]

theorem nodup_map_pair (a : Nat) : ∀ l : List Nat, l.Nodup →
    (l.map (fun b => (a, b))).Nodup
  | [], _ => List.nodup_nil
  | b :: l, h => by
      rw [List.nodup_cons] at h
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, nodup_map_pair a l h.2⟩
      intro hmem
      obtain ⟨b', hb', heq⟩ := List.mem_map.mp hmem
      exact h.1 ((Prod.mk.inj heq).2 ▸ hb')

theorem nodup_pairsOf (n : Nat) : ∀ l : List Nat, l.Nodup →
    (l.flatMap (fun a => (List.range n).map (fun b => (a, b)))).Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
      rw [List.nodup_cons] at h
      rw [List.flatMap_cons, List.nodup_append]
      refine ⟨?_, nodup_pairsOf n l h.2, ?_⟩
      · exact nodup_map_pair a _ (nodup_range_cf _)
      · intro x hx y hy hxy
        obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
        obtain ⟨a', ha', hmem⟩ := List.mem_flatMap.mp hy
        obtain ⟨b', _, rfl⟩ := List.mem_map.mp hmem
        have : a = a' := (Prod.mk.inj hxy).1
        exact h.1 (this ▸ ha')

theorem nodup_indexPairs (m n : Nat) : (indexPairs m n).Nodup :=
  nodup_pairsOf n _ (nodup_range_cf _)

/-- A predicate that singles out one point of a list not containing it. -/
theorem filter_point_absent {α : Type} [DecidableEq α] (c : α) (B : Bool) :
    ∀ L : List α, c ∉ L → (L.filter (fun p => decide (p = c) && B)).length = 0
  | [], _ => rfl
  | x :: L, h => by
      have hx : x ≠ c := fun hxc => h (hxc ▸ List.mem_cons_self ..)
      have hL : c ∉ L := fun hc => h (List.mem_cons_of_mem x hc)
      rw [List.filter_cons_of_neg (by
        rw [decide_eq_false hx]
        exact Bool.false_ne_true)]
      exact filter_point_absent c B L hL

/-- A predicate that singles out one point of a repeat-free list. -/
theorem filter_point_length {α : Type} [DecidableEq α] (c : α) (B : Bool) :
    ∀ L : List α, L.Nodup → c ∈ L →
      (L.filter (fun p => decide (p = c) && B)).length = if B then 1 else 0
  | [], _, h => nomatch h
  | x :: L, hnd, hc => by
      rw [List.nodup_cons] at hnd
      rcases Decidable.em (x = c) with hxc | hxc
      · subst hxc
        cases B with
        | true =>
            rw [List.filter_cons_of_pos (by rw [decide_eq_true rfl]; rfl), List.length_cons,
              filter_point_absent x true L hnd.1]
            rfl
        | false =>
            rw [List.filter_cons_of_neg (by
              rw [Bool.and_false]
              exact Bool.false_ne_true)]
            rw [filter_point_absent x false L hnd.1]
            rfl
      · have hcL : c ∈ L := by
          rcases List.mem_cons.mp hc with h | h
          · exact absurd h.symm hxc
          · exact h
        rw [List.filter_cons_of_neg (by
          rw [decide_eq_false hxc]
          exact Bool.false_ne_true)]
        exact filter_point_length c B L hnd.2 hcL

/-! ## `L-HGP` -/

theorem length_hgpXVector (H1 H2 : List (List Bool)) (aj : Nat × Nat) :
    (hgpXVector H1 H2 aj).length = hgpQubits H1 H2 := by
  unfold hgpXVector hgpQubits
  rw [List.length_append, List.length_map, List.length_map, length_indexPairs,
    length_indexPairs]

theorem length_hgpZVector (H1 H2 : List (List Bool)) (ib : Nat × Nat) :
    (hgpZVector H1 H2 ib).length = hgpQubits H1 H2 := by
  unfold hgpZVector hgpQubits
  rw [List.length_append, List.length_map, List.length_map, length_indexPairs,
    length_indexPairs]

/-- §4.34 for `L-HGP`: the natural `X`-row `(a, j)` and the natural `Z`-row
    `(i, b)` meet at the left qubit `(i, j)` and the right qubit `(a, b)`,
    each exactly when `H₁[a, i] H₂[b, j] = 1`. -/
theorem hgp_overlap (H1 H2 : List (List Bool)) (aj ib : Nat × Nat)
    (haj : aj ∈ indexPairs H1.length (matCols H2))
    (hib : ib ∈ indexPairs (matCols H1) H2.length) :
    dotPar (hgpXVector H1 H2 aj) (hgpZVector H1 H2 ib) % 2 = 0 := by
  obtain ⟨a, j⟩ := aj
  obtain ⟨i, b⟩ := ib
  have haj' := mem_indexPairs.mp haj
  have hib' := mem_indexPairs.mp hib
  unfold hgpXVector hgpZVector
  rw [dotPar_append _ _ _ _ (by rw [List.length_map, List.length_map]),
    dotPar_map_map_gen, dotPar_map_map_gen]
  have hleft : (fun ij : Nat × Nat =>
      (decide (ij.2 = j) && matEntry H1 a ij.1) && (decide (ij.1 = i) && matEntry H2 b ij.2)) =
      (fun ij => decide (ij = (i, j)) && (matEntry H1 a i && matEntry H2 b j)) := by
    funext ij
    obtain ⟨i', j'⟩ := ij
    rcases Decidable.em (j' = j) with h1 | h1
    · rcases Decidable.em (i' = i) with h2 | h2
      · subst h1; subst h2
        rw [decide_eq_true rfl, decide_eq_true rfl, decide_eq_true rfl]
        rfl
      · rw [decide_eq_false h2, decide_eq_false (fun h => h2 (Prod.mk.inj h).1)]
        rw [Bool.false_and, Bool.and_false, Bool.false_and]
    · rw [decide_eq_false h1, decide_eq_false (fun h => h1 (Prod.mk.inj h).2)]
      rw [Bool.false_and, Bool.false_and, Bool.false_and]
  have hright : (fun ab : Nat × Nat =>
      (decide (ab.1 = a) && matEntry H2 ab.2 j) && (decide (ab.2 = b) && matEntry H1 ab.1 i)) =
      (fun ab => decide (ab = (a, b)) && (matEntry H2 b j && matEntry H1 a i)) := by
    funext ab
    obtain ⟨a', b'⟩ := ab
    rcases Decidable.em (a' = a) with h1 | h1
    · rcases Decidable.em (b' = b) with h2 | h2
      · subst h1; subst h2
        rw [decide_eq_true rfl, decide_eq_true rfl, decide_eq_true rfl]
        rfl
      · rw [decide_eq_false h2, decide_eq_false (fun h => h2 (Prod.mk.inj h).2)]
        rw [Bool.false_and, Bool.and_false, Bool.false_and]
    · rw [decide_eq_false h1, decide_eq_false (fun h => h1 (Prod.mk.inj h).1)]
      rw [Bool.false_and, Bool.false_and, Bool.false_and]
  rw [hleft, hright,
    filter_point_length (i, j) _ _ (nodup_indexPairs _ _)
      (mem_indexPairs.mpr ⟨hib'.1, haj'.2⟩),
    filter_point_length (a, b) _ _ (nodup_indexPairs _ _)
      (mem_indexPairs.mpr ⟨haj'.1, hib'.2⟩)]
  cases matEntry H1 a i <;> cases matEntry H2 b j <;> rfl

/-- The natural rows of `hgp(H₁, H₂)` have pairwise even overlap across the
    sectors, for every pair of matrices. -/
theorem hgp_naturalOrthogonal (H1 H2 : List (List Bool)) :
    NaturalOrthogonal (naturalRows (hgpQubits H1 H2) (hgpVectors H1 H2)) := by
  intro x hx y hy hsec
  unfold naturalRows at hx hy
  obtain ⟨vx, hvx, rfl⟩ := List.mem_map.mp hx
  obtain ⟨vy, hvy, rfl⟩ := List.mem_map.mp hy
  unfold hgpVectors at hvx hvy
  rcases List.mem_append.mp hvx with hX | hZ
  · obtain ⟨aj, haj, rfl⟩ := List.mem_map.mp hX
    rcases List.mem_append.mp hvy with hX' | hZ'
    · obtain ⟨aj', _, rfl⟩ := List.mem_map.mp hX'
      cases hsec
    · obtain ⟨ib, hib, rfl⟩ := List.mem_map.mp hZ'
      show supportIntersectionSize (supportOfVector _ (hgpXVector H1 H2 aj))
        (supportOfVector _ (hgpZVector H1 H2 ib)) % 2 = 0
      rw [overlap_supportOfVector _ _ _ (length_hgpXVector H1 H2 aj)
        (length_hgpZVector H1 H2 ib)]
      exact hgp_overlap H1 H2 aj ib haj hib
  · obtain ⟨ib, hib, rfl⟩ := List.mem_map.mp hZ
    rcases List.mem_append.mp hvy with hX' | hZ'
    · obtain ⟨aj, haj, rfl⟩ := List.mem_map.mp hX'
      show supportIntersectionSize (supportOfVector _ (hgpZVector H1 H2 ib))
        (supportOfVector _ (hgpXVector H1 H2 aj)) % 2 = 0
      rw [overlap_supportOfVector _ _ _ (length_hgpZVector H1 H2 ib)
        (length_hgpXVector H1 H2 aj), dotPar_comm]
      exact hgp_overlap H1 H2 aj ib haj hib
    · obtain ⟨ib', _, rfl⟩ := List.mem_map.mp hZ'
      cases hsec

/-- The output of `L-HGP` is well-formed. -/
theorem wf_hgpState (H1 H2 : List (List Bool)) : EncodingWellFormed (hgpState H1 H2) :=
  wf_constructedState _ _ (hgp_naturalOrthogonal H1 H2)

/-! ## Evaluations -/

/-- Every evaluation of `hgp(H₁, H₂)` yields a well-formed state. -/
theorem evalExpr_hgp_wf {H1 H2 : List (List Bool)} {s : CodeState}
    (h : EvalExpr (StateExpr.hgp H1 H2) s) : EncodingWellFormed s := by
  cases h
  exact wf_hgpState H1 H2

/-- The `n` of an evaluation of `lift_G(A, B)`. -/
theorem evalExpr_lift_n {orders : List Nat} {A B : List (List (List (List Nat)))}
    {s : CodeState} (h : EvalExpr (StateExpr.lift orders A B) s) :
    s.Q.length = (groupElements orders).length *
      (matCols A * matCols B + A.length * B.length) := by
  cases h
  exact liftState_n orders A B

/-- The `n` of an evaluation of `twoblock_G(a, b)`. -/
theorem evalExpr_twoblock_n {orders : List Nat} {a b : List (List Nat)}
    {s : CodeState} (h : EvalExpr (StateExpr.twoblock orders a b) s) :
    s.Q.length = 2 * (groupElements orders).length := by
  cases h
  exact twoblockState_n orders a b

/-- The `n` of an evaluation of `hgp(H₁, H₂)`: `n₁ n₂ + m₁ m₂`. -/
theorem evalExpr_hgp_n {H1 H2 : List (List Bool)} {s : CodeState}
    (h : EvalExpr (StateExpr.hgp H1 H2) s) :
    s.Q.length = matCols H1 * matCols H2 + H1.length * H2.length := by
  cases h
  exact hgpState_n H1 H2

/-! ## The `k` bookkeeping -/

/-- On a well-formed state, `k` is `n` minus the two displayed row counts. -/
theorem stateK_of_wf (s : CodeState) (hwf : EncodingWellFormed s) :
    stateK s = s.Q.length - (sectorRows s Sector.X).length - (sectorRows s Sector.Z).length := by
  obtain ⟨hQ, hids, _, _, _, _, _, hI2⟩ := hwf
  unfold stateK
  rw [sectorRank_eq_length_of_I2 s hQ hids hI2 Sector.X,
    sectorRank_eq_length_of_I2 s hQ hids hI2 Sector.Z]

end CodeCalculus
