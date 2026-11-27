import CodeCalculus.BalancedOverlap
import CodeCalculus.MaskBlocks

/-!
# `k` of `L-BALANCED`, `L-TANNER`, and `L-TILE` from the natural matrices

`spec/OPERATIONAL_SEMANTICS.md` §4.35 claims no closed form for the `k` of
these three constructors: it is the rank bookkeeping of the output. This
module states that bookkeeping against the inputs, the counting and local-rank
bounds, the exact equality conditions, the disjoint-views closed form for
`L-TANNER`, and the formal no-go theorems showing that no function of
`(n, LX, LZ, |viewsX|, |viewsZ|)` determines `k` across all valid `L-TANNER`
evaluations and no function of `(tiles, tileQubits, |placements|,
tileKeptRows X, tileKeptRows Z)` determines `k` across all valid `L-TILE`
evaluations.

For each constructor, `k` is `n` minus the rank of the matrix of natural
`X`-rows minus the rank of the matrix of natural `Z`-rows, the two matrices
being written out as lists of row masks. The bookkeeping statements hold for
every input, with no typing premise, because they are instances of
`stateK_constructedState`.

These bookkeeping theorems are not formulas in the parameters of the inputs,
and the names ending in `_k_closed` follow the established naming only.
-/

namespace CodeCalculus

/-! ## `L-BALANCED` -/

/-- `k` of `L-BALANCED`: `n` minus the ranks of the two matrices of natural
    rows, one row per orbit. -/
theorem balancedState_k_closed (orders : List Nat) (H1 : List (List Bool))
    (rows1 cols1 : List (List Nat)) (H2 : List (List Bool)) (rows2 cols2 : List (List Nat)) :
    stateK (balancedState orders H1 rows1 cols1 H2 rows2 cols2) =
      balancedQubits orders H1 rows1 cols1 H2 rows2 cols2 -
        rankBitmasks ((orbitReps orders rows1 cols2 H1.length (matCols H2)).map (fun c =>
          boolsToMask (balancedXVector orders H1 rows1 cols1 H2 rows2 cols2 c))) -
        rankBitmasks ((orbitReps orders cols1 rows2 (matCols H1) H2.length).map (fun c =>
          boolsToMask (balancedZVector orders H1 rows1 cols1 H2 rows2 cols2 c))) := by
  unfold balancedState
  rw [stateK_constructedState, balancedVectors_eq]
  obtain ⟨hX, hZ⟩ := naturalMasks_XZ (balancedQubits orders H1 rows1 cols1 H2 rows2 cols2)
    (balancedXVector orders H1 rows1 cols1 H2 rows2 cols2)
    (balancedZVector orders H1 rows1 cols1 H2 rows2 cols2)
    (orbitReps orders rows1 cols2 H1.length (matCols H2))
    (orbitReps orders cols1 rows2 (matCols H1) H2.length)
  have hmX : (orbitReps orders rows1 cols2 H1.length (matCols H2)).map (fun h =>
        vecMask (balancedQubits orders H1 rows1 cols1 H2 rows2 cols2)
          (balancedXVector orders H1 rows1 cols1 H2 rows2 cols2 h)) =
      (orbitReps orders rows1 cols2 H1.length (matCols H2)).map (fun c =>
        boolsToMask (balancedXVector orders H1 rows1 cols1 H2 rows2 cols2 c)) :=
    List.map_congr_left (fun c _ => vecMask_eq_boolsToMask _ _
      (length_balancedXVector orders H1 rows1 cols1 H2 rows2 cols2 c))
  have hmZ : (orbitReps orders cols1 rows2 (matCols H1) H2.length).map (fun h =>
        vecMask (balancedQubits orders H1 rows1 cols1 H2 rows2 cols2)
          (balancedZVector orders H1 rows1 cols1 H2 rows2 cols2 h)) =
      (orbitReps orders cols1 rows2 (matCols H1) H2.length).map (fun c =>
        boolsToMask (balancedZVector orders H1 rows1 cols1 H2 rows2 cols2 c)) :=
    List.map_congr_left (fun c _ => vecMask_eq_boolsToMask _ _
      (length_balancedZVector orders H1 rows1 cols1 H2 rows2 cols2 c))
  rw [hX, hZ, hmX, hmZ]

theorem evalExpr_balanced_k {orders : List Nat} {H1 H2 : List (List Bool)}
    {rows1 cols1 rows2 cols2 : List (List Nat)} {s : CodeState}
    (h : EvalExpr (StateExpr.balanced orders H1 rows1 cols1 H2 rows2 cols2) s) :
    stateK s =
      balancedQubits orders H1 rows1 cols1 H2 rows2 cols2 -
        rankBitmasks ((orbitReps orders rows1 cols2 H1.length (matCols H2)).map (fun c =>
          boolsToMask (balancedXVector orders H1 rows1 cols1 H2 rows2 cols2 c))) -
        rankBitmasks ((orbitReps orders cols1 rows2 (matCols H1) H2.length).map (fun c =>
          boolsToMask (balancedZVector orders H1 rows1 cols1 H2 rows2 cols2 c))) := by
  cases h with
  | balanced _ _ => exact balancedState_k_closed orders H1 rows1 cols1 H2 rows2 cols2

/-! ## `L-TANNER` -/

theorem flatMap_map_pair {α β γ : Type} (f : α → β → γ) (M : List β) : ∀ L : List α,
    L.flatMap (fun a => M.map (fun b => f a b)) =
      (L.flatMap (fun a => M.map (fun b => (a, b)))).map (fun ab => f ab.1 ab.2)
  | [] => rfl
  | a :: L => by
      rw [List.flatMap_cons, List.flatMap_cons, List.map_append, List.map_map,
        flatMap_map_pair f M L]
      rfl

theorem length_tannerRow (n : Nat) (view : List Nat) (l : List Bool) :
    (tannerRow n view l).length = n := by
  unfold tannerRow
  rw [List.length_map, List.length_range]

/-- `k` of `L-TANNER`: `n` minus the ranks of the two matrices of natural
    rows, one row per vertex and local row. -/
theorem tannerState_k_closed (n : Nat) (LX LZ : List (List Bool))
    (viewsX viewsZ : List (List Nat)) :
    stateK (tannerState n LX LZ viewsX viewsZ) =
      n - rankBitmasks (viewsX.flatMap (fun v =>
            LX.map (fun l => boolsToMask (tannerRow n v l)))) -
        rankBitmasks (viewsZ.flatMap (fun v =>
            LZ.map (fun l => boolsToMask (tannerRow n v l)))) := by
  unfold tannerState
  rw [stateK_constructedState]
  have e : tannerVectors n LX LZ viewsX viewsZ =
      (viewsX.flatMap (fun v => LX.map (fun l => (v, l)))).map
        (fun vl => (Sector.X, tannerRow n vl.1 vl.2)) ++
      (viewsZ.flatMap (fun v => LZ.map (fun l => (v, l)))).map
        (fun vl => (Sector.Z, tannerRow n vl.1 vl.2)) := by
    unfold tannerVectors
    rw [flatMap_map_pair (fun v l => (Sector.X, tannerRow n v l)) LX viewsX,
      flatMap_map_pair (fun v l => (Sector.Z, tannerRow n v l)) LZ viewsZ]
  obtain ⟨hX, hZ⟩ := naturalMasks_XZ n
    (fun vl : List Nat × List Bool => tannerRow n vl.1 vl.2)
    (fun vl : List Nat × List Bool => tannerRow n vl.1 vl.2)
    (viewsX.flatMap (fun v => LX.map (fun l => (v, l))))
    (viewsZ.flatMap (fun v => LZ.map (fun l => (v, l))))
  have hmX : (viewsX.flatMap (fun v => LX.map (fun l => (v, l)))).map
        (fun h => vecMask n (tannerRow n h.1 h.2)) =
      (viewsX.flatMap (fun v => LX.map (fun l => (v, l)))).map
        (fun ab => boolsToMask (tannerRow n ab.1 ab.2)) :=
    List.map_congr_left (fun h _ => vecMask_eq_boolsToMask n _ (length_tannerRow n h.1 h.2))
  have hmZ : (viewsZ.flatMap (fun v => LZ.map (fun l => (v, l)))).map
        (fun h => vecMask n (tannerRow n h.1 h.2)) =
      (viewsZ.flatMap (fun v => LZ.map (fun l => (v, l)))).map
        (fun ab => boolsToMask (tannerRow n ab.1 ab.2)) :=
    List.map_congr_left (fun h _ => vecMask_eq_boolsToMask n _ (length_tannerRow n h.1 h.2))
  rw [e, hX, hZ, hmX, hmZ,
    flatMap_map_pair (fun v l => boolsToMask (tannerRow n v l)) LX viewsX,
    flatMap_map_pair (fun v l => boolsToMask (tannerRow n v l)) LZ viewsZ]

theorem evalExpr_tanner_k {n : Nat} {LX LZ : List (List Bool)}
    {viewsX viewsZ : List (List Nat)} {s : CodeState}
    (h : EvalExpr (StateExpr.tanner n LX LZ viewsX viewsZ) s) :
    stateK s =
      n - rankBitmasks (viewsX.flatMap (fun v =>
            LX.map (fun l => boolsToMask (tannerRow n v l)))) -
        rankBitmasks (viewsZ.flatMap (fun v =>
            LZ.map (fun l => boolsToMask (tannerRow n v l)))) := by
  cases h with
  | tanner _ _ _ => exact tannerState_k_closed n LX LZ viewsX viewsZ

/-! ## `L-TILE` -/

/-- The local rows of sector `σ` of placement `pos` that are not removed. -/
def tileRowIdxs (tiles : List (Nat × List (List Nat) × List (List Nat)))
    (placements : List (Nat × List Nat)) (removed : List (Nat × Sector × Nat))
    (pos : Nat) (σ : Sector) : List Nat :=
  (List.range (tileRows (tiles.getD (placements.getD pos (0, [])).1 (0, [], [])) σ).length).filter
    (fun idx => !removed.any (fun x => x.1 == pos && decide (x.2.1 = σ) && x.2.2 == idx))

/-- The natural row of local row `idx` of sector `σ` of placement `pos`,
    over the site classes. -/
def tileRowVector (tiles : List (Nat × List (List Nat) × List (List Nat)))
    (placements : List (Nat × List Nat)) (idents : List (Nat × Nat))
    (pos : Nat) (σ : Sector) (idx : Nat) : List Bool :=
  (tileClasses placements idents).map (fun c =>
    (((tileRows (tiles.getD (placements.getD pos (0, [])).1 (0, [], [])) σ).getD idx []).filter
      (fun q => ((tileReps placements idents).lookup
        ((placements.getD pos (0, [])).2.getD q 0)).getD 0 == c)).length % 2 == 1)

theorem tileVectors_eq (tiles : List (Nat × List (List Nat) × List (List Nat)))
    (placements : List (Nat × List Nat)) (idents : List (Nat × Nat))
    (removed : List (Nat × Sector × Nat)) :
    tileVectors tiles placements idents removed =
      (List.range placements.length).flatMap (fun pos =>
        [Sector.X, Sector.Z].flatMap (fun σ =>
          (tileRowIdxs tiles placements removed pos σ).map (fun idx =>
            (σ, tileRowVector tiles placements idents pos σ idx)))) := rfl

theorem length_tileRowVector (tiles : List (Nat × List (List Nat) × List (List Nat)))
    (placements : List (Nat × List Nat)) (idents : List (Nat × Nat))
    (pos : Nat) (σ : Sector) (idx : Nat) :
    (tileRowVector tiles placements idents pos σ idx).length = tileQubits placements idents := by
  unfold tileRowVector tileQubits
  rw [List.length_map]

/-- The masks of one sector of rows listed position by position, the
    `X`-rows of a position before its `Z`-rows. -/
theorem naturalMasks_interleaved (n : Nat) (R : Nat → Sector → List Nat)
    (V : Nat → Sector → Nat → List Bool) (σ0 : Sector) : ∀ L : List Nat,
    naturalMasks n (L.flatMap (fun pos => [Sector.X, Sector.Z].flatMap (fun σ =>
        (R pos σ).map (fun idx => (σ, V pos σ idx))))) σ0 =
      L.flatMap (fun pos => (R pos σ0).map (fun idx => vecMask n (V pos σ0 idx)))
  | [] => rfl
  | pos :: L => by
      have ih := naturalMasks_interleaved n R V σ0 L
      unfold naturalMasks at ih ⊢
      have hhead : [Sector.X, Sector.Z].flatMap (fun σ =>
            (R pos σ).map (fun idx => (σ, V pos σ idx))) =
          (R pos Sector.X).map (fun idx => (Sector.X, V pos Sector.X idx)) ++
            (R pos Sector.Z).map (fun idx => (Sector.Z, V pos Sector.Z idx)) := by
        rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [List.flatMap_cons, hhead, List.flatMap_cons, List.filter_append, List.map_append, ih,
        List.filter_append]
      cases σ0 with
      | X =>
          rw [filter_tagged_same Sector.X (V pos Sector.X) (R pos Sector.X),
            filter_tagged_other Sector.Z Sector.X (by decide) (V pos Sector.Z) (R pos Sector.Z),
            List.append_nil, List.map_map]
          rfl
      | Z =>
          rw [filter_tagged_other Sector.X Sector.Z (by decide) (V pos Sector.X) (R pos Sector.X),
            filter_tagged_same Sector.Z (V pos Sector.Z) (R pos Sector.Z),
            List.nil_append, List.map_map]
          rfl

theorem flatMap_congr_on {α β : Type} (f g : α → List β) : ∀ L : List α,
    (∀ a ∈ L, f a = g a) → L.flatMap f = L.flatMap g
  | [], _ => rfl
  | a :: L, h => by
      rw [List.flatMap_cons, List.flatMap_cons, h a (List.mem_cons_self ..),
        flatMap_congr_on f g L (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- `k` of `L-TILE`: `n` minus the ranks of the two matrices of natural
    rows, one row per placement and local row that is not removed. -/
theorem tileState_k_closed (tiles : List (Nat × List (List Nat) × List (List Nat)))
    (placements : List (Nat × List Nat)) (idents : List (Nat × Nat))
    (removed : List (Nat × Sector × Nat)) :
    stateK (tileState tiles placements idents removed) =
      tileQubits placements idents -
        rankBitmasks ((List.range placements.length).flatMap (fun pos =>
          (tileRowIdxs tiles placements removed pos Sector.X).map (fun idx =>
            boolsToMask (tileRowVector tiles placements idents pos Sector.X idx)))) -
        rankBitmasks ((List.range placements.length).flatMap (fun pos =>
          (tileRowIdxs tiles placements removed pos Sector.Z).map (fun idx =>
            boolsToMask (tileRowVector tiles placements idents pos Sector.Z idx)))) := by
  unfold tileState
  rw [stateK_constructedState, tileVectors_eq,
    naturalMasks_interleaved (tileQubits placements idents)
      (tileRowIdxs tiles placements removed) (tileRowVector tiles placements idents) Sector.X,
    naturalMasks_interleaved (tileQubits placements idents)
      (tileRowIdxs tiles placements removed) (tileRowVector tiles placements idents) Sector.Z]
  have hm : ∀ σ : Sector, (List.range placements.length).flatMap (fun pos =>
        (tileRowIdxs tiles placements removed pos σ).map (fun idx =>
          vecMask (tileQubits placements idents)
            (tileRowVector tiles placements idents pos σ idx))) =
      (List.range placements.length).flatMap (fun pos =>
        (tileRowIdxs tiles placements removed pos σ).map (fun idx =>
          boolsToMask (tileRowVector tiles placements idents pos σ idx))) :=
    fun σ => flatMap_congr_on _ _ _ (fun pos _ => List.map_congr_left (fun idx _ =>
      vecMask_eq_boolsToMask _ _ (length_tileRowVector tiles placements idents pos σ idx)))
  rw [hm Sector.X, hm Sector.Z]

theorem evalExpr_tile_k {tiles : List (Nat × List (List Nat) × List (List Nat))}
    {placements : List (Nat × List Nat)} {idents : List (Nat × Nat)}
    {removed : List (Nat × Sector × Nat)} {s : CodeState}
    (h : EvalExpr (StateExpr.tile tiles placements idents removed) s) :
    stateK s =
      tileQubits placements idents -
        rankBitmasks ((List.range placements.length).flatMap (fun pos =>
          (tileRowIdxs tiles placements removed pos Sector.X).map (fun idx =>
            boolsToMask (tileRowVector tiles placements idents pos Sector.X idx)))) -
        rankBitmasks ((List.range placements.length).flatMap (fun pos =>
          (tileRowIdxs tiles placements removed pos Sector.Z).map (fun idx =>
            boolsToMask (tileRowVector tiles placements idents pos Sector.Z idx)))) := by
  cases h with
  | tile _ _ _ => exact tileState_k_closed tiles placements idents removed

/-! ## Counting bounds for `L-TANNER` and `L-TILE`

`k` of these two constructors has no closed form in the parameters of the
inputs. What the inputs do give is the counting bound: `k` is at least `n`
minus the number of natural rows, with equality exactly when the natural
rows of each sector are independent. For `L-TANNER` the number of natural
rows of a sector is the number of vertices times the number of local rows.
For `L-TILE` it is the number of local rows that are not removed. -/

theorem length_flatMap_map_dep {α β γ : Type} (f : α → List β) (g : α → β → γ) :
    ∀ L : List α, (L.flatMap (fun a => (f a).map (g a))).length = (L.flatMap f).length
  | [] => rfl
  | a :: L => by
      rw [List.flatMap_cons, List.flatMap_cons, List.length_append, List.length_append,
        List.length_map, length_flatMap_map_dep f g L]

/-- The counting bound for `L-TANNER`: `n` is at most `k` plus the number
    of natural rows. -/
theorem tannerState_k_ge (n : Nat) (LX LZ : List (List Bool))
    (viewsX viewsZ : List (List Nat)) :
    n ≤ stateK (tannerState n LX LZ viewsX viewsZ) +
      viewsX.length * LX.length + viewsZ.length * LZ.length := by
  rw [tannerState_k_closed]
  have hX := rankBitmasks_le_length (viewsX.flatMap (fun v =>
    LX.map (fun l => boolsToMask (tannerRow n v l))))
  have hZ := rankBitmasks_le_length (viewsZ.flatMap (fun v =>
    LZ.map (fun l => boolsToMask (tannerRow n v l))))
  rw [length_flatMap_map (fun v l => boolsToMask (tannerRow n v l)) LX viewsX] at hX
  rw [length_flatMap_map (fun v l => boolsToMask (tannerRow n v l)) LZ viewsZ] at hZ
  omega

/-- Equality in the counting bound for `L-TANNER`, when the natural rows of
    each sector are independent. -/
theorem tannerState_k_of_indep (n : Nat) (LX LZ : List (List Bool))
    (viewsX viewsZ : List (List Nat))
    (hX : independentMasks (viewsX.flatMap (fun v =>
      LX.map (fun l => boolsToMask (tannerRow n v l)))))
    (hZ : independentMasks (viewsZ.flatMap (fun v =>
      LZ.map (fun l => boolsToMask (tannerRow n v l))))) :
    stateK (tannerState n LX LZ viewsX viewsZ) =
      n - viewsX.length * LX.length - viewsZ.length * LZ.length := by
  rw [tannerState_k_closed, rankBitmasks_of_indep hX, rankBitmasks_of_indep hZ,
    length_flatMap_map (fun v l => boolsToMask (tannerRow n v l)) LX viewsX,
    length_flatMap_map (fun v l => boolsToMask (tannerRow n v l)) LZ viewsZ]

theorem evalExpr_tanner_k_ge {n : Nat} {LX LZ : List (List Bool)}
    {viewsX viewsZ : List (List Nat)} {s : CodeState}
    (h : EvalExpr (StateExpr.tanner n LX LZ viewsX viewsZ) s) :
    n ≤ stateK s + viewsX.length * LX.length + viewsZ.length * LZ.length := by
  cases h with
  | tanner _ _ _ => exact tannerState_k_ge n LX LZ viewsX viewsZ

/-- The number of local rows of sector `σ` that are not removed, over all
    placements. -/
def tileKeptRows (tiles : List (Nat × List (List Nat) × List (List Nat)))
    (placements : List (Nat × List Nat)) (removed : List (Nat × Sector × Nat))
    (σ : Sector) : Nat :=
  ((List.range placements.length).flatMap (fun pos =>
    tileRowIdxs tiles placements removed pos σ)).length

/-- The counting bound for `L-TILE`: the number of site classes is at most
    `k` plus the number of local rows that are not removed. -/
theorem tileState_k_ge (tiles : List (Nat × List (List Nat) × List (List Nat)))
    (placements : List (Nat × List Nat)) (idents : List (Nat × Nat))
    (removed : List (Nat × Sector × Nat)) :
    tileQubits placements idents ≤ stateK (tileState tiles placements idents removed) +
      tileKeptRows tiles placements removed Sector.X +
      tileKeptRows tiles placements removed Sector.Z := by
  rw [tileState_k_closed]
  have hX := rankBitmasks_le_length ((List.range placements.length).flatMap (fun pos =>
    (tileRowIdxs tiles placements removed pos Sector.X).map (fun idx =>
      boolsToMask (tileRowVector tiles placements idents pos Sector.X idx))))
  have hZ := rankBitmasks_le_length ((List.range placements.length).flatMap (fun pos =>
    (tileRowIdxs tiles placements removed pos Sector.Z).map (fun idx =>
      boolsToMask (tileRowVector tiles placements idents pos Sector.Z idx))))
  rw [length_flatMap_map_dep (fun pos => tileRowIdxs tiles placements removed pos Sector.X)
    (fun pos idx => boolsToMask (tileRowVector tiles placements idents pos Sector.X idx))] at hX
  rw [length_flatMap_map_dep (fun pos => tileRowIdxs tiles placements removed pos Sector.Z)
    (fun pos idx => boolsToMask (tileRowVector tiles placements idents pos Sector.Z idx))] at hZ
  unfold tileKeptRows
  omega

/-- Equality in the counting bound for `L-TILE`, when the natural rows of
    each sector are independent. -/
theorem tileState_k_of_indep (tiles : List (Nat × List (List Nat) × List (List Nat)))
    (placements : List (Nat × List Nat)) (idents : List (Nat × Nat))
    (removed : List (Nat × Sector × Nat))
    (hX : independentMasks ((List.range placements.length).flatMap (fun pos =>
      (tileRowIdxs tiles placements removed pos Sector.X).map (fun idx =>
        boolsToMask (tileRowVector tiles placements idents pos Sector.X idx)))))
    (hZ : independentMasks ((List.range placements.length).flatMap (fun pos =>
      (tileRowIdxs tiles placements removed pos Sector.Z).map (fun idx =>
        boolsToMask (tileRowVector tiles placements idents pos Sector.Z idx))))) :
    stateK (tileState tiles placements idents removed) =
      tileQubits placements idents - tileKeptRows tiles placements removed Sector.X -
        tileKeptRows tiles placements removed Sector.Z := by
  rw [tileState_k_closed, rankBitmasks_of_indep hX, rankBitmasks_of_indep hZ,
    length_flatMap_map_dep (fun pos => tileRowIdxs tiles placements removed pos Sector.X)
      (fun pos idx => boolsToMask (tileRowVector tiles placements idents pos Sector.X idx)),
    length_flatMap_map_dep (fun pos => tileRowIdxs tiles placements removed pos Sector.Z)
      (fun pos idx => boolsToMask (tileRowVector tiles placements idents pos Sector.Z idx))]
  rfl

theorem evalExpr_tile_k_ge {tiles : List (Nat × List (List Nat) × List (List Nat))}
    {placements : List (Nat × List Nat)} {idents : List (Nat × Nat)}
    {removed : List (Nat × Sector × Nat)} {s : CodeState}
    (h : EvalExpr (StateExpr.tile tiles placements idents removed) s) :
    tileQubits placements idents ≤ stateK s +
      tileKeptRows tiles placements removed Sector.X +
      tileKeptRows tiles placements removed Sector.Z := by
  cases h with
  | tile _ _ _ => exact tileState_k_ge tiles placements idents removed

theorem evalExpr_tanner_k_of_indep {n : Nat} {LX LZ : List (List Bool)}
    {viewsX viewsZ : List (List Nat)} {s : CodeState}
    (h : EvalExpr (StateExpr.tanner n LX LZ viewsX viewsZ) s)
    (hX : independentMasks (viewsX.flatMap (fun v =>
      LX.map (fun l => boolsToMask (tannerRow n v l)))))
    (hZ : independentMasks (viewsZ.flatMap (fun v =>
      LZ.map (fun l => boolsToMask (tannerRow n v l))))) :
    stateK s = n - viewsX.length * LX.length - viewsZ.length * LZ.length := by
  cases h with
  | tanner _ _ _ => exact tannerState_k_of_indep n LX LZ viewsX viewsZ hX hZ

theorem evalExpr_tile_k_of_indep {tiles : List (Nat × List (List Nat) × List (List Nat))}
    {placements : List (Nat × List Nat)} {idents : List (Nat × Nat)}
    {removed : List (Nat × Sector × Nat)} {s : CodeState}
    (h : EvalExpr (StateExpr.tile tiles placements idents removed) s)
    (hX : independentMasks ((List.range placements.length).flatMap (fun pos =>
      (tileRowIdxs tiles placements removed pos Sector.X).map (fun idx =>
        boolsToMask (tileRowVector tiles placements idents pos Sector.X idx)))))
    (hZ : independentMasks ((List.range placements.length).flatMap (fun pos =>
      (tileRowIdxs tiles placements removed pos Sector.Z).map (fun idx =>
        boolsToMask (tileRowVector tiles placements idents pos Sector.Z idx))))) :
    stateK s = tileQubits placements idents -
      tileKeptRows tiles placements removed Sector.X -
      tileKeptRows tiles placements removed Sector.Z := by
  cases h with
  | tile _ _ _ => exact tileState_k_of_indep tiles placements idents removed hX hZ

/-! ## Exact characterization of counting-bound equality -/

/-- A dependent mask list is spanned by a strictly shorter list. -/
theorem exists_shorter_spanning_of_dep : ∀ (xs cs : List Nat),
    cs.length = xs.length → (∀ c ∈ cs, c = 0 ∨ c = 1) →
    combineMasks xs cs = 0 → (∃ c ∈ cs, c = 1) →
    ∃ ys : List Nat, ys.length < xs.length ∧ ∀ x ∈ xs, inSpanMasks ys x
  | [], [], _, _, _, ⟨_, hc, _⟩ => nomatch hc
  | [], _ :: _, hlen, _, _, _ => nomatch hlen
  | _ :: _, [], hlen, _, _, _ => nomatch hlen
  | x :: xs, c :: cs, hlen, h01, hzero, hex => by
      cases Nat.decEq c 1 with
      | isTrue hc1 =>
          refine ⟨xs, Nat.lt_succ_self xs.length, fun y hy => ?_⟩
          rcases List.mem_cons.mp hy with rfl | hy'
          · refine ⟨cs, Nat.succ.inj hlen, fun d hd => h01 d (List.mem_cons_of_mem _ hd), ?_⟩
            rw [combineMasks_cons, ite_eq_left_of_eq_true _ _ (eq_true hc1)] at hzero
            have h := congrArg (y ^^^ ·) hzero
            rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.xor_zero] at h
            exact h
          · exact inSpanMasks_of_mem hy'
      | isFalse hc1 =>
          have hex' : ∃ d ∈ cs, d = 1 := by
            obtain ⟨d, hd, hd1⟩ := hex
            rcases List.mem_cons.mp hd with rfl | hd'
            · exact absurd hd1 hc1
            · exact ⟨d, hd', hd1⟩
          rw [combineMasks_cons, ite_eq_right_of_eq_false _ _ (eq_false hc1),
            Nat.zero_xor] at hzero
          obtain ⟨ys, hlt, hsp⟩ := exists_shorter_spanning_of_dep xs cs (Nat.succ.inj hlen)
            (fun d hd => h01 d (List.mem_cons_of_mem _ hd)) hzero hex'
          refine ⟨x :: ys, Nat.succ_lt_succ hlt, fun y hy => ?_⟩
          rcases List.mem_cons.mp hy with rfl | hy'
          · exact inSpanMasks_of_mem (List.mem_cons_self ..)
          · exact inSpanMasks_cons_zero (hsp y hy')

/-- A mask list has greedy rank equal to its length iff it is independent. -/
theorem rankBitmasks_eq_length_iff_indep (xs : List Nat) :
    rankBitmasks xs = xs.length ↔ independentMasks xs := by
  constructor
  · intro hrank cs hlen h01 hzero c hc
    rcases h01 c hc with h0 | h1
    · exact h0
    · obtain ⟨ys, hlt, hsp⟩ := exists_shorter_spanning_of_dep xs cs hlen h01 hzero ⟨c, hc, h1⟩
      have h1' := rankBitmasks_le_of_span hsp
      have h2' := rankBitmasks_le_length ys
      omega
  · exact rankBitmasks_of_indep

/-- Equality in the counting bound for `L-TANNER` holds iff the natural rows of
    each sector are independent (when the row counts fit in `n`). -/
theorem tannerState_k_eq_counting_iff (n : Nat) (LX LZ : List (List Bool))
    (viewsX viewsZ : List (List Nat))
    (hfit : viewsX.length * LX.length + viewsZ.length * LZ.length ≤ n) :
    stateK (tannerState n LX LZ viewsX viewsZ) =
        n - viewsX.length * LX.length - viewsZ.length * LZ.length ↔
      independentMasks (viewsX.flatMap (fun v =>
          LX.map (fun l => boolsToMask (tannerRow n v l)))) ∧
      independentMasks (viewsZ.flatMap (fun v =>
          LZ.map (fun l => boolsToMask (tannerRow n v l)))) := by
  constructor
  · intro heq
    rw [tannerState_k_closed] at heq
    have hX := rankBitmasks_le_length (viewsX.flatMap (fun v =>
      LX.map (fun l => boolsToMask (tannerRow n v l))))
    have hZ := rankBitmasks_le_length (viewsZ.flatMap (fun v =>
      LZ.map (fun l => boolsToMask (tannerRow n v l))))
    have hlX := length_flatMap_map (fun v l => boolsToMask (tannerRow n v l)) LX viewsX
    have hlZ := length_flatMap_map (fun v l => boolsToMask (tannerRow n v l)) LZ viewsZ
    rw [hlX] at hX
    rw [hlZ] at hZ
    exact ⟨(rankBitmasks_eq_length_iff_indep _).mp (by omega),
      (rankBitmasks_eq_length_iff_indep _).mp (by omega)⟩
  · rintro ⟨hX, hZ⟩
    exact tannerState_k_of_indep n LX LZ viewsX viewsZ hX hZ

/-- Equality in the counting bound for `L-TILE` holds iff the kept natural rows
    of each sector are independent (when the kept row counts fit in `n`). -/
theorem tileState_k_eq_counting_iff (tiles : List (Nat × List (List Nat) × List (List Nat)))
    (placements : List (Nat × List Nat)) (idents : List (Nat × Nat))
    (removed : List (Nat × Sector × Nat))
    (hfit : tileKeptRows tiles placements removed Sector.X +
      tileKeptRows tiles placements removed Sector.Z ≤ tileQubits placements idents) :
    stateK (tileState tiles placements idents removed) =
        tileQubits placements idents -
          tileKeptRows tiles placements removed Sector.X -
          tileKeptRows tiles placements removed Sector.Z ↔
      independentMasks ((List.range placements.length).flatMap (fun pos =>
          (tileRowIdxs tiles placements removed pos Sector.X).map (fun idx =>
            boolsToMask (tileRowVector tiles placements idents pos Sector.X idx)))) ∧
      independentMasks ((List.range placements.length).flatMap (fun pos =>
          (tileRowIdxs tiles placements removed pos Sector.Z).map (fun idx =>
            boolsToMask (tileRowVector tiles placements idents pos Sector.Z idx)))) := by
  constructor
  · intro heq
    rw [tileState_k_closed] at heq
    have hX := rankBitmasks_le_length ((List.range placements.length).flatMap (fun pos =>
      (tileRowIdxs tiles placements removed pos Sector.X).map (fun idx =>
        boolsToMask (tileRowVector tiles placements idents pos Sector.X idx))))
    have hZ := rankBitmasks_le_length ((List.range placements.length).flatMap (fun pos =>
      (tileRowIdxs tiles placements removed pos Sector.Z).map (fun idx =>
        boolsToMask (tileRowVector tiles placements idents pos Sector.Z idx))))
    have hlX := length_flatMap_map_dep (fun pos => tileRowIdxs tiles placements removed pos Sector.X)
      (fun pos idx => boolsToMask (tileRowVector tiles placements idents pos Sector.X idx))
      (List.range placements.length)
    have hlZ := length_flatMap_map_dep (fun pos => tileRowIdxs tiles placements removed pos Sector.Z)
      (fun pos idx => boolsToMask (tileRowVector tiles placements idents pos Sector.Z idx))
      (List.range placements.length)
    unfold tileKeptRows at hfit heq
    rw [hlX] at hX
    rw [hlZ] at hZ
    exact ⟨(rankBitmasks_eq_length_iff_indep _).mp (by omega),
      (rankBitmasks_eq_length_iff_indep _).mp (by omega)⟩
  · rintro ⟨hX, hZ⟩
    exact tileState_k_of_indep tiles placements idents removed hX hZ

/-! ## Local-code rank bound and disjoint-views closed form for `L-TANNER` -/

/-- Embeds a local row bitmask into global qubit positions along `view`. -/
def tannerEmbedMask : List Nat → Nat → Nat
  | [], _ => 0
  | q :: qs, m => sel (m.testBit 0) (2 ^ q) ^^^ tannerEmbedMask qs (m >>> 1)

theorem shiftRight_one_xor (a b : Nat) : (a ^^^ b) >>> 1 = (a >>> 1) ^^^ (b >>> 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_shiftRight, Nat.testBit_xor, Nat.testBit_xor,
    Nat.testBit_shiftRight, Nat.testBit_shiftRight]

theorem tannerEmbedMask_xor : ∀ (view : List Nat) (a b : Nat),
    tannerEmbedMask view (a ^^^ b) = tannerEmbedMask view a ^^^ tannerEmbedMask view b
  | [], _, _ => (Nat.xor_self 0).symm
  | q :: qs, a, b => by
      unfold tannerEmbedMask
      rw [Nat.testBit_xor, sel_xor_bool, shiftRight_one_xor, tannerEmbedMask_xor qs,
        xor_interchange]

theorem testBit_tannerEmbedMask_false_of_not_mem : ∀ (view : List Nat) (m i : Nat),
    i ∉ view → (tannerEmbedMask view m).testBit i = false
  | [], _, i, _ => Nat.zero_testBit i
  | q :: qs, m, i, hi => by
      have hne : q ≠ i := fun h => hi (h ▸ List.mem_cons_self ..)
      have hqs : i ∉ qs := fun h => hi (List.mem_cons_of_mem _ h)
      unfold tannerEmbedMask
      rw [Nat.testBit_xor, testBit_sel, Nat.testBit_two_pow, decide_eq_false hne,
        Bool.and_false, testBit_tannerEmbedMask_false_of_not_mem qs _ i hqs]
      rfl

theorem boolsToMask_cons_shiftRight (b : Bool) (bs : List Bool) :
    boolsToMask (b :: bs) >>> 1 = boolsToMask bs := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_shiftRight, Nat.add_comm, testBit_boolsToMask, testBit_boolsToMask]
  rfl

theorem nat_beq_eq_true (q : Nat) : (q == q) = true := Nat.beq_refl q

theorem nat_beq_eq_false {a b : Nat} (h : a ≠ b) : (a == b) = false := by
  cases heq : (a == b) with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true heq) h

theorem any_zip_false_of_not_mem : ∀ (view : List Nat) (l : List Bool) (i : Nat),
    i ∉ view → (view.zip l).any (fun p => p.1 == i && p.2) = false
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | q :: qs, b :: bs, i, hi => by
      have hne : q ≠ i := fun h => hi (h ▸ List.mem_cons_self ..)
      have hqs : i ∉ qs := fun h => hi (List.mem_cons_of_mem _ h)
      rw [List.zip_cons_cons, List.any_cons, nat_beq_eq_false hne, Bool.false_and,
        Bool.false_or]
      exact any_zip_false_of_not_mem qs bs i hqs

theorem testBit_tannerEmbedMask_boolsToMask (view : List Nat) (l : List Bool) (i : Nat)
    (hnd : view.Nodup) (hlen : l.length = view.length) :
    (tannerEmbedMask view (boolsToMask l)).testBit i =
      (view.zip l).any (fun p => p.1 == i && p.2) := by
  induction view generalizing l with
  | nil =>
      cases l with
      | nil => exact Nat.zero_testBit i
      | cons _ _ => exact absurd hlen (Nat.succ_ne_zero _)
  | cons q qs ih =>
      cases l with
      | nil => exact absurd hlen.symm (Nat.succ_ne_zero _)
      | cons b bs =>
          rw [List.nodup_cons] at hnd
          have ih' := ih bs hnd.2 (Nat.succ.inj hlen)
          unfold tannerEmbedMask
          rw [Nat.testBit_xor, testBit_sel, testBit_boolsToMask, boolsToMask_cons_shiftRight,
            Nat.testBit_two_pow, ih', List.zip_cons_cons, List.any_cons]
          show ((b && decide (q = i)) ^^ (qs.zip bs).any (fun p => p.1 == i && p.2)) =
            (((q == i) && b) || (qs.zip bs).any (fun p => p.1 == i && p.2))
          cases Nat.decEq q i with
          | isTrue hqi =>
              subst hqi
              rw [decide_eq_true rfl, nat_beq_eq_true q, Bool.and_true, Bool.true_and,
                any_zip_false_of_not_mem qs bs q hnd.1]
              cases b <;> rfl
          | isFalse hqi =>
              rw [decide_eq_false hqi, nat_beq_eq_false hqi, Bool.and_false,
                Bool.false_and, Bool.false_or]
              cases (qs.zip bs).any (fun p => p.1 == i && p.2) <;> rfl

/-- On a valid view and local row of matching length, `tannerRow` is the
    additive bitmask embedding `tannerEmbedMask`. -/
theorem boolsToMask_tannerRow (n : Nat) (view : List Nat) (l : List Bool)
    (hnd : view.Nodup) (hlt : ∀ q ∈ view, q < n) (hlen : l.length = view.length) :
    boolsToMask (tannerRow n view l) = tannerEmbedMask view (boolsToMask l) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_boolsToMask, testBit_tannerEmbedMask_boolsToMask view l i hnd hlen]
  unfold tannerRow
  cases Nat.lt_or_ge i n with
  | inl hi =>
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
      rfl
  | inr hge =>
      have hni : i ∉ view := fun hm => Nat.not_lt.mpr hge (hlt i hm)
      have hout : ((List.range n).map
          (fun q => (view.zip l).any (fun p => p.1 == q && p.2))).length ≤ i := by
        rw [List.length_map, List.length_range]
        exact hge
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hout,
        any_zip_false_of_not_mem view l i hni]
      rfl

/-- `tannerEmbedMask` is injective on bitmasks below `view.length` when
    `view` has no duplicates. -/
theorem eq_zero_of_tannerEmbedMask_eq_zero : ∀ (view : List Nat) (m : Nat),
    view.Nodup → Below view.length m → tannerEmbedMask view m = 0 → m = 0
  | [], m, _, hbelow, _ => eq_zero_of_below_zero hbelow
  | q :: qs, m, hnd, hbelow, hzero => by
      rw [List.nodup_cons] at hnd
      have hbitq : (tannerEmbedMask (q :: qs) m).testBit q = false := by
        rw [hzero]
        exact Nat.zero_testBit q
      unfold tannerEmbedMask at hbitq hzero
      rw [Nat.testBit_xor, testBit_sel, Nat.testBit_two_pow, decide_eq_true rfl,
        Bool.and_true, testBit_tannerEmbedMask_false_of_not_mem qs _ q hnd.1,
        Bool.xor_false] at hbitq
      rw [hbitq, sel_false, Nat.zero_xor] at hzero
      have hbelow' : Below qs.length (m >>> 1) := by
        intro j hj
        rw [Nat.testBit_shiftRight]
        exact hbelow (1 + j) (by rw [List.length_cons]; omega)
      have hshift : m >>> 1 = 0 :=
        eq_zero_of_tannerEmbedMask_eq_zero qs (m >>> 1) hnd.2 hbelow' hzero
      apply eq_zero_of_testBit
      intro j
      cases j with
      | zero => exact hbitq
      | succ j =>
          have hj : (m >>> 1).testBit j = false := by rw [hshift]; exact Nat.zero_testBit j
          rw [Nat.testBit_shiftRight, Nat.add_comm] at hj
          exact hj

/-- On a valid view, the global rank of one vertex's embedded local rows equals
    the local code's rank. -/
theorem rankBitmasks_tannerVertex (n : Nat) (view : List Nat) (L : List (List Bool))
    (hnd : view.Nodup) (hlt : ∀ q ∈ view, q < n)
    (hlen : ∀ l ∈ L, l.length = view.length) :
    rankBitmasks (L.map (fun l => boolsToMask (tannerRow n view l))) =
      rankBitmasks (L.map boolsToMask) := by
  have hmap : L.map (fun l => boolsToMask (tannerRow n view l)) =
      (L.map boolsToMask).map (tannerEmbedMask view) := by
    rw [List.map_map]
    exact List.map_congr_left (fun l hl =>
      boolsToMask_tannerRow n view l hnd hlt (hlen l hl))
  rw [hmap]
  apply rankBitmasks_map (tannerEmbedMask view) (tannerEmbedMask_xor view)
  intro a ha h0
  have hbelow : Below view.length a := below_of_inSpan (fun x hx => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    rw [← hlen l hl]
    exact below_boolsToMask l) ha
  exact eq_zero_of_tannerEmbedMask_eq_zero view a hnd hbelow h0

/-- Rank is subadditive across a `flatMap` with a per-element rank cap. -/
theorem rankBitmasks_flatMap_le {α : Type} (F : α → List Nat) (bound : Nat) :
    ∀ (L : List α), (∀ a ∈ L, rankBitmasks (F a) ≤ bound) →
    rankBitmasks (L.flatMap F) ≤ L.length * bound
  | [], _ => by
      rw [List.flatMap_nil, List.length_nil, Nat.zero_mul]
      exact Nat.zero_le _
  | a :: L, h => by
      rw [List.flatMap_cons, List.length_cons, Nat.succ_mul]
      have h1 := rankBitmasks_append_le (F a) (L.flatMap F)
      have h2 := h a (List.mem_cons_self ..)
      have h3 := rankBitmasks_flatMap_le F bound L (fun b hb => h b (List.mem_cons_of_mem _ hb))
      omega

/-- Rank is additive across a `flatMap` whose blocks live on pairwise disjoint
    bit sets. -/
theorem rankBitmasks_flatMap_of_disjoint {α : Type} (F : α → List Nat) (S : α → List Nat) :
    ∀ (L : List α),
    (∀ a ∈ L, ∀ x ∈ F a, ∀ i, i ∉ S a → x.testBit i = false) →
    L.Pairwise (fun a b => ∀ i ∈ S a, i ∉ S b) →
    rankBitmasks (L.flatMap F) = (L.map (fun a => rankBitmasks (F a))).sum
  | [], _, _ => rfl
  | a :: L, hsup, hdis => by
      rw [List.pairwise_cons] at hdis
      rw [List.flatMap_cons, List.map_cons, List.sum_cons]
      rw [rankBitmasks_append_of_disjoint]
      · rw [rankBitmasks_flatMap_of_disjoint F S L
          (fun b hb => hsup b (List.mem_cons_of_mem _ hb)) hdis.2]
      · intro x y hx hy hxy
        have heq : x = y := by
          have h := congrArg (· ^^^ y) hxy
          rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] at h
          exact h
        apply eq_zero_of_testBit
        intro i
        cases Decidable.em (i ∈ S a) with
        | inl hi =>
            rw [heq]
            apply testBit_false_of_inSpan _ hy
            intro z hz
            obtain ⟨b, hb, hzb⟩ := List.mem_flatMap.mp hz
            exact hsup b (List.mem_cons_of_mem _ hb) z hzb i (hdis.1 b hb i hi)
        | inr hi =>
            exact testBit_false_of_inSpan (fun z hz =>
              hsup a (List.mem_cons_self ..) z hz i hi) hx

theorem sum_map_const {α : Type} (c : Nat) : ∀ (L : List α),
    (L.map (fun _ => c)).sum = L.length * c
  | [] => by rw [List.map_nil, List.sum_nil, List.length_nil, Nat.zero_mul]
  | _ :: L => by
      rw [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul, sum_map_const c L]
      omega

theorem binaryMatrixTyped_row_length : ∀ (M : List (List Bool)),
    binaryMatrixTyped M = true → ∀ l ∈ M, l.length = matCols M
  | [], h => nomatch h
  | r :: rs, h => by
      unfold binaryMatrixTyped at h
      rw [Bool.and_eq_true] at h
      intro l hl
      rcases List.mem_cons.mp hl with rfl | hl'
      · rfl
      · exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp h.2 l hl')

theorem tannerTyped_unpack (n : Nat) (LX LZ : List (List Bool))
    (viewsX viewsZ : List (List Nat)) (hty : tannerTyped n LX LZ viewsX viewsZ = true) :
    (∀ l ∈ LX, l.length = matCols LX) ∧
    (∀ l ∈ LZ, l.length = matCols LZ) ∧
    (∀ v ∈ viewsX, v.length = matCols LX ∧ v.Nodup ∧ ∀ q ∈ v, q < n) ∧
    (∀ v ∈ viewsZ, v.length = matCols LZ ∧ v.Nodup ∧ ∀ q ∈ v, q < n) := by
  unfold tannerTyped at hty
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hty
  obtain ⟨⟨⟨⟨_, hLX⟩, hLZ⟩, hvX⟩, hvZ⟩ := hty
  refine ⟨binaryMatrixTyped_row_length LX hLX, binaryMatrixTyped_row_length LZ hLZ, ?_, ?_⟩
  · intro v hv
    have h := List.all_eq_true.mp hvX v hv
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    exact ⟨Nat.eq_of_beq_eq_true h.1.1, of_decide_eq_true h.1.2,
      fun q hq => of_decide_eq_true (List.all_eq_true.mp h.2 q hq)⟩
  · intro v hv
    have h := List.all_eq_true.mp hvZ v hv
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    exact ⟨Nat.eq_of_beq_eq_true h.1.1, of_decide_eq_true h.1.2,
      fun q hq => of_decide_eq_true (List.all_eq_true.mp h.2 q hq)⟩

/-- Local-code rank counting bound for `L-TANNER`: `k` is at least `n` minus
    `|viewsX| * rank(LX)` minus `|viewsZ| * rank(LZ)`. No weaker than
    `tannerState_k_ge`, and tighter when a sector with a view has redundant
    local checks. -/
theorem tannerState_k_ge_localRank (n : Nat) (LX LZ : List (List Bool))
    (viewsX viewsZ : List (List Nat)) (hty : tannerTyped n LX LZ viewsX viewsZ = true) :
    n ≤ stateK (tannerState n LX LZ viewsX viewsZ) +
      viewsX.length * rankBitmasks (LX.map boolsToMask) +
      viewsZ.length * rankBitmasks (LZ.map boolsToMask) := by
  obtain ⟨hLX, hLZ, hvX, hvZ⟩ := tannerTyped_unpack n LX LZ viewsX viewsZ hty
  rw [tannerState_k_closed]
  have hX : rankBitmasks (viewsX.flatMap (fun v =>
      LX.map (fun l => boolsToMask (tannerRow n v l)))) ≤
      viewsX.length * rankBitmasks (LX.map boolsToMask) := by
    apply rankBitmasks_flatMap_le
    intro v hv
    obtain ⟨hlen, hnd, hlt⟩ := hvX v hv
    rw [rankBitmasks_tannerVertex n v LX hnd hlt (fun l hl => (hLX l hl).trans hlen.symm)]
    exact Nat.le_refl _
  have hZ : rankBitmasks (viewsZ.flatMap (fun v =>
      LZ.map (fun l => boolsToMask (tannerRow n v l)))) ≤
      viewsZ.length * rankBitmasks (LZ.map boolsToMask) := by
    apply rankBitmasks_flatMap_le
    intro v hv
    obtain ⟨hlen, hnd, hlt⟩ := hvZ v hv
    rw [rankBitmasks_tannerVertex n v LZ hnd hlt (fun l hl => (hLZ l hl).trans hlen.symm)]
    exact Nat.le_refl _
  omega

theorem evalExpr_tanner_k_ge_localRank {n : Nat} {LX LZ : List (List Bool)}
    {viewsX viewsZ : List (List Nat)} {s : CodeState}
    (h : EvalExpr (StateExpr.tanner n LX LZ viewsX viewsZ) s) :
    n ≤ stateK s +
      viewsX.length * rankBitmasks (LX.map boolsToMask) +
      viewsZ.length * rankBitmasks (LZ.map boolsToMask) := by
  cases h with
  | tanner hty _ _ => exact tannerState_k_ge_localRank n LX LZ viewsX viewsZ hty

/-- Closed form for `k` of `L-TANNER` on vertex-disjoint views (in each sector):
    holds without a global independence hypothesis, even when `LX` or `LZ` has
    redundant local generators. -/
theorem tannerState_k_of_disjoint_views (n : Nat) (LX LZ : List (List Bool))
    (viewsX viewsZ : List (List Nat)) (hty : tannerTyped n LX LZ viewsX viewsZ = true)
    (hdisX : viewsX.Pairwise (fun u v => ∀ q ∈ u, q ∉ v))
    (hdisZ : viewsZ.Pairwise (fun u v => ∀ q ∈ u, q ∉ v)) :
    stateK (tannerState n LX LZ viewsX viewsZ) =
      n - viewsX.length * rankBitmasks (LX.map boolsToMask) -
        viewsZ.length * rankBitmasks (LZ.map boolsToMask) := by
  obtain ⟨hLX, hLZ, hvX, hvZ⟩ := tannerTyped_unpack n LX LZ viewsX viewsZ hty
  rw [tannerState_k_closed]
  have hX : rankBitmasks (viewsX.flatMap (fun v =>
      LX.map (fun l => boolsToMask (tannerRow n v l)))) =
      viewsX.length * rankBitmasks (LX.map boolsToMask) := by
    rw [rankBitmasks_flatMap_of_disjoint _ id viewsX (fun v hv x hx i hi => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
      obtain ⟨hlen, hnd, hlt⟩ := hvX v hv
      rw [boolsToMask_tannerRow n v l hnd hlt ((hLX l hl).trans hlen.symm)]
      exact testBit_tannerEmbedMask_false_of_not_mem v _ i hi) hdisX]
    have hcongr : viewsX.map (fun v => rankBitmasks
        (LX.map (fun l => boolsToMask (tannerRow n v l)))) =
        viewsX.map (fun _ => rankBitmasks (LX.map boolsToMask)) :=
      List.map_congr_left (fun v hv => by
        obtain ⟨hlen, hnd, hlt⟩ := hvX v hv
        exact rankBitmasks_tannerVertex n v LX hnd hlt (fun l hl => (hLX l hl).trans hlen.symm))
    rw [hcongr, sum_map_const]
  have hZ : rankBitmasks (viewsZ.flatMap (fun v =>
      LZ.map (fun l => boolsToMask (tannerRow n v l)))) =
      viewsZ.length * rankBitmasks (LZ.map boolsToMask) := by
    rw [rankBitmasks_flatMap_of_disjoint _ id viewsZ (fun v hv x hx i hi => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
      obtain ⟨hlen, hnd, hlt⟩ := hvZ v hv
      rw [boolsToMask_tannerRow n v l hnd hlt ((hLZ l hl).trans hlen.symm)]
      exact testBit_tannerEmbedMask_false_of_not_mem v _ i hi) hdisZ]
    have hcongr : viewsZ.map (fun v => rankBitmasks
        (LZ.map (fun l => boolsToMask (tannerRow n v l)))) =
        viewsZ.map (fun _ => rankBitmasks (LZ.map boolsToMask)) :=
      List.map_congr_left (fun v hv => by
        obtain ⟨hlen, hnd, hlt⟩ := hvZ v hv
        exact rankBitmasks_tannerVertex n v LZ hnd hlt (fun l hl => (hLZ l hl).trans hlen.symm))
    rw [hcongr, sum_map_const]
  rw [hX, hZ]

theorem evalExpr_tanner_k_of_disjoint_views {n : Nat} {LX LZ : List (List Bool)}
    {viewsX viewsZ : List (List Nat)} {s : CodeState}
    (h : EvalExpr (StateExpr.tanner n LX LZ viewsX viewsZ) s)
    (hdisX : viewsX.Pairwise (fun u v => ∀ q ∈ u, q ∉ v))
    (hdisZ : viewsZ.Pairwise (fun u v => ∀ q ∈ u, q ∉ v)) :
    stateK s =
      n - viewsX.length * rankBitmasks (LX.map boolsToMask) -
        viewsZ.length * rankBitmasks (LZ.map boolsToMask) := by
  cases h with
  | tanner hty _ _ => exact tannerState_k_of_disjoint_views n LX LZ viewsX viewsZ hty hdisX hdisZ

/-! ## Formal no-go theorems for `L-TANNER` and `L-TILE`

Two valid, commuting `L-TANNER` evaluations with identical `(n, LX, LZ,
|viewsX|, |viewsZ|)` (and distinct, repeat-free views) yield different `stateK`
values (`0` vs `1`), and likewise two valid, commuting `L-TILE` evaluations
with identical `(tiles, tileQubits, |placements|, tileKeptRows X, tileKeptRows Z)`
yield `0` vs `1`. Thus no function of `(n, LX, LZ, |viewsX|, |viewsZ|)` equals
`stateK` across all valid `L-TANNER` evaluations, and no function of
`(tiles, tileQubits, |placements|, tileKeptRows X, tileKeptRows Z)` equals
`stateK` across all valid `L-TILE` evaluations (closed forms in richer
invariants of the views or placements, such as their intersection pattern,
are not excluded). -/

/-- No function of `(n, LX, LZ, |viewsX|, |viewsZ|)` equals `stateK` on all
    valid `L-TANNER` evaluations. -/
theorem tanner_k_not_determined_by_params :
    ¬ ∃ f : Nat → List (List Bool) → List (List Bool) → Nat → Nat → Nat,
      ∀ n LX LZ viewsX viewsZ s,
        EvalExpr (StateExpr.tanner n LX LZ viewsX viewsZ) s →
        stateK s = f n LX LZ viewsX.length viewsZ.length := by
  rintro ⟨f, hf⟩
  let LX : List (List Bool) := [[true, true]]
  let LZ : List (List Bool) := [[true, true, true, true]]
  let vX1 : List (List Nat) := [[0, 1], [1, 2], [2, 3]]
  let vX2 : List (List Nat) := [[0, 1], [1, 2], [0, 2]]
  let vZ : List (List Nat) := [[0, 1, 2, 3]]
  have h1 : EvalExpr (StateExpr.tanner 4 LX LZ vX1 vZ) (tannerState 4 LX LZ vX1 vZ) :=
    EvalExpr.tanner (by decide) (by decide) (by decide)
  have h2 : EvalExpr (StateExpr.tanner 4 LX LZ vX2 vZ) (tannerState 4 LX LZ vX2 vZ) :=
    EvalExpr.tanner (by decide) (by decide) (by decide)
  have hk1 : stateK (tannerState 4 LX LZ vX1 vZ) = 0 := by decide
  have hk2 : stateK (tannerState 4 LX LZ vX2 vZ) = 1 := by decide
  have e1 := hf 4 LX LZ vX1 vZ _ h1
  have e2 := hf 4 LX LZ vX2 vZ _ h2
  rw [hk1] at e1
  rw [hk2] at e2
  have hlen : vX1.length = vX2.length := rfl
  rw [hlen] at e1
  exact absurd (e1.trans e2.symm) (by decide)

/-- No function of `(tiles, tileQubits, |placements|, tileKeptRows X,
    tileKeptRows Z)` equals `stateK` on all valid `L-TILE` evaluations. -/
theorem tile_k_not_determined_by_params :
    ¬ ∃ f : List (Nat × List (List Nat) × List (List Nat)) → Nat → Nat → Nat → Nat → Nat,
      ∀ tiles placements idents removed s,
        EvalExpr (StateExpr.tile tiles placements idents removed) s →
        stateK s = f tiles (tileQubits placements idents) placements.length
          (tileKeptRows tiles placements removed Sector.X)
          (tileKeptRows tiles placements removed Sector.Z) := by
  rintro ⟨f, hf⟩
  let tiles : List (Nat × List (List Nat) × List (List Nat)) :=
    [(2, [[0, 1]], []), (4, [], [[0, 1, 2, 3]])]
  let pl1 : List (Nat × List Nat) :=
    [(0, [0, 1]), (0, [1, 2]), (0, [2, 3]), (1, [0, 1, 2, 3])]
  let pl2 : List (Nat × List Nat) :=
    [(0, [0, 1]), (0, [1, 2]), (0, [0, 2]), (1, [0, 1, 2, 3])]
  have h1 : EvalExpr (StateExpr.tile tiles pl1 [] []) (tileState tiles pl1 [] []) :=
    EvalExpr.tile (by decide) (by decide) (by decide)
  have h2 : EvalExpr (StateExpr.tile tiles pl2 [] []) (tileState tiles pl2 [] []) :=
    EvalExpr.tile (by decide) (by decide) (by decide)
  have hk1 : stateK (tileState tiles pl1 [] []) = 0 := by decide
  have hk2 : stateK (tileState tiles pl2 [] []) = 1 := by decide
  have hq : tileQubits pl1 [] = tileQubits pl2 [] := by decide
  have hX : tileKeptRows tiles pl1 [] Sector.X = tileKeptRows tiles pl2 [] Sector.X := by decide
  have hZ : tileKeptRows tiles pl1 [] Sector.Z = tileKeptRows tiles pl2 [] Sector.Z := by decide
  have e1 := hf tiles pl1 [] [] _ h1
  have e2 := hf tiles pl2 [] [] _ h2
  rw [hk1, hq, hX, hZ] at e1
  rw [hk2] at e2
  have hlen : pl1.length = pl2.length := rfl
  rw [hlen] at e1
  exact absurd (e1.trans e2.symm) (by decide)

end CodeCalculus
