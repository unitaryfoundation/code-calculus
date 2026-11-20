import CodeCalculus.BalancedOverlap

/-!
# `k` of `L-BALANCED`, `L-TANNER`, and `L-TILE` from the natural matrices

`spec/OPERATIONAL_SEMANTICS.md` §4.35 claims no closed form for the `k` of
these three constructors: it is the rank bookkeeping of the output. This
module states that bookkeeping against the inputs. For each constructor,
`k` is `n` minus the rank of the matrix of natural `X`-rows minus the rank
of the matrix of natural `Z`-rows, the two matrices being written out as
lists of row masks. The statements hold for every input, with no typing
premise, because they are instances of `stateK_constructedState`.

These are not formulas in the parameters of the inputs, and the names
ending in `_k_closed` follow the established naming only.
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

end CodeCalculus
