import CodeCalculus.ExactPeel
import CodeCalculus.ExactGraft

namespace CodeCalculus

/-!
# Duality adjunctions and sector-swap conjugation (issue #518, Candidate A)

This module mechanizes the two components of Candidate A from the
category-theoretic and duality disposition (issue #518;
`design/DUALITY_AND_METATHEORY.md` §2; `design/DERIVED_RELATIONS.md` §2b)
without introducing a category-theory library (`spec/GATES.md` §11):

1. **The classical `puncture ⊣ shorten` Galois connections and the dual-code
   identity `P_i(C)^⊥ = S_i(C^⊥)`.** On predicates `CodePred := List Bool → Prop`
   ordered by length-indexed inclusion `CodeSub n`, zero-extension `zeroExtend i`
   is left adjoint to coordinate shortening `shorten i` (`zeroExtend_adj_shorten`),
   and coordinate puncturing `puncture i` is left adjoint to drop-pullback
   `pullDrop i` (`puncture_adj_pullDrop`). The orthogonal complement `dualCode n`
   is an antitone Galois connection on `CodeSub n` (`sub_dualCode_iff_symm`), and
   the bilinear transpose `dotPar_insertAt_false` (`⟨ι_i u, v⟩ = ⟨u, π_i v⟩`)
   intertwines the two pairs to yield the pointwise duality identity
   `dualCode_puncture_iff_shorten_dualCode` (`P_i(C)^⊥ = S_i(C^⊥)`) and its
   dual inclusion `puncture_dualCode_sub_dualCode_shorten` (`P_i(C^⊥) ⊆ S_i(C)^⊥`).
2. **The sector-swap involution `H^{⊗ Q}` (`swapState`) and the transition
   conjugation law `H(m_σ(C)) = m_{σ̄}(H(C))`.** `swapState` and `swapCommand`
   are involutions (`swapState_involutive`, `swapCommand_involutive`), and
   `swapState` conjugates every kernel and Gate 6 state update (`deleteState`,
   `addState`, `peelState`, `punctureState`, `hadamardState`, `graftState`,
   `rebaseState`, `extendState`, `directSumState`, `glueState`) into its
   opposite-sector mirror.
-/

/-! ## 1. Classical puncture/shorten adjunctions and `P_i(C)^⊥ = S_i(C^⊥)` -/

/-- A predicate on boolean vectors representing a subset/subspace of `F_2^n`. -/
abbrev CodePred : Type := List Bool → Prop

/-- Length-indexed inclusion of vector predicates on `F_2^n`. -/
def CodeSub (n : Nat) (C D : CodePred) : Prop :=
  ∀ v, v.length = n → C v → D v

/-- Zero-extension `ι_i(D)` from `F_2^{n-1}` into `F_2^n`: vectors vanishing at `i`
    whose `i`-th coordinate restriction lies in `D`. -/
def zeroExtend (i : Nat) (D : CodePred) : CodePred :=
  fun v => entryAt i v = false ∧ D (dropAt i v)

/-- Coordinate shortening `S_i(C)` from `F_2^n` to `F_2^{n-1}`: preimage of `C`
    under `insertAt i false`. -/
def shorten (i : Nat) (C : CodePred) : CodePred :=
  fun u => C (insertAt i false u)

/-- Coordinate puncturing `P_i(C)` from `F_2^n` to `F_2^{n-1}`: direct image of
    `C` under `dropAt i`. -/
def puncture (i : Nat) (C : CodePred) : CodePred :=
  fun u => ∃ v, v.length = u.length + 1 ∧ C v ∧ u = dropAt i v

/-- Preimage `π_i^{-1}(D)` of `D` under `dropAt i`. -/
def pullDrop (i : Nat) (D : CodePred) : CodePred :=
  fun v => D (dropAt i v)

/-- Orthogonal complement `C^⊥` in `F_2^n` with respect to `dotPar · · % 2 = 0`. -/
def dualCode (n : Nat) (C : CodePred) : CodePred :=
  fun w => w.length = n ∧ ∀ v, v.length = n → C v → dotPar w v % 2 = 0

/-- Galois connection `zeroExtend i ⊣ shorten i` between `(CodePred, CodeSub (n-1))`
    and `(CodePred, CodeSub n)`. -/
theorem zeroExtend_adj_shorten {n i : Nat} (hi : i < n) (D C : CodePred) :
    CodeSub n (zeroExtend i D) C ↔ CodeSub (n - 1) D (shorten i C) := by
  constructor
  · intro h u hu hDu
    unfold shorten
    have hiu : i ≤ u.length := by omega
    have hlen : (insertAt i false u).length = n := by
      rw [length_insertAt i false u hiu]
      omega
    apply h (insertAt i false u) hlen
    exact ⟨entryAt_insertAt i false u hiu, by rw [dropAt_insertAt i false u hiu]; exact hDu⟩
  · intro h v hv ⟨hent, hdrop⟩
    have hiv : i < v.length := by omega
    have hlen : (dropAt i v).length = n - 1 := by
      rw [length_dropAt i v hiv, hv]
    have hsh := h (dropAt i v) hlen hdrop
    unfold shorten at hsh
    have hins : insertAt i false (dropAt i v) = v := by
      rw [← hent]
      exact insertAt_entryAt_dropAt i v hiv
    rwa [hins] at hsh

/-- Unit of `zeroExtend i ⊣ shorten i`: `D ⊆ S_i(ι_i(D))`. -/
theorem zeroExtend_shorten_unit {n i : Nat} (hi : i < n) (D : CodePred) :
    CodeSub (n - 1) D (shorten i (zeroExtend i D)) :=
  (zeroExtend_adj_shorten hi D (zeroExtend i D)).mp (fun _ _ h => h)

/-- Counit of `zeroExtend i ⊣ shorten i`: `ι_i(S_i(C)) ⊆ C`. -/
theorem zeroExtend_shorten_counit {n i : Nat} (hi : i < n) (C : CodePred) :
    CodeSub n (zeroExtend i (shorten i C)) C :=
  (zeroExtend_adj_shorten hi (shorten i C) C).mpr (fun _ _ h => h)

/-- Galois connection `puncture i ⊣ pullDrop i` between `(CodePred, CodeSub n)`
    and `(CodePred, CodeSub (n-1))`. -/
theorem puncture_adj_pullDrop {n i : Nat} (hi : i < n) (C D : CodePred) :
    CodeSub (n - 1) (puncture i C) D ↔ CodeSub n C (pullDrop i D) := by
  constructor
  · intro h v hv hCv
    unfold pullDrop
    have hiv : i < v.length := by omega
    have hlen : (dropAt i v).length = n - 1 := by
      rw [length_dropAt i v hiv, hv]
    apply h (dropAt i v) hlen
    exact ⟨v, by omega, hCv, rfl⟩
  · intro h u hu ⟨v, hvl, hCv, hdrop⟩
    have hv : v.length = n := by omega
    have hp := h v hv hCv
    unfold pullDrop at hp
    rwa [← hdrop] at hp

/-- Unit of `puncture i ⊣ pullDrop i`: `C ⊆ π_i^{-1}(P_i(C))`. -/
theorem puncture_pullDrop_unit {n i : Nat} (hi : i < n) (C : CodePred) :
    CodeSub n C (pullDrop i (puncture i C)) :=
  (puncture_adj_pullDrop hi C (puncture i C)).mp (fun _ _ h => h)

/-- Counit of `puncture i ⊣ pullDrop i`: `P_i(π_i^{-1}(D)) ⊆ D`. -/
theorem puncture_pullDrop_counit {n i : Nat} (hi : i < n) (D : CodePred) :
    CodeSub (n - 1) (puncture i (pullDrop i D)) D :=
  (puncture_adj_pullDrop hi (pullDrop i D) D).mpr (fun _ _ h => h)

/-- Orthogonal complement is antitone on `CodeSub n`. -/
theorem dualCode_antitone (n : Nat) {C D : CodePred} (h : CodeSub n C D) :
    CodeSub n (dualCode n D) (dualCode n C) := by
  intro w _ ⟨hw, hperp⟩
  exact ⟨hw, fun v hv hCv => hperp v hv (h v hv hCv)⟩

/-- `(-)^⊥` is a symmetric antitone Galois connection on `CodeSub n`. -/
theorem sub_dualCode_iff_symm (n : Nat) (C D : CodePred) :
    CodeSub n C (dualCode n D) ↔ CodeSub n D (dualCode n C) := by
  constructor <;> (
    intro h v hv hDv
    refine ⟨hv, fun u hu hCu => ?_⟩
    rw [dotPar_comm]
    exact (h u hu hCu).2 v hv hDv)

/-- Double-dual inflation `C ⊆ (C^⊥)^⊥`. -/
theorem le_double_dualCode (n : Nat) (C : CodePred) :
    CodeSub n C (dualCode n (dualCode n C)) :=
  (sub_dualCode_iff_symm n C (dualCode n C)).mpr (fun _ _ h => h)

/-- **The classical puncture-shorten duality identity**: `P_i(C)^⊥ = S_i(C^⊥)`
    on `(n-1)`-bit vectors (`design/DUALITY_AND_METATHEORY.md` §2.1). -/
theorem dualCode_puncture_iff_shorten_dualCode {n i : Nat} (hi : i < n)
    (C : CodePred) {u : List Bool} (hu : u.length = n - 1) :
    dualCode (n - 1) (puncture i C) u ↔ shorten i (dualCode n C) u := by
  have hiu : i ≤ u.length := by omega
  have hlen_ins : (insertAt i false u).length = n := by
    rw [length_insertAt i false u hiu]
    omega
  constructor
  · intro ⟨_, hperp⟩
    unfold shorten dualCode
    refine ⟨hlen_ins, fun v hv hCv => ?_⟩
    have hiv : i < v.length := by omega
    rw [dotPar_insertAt_false i u v hiu hiv]
    have hdrop_len : (dropAt i v).length = n - 1 := by
      rw [length_dropAt i v hiv, hv]
    exact hperp (dropAt i v) hdrop_len ⟨v, by omega, hCv, rfl⟩
  · intro ⟨_, hperp⟩
    unfold dualCode
    refine ⟨hu, fun w hw ⟨v, hvl, hCv, hdrop⟩ => ?_⟩
    have hv : v.length = n := by omega
    have hiv : i < v.length := by omega
    rw [hdrop, ← dotPar_insertAt_false i u v hiu hiv]
    exact hperp v hv hCv

/-- Dual inclusion `P_i(C^⊥) ⊆ S_i(C)^⊥` (the constructive direction of
    `S_i(C)^⊥ = P_i(C^⊥)`). -/
theorem puncture_dualCode_sub_dualCode_shorten {n i : Nat} (hi : i < n) (C : CodePred) :
    CodeSub (n - 1) (puncture i (dualCode n C)) (dualCode (n - 1) (shorten i C)) := by
  intro u hu ⟨w, hwl, ⟨_, hwperp⟩, hdrop⟩
  have hw : w.length = n := by omega
  have hiw : i < w.length := by omega
  refine ⟨hu, fun z hz hSz => ?_⟩
  unfold shorten at hSz
  have hiz : i ≤ z.length := by omega
  have hins_len : (insertAt i false z).length = n := by
    rw [length_insertAt i false z hiz]
    omega
  rw [hdrop, dotPar_comm, ← dotPar_insertAt_false i z w hiz hiw, dotPar_comm]
  exact hwperp (insertAt i false z) hins_len hSz

/-- The row-space predicate of a displayed row list on namespace `Q`. -/
def spanCode (Q : List Nat) (rows : List Row) : CodePred :=
  fun v => v.length = Q.length ∧ inSpanRows Q rows v

/-- A vector `v` of length `|Q|` commutes with every displayed row in `rows` iff
    it lies in `dualCode |Q| (spanCode Q rows)`. -/
theorem mem_dualCode_rowVectors {Q : List Nat} {rows : List Row} {v : List Bool}
    (hv : v.length = Q.length) :
    (∀ r ∈ rows, dotPar v (rowVector Q r) % 2 = 0) →
    (∀ r ∈ rows, dualCode Q.length (fun w => w = rowVector Q r) v) := by
  intro h r hr
  refine ⟨hv, fun w _ hw => ?_⟩
  rw [hw]
  exact h r hr

/-! ## 2. Sector-swap involution `H^{⊗ Q}` and conjugation `H(m_σ(C)) = m_{σ̄}(H(C))` -/

/-- `swapRow` is an involution. -/
theorem swapRow_involutive (r : Row) : swapRow (swapRow r) = r := by
  cases r
  simp [swapRow, oppositeSector_involutive]

/-- `swapState` (`E-LOCAL-HADAMARD` at `T = Q`) is an involution on `CodeState`. -/
theorem swapState_involutive (s : CodeState) : swapState (swapState s) = s := by
  cases s with
  | mk Q rows used =>
    simp only [swapState, List.map_map]
    congr 1
    have hfun : (swapRow ∘ swapRow) = id := funext swapRow_involutive
    rw [hfun, List.map_id]

/-- Mirror every sector parameter in a command (`m_σ ↦ m_{σ̄}`). -/
def swapCommand : Command → Command
  | Command.skip => Command.skip
  | Command.seq m1 m2 => Command.seq (swapCommand m1) (swapCommand m2)
  | Command.delete r => Command.delete r
  | Command.addStab τ supp => Command.addStab (oppositeSector τ) supp
  | Command.graft q τ ids => Command.graft q (oppositeSector τ) ids
  | Command.rebase τ M => Command.rebase (oppositeSector τ) M
  | Command.hadamard T => Command.hadamard T
  | Command.peel q τ r_id => Command.peel q (oppositeSector τ) r_id
  | Command.puncture q => Command.puncture q
  | Command.extend delta adds =>
      Command.extend delta (adds.map (fun p => (oppositeSector p.1, p.2)))

/-- `swapCommand` is an involution on `Command`. -/
theorem swapCommand_involutive : ∀ (m : Command), swapCommand (swapCommand m) = m
  | Command.skip => rfl
  | Command.seq m1 m2 => by
      simp [swapCommand, swapCommand_involutive m1, swapCommand_involutive m2]
  | Command.delete _ => rfl
  | Command.addStab τ _ => by simp [swapCommand, oppositeSector_involutive]
  | Command.graft _ τ _ => by simp [swapCommand, oppositeSector_involutive]
  | Command.rebase τ _ => by simp [swapCommand, oppositeSector_involutive]
  | Command.hadamard _ => rfl
  | Command.peel _ τ _ => by simp [swapCommand, oppositeSector_involutive]
  | Command.puncture _ => rfl
  | Command.extend delta adds => by
      simp only [swapCommand, List.map_map]
      congr 1
      have hfun : ((fun p : Sector × List Nat => (oppositeSector p.1, p.2)) ∘
          (fun p : Sector × List Nat => (oppositeSector p.1, p.2))) = id := by
        funext ⟨τ, supp⟩
        simp [oppositeSector_involutive]
      rw [hfun, List.map_id]

/-- Conjugation for `C-DELETE-CHECK`: `H(delete(C, r)) = delete(H(C), r)`. -/
theorem swapState_deleteState (s : CodeState) (r : Nat) :
    swapState (deleteState s r) = deleteState (swapState s) r := by
  simp only [swapState, deleteState]
  congr 1
  rw [List.filter_map]
  rfl

/-- Conjugation for `C-ADD-CHECK`: `H(add_τ(C, supp)) = add_{τ̄}(H(C), supp)`. -/
theorem swapState_addState (s : CodeState) (τ : Sector) (supp : List Nat) :
    swapState (addState s τ supp) = addState (swapState s) (oppositeSector τ) supp := by
  simp [swapState, addState, swapRow]

/-- Conjugation for `C-DIRECT-SUM`: `H(A ⊕ B) = H(A) ⊕ H(B)`. -/
theorem swapState_directSumState (a b : CodeState) :
    swapState (directSumState a b) = directSumState (swapState a) (swapState b) := by
  simp [swapState, directSumState]

/-- Helper for zipping sector-swapped seam or extension records with minted IDs. -/
private theorem map_swapRow_zip_records (f : List Nat → List Nat) :
    ∀ (xs : List (Sector × List Nat)) (ys : List Nat),
      ((xs.zip ys).map (fun (si, id) =>
        ({ id := id, sector := si.1, support := f si.2 } : Row))).map swapRow =
      ((xs.map (fun p => (oppositeSector p.1, p.2))).zip ys).map
        (fun (si, id) => ({ id := id, sector := si.1, support := f si.2 } : Row))
  | [], _ => rfl
  | _ :: _, [] => rfl
  | (τ, supp) :: xs, id :: ys => by
      simp only [List.map_cons, List.zip_cons_cons, swapRow]
      exact congrArg
        (({ id := id, sector := oppositeSector τ, support := f supp } : Row) :: ·)
        (map_swapRow_zip_records f xs ys)

/-- Conjugation for `E-GLUE`: `H(glue(A, B, seams)) = glue(H(A), H(B), swap(seams))`. -/
theorem swapState_glueState (a b : CodeState) (seams : List (Sector × List Nat)) :
    swapState (glueState a b seams) =
      glueState (swapState a) (swapState b)
        (seams.map (fun p => (oppositeSector p.1, p.2))) := by
  simp only [swapState, glueState, List.length_map, List.map_append]
  rw [map_swapRow_zip_records (fun x => x) seams]

/-- `shortenRow` and `swapRow` commute. -/
theorem swapRow_shortenRow (q : Nat) (r : Row) :
    swapRow (shortenRow q r) = shortenRow q (swapRow r) := by
  unfold shortenRow swapRow
  split <;> rfl

/-- Conjugation for `E-PEEL`: `H(peel(C, q, r_id)) = peel(H(C), q, r_id)`. -/
theorem swapState_peelState (s : CodeState) (q r_id : Nat) :
    swapState (peelState s q r_id) = peelState (swapState s) q r_id := by
  simp only [swapState, peelState, List.map_map, List.filter_map]
  congr 1
  have hfun : (swapRow ∘ shortenRow q) = (shortenRow q ∘ swapRow) :=
    funext (swapRow_shortenRow q)
  rw [hfun]
  rfl

/-- Conjugation for `E-PUNCTURE`: `H(puncture(C, q)) = puncture(H(C), q)`. -/
theorem swapState_punctureState (s : CodeState) (q : Nat) :
    swapState (punctureState s q) = punctureState (swapState s) q := by
  simp only [swapState, punctureState, List.filter_map]
  rfl

/-- Conjugation for `E-LOCAL-HADAMARD`: `H(hadamard(C, T)) = hadamard(H(C), T)`. -/
theorem swapState_hadamardState (s : CodeState) (T : List Nat) :
    swapState (hadamardState s T) = hadamardState (swapState s) T := by
  unfold hadamardState
  split <;> rfl

private theorem foldl_xorList_map_swapRow :
    ∀ (rs : List Row) (ks : List Nat) (acc : List Nat),
      ((rs.map swapRow).zip ks).foldl
        (fun a (r, c) => if c = 1 then xorList a r.support else a) acc =
      (rs.zip ks).foldl
        (fun a (r, c) => if c = 1 then xorList a r.support else a) acc
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | r :: rs, k :: ks, acc => by
      simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons, swapRow]
      exact foldl_xorList_map_swapRow rs ks _

/-- `mixSupport` ignores the sector label of the ordered rows. -/
theorem mixSupport_map_swapRow (ordered : List Row) (cs : List Nat) :
    mixSupport (ordered.map swapRow) cs = mixSupport ordered cs := by
  unfold mixSupport
  rw [foldl_xorList_map_swapRow]

/-- Conjugation for `P-REBASE`: `H(rebase_τ(C, M)) = rebase_{τ̄}(H(C), M)`. -/
theorem swapState_rebaseState (s : CodeState) (τ : Sector) (M : List (List Nat)) :
    swapState (rebaseState s τ M) = rebaseState (swapState s) (oppositeSector τ) M := by
  have hneq : ∀ (r : Row), (decide (r.sector ≠ τ)) =
      (decide ((swapRow r).sector ≠ oppositeSector τ)) := by
    intro ⟨_, sec, _⟩
    cases sec <;> cases τ <;> rfl
  have hfilt : (s.rows.filter (fun r => r.sector ≠ τ)).map swapRow =
      (s.rows.map swapRow).filter (fun r => r.sector ≠ oppositeSector τ) := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro r _
    exact hneq r
  have hmint : (rebaseMintedRows s τ M).map swapRow =
      rebaseMintedRows (swapState s) (oppositeSector τ) M := by
    unfold rebaseMintedRows
    have hused : (swapState s).used = s.used := rfl
    rw [hused, sectorRows_swapState s (oppositeSector τ), oppositeSector_involutive,
      List.map_map]
    apply List.map_congr_left
    intro ⟨cs, id⟩ _
    simp [swapRow, mixSupport_map_swapRow]
  apply GlobalHadamard.codeState_ext
  · rfl
  · show ((s.rows.filter (fun r => r.sector ≠ τ)) ++ rebaseMintedRows s τ M).map swapRow =
      ((s.rows.map swapRow).filter (fun r => r.sector ≠ oppositeSector τ)) ++
        rebaseMintedRows (swapState s) (oppositeSector τ) M
    rw [List.map_append, hfilt, hmint]
  · rfl

/-- Conjugation for `E-EXTEND`: `H(extend(C, Δ, adds)) = extend(H(C), Δ, swap(adds))`. -/
theorem swapState_extendState (s : CodeState) (delta : List Nat)
    (adds : List (Sector × List Nat)) :
    swapState (extendState s delta adds) =
      extendState (swapState s) delta (adds.map (fun p => (oppositeSector p.1, p.2))) := by
  simp only [swapState, extendState, extendMintedRows, List.length_map, List.map_append]
  rw [map_swapRow_zip_records sortNat adds]

/-- `rowById` commutes with `swapState`. -/
theorem rowById_swapState (s : CodeState) (id : Nat) :
    rowById (swapState s) id = (rowById s id).map swapRow := by
  unfold rowById swapState
  induction s.rows with
  | nil => rfl
  | cons r rs ih =>
      simp only [List.map_cons, List.find?_cons]
      have hid : (swapRow r).id = r.id := rfl
      rw [hid]
      split
      · rfl
      · exact ih

private theorem zip_drop_map_swapRow :
    ∀ (cs : List Row),
      List.zip (cs.map swapRow) ((cs.map swapRow).drop 1) =
      (List.zip cs (cs.drop 1)).map (fun p => (swapRow p.1, swapRow p.2))
  | [] => rfl
  | [_] => rfl
  | a :: b :: cs => by
      show (swapRow a, swapRow b) :: List.zip ((b :: cs).map swapRow) (((b :: cs).map swapRow).drop 1) =
        (swapRow a, swapRow b) :: (List.zip (b :: cs) ((b :: cs).drop 1)).map (fun p => (swapRow p.1, swapRow p.2))
      rw [zip_drop_map_swapRow (b :: cs)]

private theorem map_swapRow_graftMinted (τ : Sector) (remQ : List Nat) :
    ∀ (ps : List (Row × Row)) (mids : List Nat),
      ((ps.zip mids).map (fun (pair, id) =>
        ({ id := id
         , sector := τ
         , support := sortNat (remQ.filter (fun qa =>
             pair.1.support.contains qa ≠ pair.2.support.contains qa)) } : Row))).map swapRow =
      ((ps.map (fun p => (swapRow p.1, swapRow p.2))).zip mids).map (fun (pair, id) =>
        ({ id := id
         , sector := oppositeSector τ
         , support := sortNat (remQ.filter (fun qa =>
             pair.1.support.contains qa ≠ pair.2.support.contains qa)) } : Row))
  | [], _ => rfl
  | _ :: _, [] => rfl
  | (r1, r2) :: ps, id :: mids => by
      simp only [List.map_cons, List.zip_cons_cons, swapRow]
      exact congrArg
        (({ id := id
          , sector := oppositeSector τ
          , support := sortNat (remQ.filter (fun qa =>
              r1.support.contains qa ≠ r2.support.contains qa)) } : Row) :: ·)
        (map_swapRow_graftMinted τ remQ ps mids)

private theorem swapRow_graftShorten_cond (q : Nat) (τ : Sector) (r : Row) :
    swapRow (if r.sector = oppositeSector τ ∧ r.support.contains q then shortenRow q r else r) =
    if (swapRow r).sector = oppositeSector (oppositeSector τ) ∧ (swapRow r).support.contains q then
      shortenRow q (swapRow r)
    else swapRow r := by
  rcases r with ⟨id, sec, supp⟩
  cases sec <;> cases τ <;> (
    by_cases hq : q ∈ supp <;>
    simp [swapRow, oppositeSector, shortenRow, hq])

/-- Conjugation for `E-GRAFT`: `H(graft(C, q, τ, ids)) = graft(H(C), q, τ̄, ids)`. -/
theorem swapState_graftState (s : CodeState) (q : Nat) (τ : Sector) (ids : List Nat) :
    swapState (graftState s q τ ids) =
      graftState (swapState s) q (oppositeSector τ) ids := by
  have hchain : ids.filterMap (rowById (swapState s)) =
      (ids.filterMap (rowById s)).map swapRow := by
    induction ids with
    | nil => rfl
    | cons i is ih =>
        simp only [List.filterMap_cons, rowById_swapState]
        cases rowById s i with
        | none => exact ih
        | some r => simp [ih]
  have hnonChain : ((swapState s).rows).filter (fun r => ¬ ids.contains r.id) =
      (s.rows.filter (fun r => ¬ ids.contains r.id)).map swapRow := by
    show (s.rows.map swapRow).filter (fun r => ¬ ids.contains r.id) = _
    rw [List.filter_map]
    rfl
  have hshort : ∀ (rs : List Row),
      (rs.map (fun r =>
        if r.sector = oppositeSector τ ∧ r.support.contains q then
          shortenRow q r
        else r)).map swapRow =
      (rs.map swapRow).map (fun r =>
        if r.sector = oppositeSector (oppositeSector τ) ∧ r.support.contains q then
          shortenRow q r
        else r) := by
    intro rs
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro r _
    exact swapRow_graftShorten_cond q τ r
  apply GlobalHadamard.codeState_ext
  · rfl
  · show ((graftState s q τ ids).rows).map swapRow =
      (graftState (swapState s) q (oppositeSector τ) ids).rows
    dsimp only [graftState]
    have hused : (swapState s).used = s.used := rfl
    have hQ : (swapState s).Q = s.Q := rfl
    rw [hused, hQ, List.map_append, hchain, hnonChain, hshort,
      zip_drop_map_swapRow, map_swapRow_graftMinted]
  · rfl

end CodeCalculus
