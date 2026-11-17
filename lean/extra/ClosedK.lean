import CodeCalculus.Constructors
import CodeCalculus.ConstructorWellFormedness
import CodeCalculus.ConstructorOrthogonality
import CodeCalculus.Eval
import CodeCalculus.ConstructorRank
import CodeCalculus.ConstructorRankTyped

/-!
# Closed forms for `stateK` of the typed constructors (issue #483)

Non-audited module (lives in `lean/extra/`): the statements are exposed
here, and they rest on axioms.
Each statement is the Lean counterpart of the hand derivation in
`spec/OPERATIONAL_SEMANTICS.md` §4.34 / §4.35.

`L-HGP` is derived from the two rank axioms `hgp_rankX` and `hgp_rankZ`,
which are not proved. `A-PRODUCT` is derived from the two rank axioms
`product_rankX` and `product_rankZ`, which are not proved. The arithmetic
that combines the ranks is proved (`hgp_arith`, `product_arith`,
issue #424). The other three named by issue #483 are proved in the audited
modules, with no axiom: `L-GROUP-ALGEBRA` (`twoblockState_k_closed`),
`A-DOUBLE` with the empty wiring (`doubleState_empty_k`), and `A-CONCAT`
(`concatState_k_closed`, `ConcatRetention.lean`, issue #505).

`k_i` and `k_iᵀ` are written below as `n_i - rank(H_i)` and
`m_i - rank(H_i)` respectively, matching `hypergraph_parameters` in
`machine/constructors.py`.
-/

namespace CodeCalculus

axiom hgp_rankX (H1 H2 : List (List Bool))
    (h1 : binaryMatrixTyped H1 = true) (h2 : binaryMatrixTyped H2 = true) :
    rankBitmasks ((indexPairs (H1.length) (matCols H2)).map
      (fun aj => boolsToMask (hgpXVector H1 H2 aj))) =
      H1.length * matCols H2 -
        (H1.length - rankBitmasks (H1.map boolsToMask)) *
          (matCols H2 - rankBitmasks (H2.map boolsToMask))

axiom hgp_rankZ (H1 H2 : List (List Bool))
    (h1 : binaryMatrixTyped H1 = true) (h2 : binaryMatrixTyped H2 = true) :
    rankBitmasks ((indexPairs (matCols H1) (H2.length)).map
      (fun ib => boolsToMask (hgpZVector H1 H2 ib))) =
      matCols H1 * H2.length -
        (matCols H1 - rankBitmasks (H1.map boolsToMask)) *
          (H2.length - rankBitmasks (H2.map boolsToMask))

/-- The rows of a typed binary matrix all have the length of the first. -/
theorem length_of_binaryMatrixTyped {H : List (List Bool)} (h : binaryMatrixTyped H = true) :
    ∀ r ∈ H, r.length = matCols H := by
  cases H with
  | nil => exact nomatch h
  | cons r0 rs =>
      intro r hr
      show r.length = r0.length
      unfold binaryMatrixTyped at h
      rw [Bool.and_eq_true] at h
      rcases List.mem_cons.mp hr with rfl | hr'
      · rfl
      · exact Nat.eq_of_beq_eq_true (List.all_eq_true.mp h.2 r hr')

/-- The rank of a typed binary matrix is at most its number of columns. -/
theorem rank_le_matCols {H : List (List Bool)} (h : binaryMatrixTyped H = true) :
    rankBitmasks (H.map boolsToMask) ≤ matCols H := by
  apply rankBitmasks_le_of_high_bits_false
  intro m hm j hj
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
  rw [testBit_boolsToMask, List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (by rw [length_of_binaryMatrixTyped h r hr]; exact hj)]
  rfl

/-- The rank of a matrix is at most its number of rows. -/
theorem rank_le_rows (H : List (List Bool)) :
    rankBitmasks (H.map boolsToMask) ≤ H.length := by
  have h := rankBitmasks_le_length (H.map boolsToMask)
  rw [List.length_map] at h
  exact h

/-- The arithmetic of the `L-HGP` closed form, for ranks bounded by the
    numbers of rows and columns. -/
theorem hgp_arith_nat (m1 n1 m2 n2 r1 r2 : Nat) (h1 : r1 ≤ m1) (h2 : r1 ≤ n1)
    (h3 : r2 ≤ m2) (h4 : r2 ≤ n2) :
    (n1 * n2 + m1 * m2) - (m1 * n2 - (m1 - r1) * (n2 - r2)) -
        (n1 * m2 - (n1 - r1) * (m2 - r2)) =
      (n1 - r1) * (n2 - r2) + (m1 - r1) * (m2 - r2) := by
  obtain ⟨a1, rfl⟩ := Nat.exists_eq_add_of_le h1
  obtain ⟨b1, rfl⟩ := Nat.exists_eq_add_of_le h2
  obtain ⟨a2, rfl⟩ := Nat.exists_eq_add_of_le h3
  obtain ⟨b2, rfl⟩ := Nat.exists_eq_add_of_le h4
  simp only [Nat.add_sub_cancel_left, Nat.add_mul, Nat.mul_add]
  omega

/-- The arithmetic that turns the two rank identities above into the closed
    form. -/
theorem hgp_arith (H1 H2 : List (List Bool))
    (h1 : binaryMatrixTyped H1 = true) (h2 : binaryMatrixTyped H2 = true) :
    (matCols H1 * matCols H2 + H1.length * H2.length) -
      (H1.length * matCols H2 -
        (H1.length - rankBitmasks (H1.map boolsToMask)) *
          (matCols H2 - rankBitmasks (H2.map boolsToMask))) -
      (matCols H1 * H2.length -
        (matCols H1 - rankBitmasks (H1.map boolsToMask)) *
          (H2.length - rankBitmasks (H2.map boolsToMask))) =
    (matCols H1 - rankBitmasks (H1.map boolsToMask)) *
      (matCols H2 - rankBitmasks (H2.map boolsToMask)) +
    (H1.length - rankBitmasks (H1.map boolsToMask)) *
      (H2.length - rankBitmasks (H2.map boolsToMask)) :=
  hgp_arith_nat _ _ _ _ _ _ (rank_le_rows H1) (rank_le_matCols h1) (rank_le_rows H2)
    (rank_le_matCols h2)

theorem hgpState_k_closed (H1 H2 : List (List Bool))
    (h1 : binaryMatrixTyped H1 = true) (h2 : binaryMatrixTyped H2 = true) :
    stateK (hgpState H1 H2) =
      (matCols H1 - rankBitmasks (H1.map boolsToMask)) *
        (matCols H2 - rankBitmasks (H2.map boolsToMask)) +
      (H1.length - rankBitmasks (H1.map boolsToMask)) *
        (H2.length - rankBitmasks (H2.map boolsToMask)) := by
  unfold hgpState
  rw [stateK_constructedState (hgpQubits H1 H2) (hgpVectors H1 H2)]
  have hX : naturalMasks (hgpQubits H1 H2) (hgpVectors H1 H2) Sector.X =
      (indexPairs (H1.length) (matCols H2)).map
        (fun aj => boolsToMask (hgpXVector H1 H2 aj)) := by
    unfold hgpVectors
    have := naturalMasks_XZ (hgpQubits H1 H2)
      (fun aj => hgpXVector H1 H2 aj) (fun ib => hgpZVector H1 H2 ib)
      (indexPairs H1.length (matCols H2)) (indexPairs (matCols H1) (H2.length))
    rcases this with ⟨hX, _⟩
    have hpt : ∀ aj, vecMask (hgpQubits H1 H2) (hgpXVector H1 H2 aj) =
        boolsToMask (hgpXVector H1 H2 aj) := by
      intro aj; exact vecMask_eq_boolsToMask (hgpQubits H1 H2) (hgpXVector H1 H2 aj)
        (length_hgpXVector H1 H2 aj)
    rw [hX]
    exact List.map_congr_left (fun aj _ => hpt aj)
  have hZ : naturalMasks (hgpQubits H1 H2) (hgpVectors H1 H2) Sector.Z =
      (indexPairs (matCols H1) (H2.length)).map
        (fun ib => boolsToMask (hgpZVector H1 H2 ib)) := by
    unfold hgpVectors
    have := naturalMasks_XZ (hgpQubits H1 H2)
      (fun aj => hgpXVector H1 H2 aj) (fun ib => hgpZVector H1 H2 ib)
      (indexPairs H1.length (matCols H2)) (indexPairs (matCols H1) (H2.length))
    rcases this with ⟨_, hZ⟩
    have hpt : ∀ ib, vecMask (hgpQubits H1 H2) (hgpZVector H1 H2 ib) =
        boolsToMask (hgpZVector H1 H2 ib) := by
      intro ib; exact vecMask_eq_boolsToMask (hgpQubits H1 H2) (hgpZVector H1 H2 ib)
        (length_hgpZVector H1 H2 ib)
    rw [hZ]
    exact List.map_congr_left (fun ib _ => hpt ib)
  rw [hX, hZ]
  rw [hgp_rankX H1 H2 h1 h2, hgp_rankZ H1 H2 h1 h2]
  exact hgp_arith H1 H2 h1 h2

theorem evalExpr_hgp_k {H1 H2 : List (List Bool)} {s : CodeState}
    (h : EvalExpr (StateExpr.hgp H1 H2) s) :
    stateK s =
      (matCols H1 - rankBitmasks (H1.map boolsToMask)) *
        (matCols H2 - rankBitmasks (H2.map boolsToMask)) +
      (H1.length - rankBitmasks (H1.map boolsToMask)) *
        (H2.length - rankBitmasks (H2.map boolsToMask)) := by
  cases h with
  | hgp h1 h2 _ => exact hgpState_k_closed H1 H2 h1 h2

/-! ## `A-PRODUCT` -/

/-- Rank of the `X`-sector of the natural rows of `A-PRODUCT`, as a
    function of the factors' qubit counts and displayed row counts. -/
axiom product_rankX (A B : CodeState)
    (hA : EncodingWellFormed A) (hB : EncodingWellFormed B) :
    rankBitmasks (naturalMasks (productQubits A B) (productVectors A B) Sector.X) =
      A.Q.length * (sectorRows B Sector.X).length +
      (sectorRows A Sector.X).length * B.Q.length -
      (sectorRows A Sector.X).length * (sectorRows B Sector.X).length

/-- Rank of the `Z`-sector of the natural rows of `A-PRODUCT`. -/
axiom product_rankZ (A B : CodeState)
    (hA : EncodingWellFormed A) (hB : EncodingWellFormed B) :
    rankBitmasks (naturalMasks (productQubits A B) (productVectors A B) Sector.Z) =
      A.Q.length * (sectorRows B Sector.Z).length +
      (sectorRows A Sector.Z).length * B.Q.length -
      (sectorRows A Sector.Z).length * (sectorRows B Sector.Z).length

/-- On a well-formed state the displayed rows of the two sectors number at
    most the qubits. -/
theorem rows_le_qubits (s : CodeState) (hwf : EncodingWellFormed s) :
    (sectorRows s Sector.X).length + (sectorRows s Sector.Z).length ≤ s.Q.length := by
  have hfit := ranksFit_of_wf s hwf
  obtain ⟨hQ, hids, _, _, _, _, _, hI2⟩ := hwf
  unfold RanksFit at hfit
  rw [sectorRank_eq_length_of_I2 s hQ hids hI2 Sector.X,
    sectorRank_eq_length_of_I2 s hQ hids hI2 Sector.Z] at hfit
  exact hfit

/-- The arithmetic of the `A-PRODUCT` closed form, for row counts bounded
    by the qubit counts. -/
theorem product_arith_nat (nA xA zA nB xB zB : Nat) (hA : xA + zA ≤ nA)
    (hB : xB + zB ≤ nB) :
    zA * xB + nA * nB + xA * zB - (nA * xB + xA * nB - xA * xB) -
        (nA * zB + zA * nB - zA * zB) =
      (nA - xA - zA) * (nB - xB - zB) := by
  obtain ⟨kA, rfl⟩ := Nat.exists_eq_add_of_le hA
  obtain ⟨kB, rfl⟩ := Nat.exists_eq_add_of_le hB
  have eA : xA + zA + kA - xA - zA = kA := by omega
  have eB : xB + zB + kB - xB - zB = kB := by omega
  rw [eA, eB]
  simp only [Nat.add_mul, Nat.mul_add]
  omega

/-- The arithmetic that turns the two rank identities above into
    `k_prod = k_A * k_B`. -/
theorem product_arith (A B : CodeState)
    (hA : EncodingWellFormed A) (hB : EncodingWellFormed B) :
    (sectorRows A Sector.Z).length * (sectorRows B Sector.X).length +
      A.Q.length * B.Q.length +
      (sectorRows A Sector.X).length * (sectorRows B Sector.Z).length -
    (A.Q.length * (sectorRows B Sector.X).length +
      (sectorRows A Sector.X).length * B.Q.length -
      (sectorRows A Sector.X).length * (sectorRows B Sector.X).length) -
    (A.Q.length * (sectorRows B Sector.Z).length +
      (sectorRows A Sector.Z).length * B.Q.length -
      (sectorRows A Sector.Z).length * (sectorRows B Sector.Z).length) =
    stateK A * stateK B := by
  rw [stateK_of_wf A hA, stateK_of_wf B hB]
  exact product_arith_nat _ _ _ _ _ _ (rows_le_qubits A hA) (rows_le_qubits B hB)

/-- Closed form for the logical count of the CSS tensor product. -/
theorem productState_k_closed (A B : CodeState)
    (hA : EncodingWellFormed A) (hB : EncodingWellFormed B) :
    stateK (productState A B) = stateK A * stateK B := by
  unfold productState
  rw [stateK_constructedState]
  rw [product_rankX A B hA hB, product_rankZ A B hA hB]
  unfold productQubits sectorMatrix
  simp only [List.length_map]
  exact product_arith A B hA hB

theorem evalExpr_product_k {eA eB : StateExpr} {s : CodeState}
    (h : EvalExpr (StateExpr.product eA eB) s) :
    ∃ sA sB, EvalExpr eA sA ∧ EvalExpr eB sB ∧
      stateK s = stateK sA * stateK sB := by
  cases h with
  | product hAwf hBwf _ hEvalA hEvalB =>
      exact ⟨_, _, hEvalA, hEvalB, productState_k_closed _ _ hAwf hBwf⟩

end CodeCalculus
