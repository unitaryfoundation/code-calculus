import CodeCalculus.ChoiceFree
import CodeCalculus.State
import CodeCalculus.Term
import CodeCalculus.Constructors
import CodeCalculus.CayleyTables
import CodeCalculus.WellFormedBool

namespace CodeCalculus

/-- Disjointness of two lists. -/
def DisjointList {α : Type} [DecidableEq α] (xs ys : List α) : Prop :=
  ∀ x, x ∈ xs → x ∉ ys

/-- `DisjointList` is a bounded universal over the first list. -/
instance (xs ys : List Nat) : Decidable (DisjointList xs ys) :=
  inferInstanceAs (Decidable (∀ x, x ∈ xs → x ∉ ys))

def mintFresh (used : List Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => canonicalMint used :: mintFresh (used ++ [canonicalMint used]) n

/-- Capacity premise (H-4, decided 2026-10-31): every identifier
    the canonical mint produces for `n` fresh rows over `used` lies in the
    finite enumeration of `spec/STATE_MODEL.md` I3 (`totalIdentifiers` names).
    A transition that would mint past the enumeration has no derivation,
    matching the Python consumer's refusal at exhaustion. -/
def MintsWithinCapacity (used : List Nat) (n : Nat) : Prop :=
  ∀ id ∈ mintFresh used n, id < totalIdentifiers

instance (used : List Nat) (n : Nat) : Decidable (MintsWithinCapacity used n) :=
  inferInstanceAs (Decidable (∀ id ∈ mintFresh used n, id < totalIdentifiers))

/-- The state produced by `E-GLUE`: disjoint factor rows followed by one
    canonically minted seam-check row per supplied seam, over the union of the
    factors' namespaces and used sets. -/
def glueState (a b : CodeState) (seams : List (Sector × List Nat)) : CodeState :=
  let used0 := a.used ++ b.used
  let ids := mintFresh used0 seams.length
  let seamRows := (seams.zip ids).map (fun (si, id) =>
    ({ id := id, sector := si.1, support := si.2 } : Row))
  { Q := a.Q ++ b.Q
  , rows := a.rows ++ b.rows ++ seamRows
  , used := used0 ++ ids }


/-- The state produced by a direct sum, once its disjointness premises hold. -/
def directSumState (a b : CodeState) : CodeState :=
  { Q := a.Q ++ b.Q
  , rows := a.rows ++ b.rows
  , used := a.used ++ b.used }

/-- Evaluation of state expressions. -/
inductive EvalExpr : StateExpr → CodeState → Prop where
  | base (s : CodeState) : EvalExpr (StateExpr.base s) s
  | directSum {e1 e2 : StateExpr} {s1 s2 : CodeState}
      (hQ : @DisjointList Nat _ s1.Q s2.Q)
      (hU : @DisjointList Nat _ s1.used s2.used) :
      EvalExpr e1 s1 → EvalExpr e2 s2 →
      EvalExpr (StateExpr.directSum e1 e2) (directSumState s1 s2)
  /-- `E-GLUE`: binary transition combining two disjoint factor states with
      seam checks; well-formedness of the glued state is the joint premise. -/
  | glue {e1 e2 : StateExpr} {s1 s2 : CodeState}
      {seams : List (Sector × List Nat)}
      (hQ : @DisjointList Nat _ s1.Q s2.Q)
      (hU : @DisjointList Nat _ s1.used s2.used)
      (hwf : EncodingWellFormed (glueState s1 s2 seams))
      (hcap : MintsWithinCapacity (s1.used ++ s2.used) seams.length) :
      EvalExpr e1 s1 → EvalExpr e2 s2 →
      EvalExpr (StateExpr.glue e1 e2 seams) (glueState s1 s2 seams)
  /-- `L-HGP`: every well-typed pair of binary matrices evaluates; the
      capacity premise bounds the identifiers minted from the empty used set. -/
  | hgp {H1 H2 : List (List Bool)}
      (h1 : binaryMatrixTyped H1 = true) (h2 : binaryMatrixTyped H2 = true)
      (hcap : MintsWithinCapacity [] (hgpState H1 H2).rows.length) :
      EvalExpr (StateExpr.hgp H1 H2) (hgpState H1 H2)
  /-- `L-LIFTED`. -/
  | lift {orders : List Nat} {A B : List (List (List (List Nat)))}
      (hG : groupTyped orders = true)
      (hA : algMatrixTyped orders A = true) (hB : algMatrixTyped orders B = true)
      (hcap : MintsWithinCapacity [] (liftState orders A B).rows.length) :
      EvalExpr (StateExpr.lift orders A B) (liftState orders A B)
  /-- `L-GROUP-ALGEBRA`. -/
  | twoblock {orders : List Nat} {a b : List (List Nat)}
      (hG : groupTyped orders = true)
      (ha : algElementTyped orders a = true) (hb : algElementTyped orders b = true)
      (hcap : MintsWithinCapacity [] (twoblockState orders a b).rows.length) :
      EvalExpr (StateExpr.twoblock orders a b) (twoblockState orders a b)
  /-- `A-CONCAT`: both factors evaluate to well-formed states, and the block
      list and the representatives are typed against them (`concatTyped`). -/
  | concat {eO eI : StateExpr} {sO sI : CodeState} {blocks repsX repsZ : List (List Nat)}
      (hO : EncodingWellFormed sO) (hI : EncodingWellFormed sI)
      (hty : concatTyped sO sI blocks repsX repsZ = true)
      (hcap : MintsWithinCapacity [] (concatState sO sI blocks repsX repsZ).rows.length) :
      EvalExpr eO sO → EvalExpr eI sI →
      EvalExpr (StateExpr.concat eO eI blocks repsX repsZ)
        (concatState sO sI blocks repsX repsZ)
  /-- `A-PRODUCT`: every pair of well-formed factors evaluates. -/
  | product {eA eB : StateExpr} {sA sB : CodeState}
      (hA : EncodingWellFormed sA) (hB : EncodingWellFormed sB)
      (hcap : MintsWithinCapacity [] (productState sA sB).rows.length) :
      EvalExpr eA sA → EvalExpr eB sB →
      EvalExpr (StateExpr.product eA eB) (productState sA sB)
  /-- `A-DOUBLE`: a well-formed factor, a typed wiring, and natural rows of
      the two sectors with pairwise even overlap. -/
  | double {e : StateExpr} {sC : CodeState} {wiring : List (Nat × List Nat)} {conj : Bool}
      (hC : EncodingWellFormed sC)
      (hty : doubleTyped sC wiring = true)
      (hcomm : naturalCommuteBool (naturalRows (doubleQubits sC)
        (doubleVectors sC wiring conj)) = true)
      (hcap : MintsWithinCapacity [] (doubleState sC wiring conj).rows.length) :
      EvalExpr e sC →
      EvalExpr (StateExpr.double e wiring conj) (doubleState sC wiring conj)
  /-- `L-BALANCED`: every well-typed input evaluates. -/
  | balanced {orders : List Nat} {H1 H2 : List (List Bool)}
      {rows1 cols1 rows2 cols2 : List (List Nat)}
      (hty : balancedTyped orders H1 rows1 cols1 H2 rows2 cols2 = true)
      (hcap : MintsWithinCapacity []
        (balancedState orders H1 rows1 cols1 H2 rows2 cols2).rows.length) :
      EvalExpr (StateExpr.balanced orders H1 rows1 cols1 H2 rows2 cols2)
        (balancedState orders H1 rows1 cols1 H2 rows2 cols2)
  /-- `L-TANNER`: well-typed inputs whose natural rows of the two sectors
      have pairwise even overlap. -/
  | tanner {n : Nat} {LX LZ : List (List Bool)} {viewsX viewsZ : List (List Nat)}
      (hty : tannerTyped n LX LZ viewsX viewsZ = true)
      (hcomm : naturalCommuteBool (naturalRows n
        (tannerVectors n LX LZ viewsX viewsZ)) = true)
      (hcap : MintsWithinCapacity [] (tannerState n LX LZ viewsX viewsZ).rows.length) :
      EvalExpr (StateExpr.tanner n LX LZ viewsX viewsZ) (tannerState n LX LZ viewsX viewsZ)
  /-- `L-TILE`: a well-typed assembly whose natural rows of the two sectors
      have pairwise even overlap. -/
  | tile {tiles : List (Nat × List (List Nat) × List (List Nat))}
      {placements : List (Nat × List Nat)} {idents : List (Nat × Nat)}
      {removed : List (Nat × Sector × Nat)}
      (hty : tileTyped tiles placements idents removed = true)
      (hcomm : naturalCommuteBool (naturalRows (tileQubits placements idents)
        (tileVectors tiles placements idents removed)) = true)
      (hcap : MintsWithinCapacity []
        (tileState tiles placements idents removed).rows.length) :
      EvalExpr (StateExpr.tile tiles placements idents removed)
        (tileState tiles placements idents removed)
  /-- `L-NESTED-CSS`: two parity-check matrices with equally many columns
      whose rows have pairwise even overlap across the two matrices. -/
  | nested {HX HZ : List (List Bool)}
      (hty : nestedTyped HX HZ = true)
      (hcomm : naturalCommuteBool (naturalRows (matCols HX)
        (nestedVectors HX HZ)) = true)
      (hcap : MintsWithinCapacity [] (nestedState HX HZ).rows.length) :
      EvalExpr (StateExpr.nested HX HZ) (nestedState HX HZ)
  | cone {DA DB F1 F0 : List (List Bool)}
      (hty : coneTyped DA DB F1 F0 = true)
      (hcomm : naturalCommuteBool (naturalRows (coneN DA DB F1 F0)
        (coneVectors DA DB F1 F0)) = true)
      (hcap : MintsWithinCapacity [] (coneState DA DB F1 F0).rows.length) :
      EvalExpr (StateExpr.cone DA DB F1 F0) (coneState DA DB F1 F0)
  /-- `L-EMPTY`: the nullary empty CSS code. -/
  | empty : EvalExpr StateExpr.empty emptyCodeState
  /-- `L-FREE`: the check-free CSS code on a finite qubit-label set. -/
  | free {qs : List Nat}
      (hty : freeTyped qs = true) :
      EvalExpr (StateExpr.free qs) (freeState qs)
  /-- `A-PULLBACK`: fiber product of two well-formed CSS states over an
      interface along CSS code morphisms whose pulled-back rows commute. -/
  | pullback {e1 e2 eI : StateExpr} {s1 s2 sI : CodeState}
      {phi1 phi2 : List (Nat × Nat)}
      (h1 : EncodingWellFormed s1) (h2 : EncodingWellFormed s2)
      (hI : EncodingWellFormed sI)
      (hty : pullbackTyped s1 s2 sI phi1 phi2 = true)
      (hm1 : cssMorphismBool s1 sI phi1 = true)
      (hm2 : cssMorphismBool s2 sI phi2 = true)
      (hcomm : naturalCommuteBool (naturalRows (pullbackPairs s1 s2 phi1 phi2).length
        (pullbackVectors s1 s2 phi1 phi2)) = true)
      (hcap : MintsWithinCapacity [] (pullbackState s1 s2 phi1 phi2).rows.length) :
      EvalExpr e1 s1 → EvalExpr e2 s2 → EvalExpr eI sI →
      EvalExpr (StateExpr.pullback e1 e2 eI phi1 phi2) (pullbackState s1 s2 phi1 phi2)
  /-- `A-PUSHOUT`: amalgamated sum of two well-formed CSS states along a
      shared subcode via CSS code morphisms whose pushed-forward rows commute. -/
  | pushout {e1 e2 eS : StateExpr} {s1 s2 sS : CodeState}
      {psi1 psi2 : List (Nat × Nat)}
      (h1 : EncodingWellFormed s1) (h2 : EncodingWellFormed s2)
      (hS : EncodingWellFormed sS)
      (hty : pushoutTyped s1 s2 sS psi1 psi2 = true)
      (hm1 : cssMorphismBool sS s1 psi1 = true)
      (hm2 : cssMorphismBool sS s2 psi2 = true)
      (hcomm : naturalCommuteBool (naturalRows (pushoutClasses s1 s2 sS psi1 psi2).length
        (pushoutVectors s1 s2 sS psi1 psi2)) = true)
      (hcap : MintsWithinCapacity [] (pushoutState s1 s2 sS psi1 psi2).rows.length) :
      EvalExpr e1 s1 → EvalExpr e2 s2 → EvalExpr eS sS →
      EvalExpr (StateExpr.pushout e1 e2 eS psi1 psi2) (pushoutState s1 s2 sS psi1 psi2)
  /-- `L-LIFTED` over a group given by its multiplication table: every
      well-typed table and pair of matrices evaluates. -/
  | liftTable {t : List (List Nat)} {A B : List (List (List Nat))}
      (hG : tableGroupTyped t = true)
      (hA : tableMatrixTyped t A = true) (hB : tableMatrixTyped t B = true)
      (hcap : MintsWithinCapacity [] (tableLiftState t A B).rows.length) :
      EvalExpr (StateExpr.liftTable t A B) (tableLiftState t A B)
  /-- `L-GROUP-ALGEBRA` over a group given by its multiplication table. -/
  | twoblockTable {t : List (List Nat)} {a b : List Nat}
      (hG : tableGroupTyped t = true)
      (ha : tableElementTyped t a = true) (hb : tableElementTyped t b = true)
      (hcap : MintsWithinCapacity [] (tableTwoblockState t a b).rows.length) :
      EvalExpr (StateExpr.twoblockTable t a b) (tableTwoblockState t a b)
  /-- `L-BALANCED` over a group given by its multiplication table: every
      well-typed input evaluates. -/
  | balancedTable {t : List (List Nat)} {H1 H2 : List (List Bool)}
      {rows1 cols1 rows2 cols2 : List (List Nat)}
      (hty : tableBalancedTyped t H1 rows1 cols1 H2 rows2 cols2 = true)
      (hcap : MintsWithinCapacity []
        (tableBalancedState t H1 rows1 cols1 H2 rows2 cols2).rows.length) :
      EvalExpr (StateExpr.balancedTable t H1 rows1 cols1 H2 rows2 cols2)
        (tableBalancedState t H1 rows1 cols1 H2 rows2 cols2)
  /-- `L-PAIR-PARTITION`: paired affine/circulant permutation blocks over lift
      size `p` whose natural rows have pairwise even overlap. -/
  | pairPartition {p : Nat} {BX BZ : List (List (Nat × Nat))}
      (hty : pairPartitionTyped p BX BZ = true)
      (hcomm : naturalCommuteBool (naturalRows (pairPartitionQubits p BX)
        (pairPartitionVectors p BX BZ)) = true)
      (hcap : MintsWithinCapacity [] (pairPartitionState p BX BZ).rows.length) :
      EvalExpr (StateExpr.pairPartition p BX BZ) (pairPartitionState p BX BZ)
  /-- `PP-SCALE`: explicit extension of a well-formed PP-presented CSS state
      to target lift size `P ≥ 2` with `k' > 0` and commuting generated rows. -/
  | ppScale {e0 : StateExpr} {s0 : CodeState} {P : Nat}
      {BX BZ : List (List (Nat × Nat))}
      (h0 : EncodingWellFormed s0)
      (hty : ppScaleTyped s0 P BX BZ = true)
      (hcomm : naturalCommuteBool (naturalRows (pairPartitionQubits P BX)
        (pairPartitionVectors P BX BZ)) = true)
      (hcap : MintsWithinCapacity s0.used (ppScaleState s0 P BX BZ).rows.length) :
      EvalExpr e0 s0 →
      EvalExpr (StateExpr.ppScale e0 P BX BZ) (ppScaleState s0 P BX BZ)


/-- A displayed generator is one whose identifier names a live row. -/
def DisplayedGenerator (r : Nat) (s : CodeState) : Prop :=
  ∃ row, row ∈ s.rows ∧ row.id = r

/-- State update for deletion; `used` unchanged. -/
def deleteState (s : CodeState) (r : Nat) : CodeState :=
  { Q := s.Q
  , rows := s.rows.filter (fun row => row.id ≠ r)
  , used := s.used }

/-- Iterated deletion: `deleteState` over a list of row identifiers.
    This is the state update of `E-SPLIT` (`Command.split`). -/
def deleteAll (s : CodeState) : List Nat → CodeState
  | [] => s
  | r :: rest => deleteAll (deleteState s r) rest

theorem deleteAll_Q (R : List Nat) : ∀ s : CodeState, (deleteAll s R).Q = s.Q := by
  induction R with
  | nil => intro s; rfl
  | cons r rest ih => intro s; exact ih (deleteState s r)

theorem deleteAll_used (R : List Nat) : ∀ s : CodeState, (deleteAll s R).used = s.used := by
  induction R with
  | nil => intro s; rfl
  | cons r rest ih => intro s; exact ih (deleteState s r)

/-- A row is displayed after `deleteAll` exactly when it was displayed
    before and its identifier is not among those deleted. -/
theorem mem_deleteAll_rows (R : List Nat) :
    ∀ (s : CodeState) (row : Row),
      row ∈ (deleteAll s R).rows ↔ row ∈ s.rows ∧ row.id ∉ R := by
  induction R with
  | nil =>
      intro s row
      exact ⟨fun h => ⟨h, fun hmem => nomatch hmem⟩, fun h => h.1⟩
  | cons r rest ih =>
      intro s row
      show row ∈ (deleteAll (deleteState s r) rest).rows ↔ _
      rw [ih (deleteState s r) row]
      show (row ∈ s.rows.filter (fun row => row.id ≠ r) ∧ row.id ∉ rest) ↔ _
      rw [List.mem_filter]
      constructor
      · rintro ⟨⟨hmem, hne⟩, hrest⟩
        refine ⟨hmem, fun hin => ?_⟩
        rcases List.mem_cons.mp hin with h | h
        · exact (of_decide_eq_true hne) h
        · exact hrest h
      · rintro ⟨hmem, hnot⟩
        exact ⟨⟨hmem, decide_eq_true (fun h => hnot (h ▸ List.mem_cons_self))⟩,
          fun h => hnot (List.mem_cons_of_mem _ h)⟩

/-- `deleteAll` preserves the relative order of surviving rows. -/
theorem deleteAll_rows_sublist (R : List Nat) :
    ∀ s : CodeState, (deleteAll s R).rows.Sublist s.rows := by
  induction R with
  | nil => intro s; exact List.Sublist.refl _
  | cons r rest ih =>
      intro s
      exact (ih (deleteState s r)).trans List.filter_sublist

/-- Every displayed row lies inside `QA` or misses it: no row meets both
    sides of the partition of the qubits into `QA` and the rest. -/
def Separated (QA : List Nat) (s : CodeState) : Prop :=
  ∀ row ∈ s.rows, (∀ q ∈ row.support, q ∈ QA) ∨ (∀ q ∈ row.support, q ∉ QA)

/-- The sector opposite to the given one. -/
def oppositeSector : Sector → Sector
  | Sector.X => Sector.Z
  | Sector.Z => Sector.X

/-- The sector swap is an involution -/
theorem oppositeSector_involutive (sec : Sector) :
    oppositeSector (oppositeSector sec) = sec := by
  cases sec <;> rfl


/-- Support subset of the qubit namespace. -/
def supportSubset (support Q : List Nat) : Prop :=
  ∀ q, q ∈ support → q ∈ Q

/-- The displayed rows of one sector. -/
def sectorRows (s : CodeState) (sector : Sector) : List Row :=
  s.rows.filter (fun r => r.sector = sector)

/-- State update for add: append a canonically minted row. -/
def addState (s : CodeState) (sector : Sector) (support : List Nat) : CodeState :=
  { Q := s.Q
  , rows := s.rows ++ [⟨canonicalMint s.used, sector, support⟩]
  , used := s.used ++ [canonicalMint s.used] }

/-- Index of a qubit in the qubit list, if present. -/
def indexOfQubit : List Nat → Nat → Option Nat
  | [], _ => none
  | q :: qs, target => if q = target then some 0 else (indexOfQubit qs target).map (· + 1)

/-- Bitmask of a displayed row over the qubit list `Q`. -/
def rowBitmask (Q : List Nat) (r : Row) : Nat :=
  r.support.foldl (fun acc q =>
    match indexOfQubit Q q with
    | some i => acc ||| (1 <<< i)
    | none => acc) 0

/-- Insert a basis vector by pivot, descending. -/
def insertByPivot (b : Nat) (bs : List Nat) : List Nat :=
  match bs with
  | [] => [b]
  | c :: cs => if Nat.log2 b >= Nat.log2 c then b :: bs else c :: insertByPivot b cs

/-- Sort basis vectors by pivot descending. -/
def sortByPivotDesc (bs : List Nat) : List Nat :=
  bs.foldl (fun acc b => insertByPivot b acc) []

/-- Reduce `x` by a basis (one pass, basis sorted descending). -/
def reduceByBasis (basis : List Nat) (x : Nat) : Nat :=
  (sortByPivotDesc basis).foldl (fun acc b =>
    if b ≠ 0 && (acc >>> Nat.log2 b) &&& 1 = 1 then acc ^^^ b else acc) x

/-- Insert a vector into an F2-basis. -/
def insertBasis (basis : List Nat) (x : Nat) : List Nat :=
  let x' := reduceByBasis basis x
  if x' = 0 then basis else x' :: basis

/-- Rank of a list of bitmasks over F2. -/
def rankBitmasks (masks : List Nat) : Nat :=
  (masks.foldl insertBasis []).length

/-- Rank of the displayed rows of one sector. -/
def sectorRank (Q : List Nat) (rows : List Row) (sector : Sector) : Nat :=
  rankBitmasks ((rows.filter (fun r => r.sector = sector)).map (rowBitmask Q))

/-- `k = n - rank(X) - rank(Z)` for a state. Uses truncated Nat
    subtraction: on a well-formed display rank X + rank Z <= n (I1), so the
    truncation is harmless there; on arbitrary inputs the equation can hold
    with both sides truncated to zero. -/
def stateK (s : CodeState) : Nat :=
  s.Q.length - sectorRank s.Q s.rows Sector.X - sectorRank s.Q s.rows Sector.Z

/-- Rows of `s` in `sector` that touch `qubit`. -/
def touchingRows (s : CodeState) (sector : Sector) (qubit : Nat) : List Row :=
  s.rows.filter (fun r => r.sector = sector ∧ r.support.contains qubit)

/-- Remove the grafted qubit from a row's support if it is present; otherwise leave the row unchanged. -/
def shortenRow (qubit : Nat) (r : Row) : Row :=
  if r.support.contains qubit then
    { id := r.id, sector := r.sector, support := r.support.filter (fun q => q ≠ qubit) }
  else r

def peelSupport (qubit : Nat) (S : List Nat) : List Nat :=
  if S.contains qubit then S.filter (fun q => q ≠ qubit) else S

/-- Coverage: every remaining qubit appears in both sectors. -/
abbrev coverage (s : CodeState) : Prop :=
  ∀ q ∈ s.Q,
    (∃ r ∈ s.rows, r.sector = Sector.X ∧ r.support.contains q) ∧
    (∃ r ∈ s.rows, r.sector = Sector.Z ∧ r.support.contains q)

/-- Insert `x` into a sorted list of naturals, preserving order. -/
def insertSorted (x : Nat) (xs : List Nat) : List Nat :=
  match xs with
  | [] => [x]
  | y :: ys => if x ≤ y then x :: xs else y :: insertSorted x ys

/-- Structurally recursive insertion sort; unfolds under `decide`/`native_decide`,
    unlike `List.mergeSort`. Minted graft supports are sorted, exactly as the
    machine transcription produces them (`priced_calculus.py` graft:
    `tuple(sorted(...))`). The display contract (REPRESENTATION.md) requires
    strictly increasing supports, and sorting keeps the minted rows on the
    contract without assuming an ambient order on `Q`. -/
def sortNat (qs : List Nat) : List Nat :=
  match qs with
  | [] => []
  | x :: xs => insertSorted x (sortNat xs)

/-! ### Gate 6 CSS conditional-cell state updates (2026-10-23)

The five state updates mirror `machine/priced_calculus.py`'s Gate 6 methods
and `spec/OPERATIONAL_SEMANTICS.md` §2. The `Eval` constructors below take the
§2 cards' applicability premises. -/

/-- The sector-exchanged row and state (the `T=Q` hadamard instance). -/
def swapRow (r : Row) : Row := { r with sector := oppositeSector r.sector }

def swapState (s : CodeState) : CodeState :=
  { s with rows := s.rows.map swapRow }

/-- Symmetric difference of two lists. -/
def xorList {α : Type} [DecidableEq α] (a b : List α) : List α :=
  (a.filter (fun x => ¬ b.contains x)) ++ (b.filter (fun x => ¬ a.contains x))

/-- F_2 sum of the supports selected by a 0/1 coefficient vector over an
    ordered row list: `c = 1` at position `j` selects row `j`; supports are
    sorted by the display contract. -/
def mixSupport (ordered : List Row) (cs : List Nat) : List Nat :=
  sortNat ((ordered.zip cs).foldl (fun acc (r, c) =>
    if c = 1 then xorList acc r.support else acc) [])

/-- A rebase coefficient row as a bitmask over *column positions*. -/
def matrixRowMask : List Nat → Nat
  | [] => 0
  | c :: cs => (if c = 0 then 0 else 1) ||| (matrixRowMask cs * 2)

/-- The rebase command's structural premises: square, 0/1, invertible. -/
def rebaseMatrix_ok (matrix : List (List Nat)) (m : Nat) : Prop :=
  (matrix.length = m) ∧
  (∀ cs, cs ∈ matrix → cs.length = m ∧ ∀ c, c ∈ cs → c = 0 ∨ c = 1) ∧
  rankBitmasks (matrix.map matrixRowMask) = m

/-- The rows minted by `P-REBASE`, shared by the state update and the
    transport row. -/
def rebaseMintedRows (s : CodeState) (sector : Sector) (matrix : List (List Nat)) : List Row :=
  let ordered := sectorRows s sector
  (matrix.zip (mintFresh s.used matrix.length)).map (fun cs_id =>
    ⟨cs_id.2, sector, mixSupport ordered cs_id.1⟩)

/-- The rebase state update: each coefficient row (its F_2 combination of the
    sector's displayed rows, symmetric difference of supports, sorted) becomes
    a canonically minted row of the same sector; the *other* sector's display
    is retained. -/
def rebaseState (s : CodeState) (sector : Sector) (matrix : List (List Nat)) : CodeState :=
  let ids := mintFresh s.used matrix.length
  { Q := s.Q
  , rows := (s.rows.filter (fun r => r.sector ≠ sector)) ++ rebaseMintedRows s sector matrix
  , used := s.used ++ ids }

/-- The peel's state update: remove the named row (its identifier stays in
    `used`, I3) and the peeled qubit, shortening the surviving opposite-sector
    rows at `q`. -/
def peelState (s : CodeState) (q : Nat) (r_id : Nat) : CodeState :=
  { Q := s.Q.filter (fun qa => qa ≠ q)
  , rows := (s.rows.filter (fun row => row.id ≠ r_id)).map (shortenRow q)
  , used := s.used }

/-- The puncture's state update (the check-puncturing induced update). -/
def punctureState (s : CodeState) (q : Nat) : CodeState :=
  { Q := s.Q.filter (fun qa => qa ≠ q)
  , rows := s.rows.filter (fun row => ¬ row.support.contains q)
  , used := s.used }

/-- Hamming weight of a nat mask (Lean 4.35's `Nat` has no `bitCount`).
    Fuel-based so no termination proof is owed. -/
def popcountNatFuel (fuel n : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel + 1 => if n = 0 then 0 else popcountNatFuel fuel (n / 2) + n % 2

/-- `popcountNat n` = the Hamming weight of `n` (fuel `n` suffices: halving
    reaches 0 within `log2 n ≤ n` steps). -/
def popcountNat (n : Nat) : Nat :=
  popcountNatFuel n n

/-- Extra fuel beyond `n` does not change `popcountNatFuel`: halving reaches 0
    within `n` steps, so any fuel `≥ n` gives the same result as fuel `n`. -/
theorem popcountNatFuel_ge {fuel n : Nat} (h : fuel ≥ n) :
    popcountNatFuel fuel n = popcountNatFuel n n := by
  let C (k : Nat) := ∀ fuel, fuel ≥ k → popcountNatFuel fuel k = popcountNatFuel k k
  have step : ∀ k, (∀ m, m < k → C m) → C k := by
    intro k ih fuel hfuel
    cases k with
    | zero => induction fuel <;> simp [popcountNatFuel]
    | succ k' =>
        cases fuel with
        | zero => omega
        | succ f =>
            have hm : (k' + 1) / 2 < k' + 1 :=
              Nat.div_lt_self (Nat.succ_pos k') (show 1 < 2 by decide)
            have hn' : k' ≥ (k' + 1) / 2 := by omega
            have hfk : f ≥ k' := by omega
            have hf : f ≥ (k' + 1) / 2 := by omega
            have hsimp : popcountNatFuel (f + 1) (k' + 1) =
                popcountNatFuel f ((k' + 1) / 2) + (k' + 1) % 2 := by
              simp [popcountNatFuel]
            have hrhs : popcountNatFuel (k' + 1) (k' + 1) =
                popcountNatFuel k' ((k' + 1) / 2) + (k' + 1) % 2 := by
              simp [popcountNatFuel]
            rw [hsimp, hrhs]
            rw [ih ((k' + 1) / 2) hm f hf, ih ((k' + 1) / 2) hm k' hn']
  have wf := (inferInstance : WellFoundedRelation Nat).wf
  exact WellFounded.induction wf (a := n) step fuel h

/-- Shifting a mask left by one bit (multiplying by 2) does not change its
    Hamming weight: the new low bit is 0. -/
theorem popcountNat_mul2 (n : Nat) : popcountNat (2 * n) = popcountNat n := by
  cases n with
  | zero => simp [popcountNat, popcountNatFuel]
  | succ n =>
      have hne : 2 * (n + 1) ≠ 0 := by omega
      have hstep : popcountNat (2 * (n + 1)) =
          popcountNatFuel (2 * (n + 1) - 1) ((2 * (n + 1)) / 2) + (2 * (n + 1)) % 2 := by
        rw [show 2 * (n + 1) = (2 * (n + 1) - 1) + 1 by omega]
        simp [popcountNat, popcountNatFuel, hne]
      rw [hstep]
      have hdiv : (2 * (n + 1)) / 2 = n + 1 := by omega
      have hmod : (2 * (n + 1)) % 2 = 0 := by omega
      rw [hdiv, hmod, Nat.add_zero]
      have hge : 2 * (n + 1) - 1 ≥ n + 1 := by omega
      show popcountNatFuel (2 * (n + 1) - 1) (n + 1) = popcountNat (n + 1)
      exact popcountNatFuel_ge hge

/-- A support list's mask over qubit *labels*. -/
def supportMaskOfList (sup : List Nat) : Nat :=
  sup.foldl (fun m q => m ||| (1 <<< q)) 0

/-- Extension additions are checked cumulatively: each addition's
    same-sector independence and opposite-sector commutation are tested at
    its own list position over the accumulated F_2 bases. -/
def extendStep (xBasis zBasis : List Nat) (rec : Sector × List Nat)
    : Except String (List Nat × List Nat) :=
  if rec.2.isEmpty then Except.error "empty support"
  else match rec.1 with
  | Sector.X =>
      if ¬ zBasis.all (fun b => ((popcountNat (supportMaskOfList rec.2 &&& b)) % 2) = 0) then
        Except.error "opposite-sector commutation fails"
      else if (reduceByBasis xBasis (supportMaskOfList rec.2)) = 0 then
        Except.error "same-sector independence fails"
      else Except.ok (insertBasis xBasis (supportMaskOfList rec.2), zBasis)
  | Sector.Z =>
      if ¬ xBasis.all (fun b => ((popcountNat (supportMaskOfList rec.2 &&& b)) % 2) = 0) then
        Except.error "opposite-sector commutation fails"
      else if (reduceByBasis zBasis (supportMaskOfList rec.2)) = 0 then
        Except.error "same-sector independence fails"
      else Except.ok (xBasis, insertBasis zBasis (supportMaskOfList rec.2))

def extendRun (s : CodeState) (delta : List Nat)
    (adds : List (Sector × List Nat)) : Except String (List Nat × List Nat) :=
  let xSeed := (sectorRows s Sector.X).foldl
      (fun b r => insertBasis b (supportMaskOfList r.support)) []
  let zSeed := (sectorRows s Sector.Z).foldl
      (fun b r => insertBasis b (supportMaskOfList r.support)) []
  match delta.foldl (fun run q =>
      match run with
      | Except.error e => Except.error e
      | Except.ok run' => if s.Q.contains q then Except.error "new qubit overlaps Q"
                          else Except.ok run') (Except.ok (xSeed, zSeed)) with
  | Except.error e => Except.error e
  | Except.ok bases =>
      adds.foldl (fun run rec =>
        match run with
        | Except.error e => Except.error e
        | Except.ok (x, z) => extendStep x z rec) (Except.ok bases)

/-- The extend command's structurally checked applicability. -/
def extend_ok (s : CodeState) (delta : List Nat)
    (adds : List (Sector × List Nat)) : Prop :=
  (∀ q, q ∈ delta → ¬ s.Q.contains q) ∧
  delta.Nodup ∧
  (∀ rec, rec ∈ adds → rec.2.Nodup ∧ rec.2 ≠ [] ∧
    rec.2.Pairwise (· ≤ ·) ∧
    supportSubset rec.2 (s.Q ++ delta)) ∧
  (match extendRun s delta adds with
   | Except.ok _ => True
   | Except.error _ => False)

/-- The rows minted by `E-EXTEND`, shared by the state update and the
    transport row. -/
def extendMintedRows (s : CodeState) (adds : List (Sector × List Nat)) : List Row :=
  (adds.zip (mintFresh s.used adds.length)).map (fun rec_id =>
    ⟨rec_id.2, rec_id.1.1, sortNat rec_id.1.2⟩)

/-- The row-added extension's state update: namespace `Q ∪ Δ`, the retained
    display, and the additions appended in list order with canonically minted
    identifiers and sorted supports. -/
def extendState (s : CodeState) (delta : List Nat)
    (adds : List (Sector × List Nat)) : CodeState :=
  let q' := sortNat ((s.Q ++ delta).eraseDups)
  let ids := mintFresh s.used adds.length
  { Q := q'
  , rows := s.rows ++ extendMintedRows s adds
  , used := s.used ++ ids }

/-- The `hadamard` state update: `T=Q` swaps every displayed row's sector;
    the `T=∅` conjugation is the identity. -/
def hadamardState (s : CodeState) (T : List Nat) : CodeState :=
  if T.isEmpty then s else swapState s

/-! ### `C-COLUMN-CNOT` state update (`spec/OPERATIONAL_SEMANTICS.md` §4.42) -/

/-- Shape check: `U` is an `n × n` binary matrix. -/
def boolMatShape (U : List (List Bool)) (n : Nat) : Bool :=
  U.length == n && U.all (fun row => row.length == n)

/-- Transpose of an `n × n` binary matrix. -/
def boolMatTranspose (n : Nat) (U : List (List Bool)) : List (List Bool) :=
  (List.range n).map (fun j =>
    (List.range n).map (fun i => (U.getD i []).getD j false))

/-- `n × n` identity matrix over `F₂`. -/
def boolMatId (n : Nat) : List (List Bool) :=
  (List.range n).map (fun i => (List.range n).map (fun j => i == j))

/-- Matrix multiplication over `F₂` of two `n × n` binary matrices. -/
def boolMatMul (n : Nat) (A B : List (List Bool)) : List (List Bool) :=
  (List.range n).map (fun i =>
    (List.range n).map (fun j =>
      (List.range n).foldl (fun acc k =>
        Bool.xor acc (((A.getD i []).getD k false) && ((B.getD k []).getD j false))) false))

/-- Row-vector times matrix over `F₂`: `(v M)_j = ∑_i v_i M_{i,j}`. -/
def vecMulMat (n : Nat) (v : List Bool) (M : List (List Bool)) : List Bool :=
  (List.range n).map (fun j =>
    (List.range n).foldl (fun acc i =>
      Bool.xor acc ((v.getD i false) && ((M.getD i []).getD j false))) false)

/-- Swap two list entries by index (no-op when indices coincide or are out of bounds). -/
def swapListAt {α : Type} (xs : List α) (i j : Nat) : List α :=
  if i = j then xs
  else
    match xs[i]?, xs[j]? with
    | some a, some b => (xs.set i b).set j a
    | _, _ => xs

private def findPivotRowAux (col idx : Nat) : List (List Bool) → Option Nat
  | [] => none
  | row :: rest =>
      if idx ≥ col && row.getD col false then some idx
      else findPivotRowAux col (idx + 1) rest

/-- Deterministic Gauss–Jordan inversion over `F₂` for an `n × n` binary matrix. -/
def gf2InvBool (U : List (List Bool)) : Option (List (List Bool)) :=
  let n := U.length
  if !boolMatShape U n then none
  else
    let aug0 : List (List Bool) :=
      (List.range n).map (fun i =>
        U.getD i [] ++ (List.range n).map (fun j => i == j))
    let augFinal := (List.range n).foldl (fun acc col =>
      match acc with
      | none => none
      | some mat =>
          match findPivotRowAux col 0 mat with
          | none => none
          | some piv =>
              let mat1 := swapListAt mat col piv
              let pivRow := mat1.getD col []
              let mat2 := (List.range n).map (fun r =>
                let row := mat1.getD r []
                if r != col && row.getD col false then
                  List.zipWith Bool.xor row pivRow
                else row)
              some mat2) (some aug0)
    augFinal.map (fun mat => mat.map (fun row => row.drop n))

/-- Decidable check that `U` is `n × n` and invertible over `F₂`, certified
    directly by two-sided multiplication against `gf2InvBool U`. -/
def cnotMatrixOkBool (U : List (List Bool)) (n : Nat) : Bool :=
  boolMatShape U n &&
  match gf2InvBool U with
  | some Uinv =>
      boolMatShape Uinv n &&
      (boolMatMul n U Uinv == boolMatId n) &&
      (boolMatMul n Uinv U == boolMatId n)
  | none => false

/-- Structural applicability premise of `C-COLUMN-CNOT` (§4.42). -/
def cnotMatrix_ok (U : List (List Bool)) (n : Nat) : Prop :=
  cnotMatrixOkBool U n = true

/-- Support transformed by `C-COLUMN-CNOT` (§4.42): X-rows by `U⁻¹`, Z-rows
    by `Uᵀ`, sorted onto the display contract. -/
def cnotSwapSupport (Q : List Nat) (U : List (List Bool)) (σ : Sector) (S : List Nat) :
    List Nat :=
  let n := Q.length
  let v := Q.map (fun q => S.contains q)
  let M := match σ with
    | Sector.X => (gf2InvBool U).getD (boolMatId n)
    | Sector.Z => boolMatTranspose n U
  let v' := vecMulMat n v M
  sortNat ((Q.zip v').filterMap (fun p => if p.2 then some p.1 else none))

def cnotSwapRow (Q : List Nat) (U : List (List Bool)) (r : Row) : Row :=
  { id := r.id, sector := r.sector, support := cnotSwapSupport Q U r.sector r.support }

/-- State update of `C-COLUMN-CNOT`: `Q` and `used` unchanged; each displayed
    row retains its identifier and sector while its support transforms by `U⁻¹`
    (X-sector) or `Uᵀ` (Z-sector). -/
def cnotSwapState (s : CodeState) (U : List (List Bool)) : CodeState :=
  { Q := s.Q, rows := s.rows.map (cnotSwapRow s.Q U), used := s.used }

/-! ### Split-subset `hadamard` (`0 < |T| < |Q|`, issue #571)

The canonical update of `spec/OPERATIONAL_SEMANTICS.md` §2 (`E-LOCAL-HADAMARD`
card) and §4.27, transcribed from `machine/state.py` `local_hadamard`. -/

/-- The inner piece `supp ∩ T` of a support. -/
def innerPiece (T sup : List Nat) : List Nat := sup.filter (fun q => T.contains q)

/-- The outer piece `supp ∖ T` of a support. -/
def outerPiece (T sup : List Nat) : List Nat := sup.filter (fun q => ¬ T.contains q)

/-- A row is `T`-pure when it lies inside `T` or is disjoint from it. -/
def isPureRow (T : List Nat) (r : Row) : Bool :=
  (innerPiece T r.support).isEmpty || (outerPiece T r.support).isEmpty

/-- A pure row's output sector: a nonempty row inside `T` changes sector, a row
    disjoint from `T` keeps it. -/
def pureSector (T : List Nat) (r : Row) : Sector :=
  if (outerPiece T r.support).isEmpty ∧ ¬ (innerPiece T r.support).isEmpty then
    oppositeSector r.sector
  else r.sector

/-- The positional bitmask of a support over `Q` (the mask `rowBitmask` gives
    a row with that support). -/
def pieceMask (Q sup : List Nat) : Nat := rowBitmask Q ⟨0, Sector.X, sup⟩

/-- The F₂ basis (positional bitmasks over `Q`) of a sector's displayed rows. -/
def sectorBasis (s : CodeState) (σ : Sector) : List Nat :=
  ((sectorRows s σ).map (rowBitmask s.Q)).foldl insertBasis []

/-- The decidable row-space splitting guard: every displayed row restricted to
    `T` lies in its own sector's span (`v|_T ∈ X` for all `v ∈ X`, and
    `w|_T ∈ Z` for all `w ∈ Z`, by linearity of restriction). -/
def splitGuard (s : CodeState) (T : List Nat) : Bool :=
  s.rows.all (fun r =>
    reduceByBasis (sectorBasis s r.sector) (pieceMask s.Q (innerPiece T r.support)) = 0)

/-- The running output basis of one sector. -/
def basisFor (xb zb : List Nat) : Sector → List Nat
  | Sector.X => xb
  | Sector.Z => zb

/-- Insert a mask into the running basis of one sector. -/
def insertFor (xb zb : List Nat) (σ : Sector) (m : Nat) : List Nat × List Nat :=
  match σ with
  | Sector.X => (insertBasis xb m, zb)
  | Sector.Z => (xb, insertBasis zb m)

/-- Insert a row into a list sorted by identifier rank (`Row.id`, the fixed
    enumeration order of `State.lean`), preserving order. -/
def insertRowByRank (r : Row) (rs : List Row) : List Row :=
  match rs with
  | [] => [r]
  | r' :: rest => if r.id ≤ r'.id then r :: rs else r' :: insertRowByRank r rest

/-- Structurally recursive insertion sort of rows by identifier rank
    (`Row.id`, the order of the fixed identifier enumeration); unfolds under
    `decide`, unlike `List.mergeSort`. -/
def sortRowsByRank (rs : List Row) : List Row :=
  match rs with
  | [] => []
  | r :: rest => insertRowByRank r (sortRowsByRank rest)

/-- The masks of the `T`-pure rows landing in output sector `σ`, in identifier
    order (the order of the fixed identifier enumeration). -/
def pureMasks (s : CodeState) (T : List Nat) (σ : Sector) : List Nat :=
  (((sortRowsByRank s.rows).filter (isPureRow T)).filter (fun r => pureSector T r = σ)).map
    (fun r => pieceMask s.Q r.support)

/-- The output bases seeded with the `T`-pure rows of each output sector. -/
def splitSeed (s : CodeState) (T : List Nat) : List Nat × List Nat :=
  ((pureMasks s T Sector.X).foldl insertBasis [], (pureMasks s T Sector.Z).foldl insertBasis [])

/-- One candidate piece against the running bases `b`: kept (`true`, and
    inserted into the basis of its output sector `τ`) exactly when its mask is
    independent of that basis. -/
def pieceStep (Q : List Nat) (b : List Nat × List Nat) (τ : Sector) (p : List Nat) :
    Bool × (List Nat × List Nat) :=
  if reduceByBasis (basisFor b.1 b.2 τ) (pieceMask Q p) = 0 then (false, b)
  else (true, insertFor b.1 b.2 τ (pieceMask Q p))

/-- The entries a mixed row emits, given which of its two pieces are kept:
    the first kept piece carries the row's identifier, a second is marked for
    minting (`none`). -/
def mixedEntries (T : List Nat) (r : Row) (ko ki : Bool) : List (Option Nat × Sector × List Nat) :=
  (if ko then [(some r.id, r.sector, outerPiece T r.support)] else []) ++
  (if ki then [(if ko then none else some r.id, oppositeSector r.sector,
    innerPiece T r.support)] else [])

/-- Pass 1 of the split update, as a recursion over a row list with the
    running output bases `b` (`splitEntries` calls this in identifier order).
    A pure row is emitted with its identifier and output sector. A mixed row
    offers its outer piece in its own sector, then its inner piece in the
    opposite sector (`pieceStep`). -/
def splitGo (Q T : List Nat) : List Nat × List Nat → List Row →
    List (Option Nat × Sector × List Nat)
  | _, [] => []
  | b, r :: rs =>
      if isPureRow T r then (some r.id, pureSector T r, r.support) :: splitGo Q T b rs
      else
        let s1 := pieceStep Q b r.sector (outerPiece T r.support)
        let s2 := pieceStep Q s1.2 (oppositeSector r.sector) (innerPiece T r.support)
        mixedEntries T r s1.1 s2.1 ++ splitGo Q T s2.2 rs

/-- The output bases after pass 1 (used only in proofs). -/
def splitFinal (Q T : List Nat) : List Nat × List Nat → List Row → List Nat × List Nat
  | b, [] => b
  | b, r :: rs =>
      if isPureRow T r then splitFinal Q T b rs
      else
        let s1 := pieceStep Q b r.sector (outerPiece T r.support)
        let s2 := pieceStep Q s1.2 (oppositeSector r.sector) (innerPiece T r.support)
        splitFinal Q T s2.2 rs

/-- The entries of pass 1 over the whole display, read in identifier order
    (the order of the fixed identifier enumeration). -/
def splitEntries (s : CodeState) (T : List Nat) : List (Option Nat × Sector × List Nat) :=
  splitGo s.Q T (splitSeed s T) (sortRowsByRank s.rows)

/-- The number of identifiers the split update mints. -/
def splitMintCount (s : CodeState) (T : List Nat) : Nat :=
  ((splitEntries s T).filter (fun e => e.1.isNone)).length

/-- Pass 2: inherited identifiers stay; each `none` entry takes the next
    canonically minted identifier. -/
def assignIds : List (Option Nat × Sector × List Nat) → List Nat → List Row
  | [], _ => []
  | (some id, σ, sup) :: rest, ids => ⟨id, σ, sup⟩ :: assignIds rest ids
  | (none, σ, sup) :: rest, id :: ids => ⟨id, σ, sup⟩ :: assignIds rest ids
  | (none, _, _) :: rest, [] => assignIds rest []

/-- The split-subset `hadamard` state update (`0 < |T| < |Q|`): `Q` is
    unchanged, the display is the canonical piece selection, and `used` grows
    by the canonically minted identifiers. -/
def splitHadamardState (s : CodeState) (T : List Nat) : CodeState :=
  let ids := mintFresh s.used (splitMintCount s T)
  { Q := s.Q
  , rows := assignIds (splitEntries s T) ids
  , used := s.used ++ ids }

/-- The split instance's subset premise: `T` is a nonempty, repeat-free,
    proper subset of `Q` (so it is disjoint from the `T = Q` and `T = ∅`
    instances of `Eval.hadamard`). -/
def ProperSubset (T Q : List Nat) : Prop :=
  T ≠ [] ∧ T.Nodup ∧ supportSubset T Q ∧ ¬ (∀ q, q ∈ Q → q ∈ T)

instance (T Q : List Nat) : Decidable (ProperSubset T Q) :=
  inferInstanceAs (Decidable (T ≠ [] ∧ T.Nodup ∧ (∀ q, q ∈ T → q ∈ Q) ∧
    ¬ (∀ q, q ∈ Q → q ∈ T)))

/-- `T` covers the namespace: every qubit of `Q` is in `T`. On a repeat-free
    `T ⊆ Q` this is the global instance `T = Q`; it is the constructive
    discriminator the ledger transport branches on (deciding `List.Perm`
    would bring `Classical.choice` into the transport). -/
def CoversQ (T Q : List Nat) : Prop := ∀ q, q ∈ Q → q ∈ T

instance (T Q : List Nat) : Decidable (CoversQ T Q) :=
  inferInstanceAs (Decidable (∀ q, q ∈ Q → q ∈ T))

theorem coversQ_of_perm {T Q : List Nat} (h : T.Perm Q) : CoversQ T Q :=
  fun _ hq => h.mem_iff.mpr hq

theorem not_coversQ_of_properSubset {T Q : List Nat} (h : ProperSubset T Q) :
    ¬ CoversQ T Q := h.2.2.2

/-- A proper subset is never a permutation of `Q` and never empty, so the
    split instance is disjoint from the `T = Q` / `T = ∅` instances. -/
theorem not_perm_or_nil_of_properSubset {T Q : List Nat} (h : ProperSubset T Q) :
    ¬ (T.Perm Q ∨ T = []) := by
  rintro (hp | hn)
  · exact h.2.2.2 (fun q hq => hp.mem_iff.mpr hq)
  · exact h.1 hn

/-- State update for the structural graft transition. -/
def graftState (s : CodeState) (qubit : Nat) (sector : Sector)
    (orderedIds : List Nat) : CodeState :=
  let remainingQ := s.Q.filter (fun q => q ≠ qubit)
  -- `filterMap` drops ids that do not resolve; the touching premise of
  -- `Eval.graft` rules that out, so `chain` has the same length as
  -- `orderedIds` on any derived transition.
  let chain := orderedIds.filterMap (rowById s)
  let nonChain := s.rows.filter (fun r => ¬ orderedIds.contains r.id)
  let shortened := nonChain.map (fun r =>
    if r.sector = oppositeSector sector ∧ r.support.contains qubit then
      shortenRow qubit r
    else r)
  let mintedIds := mintFresh s.used (orderedIds.length - 1)
  let mintedRows :=
    (List.zip chain (chain.drop 1)).zip mintedIds |>.map (fun (pair, id) =>
      let left := pair.1
      let right := pair.2
      { id := id
      , sector := sector
      , support := sortNat (remainingQ.filter (fun q =>
          left.support.contains q ≠ right.support.contains q)) })
  { Q := remainingQ
  , rows := shortened ++ mintedRows
  , used := s.used ++ mintedIds }

/-- The support a surviving row has after a graft at `qubit` in `sector`: an
    opposite-sector row that contains the grafted qubit loses it, and every
    other row keeps its support. -/
def graftSupport (qubit : Nat) (sector σ : Sector) (S : List Nat) : List Nat :=
  if σ = oppositeSector sector ∧ S.contains qubit then S.filter (fun q => q ≠ qubit) else S

/-- Evaluation of commands. WP1 covers skip, sequencing, deletion, addition,
    the structural graft transition, and the five admitted Gate 6 conditional
    cells (rebase, peel, puncture, extend, hadamard). The add rule carries the row
    conditions `EncodingWellFormed` requires on a displayed row (support
    inside `Q`, no repeats, sorted) so the rule cannot derive a display that
    is not a CSS code. With a no-repeat support the multiplicity sensitivity
    of `supportIntersectionSize` (State.lean) cannot be exploited: counting an
    overlap twice requires a repeated qubit. The graft mints no external
    support, so its supports are sorted by construction (see `sortNat`). -/
inductive Eval : Command → CodeState → CodeState → Prop where
  | skip (s : CodeState) : Eval Command.skip s s
  | seq {m1 m2 : Command} {s s1 s' : CodeState} :
      Eval m1 s s1 → Eval m2 s1 s' →
      Eval (Command.seq m1 m2) s s'
  | delete {r : Nat} {s s' : CodeState} :
      DisplayedGenerator r s →
      IndependentGenerator r s →
      s' = deleteState s r →
      Eval (Command.delete r) s s'
  | add {sector : Sector} {support : List Nat} {s s' : CodeState} :
      supportSubset support s.Q →
      support.Nodup →
      support.Pairwise (· ≤ ·) →
      (∀ row ∈ s.rows, row.sector = oppositeSector sector →
        supportIntersectionSize support row.support % 2 = 0) →
      ¬ inSpanRows s.Q (sectorRows s sector)
          (rowVector s.Q ⟨canonicalMint s.used, sector, support⟩) →
      s' = addState s sector support →
      canonicalMint s.used < totalIdentifiers →
      Eval (Command.addStab sector support) s s'
  | graft {qubit : Nat} {sector : Sector} {orderedIds : List Nat}
      {s s' : CodeState} :
      qubit ∈ s.Q →
      (∃ r ∈ s.rows, r.sector = oppositeSector sector ∧
        r.support.contains qubit) →
      (touchingRows s sector qubit ≠ []) →
      (orderedIds.length = (touchingRows s sector qubit).length) →
      (orderedIds.Nodup) →
      (∀ id ∈ orderedIds, id ∈ (touchingRows s sector qubit).map Row.id) →
      coverage (graftState s qubit sector orderedIds) →
      stateK (graftState s qubit sector orderedIds) = stateK s →
      s' = graftState s qubit sector orderedIds →
      MintsWithinCapacity s.used (orderedIds.length - 1) →
      Eval (Command.graft qubit sector orderedIds) s s'
  | rebase {sector : Sector} {matrix : List (List Nat)} {s s' : CodeState} :
      (sectorRows s sector ≠ []) →
      rebaseMatrix_ok matrix (sectorRows s sector).length →
      s' = rebaseState s sector matrix →
      EncodingWellFormed s' →
      MintsWithinCapacity s.used matrix.length →
      Eval (Command.rebase sector matrix) s s'
  | hadamard {T : List Nat} {s s' : CodeState} :
      (T.Perm s.Q ∨ T = []) →
      s' = hadamardState s T →
      EncodingWellFormed s' →
      Eval (Command.hadamard T) s s'
  /-- `E-LOCAL-HADAMARD`, split-subset instance (`0 < |T| < |Q|`, issue #571):
      a proper subset, the row-space splitting guard, the canonical update,
      and the checked output premises (`EncodingWellFormed`, `k' = k`, mint
      capacity) that §4.27 derives by hand. -/
  | hadamardSplit {T : List Nat} {s s' : CodeState} :
      ProperSubset T s.Q →
      splitGuard s T = true →
      s' = splitHadamardState s T →
      EncodingWellFormed s' →
      stateK s' = stateK s →
      MintsWithinCapacity s.used (splitMintCount s T) →
      Eval (Command.hadamard T) s s'
  | peel {q : Nat} {tau : Sector} {r_id : Nat} {s s' : CodeState} :
      q ∈ s.Q →
      (∃ row, row ∈ s.rows ∧ row.id = r_id ∧ row.sector = tau ∧
        row.support.contains q) →
      ((touchingRows s tau q).length = 1) →
      (¬ ∃ row ∈ s.rows, row.sector = oppositeSector tau ∧
        row.support = [q]) →
      s' = peelState s q r_id →
      EncodingWellFormed s' →
      Eval (Command.peel q tau r_id) s s'
  | puncture {q : Nat} {s s' : CodeState} :
      q ∈ s.Q →
      s' = punctureState s q →
      EncodingWellFormed s' →
      Eval (Command.puncture q) s s'
  | extend {delta : List Nat} {adds : List (Sector × List Nat)} {s s' : CodeState} :
      extend_ok s delta adds →
      s' = extendState s delta adds →
      EncodingWellFormed s' →
      MintsWithinCapacity s.used adds.length →
      Eval (Command.extend delta adds) s s'
  | cnotSwap {U : List (List Bool)} {s s' : CodeState} :
      cnotMatrix_ok U s.Q.length →
      s' = cnotSwapState s U →
      EncodingWellFormed s' →
      Eval (Command.cnotSwap U) s s'
  /-- `E-SPLIT` (admitted 2026-11-25): separating deletion of an explicit
      displayed cut-row set `R` covering all rows crossing `QA` vs `Q \ QA`.
      Well-formedness of `deleteAll s R` follows from `EncodingWellFormed s`
      via `wf_deleteAll` (`WellFormedness.lean`), so it is not a rule premise. -/
  | split {QA R : List Nat} {s s' : CodeState} :
      QA.Nodup →
      (∀ q ∈ QA, q ∈ s.Q) →
      R.Nodup →
      (∀ r ∈ R, DisplayedGenerator r s) →
      (∀ row ∈ s.rows,
        (∀ q ∈ row.support, q ∈ QA) ∨ (∀ q ∈ row.support, q ∉ QA) ∨ row.id ∈ R) →
      s' = deleteAll s R →
      Eval (Command.split QA R) s s'

/-- Evaluation of a closed construction term. -/
inductive EvalTerm : ClosedTerm → CodeState → Prop where
  | eval {m : Command} {e : StateExpr} {s s' : CodeState} :
      EvalExpr e s → Eval m s s' →
      EvalTerm { command := m, expr := e } s'

/-! ### The derived denotation (2026-10-25)

`spec/OPERATIONAL_SEMANTICS.md` §1a fixes the reading after the authority
reconciliation: the partial big-step relation `Eval` is **primary**, and the
denotation is derived from it — `⟦m⟧(S) = some S'` iff `Eval m S S'`, `none`
otherwise, and `⟦e⟧ = some S` iff `EvalExpr e S`. Each branch below carries
exactly the corresponding `Eval` constructor's premises, decided classically,
so both functions are `noncomputable`. Nothing here reads `steps` or computes
a distance (D1, D2), and an inapplicable command denotes `none` with no
partial result exposed (`W10`). -/

open Classical in
/-- The derived denotation of a state expression. -/
noncomputable def denoteExpr : StateExpr → Option CodeState
  | StateExpr.base s => some s
  | StateExpr.directSum e1 e2 =>
      match denoteExpr e1, denoteExpr e2 with
      | some s1, some s2 =>
          if DisjointList s1.Q s2.Q ∧ DisjointList s1.used s2.used then
            some (directSumState s1 s2)
          else none
      | _, _ => none
  | StateExpr.glue e1 e2 seams =>
      match denoteExpr e1, denoteExpr e2 with
      | some s1, some s2 =>
          if DisjointList s1.Q s2.Q ∧ DisjointList s1.used s2.used ∧
             EncodingWellFormed (glueState s1 s2 seams) ∧
             MintsWithinCapacity (s1.used ++ s2.used) seams.length then
            some (glueState s1 s2 seams)
          else none
      | _, _ => none
  | StateExpr.hgp H1 H2 =>
      if binaryMatrixTyped H1 = true ∧ binaryMatrixTyped H2 = true ∧
         MintsWithinCapacity [] (hgpState H1 H2).rows.length then
        some (hgpState H1 H2)
      else none
  | StateExpr.lift orders A B =>
      if groupTyped orders = true ∧ algMatrixTyped orders A = true ∧
         algMatrixTyped orders B = true ∧
         MintsWithinCapacity [] (liftState orders A B).rows.length then
        some (liftState orders A B)
      else none
  | StateExpr.twoblock orders a b =>
      if groupTyped orders = true ∧ algElementTyped orders a = true ∧
         algElementTyped orders b = true ∧
         MintsWithinCapacity [] (twoblockState orders a b).rows.length then
        some (twoblockState orders a b)
      else none
  | StateExpr.concat eO eI blocks repsX repsZ =>
      match denoteExpr eO, denoteExpr eI with
      | some sO, some sI =>
          if EncodingWellFormed sO ∧ EncodingWellFormed sI ∧
             concatTyped sO sI blocks repsX repsZ = true ∧
             MintsWithinCapacity [] (concatState sO sI blocks repsX repsZ).rows.length then
            some (concatState sO sI blocks repsX repsZ)
          else none
      | _, _ => none
  | StateExpr.product eA eB =>
      match denoteExpr eA, denoteExpr eB with
      | some sA, some sB =>
          if EncodingWellFormed sA ∧ EncodingWellFormed sB ∧
             MintsWithinCapacity [] (productState sA sB).rows.length then
            some (productState sA sB)
          else none
      | _, _ => none
  | StateExpr.double e wiring conj =>
      match denoteExpr e with
      | some sC =>
          if EncodingWellFormed sC ∧ doubleTyped sC wiring = true ∧
             naturalCommuteBool (naturalRows (doubleQubits sC)
               (doubleVectors sC wiring conj)) = true ∧
             MintsWithinCapacity [] (doubleState sC wiring conj).rows.length then
            some (doubleState sC wiring conj)
          else none
      | none => none
  | StateExpr.balanced orders H1 rows1 cols1 H2 rows2 cols2 =>
      if balancedTyped orders H1 rows1 cols1 H2 rows2 cols2 = true ∧
         MintsWithinCapacity []
           (balancedState orders H1 rows1 cols1 H2 rows2 cols2).rows.length then
        some (balancedState orders H1 rows1 cols1 H2 rows2 cols2)
      else none
  | StateExpr.tanner n LX LZ viewsX viewsZ =>
      if tannerTyped n LX LZ viewsX viewsZ = true ∧
         naturalCommuteBool (naturalRows n (tannerVectors n LX LZ viewsX viewsZ)) = true ∧
         MintsWithinCapacity [] (tannerState n LX LZ viewsX viewsZ).rows.length then
        some (tannerState n LX LZ viewsX viewsZ)
      else none
  | StateExpr.tile tiles placements idents removed =>
      if tileTyped tiles placements idents removed = true ∧
         naturalCommuteBool (naturalRows (tileQubits placements idents)
           (tileVectors tiles placements idents removed)) = true ∧
         MintsWithinCapacity [] (tileState tiles placements idents removed).rows.length then
        some (tileState tiles placements idents removed)
      else none
  | StateExpr.nested HX HZ =>
      if nestedTyped HX HZ = true ∧
         naturalCommuteBool (naturalRows (matCols HX) (nestedVectors HX HZ)) = true ∧
         MintsWithinCapacity [] (nestedState HX HZ).rows.length then
        some (nestedState HX HZ)
      else none
  | StateExpr.cone DA DB F1 F0 =>
      if coneTyped DA DB F1 F0 = true ∧
         naturalCommuteBool (naturalRows (coneN DA DB F1 F0) (coneVectors DA DB F1 F0)) = true ∧
         MintsWithinCapacity [] (coneState DA DB F1 F0).rows.length then
        some (coneState DA DB F1 F0)
      else none
  | StateExpr.empty => some emptyCodeState
  | StateExpr.free qs =>
      if freeTyped qs = true then some (freeState qs) else none
  | StateExpr.pullback e1 e2 eI phi1 phi2 =>
      match denoteExpr e1, denoteExpr e2, denoteExpr eI with
      | some s1, some s2, some sI =>
          if EncodingWellFormed s1 ∧ EncodingWellFormed s2 ∧ EncodingWellFormed sI ∧
             pullbackTyped s1 s2 sI phi1 phi2 = true ∧
             cssMorphismBool s1 sI phi1 = true ∧
             cssMorphismBool s2 sI phi2 = true ∧
             naturalCommuteBool (naturalRows (pullbackPairs s1 s2 phi1 phi2).length
               (pullbackVectors s1 s2 phi1 phi2)) = true ∧
             MintsWithinCapacity [] (pullbackState s1 s2 phi1 phi2).rows.length then
            some (pullbackState s1 s2 phi1 phi2)
          else none
      | _, _, _ => none
  | StateExpr.pushout e1 e2 eS psi1 psi2 =>
      match denoteExpr e1, denoteExpr e2, denoteExpr eS with
      | some s1, some s2, some sS =>
          if EncodingWellFormed s1 ∧ EncodingWellFormed s2 ∧ EncodingWellFormed sS ∧
             pushoutTyped s1 s2 sS psi1 psi2 = true ∧
             cssMorphismBool sS s1 psi1 = true ∧
             cssMorphismBool sS s2 psi2 = true ∧
             naturalCommuteBool (naturalRows (pushoutClasses s1 s2 sS psi1 psi2).length
               (pushoutVectors s1 s2 sS psi1 psi2)) = true ∧
             MintsWithinCapacity [] (pushoutState s1 s2 sS psi1 psi2).rows.length then
            some (pushoutState s1 s2 sS psi1 psi2)
          else none
      | _, _, _ => none
  | StateExpr.liftTable t A B =>
      if tableGroupTyped t = true ∧ tableMatrixTyped t A = true ∧
         tableMatrixTyped t B = true ∧
         MintsWithinCapacity [] (tableLiftState t A B).rows.length then
        some (tableLiftState t A B)
      else none
  | StateExpr.twoblockTable t a b =>
      if tableGroupTyped t = true ∧ tableElementTyped t a = true ∧
         tableElementTyped t b = true ∧
         MintsWithinCapacity [] (tableTwoblockState t a b).rows.length then
        some (tableTwoblockState t a b)
      else none
  | StateExpr.balancedTable t H1 rows1 cols1 H2 rows2 cols2 =>
      if tableBalancedTyped t H1 rows1 cols1 H2 rows2 cols2 = true ∧
         MintsWithinCapacity []
           (tableBalancedState t H1 rows1 cols1 H2 rows2 cols2).rows.length then
        some (tableBalancedState t H1 rows1 cols1 H2 rows2 cols2)
      else none
  | StateExpr.pairPartition p BX BZ =>
      if pairPartitionTyped p BX BZ = true ∧
         naturalCommuteBool (naturalRows (pairPartitionQubits p BX)
           (pairPartitionVectors p BX BZ)) = true ∧
         MintsWithinCapacity [] (pairPartitionState p BX BZ).rows.length then
        some (pairPartitionState p BX BZ)
      else none
  | StateExpr.ppScale e0 P BX BZ =>
      match denoteExpr e0 with
      | some s0 =>
          if EncodingWellFormed s0 ∧
             ppScaleTyped s0 P BX BZ = true ∧
             naturalCommuteBool (naturalRows (pairPartitionQubits P BX)
               (pairPartitionVectors P BX BZ)) = true ∧
             MintsWithinCapacity s0.used (ppScaleState s0 P BX BZ).rows.length then
            some (ppScaleState s0 P BX BZ)
          else none
      | none => none


open Classical in
/-- The derived denotation of a command. -/
noncomputable def denote : Command → CodeState → Option CodeState
  | Command.skip, s => some s
  | Command.seq m1 m2, s =>
      match denote m1 s with
      | some s1 => denote m2 s1
      | none => none
  | Command.delete r, s =>
      if DisplayedGenerator r s ∧ IndependentGenerator r s then
        some (deleteState s r)
      else none
  | Command.addStab sector support, s =>
      if supportSubset support s.Q
          ∧ support.Nodup
          ∧ support.Pairwise (· ≤ ·)
          ∧ (∀ row ∈ s.rows, row.sector = oppositeSector sector →
              supportIntersectionSize support row.support % 2 = 0)
          ∧ ¬ inSpanRows s.Q (sectorRows s sector)
              (rowVector s.Q ⟨canonicalMint s.used, sector, support⟩)
          ∧ canonicalMint s.used < totalIdentifiers then
        some (addState s sector support)
      else none
  | Command.graft qubit sector orderedIds, s =>
      if qubit ∈ s.Q
          ∧ (∃ r ∈ s.rows, r.sector = oppositeSector sector ∧
              r.support.contains qubit)
          ∧ touchingRows s sector qubit ≠ []
          ∧ orderedIds.length = (touchingRows s sector qubit).length
          ∧ orderedIds.Nodup
          ∧ (∀ id ∈ orderedIds, id ∈ (touchingRows s sector qubit).map Row.id)
          ∧ coverage (graftState s qubit sector orderedIds)
          ∧ stateK (graftState s qubit sector orderedIds) = stateK s
          ∧ MintsWithinCapacity s.used (orderedIds.length - 1) then
        some (graftState s qubit sector orderedIds)
      else none
  | Command.rebase sector matrix, s =>
      if sectorRows s sector ≠ []
          ∧ rebaseMatrix_ok matrix (sectorRows s sector).length
          ∧ EncodingWellFormed (rebaseState s sector matrix)
          ∧ MintsWithinCapacity s.used matrix.length then
        some (rebaseState s sector matrix)
      else none
  | Command.hadamard T, s =>
      if (T.Perm s.Q ∨ T = []) ∧ EncodingWellFormed (hadamardState s T) then
        some (hadamardState s T)
      else if ProperSubset T s.Q ∧ splitGuard s T = true
          ∧ EncodingWellFormed (splitHadamardState s T)
          ∧ stateK (splitHadamardState s T) = stateK s
          ∧ MintsWithinCapacity s.used (splitMintCount s T) then
        some (splitHadamardState s T)
      else none
  | Command.peel q tau r_id, s =>
      if q ∈ s.Q
          ∧ (∃ row, row ∈ s.rows ∧ row.id = r_id ∧ row.sector = tau ∧
              row.support.contains q)
          ∧ (touchingRows s tau q).length = 1
          ∧ (¬ ∃ row ∈ s.rows, row.sector = oppositeSector tau ∧
              row.support = [q])
          ∧ EncodingWellFormed (peelState s q r_id) then
        some (peelState s q r_id)
      else none
  | Command.puncture q, s =>
      if q ∈ s.Q ∧ EncodingWellFormed (punctureState s q) then
        some (punctureState s q)
      else none
  | Command.extend delta adds, s =>
      if extend_ok s delta adds
          ∧ EncodingWellFormed (extendState s delta adds)
          ∧ MintsWithinCapacity s.used adds.length then
        some (extendState s delta adds)
      else none
  | Command.cnotSwap U, s =>
      if cnotMatrix_ok U s.Q.length
          ∧ EncodingWellFormed (cnotSwapState s U) then
        some (cnotSwapState s U)
      else none
  | Command.split QA R, s =>
      if QA.Nodup
          ∧ (∀ q ∈ QA, q ∈ s.Q)
          ∧ R.Nodup
          ∧ (∀ r ∈ R, DisplayedGenerator r s)
          ∧ (∀ row ∈ s.rows,
              (∀ q ∈ row.support, q ∈ QA) ∨ (∀ q ∈ row.support, q ∉ QA) ∨ row.id ∈ R) then
        some (deleteAll s R)
      else none

/-- Every derivation yields the denotation's `some` branch (spec §1a). -/
theorem eval_denoteExpr {e : StateExpr} {s : CodeState}
    (h : EvalExpr e s) : denoteExpr e = some s := by
  induction h with
  | base t => rfl
  | directSum hQ hU _ _ ih1 ih2 =>
      simp only [denoteExpr, ih1, ih2]
      split
      · rfl
      · rename_i hNot
        exact absurd (And.intro hQ hU) hNot
  | glue hQ hU hwf hcap _ _ ih1 ih2 =>
      simp only [denoteExpr, ih1, ih2]
      split
      · rfl
      · rename_i hNot
        exact absurd (And.intro hQ (And.intro hU (And.intro hwf hcap))) hNot
  | hgp h1 h2 hcap =>
      simp only [denoteExpr]
      split
      · rfl
      · rename_i hNot
        exact absurd ⟨h1, h2, hcap⟩ hNot
  | lift hG hA hB hcap =>
      simp only [denoteExpr]
      split
      · rfl
      · rename_i hNot
        exact absurd ⟨hG, hA, hB, hcap⟩ hNot
  | twoblock hG ha hb hcap =>
      simp only [denoteExpr]
      split
      · rfl
      · rename_i hNot
        exact absurd ⟨hG, ha, hb, hcap⟩ hNot
  | concat hO hI hty hcap _ _ ih1 ih2 =>
      simp only [denoteExpr, ih1, ih2]
      split
      · rfl
      · rename_i hNot
        exact absurd ⟨hO, hI, hty, hcap⟩ hNot
  | product hA hB hcap _ _ ih1 ih2 =>
      simp only [denoteExpr, ih1, ih2]
      split
      · rfl
      · rename_i hNot
        exact absurd ⟨hA, hB, hcap⟩ hNot
  | double hC hty hcomm hcap _ ih =>
      simp only [denoteExpr, ih]
      split
      · rfl
      · rename_i hNot
        exact absurd ⟨hC, hty, hcomm, hcap⟩ hNot
  | balanced hty hcap =>
      simp only [denoteExpr]
      split
      · rfl
      · rename_i hNot
        exact absurd ⟨hty, hcap⟩ hNot
  | tanner hty hcomm hcap =>
      simp only [denoteExpr]
      split
      · rfl
      · rename_i hNot
        exact absurd ⟨hty, hcomm, hcap⟩ hNot
  | tile hty hcomm hcap =>
      simp only [denoteExpr]
      split
      · rfl
      · rename_i hNot
        exact absurd ⟨hty, hcomm, hcap⟩ hNot
  | nested hty hcomm hcap =>
      simp only [denoteExpr]
      split
      · rfl
      · rename_i hNot
        exact absurd ⟨hty, hcomm, hcap⟩ hNot
  | cone hty hcomm hcap =>
      simp only [denoteExpr]
      split
      · rfl
      · rename_i hNot
        exact absurd ⟨hty, hcomm, hcap⟩ hNot
  | empty => rfl
  | free hty =>
      simp only [denoteExpr]
      split
      · rfl
      · rename_i hNot
        exact absurd hty hNot
  | pullback h1 h2 hI hty hm1 hm2 hcomm hcap _ _ _ ih1 ih2 ihI =>
      simp only [denoteExpr, ih1, ih2, ihI]
      split
      · rfl
      · rename_i hNot
        exact absurd ⟨h1, h2, hI, hty, hm1, hm2, hcomm, hcap⟩ hNot
  | pushout h1 h2 hS hty hm1 hm2 hcomm hcap _ _ _ ih1 ih2 ihS =>
      simp only [denoteExpr, ih1, ih2, ihS]
      split
      · rfl
      · rename_i hNot
        exact absurd ⟨h1, h2, hS, hty, hm1, hm2, hcomm, hcap⟩ hNot
  | liftTable hG hA hB hcap =>
      simp only [denoteExpr]
      split
      · rfl
      · rename_i hNot
        exact absurd ⟨hG, hA, hB, hcap⟩ hNot
  | twoblockTable hG ha hb hcap =>
      simp only [denoteExpr]
      split
      · rfl
      · rename_i hNot
        exact absurd ⟨hG, ha, hb, hcap⟩ hNot
  | balancedTable hty hcap =>
      simp only [denoteExpr]
      split
      · rfl
      · rename_i hNot
        exact absurd ⟨hty, hcap⟩ hNot
  | pairPartition hty hcomm hcap =>
      simp only [denoteExpr]
      split
      · rfl
      · rename_i hNot
        exact absurd ⟨hty, hcomm, hcap⟩ hNot
  | ppScale h0 hty hcomm hcap _ ih0 =>
      simp only [denoteExpr, ih0]
      split
      · rfl
      · rename_i hNot
        exact absurd ⟨h0, hty, hcomm, hcap⟩ hNot


/-- The denotation's `some` branch has a derivation (spec §1a). -/
theorem denoteExpr_some_eval : ∀ (e : StateExpr) (s : CodeState),
    denoteExpr e = some s → EvalExpr e s := by
  intro e
  induction e with
  | base t =>
      intro s hEq
      simp only [denoteExpr] at hEq
      cases hEq
      exact EvalExpr.base _
  | directSum e1 e2 ih1 ih2 =>
      intro s hEq
      simp only [denoteExpr] at hEq
      cases h1 : denoteExpr e1
      · simp only [h1] at hEq
        exact absurd hEq (by simp)
      · rename_i s1
        cases h2 : denoteExpr e2
        · simp only [h1, h2] at hEq
          exact absurd hEq (by simp)
        · rename_i s2
          simp only [h1, h2] at hEq
          split at hEq
          · rename_i hDisj
            obtain ⟨hQ, hU⟩ := hDisj
            cases hEq
            exact EvalExpr.directSum hQ hU (ih1 s1 h1) (ih2 s2 h2)
          · exact absurd hEq (by simp)
  | glue e1 e2 seams ih1 ih2 =>
      intro s hEq
      simp only [denoteExpr] at hEq
      cases h1 : denoteExpr e1
      · simp only [h1] at hEq
        exact absurd hEq (by simp)
      · rename_i s1
        cases h2 : denoteExpr e2
        · simp only [h1, h2] at hEq
          exact absurd hEq (by simp)
        · rename_i s2
          simp only [h1, h2] at hEq
          split at hEq
          · rename_i hDisj
            obtain ⟨hQ, hU, hwf, hcap⟩ := hDisj
            cases hEq
            exact EvalExpr.glue hQ hU hwf hcap (ih1 s1 h1) (ih2 s2 h2)
          · exact absurd hEq (by simp)
  | hgp H1 H2 =>
      intro s hEq
      simp only [denoteExpr] at hEq
      split at hEq
      · rename_i hP
        obtain ⟨h1, h2, hcap⟩ := hP
        cases hEq
        exact EvalExpr.hgp h1 h2 hcap
      · exact absurd hEq (by simp)
  | lift orders A B =>
      intro s hEq
      simp only [denoteExpr] at hEq
      split at hEq
      · rename_i hP
        obtain ⟨hG, hA, hB, hcap⟩ := hP
        cases hEq
        exact EvalExpr.lift hG hA hB hcap
      · exact absurd hEq (by simp)
  | twoblock orders a b =>
      intro s hEq
      simp only [denoteExpr] at hEq
      split at hEq
      · rename_i hP
        obtain ⟨hG, ha, hb, hcap⟩ := hP
        cases hEq
        exact EvalExpr.twoblock hG ha hb hcap
      · exact absurd hEq (by simp)
  | concat eO eI blocks repsX repsZ ih1 ih2 =>
      intro s hEq
      simp only [denoteExpr] at hEq
      cases h1 : denoteExpr eO
      · simp only [h1] at hEq
        exact absurd hEq (by simp)
      · rename_i sO
        cases h2 : denoteExpr eI
        · simp only [h1, h2] at hEq
          exact absurd hEq (by simp)
        · rename_i sI
          simp only [h1, h2] at hEq
          split at hEq
          · rename_i hP
            obtain ⟨hO, hI, hty, hcap⟩ := hP
            cases hEq
            exact EvalExpr.concat hO hI hty hcap (ih1 sO h1) (ih2 sI h2)
          · exact absurd hEq (by simp)
  | product eA eB ih1 ih2 =>
      intro s hEq
      simp only [denoteExpr] at hEq
      cases h1 : denoteExpr eA
      · simp only [h1] at hEq
        exact absurd hEq (by simp)
      · rename_i sA
        cases h2 : denoteExpr eB
        · simp only [h1, h2] at hEq
          exact absurd hEq (by simp)
        · rename_i sB
          simp only [h1, h2] at hEq
          split at hEq
          · rename_i hP
            obtain ⟨hA, hB, hcap⟩ := hP
            cases hEq
            exact EvalExpr.product hA hB hcap (ih1 sA h1) (ih2 sB h2)
          · exact absurd hEq (by simp)
  | double e wiring conj ih =>
      intro s hEq
      simp only [denoteExpr] at hEq
      cases h1 : denoteExpr e
      · simp only [h1] at hEq
        exact absurd hEq (by simp)
      · rename_i sC
        simp only [h1] at hEq
        split at hEq
        · rename_i hP
          obtain ⟨hC, hty, hcomm, hcap⟩ := hP
          cases hEq
          exact EvalExpr.double hC hty hcomm hcap (ih sC h1)
        · exact absurd hEq (by simp)
  | balanced orders H1 rows1 cols1 H2 rows2 cols2 =>
      intro s hEq
      simp only [denoteExpr] at hEq
      split at hEq
      · rename_i hP
        obtain ⟨hty, hcap⟩ := hP
        cases hEq
        exact EvalExpr.balanced hty hcap
      · exact absurd hEq (by simp)
  | tanner n LX LZ viewsX viewsZ =>
      intro s hEq
      simp only [denoteExpr] at hEq
      split at hEq
      · rename_i hP
        obtain ⟨hty, hcomm, hcap⟩ := hP
        cases hEq
        exact EvalExpr.tanner hty hcomm hcap
      · exact absurd hEq (by simp)
  | tile tiles placements idents removed =>
      intro s hEq
      simp only [denoteExpr] at hEq
      split at hEq
      · rename_i hP
        obtain ⟨hty, hcomm, hcap⟩ := hP
        cases hEq
        exact EvalExpr.tile hty hcomm hcap
      · exact absurd hEq (by simp)
  | nested HX HZ =>
      intro s hEq
      simp only [denoteExpr] at hEq
      split at hEq
      · rename_i hP
        obtain ⟨hty, hcomm, hcap⟩ := hP
        cases hEq
        exact EvalExpr.nested hty hcomm hcap
      · exact absurd hEq (by simp)
  | cone DA DB F1 F0 =>
      intro s hEq
      simp only [denoteExpr] at hEq
      split at hEq
      · rename_i hP
        obtain ⟨hty, hcomm, hcap⟩ := hP
        cases hEq
        exact EvalExpr.cone hty hcomm hcap
      · exact absurd hEq (by simp)
  | empty =>
      intro s hEq
      simp only [denoteExpr] at hEq
      cases hEq
      exact EvalExpr.empty
  | free qs =>
      intro s hEq
      simp only [denoteExpr] at hEq
      split at hEq
      · rename_i hty
        cases hEq
        exact EvalExpr.free hty
      · exact absurd hEq (by simp)
  | pullback e1 e2 eI phi1 phi2 ih1 ih2 ihI =>
      intro s hEq
      simp only [denoteExpr] at hEq
      cases h1 : denoteExpr e1
      · simp only [h1] at hEq
        exact absurd hEq (by simp)
      · rename_i s1
        cases h2 : denoteExpr e2
        · simp only [h1, h2] at hEq
          exact absurd hEq (by simp)
        · rename_i s2
          cases hI : denoteExpr eI
          · simp only [h1, h2, hI] at hEq
            exact absurd hEq (by simp)
          · rename_i sI
            simp only [h1, h2, hI] at hEq
            split at hEq
            · rename_i hP
              obtain ⟨hw1, hw2, hwI, hty, hm1, hm2, hcomm, hcap⟩ := hP
              cases hEq
              exact EvalExpr.pullback hw1 hw2 hwI hty hm1 hm2 hcomm hcap
                (ih1 s1 h1) (ih2 s2 h2) (ihI sI hI)
            · exact absurd hEq (by simp)
  | pushout e1 e2 eS psi1 psi2 ih1 ih2 ihS =>
      intro s hEq
      simp only [denoteExpr] at hEq
      cases h1 : denoteExpr e1
      · simp only [h1] at hEq
        exact absurd hEq (by simp)
      · rename_i s1
        cases h2 : denoteExpr e2
        · simp only [h1, h2] at hEq
          exact absurd hEq (by simp)
        · rename_i s2
          cases hS : denoteExpr eS
          · simp only [h1, h2, hS] at hEq
            exact absurd hEq (by simp)
          · rename_i sS
            simp only [h1, h2, hS] at hEq
            split at hEq
            · rename_i hP
              obtain ⟨hw1, hw2, hwS, hty, hm1, hm2, hcomm, hcap⟩ := hP
              cases hEq
              exact EvalExpr.pushout hw1 hw2 hwS hty hm1 hm2 hcomm hcap
                (ih1 s1 h1) (ih2 s2 h2) (ihS sS hS)
            · exact absurd hEq (by simp)
  | liftTable t A B =>
      intro s hEq
      simp only [denoteExpr] at hEq
      split at hEq
      · rename_i hP
        obtain ⟨hG, hA, hB, hcap⟩ := hP
        cases hEq
        exact EvalExpr.liftTable hG hA hB hcap
      · exact absurd hEq (by simp)
  | twoblockTable t a b =>
      intro s hEq
      simp only [denoteExpr] at hEq
      split at hEq
      · rename_i hP
        obtain ⟨hG, ha, hb, hcap⟩ := hP
        cases hEq
        exact EvalExpr.twoblockTable hG ha hb hcap
      · exact absurd hEq (by simp)
  | balancedTable t H1 rows1 cols1 H2 rows2 cols2 =>
      intro s hEq
      simp only [denoteExpr] at hEq
      split at hEq
      · rename_i hP
        obtain ⟨hty, hcap⟩ := hP
        cases hEq
        exact EvalExpr.balancedTable hty hcap
      · exact absurd hEq (by simp)
  | pairPartition p BX BZ =>
      intro s hEq
      simp only [denoteExpr] at hEq
      split at hEq
      · rename_i hP
        obtain ⟨hty, hcomm, hcap⟩ := hP
        cases hEq
        exact EvalExpr.pairPartition hty hcomm hcap
      · exact absurd hEq (by simp)
  | ppScale e0 P BX BZ ih0 =>
      intro s hEq
      simp only [denoteExpr] at hEq
      cases h0 : denoteExpr e0
      · simp only [h0] at hEq
        exact absurd hEq (by simp)
      · rename_i s0
        simp only [h0] at hEq
        split at hEq
        · rename_i hP
          obtain ⟨hw0, hty, hcomm, hcap⟩ := hP
          cases hEq
          exact EvalExpr.ppScale hw0 hty hcomm hcap (ih0 s0 h0)
        · exact absurd hEq (by simp)


/-- The derived denotation is adequate for the expression relation. -/
theorem denoteExpr_eval {e : StateExpr} {s : CodeState} :
    denoteExpr e = some s ↔ EvalExpr e s :=
  ⟨denoteExpr_some_eval e s, eval_denoteExpr⟩

/-- Every derivation yields the denotation's `some` branch (spec §1a). -/
theorem eval_denote {m : Command} {s s' : CodeState}
    (h : Eval m s s') : denote m s = some s' := by
  induction h with
  | skip s => rfl
  | seq _ _ ih1 ih2 => simp only [denote, ih1, ih2]
  | delete hgen hind hs' =>
      simp only [denote]
      split
      · rw [hs']
      · rename_i hNot
        exact absurd (And.intro hgen hind) hNot
  | add hSub hNodup hSort hComm hSpan hs' hcap =>
      simp only [denote]
      split
      · rw [hs']
      · rename_i hNot
        exact absurd (⟨hSub, hNodup, hSort, hComm, hSpan, hcap⟩) hNot
  | graft hq hopp htouch hlen hnodup hids hcov hk hs' hcap =>
      simp only [denote]
      split
      · rw [hs']
      · rename_i hNot
        exact absurd (⟨hq, hopp, htouch, hlen, hnodup, hids, hcov, hk, hcap⟩) hNot
  | rebase hne hok hs' hwf hcap =>
      simp only [denote]
      split
      · rw [hs']
      · rename_i hNot
        rw [← hs'] at hNot
        exact absurd (⟨hne, hok, hwf, hcap⟩) hNot
  | hadamard hperm hs' hwf =>
      simp only [denote]
      split
      · rw [hs']
      · rename_i hNot
        rw [← hs'] at hNot
        exact absurd (⟨hperm, hwf⟩) hNot
  | hadamardSplit hsub hguard hs' hwf hk hcap =>
      simp only [denote]
      split
      · rename_i hPre
        exact absurd hPre.1 (not_perm_or_nil_of_properSubset hsub)
      · split
        · rw [hs']
        · rename_i _ hNot
          rw [← hs'] at hNot
          exact absurd (⟨hsub, hguard, hwf, hk, hcap⟩) hNot
  | peel hq hrow hlen1 hno hs' hwf =>
      simp only [denote]
      split
      · rw [hs']
      · rename_i hNot
        rw [← hs'] at hNot
        exact absurd (⟨hq, hrow, hlen1, hno, hwf⟩) hNot
  | puncture hq hs' hwf =>
      simp only [denote]
      split
      · rw [hs']
      · rename_i hNot
        rw [← hs'] at hNot
        exact absurd (⟨hq, hwf⟩) hNot
  | extend hok hs' hwf hcap =>
      simp only [denote]
      split
      · rw [hs']
      · rename_i hNot
        rw [← hs'] at hNot
        exact absurd (⟨hok, hwf, hcap⟩) hNot
  | cnotSwap hok hs' hwf =>
      simp only [denote]
      split
      · rw [hs']
      · rename_i hNot
        rw [← hs'] at hNot
        exact absurd (⟨hok, hwf⟩) hNot
  | split hQAnd hQA hRnd hRdisp hcut hs' =>
      simp only [denote]
      split
      · rw [hs']
      · rename_i hNot
        exact absurd (⟨hQAnd, hQA, hRnd, hRdisp, hcut⟩) hNot

/-- The denotation's `some` branch has a derivation (spec §1a). -/
theorem denote_some_eval : ∀ (m : Command) (s s' : CodeState),
    denote m s = some s' → Eval m s s' := by
  intro m
  induction m with
  | skip =>
      intro s s' hEq
      simp only [denote] at hEq
      cases hEq
      exact Eval.skip s
  | seq m1 m2 ih1 ih2 =>
      intro s s' hEq
      simp only [denote] at hEq
      cases h1 : denote m1 s
      · simp only [h1] at hEq
        exact absurd hEq (by simp)
      · rename_i s1
        simp only [h1] at hEq
        exact Eval.seq (ih1 s s1 h1) (ih2 s1 s' hEq)
  | delete r =>
      intro s s' hEq
      simp only [denote] at hEq
      split at hEq
      · rename_i hPre
        obtain ⟨hgen, hind⟩ := hPre
        cases hEq
        exact Eval.delete hgen hind rfl
      · exact absurd hEq (by simp)
  | addStab sector support =>
      intro s s' hEq
      simp only [denote] at hEq
      split at hEq
      · rename_i hPre
        obtain ⟨hSub, hNodup, hSort, hComm, hSpan, hcap⟩ := hPre
        cases hEq
        exact Eval.add hSub hNodup hSort hComm hSpan rfl hcap
      · exact absurd hEq (by simp)
  | graft qubit sector orderedIds =>
      intro s s' hEq
      simp only [denote] at hEq
      split at hEq
      · rename_i hPre
        obtain ⟨hq, hopp, htouch, hlen, hnodup, hids, hcov, hk, hcap⟩ := hPre
        cases hEq
        exact Eval.graft hq hopp htouch hlen hnodup hids hcov hk rfl hcap
      · exact absurd hEq (by simp)
  | rebase sector matrix =>
      intro s s' hEq
      simp only [denote] at hEq
      split at hEq
      · rename_i hPre
        obtain ⟨hne, hok, hwf, hcap⟩ := hPre
        cases hEq
        exact Eval.rebase hne hok rfl hwf hcap
      · exact absurd hEq (by simp)
  | hadamard T =>
      intro s s' hEq
      simp only [denote] at hEq
      split at hEq
      · rename_i hPre
        obtain ⟨hperm, hwf⟩ := hPre
        cases hEq
        exact Eval.hadamard hperm rfl hwf
      · split at hEq
        · rename_i _ hPre
          obtain ⟨hsub, hguard, hwf, hk, hcap⟩ := hPre
          cases hEq
          exact Eval.hadamardSplit hsub hguard rfl hwf hk hcap
        · exact absurd hEq (by simp)
  | peel q tau r_id =>
      intro s s' hEq
      simp only [denote] at hEq
      split at hEq
      · rename_i hPre
        obtain ⟨hq, hrow, hlen1, hno, hwf⟩ := hPre
        cases hEq
        exact Eval.peel hq hrow hlen1 hno rfl hwf
      · exact absurd hEq (by simp)
  | puncture q =>
      intro s s' hEq
      simp only [denote] at hEq
      split at hEq
      · rename_i hPre
        obtain ⟨hq, hwf⟩ := hPre
        cases hEq
        exact Eval.puncture hq rfl hwf
      · exact absurd hEq (by simp)
  | extend delta adds =>
      intro s s' hEq
      simp only [denote] at hEq
      split at hEq
      · rename_i hPre
        obtain ⟨hok, hwf, hcap⟩ := hPre
        cases hEq
        exact Eval.extend hok rfl hwf hcap
      · exact absurd hEq (by simp)
  | cnotSwap U =>
      intro s s' hEq
      simp only [denote] at hEq
      split at hEq
      · rename_i hPre
        obtain ⟨hok, hwf⟩ := hPre
        cases hEq
        exact Eval.cnotSwap hok rfl hwf
      · exact absurd hEq (by simp)
  | split QA R =>
      intro s s' hEq
      simp only [denote] at hEq
      split at hEq
      · rename_i hPre
        obtain ⟨hQAnd, hQA, hRnd, hRdisp, hcut⟩ := hPre
        cases hEq
        exact Eval.split hQAnd hQA hRnd hRdisp hcut rfl
      · exact absurd hEq (by simp)

/-- The derived denotation is adequate for the command relation:
    `⟦m⟧(S) = some S'` iff `Eval(m, S, S')` (spec §1a). -/
theorem denote_eval {m : Command} {s s' : CodeState} :
    denote m s = some s' ↔ Eval m s s' :=
  ⟨denote_some_eval m s s', eval_denote⟩

/-- Determinism of `Eval`: a command has at most one output state. This is the
    single-valuation property that makes the derived denotation well-posed
    (spec §1a; `OBL-PRIMITIVE-DETERMINISM` asks for one lemma per primitive,
    and this covers every command at once). Proved by induction on the
    derivation rather than through `denote_eval`, so that it does not inherit
    the denotation's `Classical.choice` footprint. -/
theorem eval_unique {m : Command} {s s1 s2 : CodeState}
    (h1 : Eval m s s1) (h2 : Eval m s s2) : s1 = s2 := by
  induction h1 generalizing s2 with
  | skip => cases h2; rfl
  | seq _ _ ih1 ih2 =>
      cases h2 with
      | seq h2a h2b =>
          have hmid := ih1 h2a
          subst hmid
          exact ih2 h2b
  | delete _ _ heq1 =>
      cases h2 with
      | delete _ _ heq2 => rw [heq1, heq2]
  | add _ _ _ _ _ heq1 =>
      cases h2 with
      | add _ _ _ _ _ heq2 => rw [heq1, heq2]
  | graft _ _ _ _ _ _ _ _ heq1 =>
      cases h2 with
      | graft _ _ _ _ _ _ _ _ heq2 => rw [heq1, heq2]
  | rebase _ _ heq1 _ =>
      cases h2 with
      | rebase _ _ heq2 _ => rw [heq1, heq2]
  | hadamard hp1 heq1 _ =>
      cases h2 with
      | hadamard _ heq2 _ => rw [heq1, heq2]
      | hadamardSplit hsub _ _ _ _ _ =>
          exact absurd hp1 (not_perm_or_nil_of_properSubset hsub)
  | hadamardSplit hsub _ heq1 _ _ _ =>
      cases h2 with
      | hadamard hp2 _ _ =>
          exact absurd hp2 (not_perm_or_nil_of_properSubset hsub)
      | hadamardSplit _ _ heq2 _ _ _ => rw [heq1, heq2]
  | peel _ _ _ _ heq1 _ =>
      cases h2 with
      | peel _ _ _ _ heq2 _ => rw [heq1, heq2]
  | puncture _ heq1 _ =>
      cases h2 with
      | puncture _ heq2 _ => rw [heq1, heq2]
  | extend _ heq1 _ =>
      cases h2 with
      | extend _ heq2 _ => rw [heq1, heq2]
  | cnotSwap _ heq1 _ =>
      cases h2 with
      | cnotSwap _ heq2 _ => rw [heq1, heq2]
  | split _ _ _ _ _ heq1 =>
      cases h2 with
      | split _ _ _ _ _ heq2 => rw [heq1, heq2]

/-- Sequencing associates in the derived denotation (spec §1a;
    `OBL-SEQUENCE-ASSOCIATIVITY` WP4 slice). -/
theorem denote_seq_assoc (m1 m2 m3 : Command) (s : CodeState) :
    denote (Command.seq (Command.seq m1 m2) m3) s =
    denote (Command.seq m1 (Command.seq m2 m3)) s := by
  simp only [denote]
  cases h1 : denote m1 s with
  | none => simp
  | some s1 =>
      cases h2 : denote m2 s1 with
      | none => simp [h2]
      | some s2 => simp [h2]

/-- A state with two identical X rows: deleting either row is not derivable,
    because the row is in the span of the other. -/
def dupState : CodeState :=
  { Q := [0, 1]
  , rows := [⟨1, Sector.X, [0]⟩, ⟨2, Sector.X, [0]⟩]
  , used := [1, 2] }

theorem not_eval_delete_dup :
    ¬ Eval (Command.delete 1) dupState (deleteState dupState 1) := by
  intro h
  cases h with
  | delete _ hi _ =>
      apply hi
      refine ⟨[true], ?_⟩
      constructor
      · rfl
      · simp [combineRows, xorVec, rowVector, dupState]

/-- The empty two-qubit state: no displayed rows at all. -/
def emptyTwoQubits : CodeState :=
  { Q := [0, 1]
  , rows := []
  , used := [] }

/-- Positive instance: adding a Z line on qubit 0 to the empty two-qubit state
    is derivable. With no displayed rows the commutation and independence
    premises are trivial, and the line passes the row conditions. -/
theorem eval_add_empty :
    Eval (Command.addStab Sector.Z [0]) emptyTwoQubits
        (addState emptyTwoQubits Sector.Z [0]) := by
  refine @Eval.add _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | h
    · simp [emptyTwoQubits]
    · simp at h
  · decide
  · decide
  · intro r hr _
    simp [emptyTwoQubits] at hr
  · intro hspan
    rcases hspan with ⟨hcoeff, hcomb⟩
    obtain hlen := hcomb.1
    cases hcoeff with
    | nil =>
        simp [sectorRows, emptyTwoQubits] at hcomb
        rw [combineRows.eq_1] at hcomb
        simp [rowVector] at hcomb
    | cons _ _ =>
        simp [sectorRows, emptyTwoQubits] at hlen
  · rfl
  · decide

/-- One displayed X row on qubit 0 over two qubits. -/
def anticommuteState : CodeState :=
  { Q := [0, 1]
  , rows := [⟨1, Sector.X, [0]⟩]
  , used := [1] }

/-- Refusal: an anticommuting line fails the commutation premise. The X row on
    qubit 0 intersects the proposed Z line in one qubit, an odd overlap. -/
theorem not_eval_add_anticommute :
    ¬ Eval (Command.addStab Sector.Z [0]) anticommuteState
        (addState anticommuteState Sector.Z [0]) := by
  intro h
  cases h with
  | add _ _ _ hcomm _ _ =>
      have h := hcomm ⟨1, Sector.X, [0]⟩ (by simp [anticommuteState]) rfl
      simp [supportIntersectionSize] at h

/-- A single displayed Z row on the one-qubit state. -/
def zRowState : CodeState :=
  { Q := [0]
  , rows := [⟨1, Sector.Z, [0]⟩]
  , used := [1] }

/-- Refusal: a repeated support is refused even though it commutes. The
    proposed X line `[0, 0]` counts its overlap with the Z row twice (even), so
    only the no-repeat premise rejects it. -/
theorem not_eval_add_dup_support :
    ¬ Eval (Command.addStab Sector.X [0, 0]) zRowState
        (addState zRowState Sector.X [0, 0]) := by
  intro h
  cases h with
  | add _ hnodup _ _ _ _ =>
      simp at hnodup

/-- Refusal: an unsorted support is refused, as `EncodingWellFormed` requires. -/
theorem not_eval_add_unsorted :
    ¬ Eval (Command.addStab Sector.X [1, 0]) emptyTwoQubits
        (addState emptyTwoQubits Sector.X [1, 0]) := by
  intro h
  cases h with
  | add _ _ hsorted _ _ _ =>
      simp at hsorted


/-- Graftable fixture state: Q = {0,...,4}, X rows {0,1} and {0,2,3,4},
    Z rows {0,1,2} and {3,4}. -/
def graftableState : CodeState :=
  { Q := [0, 1, 2, 3, 4]
  , rows := [⟨1, Sector.X, [0, 1]⟩, ⟨2, Sector.X, [0, 2, 3, 4]⟩,
             ⟨3, Sector.Z, [0, 1, 2]⟩, ⟨4, Sector.Z, [3, 4]⟩]
  , used := [1, 2, 3, 4] }

/-- Positive instance: grafting qubit 0 in the X sector with the touching
    chain [1, 2] is derivable. -/
theorem eval_graft_graftable :
    Eval (Command.graft 0 Sector.X [1, 2]) graftableState
        (graftState graftableState 0 Sector.X [1, 2]) := by
  apply Eval.graft
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · rfl
  · decide

/-- A state with no opposite-sector row touching the grafted qubit. -/
def noOppositeState : CodeState :=
  { Q := [0, 1]
  , rows := [⟨1, Sector.X, [0, 1]⟩]
  , used := [1] }

/-- Refusal: a grafted qubit must lie in an opposite-sector row. -/
theorem not_eval_graft_no_opposite :
    ¬ Eval (Command.graft 0 Sector.X [1]) noOppositeState
        (graftState noOppositeState 0 Sector.X [1]) := by
  intro h
  cases h with
  | graft _ hopp _ _ _ _ _ _ _ =>
      rcases hopp with ⟨r, hr, hsec, _⟩
      rcases List.mem_cons.mp hr with rfl | hr'
      · cases hsec
      · simp at hr'

/-- Refusal: a chain that omits a touching row (length mismatch) is refused. -/
theorem not_eval_graft_short_chain :
    ¬ Eval (Command.graft 0 Sector.X [1]) graftableState
        (graftState graftableState 0 Sector.X [1]) := by
  intro h
  cases h with
  | graft _ _ _ hlen _ _ _ _ _ =>
      simp [graftableState, touchingRows] at hlen

/-- Refusal: an unknown identifier in the chain is refused. -/
theorem not_eval_graft_unknown_id :
    ¬ Eval (Command.graft 0 Sector.X [1, 99]) graftableState
        (graftState graftableState 0 Sector.X [1, 99]) := by
  intro h
  cases h with
  | graft _ _ _ _ _ hid _ _ _ =>
      have := hid 99 (by decide)
      simp [graftableState, touchingRows] at this

/-- Pinned fact: the corrected rank uses xor, so duplicate masks collapse. -/
theorem rankBitmasks_duplicates :
    rankBitmasks [1, 1] = 1 ∧ rankBitmasks [3, 1, 2] = 2 := by
  decide

namespace GlobalHadamard

/-- The sector opposite to a given sector is involutive. -/
theorem oppositeSector_involutive (σ : Sector) : oppositeSector (oppositeSector σ) = σ := by
  cases σ <;> rfl

/-- Global Hadamard (`T = Q`): swap the sector label of every displayed row.
    Supports and identifiers are unchanged. Splitting along all qubits is
    automatic, so this is the unconditional CSS-model instance of the local
    Hadamard. -/
def hadamardState (s : CodeState) : CodeState :=
  { Q := s.Q
  , rows := s.rows.map (fun r =>
      ({ id := r.id, sector := oppositeSector r.sector, support := r.support } : Row))
  , used := s.used }

/-- `Q` is unchanged by the global Hadamard. -/
theorem hadamardState_Q (s : CodeState) : (hadamardState s).Q = s.Q := by
  rfl

/-- `used` is unchanged by the global Hadamard. -/
theorem hadamardState_used (s : CodeState) : (hadamardState s).used = s.used := by
  rfl

/-- Extensionality for `CodeState` (manual, since no `@[ext]` lemma is
    generated). -/
theorem codeState_ext (a b : CodeState)
    (hQ : a.Q = b.Q) (hr : a.rows = b.rows) (hu : a.used = b.used) :
    a = b := by
  cases a; cases b; simp_all

/-- A single displayed row is restored by two sector swaps. -/
theorem hadamardRow_involutive (r : Row) :
    { id := r.id, sector := oppositeSector (oppositeSector r.sector),
      support := r.support } = r := by
  cases r
  rename_i id sector support
  have hs : oppositeSector (oppositeSector sector) = sector :=
    oppositeSector_involutive sector
  simp [hs]

/-- The global Hadamard is an involution on states. -/
theorem hadamardState_involutive (s : CodeState) :
    hadamardState (hadamardState s) = s := by
  apply codeState_ext
  · exact (hadamardState_Q (hadamardState s)).trans (hadamardState_Q s)
  · -- rows: two sector swaps restore the list
    have hrows : List.map (fun r =>
        { id := r.id, sector := oppositeSector (oppositeSector r.sector),
          support := r.support }) s.rows = s.rows := by
      induction s.rows with
      | nil => rfl
      | cons r rs ih =>
          have hr := hadamardRow_involutive r
          simp [hr, ih]
    -- (hadamardState (hadamardState s)).rows = map (swap∘swap) s.rows
    have hunfold : (hadamardState (hadamardState s)).rows =
        List.map (fun r =>
          { id := r.id, sector := oppositeSector (oppositeSector r.sector),
            support := r.support }) s.rows := by
      simp [hadamardState, List.map_map]
    rw [hunfold, hrows]
  · exact (hadamardState_used (hadamardState s)).trans (hadamardState_used s)

/-- Sector rank is exchanged by the global Hadamard: the new `σ`-sector rank
    equals the old opposite-sector rank. -/
theorem hadamardState_sectorRank (s : CodeState) (σ : Sector) :
    sectorRank s.Q (hadamardState s).rows σ =
      sectorRank s.Q s.rows (oppositeSector σ) := by
  unfold sectorRank hadamardState
  -- The filtered swapped list equals the swapped filtered list.
  have inner :
      List.filter (fun (r : Row) => r.sector = σ)
        (List.map (fun (r : Row) =>
          ({ id := r.id, sector := oppositeSector r.sector,
             support := r.support } : Row)) s.rows) =
      List.map (fun (r : Row) =>
          ({ id := r.id, sector := oppositeSector r.sector,
             support := r.support } : Row))
        (List.filter (fun (r : Row) => oppositeSector r.sector = σ) s.rows) := by
    apply List.filter_map
  -- Push the outer rowBitmask map through.
  rw [inner]
  -- rowBitmask ignores the sector field.
  have hmask : ∀ (r : Row),
      rowBitmask s.Q ({ id := r.id, sector := oppositeSector r.sector,
                        support := r.support } : Row) =
      rowBitmask s.Q r := by
    intro r
    unfold rowBitmask
    rfl
  -- Rewrite the mapped list.
  have hmap :
      List.map (rowBitmask s.Q)
        (List.map (fun (r : Row) =>
          ({ id := r.id, sector := oppositeSector r.sector,
             support := r.support } : Row))
          (List.filter (fun (r : Row) => oppositeSector r.sector = σ) s.rows)) =
      List.map (rowBitmask s.Q)
        (List.filter (fun (r : Row) => oppositeSector r.sector = σ) s.rows) := by
    induction (List.filter (fun (r : Row) => oppositeSector r.sector = σ) s.rows) with
    | nil => rfl
    | cons r rs ih => simp [hmask r, ih]
  rw [hmap]
  have hfilter : List.filter (fun (r : Row) => oppositeSector r.sector = σ) s.rows =
                 List.filter (fun (r : Row) => r.sector = oppositeSector σ) s.rows := by
    apply List.filter_congr
    intro r _
    have heq : (oppositeSector r.sector = σ) ↔ (r.sector = oppositeSector σ) := by
      constructor
      · intro h
        have := congrArg oppositeSector h
        simpa [oppositeSector_involutive] using this
      · intro h
        rw [h, oppositeSector_involutive σ]
    exact decide_eq_decide.mpr heq
  rw [hfilter]

/-- `k` is preserved by the global Hadamard (sector ranks are exchanged). -/
theorem hadamardState_stateK (s : CodeState) :
    stateK (hadamardState s) = stateK s := by
  unfold stateK
  have hQ : (hadamardState s).Q = s.Q := hadamardState_Q s
  rw [hQ]
  have hX : sectorRank s.Q (hadamardState s).rows Sector.X =
      sectorRank s.Q s.rows Sector.Z := by
    simpa [oppositeSector] using hadamardState_sectorRank s Sector.X
  have hZ : sectorRank s.Q (hadamardState s).rows Sector.Z =
      sectorRank s.Q s.rows Sector.X := by
    simpa [oppositeSector] using hadamardState_sectorRank s Sector.Z
  rw [hX, hZ]
  have hcomm : ∀ (a b c : Nat), a - b - c = a - c - b := by
    intro a b c
    by_cases h1 : a ≥ b + c
    · omega
    · have hb : a - b ≤ c := by omega
      have hc : a - c ≤ b := by omega
      have left0 : a - b - c = 0 := Nat.sub_eq_zero_of_le hb
      have right0 : a - c - b = 0 := Nat.sub_eq_zero_of_le hc
      rw [left0, right0]
  exact hcomm s.Q.length (sectorRank s.Q s.rows Sector.Z)
    (sectorRank s.Q s.rows Sector.X)

end GlobalHadamard

/-! ### Gate 6 conditional-cell transitions: mechanical exactness theorems

The Lean home of the mechanically derivable halves of
`spec/OPERATIONAL_SEMANTICS.md` §4.26–§4.30 that the updates above make
tractable. These are theorems about the transcribed updates; they are
evidence in this development only. -/

/-- Supports of the rows as a weights list. -/
def rowWeights (rows : List Row) : List Nat :=
  rows.map (fun r => r.support.length)

/-- A `swapRow` keeps its support (§4.27: the swaps move sector labels). -/
theorem swapRow_weight (r : Row) : (swapRow r).support.length = r.support.length := by
  rfl

/-- The row-weight list is carried by the sector exchange. -/
theorem rowWeights_swap (rows : List Row) :
    rowWeights (rows.map swapRow) = rowWeights rows := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
      show (swapRow r).support.length :: rowWeights (rs.map swapRow)
            = r.support.length :: rowWeights rs
      rw [swapRow_weight, ih]

/-- The pointwise bridge: the swapped display's sector-test computes to the
    original's opposite-sector test. -/
theorem swapSector_test (sector : Sector) :
    (fun r => decide ((swapRow r).sector = sector))
      = (fun r => decide (r.sector = oppositeSector sector)) := by
  funext r
  show decide (oppositeSector r.sector = sector)
      = decide (r.sector = oppositeSector sector)
  cases r.sector <;> cases sector <;> simp [oppositeSector]

/-- The `- = sector` filter's transfer: through the pointwise bridge, the
    filter of the swapped display at `sector` is the original's
    opposite-sector filter. -/
theorem sector_swap_filter (sector : Sector) (rows : List Row) :
    ((rows.map swapRow).filter (fun r => r.sector = sector))
      = (rows.filter (fun r => r.sector = oppositeSector sector)).map swapRow := by
  show List.filter (fun r => decide (r.sector = sector)) (List.map swapRow rows)
      = List.map swapRow (List.filter (fun r => decide (r.sector = oppositeSector sector)) rows)
  rw [List.filter_map]
  -- the composition's predicate now matches, pointwise:
  have comp : ((fun r => decide (r.sector = sector)) ∘ swapRow)
      = (fun r => decide (r.sector = oppositeSector sector)) := by
    funext r
    exact congrFun (swapSector_test sector) r
  rw [comp]

/-- `rowBitmask` is unaffected by the sector swap (it reads only the support). -/
theorem rowBitmask_swap (Q : List Nat) (r : Row) :
    rowBitmask Q (swapRow r) = rowBitmask Q r := rfl

/-- The sector rank exchanges under the swap (§4.27). -/
theorem sectorRank_swap (Q : List Nat) (rows : List Row) (sector : Sector) :
    sectorRank Q (rows.map swapRow) sector
      = sectorRank Q rows (oppositeSector sector) := by
  unfold sectorRank
  rw [sector_swap_filter, List.map_map]
  congr 1

/-- The logical dimension `k` is preserved by the sector exchange (§4.27). -/
theorem stateK_swap (s : CodeState) : stateK (swapState s) = stateK s := by
  show s.Q.length - sectorRank s.Q (s.rows.map swapRow) Sector.X
        - sectorRank s.Q (s.rows.map swapRow) Sector.Z
      = s.Q.length - sectorRank s.Q s.rows Sector.X - sectorRank s.Q s.rows Sector.Z
  rw [sectorRank_swap, sectorRank_swap]
  show s.Q.length - sectorRank s.Q s.rows Sector.Z - sectorRank s.Q s.rows Sector.X
      = s.Q.length - sectorRank s.Q s.rows Sector.X - sectorRank s.Q s.rows Sector.Z
  omega

def twoQubitState : CodeState :=
  { Q := [0, 1]
  , rows := [⟨1, Sector.X, [0, 1]⟩]
  , used := [1] }

/-- A hadamard term with a subset strictly between ∅ and Q is refused when the
    row spaces do not split along it: `T = [0]` is neither `Q` nor `[]`, and
    the splitting guard fails (`{0} ∉ span{{0,1}}`; OPERATIONAL_SEMANTICS.md
    §4.27). The refusal holds for every candidate child. -/
theorem not_eval_hadamard_subset (s' : CodeState) :
    ¬ Eval (Command.hadamard [0]) twoQubitState s' := by
  intro h
  cases h with
  | hadamard h1 _ _ =>
      rcases h1 with hfl | hn
      · exact absurd hfl.length_eq (by decide)
      · exact absurd hn (by decide)
  | hadamardSplit _ hguard _ _ _ _ =>
      exact absurd hguard (by decide)

/-- A split-subset example (issue #571): the Z display `{0,1,3,4}`, `{1,2}`,
    `{3,4}`, `{4,5}` splits along `T = {0,1,2}`. -/
def splitExampleState : CodeState :=
  { Q := [0, 1, 2, 3, 4, 5]
  , rows := [⟨1, Sector.Z, [0, 1, 3, 4]⟩, ⟨2, Sector.Z, [1, 2]⟩,
             ⟨3, Sector.Z, [3, 4]⟩, ⟨4, Sector.Z, [4, 5]⟩]
  , used := [1, 2, 3, 4] }

/-- The canonical update on the example: the mixed row's outer piece `{3,4}`
    is dependent on the pure `Z` rows and is dropped; its inner piece `{0,1}`
    inherits identifier `1` in the `X` sector; nothing is minted. -/
theorem splitHadamardState_example :
    splitHadamardState splitExampleState [0, 1, 2] =
      { Q := [0, 1, 2, 3, 4, 5]
      , rows := [⟨1, Sector.X, [0, 1]⟩, ⟨2, Sector.X, [1, 2]⟩,
                 ⟨3, Sector.Z, [3, 4]⟩, ⟨4, Sector.Z, [4, 5]⟩]
      , used := [1, 2, 3, 4] } := by
  decide

/-- The split-subset example derives. -/
theorem eval_hadamard_split_example :
    Eval (Command.hadamard [0, 1, 2]) splitExampleState
      (splitHadamardState splitExampleState [0, 1, 2]) :=
  Eval.hadamardSplit (by decide) (by decide) rfl
    ((wellFormedBool_iff _).mp (by decide)) (by decide) (by decide)

/-- A minting example: the X display `{0,1}`, `{0,2}`, `{0,1,2}` with
    `T = {0}`: every row is mixed; the first row's inner piece is minted. -/
def splitMintState : CodeState :=
  { Q := [0, 1, 2]
  , rows := [⟨1, Sector.X, [0, 1]⟩, ⟨2, Sector.X, [0, 2]⟩, ⟨3, Sector.X, [0, 1, 2]⟩]
  , used := [1, 2, 3] }

/-- Row `1` keeps `{1}` and mints its inner piece `{0}` (identifier `0`, the
    first natural not in `used`); row `2` keeps `{2}`; row `3` has no kept
    piece and retires. -/
theorem splitHadamardState_mint_example :
    splitHadamardState splitMintState [0] =
      { Q := [0, 1, 2]
      , rows := [⟨1, Sector.X, [1]⟩, ⟨0, Sector.Z, [0]⟩, ⟨2, Sector.X, [2]⟩]
      , used := [1, 2, 3, 0] } := by
  decide

theorem eval_hadamard_split_mint_example :
    Eval (Command.hadamard [0]) splitMintState
      (splitHadamardState splitMintState [0]) :=
  Eval.hadamardSplit (by decide) (by decide) rfl
    ((wellFormedBool_iff _).mp (by decide)) (by decide) (by decide)

/-- A 4-row split example (`Q = {0..6}`, `T = {0, 1, 2}`) where reading rows
    in display order would depend on row order (changing which identifier
    retires and whether a fresh identifier is minted). -/
def splitOrderStateSorted : CodeState :=
  { Q := [0, 1, 2, 3, 4, 5, 6]
  , rows := [⟨0, Sector.X, [0, 3, 4, 5, 6]⟩, ⟨1, Sector.X, [0]⟩,
             ⟨2, Sector.X, [0, 5, 6]⟩, ⟨3, Sector.X, [0, 2, 5, 6]⟩]
  , used := [0, 1, 2, 3] }

def splitOrderStateSwapped : CodeState :=
  { Q := [0, 1, 2, 3, 4, 5, 6]
  , rows := [⟨0, Sector.X, [0, 3, 4, 5, 6]⟩, ⟨1, Sector.X, [0]⟩,
             ⟨3, Sector.X, [0, 2, 5, 6]⟩, ⟨2, Sector.X, [0, 5, 6]⟩]
  , used := [0, 1, 2, 3] }

def splitOrderStateReversed : CodeState :=
  { Q := [0, 1, 2, 3, 4, 5, 6]
  , rows := [⟨3, Sector.X, [0, 2, 5, 6]⟩, ⟨2, Sector.X, [0, 5, 6]⟩,
             ⟨1, Sector.X, [0]⟩, ⟨0, Sector.X, [0, 3, 4, 5, 6]⟩]
  , used := [0, 1, 2, 3] }

/-- Reading rows in identifier order produces the exact same child (no minting,
    `used = [0, 1, 2, 3]`) across sorted, swapped, and reversed parent row
    orders. -/
theorem splitHadamardState_order_invariant_example :
    splitHadamardState splitOrderStateSorted [0, 1, 2] =
      { Q := [0, 1, 2, 3, 4, 5, 6]
      , rows := [⟨0, Sector.X, [3, 4, 5, 6]⟩, ⟨1, Sector.Z, [0]⟩,
                 ⟨2, Sector.X, [5, 6]⟩, ⟨3, Sector.Z, [0, 2]⟩]
      , used := [0, 1, 2, 3] } ∧
    splitHadamardState splitOrderStateSwapped [0, 1, 2] =
      splitHadamardState splitOrderStateSorted [0, 1, 2] ∧
    splitHadamardState splitOrderStateReversed [0, 1, 2] =
      splitHadamardState splitOrderStateSorted [0, 1, 2] := by
  decide

/-- Puncturing a qubit outside the namespace is refused (`q ∈ s.Q` fails). -/
theorem not_eval_puncture_unknown :
    ¬ Eval (Command.puncture 9) twoQubitState
        (punctureState twoQubitState 9) := by
  intro h
  cases h with
  | puncture h1 _ _ =>
      exact absurd h1 (by decide)

/-- A singular rebase matrix is refused: the constructor's `rebaseMatrix_ok`
    premise requires full F_2 rank, and two identical coefficient rows
    collapse to rank 1 over two displayed rows. -/
theorem not_eval_rebase_singular :
    ¬ Eval (Command.rebase Sector.X [[1, 1], [1, 1]])
        graftableState
        (rebaseState graftableState Sector.X [[1, 1], [1, 1]]) := by
  intro h
  cases h with
  | rebase _ hok _ _ =>
      unfold rebaseMatrix_ok at hok
      rcases hok with ⟨_, _, hrank⟩
      exact absurd hrank (by decide)

/-- The empty display is refused (`sectorRows s sector ≠ []` fails). -/
theorem not_eval_rebase_empty :
    ¬ Eval (Command.rebase Sector.X []) emptyTwoQubits
        (rebaseState emptyTwoQubits Sector.X []) := by
  intro h
  cases h with
  | rebase h1 _ _ _ =>
      simp [sectorRows, emptyTwoQubits] at h1




/-- XOR-fold of a list of masks selected by 0/1 coefficients. -/
def combineMasks : List Nat → List Nat → Nat
  | [], _ => 0
  | m :: ms, c :: cs => (if c = 1 then m else 0) ^^^ combineMasks ms cs
  | _ :: _, [] => 0

/-- Span membership for a list of masks. -/
def inSpanMasks (xs : List Nat) (v : Nat) : Prop :=
  ∃ coeffs : List Nat, coeffs.length = xs.length ∧
    (∀ c ∈ coeffs, c = 0 ∨ c = 1) ∧
    combineMasks xs coeffs = v

/-- All 2^k combinations of a list, with duplicates when dependent. -/
def spanList : List Nat → List Nat
  | [] => [0]
  | x :: xs => spanList xs ++ (spanList xs).map (fun v => v ^^^ x)

/-- `combineMasks` over an empty mask list is zero. -/
theorem combineMasks_nil (coeffs : List Nat) : combineMasks [] coeffs = 0 := by
  cases coeffs <;> rfl

/-- A single coefficient selects or drops the head mask. -/
theorem combineMasks_cons (m : Nat) (ms : List Nat) (c : Nat) (cs : List Nat) :
    combineMasks (m :: ms) (c :: cs) = (if c = 1 then m else 0) ^^^ combineMasks ms cs := by
  rfl

/-- `inSpanMasks` of the empty list contains only zero. -/
theorem inSpanMasks_nil (v : Nat) : inSpanMasks [] v ↔ v = 0 := by
  constructor
  · intro h
    rcases h with ⟨coeffs, hlen, _, heq⟩
    cases coeffs with
    | nil =>
        simp [combineMasks] at heq
        exact heq.symm
    | cons _ _ => simp at hlen
  · intro hv
    refine ⟨[], ?_⟩
    constructor
    · rfl
    constructor
    · intro c hc; cases hc
    · simp [combineMasks, hv]

/-- Namespace decrease for peel: the peeled qubit leaves `Q`. -/
theorem peelState_Q_length {s : CodeState} {q r_id : Nat}
    (hq : q ∈ s.Q) (hnd : s.Q.Nodup) :
    (peelState s q r_id).Q.length = s.Q.length - 1 :=
  length_filter_ne_of_nodup_mem hnd hq

/-- The peel evaluation decreases the namespace length by one. -/
theorem peelEval_Q_length {q : Nat} {tau : Sector} {r_id : Nat}
    {s s' : CodeState} (hEval : Eval (Command.peel q tau r_id) s s')
    (hWF : EncodingWellFormed s) :
    s'.Q.length = s.Q.length - 1 := by
  cases hEval with
  | peel hq _ _ _ hs' _ =>
      rw [hs']
      exact peelState_Q_length hq hWF.1

/-- Example states for the `E-GLUE` positive instance (review). -/
def glueExampleA : CodeState :=
  { Q := [0, 1]
  , rows := [⟨1, Sector.X, [0, 1]⟩]
  , used := [1] }

/-- Example states for the `E-GLUE` positive instance (review). -/
def glueExampleB : CodeState :=
  { Q := [2, 3]
  , rows := [⟨2, Sector.X, [2, 3]⟩]
  , used := [2] }

/-- Seam checks for the positive instance: one Z check spanning the union. -/
def glueExampleSeams : List (Sector × List Nat) :=
  [(Sector.Z, [0, 1, 2, 3])]

/-- Seam checks for the refusal instance: a Z check on `[1, 2]` that
    anticommutes with both factor rows. -/
def glueExampleRefusalSeams : List (Sector × List Nat) :=
  [(Sector.Z, [1, 2])]

/-- Positive instance: gluing two disjoint factor states with one seam check
    is derivable. -/
theorem evalExpr_glue_example :
    EvalExpr (StateExpr.glue (StateExpr.base glueExampleA) (StateExpr.base glueExampleB) glueExampleSeams)
      (glueState glueExampleA glueExampleB glueExampleSeams) :=
  EvalExpr.glue (by decide) (by decide) ((wellFormedBool_iff _).mp (by decide)) (by decide)
    (EvalExpr.base _) (EvalExpr.base _)

/-- Refusal: a seam check that anticommutes with the factor rows is refused,
    since `EncodingWellFormed` of the glued state is false. -/
theorem glue_example_refusal_not_well_formed :
    wellFormedBool (glueState glueExampleA glueExampleB glueExampleRefusalSeams) = false := by
  decide

theorem not_encodingWellFormed_glue_example :
    ¬ EncodingWellFormed (glueState glueExampleA glueExampleB glueExampleRefusalSeams) :=
  not_encodingWellFormed_of_bool glue_example_refusal_not_well_formed

/-- Refusal: a seam check that anticommutes with the factor rows is refused,
    since `EncodingWellFormed` of the glued state is false. -/
theorem glue_example_refusal_not_wellFormed :
    ¬ EncodingWellFormed (glueState glueExampleA glueExampleB glueExampleRefusalSeams) :=
  not_encodingWellFormed_glue_example

/-- An `EvalExpr.glue` proof carries `EncodingWellFormed` of its result. -/
theorem evalExpr_glue_implies_wf {e1 e2 : StateExpr}
    {seams : List (Sector × List Nat)} {s : CodeState}
    (h : EvalExpr (StateExpr.glue e1 e2 seams) s) :
    EncodingWellFormed s := by
  cases h with
  | glue hQ hU hwf _ _ _ => exact hwf

/-- Refusal at the `EvalExpr` level: the glued state is not well-formed. -/
theorem not_evalExpr_glue_example :
    ¬ EvalExpr (StateExpr.glue (StateExpr.base glueExampleA) (StateExpr.base glueExampleB) glueExampleRefusalSeams)
      (glueState glueExampleA glueExampleB glueExampleRefusalSeams) := by
  intro h
  exact glue_example_refusal_not_wellFormed (evalExpr_glue_implies_wf h)

/-! ## Capacity alignment (H-4)

The five minting rules carry a capacity premise, so no derivation mints an
identifier at or beyond `totalIdentifiers`: a history inside the finite
enumeration stays inside it under every evaluation. -/

theorem eval_used_within_capacity {m : Command} {s s' : CodeState}
    (h : Eval m s s') (hs : ∀ id ∈ s.used, id < totalIdentifiers) :
    ∀ id ∈ s'.used, id < totalIdentifiers := by
  induction h with
  | skip _ => exact hs
  | seq _ _ ih1 ih2 => exact ih2 (ih1 hs)
  | delete _ _ heq =>
      rw [heq]
      intro id hid
      exact hs id hid
  | add _ _ _ _ _ heq hcap =>
      rw [heq]
      intro id hid
      simp only [addState, List.mem_append, List.mem_singleton] at hid
      rcases hid with h1 | h2
      · exact hs id h1
      · rw [h2]; exact hcap
  | graft _ _ _ _ _ _ _ _ heq hcap =>
      rw [heq]
      intro id hid
      simp only [graftState, List.mem_append] at hid
      rcases hid with h1 | h2
      · exact hs id h1
      · exact hcap id h2
  | rebase _ _ heq _ hcap =>
      rw [heq]
      intro id hid
      simp only [rebaseState, List.mem_append] at hid
      rcases hid with h1 | h2
      · exact hs id h1
      · exact hcap id h2
  | hadamard _ heq _ =>
      rw [heq]
      intro id hid
      unfold hadamardState at hid
      split at hid
      · exact hs id hid
      · simp only [swapState] at hid
        exact hs id hid
  | hadamardSplit _ _ heq _ _ hcap =>
      rw [heq]
      intro id hid
      simp only [splitHadamardState, List.mem_append] at hid
      rcases hid with h1 | h2
      · exact hs id h1
      · exact hcap id h2
  | peel _ _ _ _ heq _ =>
      rw [heq]
      intro id hid
      exact hs id hid
  | puncture _ heq _ =>
      rw [heq]
      intro id hid
      exact hs id hid
  | extend _ heq _ hcap =>
      rw [heq]
      intro id hid
      simp only [extendState, List.mem_append] at hid
      rcases hid with h1 | h2
      · exact hs id h1
      · exact hcap id h2
  | cnotSwap _ heq _ =>
      rw [heq]
      intro id hid
      exact hs id hid
  | split _ _ _ _ _ heq =>
      rw [heq, deleteAll_used]
      exact hs

end CodeCalculus
