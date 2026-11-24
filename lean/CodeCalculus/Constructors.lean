import CodeCalculus.State

/-!
# State updates of the typed constructors

`spec/TERM_LANGUAGE.md` §1 and §2 admit nine expression constructors
(2026-11-11): `L-HGP`, `L-LIFTED`, `L-GROUP-ALGEBRA`, and `A-CONCAT`
, then `A-PRODUCT`, `A-DOUBLE`, `L-BALANCED`, `L-TANNER`, and
`L-TILE`. This module defines their state updates as computable functions,
following the cards of `spec/OPERATIONAL_SEMANTICS.md` §2. The productions
are in `Term.lean` and the rules in `Eval.lean` (`EvalExpr.hgp`,
`EvalExpr.lift`, `EvalExpr.twoblock`, `EvalExpr.concat`).

Each constructor lists natural check rows as vectors over the labels
`0, …, n - 1`, in the index order of its card. `constructedState` is the
retained display of §4.34: the natural rows are read in order from the state
with no rows and no used identifiers, and a row is appended, with the
canonical mint as its identifier, when its vector lies outside the span of
the displayed rows of its sector.

Typed inputs. A binary matrix is a nonempty list of rows of one positive
length. A finite abelian group is the list of its cyclic orders. An element
of the group algebra is a list of exponent tuples with natural-number
exponents, read modulo the orders, a term that occurs an even number of
times cancelling. `A-CONCAT` takes its representatives explicitly, as
supports over the inner labels; the default of the Python consumer
(`tower_level_data`) is a consumer computation and is not mirrored.
-/

namespace CodeCalculus

/-! ## The retained display -/

/-- The support of a vector over the labels `0, …, n - 1`. -/
def supportOfVector (n : Nat) (v : List Bool) : List Nat :=
  (List.range n).filter (fun q => v.getD q false)

/-- One step of the retained display: keep the natural row when its vector
    lies outside the span of the displayed rows of its sector. -/
def retainStep (s : CodeState) (x : Sector × List Nat) : CodeState :=
  if inSpanRowsBool s.Q (s.rows.filter (fun r => r.sector = x.1))
      (s.Q.map (fun q => x.2.contains q)) then s
  else
    { Q := s.Q
    , rows := s.rows ++ [⟨canonicalMint s.used, x.1, x.2⟩]
    , used := s.used ++ [canonicalMint s.used] }

/-- The natural rows of a constructor, as sector and support. -/
def naturalRows (n : Nat) (vs : List (Sector × List Bool)) : List (Sector × List Nat) :=
  vs.map (fun x => (x.1, supportOfVector n x.2))

/-- The state with qubits `0, …, n - 1`, no rows, and no used identifier. -/
def emptyState (n : Nat) : CodeState := { Q := List.range n, rows := [], used := [] }

/-- The state with qubits `0, …, n - 1`, no rows, and initial used identifiers `used0`. -/
def emptyStateWithUsed (n : Nat) (used0 : List Nat) : CodeState :=
  { Q := List.range n, rows := [], used := used0 }

/-- The constructed state: the retained display of the natural rows. -/
def constructedState (n : Nat) (vs : List (Sector × List Bool)) : CodeState :=
  (naturalRows n vs).foldl retainStep (emptyState n)

/-- The constructed state with identifiers canonically minted starting from `used0`. -/
def constructedStateFrom (used0 : List Nat) (n : Nat) (vs : List (Sector × List Bool)) : CodeState :=
  (naturalRows n vs).foldl retainStep (emptyStateWithUsed n used0)

/-! ## Binary matrices and index pairs -/

/-- A nonempty list of rows of one positive length. -/
def binaryMatrixTyped : List (List Bool) → Bool
  | [] => false
  | r :: rs => decide (1 ≤ r.length) && rs.all (fun r' => r'.length == r.length)

/-- The entry of a binary matrix, `false` outside it. -/
def matEntry (M : List (List Bool)) (r c : Nat) : Bool := (M.getD r []).getD c false

/-- The number of columns: the length of the first row. -/
def matCols {α : Type} (M : List (List α)) : Nat := (M.headD []).length

/-- The pairs `(a, b)` with `a < m` and `b < n`, the first index slowest. -/
def indexPairs (m n : Nat) : List (Nat × Nat) :=
  (List.range m).flatMap (fun a => (List.range n).map (fun b => (a, b)))

/-! ## `L-HGP` -/

/-- The natural `X`-row `(a, j)` of `hgp(H₁, H₂)`, over the left qubits
    `(i, j)` and then the right qubits `(a, b)`. -/
def hgpXVector (H1 H2 : List (List Bool)) (aj : Nat × Nat) : List Bool :=
  (indexPairs (matCols H1) (matCols H2)).map
    (fun ij => decide (ij.2 = aj.2) && matEntry H1 aj.1 ij.1) ++
  (indexPairs H1.length H2.length).map
    (fun ab => decide (ab.1 = aj.1) && matEntry H2 ab.2 aj.2)

/-- The natural `Z`-row `(i, b)` of `hgp(H₁, H₂)`. -/
def hgpZVector (H1 H2 : List (List Bool)) (ib : Nat × Nat) : List Bool :=
  (indexPairs (matCols H1) (matCols H2)).map
    (fun ij => decide (ij.1 = ib.1) && matEntry H2 ib.2 ij.2) ++
  (indexPairs H1.length H2.length).map
    (fun ab => decide (ab.2 = ib.2) && matEntry H1 ab.1 ib.1)

/-- The natural rows of `hgp(H₁, H₂)`: the `X`-rows by `(a, j)`, then the
    `Z`-rows by `(i, b)`. -/
def hgpVectors (H1 H2 : List (List Bool)) : List (Sector × List Bool) :=
  (indexPairs H1.length (matCols H2)).map (fun aj => (Sector.X, hgpXVector H1 H2 aj)) ++
  (indexPairs (matCols H1) H2.length).map (fun ib => (Sector.Z, hgpZVector H1 H2 ib))

/-- The number of qubits of `hgp(H₁, H₂)`: `n₁ n₂ + m₁ m₂`. -/
def hgpQubits (H1 H2 : List (List Bool)) : Nat :=
  matCols H1 * matCols H2 + H1.length * H2.length

/-- The state update of `L-HGP`. -/
def hgpState (H1 H2 : List (List Bool)) : CodeState :=
  constructedState (hgpQubits H1 H2) (hgpVectors H1 H2)

/-! ## Finite abelian groups and the group algebra over `F₂` -/

/-- Every cyclic order is positive. -/
def groupTyped (orders : List Nat) : Bool := orders.all (fun o => decide (1 ≤ o))

/-- The elements, as exponent tuples in lexicographic order. -/
def groupElements : List Nat → List (List Nat)
  | [] => [[]]
  | o :: os => (List.range o).flatMap (fun e => (groupElements os).map (fun g => e :: g))

/-- An exponent tuple read modulo the orders. -/
def groupNorm : List Nat → List Nat → List Nat
  | o :: os, x :: xs => (x % o) :: groupNorm os xs
  | _, _ => []

/-- The inverse of a group element. -/
def groupNeg : List Nat → List Nat → List Nat
  | o :: os, x :: xs => ((o - x % o) % o) :: groupNeg os xs
  | _, _ => []

/-- The difference `g - h`. -/
def groupSub : List Nat → List Nat → List Nat → List Nat
  | o :: os, x :: xs, y :: ys => ((x % o + (o - y % o)) % o) :: groupSub os xs ys
  | _, _, _ => []

/-- An algebra element is a list of exponent tuples of the group's rank. -/
def algElementTyped (orders : List Nat) (x : List (List Nat)) : Bool :=
  x.all (fun t => t.length == orders.length)

/-- A nonempty matrix of algebra elements with rows of one positive length. -/
def algMatrixTyped (orders : List Nat) : List (List (List (List Nat))) → Bool
  | [] => false
  | r :: rs =>
      decide (1 ≤ r.length) && rs.all (fun r' => r'.length == r.length) &&
        (r :: rs).all (fun r' => r'.all (algElementTyped orders))

/-- The coefficient of `g` in `x`: the parity of the terms equal to `g`. -/
def algCoeff (orders : List Nat) (x : List (List Nat)) (g : List Nat) : Bool :=
  (x.filter (fun t => groupNorm orders t == g)).length % 2 == 1

/-- The involution that negates every term. -/
def algInv (orders : List Nat) (x : List (List Nat)) : List (List Nat) :=
  x.map (groupNeg orders)

/-- Row `h` of the regular representation `L(x)`: the entry at `h'` is the
    coefficient of `h - h'` in `x`. -/
def regRow (orders : List Nat) (x : List (List Nat)) (h : List Nat) : List Bool :=
  (groupElements orders).map (fun h' => algCoeff orders x (groupSub orders h h'))

/-- The entry of a matrix of algebra elements, the zero element outside it. -/
def algEntry (M : List (List (List (List Nat)))) (r c : Nat) : List (List Nat) :=
  (M.getD r []).getD c []

/-! ## `L-LIFTED` -/

/-- The natural rows of `lift_G(A, B)`: the `X`-rows by `(a, j, h)`, then the
    `Z`-rows by `(i, b, h)`. -/
def liftVectors (orders : List Nat) (A B : List (List (List (List Nat)))) :
    List (Sector × List Bool) :=
  let G := groupElements orders
  let zero := List.replicate G.length false
  let mA := A.length
  let nA := matCols A
  let mB := B.length
  let nB := matCols B
  (indexPairs mA nB).flatMap (fun aj => G.map (fun h => (Sector.X,
    (indexPairs nA nB).flatMap (fun ij =>
      if ij.2 = aj.2 then regRow orders (algEntry A aj.1 ij.1) h else zero) ++
    (indexPairs mA mB).flatMap (fun ab =>
      if ab.1 = aj.1 then regRow orders (algInv orders (algEntry B ab.2 aj.2)) h else zero)))) ++
  (indexPairs nA mB).flatMap (fun ib => G.map (fun h => (Sector.Z,
    (indexPairs nA nB).flatMap (fun ij =>
      if ij.1 = ib.1 then regRow orders (algEntry B ib.2 ij.2) h else zero) ++
    (indexPairs mA mB).flatMap (fun ab =>
      if ab.2 = ib.2 then regRow orders (algInv orders (algEntry A ab.1 ib.1)) h else zero))))

/-- The number of qubits of `lift_G(A, B)`: `ℓ (n_A n_B + m_A m_B)`. -/
def liftQubits (orders : List Nat) (A B : List (List (List (List Nat)))) : Nat :=
  (groupElements orders).length * (matCols A * matCols B + A.length * B.length)

/-- The state update of `L-LIFTED`. -/
def liftState (orders : List Nat) (A B : List (List (List (List Nat)))) : CodeState :=
  constructedState (liftQubits orders A B) (liftVectors orders A B)

/-! ## `L-GROUP-ALGEBRA` -/

/-- The natural rows of `twoblock_G(a, b)`: the rows of `[L(a) | L(b)]`, then
    the rows of `[L(b)ᵀ | L(a)ᵀ]`, with `L(x)ᵀ = L(x*)`. -/
def twoblockVectors (orders : List Nat) (a b : List (List Nat)) : List (Sector × List Bool) :=
  let G := groupElements orders
  G.map (fun h => (Sector.X, regRow orders a h ++ regRow orders b h)) ++
  G.map (fun h => (Sector.Z,
    regRow orders (algInv orders b) h ++ regRow orders (algInv orders a) h))

/-- The number of qubits of `twoblock_G(a, b)`: `2ℓ`. -/
def twoblockQubits (orders : List Nat) : Nat := 2 * (groupElements orders).length

/-- The state update of `L-GROUP-ALGEBRA`. -/
def twoblockState (orders : List Nat) (a b : List (List Nat)) : CodeState :=
  constructedState (twoblockQubits orders) (twoblockVectors orders a b)

/-! ## `A-CONCAT` -/

/-- The typing of `concat(e_O, e_I; blocks)` with explicit representatives,
    for an outer state `O` and an inner state `I`: there are `k_in ≥ 1`
    representatives per sector with `k_in = n_in - |rows of I|`; the blocks
    are `k_in`-tuples that partition the outer labels; every representative
    is a repeat-free support over the inner labels that commutes with the
    inner rows of the opposite sector; and the two families are dual. -/
def concatTyped (O I : CodeState) (blocks repsX repsZ : List (List Nat)) : Bool :=
  let k := repsX.length
  decide (1 ≤ k) && repsZ.length == k &&
  I.Q.length == I.rows.length + k &&
  blocks.all (fun B => B.length == k) &&
  decide blocks.flatten.Nodup &&
  blocks.flatten.all (fun q => O.Q.contains q) &&
  O.Q.all (fun q => blocks.flatten.contains q) &&
  (repsX ++ repsZ).all (fun sup => decide sup.Nodup && sup.all (fun q => I.Q.contains q)) &&
  repsX.all (fun sup => I.rows.all (fun r =>
    r.sector == Sector.X || supportIntersectionSize sup r.support % 2 == 0)) &&
  repsZ.all (fun sup => I.rows.all (fun r =>
    r.sector == Sector.Z || supportIntersectionSize sup r.support % 2 == 0)) &&
  (List.range k).all (fun p => (List.range k).all (fun p' =>
    (supportIntersectionSize (repsX.getD p []) (repsZ.getD p' []) % 2 == 1) == (p == p')))

/-- The natural rows of `concat`: every inner row on every copy, copy by
    copy, then every outer row lifted block by block through the
    representatives of its sector. -/
def concatVectors (O I : CodeState) (blocks repsX repsZ : List (List Nat)) :
    List (Sector × List Bool) :=
  let nb := blocks.length
  let zero := List.replicate I.Q.length false
  let repVectors : Sector → List (List Bool) := fun σ =>
    (match σ with | Sector.X => repsX | Sector.Z => repsZ).map
      (fun (sup : List Nat) => I.Q.map (fun q => sup.contains q))
  (List.range nb).flatMap (fun j => I.rows.map (fun r => (r.sector,
    (List.range nb).flatMap (fun j' => if j' = j then rowVector I.Q r else zero)))) ++
  O.rows.map (fun r => (r.sector,
    blocks.flatMap (fun B =>
      combineRows I.Q.length (repVectors r.sector) (B.map (fun q => r.support.contains q)))))

/-- The number of qubits of `concat`: `n_in n_out`. -/
def concatQubits (I : CodeState) (blocks : List (List Nat)) : Nat :=
  I.Q.length * blocks.length

/-- The state update of `A-CONCAT`. -/
def concatState (O I : CodeState) (blocks repsX repsZ : List (List Nat)) : CodeState :=
  constructedState (concatQubits I blocks) (concatVectors O I blocks repsX repsZ)

/-! ## The five constructors

`A-PRODUCT`, `A-DOUBLE`, `L-BALANCED`, `L-TANNER`, and `L-TILE`, following
their cards in `spec/OPERATIONAL_SEMANTICS.md` §2. Each lists natural rows
and takes the retained display, as the four above do. `A-DOUBLE`,
`L-TANNER`, and `L-TILE` carry a commutation premise, which the rules of
`Eval.lean` state with `naturalCommuteBool`. -/

/-- The natural rows of the two sectors have pairwise even overlap. -/
def naturalCommuteBool (rows : List (Sector × List Nat)) : Bool :=
  rows.all (fun x => rows.all (fun y =>
    decide (x.1 = y.1) || supportIntersectionSize x.2 y.2 % 2 == 0))

/-! ## `A-PRODUCT` -/

/-- The displayed rows of one sector as a binary matrix over `Q`, in display
    order. -/
def sectorMatrix (s : CodeState) (σ : Sector) : List (List Bool) :=
  (s.rows.filter (fun r => r.sector = σ)).map (rowVector s.Q)

/-- The natural `X`-row `(i, x)` of the product, for a qubit `i` of `A` and
    an `X`-row `x` of `B`. The labels are the pairs (`Z`-row of `A`, `X`-row
    of `B`), then (qubit of `A`, qubit of `B`), then (`X`-row of `A`,
    `Z`-row of `B`); the factors enter through their qubit counts and their
    sector matrices. -/
def productX1 (na nb : Nat) (AX AZ BX BZ : List (List Bool)) (ix : Nat × Nat) : List Bool :=
  (indexPairs AZ.length BX.length).map
    (fun p => decide (p.2 = ix.2) && matEntry AZ p.1 ix.1) ++
  (indexPairs na nb).map (fun p => decide (p.1 = ix.1) && matEntry BX ix.2 p.2) ++
  (indexPairs AX.length BZ.length).map (fun _ => false)

/-- The natural `X`-row `(x, j)`, for an `X`-row `x` of `A` and a qubit `j`
    of `B`. -/
def productX2 (na nb : Nat) (AX AZ BX BZ : List (List Bool)) (xj : Nat × Nat) : List Bool :=
  (indexPairs AZ.length BX.length).map (fun _ => false) ++
  (indexPairs na nb).map (fun p => decide (p.2 = xj.2) && matEntry AX xj.1 p.1) ++
  (indexPairs AX.length BZ.length).map
    (fun p => decide (p.1 = xj.1) && matEntry BZ p.2 xj.2)

/-- The natural `Z`-row `(z, j)`, for a `Z`-row `z` of `A` and a qubit `j`
    of `B`. -/
def productZ1 (na nb : Nat) (AX AZ BX BZ : List (List Bool)) (zj : Nat × Nat) : List Bool :=
  (indexPairs AZ.length BX.length).map
    (fun p => decide (p.1 = zj.1) && matEntry BX p.2 zj.2) ++
  (indexPairs na nb).map (fun p => decide (p.2 = zj.2) && matEntry AZ zj.1 p.1) ++
  (indexPairs AX.length BZ.length).map (fun _ => false)

/-- The natural `Z`-row `(i, z)`, for a qubit `i` of `A` and a `Z`-row `z`
    of `B`. -/
def productZ2 (na nb : Nat) (AX AZ BX BZ : List (List Bool)) (iz : Nat × Nat) : List Bool :=
  (indexPairs AZ.length BX.length).map (fun _ => false) ++
  (indexPairs na nb).map (fun p => decide (p.1 = iz.1) && matEntry BZ iz.2 p.2) ++
  (indexPairs AX.length BZ.length).map
    (fun p => decide (p.2 = iz.2) && matEntry AX p.1 iz.1)

/-- The natural `X`-rows: by `(i, x)`, then by `(x, j)`. -/
def productXVectors (na nb : Nat) (AX AZ BX BZ : List (List Bool)) : List (List Bool) :=
  (indexPairs na BX.length).map (productX1 na nb AX AZ BX BZ) ++
  (indexPairs AX.length nb).map (productX2 na nb AX AZ BX BZ)

/-- The natural `Z`-rows: by `(z, j)`, then by `(i, z)`. -/
def productZVectors (na nb : Nat) (AX AZ BX BZ : List (List Bool)) : List (List Bool) :=
  (indexPairs AZ.length nb).map (productZ1 na nb AX AZ BX BZ) ++
  (indexPairs na BZ.length).map (productZ2 na nb AX AZ BX BZ)

/-- The natural rows of `product(A, B)`: the `X`-rows, then the `Z`-rows. -/
def productVectors (A B : CodeState) : List (Sector × List Bool) :=
  (productXVectors A.Q.length B.Q.length (sectorMatrix A Sector.X) (sectorMatrix A Sector.Z)
    (sectorMatrix B Sector.X) (sectorMatrix B Sector.Z)).map (fun v => (Sector.X, v)) ++
  (productZVectors A.Q.length B.Q.length (sectorMatrix A Sector.X) (sectorMatrix A Sector.Z)
    (sectorMatrix B Sector.X) (sectorMatrix B Sector.Z)).map (fun v => (Sector.Z, v))

/-- The number of qubits of `product(A, B)`:
    `m_Z^A m_X^B + n_A n_B + m_X^A m_Z^B`. -/
def productQubits (A B : CodeState) : Nat :=
  (sectorMatrix A Sector.Z).length * (sectorMatrix B Sector.X).length +
    A.Q.length * B.Q.length +
    (sectorMatrix A Sector.X).length * (sectorMatrix B Sector.Z).length

/-- The state update of `A-PRODUCT`. -/
def productState (A B : CodeState) : CodeState :=
  constructedState (productQubits A B) (productVectors A B)

/-! ## `A-DOUBLE` -/

/-- The typing of a wiring map against a state `C`: one entry per named
    row, every named identifier displayed, and the twisted qubits a
    repeat-free subset of the row's support. -/
def doubleTyped (C : CodeState) (wiring : List (Nat × List Nat)) : Bool :=
  decide (wiring.map Prod.fst).Nodup &&
  wiring.all (fun w => decide w.2.Nodup &&
    C.rows.any (fun r => r.id == w.1 && w.2.all (fun q => r.support.contains q)))

/-- Whether the incidence of row `r` at qubit `q` is twisted. -/
def doubleTwisted (wiring : List (Nat × List Nat)) (r : Row) (q : Nat) : Bool :=
  wiring.any (fun w => w.1 == r.id && w.2.contains q)

/-- The natural rows of `double_{w,s}(C)`: for each displayed row `r`, the
    rows `(r, 0)` and `(r, 1)`, over sheet `0` and then sheet `1`. With
    `conj` the rows of sheet `1` take the opposite sector. -/
def doubleVectors (C : CodeState) (wiring : List (Nat × List Nat)) (conj : Bool) :
    List (Sector × List Bool) :=
  C.rows.flatMap (fun r => [false, true].map (fun t =>
    (if conj && t then (match r.sector with
        | Sector.X => Sector.Z
        | Sector.Z => Sector.X) else r.sector,
     [false, true].flatMap (fun s => C.Q.map (fun q =>
       r.support.contains q && ((t ^^ doubleTwisted wiring r q) == s))))))

/-- The number of qubits of `double_{w,s}(C)`: `2 n_C`. -/
def doubleQubits (C : CodeState) : Nat := 2 * C.Q.length

/-- The state update of `A-DOUBLE`. -/
def doubleState (C : CodeState) (wiring : List (Nat × List Nat)) (conj : Bool) : CodeState :=
  constructedState (doubleQubits C) (doubleVectors C wiring conj)

/-! ## `L-BALANCED` -/

/-- The image of `x` under a permutation given as its list of images. -/
def permApply (p : List Nat) (x : Nat) : Nat := p.getD x 0

/-- The preimage of `y` under a permutation. -/
def permInv (p : List Nat) (y : Nat) : Nat := p.idxOf y

/-- A permutation of `0, …, size - 1`. -/
def permTyped (size : Nat) (p : List Nat) : Bool :=
  p.length == size && decide p.Nodup && p.all (fun x => decide (x < size))

/-- One permutation per cyclic generator, each of order dividing its cyclic
    order, any two commuting. -/
def actionTyped (orders : List Nat) (size : Nat) (perms : List (List Nat)) : Bool :=
  perms.length == orders.length && perms.all (permTyped size) &&
  (perms.zip orders).all (fun po =>
    (List.range size).all (fun x => Nat.repeat (permApply po.1) po.2 x == x)) &&
  perms.all (fun p => perms.all (fun p' => (List.range size).all (fun x =>
    permApply p (permApply p' x) == permApply p' (permApply p x))))

/-- `H[g a, g i] = H[a, i]` for every generator `g`. -/
def equivariantTyped (H : List (List Bool)) (rows cols : List (List Nat)) : Bool :=
  (rows.zip cols).all (fun rc => (List.range H.length).all (fun a =>
    (List.range (matCols H)).all (fun i =>
      matEntry H (permApply rc.1 a) (permApply rc.2 i) == matEntry H a i)))

/-- The typing of `balanced_G(H₁, α₁; H₂, α₂)`, an action given by its row
    permutations and its column permutations. -/
def balancedTyped (orders : List Nat) (H1 : List (List Bool)) (rows1 cols1 : List (List Nat))
    (H2 : List (List Bool)) (rows2 cols2 : List (List Nat)) : Bool :=
  groupTyped orders && binaryMatrixTyped H1 && binaryMatrixTyped H2 &&
  actionTyped orders H1.length rows1 && actionTyped orders (matCols H1) cols1 &&
  actionTyped orders H2.length rows2 && actionTyped orders (matCols H2) cols2 &&
  equivariantTyped H1 rows1 cols1 && equivariantTyped H2 rows2 cols2

/-- The image of `x` under the group element with exponent tuple `g`. -/
def actFwd (perms : List (List Nat)) (g : List Nat) (x : Nat) : Nat :=
  (perms.zip g).foldl (fun u pe => Nat.repeat (permApply pe.1) pe.2 u) x

/-- The image of `y` under the inverse of the group element `g`. -/
def actInv (perms : List (List Nat)) (g : List Nat) (y : Nat) : Nat :=
  (perms.zip g).foldl (fun u pe => Nat.repeat (permInv pe.1) pe.2 u) y

/-- The lesser of two pairs in lexicographic order. -/
def pairMin (a b : Nat × Nat) : Nat × Nat :=
  if a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2) then a else b

/-- The least pair of the orbit of `p` under `g (x, y) = (g x, g⁻¹ y)`. -/
def orbitRep (orders : List Nat) (first second : List (List Nat)) (p : Nat × Nat) :
    Nat × Nat :=
  ((groupElements orders).map (fun g => (actFwd first g p.1, actInv second g p.2))).foldl
    pairMin p

/-- The orbits of the pairs below `(m, n)`, each by its least pair, in the
    order of their least pairs. -/
def orbitReps (orders : List Nat) (first second : List (List Nat)) (m n : Nat) :
    List (Nat × Nat) :=
  (indexPairs m n).filter (fun p => orbitRep orders first second p == p)

/-- The natural rows of `balanced_G(H₁, α₁; H₂, α₂)`: one `X`-row for each
    orbit of the pairs `(a, j)`, then one `Z`-row for each orbit of the
    pairs `(i, b)`, over the orbits of the pairs `(i, j)` and then the
    orbits of the pairs `(a, b)`. -/
def balancedVectors (orders : List Nat) (H1 : List (List Bool))
    (rows1 cols1 : List (List Nat)) (H2 : List (List Bool))
    (rows2 cols2 : List (List Nat)) : List (Sector × List Bool) :=
  let m1 := H1.length
  let n1 := matCols H1
  let m2 := H2.length
  let n2 := matCols H2
  let left := orbitReps orders cols1 cols2 n1 n2
  let right := orbitReps orders rows1 rows2 m1 m2
  (orbitReps orders rows1 cols2 m1 n2).map (fun c => (Sector.X,
    left.map (fun o => ((indexPairs m1 n2).filter (fun p =>
      orbitRep orders rows1 cols2 p == c && p.2 == o.2 && matEntry H1 p.1 o.1)).length
        % 2 == 1) ++
    right.map (fun o => ((indexPairs m1 n2).filter (fun p =>
      orbitRep orders rows1 cols2 p == c && p.1 == o.1 && matEntry H2 o.2 p.2)).length
        % 2 == 1))) ++
  (orbitReps orders cols1 rows2 n1 m2).map (fun c => (Sector.Z,
    left.map (fun o => ((List.range n2).filter (fun j =>
      matEntry H2 c.2 j && orbitRep orders cols1 cols2 (c.1, j) == o)).length % 2 == 1) ++
    right.map (fun o => ((List.range m1).filter (fun a =>
      matEntry H1 a c.1 && orbitRep orders rows1 rows2 (a, c.2) == o)).length % 2 == 1)))

/-- The number of qubits of `balanced_G(H₁, α₁; H₂, α₂)`: the number of
    orbits of the pairs `(i, j)` plus the number of orbits of the pairs
    `(a, b)`. -/
def balancedQubits (orders : List Nat) (H1 : List (List Bool))
    (rows1 cols1 : List (List Nat)) (H2 : List (List Bool))
    (rows2 cols2 : List (List Nat)) : Nat :=
  (orbitReps orders cols1 cols2 (matCols H1) (matCols H2)).length +
    (orbitReps orders rows1 rows2 H1.length H2.length).length

/-- The state update of `L-BALANCED`. -/
def balancedState (orders : List Nat) (H1 : List (List Bool))
    (rows1 cols1 : List (List Nat)) (H2 : List (List Bool))
    (rows2 cols2 : List (List Nat)) : CodeState :=
  constructedState (balancedQubits orders H1 rows1 cols1 H2 rows2 cols2)
    (balancedVectors orders H1 rows1 cols1 H2 rows2 cols2)

/-! ## `L-TANNER` -/

/-- The typing of `tanner(n; Λ_X, Λ_Z; ι_X, ι_Z)`: a positive qubit count,
    two binary matrices, and embeddings that list as many distinct labels
    below `n` as their local code has columns. -/
def tannerTyped (n : Nat) (LX LZ : List (List Bool)) (viewsX viewsZ : List (List Nat)) :
    Bool :=
  decide (1 ≤ n) && binaryMatrixTyped LX && binaryMatrixTyped LZ &&
  viewsX.all (fun v => v.length == matCols LX && decide v.Nodup &&
    v.all (fun q => decide (q < n))) &&
  viewsZ.all (fun v => v.length == matCols LZ && decide v.Nodup &&
    v.all (fun q => decide (q < n)))

/-- A local row read through an embedding. -/
def tannerRow (n : Nat) (view : List Nat) (l : List Bool) : List Bool :=
  (List.range n).map (fun q => (view.zip l).any (fun p => p.1 == q && p.2))

/-- The natural rows of `tanner`: every local `X`-row at every vertex of
    the `X` class, then the same for the `Z` class. -/
def tannerVectors (n : Nat) (LX LZ : List (List Bool)) (viewsX viewsZ : List (List Nat)) :
    List (Sector × List Bool) :=
  viewsX.flatMap (fun v => LX.map (fun l => (Sector.X, tannerRow n v l))) ++
  viewsZ.flatMap (fun v => LZ.map (fun l => (Sector.Z, tannerRow n v l)))

/-- The state update of `L-TANNER`. -/
def tannerState (n : Nat) (LX LZ : List (List Bool)) (viewsX viewsZ : List (List Nat)) :
    CodeState :=
  constructedState n (tannerVectors n LX LZ viewsX viewsZ)

/-! ## `L-TILE` -/

/-- The local rows of one sector of a tile, a tile being its local qubit
    count, its local `X`-row supports, and its local `Z`-row supports. -/
def tileRows (t : Nat × List (List Nat) × List (List Nat)) : Sector → List (List Nat)
  | Sector.X => t.2.1
  | Sector.Z => t.2.2

/-- The typing of `tile(τ; α; β)`: a nonempty tile set of repeat-free local
    supports; a nonempty list of placements, each a tile with one distinct
    site per local qubit; identifications of placed sites; and removed
    checks that name a local row of a placement's tile. -/
def tileTyped (tiles : List (Nat × List (List Nat) × List (List Nat)))
    (placements : List (Nat × List Nat)) (idents : List (Nat × Nat))
    (removed : List (Nat × Sector × Nat)) : Bool :=
  !tiles.isEmpty && !placements.isEmpty &&
  tiles.all (fun t => decide (1 ≤ t.1) && (t.2.1 ++ t.2.2).all (fun sup =>
    decide sup.Nodup && sup.all (fun q => decide (q < t.1)))) &&
  placements.all (fun p => decide (p.1 < tiles.length) &&
    p.2.length == (tiles.getD p.1 (0, [], [])).1 && decide p.2.Nodup) &&
  idents.all (fun e => (placements.flatMap (·.2)).contains e.1 &&
    (placements.flatMap (·.2)).contains e.2) &&
  removed.all (fun x => decide (x.1 < placements.length) &&
    decide (x.2.2 < (tileRows (tiles.getD (placements.getD x.1 (0, [])).1 (0, [], []))
      x.2.1).length))

/-- One identification: the class of the greater representative takes the
    lesser one. -/
def tileMerge (m : List (Nat × Nat)) (e : Nat × Nat) : List (Nat × Nat) :=
  let ru := (m.lookup e.1).getD e.1
  let rv := (m.lookup e.2).getD e.2
  m.map (fun p => if p.2 = max ru rv then (p.1, min ru rv) else p)

/-- Each placed site with the least site of its class. -/
def tileReps (placements : List (Nat × List Nat)) (idents : List (Nat × Nat)) :
    List (Nat × Nat) :=
  idents.foldl tileMerge ((placements.flatMap (·.2)).map (fun s => (s, s)))

/-- The site classes, each by its least site, in increasing order. -/
def tileClasses (placements : List (Nat × List Nat)) (idents : List (Nat × Nat)) :
    List Nat :=
  let reps := tileReps placements idents
  (List.range (reps.foldl (fun b p => max b p.2) 0 + 1)).filter
    (fun s => reps.any (fun p => p.2 == s))

/-- The natural rows of `tile`: placement by placement, the local `X`-rows
    and then the local `Z`-rows that are not removed. A row contains a site
    class when an odd number of its local qubits sit in the class. -/
def tileVectors (tiles : List (Nat × List (List Nat) × List (List Nat)))
    (placements : List (Nat × List Nat)) (idents : List (Nat × Nat))
    (removed : List (Nat × Sector × Nat)) : List (Sector × List Bool) :=
  let reps := tileReps placements idents
  let classes := tileClasses placements idents
  (List.range placements.length).flatMap (fun pos =>
    let pl := placements.getD pos (0, [])
    let t := tiles.getD pl.1 (0, [], [])
    [Sector.X, Sector.Z].flatMap (fun σ =>
      ((List.range (tileRows t σ).length).filter (fun idx =>
        !removed.any (fun x => x.1 == pos && decide (x.2.1 = σ) && x.2.2 == idx))).map
        (fun idx => (σ, classes.map (fun c =>
          (((tileRows t σ).getD idx []).filter (fun q =>
            (reps.lookup (pl.2.getD q 0)).getD 0 == c)).length % 2 == 1)))))

/-- The number of qubits of `tile`: the number of site classes. -/
def tileQubits (placements : List (Nat × List Nat)) (idents : List (Nat × Nat)) : Nat :=
  (tileClasses placements idents).length

/-- The state update of `L-TILE`. -/
def tileState (tiles : List (Nat × List (List Nat) × List (List Nat)))
    (placements : List (Nat × List Nat)) (idents : List (Nat × Nat))
    (removed : List (Nat × Sector × Nat)) : CodeState :=
  constructedState (tileQubits placements idents)
    (tileVectors tiles placements idents removed)

/-! ## `L-NESTED-CSS` -/

/-- The typing of `nested(H_X, H_Z)`: two binary matrices with equally many
    columns. -/
def nestedTyped (HX HZ : List (List Bool)) : Bool :=
  binaryMatrixTyped HX && binaryMatrixTyped HZ && matCols HX == matCols HZ

/-- The natural rows of `nested`: the rows of `H_X` as `X`-rows, then the
    rows of `H_Z` as `Z`-rows. -/
def nestedVectors (HX HZ : List (List Bool)) : List (Sector × List Bool) :=
  HX.map (fun l => (Sector.X, l)) ++ HZ.map (fun l => (Sector.Z, l))

/-- The state update of `L-NESTED-CSS`. -/
def nestedState (HX HZ : List (List Bool)) : CodeState :=
  constructedState (matCols HX) (nestedVectors HX HZ)

/-! ## `L-MAPPING-CONE` -/

def coneTyped (DA DB F1 F0 : List (List Bool)) : Bool :=
  binaryMatrixTyped DA && binaryMatrixTyped DB && binaryMatrixTyped F1 && binaryMatrixTyped F0 &&
  DA.length == F1.length && DB.length == (matCols F1) &&
  F0.length == (matCols DA) && (matCols F0) == (matCols DB)

def coneN (DA DB F1 F0 : List (List Bool)) : Nat :=
  matCols DA + DB.length

def coneVectors (DA DB F1 F0 : List (List Bool)) : List (Sector × List Bool) :=
  (List.range (matCols DB)).map (fun r =>
    (Sector.X,
      (List.range (matCols DA)).map (fun i => matEntry F0 i r) ++
      (List.range DB.length).map (fun j => matEntry DB j r))) ++
  (List.range DA.length).map (fun j =>
    (Sector.Z,
      (List.range (matCols DA)).map (fun i => matEntry DA j i) ++
      (List.range (matCols F1)).map (fun jj => matEntry F1 j jj)))

def coneState (DA DB F1 F0 : List (List Bool)) : CodeState :=
  constructedState (coneN DA DB F1 F0) (coneVectors DA DB F1 F0)

/-! ## `L-EMPTY`, `L-FREE`, `A-PULLBACK`, `A-PUSHOUT` -/

/-- The state update of `L-EMPTY`. -/
def emptyCodeState : CodeState := emptyState 0

/-- The typing of `free(Q)`: a duplicate-free, strictly increasing list of
    qubit labels. -/
def freeTyped (qs : List Nat) : Bool :=
  decide qs.Nodup && decide (qs.Pairwise (· ≤ ·))

/-- The state update of `L-FREE`. -/
def freeState (qs : List Nat) : CodeState :=
  { Q := qs, rows := [], used := [] }

/-- Typing of a total qubit map `dom → cod` given as `(src, dst)` pairs. -/
def qubitMapTyped (phi : List (Nat × Nat)) (dom cod : List Nat) : Bool :=
  phi.all (fun p => dom.contains p.1 && cod.contains p.2) &&
  decide (phi.map Prod.fst).Nodup &&
  dom.all (fun q => (phi.map Prod.fst).contains q)

/-- Whether `phi : src.Q → dst.Q` is a CSS code morphism: the `F₂`-pushforward
    of every displayed row of `src` lies in the same-sector span of `dst`. -/
def cssMorphismBool (src dst : CodeState) (phi : List (Nat × Nat)) : Bool :=
  src.rows.all (fun r =>
    let pushed := dst.Q.map (fun y =>
      (r.support.filter (fun q => (phi.lookup q).getD 0 == y)).length % 2 == 1)
    inSpanRowsBool dst.Q (dst.rows.filter (fun r' => r'.sector == r.sector)) pushed)

/-- The fiber-product qubit pairs `(q₁, q₂)` with `φ₁(q₁) = φ₂(q₂)`. -/
def pullbackPairs (s1 s2 : CodeState) (phi1 phi2 : List (Nat × Nat)) : List (Nat × Nat) :=
  s1.Q.flatMap (fun q1 =>
    (s2.Q.filter (fun q2 => (phi1.lookup q1).getD 0 == (phi2.lookup q2).getD 0)).map
      (fun q2 => (q1, q2)))

/-- Typing of `pullback(e₁, e₂, e_I; φ₁, φ₂)`. -/
def pullbackTyped (s1 s2 sI : CodeState) (phi1 phi2 : List (Nat × Nat)) : Bool :=
  qubitMapTyped phi1 s1.Q sI.Q && qubitMapTyped phi2 s2.Q sI.Q

/-- The natural rows of `pullback`. -/
def pullbackVectors (s1 s2 : CodeState) (phi1 phi2 : List (Nat × Nat)) :
    List (Sector × List Bool) :=
  let pairs := pullbackPairs s1 s2 phi1 phi2
  s1.rows.map (fun r => (r.sector, pairs.map (fun p => r.support.contains p.1))) ++
  s2.rows.map (fun r => (r.sector, pairs.map (fun p => r.support.contains p.2)))

/-- The state update of `A-PULLBACK`. -/
def pullbackState (s1 s2 : CodeState) (phi1 phi2 : List (Nat × Nat)) : CodeState :=
  constructedState (pullbackPairs s1 s2 phi1 phi2).length (pullbackVectors s1 s2 phi1 phi2)

/-- Typing of `pushout(e₁, e₂, e_S; ψ₁, ψ₂)`. -/
def pushoutTyped (s1 s2 sS : CodeState) (psi1 psi2 : List (Nat × Nat)) : Bool :=
  qubitMapTyped psi1 sS.Q s1.Q && qubitMapTyped psi2 sS.Q s2.Q

/-- Each tagged qubit index `0 .. |Q₁| + |Q₂| - 1` paired with its
    equivalence-class representative under `ψ₁(s) ~ ψ₂(s)`. -/
def pushoutReps (s1 s2 sS : CodeState) (psi1 psi2 : List (Nat × Nat)) : List (Nat × Nat) :=
  let n1 := s1.Q.length
  let n2 := s2.Q.length
  let idx1 (q : Nat) : Nat := (s1.Q.findIdx? (· == q)).getD 0
  let idx2 (q : Nat) : Nat := n1 + (s2.Q.findIdx? (· == q)).getD 0
  let pairs := sS.Q.map (fun s => (idx1 ((psi1.lookup s).getD 0), idx2 ((psi2.lookup s).getD 0)))
  pairs.foldl tileMerge ((List.range (n1 + n2)).map (fun i => (i, i)))

/-- The equivalence classes of `Q₁ ⊔_{Q_S} Q₂` in increasing order. -/
def pushoutClasses (s1 s2 sS : CodeState) (psi1 psi2 : List (Nat × Nat)) : List Nat :=
  let reps := pushoutReps s1 s2 sS psi1 psi2
  (List.range (s1.Q.length + s2.Q.length)).filter (fun c => reps.any (fun p => p.2 == c))

/-- The natural rows of `pushout`. -/
def pushoutVectors (s1 s2 sS : CodeState) (psi1 psi2 : List (Nat × Nat)) :
    List (Sector × List Bool) :=
  let n1 := s1.Q.length
  let reps := pushoutReps s1 s2 sS psi1 psi2
  let classes := pushoutClasses s1 s2 sS psi1 psi2
  let idx1 (q : Nat) : Nat := (s1.Q.findIdx? (· == q)).getD 0
  let idx2 (q : Nat) : Nat := n1 + (s2.Q.findIdx? (· == q)).getD 0
  s1.rows.map (fun r => (r.sector, classes.map (fun c =>
    (r.support.filter (fun q => (reps.lookup (idx1 q)).getD 0 == c)).length % 2 == 1))) ++
  s2.rows.map (fun r => (r.sector, classes.map (fun c =>
    (r.support.filter (fun q => (reps.lookup (idx2 q)).getD 0 == c)).length % 2 == 1)))

/-- The state update of `A-PUSHOUT`. -/
def pushoutState (s1 s2 sS : CodeState) (psi1 psi2 : List (Nat × Nat)) : CodeState :=
  constructedState (pushoutClasses s1 s2 sS psi1 psi2).length
    (pushoutVectors s1 s2 sS psi1 psi2)


/-! ## `L-PAIR-PARTITION` and `PP-SCALE` -/

/-- A nonempty rectangular matrix of affine descriptors `(a, b)` with even column
    count `L ≥ 2` and unit slopes `gcd(a, p) = 1`. -/
def affineMatrixTyped (p : Nat) : List (List (Nat × Nat)) → Bool
  | [] => false
  | r :: rs =>
      decide (2 ≤ r.length) && decide (r.length % 2 = 0) &&
      rs.all (fun r' => r'.length == r.length) &&
      (r :: rs).all (fun r' => r'.all (fun ab => decide (Nat.gcd ab.1 p = 1)))

/-- The inverse of a unit `a` modulo `p`, found by search: the least `x < p`
    with `a · x ≡ 1 (mod p)`, and `0` when there is none. -/
def modInv (p a : Nat) : Nat :=
  ((List.range p).find? (fun x => (a * x) % p == 1 % p)).getD 0

/-- The relative affine map of an `X` block `(a_X, b_X)` and a `Z` block
    `(a_Z, b_Z)` in one block column: `A(a_X, b_X) A(a_Z, b_Z)ᵀ = A(α, β)` with
    `α = a_X a_Z⁻¹` and `β = a_Z⁻¹ (b_X - b_Z)` modulo `p`. -/
def relAffine (p : Nat) (x z : Nat × Nat) : Nat × Nat :=
  let zi := modInv p z.1
  ((x.1 * zi) % p, (zi * (x.2 % p + (p - z.2 % p))) % p)

/-- The relative affine maps of an `X` block row and a `Z` block row, one per
    block column. -/
def relAffineRow (p : Nat) (rx rz : List (Nat × Nat)) : List (Nat × Nat) :=
  List.zipWith (relAffine p) rx rz

/-- Every entry of the list occurs an even number of times. A list has this
    property exactly when its positions split into pairs with equal entries. -/
def evenMultiplicity (l : List (Nat × Nat)) : Bool :=
  l.all (fun x => (l.filter (fun y => y == x)).length % 2 == 0)

/-- The pair-partition premise of the `L-PAIR-PARTITION` card (applicability
    (ii)): for every `X` block row and every `Z` block row, the block columns
    split into pairs on which the relative affine maps coincide. -/
def pairPartitionPaired (p : Nat) (BX BZ : List (List (Nat × Nat))) : Bool :=
  BX.all (fun rx => BZ.all (fun rz => evenMultiplicity (relAffineRow p rx rz)))

/-- Typing of `pair_partition(p; B_X, B_Z)`: the shapes and unit slopes of
    applicability (i), and the pair partition of applicability (ii). -/
def pairPartitionTyped (p : Nat) (BX BZ : List (List (Nat × Nat))) : Bool :=
  decide (1 ≤ p) && affineMatrixTyped p BX && affineMatrixTyped p BZ &&
  matCols BX == matCols BZ && pairPartitionPaired p BX BZ

/-- The number of qubits of `pair_partition(p; B_X, B_Z)`: `L · p`. -/
def pairPartitionQubits (p : Nat) (BX : List (List (Nat × Nat))) : Nat :=
  matCols BX * p

/-- Lift row `u < p` of a block row `[(a_0, b_0), …, (a_{L-1}, b_{L-1})]` over
    `L · p` qubits: qubit `(c, v)` at `c · p + v` is `true` iff
    `v = (a_c · u + b_c) mod p`. -/
def affineBlockRow (p : Nat) (row : List (Nat × Nat)) (u : Nat) : List Bool :=
  row.flatMap (fun ab =>
    (List.range p).map (fun v => decide (v = (ab.1 * u + ab.2) % p)))

/-- The natural rows of `pair_partition(p; B_X, B_Z)`. -/
def pairPartitionVectors (p : Nat) (BX BZ : List (List (Nat × Nat))) :
    List (Sector × List Bool) :=
  BX.flatMap (fun r => (List.range p).map (fun u => (Sector.X, affineBlockRow p r u))) ++
  BZ.flatMap (fun s => (List.range p).map (fun u => (Sector.Z, affineBlockRow p s u)))

/-- The state update of `L-PAIR-PARTITION`. -/
def pairPartitionState (p : Nat) (BX BZ : List (List (Nat × Nat))) : CodeState :=
  constructedState (pairPartitionQubits p BX) (pairPartitionVectors p BX BZ)

/-- The state update of `PP-SCALE`: fresh namespace `0 .. L·P - 1`, natural rows
    from the scaled affine blocks at target size `P`, and identifiers canonically
    minted starting from `s0.used`. -/
def ppScaleState (s0 : CodeState) (P : Nat) (BX BZ : List (List (Nat × Nat))) : CodeState :=
  constructedStateFrom s0.used (pairPartitionQubits P BX) (pairPartitionVectors P BX BZ)

/-- Typing and positive-dimension premise (`k' > 0`, i.e. retained independent
    display has strictly fewer rows than `L · P`) for `pp_scale(e; P)`. -/
def ppScaleTyped (s0 : CodeState) (P : Nat) (BX BZ : List (List (Nat × Nat))) : Bool :=
  decide (2 ≤ P) && pairPartitionTyped P BX BZ &&
  decide ((ppScaleState s0 P BX BZ).rows.length < pairPartitionQubits P BX)

/-! ## Retention of factor rows by `A-CONCAT` -/

/-- The natural list of `A-CONCAT` has one entry per inner row per block and
    one per outer row; it says nothing about the retained display, which is
    governed by the independence argument of §4.34. -/
theorem concatVectors_length (O I : CodeState) (blocks repsX repsZ : List (List Nat)) :
    (concatVectors O I blocks repsX repsZ).length =
      blocks.length * I.rows.length + O.rows.length := by
  unfold concatVectors
  simp only [List.length_append, List.length_flatMap, List.length_map, List.map_const',
    List.length_range]
  rw [List.sum_replicate_nat]

end CodeCalculus
