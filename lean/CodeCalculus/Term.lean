import CodeCalculus.State

namespace CodeCalculus

/-- State expressions: a base presented CSS state, a direct sum of two state
    expressions, the nine typed constructors admitted 2026-11-11 (`hgp`,
    `lift`, `twoblock`, `concat`, `product`, `double`, `balanced`, `tanner`,
    `tile`), the three group constructors again with the group given by its
    multiplication table (`liftTable`, `twoblockTable`, `balancedTable`), or
    the Lean rendering of the binary `E-GLUE` transition
    (`glue(e₁, e₂; seams)`), which evaluates both factors to presented states
    first and is the same transition the spec writes as
    `Eval(glue(C_A, C_B; seam checks), C)` (TERM_LANGUAGE.md §2). Commands
    are deliberately a separate syntactic category (see
    `spec/TERM_LANGUAGE.md` §1). -/
inductive StateExpr where
  | base : CodeState → StateExpr
  | directSum : StateExpr → StateExpr → StateExpr
  /-- Lean rendering of the binary `E-GLUE` transition: a state-expression
      constructor beside `⊕`, so that `EvalExpr` evaluates both factors to
      presented states first. On closed terms this is the same transition as
      the spec's `Eval(glue(C_A, C_B; seam checks), C)`; `E-GLUE` has no
      unary grammar production (TERM_LANGUAGE.md §2). -/
  | glue : StateExpr → StateExpr → List (Sector × List Nat) → StateExpr
  /-- `L-HGP`: `hgp(H₁, H₂)`, two binary matrices given row by row
      (TERM_LANGUAGE.md §1). -/
  | hgp : List (List Bool) → List (List Bool) → StateExpr
  /-- `L-LIFTED`: `lift_G(A, B)`, the group by its cyclic orders and two
      matrices of group-algebra elements, an element being a list of
      exponent tuples. -/
  | lift : List Nat → List (List (List (List Nat))) → List (List (List (List Nat))) →
      StateExpr
  /-- `L-GROUP-ALGEBRA`: `twoblock_G(a, b)`. -/
  | twoblock : List Nat → List (List Nat) → List (List Nat) → StateExpr
  /-- `A-CONCAT`: `concat(e_O, e_I; blocks)` with its `X` and `Z`
      representatives given explicitly as supports over the inner labels. -/
  | concat : StateExpr → StateExpr → List (List Nat) → List (List Nat) → List (List Nat) →
      StateExpr
  /-- `A-PRODUCT`: `product(e_A, e_B)`, the CSS tensor product of two
      presented states. -/
  | product : StateExpr → StateExpr → StateExpr
  /-- `A-DOUBLE`: `double_{w,s}(e)`, the wiring as a list of displayed row
      identifiers with their twisted qubits, and the `conjugate` flag. -/
  | double : StateExpr → List (Nat × List Nat) → Bool → StateExpr
  /-- `L-BALANCED`: `balanced_G(H₁, α₁; H₂, α₂)`, the group by its cyclic
      orders, and each action by its row permutations and then its column
      permutations, one per cyclic generator. -/
  | balanced : List Nat → List (List Bool) → List (List Nat) → List (List Nat) →
      List (List Bool) → List (List Nat) → List (List Nat) → StateExpr
  /-- `L-TANNER`: `tanner(n; Λ_X, Λ_Z; ι_X, ι_Z)`. -/
  | tanner : Nat → List (List Bool) → List (List Bool) → List (List Nat) →
      List (List Nat) → StateExpr
  /-- `L-TILE`: `tile(τ; α; β)`, a tile being its local qubit count with
      its local `X`-row and `Z`-row supports, a placement a tile index with
      its sites, and the boundary rules the identified site pairs and the
      removed checks (placement, sector, local row). -/
  | tile : List (Nat × List (List Nat) × List (List Nat)) → List (Nat × List Nat) →
      List (Nat × Nat) → List (Nat × Sector × Nat) → StateExpr
  /-- `L-NESTED-CSS`: `nested(H_X, H_Z)`, two parity-check matrices with
      equally many columns. -/
  | nested : List (List Bool) → List (List Bool) → StateExpr
  /-- `L-MAPPING-CONE`: `cone(D_A, D_B, f_1, f_0)`. -/
  | cone : List (List Bool) → List (List Bool) → List (List Bool) → List (List Bool) → StateExpr
  /-- `L-EMPTY`: `empty`, the 0-qubit empty CSS code. -/
  | empty : StateExpr
  /-- `L-FREE`: `free(Q)`, the check-free CSS code on a finite qubit set. -/
  | free : List Nat → StateExpr
  /-- `A-PULLBACK`: `pullback(e₁, e₂, e_I; φ₁, φ₂)`, fiber product along
      CSS code morphisms. -/
  | pullback : StateExpr → StateExpr → StateExpr → List (Nat × Nat) → List (Nat × Nat) →
      StateExpr
  /-- `A-PUSHOUT`: `pushout(e₁, e₂, e_S; ψ₁, ψ₂)`, amalgamated sum along
      CSS code morphisms. -/
  | pushout : StateExpr → StateExpr → StateExpr → List (Nat × Nat) → List (Nat × Nat) →
      StateExpr
  /-- `L-LIFTED` over a group given by its multiplication table:
      `lift_G(A, B)`, the table row by row on `{0, ..., ℓ - 1}` and two
      matrices of group-algebra elements, an element being a list of group
      elements (`spec/OPERATIONAL_SEMANTICS.md` §2 card and §4.44). -/
  | liftTable : List (List Nat) → List (List (List Nat)) → List (List (List Nat)) →
      StateExpr
  /-- `L-GROUP-ALGEBRA` over a group given by its multiplication table:
      `twoblock_G(a, b)`. -/
  | twoblockTable : List (List Nat) → List Nat → List Nat → StateExpr
  /-- `L-BALANCED` over a group given by its multiplication table:
      `balanced_G(H₁, α₁; H₂, α₂)`, the right action `α₁` and the left
      action `α₂` each by its row permutations and then its column
      permutations, one per group element in the order of the table. -/
  | balancedTable : List (List Nat) → List (List Bool) → List (List Nat) →
      List (List Nat) → List (List Bool) → List (List Nat) → List (List Nat) → StateExpr
  /-- `L-PAIR-PARTITION`: `pair_partition(p; B_X, B_Z)`, paired affine/circulant
      permutation blocks over lift size `p`. -/
  | pairPartition : Nat → List (List (Nat × Nat)) → List (List (Nat × Nat)) → StateExpr
  /-- `PP-SCALE`: `pp_scale(e; P)`, explicit extension of a PP-presented CSS
      state to target lift size `P ≥ 2`. -/
  | ppScale : StateExpr → Nat → List (List (Nat × Nat)) → List (List (Nat × Nat)) →
      StateExpr

  deriving Repr, BEq, DecidableEq

/-- Commands: the kernel primitives plus the admitted conditional graft, the five
    Gate 6 conditional cells, and the admitted separating deletion (`E-SPLIT`,
    2026-11-25). `addStab` carries its sector and support; `graft` carries the
    grafted qubit, the spliced sector, and the ordered list of selected-sector
    row identifiers; `split` carries the qubit block `Q_A` and the cut-row
    identifiers `R`. Prices are not command arguments. -/
inductive Command where
  | skip : Command
  | delete : Nat → Command
  | addStab : Sector → List Nat → Command
  | graft : Nat → Sector → List Nat → Command
  | peel : Nat → Sector → Nat → Command
  | puncture : Nat → Command
  | extend : List Nat → List (Sector × List Nat) → Command
  | hadamard : List Nat → Command
  | rebase : Sector → List (List Nat) → Command
  /-- `C-COLUMN-CNOT`: `cnotSwap(U)`, an invertible binary matrix `U ∈ GL(Q, 2)`
      transforming X-rows by `U⁻¹` and Z-rows by `Uᵀ` while retaining `Q`,
      generator identifiers, and `used` (`spec/OPERATIONAL_SEMANTICS.md` §4.42). -/
  | cnotSwap : List (List Bool) → Command
  | split : List Nat → List Nat → Command
  | seq : Command → Command → Command
  deriving Repr, BEq, DecidableEq

/-- A closed construction term: a command applied to a state expression. -/
structure ClosedTerm where
  command : Command
  expr : StateExpr
  deriving Repr, BEq, DecidableEq

end CodeCalculus
