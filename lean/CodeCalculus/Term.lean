import CodeCalculus.State

namespace CodeCalculus

/-- State expressions: a base presented CSS state, or a direct sum of two
    state expressions. Commands are deliberately a separate syntactic
    category (see `spec/TERM_LANGUAGE.md` §1). -/
inductive StateExpr where
  | base : CodeState → StateExpr
  | directSum : StateExpr → StateExpr → StateExpr
  deriving Repr, BEq, DecidableEq

/-- Commands: the kernel primitives plus the admitted conditional graft and the five Gate 6 conditional cells.
    `addStab` carries its sector and support; `graft` carries the grafted
    qubit, the spliced sector, and the ordered list of selected-sector row
    identifiers. Prices are not command arguments. -/
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
  | seq : Command → Command → Command
  deriving Repr, BEq, DecidableEq

/-- A closed construction term: a command applied to a state expression. -/
structure ClosedTerm where
  command : Command
  expr : StateExpr
  deriving Repr, BEq, DecidableEq

end CodeCalculus
