import Lean
import CodeCalculus.ChoiceFree
import CodeCalculus.State
import CodeCalculus.Invariants
import CodeCalculus.Term
import CodeCalculus.Eval
import CodeCalculus.RebaseRank
import CodeCalculus.MaskRank
import CodeCalculus.MixSupport
import CodeCalculus.RebaseRankSector
import CodeCalculus.Judgment
import CodeCalculus.Property
import CodeCalculus.Interval
import CodeCalculus.Refinement
import CodeCalculus.PricedInterval
import CodeCalculus.WellFormedness
import CodeCalculus.RanksFit
import CodeCalculus.GraftWellFormedness
import CodeCalculus.RebaseWellFormedness
import CodeCalculus.Soundness
import CodeCalculus.Transport
import CodeCalculus.SeamChains
import CodeCalculus.ExactDistance
import CodeCalculus.TermSoundness
import CodeCalculus.Gate6Soundness
import CodeCalculus.ExactPeel
import CodeCalculus.ExactDirectSum
import CodeCalculus.ExactPermute
import CodeCalculus.ExactGraft
import CodeCalculus.ExactGlue
import CodeCalculus.ExactGluePairs
import CodeCalculus.ExactGlueDistance
import CodeCalculus.ExactGlueSurvival
import CodeCalculus.LogicalWitness
import CodeCalculus.WitnessFields
import CodeCalculus.AdmissibleSeamFamily
import CodeCalculus.Gate6Exact
import CodeCalculus.CertificateChecker
import CodeCalculus.CertificateInstances
import CodeCalculus.Constructors
import CodeCalculus.ConstructorWellFormedness
import CodeCalculus.ConstructorOrthogonality
import CodeCalculus.ConstructorAssembly
import CodeCalculus.ConstructorOverlap
import CodeCalculus.ConstructorRank
import CodeCalculus.ConstructorRankTyped
import CodeCalculus.ConcatRetention
import CodeCalculus.BalancedOverlap
import CodeCalculus.ConstructorRankNatural
import CodeCalculus.ConstructorInstances
import CodeCalculus.KernelObligations
import CodeCalculus.Fixtures
import CodeCalculus.FixtureReplay
import CodeCalculus.WellFormedBool
import CodeCalculus.FixtureEvalReplay

/-! # Axiom audit

Checks, at build time, the trust basis that `lean/README.md` records:

* `Classical.choice` is confined to the noncomputable denotation. Every
  constant of a `CodeCalculus` module whose axioms include `Classical.choice`
  is `denoteExpr`, `denote`, one of their generated auxiliaries, or a theorem
  whose statement mentions one of them.
* No constant depends on `sorryAx`.
* The only axioms beyond `propext`, `Quot.sound`, and `Classical.choice` are
  the `native_decide` axioms generated for `rankOf_identifierAt` (`State.lean`).

A violation is an elaboration error, so `lake build` fails. The summary line
the command logs names the constants that depend on `Classical.choice`, so a
reader can see the confinement set without running `#print axioms`. -/

open Lean Elab Command

namespace CodeCalculus.AxiomAudit

/-- The constants allowed to depend on `Classical.choice`: the two denotation
    functions, their generated auxiliaries, and the theorems stated about them. -/
def isDenotation (env : Environment) (n : Name) : Bool :=
  let roots : List Name := [``CodeCalculus.denoteExpr, ``CodeCalculus.denote]
  roots.any (fun r => r.isPrefixOf n) ||
    match env.find? n with
    | some ci => (ci.type.getUsedConstants).any (fun c => roots.contains c)
    | none => false

/-- The constants whose generated `native_decide` axioms the trust basis accepts. -/
def nativeDecideSites : List Name := [``CodeCalculus.rankOf_identifierAt]

def isAcceptedNative (a : Name) : Bool :=
  nativeDecideSites.any (fun s => s.isPrefixOf a)

def isStandard (a : Name) : Bool :=
  a == ``propext || a == ``Quot.sound || a == ``Classical.choice

elab "#audit_trust_basis" : command => do
  let env ← getEnv
  let mut choiceUsers : Array Name := #[]
  let mut unconfined : Array Name := #[]
  let mut sorried : Array Name := #[]
  let mut nonstandard : Array (Name × Name) := #[]
  let mut natives : Array Name := #[]
  let mut total : Nat := 0
  for (n, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!
    unless (`CodeCalculus).isPrefixOf modName || (`CodeCalculus).isPrefixOf n do continue
    total := total + 1
    let axs ← collectAxioms n
    for a in axs do
      if a == ``Classical.choice then
        choiceUsers := choiceUsers.push n
        unless isDenotation env n do unconfined := unconfined.push n
      else if a == ``sorryAx then
        sorried := sorried.push n
      else if isStandard a then
        pure ()
      else if isAcceptedNative a then
        unless natives.contains a do natives := natives.push a
      else
        nonstandard := nonstandard.push (n, a)
  let sortNames (xs : Array Name) : Array Name :=
    xs.qsort (fun a b => a.toString < b.toString)
  logInfo m!"trust basis: {total} constants in CodeCalculus modules; \
    {choiceUsers.size} depend on Classical.choice: {sortNames choiceUsers}; \
    accepted native_decide axioms: {natives}"
  unless unconfined.isEmpty do
    throwError "Classical.choice is not confined to the denotation: {sortNames unconfined}"
  unless sorried.isEmpty do
    throwError "sorryAx in: {sortNames sorried}"
  unless nonstandard.isEmpty do
    throwError "unexpected axioms: {nonstandard}"

end CodeCalculus.AxiomAudit

#audit_trust_basis
