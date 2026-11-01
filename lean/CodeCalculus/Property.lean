import CodeCalculus.Eval
import CodeCalculus.State
import CodeCalculus.Term

namespace CodeCalculus

inductive Carrier where
  | span
  | display
  | presentation
  | consumer
  | state
  deriving Repr, BEq, DecidableEq

inductive Opacity where
  | none
  | distance
  | certificate
  | price
  deriving Repr, BEq, DecidableEq

structure Property (State V : Type) where
  carrier : Carrier
  quantity : State -> V
  update : Command -> State -> State -> V
  transfer : Prop
  opacity : Opacity

def nSignature : Property CodeState Nat where
  carrier := Carrier.span
  quantity := fun s => s.Q.length
  update := fun _ _ s' => s'.Q.length
  transfer := True
  opacity := Opacity.none

theorem n_skip_transfer (s t : CodeState) (h : Eval Command.skip s t) :
    nSignature.quantity s = nSignature.quantity t := by
  cases h
  rfl

end CodeCalculus
