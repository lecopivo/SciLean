import SciLean

open SciLean
-- set_option profiler true 
set_option maxHeartbeats 50000

/--
info: false
-/
#guard_msgs in
open Lean Meta Qq in
#eval show MetaM Unit from do

  let X : Q(Type) := q(Float → DataArrayN Float (Idx 10))
  withLocalDecl `x default X fun x => do
  let x : Q($X) := x
  let HX := q(IsDifferentiable Float $x)
  withLocalDecl `hx default HX fun hx => do

  let H := q(IsDifferentiable Float fun w => ⊞ i => ($x w)[i])
  let h ← mkFreshExprMVar H 
  IO.println (← isDefEq hx h)
