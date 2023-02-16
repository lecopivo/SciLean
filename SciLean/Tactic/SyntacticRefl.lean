import Lean.Meta

syntax (name := stx_rfl) "stx_rfl" : tactic

open Lean.Elab.Tactic Lean Meta in
@[tactic stx_rfl] def syntacticRefl : Tactic := fun _ => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  match goalType.app3? ``Eq with
  | none => throwTacticEx `stx_rfl goal m!"equality expected"
  | some (_,lhs,rhs) => 

    let lhs ← instantiateMVars lhs
    let rhs ← instantiateMVars rhs

    -- This is a very crude test and maybe too strict
    -- In my use case I wand defEq witout zeta reduction
    if lhs == rhs then
      goal.applyRefl
    else
      throwTacticEx `stx_rfl goal m!"{← Lean.Meta.ppExpr lhs} and {← Lean.Meta.ppExpr rhs} are not syntactically equal!"  

example : 0 = 0 := 
by
  stx_rfl
