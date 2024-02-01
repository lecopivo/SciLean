import Lean

import SciLean.Tactic.FProp.Basic

open Lean Elab Tactic

namespace SciLean.FProp

open Lean.Parser.Tactic

elab (name := fpropTac) "fprop" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let goalType ← goal.getType

    let (.some proof, _) ← fprop goalType {} |>.run {}
      | throwError "fprop was unable to prove `{← Meta.ppExpr goalType}`"

    goal.assign proof
