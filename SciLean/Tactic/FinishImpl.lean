import SciLean.Solver.Basic

import Lean
import Lean.Meta.Basic
import Lean.Elab.Tactic.Basic

open Lean 
open Lean.Meta
open Lean.Elab.Tactic

-- It is necessary only if `SciLean.Solver.Basic` is imported. But why???
set_option synthInstance.maxHeartbeats 10000

-- def finishImplCore (mvarId : MVarId) : MetaM (List MVarId) :=
--   withMVarContext mvarId do
--     let tag      ← getMVarTag mvarId
--     let target   ← getMVarType mvarId

--     -- Check if target is actually `Impl`
--     let spec := target.getAppArgs[1]

--     IO.println s!"Finishing with: {spec}"

--     assignExprMVar mvarId (← mkAppM `Impl.pure #[spec])

--     return [mvarId]  

syntax (name := finish_impl) "finish_impl" (colGt term:max)* : tactic

@[tactic finish_impl] def tacticFinishImpl : Tactic
| `(tactic| finish_impl) => do 
          -- let mainGoal ← getMainGoal
          -- Check if `mainGoal` is in the form of `Impl a` and test if `a` is computable
          evalTactic (← `(tactic| apply SciLean.ImplSpec.pure _ (by rfl)))
| _ => Lean.Elab.throwUnsupportedSyntax
