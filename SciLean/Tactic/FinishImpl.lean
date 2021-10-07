import Lean
import Lean.Meta.Basic
import Lean.Elab.Tactic.Basic

open Lean 
open Lean.Meta
open Lean.Elab.Tactic

def finishImplCore (mvarId : MVarId) : MetaM (List MVarId) :=
  withMVarContext mvarId do
    let tag      ← getMVarTag mvarId
    let target   ← getMVarType mvarId

    -- Check if target is actually `Impl`
    let spec := target.getAppArgs[1]

    IO.println s!"Finishing with: {spec}"

    assignExprMVar mvarId (← mkAppM `Impl.pure #[spec])

    return [mvarId]  

syntax (name := finish_impl) "finish_impl" (colGt term:max)* : tactic

@[tactic finish_impl] def tacticFinishImpl : Tactic
| `(tactic| finish_impl) => do 
          let mainGoal ← getMainGoal
          let todos ← finishImplCore mainGoal
          setGoals todos
          pure ()
| _ => Lean.Elab.throwUnsupportedSyntax
