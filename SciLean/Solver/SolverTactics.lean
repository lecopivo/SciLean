-- import SciLean.Solver.Basic
-- set_option synthInstance.maxHeartbeats 10000

import Lean
import Lean.Meta.Basic
import Lean.Elab.Tactic.Basic

open Lean 
open Lean.Meta
open Lean.Elab.Tactic

open TSyntax.Compat -- makes old untyped syntax code compile

--- Add an assumption 
syntax (name := impl_assume) "impl_assume" notFollowedBy("|") (colGt term:max)* : tactic
--- Add a runtime check
syntax (name := impl_check) "impl_check" notFollowedBy("|") (colGt term:max)* : tactic

-- --- Solve the current Prop goal by adding it to the list of assumptions/promisses
-- syntax (name := assume_this) "assume_this" notFollowedBy("|") (colGt term:max)* : tactic
-- --- Solve the current Decidable Prop goal by adding a runtime check
-- syntax (name := check_this) "check_this" notFollowedBy("|") (colGt term:max)* : tactic

-- --- Focus on a subexpression to implement
-- syntax (name := impl) "impl" notFollowedBy("|") (colGt term:max)* : tactic

syntax (name := print_main_goal) "print_main_goal" notFollowedBy("|") : tactic

def Syntax.mkStrLit (str : String) : Syntax := Syntax.node default strLitKind #[mkAtom ("\"" ++ str ++ "\"")]

inductive assumeOrCheck where | assume | check 

def implAssumeCheckCore (mvarId : MVarId) (prop msg : Expr) (type : assumeOrCheck) : MetaM (List MVarId) :=
  withMVarContext mvarId do
    let tag    ← getMVarTag mvarId
    let target ← getMVarType mvarId
    
    let newTarget ← pure $ mkForall Name.anonymous BinderInfo.default prop target
    let newMVarId  ← mkFreshExprSyntheticOpaqueMVar newTarget tag

    match type with
      | assumeOrCheck.assume => assignExprMVar mvarId (← mkAppM `SciLean.ImplSpec.assumption #[newMVarId, msg])
      | assumeOrCheck.check  => assignExprMVar mvarId (← mkAppM `SciLean.ImplSpec.check #[newMVarId, msg])

    return [newMVarId.mvarId!]

@[tactic impl_assume] def tacticImplAssume : Tactic
| `(tactic| impl_assume $prop:term $msg:term $h:term) => do 
            let mainGoal ← getMainGoal  
            let p ← elabTerm prop none true
            let m ← elabTerm msg none true
            setGoals (← implAssumeCheckCore mainGoal p m assumeOrCheck.assume)
            evalTactic (← `(tactic| intro $h:term))
| `(tactic| impl_assume $prop:term $msg:term) => do
            evalTactic (← `(tactic| impl_assume $prop:term $msg:term h))
| `(tactic| impl_assume $prop:term) => do
            let msg := Syntax.mkStrLit (toString prop.raw.prettyPrint)
            evalTactic (← `(tactic| impl_assume $prop:term $msg h))
| _ => Lean.Elab.throwUnsupportedSyntax


@[tactic impl_check] def tacticImplCheck : Tactic
| `(tactic| impl_check $prop:term $msg:term $h:term) => do 
            let mainGoal ← getMainGoal  
            let p ← elabTerm prop none true
            let m ← elabTerm msg none true
            setGoals (← implAssumeCheckCore mainGoal p m assumeOrCheck.check)
            evalTactic (← `(tactic| intro $h:term))
| `(tactic| impl_check $prop:term $msg:term) => do
            evalTactic (← `(tactic| impl_check $prop:term $msg:term h))
| `(tactic| impl_check $prop:term) => do
            let msg := Syntax.mkStrLit (toString prop.raw.prettyPrint)
            evalTactic (← `(tactic| impl_check $prop:term $msg h))
| _ => Lean.Elab.throwUnsupportedSyntax


def printGoal (mvarId : MVarId)  : MetaM Unit :=
  withMVarContext mvarId do
    let tag    ← getMVarTag mvarId
    let target ← getMVarType mvarId

    IO.println s!"{target}"


@[tactic print_main_goal] def tacticPrintMainGoal : Tactic
| _ =>  do 
        let mainGoal ← getMainGoal  
        printGoal mainGoal


-- def assumeThisCore (propMVarId implMVarId : MVarId) (msg : Expr) : MetaM (List MVarId) := do
--   withMVarContext implMVarId do
--   -- withMVarContext propMVarId do
--     let prop ← getMVarType propMVarId
--     let tag  ← getMVarTag implMVarId
--     let implTarget ← getMVarType implMVarId

--     let newTarget ← mkForall Name.anonymous BinderInfo.default implTarget prop 
--     let newMVarId  ← mkFreshExprSyntheticOpaqueMVar newTarget tag

--     assignExprMVar implMVarId (← mkAppM `Solver.promise #[newMVarId, msg])

--     return [newMVarId.mvarId!, propMVarId]

-- def getImplGoal (vars : List MVarId) : MetaM (Option MVarId) := do
--   let mut r : (Option MVarId) := none
--   for var in vars do
--      let type ← getMVarType var
--      if (type.getAppFn.constName! == `Impl) then 
--        r := var
--   r

-- @[tactic assume_this] def tacticAssumeThis : Tactic
-- | `(tactic| assume_this $msg:term ) => do 
--         let m ← elabTerm msg none true
--         let propGoal ← getMainGoal  
--         let implGoal ← getImplGoal (← getGoals)
--         match implGoal with
--           | some impl => setGoals (← assumeThisCore impl propGoal m)
--           | none => ()
-- | _ => Lean.Elab.throwUnsupportedSyntax


