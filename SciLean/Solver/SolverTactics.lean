-- import Lean
-- import Lean.Meta.Basic
-- import Lean.Elab.Tactic.Basic

-- import SciLean.Solver.Basic

-- open Lean 
-- open Lean.Meta
-- open Lean.Elab.Tactic

-- --- Add an assumption 
-- syntax (name := solver_assume) "solver_assume" notFollowedBy("|") (colGt term:max)* : tactic
-- --- Add a runtime check
-- syntax (name := solver_check) "solver_check" notFollowedBy("|") (colGt term:max)* : tactic

-- --- Solve the current Prop goal by adding it to the list of assumptions/promisses
-- syntax (name := assume_this) "assume_this" notFollowedBy("|") (colGt term:max)* : tactic
-- --- Solve the current Decidable Prop goal by adding a runtime check
-- syntax (name := check_this) "check_this" notFollowedBy("|") (colGt term:max)* : tactic

-- --- Focus on a subexpression to implement
-- syntax (name := impl) "impl" notFollowedBy("|") (colGt term:max)* : tactic

-- syntax (name := print_main_goal) "print_main_goal" notFollowedBy("|") : tactic

-- def Syntax.mkStrLit (str : String) : Syntax := Syntax.node strLitKind #[mkAtom ("\"" ++ str ++ "\"")]

-- def solverAssumeCore (mvarId : MVarId) (prop msg : Expr) : MetaM (List MVarId) :=
--   withMVarContext mvarId do
--     let tag    ← getMVarTag mvarId
--     let target ← getMVarType mvarId
    
--     let newTarget ← mkForall Name.anonymous BinderInfo.default prop target
--     let newMVarId  ← mkFreshExprSyntheticOpaqueMVar newTarget tag

--     assignExprMVar mvarId (← mkAppM `Solver.promise #[newMVarId, msg])

--     return [newMVarId.mvarId!]

-- @[tactic solver_assume] def tacticSolverAssume : Tactic
-- | `(tactic| solver_assume $prop:term $msg:term $h:term) => do 
--             let mainGoal ← getMainGoal  
--             let p ← elabTerm prop none true
--             let m ← elabTerm msg none true
--             setGoals (← solverAssumeCore mainGoal p m)
--             evalTactic (← `(tactic| intro $h:term))
-- | `(tactic| solver_assume $prop:term $msg:term) => do
--             evalTactic (← `(tactic| solver_assume $prop:term $msg:term h))
-- | `(tactic| solver_assume $prop:term) => do
--             let msg := Syntax.mkStrLit (toString prop.prettyPrint)
--             evalTactic (← `(tactic| solver_assume $prop:term $msg h))
-- | _ => Lean.Elab.throwUnsupportedSyntax

-- -- | _ => do 
-- --           let mainGoal ← getMainGoal
-- --           let todos ← solverAssumeCore mainGoal 
-- --           setGoals todos
-- --           pure ()

-- def solverCheckCore (mvarId : MVarId) (prop msg : Expr) : MetaM (List MVarId) :=
--   withMVarContext mvarId do
--     let tag    ← getMVarTag mvarId
--     let target ← getMVarType mvarId

--     let newTarget ← mkForall Name.anonymous BinderInfo.default prop target
--     let newMVarId  ← mkFreshExprSyntheticOpaqueMVar newTarget tag

--     assignExprMVar mvarId (← mkAppM `Solver.check #[newMVarId, msg])

--     return [newMVarId.mvarId!]

-- @[tactic solver_check] def tacticSolverCheck : Tactic
-- | `(tactic| solver_check $prop:term $msg:term $h:term) => do 
--             let mainGoal ← getMainGoal  
--             let p ← elabTerm prop none true
--             let m ← elabTerm msg none true
--             setGoals (← solverCheckCore mainGoal p m)
--             evalTactic (← `(tactic| intro $h:term))
-- | `(tactic| solver_check $prop:term $msg:term) => do 
--             evalTactic (← `(tactic| solver_check $prop:term $msg:term h))
-- | `(tactic| solver_check $prop:term) => do 
--             let msg := Syntax.mkStrLit (toString prop.prettyPrint)
--             evalTactic (← `(tactic| solver_check $prop:term $msg:term))
-- | _ => Lean.Elab.throwUnsupportedSyntax

-- #check Syntax

-- def printGoal (mvarId : MVarId)  : MetaM Unit :=
--   withMVarContext mvarId do
--     let tag    ← getMVarTag mvarId
--     let target ← getMVarType mvarId

--     IO.println s!"{target}"


-- @[tactic print_main_goal] def tacticPrintMainGoal : Tactic
-- | _ =>  do 
--         let mainGoal ← getMainGoal  
--         printGoal mainGoal


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


-- theorem foo (n : Nat) (h : n=6) : n = 6 := sorry


-- def solver (n : Nat) (y : Nat) : Impl (y * (∑ i : Fin (n+1), i.1*i.1 : Nat)) :=
-- by

--   solver_assume (y<10) "Is y sufficiently small?" h_y
--   solver_check (n>6) -- "Is n sufficiently large?" h_n

--   -- does not work :(
--   -- assume_this "asdfa"

--   apply finish_impl

-- def main : IO Unit := do

--   IO.println ""

--   IO.println (← Solver.run! (solver 8 6) #[])

-- #eval main

