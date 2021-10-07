import Lean
import Lean.Meta.Basic
import Lean.Elab.Tactic.Basic

open Lean 
open Lean.Meta
open Lean.Elab.Tactic

def replaceSubExpression (e : Expr) (test : Expr → Bool) (replace : Expr → MetaM Expr) : MetaM Expr := do
if (test e) then
  (replace e)
else
match e with
  | Expr.app f x d => do (mkApp (← (replaceSubExpression f test replace)) (← (replaceSubExpression x test replace)))
  | Expr.lam n x b d => Expr.lam n x (← replaceSubExpression b test replace) d
  -- this is incomplete and should use lambda telescope
  | _ => e


-- use 
def getlimit (e : Expr) : MetaM (Expr × Expr) := do
  let sub : IO.Ref Expr ← IO.mkRef arbitrary
  let test := (λ e : Expr => 
                   match e.getAppFn.constName? with
                     | some name => name == `limit
                     | none => false)
  let replace := (λ e : Expr => 
                    do
                      IO.println "Got match!"
                      sub.modify (λ _ => e)
                      pure e)
  (← replaceSubExpression e test replace, ← sub.get)
  
syntax (name := lift_limit) "lift_limit" : tactic

def liftLimitCore (mvarId : MVarId) : MetaM (List MVarId) :=
  withMVarContext mvarId do
    let tag      ← getMVarTag mvarId
    let target   ← getMVarType mvarId

    -- IO.println s!"Target is: {target}"

    let (e, l) ← getlimit target
    IO.println s!"Found limit: {l}"
    IO.println s!"Limit body: {l.getAppArgs[2]}"

    -- let targetNew ← (removelambdalet target (← getLCtx))
    -- let mvarNew  ← mkFreshExprSyntheticOpaqueMVar targetNew tag
    -- let eq       ← mkEq target targetNew
    -- let eqMvar  ← mkFreshExprSyntheticOpaqueMVar eq
    -- let val  := mkAppN (Lean.mkConst `Eq.mpr [u]) #[target, targetNew, eqMvar, mvarNew]
    -- assignExprMVar mvarId var
    -- assignExprMVar mvarId mvarNew
    return [mvarId]

@[tactic lift_limit] def tacticLiftLimit : Tactic
| _ => do 
          let mainGoal ← getMainGoal
          let todos ← liftLimitCore mainGoal 
          setGoals todos
          pure ()
