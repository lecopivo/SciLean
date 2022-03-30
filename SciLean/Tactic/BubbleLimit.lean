import Lean
import Lean.Meta.Basic
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Conv.Basic


open Lean 
open Lean.Meta
open Lean.Elab.Tactic

namespace BubbleLimit

partial def replaceSubExpression (e : Expr) (test : Expr → Bool) (replace : Expr → MetaM Expr) : MetaM Expr := do
if (test e) then
  (replace e)
else
match e with
  | Expr.app f x d => do pure (mkApp (← (replaceSubExpression f test replace)) (← (replaceSubExpression x test replace)))
  | Expr.lam n x b _ => pure $ mkLambda n e.binderInfo x (← replaceSubExpression b test replace)
  | _ => pure e

-- use 
def getlimit  (e : Expr) : MetaM Expr := do
  let nId ← mkFreshFVarId
  withLCtx ((← getLCtx).mkLocalDecl nId `n (mkConst `Nat)) (← getLocalInstances) do
    let nFv := mkFVar nId
    let test := (λ e : Expr => 
      match e.getAppFn.constName? with
        | some name => name == `SciLean.limit
        | none => false)
    let replace := (λ e : Expr => 
      do
        let lim := e.getAppArgs[2]
        let args := #[nFv].append e.getAppArgs[3:]
        mkAppM' lim args)
    mkLambdaFVars #[nFv] (← replaceSubExpression e test replace)
  
def bubbleLimitCore (mvarId : MVarId) : MetaM (List MVarId) :=
  withMVarContext mvarId do
    let tag      ← getMVarTag mvarId
    let target   ← getMVarType mvarId

    -- Check if target is actually `Impl spec`
    let spec := target.getAppArgs[1]
    let lim ← getlimit spec

    let new_spec ← mkAppM `SciLean.limit #[lim]
    let new_target ← mkAppM `SciLean.Impl #[new_spec]
    let new_mvar  ← mkFreshExprSyntheticOpaqueMVar new_target tag
    let eq       ← mkEq new_target target
    let eq_mvar  ← mkFreshExprSyntheticOpaqueMVar eq

    assignExprMVar mvarId (← mkAppM `Eq.mp #[eq_mvar, new_mvar])

    return [eq_mvar.mvarId!, new_mvar.mvarId!]  

syntax (name := bubble_limit) "bubble_limit": tactic

@[tactic bubble_limit] def tacticBubbleLimit : Tactic
| `(tactic| bubble_limit) => do 
          let mainGoal ← getMainGoal
          let todos ← bubbleLimitCore mainGoal
          setGoals todos
          pure ()
| _ => Lean.Elab.throwUnsupportedSyntax


syntax (name := bubble_lim) "bubble_lim": conv

open Conv

#check Eq.trans

@[tactic bubble_lim] def tacticBubbleLim : Tactic
| `(conv| bubble_lim) => do  
  withMVarContext (← getMainGoal) do
    let lhs ← getLhs
    let f ← getlimit lhs
    let lhs' ← mkAppM `SciLean.limit #[f]

    let eqGoal ← mkFreshExprSyntheticOpaqueMVar (← mkEq lhs lhs')

    updateLhs lhs' eqGoal
    replaceMainGoal [eqGoal.mvarId!, (← getMainGoal)]
| _ => Lean.Elab.throwUnsupportedSyntax

end BubbleLimit
  
