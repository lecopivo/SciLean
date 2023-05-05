import Lean
import Lean.Meta.Basic
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Conv.Basic

import Qq

import SciLean.Functions.Limit

open Lean 
open Lean.Meta
open Lean.Elab.Tactic

namespace BubbleLimit

open Qq in
def bubbleLimit (e : Expr) : MetaM Expr := do
  withLocalDecl `n default q(Nat) λ n => do
    let e' ← Meta.transform e
      (pre := λ e => 
        let args := e.getAppArgs
        if e.getAppFn.isConstOf ``SciLean.limit &&
           args.size ≥ 2 then 
          let f := args[1]!
          return .done (mkAppN (mkApp f n) args[2:])
        else
          return .continue)
    mkAppM ``SciLean.limit #[← mkLambdaFVars #[n] e']


-- syntax (name := bubble_limit) "bubble_limit": tactic

-- @[tactic bubble_limit] def tacticBubbleLimit : Tactic
-- | `(tactic| bubble_limit) => do 
--           let mainGoal ← getMainGoal
--           let todos ← bubbleLimitCore mainGoal
--           setGoals todos
--           pure ()
-- | _ => Lean.Elab.throwUnsupportedSyntax


syntax (name := bubble_lim) "bubble_lim": conv

open Conv

@[tactic bubble_lim] def tacticBubbleLim : Tactic
| `(conv| bubble_lim) => do  
  (← getMainGoal).withContext do
    let lhs ← getLhs
    -- let f ← getlimit lhs
    let lhs' ← bubbleLimit lhs

    let eqGoal ← mkFreshExprSyntheticOpaqueMVar (← mkEq lhs lhs')

    updateLhs lhs' eqGoal
    replaceMainGoal [eqGoal.mvarId!, (← getMainGoal)]
| _ => Lean.Elab.throwUnsupportedSyntax

end BubbleLimit
  
