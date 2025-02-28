import Lean

import SciLean.Util.Approx.Basic
import SciLean.Tactic.PullLimitOut
import SciLean.Lean.Meta.Basic

namespace SciLean

open Lean Elab Tactic
/-- This tactic eliminates `limit` from an expression that you are approximating

For example, for goal

```
  ⊢ Approx _ (x + limit n → ∞, (1 + x/n)^n)
```

calling `approx_limit n := <proof>` produces goal

```
  n : Nat
  ⊢ Approx _ (x + (1 + x/n)^n)
```

where `<proof>` is a proof that this approximation is indeed valid

Warning: The validity proof is not completely correct right now
-/
syntax (name:=approx_limit_tactic) "approx_limit " ident term : tactic

open Lean Meta in
@[tactic approx_limit_tactic]
def approxLimitTactic : Tactic
| `(tactic| approx_limit $n:ident $prf:term) => do
  let mainGoal ← getMainGoal
  mainGoal.withContext do
  let goal ← instantiateMVars (← mainGoal.getType)

  Lean.Meta.letTelescope goal fun xs goal' => do
  if ¬(goal'.isAppOfArity' ``Approx 6) then
    throwError "the goal is not `Approx _ _`"

  let .app f a := goal' | panic! "unreachable code in approxLimitTactic"
  let a' ← pullLimitOut a
  let goal'' ← mkLambdaFVars xs (f.app a')
  let limitPullProof ← elabTerm (← `($prf)) (← Meta.mkEq a a')
  let mainGoal ← mainGoal.replaceTargetEq goal'' (← mkLambdaFVars xs (← Meta.mkAppM ``congr_arg #[f,limitPullProof]))
  setGoals [mainGoal]

  -- TODO: this probably should be done manually as these holes should not become new goals
  evalTactic (← `(tactic| apply Approx.limit _ _))
  evalTactic (← `(tactic| intros $n))
| _ => throwUnsupportedSyntax
