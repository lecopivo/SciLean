import SciLean.Core.Meta.FunctionProperty.EnvExtension

open Lean Meta

namespace SciLean

/--
For `T = funTrans` and `f = function`
Get statement for `T (λ t => f x₁ .. xₙ) = ...`
-/
def applyCompTheorem (funTrans function : Name) (xs : Array Expr) (t : Expr) : MetaM (Option (Expr×Name)) := do

  let tId := t.fvarId!
  
  -- Find `xs` that depend on `t`
  let mut depArgIds : Array Nat := #[]
  for i in [0:xs.size] do
    if xs[i]!.containsFVar tId then
      depArgIds := depArgIds.push i

  let depArgIds' := depArgIds.toArraySet

  let some thrmMap ← getFunctionProperty function funTrans
    | return none

  for (args, thrms) in thrmMap do

    let some compTheorem := thrms.compTheorem
      | continue

    if depArgIds' ⊆ args then
      let mut ys := xs
    
      -- abstract `t` in all arguments in the composition theorem
      for i in args.data do
        ys := ys.set! i (← mkLambdaFVars #[t] ys[i]!)

      let explicitArgIds ← getConstExplicitArgIds function
      let explicitYs := explicitArgIds.map (λ i => ys[i]!)
      
      return some ((← mkAppNoTrailingM compTheorem explicitYs), compTheorem)

  return none
  
