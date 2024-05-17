import Lean
import Mathlib.Tactic.FunProp

import SciLean.Tactic.GTrans.Decl
import SciLean.Tactic.GTrans.Theorems

import SciLean.Tactic.LetNormalize2

import SciLean.Lean.ToSSA

open Lean Meta Qq
open Mathlib.Meta.FunProp


namespace SciLean.Tactic.GTrans


----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

private def ppExprWithType (e : Expr) : MetaM String := do
  return s!"{← ppExpr e} : {← ppExpr (← inferType e)}"


def normalize (e : Expr) : MetaM (Expr × Option Expr) := do
  trace[Meta.Tactic.gtrans.normalize] "normalizing {e}"
  -- let e ← whnfCore e {zeta:=false,zetaDelta:=false}
  -- let e ← e.toSSA #[]
  let e ← e.liftLets2 mkLambdaFVars (config:={pullLetOutOfLambda:=false})
  trace[Meta.Tactic.gtrans.normalize] "normalized {e}"
  return (e,none)


unsafe def synthesizeArgument (x : Expr)
    (fuel : Nat) (gtrans : Nat → Expr → MetaM (Option Expr)) :
    MetaM Bool := do

  let x ← instantiateMVars x
  let X ← inferType x

  unless x.isMVar do return true

  withTraceNode
    `Meta.Tactic.gtrans.arg
    (fun r => do pure s!"[{ExceptToEmoji.toEmoji r}] synthesizing argument {← ppExprWithType x}") do

    if let .some _ ← isGTrans? X then
      if let .some prf ← gtrans (fuel-1) X then
        x.mvarId!.assignIfDefeq prf
        return true
      else
        return false
    else if let .some _ ← isClass? X then
      try
        let inst ← synthInstance X
        x.mvarId!.assignIfDefeq inst
        return true
      catch _ =>
        return false
    else if ← Mathlib.Meta.FunProp.isFunPropGoal X then
      if let (.some prf, _) ← (funProp X).run {} {} then
        x.mvarId!.assign prf.proof
        return true
      else
        return false
    else if X.isAppOfArity ``autoParam 2 then
      let tactic ← Meta.evalExpr (TSyntax `tactic) q(Lean.Syntax) X.appArg!
      trace[Meta.Tactic.gtrans.arg] s!"auto arg tactic {tactic.raw.prettyPrint}"
      let .some prf ← tacticToDischarge ⟨tactic⟩ X.appFn!.appArg! | return false
      if ← isDefEq (← inferType prf) X then
        x.mvarId!.assignIfDefeq prf
        return true
      else
        return false
    else
      return false


unsafe def tryTheorem? (e : Expr) (thm : GTransTheorem) (fuel : Nat)
    (gtrans : Nat → Expr → MetaM (Option Expr)) : MetaM (Option Expr) := do

  trace[Meta.Tactic.gtrans] "goal {← ppExpr e}"


  let thmProof ← thm.getProof
  let type ← inferType thmProof
  let (xs, _, type) ← forallMetaTelescope type
  let thmProof := thmProof.beta xs

  -- if applying this theorem fails we want to roll back any changes to metavariables
  let s ← saveState

  trace[Meta.Tactic.gtrans.unify] "unify\n{e}\n=?=\n{type}"
  unless (← isDefEq e type) do
    trace[Meta.Tactic.gtrans.unify] "unification failed"
    return none

  for x in xs do
    let _ ← synthesizeArgument x fuel gtrans

  for x in xs do
    let x ← instantiateMVars x
    if x.hasMVar then
      restoreState s
      trace[Meta.Tactic.gtrans] "failed to synthesize argument {← ppExprWithType x}"
      return none

  return some thmProof



/-- `gtrans` accespt expression `e` that has to be of type `Prop` and application of registered
generalized transformation. The goal of `gtrans` is to fill in metavariables in `e` and provide
proof of the resulting proposition.

Meta variables in `e` can appear only in particular places. Each generalize transformation is
expected to have some arguments marked as `outParam` and only these arguments can be metavariables.

Examples:

- `simp` as generalized transformation
  calling `gtrans q(0+n+0 = ?m)` will call simp on `0+n+0` and assign the result to `?m`

- computing derivatives
  calling `gtrans q(HasFDeriv (fun x : ℝ => x*x) ?f' x` will compute derivative
  `?f := fun dx ↦L[K] 2*dx`
 -/
unsafe def gtrans (fuel : Nat) (e : Expr) : MetaM (Option Expr) := do

  forallTelescope e fun ctx e => do
  Meta.letTelescope e fun ctx' e => do

  if fuel = 0 then
    return none

  let .some gtransDecl ← isGTrans? e
    | throwError "expected application of generalized transformation, got {← ppExpr e}"

  let ext := gtransTheoremsExt.getState (← getEnv)
  let thms ← ext.theorems.getMatchWithScore e false {}
  -- let thms := thms.qsort (fun t s => t.2 < s.2) |>.map (·.1) |>.flatten
  let thms := thms |>.map (·.1) |>.flatten

  withTraceNode `Meta.Tactic.gtrans (fun r => do pure s!"[{ExceptToEmoji.toEmoji r}] {← ppExpr e}") do

  -- replace output argument mvars with fresh mvars
  let mut e' := e
  for i in gtransDecl.outputArgs do
    -- this check is a temporary hack, we should have proper handling of output arguments that
    -- depend on another output arguments. Types that are output arguments are the prime examples
    -- and right now we just skip them and do not replace them with a fresh mvar.
    unless (← isType (← inferType (e.getArg! i))) do continue
    e' := e'.setArg i (← mkFreshExprMVar (← inferType (e'.getArg! i)))

  let keys := ← RefinedDiscrTree.mkDTExprs e {} false
  trace[Meta.Tactic.gtrans.candidates] "look up key: {keys}"
  trace[Meta.Tactic.gtrans.candidates] "candidates: {thms.map (·.thmName)}"

  for thm in thms do
    if let .some prf ←
      withTraceNode `Meta.Tactic.gtrans
        (fun r => do pure s!"[{ExceptToEmoji.toEmoji r}] applying {thm.thmName}") do
        tryTheorem? e' thm fuel gtrans then

      trace[Meta.Tactic.gtrans] "application successful"

      -- get output arguments and normalize them
      for i in gtransDecl.outputArgs do
        let arg := (← instantiateMVars (e'.getArg! i))
        let (arg',_) ← normalize arg

        if ← isDefEq arg' (e.getArg! i) then
          trace[Meta.Tactic.gtrans] "argument {i} assigned with {← ppExpr arg'}"
        else
          trace[Meta.Tactic.gtrans] "failed to assign {← ppExprWithType arg'} to {← ppExprWithType (e.getArg! i)}"


      -- todo: use proofs from normalization
      --       right now we assume that normalization produces terms that are defeq to the original ones

      return ← mkLambdaFVars (ctx++ctx') prf

  return none

  -- check if `e` is application of generalized transformation



initialize registerTraceClass `Meta.Tactic.gtrans.candidates
initialize registerTraceClass `Meta.Tactic.gtrans.normalize
initialize registerTraceClass `Meta.Tactic.gtrans.unify
initialize registerTraceClass `Meta.Tactic.gtrans.arg
initialize registerTraceClass `Meta.Tactic.gtrans
