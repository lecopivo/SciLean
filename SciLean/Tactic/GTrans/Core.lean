import Lean
import Mathlib.Tactic.FunProp

import SciLean.Tactic.GTrans.Decl
import SciLean.Tactic.GTrans.Theorems

import SciLean.Tactic.LetNormalize2

import SciLean.Lean.ToSSA

open Lean Meta
open Mathlib.Meta.FunProp


namespace SciLean.Tactic.GTrans


----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

def normalize (e : Expr) : MetaM (Expr × Option Expr) := do
  trace[Meta.Tactic.gtrans.normalize] "normalizing {e}"
  -- let e ← whnfCore e {zeta:=false,zetaDelta:=false}
  -- let e ← e.toSSA #[]
  let e ← e.liftLets2 mkLambdaFVars (config:={pullLetOutOfLambda:=false})
  trace[Meta.Tactic.gtrans.normalize] "normalized {e}"
  return (e,none)

def tryTheorem? (e : Expr) (thm : GTransTheorem) (fuel : Nat)
    (gtrans : Nat → Expr → MetaM (Option Expr)) : MetaM (Option Expr) := do

  let thmProof ← thm.getProof
  let type ← inferType thmProof
  let (xs, _, type) ← forallMetaTelescope type
  let thmProof := thmProof.beta xs

  trace[Meta.Tactic.gtrans.unify] "unify\n{e}\n=?=\n{type}"
  unless (← isDefEq e type) do
    trace[Meta.Tactic.gtrans.unify] "unification failed"
    return none


  for x in xs do
    let x ← instantiateMVars x
    let X ← inferType x

    unless x.isMVar do continue

    if let .some _ ← isGTrans? X then
      if let .some prf ← gtrans (fuel-1) X then
        x.mvarId!.assignIfDefeq prf
      else
        trace[Meta.Tactic.gtrans] "failed to synthesize argument `{← ppExpr x} : {← ppExpr X}`"
        return none
    else if let .some _ ← isClass? X then
      let inst ← synthInstance X
      x.mvarId!.assignIfDefeq inst
    else if ← Mathlib.Meta.FunProp.isFunPropGoal X then
      if let (.some prf, _) ← (funProp X).run {} {} then
        x.mvarId!.assign prf.proof
      else
        trace[Meta.Tactic.gtrans] "failed to prove argument `{← ppExpr x} : {← ppExpr X}`"
        return none

  -- if (← instantiateMVars thmProof).hasExprMVar then
  --   let mvars := (thmProof.collectMVars {}).result

  --   throwError s!"proof has unassigned metavariables {← mvars.mapM (fun mvar => mvar.getType >>= ppExpr)}"
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
partial def gtrans (fuel : Nat) (e : Expr) : MetaM (Option Expr) := do

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
    unless (e.getArg! i).getAppFn |>.isMVar do
      throwError "expected metavariable in output argument {i} of {← ppExpr e}"
    e' := e'.setArg i (← mkFreshExprMVar (← inferType (e'.getArg! i)))

  let keys := ← RefinedDiscrTree.mkDTExprs e {} false
  trace[Meta.Tactic.gtrans.candidates] "look up key: {keys}"
  trace[Meta.Tactic.gtrans.candidates] "candidates: {thms.map (·.thmName)}"

  for thm in thms do
    trace[Meta.Tactic.gtrans] "applying {thm.thmName}"
    if let .some prf ← tryTheorem? e' thm fuel gtrans then

      -- get output arguments and normalize them
      for i in gtransDecl.outputArgs do
        let arg := (← instantiateMVars (e'.getArg! i))
        let (arg',_) ← normalize arg
        (e.getArg! i).mvarId!.assign arg'


      -- todo: use proofs from normalization
      --       right now we assume that normalization produces terms that are defeq to the original ones

      return prf

  return none

  -- check if `e` is application of generalized transformation



initialize registerTraceClass `Meta.Tactic.gtrans.candidates
initialize registerTraceClass `Meta.Tactic.gtrans.normalize
initialize registerTraceClass `Meta.Tactic.gtrans
