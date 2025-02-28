import Lean

import Qq

import SciLean.Util.Limit

open Lean
open Lean.Meta
open Lean.Elab.Tactic

open Qq in
def pullLimitOut (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e

  -- find the first subexpression `Filter.limit filter f`
  let .some limitExpr := e.find?
    (fun e => e.isAppOf' ``Filter.limit && e.getAppNumArgs ≥ 0)
    | throwError s!"no limit found in {← ppExpr e}"
  let xType   := limitExpr.getArg!' 0
  let filter := limitExpr.getArg!' 4

  if xType.hasLooseBVars || filter.hasLooseBVars then
    throwError s!"can't pull limit out as the type of the limit depends on the local context of the expression"

  let f := limitExpr.getArg!' 5
  let xName := if f.isLambda then f.bindingName! else `x

  withLocalDecl xName default xType λ x => do

    let e' ← Meta.transform e
      (pre := λ e => do
        let (fName, args) := e.getAppFnArgs
        if fName == ``Filter.limit && args.size ≥ 6 then
          let type'   := args[0]!
          let filter' := args[4]!
          let f := e.getArg!' 5
          if (← isDefEq xType type') && (← isDefEq filter filter') then
            return .done (f.beta (#[x] ++ args[6:]))
          else
            return .continue
        else
          return .continue)

    mkAppM ``Filter.limit #[filter, ← mkLambdaFVars #[x] e']


syntax (name := pull_limit_out) "pull_limit_out" " := " term: conv

open Conv

@[tactic pull_limit_out] def pullLimitOutTactic : Tactic
| `(conv| pull_limit_out := $prf) => do
  (← getMainGoal).withContext do
    let lhs ← getLhs
    let lhs' ← pullLimitOut lhs

    let eqGoal ← mkEq lhs lhs'
    let eqProof ← elabTerm prf eqGoal

    updateLhs lhs' eqProof

| _ => Lean.Elab.throwUnsupportedSyntax
