/-
Most of this code is from the main Lean 4 repository, in particular: src/Lean/Meta/Tactic/Simp/Main.lean

Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Simp.Main
import Lean.Elab.Tactic

import SciLean.Tactic.CustomSimp.Rewrite

namespace Lean.Meta.Simp

def Methods.appendPre (methods : Methods) (pre : Expr → SimpM Step) : Methods :=
  {methods with pre := λ e => do
    let s ← methods.pre e
    andThen s (λ e => do pure (some (← pre e)))
  }

def Methods.prependPre (methods : Methods) (pre : Expr → SimpM Step) : Methods :=
  {methods with pre := λ e => do
    let s ← pre e
    andThen s (λ e => do pure (some (← methods.pre e)))
  }

def Methods.appendPost (methods : Methods) (post : Expr → SimpM Step) : Methods :=
  {methods with post := λ e => do
    let s ← methods.post e
    andThen s (λ e => do pure (some (← post e)))
  }

def Methods.prependPost (methods : Methods) (post : Expr → SimpM Step) : Methods :=
  {methods with post := λ e => do
    let s ← post e
    andThen s (λ e => do pure (some (← methods.post e)))
  }

end Lean.Meta.Simp

namespace SciLean.Meta.CustomSimp

open Lean Meta Simp

namespace DefaultMethods
mutual
  partial def discharge? (e : Expr) : SimpM (Option Expr) := do
    if isEqnThmHypothesis e then
      if let some r ← dischargeUsingAssumption? e then
        return some r
      if let some r ← dischargeEqnThmHypothesis? e then
        return some r
    let ctx ← read
    trace[Meta.Tactic.simp.discharge] ">> discharge?: {e}"
    if ctx.dischargeDepth >= ctx.config.maxDischargeDepth then
      trace[Meta.Tactic.simp.discharge] "maximum discharge depth has been reached"
      return none
    else
      withReader (fun ctx => { ctx with dischargeDepth := ctx.dischargeDepth + 1 }) do
        let r ← simp e { pre := pre, post := post, discharge? := discharge? }
        if r.expr.isConstOf ``True then
          try
            return some (← mkOfEqTrue (← r.getProof))
          catch _ =>
            return none
        else
          return none

  partial def pre (e : Expr) : SimpM Step :=
    preDefault e discharge?

  partial def post (e : Expr) : SimpM Step :=
    postDefault e discharge?
end

def methods : Methods :=
  { pre := pre, post := post, discharge? := discharge? }

end DefaultMethods


def simp (e : Expr) (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none)
    (pres posts : Array (Expr → SimpM Simp.Step))
    (usedSimps : UsedSimps := {})
    : MetaM (Simp.Result × UsedSimps) :=
do
  profileitM Exception "simp" (← getOptions) do
  let methods :=
    (match discharge? with
    | none => DefaultMethods.methods
    | some d => { pre := (preDefault · d), post := (Simp.postDefault · d), discharge? := d })
  Simp.main e ctx usedSimps (methods
                             |> pres.foldr  (λ p m => m.prependPre p)
                             |> posts.foldr (λ p m => m.prependPost p))

/--
  Auxiliary method.
  Given the current `target` of `mvarId`, apply `r` which is a new target and proof that it is equaal to the current one.
-/
def applySimpResultToTarget (mvarId : MVarId) (target : Expr) (r : Simp.Result) : MetaM MVarId := do
  match r.proof? with
  | some proof => mvarId.replaceTargetEq r.expr proof
  | none =>
    if target != r.expr then
      mvarId.replaceTargetDefEq r.expr
    else
      return mvarId

/-- See `simpTarget`. This method assumes `mvarId` is not assigned, and we are already using `mvarId`s local context. -/
def simpTargetCore (mvarId : MVarId) (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none)
    (mayCloseGoal := true) (pres posts : Array (Expr → SimpM Simp.Step)) (usedSimps : UsedSimps := {})
    : MetaM (Option MVarId × UsedSimps) := do
  let target ← instantiateMVars (← mvarId.getType)
  let (r, usedSimps) ← simp target ctx discharge? pres posts usedSimps
  if mayCloseGoal && r.expr.isConstOf ``True then
    match r.proof? with
    | some proof => mvarId.assign (← mkOfEqTrue proof)
    | none => mvarId.assign (mkConst ``True.intro)
    return (none, usedSimps)
  else
    return (← applySimpResultToTarget mvarId target r, usedSimps)


/--
  Simplify the given goal target (aka type). Return `none` if the goal was closed. Return `some mvarId'` otherwise,
  where `mvarId'` is the simplified new goal. -/
def simpTarget (mvarId : MVarId) (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none)
    (mayCloseGoal := true) (pres posts : Array (Expr → SimpM Simp.Step)) (usedSimps : UsedSimps := {})
    : MetaM (Option MVarId × UsedSimps) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `simp
    simpTargetCore mvarId ctx discharge? mayCloseGoal pres posts usedSimps

def simpGoal (mvarId : MVarId) (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none)
    (simplifyTarget : Bool := true) (fvarIdsToSimp : Array FVarId := #[])
    (pres posts : Array (Expr → SimpM Simp.Step)) (usedSimps : UsedSimps := {})
    : MetaM (Option (Array FVarId × MVarId) × UsedSimps) := do
  mvarId.withContext do
    mvarId.checkNotAssigned `simp
    let mut mvarId := mvarId
    let mut toAssert := #[]
    let mut replaced := #[]
    let mut usedSimps := usedSimps
    for fvarId in fvarIdsToSimp do
      let localDecl ← fvarId.getDecl
      let type ← instantiateMVars localDecl.type
      let ctx := { ctx with simpTheorems := ctx.simpTheorems.eraseTheorem (.fvar localDecl.fvarId) }
      let (r, usedSimps') ← simp type ctx discharge? pres posts usedSimps
      usedSimps := usedSimps'
      match r.proof? with
      | some _ => match (← applySimpResultToProp mvarId (mkFVar fvarId) type r) with
        | none => return (none, usedSimps)
        | some (value, type) => toAssert := toAssert.push { userName := localDecl.userName, type := type, value := value }
      | none =>
        if r.expr.isConstOf ``False then
          mvarId.assign (← mkFalseElim (← mvarId.getType) (mkFVar fvarId))
          return (none, usedSimps)
        -- TODO: if there are no forwards dependencies we may consider using the same approach we used when `r.proof?` is a `some ...`
        -- Reason: it introduces a `mkExpectedTypeHint`
        mvarId ← mvarId.replaceLocalDeclDefEq fvarId r.expr
        replaced := replaced.push fvarId
    if simplifyTarget then
      match (← simpTarget mvarId ctx discharge? true pres posts) with
      | (none, usedSimps') => return (none, usedSimps')
      | (some mvarIdNew, usedSimps') => mvarId := mvarIdNew; usedSimps := usedSimps'
    let (fvarIdsNew, mvarIdNew) ← mvarId.assertHypotheses toAssert
    let toClear := fvarIdsToSimp.filter fun fvarId => !replaced.contains fvarId
    let mvarIdNew ← mvarIdNew.tryClearMany toClear
    return (some (fvarIdsNew, mvarIdNew), usedSimps)

open Lean Elab.Tactic

/--
`simpLocation ctx discharge? varIdToLemmaId loc`
runs the simplifier at locations specified by `loc`,
using the simp theorems collected in `ctx`
optionally running a discharger specified in `discharge?` on generated subgoals.

Its primary use is as the implementation of the
`simp [...] at ...` and `simp only [...] at ...` syntaxes,
but can also be used by other tactics when a `Syntax` is not available.

For many tactics other than the simplifier,
one should use the `withLocation` tactic combinator
when working with a `location`.
-/
def simpLocation (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none) (loc : Location) (pres posts : Array (Expr → Simp.SimpM Simp.Step) := #[]) : TacticM UsedSimps := do
  match loc with
  | Location.targets hyps simplifyTarget =>
    withMainContext do
      let fvarIds ← getFVarIds hyps
      go fvarIds simplifyTarget
  | Location.wildcard =>
    withMainContext do
      go (← (← getMainGoal).getNondepPropHyps) (simplifyTarget := true)
where
  go (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool) : TacticM UsedSimps := do
    let mvarId ← getMainGoal
    let (result?, usedSimps) ← simpGoal mvarId ctx (simplifyTarget := simplifyTarget) (discharge? := discharge?) (fvarIdsToSimp := fvarIdsToSimp) (pres := pres) (posts := posts)
    match result? with
    | none => replaceMainGoal []
    | some (_, mvarId) => replaceMainGoal [mvarId]
    return usedSimps
