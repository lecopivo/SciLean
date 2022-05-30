-- This is code from the main Lean 4 repository, in particular: src/Lean/Meta/Tactic/Simp/Main.lean

/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Tactic.Simp.Rewrite
import Lean.Elab.Tactic

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

namespace SciLean.Tactic.CustomSimp

open Lean.Meta Simp
open Lean.Meta.Simp
open Lean

def simp (e : Expr) (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none) (pres posts : Array (Expr → SimpM Simp.Step) := #[]) : MetaM Simp.Result := do profileitM Exception "simp" (← getOptions) do
  match discharge? with
  | none   => Simp.main e ctx (methods := Simp.DefaultMethods.methods 
                                          |> pres.foldr  (λ p m => m.prependPre p) 
                                          |> posts.foldr (λ p m => m.prependPost p))
  | some d => Simp.main e ctx (methods := { pre := (Simp.preDefault · d), post := (Simp.postDefault · d), discharge? := d }
                                          |> pres.foldr  (λ p m => m.prependPre  p) 
                                          |> posts.foldr (λ p m => m.prependPost p))

/--
  Auxiliary method.
  Given the current `target` of `mvarId`, apply `r` which is a new target and proof that it is equaal to the current one.
-/
def applySimpResultToTarget (mvarId : MVarId) (target : Expr) (r : Simp.Result) : MetaM MVarId := do
  match r.proof? with
  | some proof => replaceTargetEq mvarId r.expr proof
  | none =>
    if target != r.expr then
      replaceTargetDefEq mvarId r.expr
    else
      return mvarId

/-- See `simpTarget`. This method assumes `mvarId` is not assigned, and we are already using `mvarId`s local context. -/
def simpTargetCore (mvarId : MVarId) (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none) (mayCloseGoal := true) (pres posts : Array (Expr → SimpM Simp.Step) := #[]) : MetaM (Option MVarId) := do
  let target ← instantiateMVars (← getMVarType mvarId)
  let r ← simp target ctx discharge? pres posts
  if mayCloseGoal && r.expr.isConstOf ``True then
    match r.proof? with
    | some proof => assignExprMVar mvarId  (← mkOfEqTrue proof)
    | none => assignExprMVar mvarId (mkConst ``True.intro)
    return none
  else
    applySimpResultToTarget mvarId target r

/--
  Simplify the given goal target (aka type). Return `none` if the goal was closed. Return `some mvarId'` otherwise,
  where `mvarId'` is the simplified new goal. -/
def simpTarget (mvarId : MVarId) (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none) (mayCloseGoal := true) (pres posts : Array (Expr → SimpM Simp.Step) := #[]) : MetaM (Option MVarId) :=
  withMVarContext mvarId do
    checkNotAssigned mvarId `simp
    simpTargetCore mvarId ctx discharge? mayCloseGoal pres posts

def simpGoal (mvarId : MVarId) (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none) (simplifyTarget : Bool := true) (fvarIdsToSimp : Array FVarId := #[]) (fvarIdToLemmaId : FVarIdToLemmaId := {}) (pres posts : Array (Expr → SimpM Simp.Step) := #[]) : MetaM (Option (Array FVarId × MVarId)) := do
  withMVarContext mvarId do
    checkNotAssigned mvarId `simp
    let mut mvarId := mvarId
    let mut toAssert := #[]
    let mut replaced := #[]
    for fvarId in fvarIdsToSimp do
      let localDecl ← getLocalDecl fvarId
      let type ← instantiateMVars localDecl.type
      let ctx ← match fvarIdToLemmaId.find? localDecl.fvarId with
        | none => pure ctx
        | some thmId => pure { ctx with simpTheorems := ctx.simpTheorems.eraseTheorem thmId }
      let r ← simp type ctx discharge? pres posts
      match r.proof? with
      | some proof => match (← applySimpResultToProp mvarId (mkFVar fvarId) type r) with
        | none => return none
        | some (value, type) => toAssert := toAssert.push { userName := localDecl.userName, type := type, value := value }
      | none =>
        if r.expr.isConstOf ``False then
          assignExprMVar mvarId (← mkFalseElim (← getMVarType mvarId) (mkFVar fvarId))
          return none
        -- TODO: if there are no forwards dependencies we may consider using the same approach we used when `r.proof?` is a `some ...`
        -- Reason: it introduces a `mkExpectedTypeHint`
        mvarId ← replaceLocalDeclDefEq mvarId fvarId r.expr
        replaced := replaced.push fvarId
    if simplifyTarget then
      match (← simpTarget mvarId ctx discharge? (pres:=pres) (posts:=posts)) with
      | none => return none
      | some mvarIdNew => mvarId := mvarIdNew
    let (fvarIdsNew, mvarIdNew) ← assertHypotheses mvarId toAssert
    let toClear := fvarIdsToSimp.filter fun fvarId => !replaced.contains fvarId
    let mvarIdNew ← tryClearMany mvarIdNew toClear
    return (fvarIdsNew, mvarIdNew)


open Lean Elab.Tactic

def simpLocation (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none) (fvarIdToLemmaId : FVarIdToLemmaId := {}) (loc : Location) (pres posts : Array (Expr → Simp.SimpM Simp.Step) := #[]) : TacticM Unit := do
  match loc with
  | Location.targets hyps simplifyTarget =>
    withMainContext do
      let fvarIds ← getFVarIds hyps
      go fvarIds simplifyTarget fvarIdToLemmaId
  | Location.wildcard =>
    withMainContext do
      go (← getNondepPropHyps (← getMainGoal)) (simplifyTarget := true) fvarIdToLemmaId
where
  go (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool) (fvarIdToLemmaId : Lean.Meta.FVarIdToLemmaId) : TacticM Unit := do
    let mvarId ← getMainGoal
    let result? ← simpGoal mvarId ctx (simplifyTarget := simplifyTarget) (discharge? := discharge?) (fvarIdsToSimp := fvarIdsToSimp) (fvarIdToLemmaId := fvarIdToLemmaId) pres posts
    match result? with
    | none => replaceMainGoal []
    | some (_, mvarId) => replaceMainGoal [mvarId]
