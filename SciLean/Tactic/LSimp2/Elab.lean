/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Replace
import Lean.Elab.BuiltinNotation
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Location
import Lean.Elab.Tactic.Config

import Lean.Elab.Tactic.Simp

import SciLean.Tactic.LSimp2.Main
import SciLean.Tactic.LSimp2.Notation

namespace SciLean.Tactic.LSimp

open Lean Elab Tactic
open TSyntax.Compat

open Lean Meta

def traceSimpCall (stx : Syntax) (usedSimps : Simp.UsedSimps) : MetaM Unit := do
  let mut stx := stx
  if stx[3].isNone then
    stx := stx.setArg 3 (mkNullNode #[mkAtom "only"])
  let mut args := #[]
  let mut localsOrStar := some #[]
  let lctx ← getLCtx
  let env ← getEnv
  for (thm, _) in usedSimps.toArray.qsort (·.2 < ·.2) do
    match thm with
    | .decl declName inv => -- global definitions in the environment
      if env.contains declName && (inv || !simpOnlyBuiltins.contains declName) then
        args := args.push (if inv then
          (← `(Parser.Tactic.simpLemma| ← $(mkIdent (← unresolveNameGlobal declName)):ident))
        else
          (← `(Parser.Tactic.simpLemma| $(mkIdent (← unresolveNameGlobal declName)):ident)))
    | .fvar fvarId => -- local hypotheses in the context
      if let some ldecl := lctx.find? fvarId then
        localsOrStar := localsOrStar.bind fun locals =>
          if !ldecl.userName.isInaccessibleUserName &&
              (lctx.findFromUserName? ldecl.userName).get!.fvarId == ldecl.fvarId then
            some (locals.push ldecl.userName)
          else
            none
      -- Note: the `if let` can fail for `simp (config := {contextual := true})` when
      -- rewriting with a variable that was introduced in a scope. In that case we just ignore.
    | .stx _ thmStx => -- simp theorems provided in the local invocation
      args := args.push thmStx
    | .other _ => -- Ignore "special" simp lemmas such as constructed by `simp_all`.
      pure ()     -- We can't display them anyway.
  if let some locals := localsOrStar then
    args := args ++ (← locals.mapM fun id => `(Parser.Tactic.simpLemma| $(mkIdent id):ident))
  else
    args := args.push (← `(Parser.Tactic.simpStar| *))
  let argsStx := if args.isEmpty then #[] else #[mkAtom "[", (mkAtom ",").mkSep args, mkAtom "]"]
  stx := stx.setArg 4 (mkNullNode argsStx)
  logInfoAt stx[0] m!"Try this: {stx}"


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
def simpLocation (ctx : Simp.Context) (discharge? : Option Simp.Discharge := none) (loc : Location) : TacticM Simp.UsedSimps := do
  match loc with
  | Location.targets hyps simplifyTarget =>
    withMainContext do
      let fvarIds ← getFVarIds hyps
      go fvarIds simplifyTarget
  | Location.wildcard =>
    withMainContext do
      go (← (← getMainGoal).getNondepPropHyps) (simplifyTarget := true)
where
  go (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool) : TacticM Simp.UsedSimps := do
    let mvarId ← getMainGoal
    let (result?, usedSimps) ← SciLean.Tactic.lsimpGoal mvarId ctx (simplifyTarget := simplifyTarget) (discharge? := discharge?) (fvarIdsToSimp := fvarIdsToSimp)
    match result? with
    | none => replaceMainGoal []
    | some (_, mvarId) => replaceMainGoal [mvarId]
    return usedSimps


/-
  "simp " (config)? (discharger)? ("only ")? ("[" simpLemma,* "]")? (location)?
-/
@[tactic SciLean.Tactic.LSimp.lsimp] def evalSimp : Tactic := fun stx => do
  let { ctx, dischargeWrapper } ← withMainContext <| mkSimpContext stx (eraseLocal := false)
  let usedSimps ← dischargeWrapper.with fun discharge? =>
    simpLocation ctx discharge? (expandOptLocation stx[5])
  if tactic.simp.trace.get (← getOptions) then
    traceSimpCall stx usedSimps

open Lean Elab Tactic Conv in
@[tactic SciLean.Tactic.LSimp.lsimp_conv] def evalSimpConv : Tactic := fun stx => do
  let { ctx, dischargeWrapper } ← withMainContext <| mkSimpContext stx (eraseLocal := false)

  let e ← getLhs
  let (r, usedSimps) ← dischargeWrapper.with fun discharge? =>
    SciLean.Tactic.simp e ctx discharge?

  updateLhs r.expr (← r.getProof' e)

  if tactic.simp.trace.get (← getOptions) then
    traceSimpCall stx usedSimps

def dsimpLocation (ctx : Simp.Context) (loc : Location) : TacticM Unit := do
  match loc with
  | Location.targets hyps simplifyTarget =>
    withMainContext do
      let fvarIds ← getFVarIds hyps
      go fvarIds simplifyTarget
  | Location.wildcard =>
    withMainContext do
      go (← (← getMainGoal).getNondepPropHyps) (simplifyTarget := true)
where
  go (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool) : TacticM Unit := do
    let mvarId ← getMainGoal
    let (result?, usedSimps) ← SciLean.Tactic.ldsimpGoal mvarId ctx (simplifyTarget := simplifyTarget) (fvarIdsToSimp := fvarIdsToSimp)
    match result? with
    | none => replaceMainGoal []
    | some mvarId => replaceMainGoal [mvarId]
    if tactic.simp.trace.get (← getOptions) then
      traceSimpCall (← getRef) usedSimps

@[tactic SciLean.Tactic.LSimp.ldsimp] def evalDSimp : Tactic := fun stx => do
  let { ctx, .. } ← withMainContext <| mkSimpContext stx (eraseLocal := false) (kind := .dsimp)
  dsimpLocation ctx (expandOptLocation stx[5])


set_option linter.unusedVariables false in
open Lean Elab Tactic Conv in
@[tactic SciLean.Tactic.LSimp.ldsimp_conv] def evalDSimpConv : Tactic := fun stx => do
  let { ctx, dischargeWrapper } ← withMainContext <| mkSimpContext stx (eraseLocal := false)

  let e ← getLhs
  let (e', usedSimps) ← SciLean.Tactic.dsimp e ctx

  changeLhs e'

  if tactic.simp.trace.get (← getOptions) then
    traceSimpCall stx usedSimps


example (f : Nat → Nat) :
  (
   let a :=
     let b := f 10
     let x := 5
     let g := hold $ λ n => n + b + 10
     let cd := (3, g (f 42))
     b + cd.1 + g 10 + cd.2 + x
   let z := a + 1
   (a*a*z, a+a+z)).1
  =
  sorry
  :=
by
  -- ldsimp (config := {zeta := false})
  lsimp (config := {zeta := false}) only

  -- dsimp (config := {zeta := false})
  admit

example (f : Nat → Nat) :
  (
   let a :=
     let b := f 10
     b + 10
   (a*a, a+a)).1
  =
  sorry
  :=
by
  ldsimp (config := {zeta := false})
  -- lsimp (config := {zeta := false}) only

  -- dsimp (config := {zeta := false})
  admit
