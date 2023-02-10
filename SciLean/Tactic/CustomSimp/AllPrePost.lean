import SciLean.Tactic.CustomSimp.Main

import Lean.Meta

namespace SciLean.Tactic.CustomSimp

open Lean Meta.Simp

partial def preRewriteAll (e : Expr) : SimpM Step := do
  -- trace[Meta.Tactic.simp] s!"Pre simp on:\n{← Meta.ppExpr e}"
  let e := e.headBeta
  for thms in (← read).simpTheorems do
    if let some r ← rewrite? e thms.pre thms.erased DefaultMethods.discharge? (tag := "pre") (rflOnly := false) then
      -- trace[Meta.Tactic.simp] s!"Simplified to: {← Meta.ppExpr r.expr}"
      return ← andThen (Step.visit r) (λ e => preRewriteAll e)
  return Step.visit { expr := e }

open Lean.Parser.Tactic in
/-- It is called `scilean_simp` for the lack of better name :( -/
syntax (name := scilean_simp) "scilean_simp " (config)? (discharger)? (&"only ")? ("[" (simpStar <|> simpErase <|> simpLemma),* "]")? (location)? : tactic

open Lean.Elab.Tactic in
@[tactic scilean_simp] def evalSciLeanSimp : Tactic := fun stx => do
  let { ctx, dischargeWrapper } ← withMainContext <| mkSimpContext stx (eraseLocal := false)
  let usedSimps ← dischargeWrapper.with fun discharge? =>
    SciLean.Meta.CustomSimp.simpLocation ctx discharge? (expandOptLocation stx[5]) #[] #[]
  if tactic.simp.trace.get (← getOptions) then
    dbg_trace "warning: Runnig custom simp with tracing, not sure if it is working properly!"
    traceSimpCall stx usedSimps


open Lean.Parser.Tactic in
/-- `simp [thm]` performs simplification using `thm` and marked `@[simp]` lemmas.
See the `simp` tactic for more information. -/
syntax (name := scilean_simp_conv) "scilean_simp" (config)? (discharger)? (&" only")? (" [" (simpStar <|> simpErase <|> simpLemma),* "]")? : conv

open Lean.Elab.Tactic Lean.Elab.Tactic.Conv in
@[tactic scilean_simp_conv] def evalSimp : Tactic := fun stx => withMainContext do
  let { ctx, dischargeWrapper, .. } ← mkSimpContext stx (eraseLocal := false)
  let lhs ← getLhs
  let (result, _) ← dischargeWrapper.with fun d? => SciLean.Meta.CustomSimp.simp lhs ctx (discharge? := d?) #[] #[]
  applySimpResult result


