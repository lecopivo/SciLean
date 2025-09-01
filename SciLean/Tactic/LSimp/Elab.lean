import SciLean.Tactic.LSimp.Main

namespace SciLean.Tactic.LSimp

open Lean Elab Tactic
open TSyntax.Compat

open Lean Meta


open Lean.Parser.Tactic in
syntax (name:=lsimp_conv) "lsimp" optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? : conv


open Lean.Parser.Tactic in
syntax (name:=lsimp_tactic) "lsimp" optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? : tactic

open private Lean.Meta.Simp.withSimpContext from Lean.Meta.Tactic.Simp.Main

open Lean Elab Tactic in
@[tactic lsimp_conv] unsafe def lsimpConv : Tactic := fun stx => do
  withMainContext do withSimpDiagnostics do
    let { ctx, simprocs, dischargeWrapper } ← mkSimpContext stx (eraseLocal := false)
    let ctx ← ctx.setConfig {ctx.config with zeta:=false}
    -- let ctx := { ctx with config := (← ctx.config.updateArith), lctxInitIndices := (← getLCtx).numIndices }

    let stats ← dischargeWrapper.with fun discharge? => do
      let e ← Conv.getLhs
      let ((e',prf),stats) ←
        Lean.Meta.Simp.withSimpContext ctx do
        lsimpMain e /- k -/ ctx simprocs discharge?
          (k := fun r => do let r ← r.bindVars; pure (r.expr, ← r.getProof))
      Conv.updateLhs e' prf
      return stats

    if tactic.simp.trace.get (← getOptions) then
      traceSimpCall stx stats.usedTheorems

    return stats.diag



open Lean Elab Tactic in
@[tactic lsimp_tactic] unsafe def lsimpTactic : Tactic := fun stx => do
  withMainContext do withSimpDiagnostics do
    let { ctx, simprocs, dischargeWrapper } ← mkSimpContext stx (eraseLocal := false)
    let ctx ← ctx.setConfig {ctx.config with zeta := false}
    -- let ctx := { ctx with config := (← ctx.config.updateArith), lctxInitIndices := (← getLCtx).numIndices }

    let stats ← dischargeWrapper.with fun discharge? => do
      let goal ← getMainGoal
      let e ← goal.getType
      let ((e',prf),stats) ←
        Lean.Meta.Simp.withSimpContext ctx do
        lsimpMain e /- k -/ ctx simprocs discharge?
          (k := fun r => do let r ← r.bindVars; pure (r.expr, ← r.getProof))

      let newGoal ← mkFreshExprMVar e'
      goal.assign (← mkAppM ``Eq.mpr #[prf, newGoal])
      replaceMainGoal [newGoal.mvarId!]
      return stats

    if tactic.simp.trace.get (← getOptions) then
      traceSimpCall stx stats.usedTheorems

    return stats.diag
