import SciLean.Tactic.LSimp.Main
import SciLean.Core

namespace SciLean.Tactic.LSimp

open Lean Elab Tactic
open TSyntax.Compat

open Lean Meta


open Lean.Parser.Tactic in
syntax (name:=lsimp_conv) "lsimp" (config)? (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? : conv


open Lean Elab Tactic in
@[tactic lsimp_conv] unsafe def lsimpConv : Tactic := fun stx => do
  withMainContext do withSimpDiagnostics do
    let { ctx, simprocs, dischargeWrapper } ← mkSimpContext stx (eraseLocal := false)
    let ctx := { ctx with config := { ctx.config with zeta := false } }
    let stats ← dischargeWrapper.with fun discharge? => do
      let e ← Conv.getLhs
      let ((e',prf),stats) ←
        lsimpMain e /- k -/ ctx simprocs discharge?
          (k := fun r => do let r ← r.bindVars; pure (r.expr, ← r.getProof))
      Conv.updateLhs e' prf
      return stats

    if tactic.simp.trace.get (← getOptions) then
      traceSimpCall stx stats.usedTheorems

    return stats.diag
