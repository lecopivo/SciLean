import SciLean.Tactic.Autodiff
import SciLean.Lean.Meta.LiftLets

namespace SciLean.Tactic

open Lean Meta Elab Tactic

/--
  Enhanced autodiff tactic that correctly and efficiently differentiates through let bindings.
  
  This tactic focuses on:
  - Handling let bindings in a single pass
  - Ensuring differential/adjoint is fully eliminated
-/

def liftLetsInExpr (e : Expr) : MetaM Expr := do
  e.liftLets2 (fun xs b => do
    if xs.size ≠ 0
    then mkLetFVars xs (← Simp.dsimp b)
    else pure b) {}

@[simp]
theorem lift_lets_theorem (e : α) : e = e := by rfl

simproc_decl lift_lets_simproc (_) := fun e => do
  let E ← inferType e
  if (← Meta.isClass? E).isSome then return .continue
  let e' ← liftLetsInExpr e
  if e == e' then
    return .continue
  else
    return .visit {expr := e', proof := (← mkAppM ``lift_lets_theorem #[e])}

syntax (name := autodiffLetBindingsTacticStx) "autodiff_let" optConfig (discharger)?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*) "]")? : tactic

macro_rules
| `(tactic| autodiff_let $cfg $[$disch]? $[[$a,*]]?) => do
  if a.isSome then
    `(tactic| ((try unfold deriv fgradient adjointFDeriv);
               lfun_trans $cfg $[$disch]? only [deriv, fgradient, adjointFDeriv, simp_core, lift_lets_simproc, $a,*]))
  else
    `(tactic| ((try unfold deriv fgradient adjointFDeriv);
               lfun_trans $cfg $[$disch]? only [deriv, fgradient, adjointFDeriv, simp_core, lift_lets_simproc]))

end SciLean.Tactic
