import Lean.Meta

namespace SciLean.Tactic.CustomSimp

open Lean Meta.Simp

partial def preRewriteAll (e : Expr) : SimpM Step := do
  trace[Meta.Tactic.simp] s!"Pre simp on: {← Meta.ppExpr e}"
  let e ← Meta.whnf e
  for thms in (← read).simpTheorems do
    if let some r ← rewrite? e thms.pre thms.erased DefaultMethods.discharge? (tag := "pre") (rflOnly := false) then
      trace[Meta.Tactic.simp] s!"Simplified to: {← Meta.ppExpr e}"
      return ← andThen (Step.visit r) (λ e => preRewriteAll e)
  return Step.visit { expr := e }
