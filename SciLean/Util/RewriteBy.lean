import Lean
-- import Mathlib

namespace SciLean

open Lean.Parser.Tactic.Conv
open Lean.Elab.Tactic.Conv

open Lean Elab Term Meta

def elabConvRewrite (e : Expr) (assumptions : Array Syntax) (stx : TSyntax `conv) : TermElabM (Expr × Expr) := do
  elabBinders assumptions fun as => do
  let (rhs, eq) ← mkConvGoalFor e

  let goals ← Tactic.run eq.mvarId! do

    let (lhsNew, proof) ← convert e (Tactic.evalTactic stx)
    if let .some a := as.find? (fun a => lhsNew.containsFVar a.fvarId!) then
      throwError "rewritten expreesion can't contain assumption {← ppExpr a}"
    updateLhs lhsNew proof
    return ()

  if goals.length = 0 then
    throwError "this is a bug in rewriteByConv"

  if goals.length > 1 then
    throwError s!"error in `rewriteByConv`, unsolved goals {← goals.mapM (fun g => do ppExpr (← g.getType))}"

  (goals.get! 0).refl

  return (← instantiateMVars rhs, ← instantiateMVars eq)

def rewriteByConv (e : Expr) (stx : TSyntax `conv) : MetaM (Expr × Expr) := do
  let (r,_) ← (elabConvRewrite e #[] stx).run {} {}
  return r


syntax:1 term "rewrite_by" (" assuming" bracketedBinder*)?  convSeq : term

elab_rules : term
| `($x:term rewrite_by $[assuming $as*]? $rw:convSeq) => do
  let x ← elabTerm x none
  let as := as.getD #[]
  synthesizeSyntheticMVarsNoPostponing
  let (x',_eq) ← elabConvRewrite x as (← `(conv| ($rw)))
  return x'
