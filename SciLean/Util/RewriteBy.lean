import Lean 
-- import Mathlib

namespace SciLean

open Lean.Parser.Tactic.Conv
open Lean.Elab.Tactic.Conv

syntax:1 term "rewrite_by" convSeq : term

open Lean Elab Term Meta in
elab_rules : term
| `($x:term rewrite_by $rw:convSeq) => do
  let x ← elabTerm x none
  let (_, eq) ← mkConvGoalFor x

  let goals ← Tactic.run eq.mvarId! do
    let (lhsNew, proof) ← convert x (Tactic.evalTactic (← `(conv| ($rw))))
    updateLhs lhsNew proof
    return ()
  
  if goals.length = 0 then
    throwError "this is a bug in rewrite_by"

  if goals.length > 1 then
    throwError s!"unsolved goals {← goals.mapM (fun g => do ppExpr (← g.getType))}"
  
  return (← (goals.get! 0).getType).consumeMData.getArg! 1
