import Lean 

namespace SciLean

open Lean.Parser.Tactic.Conv

syntax:1 term "rewrite_by" convSeq : term

open Lean Elab Term Meta in
elab_rules : term
| `($x:term rewrite_by $rw:convSeq) => do
  let x ← elabTerm x none
  let eq ← mkFreshExprMVar (← mkEq x x)
  let goals ← Tactic.run eq.mvarId! do
    let _ ← Tactic.evalTactic (← `(tactic| conv => lhs; ($rw)))
    return ()

  if goals.length ≠ 1 then
    throwError "someting unexpected happend with rewrite_by"
  
  return (← (goals.get! 0).getType).getArg! 1
