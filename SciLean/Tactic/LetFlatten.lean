import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Conv.Basic

import SciLean.Lean.Meta.Basic

namespace SciLean.Meta

open Lean Meta Elab Tactic Conv

syntax (name := let_flatten) " let_flatten " : conv 

@[tactic let_flatten] 
def convLetFlatten : Tactic
| `(conv| let_flatten) => do  
  (← getMainGoal).withContext do
    let lhs ← getLhs
    let lhs' ← flattenLet 100 lhs
    
    changeLhs lhs'
| _ => Lean.Elab.throwUnsupportedSyntax
