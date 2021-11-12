import SciLean.Prelude
import SciLean.Tactic.RemoveLambdaLet
import SciLean.Tactic.Autodiff

import Lean
import Lean.Meta.Basic
import Lean.Elab.Tactic.Basic

-- It is necessary only if `SciLean.Prelude` is imported. But why???
set_option synthInstance.maxHeartbeats 10000

open Lean 
open Lean.Meta
open Lean.Elab.Tactic

namespace Autograd

  def comp_dual_intro {α X} [Vec X] (f : α → (X → ℝ)) : comp dual f = (λ x => dual (f x)) := by funext x; simp; done

end Autograd


syntax (name := autograd) "autograd" notFollowedBy("|") : tactic

@[tactic autograd] def tacticAutograd : Tactic
| `(tactic| autograd ) => do
            evalTactic (← `(tactic| autodiff; rmlamlet; rw [Autograd.comp_dual_intro]; simp;))
| _ => Lean.Elab.throwUnsupportedSyntax
