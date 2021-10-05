import SciLean.Prelude
import SciLean.Tactic.RemoveLambdaLet

import Lean
import Lean.Meta.Basic
import Lean.Elab.Tactic.Basic

-- It is necessary only if `SciLean.Prelude` is imported. But why???
set_option synthInstance.maxHeartbeats 10000

open Lean 
open Lean.Meta
open Lean.Elab.Tactic

namespace Autodiff
  def diff_intro {X Y} [Vec X] [Vec Y] (f : X → Y) : δ f = λ x dx => δ f x dx := by simp
end Autodiff

syntax (name := autodiff) "autodiff" notFollowedBy("|") : tactic

@[tactic autodiff] def tacticAutodiff : Tactic
| `(tactic| autodiff ) => do
            evalTactic (← `(tactic| rmlamlet; rw [Autodiff.diff_intro]; simp))
| _ => Lean.Elab.throwUnsupportedSyntax
