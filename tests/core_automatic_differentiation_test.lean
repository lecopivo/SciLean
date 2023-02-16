import SciLean.Core
import SciLean.Tactic.AutoDiff
import SciLean.Tactic.SyntacticRefl

open SciLean

variable {α β γ : Type}
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]

set_option maxHeartbeats 4000
set_option synthInstance.maxHeartbeats 1000
set_option synthInstance.maxSize 80

opaque wait {α : Type} (a : α) : α := a
axiom wait_unfold (a : α) : wait a = a

example : 
  ∂ (λ x : X => 
     let y := x
     let z := y
     z)
  =
  wait (
  λ x dx =>
    let y := x
    let dy := dx
    let z := y
    let dz := dy
    dz)
  := by (conv => lhs; autodiff); rw[wait_unfold]; 
