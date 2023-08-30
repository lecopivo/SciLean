import SciLean

import SciLean
open SciLean

example : IsDifferentiable ℝ (fun ((_,_,z) : ℝ×ℝ×ℝ) => z) := by dsimp; fprop

example 
  : (cderiv ℝ (fun ((_,_,z) : ℝ×ℝ×ℝ) => z))
    =
    fun (_,_,z) (_,_,dz) => dz := by dsimp; ftrans only
