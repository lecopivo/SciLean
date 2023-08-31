import SciLean
open SciLean

example : IsDifferentiable ℝ (fun ((_,_,z) : ℝ×ℝ×ℝ) => z) := by fprop

example 
  : (cderiv ℝ (fun ((_,_,z) : ℝ×ℝ×ℝ) => z))
    =
    fun (_,_,_) (_,_,dz) => dz := by ftrans only
