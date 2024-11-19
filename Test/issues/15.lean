import SciLean

import SciLean
open SciLean

example : CDifferentiable ℝ (fun ((_,_,z) : ℝ×ℝ×ℝ) => z) := by fun_prop

example
  : (cderiv ℝ (fun ((_,_,z) : ℝ×ℝ×ℝ) => z))
    =
    fun (_,_,_) (_,_,dz) => dz := by fun_trans
