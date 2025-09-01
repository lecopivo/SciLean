import SciLean

import SciLean
open SciLean

example : Differentiable ℝ (fun ((_,_,z) : ℝ×ℝ×ℝ) => z) := by fun_prop

example
  : (fderiv ℝ (fun ((_,_,z) : ℝ×ℝ×ℝ) => z))
    =
    fun (_,_,_) => fun dx =>L[ℝ] dx.2.2 := by fun_trans
