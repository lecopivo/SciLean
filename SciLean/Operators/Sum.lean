import SciLean.Mathlib.Data.Enumtype
import SciLean.Categories

namespace SciLean

instance {X ι} [Vec X] [Enumtype ι] : IsLin (Enumtype.sum : (ι → X) → X) := sorry

@[inline] 
def kron {ι} (i j : ι) [DecidableEq ι] : ℝ := if (i==j) then 1 else 0
