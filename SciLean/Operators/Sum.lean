import SciLean.Mathlib.Data.Iterable
import SciLean.Categories

namespace SciLean

instance {X ι} [Vec X] [Iterable ι] : IsLin (Iterable.sum : (ι → X) → X) := sorry

@[inline] 
def kron {ι} (i j : ι) [DecidableEq ι] : ℝ := if (i==j) then 1 else 0
