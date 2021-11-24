import SciLean.Categories

namespace SciLean

instance {n X} [Vec X] : IsLin (sum : (Fin n → X) → X) := sorry

def kron {n} (i j : Fin n) : ℝ := if (i==j) then 1 else 0



