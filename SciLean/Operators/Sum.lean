import SciLean.Operators.Adjoint
import SciLean.Operators.Calculus

namespace SciLean

instance {n X} [Vec X] : IsLin (sum : (Fin n → X) → X) := sorry


