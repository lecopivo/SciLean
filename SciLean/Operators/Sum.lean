import SciLean.Categories

namespace SciLean

instance {n X} [Vec X] : IsLin (sum : (Fin n → X) → X) := sorry


