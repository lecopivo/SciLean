import SciLean.Prelude

variable {X} [Vec X]
variable {U} [Hilbert U]

instance : IsLin (sum : (Fin n → X) → X) := sorry

@[simp] def sum_adjoint : adjoint (sum : (Fin n → U) → U) = const (Fin n) := sorry
@[simp] def sum_dual : dual (sum : (Fin n → ℝ) → ℝ) = const (Fin n) 1 := sorry


