import SciLean.Core.Integral.MovingDomain
import SciLean.Core.Integral.Substitution
import SciLean.Core.Integral.ParametricInverse
import SciLean.Core.Integral.Frontier
import SciLean.Core.Functions.Trigonometric

open MeasureTheory

namespace SciLean

variable
  {R} [RealScalar R]
  {W} [SemiHilbert R W]
  {X} [SemiHilbert R X]
  {Y} [SemiHilbert R Y] [Module ℝ Y]
  {Z} [SemiHilbert R Z] [Module ℝ Z]

set_default_scalar R

variable [MeasureSpace R] [Module ℝ R]

attribute [ftrans_simp] FiniteDimensional.finrank_prod FiniteDimensional.finrank_self Finset.univ_unique Finset.sum_const Finset.card_singleton Prod.smul_mk -- Nat.reduceAdd

@[simp, ftrans_simp]
theorem Scalar.sqrt_pow (r : R) : Scalar.sqrt (r^2) = Scalar.abs r := sorry_proof

@[simp, ftrans_simp]
theorem Scalar.abs_abs (r : R) : Scalar.abs (Scalar.abs r) = Scalar.abs r := sorry_proof
