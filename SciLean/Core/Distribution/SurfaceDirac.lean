import SciLean.Core.Distribution.Basic
import SciLean.Core.Distribution.ParametricDistribDeriv
import SciLean.Core.Integral.Surface

open MeasureTheory

namespace SciLean

variable
  {R} [RealScalar R]
  {X} [Vec R X] [MeasureSpace X]

set_default_scalar R

variable (R)
noncomputable
def surfaceDirac (A : Set X) (d : ℕ) : 𝒟' X := ⟨fun φ => ∫' x in A, φ x ∂(surfaceMeasure d)⟩
variable {R}

@[simp, ftrans_simp]
theorem surfaceDirac_pure (x : X) : surfaceDirac R {x} 0 = pure x := sorry_proof




theorem surfaceDirac.arg_A.DistribDifferentiable
