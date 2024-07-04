import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Hausdorff
-- import SciLean.Core.Obj.Scalar

import SciLean.Mathlib.Analysis.AdjointSpace.Adjoint
import SciLean.Core.Integral.Jacobian
import SciLean.Core.Integral.PlaneDecomposition'
import SciLean.Tactic.GTrans

open MeasureTheory

namespace SciLean


variable
  {R} [RealScalar R]
  {W} [NormedAddCommGroup W] [NormedSpace R W]
  {X} [NormedAddCommGroup X] [AdjointSpace ℝ X] [AdjointSpace R X] [MeasurableSpace X] [BorelSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedSpace R Y] [CompleteSpace Y]
  {Z} [SemiHilbert R Z] [Module ℝ Z]
  {X₁ : I → Type}
  {X₂ : I → Type}

open FiniteDimensional

-- @[ftrans_simp]
-- theorem surface_integral_parametrization
--     (f : X → Y) (A : Set X)
--     {U param} (p : SetParametrization A U param)
--     [NormedAddCommGroup U] [AdjointSpace ℝ U] [MeasureSpace U]
--     (hdim : d = finrank ℝ U) :
--     (∫ x in A, f x ∂μH[d])
--     =
--     param.foldl (init:=(0:Y))
--       fun s (dom,p) => s + ∫ u in dom, jacobian ℝ p u • f (p u) := sorry_proof


variable (R)
theorem surface_integral_parametrization_inter
    (f : X → Y) (A B : Set X)
    {U param} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (p : SurfaceParametrization A U param)
    [MeasureSpace U] [AdjointSpace R U] :
    (∫ x in A ∩ B, f x ∂μH[d])
    =
    param.foldl (init:=(0:Y))
      fun s (dom,p) => s + ∫ u in dom ∩ p ⁻¹' B, let x := p u; jacobian R p u • f x := sorry_proof
