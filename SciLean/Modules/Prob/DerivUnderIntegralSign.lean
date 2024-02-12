import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Integral.Bochner

open MeasureTheory

namespace SciLean.Prob

variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {Y} {_ : MeasurableSpace Y}
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z]


structure DifferentiableUnderIntegralAt (f : X → Y → Z) (μ : X → Measure Y) (x : X) : Prop where
  diff : DifferentiableAt ℝ (fun (x : X) => ∫ y, f x y ∂(μ x)) x

  deriv : ∀ x' dx,
    fderiv ℝ (fun x'' => ∫ y, f x'' y ∂(μ x')) x dx
    =
    ∫ y, fderiv ℝ (f · y) x dx ∂(μ x')


theorem deriv_under_integral_sign {μ : X → Measure Y} {f : X → Y → Z} {x dx : X}
    (h : DifferentiableUnderIntegralAt f μ x)
    /- some conditions on f and μ   -/ :
    fderiv ℝ (fun x => ∫ y, f x y ∂(μ x)) x dx
    =
    fderiv ℝ (fun x' => ∫ y, f x y ∂(μ x')) x dx
    +
    ∫ y, fderiv ℝ (f · y) x dx ∂(μ x) := sorry
