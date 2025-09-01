import Mathlib.Data.Set.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff

import SciLean.Analysis.Scalar
-- import SciLean.Analysis.Calculus.Jacobian
import SciLean.Tactic.GTrans

open MeasureTheory

namespace SciLean


/-- `SurfaceParametrization A [(dom₁,p₁), ..., (domₙ,pₙ)]` says that the set `A` (assumed to be a
surface) is parametrized by functions `pᵢ` with domain `domᵢ`. -/
@[gtrans]
structure SurfaceParametrization
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : Set X)
    (U : outParam <| Type) [outParam (NormedAddCommGroup U)] [outParam (NormedSpace ℝ U)]
    (param : outParam <| List (Set U × (U → X))) : Prop where

  /-- Every point of the parametrization yields a point in `A`. -/
  is_parametrization : ∀ p ∈ param, let (domᵢ,pᵢ) := p; ∀ u ∈ domᵢ, pᵢ u ∈ A
  /-- Every point in `A` has unique parametrization representative. -/
  complete_and_unique : ∀ x ∈ A, ∃! p ∈ param, ∃! u ∈ p.1, p.2 u = x
  /-- Interior of every domain `domᵢ` can't be empty. Thanks to this we are really working with
  a surface parametrization. -/
  non_empty_interior : ∀ p ∈ param, let (domᵢ,_) := p; interior domᵢ ≠ ∅
  /-- Parametrizations `pᵢ` are differentiable. -/
  differentiable : ∀ p ∈ param, let (domᵢ,pᵢ) := p; DifferentiableOn ℝ pᵢ domᵢ



set_option deprecated.oldSectionVars true
variable
  {R} [RealScalar R]
  {X} [NormedAddCommGroup X] [AdjointSpace ℝ X] [AdjointSpace R X] [MeasurableSpace X] [BorelSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedSpace R Y] [CompleteSpace Y]


-- variable (R)
-- set_option linter.unusedVariables false in
-- theorem surface_integral_parametrization_inter
--     (f : X → Y) (A B : Set X)
--     {U param} [NormedAddCommGroup U] [NormedSpace ℝ U]
--     (p : SurfaceParametrization A U param)
--     [MeasureSpace U] [AdjointSpace R U] :
--     (∫ x in A ∩ B, f x ∂μH[d])
--     =
--     param.foldl (init:=(0:Y))
--       fun s (dom,p) => s + ∫ u in dom ∩ p ⁻¹' B, let x := p u; jacobian R p u • f x := sorry_proof
