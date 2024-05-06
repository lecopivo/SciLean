import Mathlib.MeasureTheory.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Mathlib.MeasureTheory.Measure.VectorMeasure

import SciLean.Core.Integral.Surface
import SciLean.Core.Integral.MovingDomain
import SciLean.Core.Integral.VectorIntegral

import SciLean.Core.Objects.Scalar

namespace SciLean

open MeasureTheory FiniteDimensional

variable
  {R} [RealScalar R] [MeasureSpace R]
  {W} [Vec R W]
  {X} [SemiHilbert R X] [MeasureSpace X]
  {U} [Vec R U] [Module ℝ U]

set_default_scalar R


-- /-- Given a family of surface `S`, compute the surface speed in the normal direction at point `x`
--  and time `t`.

-- TODO: Fix the definition if `x` is not a point on the surface `S t`.
--       Possible return values are:
--         - speed on the closes point
--         - zero -/
-- noncomputable
-- def surfaceSpeed (S : R → Set X) (x : X) (t : R) : R :=
--   -- 'if _ then _ else _' breaks where for some reason
--   match Classical.dec (∃ (φ : X → R → R), (∀ t, S t = {x | φ x t = 0})) with
--   | .isTrue h =>
--     let φ := Classical.choose h
--     (-(∂ (t':=t), φ x t')/‖∇ x':=x, φ x' t‖₂)
--   | .isFalse _ => 0


-- /-- Given a familly of surfaces `S`, restrict `μ` to the surface `S θ`.

-- It is necessary that `μ` is absolutely continuous w.r.t. to Lebesgue measure and that `S` vary
-- smoothly.  -/
-- noncomputable
-- def _root_.MeasureTheory.Measure.restrictToSurface (μ : Measure X) (S : R → Set X) (θ : R) :
--     Measure X where
--   measureOf := fun A =>
--     let Dφ := fun x => Scalar.toENNReal (surfaceSpeed S x θ)
--     let dμdV := μ.rnDeriv volume
--     ∫⁻ x in A ∩ S θ, Dφ x * dμdV x ∂(surfaceMeasure (finrank R X - 1))
--   empty := sorry_proof
--   mono := sorry_proof
--   iUnion_nat := sorry_proof
--   m_iUnion := sorry_proof
--   trimmed := sorry_proof



variable (R)

/-- Given a familly of surfaces `S`, restrict `μ` to the surface `S w`.

It is necessary that `μ` is absolutely continuous w.r.t. to Lebesgue measure and that `S` vary
smoothly.  -/
noncomputable
def _root_.MeasureTheory.Measure.restrictToFrontier (μ : Measure X) (S : W → Set X) (w dw : W) :
    VectorMeasure X R where
  measureOf' := fun A =>
    let s := fun x => (frontierSpeed R S w dw x)
    let dμdV := fun x => (μ.rnDeriv volume x).toReal
    ∫ x in A ∩ S w, s x * dμdV x ∂(surfaceMeasure (finrank R X - 1))
  empty' := sorry_proof
  not_measurable' := sorry_proof
  m_iUnion' := sorry_proof


variable {R}


/-- Restrict measure `μ` to `θ` level set of a function `φ` obtaining (n-1)-dimensional integral -/
noncomputable
def _root_.MeasureTheory.Measure.restrictToLevelSet (μ : Measure X) (φ : W → X → R) (w dw : W) :
    VectorMeasure X R := μ.restrictToFrontier R (fun w => {x | φ w x ≤ 0}) w dw


@[ftrans_simp]
theorem restrictToFrontier_eq_restrictToLevelSet (μ : Measure X) (φ ψ : W → X → R) :
  μ.restrictToFrontier R (fun w => {x | φ w x ≤ ψ w x})
  =
  μ.restrictToLevelSet (fun w x => φ w x - ψ w x) := sorry_proof


-- /-- Volume integral can be split into integral over reals and level sets.

--   TODO: add proper assumptions:
--             - integrability of f
--             - non-zero gradient of `φ` almost everywhere
--             - `μ ≪ volume`
-- -/
-- theorem cintegral_cintegral_conditionOn (f : X → U) (φ : X → R) (μ : Measure X) :
--     ∫' t, ∫' x, f x ∂(μ.restrictToLevelSet (fun t x => φ x - t) t)
--     =
--     ∫' x, f x ∂μ := sorry_proof



-- /-- Derivative of integral over sub-levelsets is equal to the integral over level set.

--   TODO: add proper assumptions:
--             - integrability of f
--             - non-zero gradient of `φ` almost everywhere
--             - `μ ≪ volume`
-- -/
-- theorem cderiv_cintegral_in_level_set (f : X → U) (φ : W → X → R) (μ : Measure X) :
--     (cderiv R fun w => ∫' x in {x | φ w x ≤ 0}, f x ∂μ)
--     =
--     fun w dw => dw • ∫' x, f x ∂(μ.restrictToLevelSet φ w dw) := sorry_proof
