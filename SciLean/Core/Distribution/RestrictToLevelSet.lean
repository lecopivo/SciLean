import Mathlib.MeasureTheory.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Mathlib.MeasureTheory.Measure.VectorMeasure

import SciLean.Core.Distribution.Basic
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

def Distribution.IsVectorMeasure (f : 𝒟'(X,U)) : Prop :=
  ∃ (μ : VectorMeasure X U), ∀ (φ : 𝒟 X),
      f φ = vectorIntegral (fun x => φ x) μ (fun u v => u•v)

open Classical
noncomputable
def Distribution.toVectorMeasure (f' : 𝒟'(X,U)) : VectorMeasure X U :=
  if h : f'.IsVectorMeasure then
    choose h
  else
    0



variable (R)


/-- Given a familly of surfaces `S`, restrict `u` to the surface `S w`.

It is necessary that the distribution `u` just an integrable function `f` i.e.
`⟨u,φ⟩ = ∫ x, φ x • f x` -/
noncomputable
def Distribution.restrictToFrontier (u : 𝒟'(X,U)) (S : W → Set X) (w dw : W) : 𝒟'(X,U) :=
  let s := fun x => (frontierSpeed R S w dw x)
  let dudV := u.toFunction
  fun φ ⊸ ∫' x in S w, (φ x * s x) • dudV x ∂(surfaceMeasure (finrank R X - 1))

variable {R}



#exit
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
