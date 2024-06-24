import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.Erased
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Hausdorff

import SciLean.Core.NotationOverField
import SciLean.Mathlib.Analysis.AdjointSpace.Adjoint
-- import SciLean.Core.Integral.MovingDomain

import SciLean.Core.FunctionTransformations.RevFDeriv
import SciLean.Core.FunctionTransformations.FwdFDeriv
import SciLean.Core.Integral.HasParamDerivWithJumps

open MeasureTheory Topology Filter

namespace SciLean

variable
  {R} [RealScalar R] [MeasureSpace R]
  {W} [NormedAddCommGroup W] [NormedSpace R W]
  {X} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace R Y] [NormedSpace ℝ Y]

set_default_scalar R


variable (R)
def HasParamFwdFDerivWithJumpsAt (f : W → X → Y) (w : W)
    (f' : W → X → Y×Y)
    (I : Type)
    /- Values of `f` on both sides of jump discontinuity.

    The first value is in the positive noramal direction and the second value in the negative
    normal direction.

    The orientation of the normal is arbitrary but fixed as `jumpVals` and `jumpSpeed` depend on it. -/
    (jumpVals : I → X → Y×Y)
    /- Normal speed of the jump discontinuity. -/
    (jumpSpeed : I → W → X → R)
    /- Jump discontinuities of `f`. -/
    (jump : I → Set X) : Prop := ∃ J Ω ι,
  HasParamFDerivWithJumpsAtImpl R f w (fun w x => (f' w x).2) I J ι Ω jumpVals jumpSpeed jump
  ∧
  ∀ w x, (f' w x).1 = f w x


def HasParamFwdFDerivWithJumps (f : W → X → Y)
    (f' : W → W → X → Y×Y)
    (I : Type)
    (jumpVals : I → W → X → Y×Y)
    (jumpSpeed : I → W → W → X → R)
    (jump : I → W → Set X) := ∀ w : W, HasParamFwdFDerivWithJumpsAt R f w (f' w) I (jumpVals · w) (jumpSpeed · w) (jump · w)

variable {R}



open FiniteDimensional
@[fun_trans]
theorem fwdFDeriv_under_integral
  {X} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X] [MeasureSpace X] [BorelSpace X]
  (f : W → X → Y) (w : W) (μ : Measure X)
  (I) [IndexType I]
  (hf : Σ' f' df s S, HasParamFwdFDerivWithJumpsAt R f w f' I df s S) (dw : W) :
  (fwdFDeriv R (fun w' => ∫ x, f w' x ∂μ) w)
  =
  let ⟨f', df, s, S, _⟩ := hf
  fun dw =>
    let interior := ∫ x, f' dw x ∂μ
    let density := fun x => Scalar.ofENNReal (R:=R) (μ.rnDeriv volume x)
    let shocks := ∑ i, ∫ x in S i, (s i dw x * density x) • ((df i x).1 - (df i x).2) ∂μH[finrank R X - 1]
    (interior.1, interior.2 + shocks) := sorry_proof
