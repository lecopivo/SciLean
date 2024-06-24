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

import Mathlib.Lean.CoreM

open MeasureTheory Topology Filter

namespace SciLean

variable
  {R} [RealScalar R] [MeasureSpace R] [BorelSpace R]
  {W} [NormedAddCommGroup W] [AdjointSpace R W] [NormedSpace ℝ W] [CompleteSpace W]
  {X} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X] [MeasureSpace X] [BorelSpace X]
  {Y} [NormedAddCommGroup Y] [AdjointSpace R Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  {Z} [NormedAddCommGroup Z] [AdjointSpace R Z]

set_default_scalar R


variable (R)
def HasParamRevFDerivWithJumpsAt (f : W → X → Y) (w : W)
    (f' : X → Y×(Y→W))
    (I : Type)
    /- Values of `f` on both sides of jump discontinuity.

    The first value is in the positive noramal direction and the second value in the negative
    normal direction.

    The orientation of the normal is arbitrary but fixed as `jumpVals` and `jumpSpeed` depend on it. -/
    (jumpVals : I → X → Y×Y)
    /- Normal speed of the jump discontinuity. -/
    (jumpGrad : I → X → W)
    /- Jump discontinuities of `f`. -/
    (jump : I → Set X)  :=
  HasParamFDerivWithJumpsAt R f w
    (fun (dw : W) (x : X) => adjoint R (fun dy => ⟪(f' x).2 dy, dw⟫) 1)
    I jumpVals
    (fun (i : I) (dw : W) (x : X) => ⟪jumpGrad i x, dw⟫)
    jump
  ∧
  ∀ x, (f' x).1 = f w x


variable {R}



open FiniteDimensional
@[fun_trans]
theorem revFDeriv_under_integral
  (f : W → X → Y) (w : W) (μ : Measure X)
  (I) [IndexType I]
  (hf : Σ' f' df s S, HasParamRevFDerivWithJumpsAt R f w f' I df s S) :
  (revFDeriv R (fun w' => ∫ x, f w' x ∂μ) w)
  =
  let ⟨f', df, s, S, _⟩ := hf
  let val := ∫ x, f w x ∂μ
  (val, fun dy =>
    let interior := ∫ x, (f' x).2 dy ∂μ
    let density := fun x => Scalar.ofENNReal (R:=R) (μ.rnDeriv volume x)
    let shocks := ∑ i, ∫ x in S i, (⟪(df i x).1 - (df i x).2, dy⟫ * density x) • s i x ∂μH[finrank R X - 1]
    interior + shocks) := sorry_proof


variable (w : X) [NormedSpace ℝ X]

#check (revFDeriv R (fun w : X => ∫ (x : R), if ‖x‖₂ ≤ ‖w‖₂² then x•w else ‖w‖₂²•w) w)
  rewrite_by
    rw[revFDeriv_under_integral (I:=Fin 1) (hf:=by sorry)]


#check (revFDeriv R (fun w => ∫ (x : X), if ‖x‖₂ ≤ ⟪x,w⟫ then ⟪w,x⟫ else ‖w‖₂² * ‖x‖₂²) w)
  rewrite_by
    rw[revFDeriv_under_integral (I:=Fin 1) (hf:=by sorry)]
