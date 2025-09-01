import SciLean.Analysis.Calculus.HasParamDerivWithDisc.HasParamFDerivWithDisc
import SciLean.Analysis.Calculus.HasParamDerivWithDisc.HasParamFwdFDerivWithDisc
import SciLean.Analysis.Calculus.HasParamDerivWithDisc.HasParamRevFDerivWithDisc

import SciLean.Analysis.SpecialFunctions.Norm2
import SciLean.Analysis.SpecialFunctions.Exp
import SciLean.Analysis.SpecialFunctions.Trigonometric
import SciLean.Analysis.SpecialFunctions.Gaussian



namespace SciLean

open MeasureTheory Scalar

section NormedSpace

variable
  {R} [RealScalar R]
  {W} [NormedAddCommGroup W] [AdjointSpace R W] [CompleteSpace W]
  {U} [NormedAddCommGroup U] [AdjointSpace R U] [NormedSpace ℝ U] [CompleteSpace U]
  {X} [NormedAddCommGroup X] [AdjointSpace R X] [NormedSpace ℝ X] [CompleteSpace X] [MeasureSpace X] [BorelSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace R Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace R Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  {V} [NormedAddCommGroup V] [AdjointSpace R V] [NormedSpace ℝ V] [CompleteSpace V]


----------------------------------------------------------------------------------------------------
-- Trigonometric functions -------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- sin

@[gtrans]
def Scalar.sin.arg_a0.HasParamFDerivWithDiscAt_rule :=
  (HasParamFDerivWithDiscAt.comp1_differentiable_discs_rule
   (R:=R) (W:=W) (X:=X) (Y:=R) (Z:=R) (fun _ y => sin y) (by simp; fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
def Scalar.sin.arg_a0.HasParamFwdFDerivWithDiscAt_rule :=
  (HasParamFwdFDerivWithDiscAt.comp1_differentiable_discs_rule
   (R:=R) (W:=W) (X:=X) (Y:=R) (Z:=R) (fun _ y => sin y) (by simp; fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[gtrans]
def Scalar.sin.arg_a0.HasParamRevFDerivWithDiscAt_rule :=
  (HasParamRevFDerivWithDiscAt.comp1_differentiable_discs_rule
   (R:=R) (W:=W) (X:=X) (Y:=R) (Z:=R) (fun _ y => sin y) (by simp; fun_prop))
  rewrite_type_by (repeat ext); autodiff


-- cos

@[gtrans]
def Scalar.cos.arg_a0.HasParamFDerivWithDiscAt_rule :=
  (HasParamFDerivWithDiscAt.comp1_differentiable_discs_rule
   (R:=R) (W:=W) (X:=X) (Y:=R) (Z:=R) (fun _ y => cos y) (by simp; fun_prop))
  -- rewrite_type_by (repeat ext); autodiff

@[gtrans]
def Scalar.cos.arg_a0.HasParamFwdFDerivWithDiscAt_rule :=
  (HasParamFwdFDerivWithDiscAt.comp1_differentiable_discs_rule
   (R:=R) (W:=W) (X:=X) (Y:=R) (Z:=R) (fun _ y => cos y) (by simp; fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[gtrans]
def Scalar.cos.arg_a0.HasParamRevFDerivWithDiscAt_rule :=
  (HasParamRevFDerivWithDiscAt.comp1_differentiable_discs_rule
   (R:=R) (W:=W) (X:=X) (Y:=R) (Z:=R) (fun _ y => cos y) (by simp; fun_prop))
  rewrite_type_by (repeat ext); autodiff


-- gaussian

@[gtrans]
def gaussian.arg_a0.HasParamFDerivWithDiscAt_rule (σ : R) :=
  (HasParamFDerivWithDiscAt.comp2_differentiable_discs_rule
   (R:=R) (W:=W) (X:=X) (Y₁:=X) (Y₂:=X) (Z:=R) (fun _ μ x => gaussian μ σ x) (by simp; fun_prop))
  -- rewrite_type_by (repeat ext); autodiff

@[gtrans]
def gaussian.arg_a0.HasParamFwdFDerivWithDiscAt_rule (σ : R) :=
  (HasParamFwdFDerivWithDiscAt.comp2_differentiable_discs_rule
   (R:=R) (W:=W) (X:=X) (Y₁:=X) (Y₂:=X) (Z:=R) (fun _ μ x => gaussian μ σ x) (by simp; fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[gtrans]
def gaussian.arg_a0.HasParamRevFDerivWithDiscAt_rule (σ : R) :=
  (HasParamRevFDerivWithDiscAt.comp2_differentiable_discs_rule
   (R:=R) (W:=W) (X:=X) (Y₁:=X) (Y₂:=X) (Z:=R) (fun _ μ x => gaussian μ σ x) (by simp; fun_prop))
  rewrite_type_by (repeat ext); autodiff


-- ‖·‖₂²

@[gtrans]
def Norm2.norm2.HasParamFDerivWithDiscAt_rule :=
  (HasParamFDerivWithDiscAt.comp1_differentiable_discs_rule (R:=R) (W:=W) (X:=X) (Y:=U) (Z:=R)
    (fun _ y => ‖y‖₂²[R]) (by simp; fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[gtrans]
def Norm2.norm2.HasParamFwdFDerivWithDiscAt_rule :=
  (HasParamFwdFDerivWithDiscAt.comp1_differentiable_discs_rule (R:=R) (W:=W) (X:=X) (Y:=U) (Z:=R)
    (fun _ y => ‖y‖₂²[R]) (by simp; fun_prop))
  rewrite_type_by (repeat ext); autodiff

open Scalar in
@[gtrans]
def Norm2.norm2.HasParamRevFDerivWithDiscAt_rule :=
  (HasParamRevFDerivWithDiscAt.comp1_differentiable_discs_rule (R:=R) (W:=U) (X:=X) (Y:=V) (Z:=R)
    (fun _ y => ‖y‖₂²[R]) (by simp; fun_prop))
  rewrite_type_by (repeat ext); autodiff


end NormedSpace
