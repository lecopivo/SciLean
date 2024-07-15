import SciLean.Core.Transformations.HasParamDerivWithJumps.HasParamFDerivWithJumps
import SciLean.Core.Transformations.HasParamDerivWithJumps.HasParamFwdFDerivWithJumps
import SciLean.Core.Transformations.HasParamDerivWithJumps.HasParamRevFDerivWithJumps
import SciLean.Core.Functions.Norm2

open MeasureTheory

namespace SciLean


section NormedSpace

variable
  {R} [RealScalar R]
  {W} [NormedAddCommGroup W] [NormedSpace R W]
  {U} [NormedAddCommGroup U] [AdjointSpace R U] [NormedSpace ℝ U] [CompleteSpace U]
  {X} [NormedAddCommGroup X] [AdjointSpace R X] [NormedSpace ℝ X] [CompleteSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace R Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace R Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  {V} [NormedAddCommGroup V] [AdjointSpace R V] [NormedSpace ℝ V] [CompleteSpace V]


open Scalar in
@[gtrans]
def Norm2.norm2.HasParamFDerivWithJumpsAt_rule :=
  (HasParamFDerivWithJumpsAt.comp1_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y:=U) (Z:=R)
    (fun _ y => ‖y‖₂²[R]) (by simp; fun_prop))
  rewrite_type_by (repeat ext); autodiff


open Scalar in
@[gtrans]
def Norm2.norm2.HasParamFwdFDerivWithJumpsAt_rule :=
  (HasParamFwdDerivWithJumps.comp1_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y:=U) (Z:=R)
    (fun _ y => ‖y‖₂²[R]) (by simp; fun_prop))
  rewrite_type_by (repeat ext); autodiff

open Scalar in
@[gtrans]
def Norm2.norm2.HasParamRevFDerivWithJumpsAt_rule :=
  (HasParamRevFDerivWithJumpsAt.comp1_smooth_jumps_rule (R:=R) (W:=U) (X:=X) (Y:=V) (Z:=R)
    (fun _ y => ‖y‖₂²[R]) (by simp; fun_prop))
  rewrite_type_by (repeat ext); autodiff


end NormedSpace
