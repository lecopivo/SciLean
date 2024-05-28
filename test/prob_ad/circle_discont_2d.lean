import SciLean.Core.Integral.Common
import SciLean.Core.Functions.Trigonometric
import SciLean.Tactic.IfPull

open SciLean MeasureTheory Set

variable
  {R : Type} [RealScalar R] [MeasureSpace R] [PlainDataType R]

set_default_scalar R

open Scalar
def circleParam (θ : R) : R×R := (cos θ, sin θ)

@[fun_prop]
theorem circleParam.arg_θ.HasAdjDiff_rule :
    HasAdjDiff R (circleParam (R:=R)) := by unfold circleParam; fun_prop

@[fun_trans]
theorem circleParam.arg_θ.jacobian_rule :
    jacobian R (circleParam (R:=R)) = 1 := by
  unfold circleParam jacobian; autodiff; autodiff; simp; sorry_proof

-- theorem asdf (r : R) :
--   ParametricInverseAt {x : R×R | x.1 ^ 2 + y.2 ^ 2 - r ^ 2 = 0}
open Scalar Set in
@[gtrans]
theorem circle_parametric_inverse_polar (r : R) (hr : r ≠ 0) :
    ParametricInverseAt (fun x : R×R => x.1 ^ 2 + x.2 ^ 2 - r ^ 2 - 0) 0
      (I:=Unit)
      (X₁:= fun _ => R)
      (X₂:= fun _ => R)
      (p := fun _ θ s => s • circleParam θ)
      (g := fun _ _ => r)
      (dom := fun _ => Ico 0 (2*RealScalar.pi)) := by
  simp[ParametricInverseAt]; intros; sorry_proof

set_option trace.Meta.Tactic.fun_trans true
set_option trace.Meta.Tactic.fun_trans.rewrite true
set_option trace.Meta.Tactic.fun_trans.discharge true
-- set_option trace.Meta.Tactic.gtrans true
set_option trace.Meta.Tactic.simp.rewrite true


example (w : R) (hw : w ≠ 0) :
    (∂ w':=w,
      ∫' x in Icc (0:R) 1, ∫' y in Icc (0:R) 1,
        if x^2 + y^2 ≤ w'^2 then (1:R) else 0)
    =
    sorry := by

  conv =>
    lhs
    integral_deriv
    autodiff
    -- unfold jacobian
    -- autodiff
    -- autodiff

  sorry_proof

#exit

variable (w : R)

/--
info: let ds :=
  ∫' x,
    jacobian R (fun x => (planeDecomposition (1, 1) ⋯) (w / Scalar.sqrt (1 + 1), x)) x *
      (Scalar.sqrt
          (1 +
            1))⁻¹ ∂volume.restrict
      (preimageSnd ((fun x12 => (planeDecomposition (1, 1) ⋯) x12) ⁻¹' Icc 0 1 ×ˢ Icc 0 1) (w / Scalar.sqrt (1 + 1)));
ds : R
-/
#guard_msgs in
#check (∂ w':=w,
      ∫' x in Icc (0:R) 1, ∫' y in Icc (0:R) 1,
        if x + y ≤ w' then (1:R) else 0) rewrite_by integral_deriv; autodiff
