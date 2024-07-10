import SciLean.Core.Transformations.HasParamDerivWithJumps.Common
import SciLean.Core.Transformations.SurfaceParametrization
import SciLean.Core.Rand.Distributions.Uniform
import SciLean.Core.Rand.PullMean
import SciLean.Tactic.Autodiff

open SciLean MeasureTheory Set

variable
  {R : Type} [RealScalar R] [MeasureSpace R] [BorelSpace R] [PlainDataType R]

set_default_scalar R

open Scalar
def circleParam (θ : R) : R×R := (cos θ, sin θ)

@[fun_prop]
theorem circleParam.arg_θ.HasAdjDiff_rule :
    Differentiable R (circleParam (R:=R)) := by unfold circleParam; fun_prop

@[fun_trans]
theorem circleParam.arg_θ.jacobian_rule :
    jacobian R (circleParam (R:=R)) = 1 := by
  funext x
  unfold circleParam
  autodiff; autodiff

open Scalar Set RealScalar in
@[gtrans]
theorem circle_parametric_inverse_polar (r : R) (hr : r ≠ 0) :
    SurfaceParametrization {x : R×R | x.1 ^ 2 + x.2 ^ 2 = r ^ 2}
      (U := R)
      (param :=
        [(Ico 0 (2*π),
          fun θ => (cos θ, sin θ))]) := sorry_proof


example (w : R) (hw : w ≠ 0) :
    (fderiv R (fun w' =>
      ∫ x in Icc (0:R) 1 ×ˢ Icc (0:R) 1,
        if x.1^2 + x.2^2 ≤ w'^2 then x.1*x.2*w'^2 else x.1+x.2+w'^2) w 1)
    =
    let interior :=
    ∫ (x : R × R) in Icc 0 1 ×ˢ Icc 0 1,
        let fx := x.1 * x.2;
        if x.1 ^ 2 + x.2 ^ 2 ≤ w ^ 2 then 2 * w * fx else 2 * w;
    let s :=
      ∫ (x : R) in closedBall₂ (2 * π / 2) (2 * π / 2),
        let x_1 := cos x;
        let x_2 := sin x;
        let vals := x_1 * x_2 * w ^ 2;
        let vals_1 := x_1 + x_2 + w ^ 2;
        if x ∈ Ico 0 (2 * π) ∩ (fun θ => (cos θ, sin θ)) ⁻¹' Icc 0 1 ×ˢ Icc 0 1 then
          2 * w / sqrt ((2 * x_1) ^ 2 + (2 * x_2) ^ 2) * (vals - vals_1)
        else 0;
    interior + s := by

  conv =>
    lhs

    rw[fderiv_under_integral_over_set
           (hf:= by gtrans
                      (disch:=first | fun_prop_no_ifs | assume_almost_disjoint)
                      (norm:=lsimp only [ftrans_simp]))
                      (hA := by assume_almost_disjoint)]

    lautodiff (disch:=first | fun_prop | gtrans (disch:=fun_prop))

    conv in (∫ _ in _, _ ∂μH[_]) =>

      lautodiff (disch:=gtrans (disch:=first | fun_prop | assumption))
        [surface_integral_parametrization_inter R]
      lautodiff (disch:=first | gtrans (disch:=fun_prop) | fun_prop)
        [integral_over_bounding_ball (R:=R)]

    conv in (occs:=*) (∫ _ in _, _ ∂_) =>
      . lsimp only [Rand.integral_eq_uniform_E R,
                    Rand.E_eq_mean_estimateE R 10]
      . lsimp only [Rand.integral_eq_uniform_E R,
                    Rand.E_eq_mean_estimateE R 10]

    pull_mean

  sorry_proof
