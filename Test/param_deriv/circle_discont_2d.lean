#exit

import SciLean.Core.Transformations.HasParamDerivWithJumps.Common
import SciLean.Core.Transformations.SurfaceParametrization
import SciLean.Core.Rand
import SciLean.Core.Meta.GenerateFunTrans
import SciLean.Core.Meta.GenerateFunProp
import SciLean.Tactic.Autodiff

open SciLean MeasureTheory Set

variable
  {R : Type} [RealScalar R] [MeasureSpace R] [BorelSpace R] [PlainDataType R]

set_default_scalar R

open Scalar
def circleParam (θ : R) : R×R := (cos θ, sin θ)

def_fun_prop with_transitive : Differentiable R (circleParam (R:=R)) by
  unfold circleParam; fun_prop

abbrev_fun_trans : jacobian R (circleParam (R:=R)) by
  unfold circleParam; autodiff; autodiff

open Scalar Set RealScalar in
@[gtrans]
theorem circle_parametric_inverse_polar (r : R) (hr : r ≠ 0) :
    SurfaceParametrization {x : R×R | x.1 ^ 2 + x.2 ^ 2 = r ^ 2}
      (U := R)
      (param :=
        [(Ico 0 (2*π), fun x => r•circleParam x)]) := sorry_proof


def test_fderiv (numSamples : ℕ) (w : R) :=
  derive_random_approx
    (fderiv R (fun w' =>
      ∫ x in Icc (0:R) 1 ×ˢ Icc (0:R) 1,
        if x.1^2 + x.2^2 ≤ w'^2 then x.1*x.2*w'^2 else x.1+x.2+w'^2) w 1)
  assuming (hw : w ≠ 0)
  by
    rw[fderiv_under_integral_over_set
           (hf:= by gtrans
                      (disch:=first | fun_prop_no_ifs | assume_almost_disjoint)
                      (norm:=lsimp only [ftrans_simp]))
                      (hA := by assume_almost_disjoint)]

    lautodiff (disch:=first | fun_prop | gtrans (disch:=fun_prop))

    conv in (∫ _ in _, _ ∂μH[_]) =>

      lsimp (disch:=gtrans (disch:=first | fun_prop | assumption)) only
        [surface_integral_parametrization_inter R]
      lautodiff (disch:=first | gtrans (disch:=fun_prop) | fun_prop)
        [integral_over_bounding_ball (R:=R)]

    conv in (occs:=*) (∫ _ in _, _ ∂_) =>
      . lsimp only [Rand.integral_eq_uniform_E R,
                    Rand.E_eq_mean_estimateE R numSamples]
        lsimp only [ftrans_simp]
      . lsimp only [Rand.integral_eq_uniform_E R,
                    Rand.E_eq_mean_estimateE R numSamples]
        lsimp only [ftrans_simp]

    pull_mean



#eval 0



#eval Rand.print_mean_variance (test_fderiv 1 0.5) 5000 ""
