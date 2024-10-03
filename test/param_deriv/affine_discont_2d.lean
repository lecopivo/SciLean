#exit

import SciLean.Core.Transformations.HasParamDerivWithJumps.Common
import SciLean.Core.Transformations.SurfaceParametrization
import SciLean.Core.LinearAlgebra.GramSchmidt.Properties
import SciLean.Core.Rand.Distributions.Uniform
import SciLean.Core.Rand.Tactic
import SciLean.Core.Rand.PullMean
import SciLean.Data.DataArray
import SciLean.Tactic.Autodiff

open SciLean MeasureTheory Set Scalar

variable
  {R : Type} [RealScalar R] [MeasureSpace R] [BorelSpace R] [PlainDataType R]

set_default_scalar R


def test_fderiv (numSamples : ℕ) (a b c d : R) (w : R) :=
  derive_random_approx
    (fderiv R (fun w' =>
      ∫ xy in Icc (0:R) 1 ×ˢ (Icc (0 : R) 1),
        if a * xy.1 + b * xy.2 + c ≤ d * w' then (1:R) else 0) w 1)
  by
    rw[fderiv_under_integral_over_set
           (hf:= by gtrans
                      (disch:=first | fun_prop_no_ifs | assume_almost_disjoint)
                      (norm:=lsimp only [ftrans_simp]))
                      (hA := by assume_almost_disjoint)]

    lautodiff (disch:=first | fun_prop | gtrans (disch:=fun_prop))

    conv in (∫ _ in _, _ ∂μH[_]) =>

      lautodiff (disch:=gtrans (disch:=fun_prop))
        [surface_integral_parametrization_inter R,
         integral_over_bounding_ball (R:=R)]

    conv in (occs:=*) (∫ _ in _, _ ∂_) =>
      . lsimp only [Rand.integral_eq_uniform_E R,
                    Rand.E_eq_mean_estimateE R numSamples]
        lsimp only [ftrans_simp]
    pull_mean


def test_fgradient (numSamples : ℕ) (a b c d : R) (w : R) :=
  derive_random_approx
    (fgradient (fun w' =>
      ∫ xy in Icc (0:R) 1 ×ˢ (Icc (0 : R) 1),
        if a * xy.1 + b * xy.2 + c ≤ d * w' then (1:R) else 0) w)
  by
    unfold fgradient
    rw[revFDeriv_under_integral_over_set
           (hf:= by gtrans
                      (disch:=first | fun_prop_no_ifs | assume_almost_disjoint)
                      (norm:=lsimp only [ftrans_simp]))
                      (hA := by assume_almost_disjoint)]

    lautodiff (disch:=first | fun_prop | gtrans (disch:=fun_prop)) [frontierGrad]

    conv in (∫ _ in _, _ ∂μH[_]) =>

      lautodiff (disch:=gtrans (disch:=fun_prop))
        [surface_integral_parametrization_inter R,
         integral_over_bounding_ball (R:=R)]
      lautodiff (disch:=fun_prop)

    conv in (occs:=*) (∫ _ in _, _ ∂_) =>
      . lsimp only [Rand.integral_eq_uniform_E R,
                    Rand.E_eq_mean_estimateE R numSamples]
        lsimp only [ftrans_simp]
    pull_mean



#eval 0

#eval! (test_fderiv    1000 1.0 1.0 0.3 1.0 0.5).get
#eval! (test_fgradient 1000 1.0 1.0 0.3 1.0 0.5).get
