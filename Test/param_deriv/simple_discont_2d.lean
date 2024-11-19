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

def test_fderiv (numSamples : ℕ) (w : R) :=
  derive_random_approx
    (fderiv R (fun w' =>
      ∫ xy in Icc (0:R) 1 ×ˢ (Icc (0 : R) 1),
        if xy.1 + xy.2 ≤ w' then (1:R) else (0:R)) w 1)
  by
    rw[fderiv_under_integral_over_set
           (hf:= by gtrans
                      (disch:=first | fun_prop_no_ifs | assume_almost_disjoint)
                      (norm:=lsimp only [ftrans_simp]))
                      (hA := by assume_almost_disjoint)]

    lautodiff (disch:=first | fun_prop | gtrans (disch:=fun_prop))

    conv in (∫ _ in _, _ ∂μH[_]) =>
      lautodiff (disch:=gtrans (disch:=fun_prop))
        [surface_integral_parametrization_inter R]
      lautodiff (disch:=gtrans (disch:=fun_prop))
        [integral_over_bounding_ball (R:=R)]

    conv in (occs:=*) (∫ _ in _, _ ∂_) =>
      . lsimp only [Rand.integral_eq_uniform_E R]
        lsimp only [Rand.E_eq_mean_estimateE R numSamples]
        lsimp only [ftrans_simp]

    pull_mean


def test_fwdFDeriv (numSamples : ℕ) (w : R) :=
  derive_random_approx
    (fwdFDeriv R (fun w' =>
      ∫ xy in Icc (0:R) 1 ×ˢ (Icc (0 : R) 1),
        if xy.1 ≤ w' then (1:R) else (0:R)) w 1)
  by
    rw[fwdFDeriv_under_integral_over_set
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
      . lsimp only [Rand.integral_eq_uniform_E R,
                    Rand.E_eq_mean_estimateE R numSamples]
        lsimp only [ftrans_simp]

    pull_mean


def test_fgrad (numSamples : ℕ) (w : R) :=
  derive_random_approx
    (fgradient (fun w' =>
      ∫ xy in Icc (0:R) 1 ×ˢ (Icc (0 : R) 1),
        if xy.1 ≤ w' then (1:R) else (0:R)) w)
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

    conv in (occs:=*) (∫ _ in _, _ ∂_) =>
      . lsimp only [Rand.integral_eq_uniform_E R,
                    Rand.E_eq_mean_estimateE R numSamples]
        lsimp only [ftrans_simp]

    pull_mean


#eval 0

#eval! Rand.print_mean_variance (test_fderiv 1 0.5) 1000 ""
#eval! (test_fwdFDeriv 100 0.5).get
#eval! (test_fgrad 100 0.5).get
