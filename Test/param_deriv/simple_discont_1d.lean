#exit

import SciLean.Core.Transformations.HasParamDerivWithJumps.Common
import SciLean.Core.Rand
import SciLean.Tactic.Autodiff

open SciLean MeasureTheory Set

variable
  {R : Type} [RealScalar R] [MeasureSpace R] [BorelSpace R]

set_default_scalar R


def test_fderiv (w : R) :=
    (fderiv R (fun w' =>
      ∫ x in Icc (0:R) 1,
        if x ≤ w' then (1:R) else 0) w 1)
  rewrite_by
    rw[fderiv_under_integral_over_set
           (hf:= by gtrans
                      (disch:=first | fun_prop_no_ifs | assume_almost_disjoint)
                      (norm:=lsimp only [ftrans_simp]))
                      (hA := by assume_almost_disjoint)]

    lautodiff (disch:=fun_prop)



def test_fwdFDeriv (numSamples : ℕ) (w : R) :=
  derive_random_approx
    (fwdFDeriv R (fun w' =>
      ∫ x in Icc (0:R) 1,
        if x ≤ w' then (1:R) else 0) w 1)
  by
    rw[fwdFDeriv_under_integral_over_set
           (hf:= by gtrans
                      (disch:=first | fun_prop_no_ifs | assume_almost_disjoint)
                      (norm:=lsimp only [ftrans_simp]))
                      (hA := by assume_almost_disjoint)]

    lautodiff (disch:=fun_prop)

    conv in (occs:=*) (∫ _ in _, _ ∂_) =>
      . lsimp only [Rand.integral_eq_uniform_E R,
                    Rand.E_eq_mean_estimateE R numSamples]
        lsimp only [ftrans_simp]

    pull_mean

def test_fgradient (w : R) :=
    (fgradient (fun w' =>
      ∫ x in Icc (0:R) 1,
        if x ≤ w' then (1:R) else 0) w)
  rewrite_by
    unfold fgradient
    rw[revFDeriv_under_integral_over_set
           (hf:= by gtrans
                      (disch:=first | fun_prop_no_ifs | assume_almost_disjoint)
                      (norm:=lsimp only [ftrans_simp]))
                      (hA := by assume_almost_disjoint)]

    lautodiff (disch:=fun_prop) [frontierGrad]


#eval 0


#eval test_fderiv 0.5
#eval (test_fwdFDeriv 100 0.1).get
#eval test_fgradient 0.1
