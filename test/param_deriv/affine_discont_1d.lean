#exit

import SciLean.Core.Transformations.HasParamDerivWithJumps.Common
import SciLean.Core.Rand.Distributions.Uniform
import SciLean.Core.Rand.Tactic
import SciLean.Tactic.Autodiff

open SciLean MeasureTheory Set



variable
  {R : Type} [RealScalar R] [MeasureSpace R] [BorelSpace R]

set_default_scalar R


def test_fderiv (a b c : R) (w : R) :=
    (fderiv R (fun w' =>
      ∫ x in Icc (0:R) 1,
        if a * x + b ≤ c * w' then (1:R) else 0) w 1)

  rewrite_by assuming (ha : a ≠ 0)
    rw[fderiv_under_integral_over_set
           (hf:= by gtrans
                      (disch:=first | fun_prop_no_ifs | assume_almost_disjoint)
                      (norm:=lsimp only [ftrans_simp]))
                      (hA := by assume_almost_disjoint)]

    lautodiff (disch:=first | assumption | fun_prop (disch:=assumption))
