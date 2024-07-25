import SciLean.Core.Transformations.HasParamDerivWithJumps.Common
import SciLean.Core.Transformations.HasParamDerivWithJumps.Functions
import SciLean.Core.Transformations.SurfaceParametrization
import SciLean.Core.Rand
import SciLean.Core.Functions.Gaussian
import SciLean.Tactic.Autodiff

open SciLean MeasureTheory Set

variable
  {R : Type} [RealScalar R] [MeasureSpace R] [BorelSpace R]

set_default_scalar R


variable (l u : R)

def test_fwdFDeriv (l u : R) (θ dθ : R×R×R) :=
  derive_random_approx
  (fwdFDeriv R (fun ((a,b,μ) : R×R×R) => ∫ x in Icc l u,
    ‖ if x ∈ Icc a b then gaussian μ (5:R) x else 0 -  gaussian 2 (5:R) x ‖₂²) θ dθ)
  assuming (hθ : θ.1 < θ.2.1)
  by
    rw[fwdFDeriv_under_integral_over_set
           (hf:= by gtrans
                      (disch:=first | fun_prop_no_ifs | assume_almost_disjoint)
                      (norm:=lsimp only [ftrans_simp]))
                      (hA := by assume_almost_disjoint)]

    lautodiff (disch:=first | fun_prop | gtrans (disch:=fun_prop) | assumption)

    conv in (occs:=*) (∫ _ in _, _ ∂_) =>
      . lsimp only [Rand.integral_eq_uniform_E R,
                    Rand.E_eq_mean_estimateE R 10]
        lsimp only [ftrans_simp]

    pull_mean


-- def test_fgradient (l u : R) (θ : R×R×R) :=
--   derive_random_approx
--   (fgradient (fun ((a,b,μ) : R×R×R) => ∫ x in Icc l u,
--     ‖ if x ∈ Icc a b then gaussian μ (5:R) x else 0 -  gaussian 2 (5:R) x ‖₂²) θ)
--   assuming (hθ : θ.1 < θ.2.1)
--   by
--     unfold fgradient
--     rw[revFDeriv_under_integral_over_set
--            (hf:= by gtrans
--                       (disch:=first | fun_prop_no_ifs | assume_almost_disjoint)
--                       (norm:=lsimp only [ftrans_simp]))
--                       (hA := by assume_almost_disjoint)]

--     lautodiff (disch:=first | fun_prop | gtrans (disch:=fun_prop) | assumption)

--     conv in (occs:=*) (∫ _ in _, _ ∂_) =>
--       . lsimp only [Rand.integral_eq_uniform_E R,
--                     Rand.E_eq_mean_estimateE R 10]
--         lsimp only [ftrans_simp]

--     pull_mean


#eval 0


#eval (test_fwdFDeriv (-1.0) 1.0 (0.0,1.0,0.5) (1.0,0.0,0.0)).get
