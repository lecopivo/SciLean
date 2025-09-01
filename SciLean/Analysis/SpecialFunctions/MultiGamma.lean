import SciLean.Analysis.Scalar

namespace SciLean

open Scalar

variable {R} [RealScalar R]

set_default_scalar R

/-- Multivariate Gamma function -/
def multiGamma (x : R) (p : ℕ) : R :=
  π^((0.25:R) * p * (p-1)) * ∏ (i : Fin p), tgamma (x - (i:R)/2)


@[simp, simp_core]
def toReal_multiGamma (x : R) (p : ℕ) :
  toReal R (multiGamma x p)
  =
  Real.pi ^ (p*(p-1)/(4:ℝ))
  *
  Finset.univ.prod (fun i : Fin p => (toReal R x - (i.1:ℝ)/2).Gamma) := sorry_proof


@[simp, simp_core]
def multiGamma_one (x : R) :
    (multiGamma x 1)
    =
    tgamma x := by simp[multiGamma]; sorry_proof


/-- Logarithm of multivariate gamma function -/
def logMultiGamma (x : R) (p : ℕ) : R :=
  0.25 * p * (p - 1) * log π +
  ∑ᴵ (j : Fin p), lgamma (x - 0.5 * j)


@[simp, simp_core]
def log_abs_multiGamma_eq_logMultiGamma (x : R) (p : ℕ) :
    log (Scalar.abs (multiGamma x p)) = logMultiGamma x p := sorry_proof


@[simp, simp_core]
def logMultiGamma_one (x : R) :
    logMultiGamma x 1 = lgamma x := by
  simp[logMultiGamma]; sorry_proof
