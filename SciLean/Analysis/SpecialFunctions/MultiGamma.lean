module

public import SciLean.Analysis.Scalar

@[expose] public section


namespace SciLean

open Scalar

variable {R} [RealScalar R]

set_default_scalar R

/-- Multivariate Gamma function -/
def multiGamma (x : R) (p : ℕ) : R :=
  π^((0.25:R) * p * (p-1)) * ∏ (i : Fin p), tgamma (x - (i:R)/2)


@[simp, simp_core]
theorem toReal_multiGamma (x : R) (p : ℕ) :
  toReal R (multiGamma x p)
  =
  Real.pi ^ (p*(p-1)/(4:ℝ))
  *
  Finset.univ.prod (fun i : Fin p => (toReal R x - (i.1:ℝ)/2).Gamma) := by
  let e : ℝ ≃+* R := RingEquiv.ofBijective (algebraMap ℝ R)
    ⟨(algebraMap ℝ R).injective, fun a => ⟨toReal R a, Scalar.algebraMap_toReal a⟩⟩
  have he : ∀ a : R, toReal R a = e.symm a := fun a => by
    rw [RingEquiv.eq_symm_apply]; exact Scalar.algebraMap_toReal a
  have hpi : toReal R (π : R) = Real.pi := by
    rw [RealScalar.pi, RealScalar.acos_def, he, map_neg, map_one, Real.arccos_neg_one]
  have hg : ∀ z : R, toReal R (tgamma z) = Real.Gamma (toReal R z) := fun z => by
    have h := Scalar.tgamma_def z
    rw [Scalar.toComplex_eq_toReal, Scalar.toComplex_eq_toReal, Complex.Gamma_ofReal] at h
    exact_mod_cast h
  unfold multiGamma
  rw [Scalar.toReal_mul, Scalar.toReal_rpow, hpi]
  congr 1
  · congr 1
    rw [show (0.25:R) = 1/4 by norm_num, he]
    simp only [map_mul, map_sub, map_div₀, map_one, map_natCast, map_ofNat]
    ring
  · rw [he, map_prod]
    congr 1; ext i
    rw [← he, hg, he, map_sub, map_div₀, map_natCast, map_ofNat, ← he]


@[simp, simp_core]
theorem multiGamma_one (x : R) :
    (multiGamma x 1)
    =
    tgamma x := by
  have h : π ^ (0:R) = 1 := by
    apply Scalar.toReal_injective
    rw [Scalar.toReal_rpow, Scalar.toReal_zero, Real.rpow_zero, Scalar.toReal_one]
  simp[multiGamma, h]


/-- Logarithm of multivariate gamma function -/
def logMultiGamma (x : R) (p : ℕ) : R :=
  0.25 * p * (p - 1) * log π +
  ∑ᴵ (j : Fin p), lgamma (x - 0.5 * j)


@[simp, simp_core]
theorem log_abs_multiGamma_eq_logMultiGamma (x : R) (p : ℕ) :
    log (Scalar.abs (multiGamma x p)) = logMultiGamma x p := sorry_proof


@[simp, simp_core]
theorem logMultiGamma_one (x : R) :
    logMultiGamma x 1 = lgamma x := by
  simp[logMultiGamma, IndexType.sum_eq_finset_sum]
