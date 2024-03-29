import Mathlib.Data.IsROrC.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

import SciLean.Util.SorryProof
import SciLean.Tactic.FTrans.Init

namespace SciLean


open Classical

/-- `K` are real or complex numbers over real numbers `R`

This class allows us to write code independent of particular implementation of real or complex numbers.

The main motivation for this class is to treat floating point numbers as real numbers but to minimize the impact of such unsoundness. We can write code with valid proofs and only at the last step before compilation provide inconsistent instance `Scalar Float Float`.

An alternative approach to get executable code would be to add a custom compiler step which would replace every occurance of real or complex numbers with their floating point equivalent. Implementing such compiler step turned out to be quite a non-trivial task thus we are taking this type class approach. -/
class Scalar (R : outParam (Type _)) (K : semiOutParam (Type _)) extends IsROrC K where
  -- used for specification
  toComplex : K → ℂ
  toReal    : R → ℝ
  ofReal    : ℝ → R
  ofComplex : ℂ → K -- If `K` model reals then this function should ignore the imaginary part

  make : R → R → K
  make_def : ∀ x y : R,
    if ∀ y : K, im y = 0 then
      toComplex (make x y) = ⟨toReal x, 0⟩
    else
      toComplex (make x y) = ⟨toReal x, toReal y⟩

  real (x : K) : R
  real_def : ∀ x, toReal (real x) = IsROrC.re (toComplex x)

  imag (x : K) : R
  imag_def : ∀ x, toReal (imag x) = IsROrC.im (toComplex x)

  sin (x : K) : K
  sin_def : ∀ x, toComplex (sin x) = Complex.sin (toComplex x)

  cos (x : K) : K
  cos_def : ∀ x, toComplex (cos x) = Complex.cos (toComplex x)

  tan (x : K) : K
  tan_def : ∀ x, toComplex (tan x) = Complex.tan (toComplex x)

  tanh (x : K) : K
  tanh_def : ∀ x, toComplex (tanh x) = Complex.tanh (toComplex x)

  exp (x : K) : K
  exp_def : ∀ x, toComplex (exp x) = Complex.exp (toComplex x)

  log (x : K) : K
  log_def : ∀ x, toComplex (log x) = Complex.log (toComplex x)

  sqrt (x : K) : K
  sqrt_def : ∀ x,
    if ∀ y : K, im y = 0 then
      -- for reals
      IsROrC.re (toComplex (sqrt x)) = Real.sqrt (IsROrC.re (toComplex x))
    else
      -- for complex
      toComplex (sqrt x) = (toComplex x).cpow (1/2)

  pow (x y : K) : K
  pow_def : ∀ x y,
    if ∀ z : K, im z = 0 then
      -- for reals
      toReal (real (pow x y)) = ((toComplex x) ^ (toComplex y)).re
    else
      -- for complex
      toComplex (pow x y) = toComplex x ^ toComplex y

  abs (x : K) : R
  abs_def : ∀ x, toReal (abs x) = Complex.abs (toComplex x)

  -- exp2 : K → K
  -- log2 : K → K
  -- log10 : K → K
  -- pow : K → K → K
  -- cbrt : K → K


/-- `R` behaves as real numbers

This class allows us to write code independent of particular implementation of real numbers.

See `Scalar` for motivation for this class.
-/
class RealScalar (R : semiOutParam (Type _)) extends Scalar R R, LinearOrder R where
  is_real : ∀ x : R, im x = 0

  asin (x : R) : R
  asin_def : ∀ x, toReal (asin x) = Real.arcsin (toReal x)

  acos (x : R) : R
  acos_def : ∀ x, toReal (acos x) = Real.arccos (toReal x)

  atan (x : R) : R
  atan_def : ∀ x, toReal (atan x) = Real.arctan (toReal x)

def RealScalar.pi [RealScalar R] : R := RealScalar.acos (-1)

instance {R K} [Scalar R K] : HPow K K K := ⟨fun x y => Scalar.pow x y⟩

  -- floor
  -- ceil


@[coe]
noncomputable
def Scalar.ofENNReal {R} [RealScalar R] (x : ENNReal) : R :=
  Scalar.ofReal R x.toReal

@[coe]
noncomputable
def Scalar.toENNReal {R} [RealScalar R] (x : R) : ENNReal :=
  .ofReal (Scalar.toReal R x)

@[simp, ftrans_simp]
theorem Scalar.oftoENNReal {R} [RealScalar R] (x : R) :
    Scalar.ofENNReal (Scalar.toENNReal x)
    =
    max x 0 := sorry_proof

@[simp, ftrans_simp]
theorem Scalar.oftoReal {R} [RealScalar R] (x : R) :
    Scalar.ofReal R (Scalar.toReal R x)
    =
    x := sorry_proof


open ComplexConjugate

@[simp, ftrans_simp]
theorem conj_for_real_scalar {R} [RealScalar R] (r : R)
  : conj r = r := sorry_proof


noncomputable
instance : Scalar ℝ ℂ where
  toComplex x := x
  toReal x := x
  ofReal x := x
  ofComplex x := x

  make x y := ⟨x,y⟩
  make_def := by intros; simp; sorry_proof

  real x := x.re
  real_def := by intros; simp

  imag x := x.im
  imag_def := by intros; simp

  sin x := x.sin
  sin_def := by intros; simp

  cos x := x.cos
  cos_def := by intros; simp

  tan x := x.tan
  tan_def := by intros; simp

  exp x := x.exp
  exp_def := by intros; simp

  log x := x.log
  log_def := by intros; simp

  tanh x := x.tanh
  tanh_def := by intros; simp

  sqrt x := x.cpow (1/2)
  sqrt_def := by simp; sorry_proof

  pow x y := x.cpow y
  pow_def := by intros; simp

  abs x := Complex.abs x
  abs_def := by intros; simp



noncomputable instance : RealScalar ℝ where
  toComplex x := ⟨x,0⟩
  toReal x := x
  ofReal x := x
  ofComplex x := x.re

  make x _ := x
  make_def := by intros; simp

  real x := x
  real_def := by intros; simp

  imag _ := 0
  imag_def := by intros; simp

  sin x := x.sin
  sin_def := by intros; simp[Real.sin]; sorry_proof

  cos x := x.cos
  cos_def := by intros; simp[Real.cos]; sorry_proof

  tan x := x.tan
  tan_def := by intros; simp[Real.tan]; sorry_proof

  asin x := x.arcsin
  asin_def := by intros; simp

  acos x := x.arccos
  acos_def := by intros; simp

  atan x := x.arctan
  atan_def := by intros; simp

  exp x := x.exp
  exp_def := by intros; simp[Real.exp]; sorry_proof

  log x := x.log
  log_def := by intros; simp[Real.log]; sorry_proof

  tanh x := x.tanh
  tanh_def := by intros; simp[Real.tanh]; sorry_proof

  sqrt x := x.sqrt
  sqrt_def := by intros; simp

  pow x y := x.rpow y
  pow_def := by intros; simp; rfl

  abs x := abs x
  abs_def := by intros; simp[Complex.abs]; sorry_proof

  is_real := by intros; simp


  le_total := by sorry_proof

  decidableLE x y :=
    have := Classical.propDecidable
    if h : x ≤ y then
      .isTrue h
    else
      .isFalse h

  decidableEq x y :=
    have := Classical.propDecidable
    if h : x = y then
      .isTrue h
    else
      .isFalse h

  decidableLT x y :=
    have := Classical.propDecidable
    if h : x < y then
      .isTrue h
    else
      .isFalse h

  min := fun a b => if a ≤ b then a else b
  max := fun a b => if a ≤ b then b else a
  min_def := by sorry_proof
  max_def := by sorry_proof
  compare a b := compareOfLessAndEq a b
  compare_eq_compareOfLessAndEq := by
    compareOfLessAndEq_rfl



----------------------------------------------------------------------------------------------------
-- Simp theorems -----------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section SimpTheorems

variable {R} [RealScalar R]

@[simp, ftrans_simp]
theorem scalar_abs_one : Scalar.abs (1 : R) = 1 := by sorry_proof

@[simp, ftrans_simp]
theorem scalar_abs_zero : Scalar.abs (0 : R) = 0 := by sorry_proof

@[simp, ftrans_simp]
theorem scalar_abs_neg (r : R) : Scalar.abs (- r) = Scalar.abs r := by sorry_proof

@[simp, ftrans_simp]
theorem scalar_div_one (x : R) : x / 1 = x := by sorry_proof

@[simp, ftrans_simp]
theorem scalar_sqrt_one  : Scalar.sqrt (1 : R) = 1 := by sorry_proof

@[simp, ftrans_simp]
theorem scalar_sqrt_zero  : Scalar.sqrt (0 : R) = 0 := by sorry_proof

@[simp, ftrans_simp]
theorem scalar_max_one_zero  : max (1 : R) (0 : R) = 1 := by sorry_proof

@[simp, ftrans_simp]
theorem scalar_max_zero_one  : max (0 : R) (1 : R) = 1 := by sorry_proof

@[simp, ftrans_simp]
theorem scalar_min_one_zero  : min (1 : R) (0 : R) = 0 := by sorry_proof

@[simp, ftrans_simp]
theorem scalar_min_zero_one  : min (0 : R) (1 : R) = 0 := by sorry_proof

end SimpTheorems
