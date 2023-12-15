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
  

open ComplexConjugate 

@[simp, ftrans_simp]
theorem conj_for_real_scalar {R} [RealScalar R] (r : R)
  : conj r = r := sorry_proof


noncomputable
instance : Scalar ℝ ℂ where
  toComplex x := x
  toReal x := x

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
