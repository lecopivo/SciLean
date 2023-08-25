import Mathlib.Data.IsROrC.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

import SciLean.Util.SorryProof

namespace SciLean


open Classical

/-- `K` are real or complex numbers over real numbers `R` -/
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

  real : K → R
  real_def : ∀ x, toReal (real x) = IsROrC.re (toComplex x)

  imag : K → R
  imag_def : ∀ x, toReal (imag x) = IsROrC.im (toComplex x)
  
  cos : K → K
  cos_def : ∀ x, toComplex (cos x) = Complex.cos (toComplex x)

  tan : K → K
  tan_def : ∀ x, toComplex (tan x) = Complex.tan (toComplex x)

  exp : K → K
  exp_def : ∀ x, toComplex (exp x) = Complex.exp (toComplex x)

  sqrt : K → K
  sqrt_def : ∀ x, 
    if ∀ y : K, im y = 0 then
      -- for reals
      IsROrC.re (toComplex (sqrt x)) = Real.sqrt (IsROrC.re (toComplex x))
    else
      -- for complex
      toComplex (sqrt x) = (toComplex x).cpow (1/2)

  -- abs : K → K
  -- abs_def : ∀ x,
  --   toComplex (abs x) = (IsROrC.re (toComplex x)).abs

  -- exp2 : K → K
  -- log : K → K
  -- log2 : K → K
  -- log10 : K → K
  -- pow : K → K → K
  -- cbrt : K → K


class RealScalar (R : semiOutParam (Type _)) extends Scalar R R where
  is_real : ∀ x : R, im x = 0


open ComplexConjugate 

@[simp]
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
  
  cos x := x.cos
  cos_def := by intros; simp

  tan x := x.tan
  tan_def := by intros; simp

  exp x := x.exp
  exp_def := by intros; simp

  sqrt x := x.cpow (1/2)
  sqrt_def := sorry_proof


  -- ceil : K → K
  -- floor : K → K
  -- round : K → K

  

  -- ceil : K → K
  -- floor : K → K
  -- round : K → K


-- instance : Scalar Real where
--   cos := Real.cos
  
