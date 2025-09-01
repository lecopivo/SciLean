import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

import SciLean.Analysis.AdjointSpace.Basic
import SciLean.Analysis.Scalar.Notation
-- import SciLean.Util.SorryProof

namespace SciLean


open Classical


/-- `K` are real or complex numbers over real numbers `R`

This class allows us to write code independent of particular implementation of real or complex numbers.

The main motivation for this class is to treat floating point numbers as real numbers but to minimize the impact of such unsoundness. We can write code with valid proofs and only at the last step before compilation provide inconsistent instance `Scalar Float Float`.

An alternative approach to get executable code would be to add a custom compiler step which would replace every occurance of real or complex numbers with their floating point equivalent. Implementing such compiler step turned out to be quite a non-trivial task thus we are taking this type class approach. -/
class Scalar (R : outParam (Type _)) (K : (Type _)) extends RCLike K where
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
  real_def : ∀ x, toReal (real x) = RCLike.re (toComplex x)

  imag (x : K) : R
  imag_def : ∀ x, toReal (imag x) = RCLike.im (toComplex x)

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
      RCLike.re (toComplex (sqrt x)) = Real.sqrt (RCLike.re (toComplex x))
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
  abs_def : ∀ x, toReal (abs x) = ‖(toComplex x)‖

  tgamma (x : K) : K
  tgamma_def (x : K) :
    toComplex (tgamma x) = Complex.Gamma (toComplex x)

  lgamma (x : K) : R
  lgamma_def (x : K) :
    toReal (lgamma x) = Real.log ‖Complex.Gamma (toComplex x)‖

  /-- Is `x` finite number? For `ℝ` and `ℂ` this should be always true.
  TODO: make dedicated class `FloatLike` that has this and `Scalar` derives from. -/
  isFinite (x : K) : Bool
  /-- Is `x` not a number? For `ℝ` and `ℂ` this should be always false.
  TODO: make dedicated class `FloatLike` that has this and `Scalar` derives from. -/
  isNaN (x : K) : Bool
  /-- Is `x` infinite? For `ℝ` and `ℂ` this should be always false.
  TODO: make dedicated class `FloatLike` that has this and `Scalar` derives from. -/
  isInf (x : K) : Bool
  -- exp2 : K → K
  -- log2 : K → K
  -- log10 : K → K
  -- pow : K → K → K
  -- cbrt : K → K


/-- `R` behaves as real numbers

This class allows us to write code independent of particular implementation of real numbers.

See `Scalar` for motivation for this class.
-/
class RealScalar (R : Type*) extends Scalar R R where
  [order : LinearOrder R]

  is_real : ∀ x : R, im x = 0

  asin (x : R) : R
  asin_def : ∀ x, toReal (asin x) = Real.arcsin (toReal x)

  acos (x : R) : R
  acos_def : ∀ x, toReal (acos x) = Real.arccos (toReal x)

  atan (x : R) : R
  atan_def : ∀ x, toReal (atan x) = Real.arctan (toReal x)

instance {R : Type*} [RealScalar R] : LinearOrder R := RealScalar.order

def RealScalar.pi [RealScalar R] : R := RealScalar.acos (-1)

scoped notation "π" => @RealScalar.pi defaultScalar% inferInstance

@[app_unexpander RealScalar.pi] def unexpandPi : Lean.PrettyPrinter.Unexpander
  | `($_) => `(π)


instance {R} [RealScalar R] : MetricSpace (WithLp p R) := (by infer_instance : MetricSpace R)

noncomputable
instance {R} [RealScalar R] : AdjointSpace ℝ R where
  inner_top_equiv_norm := sorry_proof
  conj_symm := sorry_proof
  add_left := sorry_proof
  smul_left := sorry_proof

-- can we provide this without messing with instance for `MeasureSpace ℝ`?
-- open MeasureTheory in
-- instance {R} [RealScalar R] : MeasureSpace R := sorry

instance {R K} [Scalar R K] : HPow K K K := ⟨fun x y => Scalar.pow x y⟩
instance {R} [RealScalar R] : ZeroLEOneClass R := sorry_proof
instance {R} [RealScalar R] : WellFoundedLT R := sorry_proof

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


open ComplexConjugate

@[simp, simp_core]
theorem conj_for_real_scalar {R} [RealScalar R] (r : R)
  : conj r = r := sorry_proof



----------------------------------------------------------------------------------------------------
-- Instances ---------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


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

  abs x := ‖x‖
  abs_def := by intros; simp

  tgamma x := x.Gamma
  tgamma_def := by intros; simp

  lgamma x := ‖x.Gamma‖.log
  lgamma_def := by intros; simp

  isFinite x := true
  isNaN x := false
  isInf x := false

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
  abs_def := by intros; sorry_proof

  tgamma x := x.Gamma
  tgamma_def := by intros;sorry_proof

  lgamma x := |x.Gamma|.log
  lgamma_def := by intros; simp; sorry_proof

  is_real := by intros; simp

  isFinite x := true
  isNaN x := false
  isInf x := false

  order := by infer_instance



----------------------------------------------------------------------------------------------------
-- Simp theorems -----------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
section SimpTheoremsComplex

variable {R K} [RealScalar R] [Scalar R K]

@[simp, simp_core]
theorem scalar_make_one : Scalar.make (1 : R) 0 = (1 : K) := by sorry_proof

end SimpTheoremsComplex

section SimpTheorems

theorem normalize_real_smul (R) [RealScalar R] [Ring X] [Module R X] [Module ℝ X] [IsScalarTower ℝ R X]
    (r : ℝ) (x : X) :
    r • x = Scalar.ofReal R r • x := sorry_proof

variable {R} [RealScalar R]

@[simp, simp_core]
theorem scalar_abs_one : Scalar.abs (1 : R) = 1 := by sorry_proof

@[simp, simp_core]
theorem scalar_abs_zero : Scalar.abs (0 : R) = 0 := by sorry_proof

@[simp, simp_core]
theorem scalar_abs_neg (r : R) : Scalar.abs (- r) = Scalar.abs r := by sorry_proof

@[simp, simp_core]
theorem scalar_div_one (x : R) : x / 1 = x := by sorry_proof

@[simp, simp_core]
theorem scalar_sqrt_one  : Scalar.sqrt (1 : R) = 1 := by sorry_proof

@[simp, simp_core]
theorem scalar_sqrt_zero  : Scalar.sqrt (0 : R) = 0 := by sorry_proof

@[simp, simp_core]
theorem scalar_max_one_zero  : max (1 : R) (0 : R) = 1 := by sorry_proof

@[simp, simp_core]
theorem scalar_max_zero_one  : max (0 : R) (1 : R) = 1 := by sorry_proof

@[simp, simp_core]
theorem scalar_min_one_zero  : min (1 : R) (0 : R) = 0 := by sorry_proof

@[simp, simp_core]
theorem scalar_min_zero_one  : min (0 : R) (1 : R) = 0 := by sorry_proof


----------------------------------------------------------------------------------------------------
-- to/ofReal ------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[simp, simp_core]
theorem Scalar.oftoReal (x : R) :
    Scalar.ofReal R (Scalar.toReal R x)
    =
    x := sorry_proof

@[simp, simp_core]
theorem Scalar.toReal_ofReal {R K} [Scalar R K] (x : ℝ)  :
    Scalar.toReal (K:=K) (Scalar.ofReal (K:=K) x) = x :=
  sorry_proof

@[simp, simp_core]
theorem Scalar.ofReal_zero :
  Scalar.ofReal R (0 : ℝ) = (0:R) := sorry_proof

@[simp, simp_core]
theorem Scalar.ofReal_one :
  Scalar.ofReal R (1 : ℝ) = (1:R) := sorry_proof

@[simp, simp_core]
theorem Scalar.toReal_zero :
  Scalar.toReal R (0:R) = 0 := sorry_proof

@[simp, simp_core]
theorem Scalar.toReal_one :
  Scalar.toReal R (1:R) = 1 := sorry_proof

@[simp_core ↓]
theorem Scalar.ofReal_mul (x y : ℝ) :
    Scalar.ofReal (K:=R) (x * y)
    =
    Scalar.ofReal (K:=R) x * Scalar.ofReal (K:=R) y := sorry_proof

@[simp, simp_core]
theorem Scalar.ofReal_ite (c : Prop) [Decidable c] (t e : ℝ) :
    Scalar.ofReal R (if c then t else e)
    =
    if c then Scalar.ofReal R t else Scalar.ofReal R e := by
  if h : c then simp[h] else simp[h]

@[simp, simp_core]
theorem Scalar.ofReal_dite (c : Prop) [Decidable c]
    (t : c → ℝ) (e : ¬c → ℝ) :
    Scalar.ofReal R (if h : c then t h else e h)
    =
    if h : c then Scalar.ofReal R (t h) else Scalar.ofReal R (e h) := by
  if h : c then simp[h] else simp[h]

@[simp, simp_core]
theorem Scalar.toReal_ite (c : Prop) [Decidable c] (t e : R) :
    Scalar.toReal R (if c then t else e)
    =
    if c then Scalar.toReal R t else Scalar.toReal R e := by
  if h : c then simp[h] else simp[h]

@[simp, simp_core]
theorem Scalar.toReal_dite (c : Prop) [Decidable c]
    (t : c → R) (e : ¬c → R) :
    Scalar.toReal R (if h : c then t h else e h)
    =
    if h : c then Scalar.toReal R (t h) else Scalar.toReal R (e h) := by
  if h : c then simp[h] else simp[h]


----------------------------------------------------------------------------------------------------
-- to/ofENNReal ------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[simp, simp_core]
theorem Scalar.oftoENNReal (x : R) :
    Scalar.ofENNReal (Scalar.toENNReal x)
    =
    max x 0 := sorry_proof

@[simp, simp_core]
theorem Scalar.ofReal_toReal (x : ENNReal) :
    Scalar.ofReal R x.toReal
    =
    Scalar.ofENNReal x := sorry_proof

@[simp, simp_core]
theorem Scalar.ofENNReal_one :
  Scalar.ofENNReal (1 : ENNReal) = (1:R) := sorry_proof

@[simp, simp_core]
theorem Scalar.ofENNReal_zero :
  Scalar.ofENNReal (0 : ENNReal) = (0:R) := sorry_proof

@[simp, simp_core]
theorem Scalar.toENNReal_one :
  Scalar.toENNReal (1:R) = 1 := sorry_proof

@[simp, simp_core]
theorem Scalar.toENNReal_zero :
  Scalar.toENNReal (0:R) = 0 := sorry_proof

@[simp_core ↓]
theorem ofENNReal_mul (x y : ENNReal) :
    Scalar.ofENNReal (R:=R) (x * y)
    =
    Scalar.ofENNReal (R:=R) x * Scalar.ofENNReal (R:=R) y := sorry_proof

@[simp ↓, simp_core ↓]
theorem Scalar.ofENNReal_ite (c : Prop) [Decidable c] (t e : ENNReal) :
    Scalar.ofENNReal (R:=R) (if c then t else e)
    =
    if c then Scalar.ofENNReal (R:=R) t else Scalar.ofENNReal (R:=R) e := by
  if h : c then simp[h] else simp[h]

@[simp ↓, simp_core ↓]
theorem Scalar.ofENNReal_dite (c : Prop) [Decidable c]
    (t : c → ENNReal) (e : ¬c → ENNReal) :
    Scalar.ofENNReal (R:=R) (if h : c then t h else e h)
    =
    if h : c then Scalar.ofENNReal (R:=R) (t h) else Scalar.ofENNReal (R:=R) (e h) := by
  if h : c then simp[h] else simp[h]

@[simp ↓, simp_core ↓]
theorem Scalar.toENNReal_ite (c : Prop) [Decidable c] (t e : R) :
    Scalar.toENNReal (if c then t else e)
    =
    if c then Scalar.toENNReal t else Scalar.toENNReal e := by
  if h : c then simp[h] else simp[h]

@[simp ↓, simp_core ↓]
theorem Scalar.toENNReal_dite (c : Prop) [Decidable c]
    (t : c → R) (e : ¬c → R) :
    Scalar.toENNReal (if h : c then t h else e h)
    =
    if h : c then Scalar.toENNReal (t h) else Scalar.toENNReal (e h) := by
  if h : c then simp[h] else simp[h]

end SimpTheorems


/-- Class saying that scalar multiplication between `R` and `K` is compatible with multiplication
for  `[RealScalar R]` and `[Scalar R K]`

This class is necessary if you want to consider `K` as vector spaces over `R`. -/
class ScalarSMul (R K : Type*) [RealScalar R] [Scalar R K] extends SMul R K where
  smul_eq_mul_make (r : R) (k : K) : r • k = Scalar.make r 0 * k

class ScalarInner (R K : Type*) [RealScalar R] [Scalar R K] extends Inner R K where
  inner_eq_inner_re_im (x y : K) :
    Inner.inner (𝕜:=R) x y
    =
    Scalar.real x * Scalar.real y + Scalar.imag x * Scalar.imag y

section ScalarSMul

instance {R} [RealScalar R] : ScalarSMul R R where
  smul_eq_mul_make := sorry_proof

instance {R} [RealScalar R] : ScalarInner R R where
  inner_eq_inner_re_im := sorry_proof

instance (priority:=low) instModuleScalarSMul {R K} {_ : RealScalar R} {_ : Scalar R K} [ScalarSMul R K] : Module R K where
  one_smul := sorry_proof
  mul_smul := sorry_proof
  smul_zero := sorry_proof
  smul_add := sorry_proof
  add_smul := sorry_proof
  zero_smul := sorry_proof

instance (priority:=low) instNormedSpaceRK {R K} {_ : RealScalar R} {_ : Scalar R K} [ScalarSMul R K] :
    NormedSpace R K where
  norm_smul_le := sorry_proof

instance (priority:=low) instInnerProductSpaceRK {R K} {_ : RealScalar R} {_ : Scalar R K} [ScalarSMul R K] [ScalarInner R K] :
    InnerProductSpace R K where
  norm_sq_eq_re_inner := sorry_proof
  conj_inner_symm := sorry_proof
  add_left := sorry_proof
  smul_left := sorry_proof

instance (priority:=low) instAdjointSpaceRK {R K} {_ : RealScalar R} {_ : Scalar R K} [ScalarSMul R K] [ScalarInner R K] :
    AdjointSpace R K where
  inner_top_equiv_norm := sorry_proof
  conj_symm := sorry_proof
  add_left := sorry_proof
  smul_left := sorry_proof

instance (priority:=low) {R K X} {_ : RealScalar R} {_ : Scalar R K} [ScalarSMul R K] [AddCommGroup X] [Module K X] [Module R X] :
    IsScalarTower R K X where
  smul_assoc := sorry_proof

-- It is important that we maintain that these instances are defeq
example {R} [RealScalar R] :
  (instModuleScalarSMul : Module R R).toSMul = (NormedSpace.toModule : Module R R).toSMul := rfl

instance (priority:=low) {R K} {_ : RealScalar R} {_ : Scalar R K} [ScalarSMul R K] : Algebra R K where
  -- toFun := fun r => Scalar.make r 0
  -- map_one' := sorry_proof
  -- map_mul' := sorry_proof
  -- map_zero' := sorry_proof
  -- map_add' := sorry_proof
  algebraMap := ⟨⟨⟨fun r => Scalar.make r 0, sorry_proof⟩, sorry_proof⟩, sorry_proof, sorry_proof⟩
  commutes' := sorry_proof
  smul_def' := sorry_proof

instance (priority:=low) {R K} {_ : RealScalar R} {_ : Scalar R K} [ScalarSMul R K] : NormedAlgebra R K where
  norm_smul_le := sorry_proof


end ScalarSMul
