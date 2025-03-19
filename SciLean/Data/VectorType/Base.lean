import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Data.Matrix.Basic

import SciLean.Analysis.AdjointSpace.Basic
import SciLean.Analysis.Scalar
import SciLean.Data.IndexType
import SciLean.Data.IdxType.Basic
import SciLean.Data.IdxType.Fold
import SciLean.Data.VectorType.Init
import SciLean.Data.ArrayOperations.Algebra

namespace SciLean

open InnerProductSpace

/-- `VectorType.Base X n K` says that `X` behaves like a vector indexed by `n` and with values in `K`.

Providing an instance of `VectorType X n K` will automatically provide the following instances
  - `Add X`, `Sub X`, `Neg X`, `SMul K X`, `Zero X`, `Inner K X`, ...

To provide algebraic instances you also need to assume `VectorType.Lawful X n K`. Then you obtain
  - `NormedAddCommGroup X` with l₂ norm
  - `InnerProductSpace K X`
  - `AdjointSpace K X`

To provide a finite dimensional instance you also need to assume `VectorType.Dense X n K`. Then you obtain
  - `FiniteDimensional K X` with the dimension equal to the cardinality of `n`.

This class is designed to provide Basic Linear Algebra Subprograms(BLAS) which allows us to define
vector space structure on `X` that is computationally efficient.
 -/
class VectorType.Base (X : Type*) (n : outParam (Type*)) {nn : outParam ℕ} [outParam (IdxType n nn)]
    {R : outParam (Type*)}  (K : outParam (Type*))
    [outParam (RealScalar R)] [outParam (Scalar R K)]
  extends
    GetElem X n K (fun _ _ => True)
  where
  -- toVec (x : X) (i : n) : K -- maybe map to Euclidean space

  /-- Zero vector. -/
  zero : X
  zero_spec (i : n) : zero[i]  = 0

  /-- Scalar multiplication.

  `x` should be modified if it is passed with ref counter one. -/
  scal  (alpha : K) (x : X) : X
  scal_spec (alpha : K) (x : X) (i : n) :
    (scal alpha x)[i] = alpha • x[i]

  /-- `sum x = ∑ i, x[i]` -/
  sum (x : X) : K
  sum_spec (x : X) : sum x = Finset.univ.sum (fun i : n => x[i])

  /-- `asum x = ∑ i, |x[i]|` -/
  asum (x : X) : R
  asum_spec (x : X) : asum x = Scalar.ofReal (K:=K) ‖(WithLp.equiv 1 (n → K)).symm (fun i : n => x[i])‖

  /-- `nrm2 x = √∑ i, |x[i]|²` -/
  nrm2 (x : X) : R
  nrm2_spec (x : X) : nrm2 x = Scalar.ofReal (K:=K) ‖(WithLp.equiv 2 (n → K)).symm (fun i : n => x[i])‖

  /-- `iamax x = argmaxᵢ |x[i]|` -/
  iamax (x : X) : n -- this is inconsistent if `n` is empty
  iamax_spec (x : X) : Scalar.abs (x[iamax x]) = Scalar.ofReal (K:=K) ‖fun i : n => x[i]‖

  /-- `imaxRe x = argmaxᵢ (real x[i])` -/
  imaxRe (x : X) (h : 0 < nn) : n
  imaxRe_spec (x : X) (h : 0 < nn) :
    Scalar.toReal R (Scalar.real (x[imaxRe x h]))
    =
    iSup (α:=ℝ) (fun i : n => Scalar.toReal R <| Scalar.real (K:=K) (x[i]))

  /-- `iminRe x = argmaxᵢ (re x[i])` -/
  iminRe (x : X) (h : 0 < nn) : n
  iminRe_spec (x : X) (h : 0 < nn) :
    Scalar.toReal R (Scalar.real (x[iminRe x h]))
    =
    iInf (α:=ℝ) (fun i : n => Scalar.toReal R <| Scalar.real (K:=K) (x[i]))

  /-- `dot x y = ∑ i, conj x[i] y[i]` -/
  dot (x y : X) : K

  dot_spec (x y : X) :
    (dot x y) =
    let x' := (WithLp.equiv 2 (n → K)).symm (fun i : n => x[i])
    let y' := (WithLp.equiv 2 (n → K)).symm (fun i : n => y[i])
    (⟪x',y'⟫_K)

  conj (x : X) : X
  conj_spec (x : X) (i : n) :
    (conj x)[i]
    =
    starRingEnd _ x[i]

  /-- `axpy a x y = a • x + y`

  `y` should be modified if it is passed with ref counter one. -/
  axpy (alpha : K) (x y : X) : X

  axpy_spec (alpha : K) (x y : X) (i : n) :
    (axpy alpha x y)[i] = alpha • x[i] + y[i]

  /-- `axpby a b x y = a • x + b • y`

  `y` should be modified if it is passed with ref counter one. -/
  axpby (alpha : K) (x : X) (beta : K) (y : X) : X := axpy alpha x (scal beta y)

  axpby_spec (alpha beta : K) (x y : X) (i : n) :
    (axpby alpha x beta y)[i] = alpha • x[i] + beta • y[i]

  /-  Element wise operations -/

  /-- Element wise multiplication.

  `x` should be modified if it is passed with ref counter one. -/
  mul (x y : X) : X
  mul_spec (x y : X) (i : n) :
    (mul x y)[i] = x[i] * y[i]


-- open VectorType.Base Function in
-- /-- Lawful a vector `x : X` is fully determined by its elements.

-- This provides the following extensionality property `x = y` if `∀ i, x[i] = y[i]` -/
-- class VectorType.Lawful (X : Type*)
--     {n : outParam (Type*)} [IndexType n]
--     {R : outParam (Type*)} {K : outParam (Type*)}
--     [RealScalar R] [Scalar R K] [VectorType.Base X n K] : Prop where
--   toVec_injective : Injective (toVec (X:=X) (n:=n))


open VectorType.Base in
/-- Scalar multiplication by real number and dot product over real numbers for `VectorType` -/
class VectorType.RealOp (X : Type*)
    {n : outParam (Type*)} {nn : outParam ℕ} [IdxType n nn]
    {R : outParam (Type*)} {K : outParam (Type*)}
    {_  : outParam (RealScalar R)} {_ : outParam (Scalar R K)} [VectorType.Base X n K]
    [ScalarSMul R K] [ScalarInner R K]  where
  rscal (a : R) (x : X) : X
  rscal_spec (a : R) (x : X) (i : n):
    (rscal a x)[i] = a • x[i]

  rdot (x y : X) : R
  rdot_spec (x y : X) (i : n) :
    (rdot x y)
    =
    let x' := (WithLp.equiv 2 (n → K)).symm (fun i : n => x[i])
    let y' := (WithLp.equiv 2 (n → K)).symm (fun i : n => y[i])
    (⟪x',y'⟫_R)


open Function VectorType.Base Classical in
class VectorType.Dense (X : Type*)
    {n : outParam (Type*)} {nn : outParam ℕ} {_ : outParam (IdxType n nn)}
    {R K : outParam (Type*)} [RealScalar R] [Scalar R K]
    [VectorType.Base X n K]
  extends
    SetElem X n K (fun _ _ => True),
    LawfulSetElem X n,
    OfFn X n K,
    LawfulOfFn X n
  where
  fromVec (f : n → K) : X
  -- protected left_inv : LeftInverse fromVec toVec
  protected right_inv : RightInverse fromVec (fun (x : X) (i : n) => x[i])

  /-- Constant vector with all elements equial to `k`. -/
  const (k : K) : X
  const_spec (k : K) (i : n) : (const k)[i] = k

  /-- Scalar multiplication and scalar addition

  `x` should be modified if it is passed with ref counter one.  -/
  scalAdd (alpha beta : K) (x : X) : X
  scalAdd_spec (alpha beta : K) (x : X) (i : n) :
    (scalAdd alpha beta x)[i] = alpha * x[i] + beta


  /-- Element wise division.

  `x` should be modified if it is passed with ref counter one. -/
  div (x y : X) : X
  div_spec (x y : X) (i : n) :
    (div x y)[i] = x[i] / y[i]

  /-- Element wise inverse.

  `x` should be modified if it is passed with ref counter one. -/
  inv (x : X) : X
  inv_spec (x : X) (i : n) :
    (inv x)[i] = (x[i])⁻¹

  /-- Element wise exponentiation.

  `x` should be modified if it is passed with ref counter one. -/
  exp (x : X) : X
  exp_spec (x : X) (i : n) :
    (exp x)[i] = Scalar.exp (x[i])

  -- /-- Element wise logarithm. -/
  -- log {n} [IndexType n] (x : X) : X
  -- log_spec {n} [IndexType n] (x : X) :
  --   toVec (log x) = fun i => Scalar.log (toVec x i)

  -- /-- Element wise square root. -/
  -- sqrt {n} [IndexType n] (x : X) : X
  -- sqrt_spec {n} [IndexType n] (x : X) :
  --   toVec (sqrt x) = fun i => Scalar.sqrt (toVec x i)

  -- /-- Element wise sine. -/
  -- sin {n} [IndexType n] (x : X) : X
  -- sin_spec {n} [IndexType n] (x : X) :
  --   toVec (sin x) = fun i => Scalar.sin (toVec x i)

  -- /-- Element wise cosine. -/
  -- cos {n} [IndexType n] (x : X) : X
  -- cos_spec {n} [IndexType n] (x : X) :
  --   toVec (cos x) = fun i => Scalar.cos (toVec x i)

  -- /-- Element wise tangent. -/
  -- tan {n} [IndexType n] (x : X) : X
  -- tan_spec {n} [IndexType n] (x : X) :
  --   toVec (tan x) = fun i => Scalar.tan (toVec x i)

  -- /-- Element wise hyperbolic sine. -/
  -- sinh {n} [IndexType n] (x : X) : X
  -- sinh_spec {n} [IndexType n] (x : X) :
  --   toVec (sinh x) = fun i => Scalar.sinh (toVec x i)

  -- /-- Element wise hyperbolic cosine. -/
  -- cosh {n} [IndexType n] (x : X) : X
  -- cosh_spec {n} [IndexType n] (x : X) :
  --   toVec (cosh x) = fun i => Scalar.cosh (toVec x i)

  -- /-- Element wise hyperbolic tangent. -/
  -- tanh {n} [IndexType n] (x : X) : X
  -- tanh_spec {n} [IndexType n] (x : X) :
  --   toVec (tanh x) = fun i => Scalar.tanh (toVec x i)

  -- /-- Element wise inverse sine. -/
  -- asin {n} [IndexType n] (x : X) : X
  -- asin_spec {n} [IndexType n] (x : X) :
  --   toVec (asin x) = fun i => Scalar.asin (toVec x i)

  -- /-- Element wise inverse cosine. -/
  -- acos {n} [IndexType n] (x : X) : X
  -- acos_spec {n} [IndexType n] (x : X) :
  --   toVec (acos x) = fun i => Scalar.acos (toVec x i)

  -- /-- Element wise inverse tangent. -/
  -- atan {n} [IndexType n] (x : X) : X
  -- atan_spec {n} [IndexType n] (x : X) :
  --   toVec (atan x) = fun i => Scalar.atan (toVec x i)

  -- /-- Element wise inverse tangent of `y/x`. -/
  -- atan2 {n} [IndexType n] (y x : X) : X
  -- atan2_spec {n} [IndexType n] (y x : X) :
  --   toVec (atan2 y x) = fun i => Scalar.atan2 (toVec y i) (toVec x i)

  -- /-- Element wise inverse hyperbolic sine. -/
  -- asinh {n} [IndexType n] (x : X) : X
  -- asinh_spec {n} [IndexType n] (x : X) :
  --   toVec (asinh x) = fun i => Scalar.asinh (toVec x i)

  -- /-- Element wise inverse hyperbolic cosine. -/
  -- acosh {n} [IndexType n] (x : X) : X
  -- acosh_spec {n} [IndexType n] (x : X) :
  --   toVec (acosh x) = fun i => Scalar.acosh (toVec x i)

  -- /-- Element wise inverse hyperbolic tangent. -/
  -- atanh {n} [IndexType n] (x : X) : X
  -- atanh_spec {n} [IndexType n] (x : X) :
  --   toVec (atanh x) = fun i => Scalar.atanh (toVec x i)

  -- /-- Element wise power. -/
  -- pow {n} [IndexType n] (x : X) (n : ℕ) : X
  -- pow_spec {n} [IndexType n] (x : X) (n : ℕ) :
  --   toVec (pow X) = fun i => Scalar.pow (toVec x i) n

  -- /-- Element wise square. -/
  -- sqr {n} [IndexType n] (x : X) : X
  -- sqr_spec {n} [IndexType n] (x : X) :
  --   toVec (sqr x) = fun i => Scalar.sqr (toVec x i)

  -- /-- Element wise cube. -/
  -- cube {n} [IndexType n] (x : X) : X
  -- cube_spec {n} [IndexType n] (x : X) :
  --   toVec (cube x) = fun i => Scalar.cube (toVec x i)

  -- /-- Element wise sign. -/
  -- sign {n} [IndexType n] (x : X) : X
  -- sign_spec {n} [IndexType n] (x : X) :
  --   toVec (sign x) = fun i => Scalar.sign (toVec x i)



-- instance (X : Type*) (n : outParam (Type*)) {_ : outParam (IndexType n)} {R : outParam (Type*)} (K : outParam (Type*))
--     {_ : outParam (Scalar R R)} {_ : outParam (Scalar R K)} [VectorType.Base X n K] [VectorType.Dense X] :
--     VectorType.Lawful X where
--   toVec_injective := (VectorType.Dense.left_inv (X:=X) (n:=n) (K:=K)).injective

namespace VectorType

export VectorType.Base
  (zero zero_spec scal scal_spec sum sum_spec asum asum_spec nrm2 nrm2_spec
   iamax iamax_spec imaxRe imaxRe_spec iminRe iminRe_spec dot dot_spec axpy axpy_spec axpby axpby_spec
   mul mul_spec conj conj_spec)

-- export VectorType.Lawful (toVec_injective)

export VectorType.Dense (fromVec const const_spec scalAdd scalAdd_spec div div_spec
  inv inv_spec exp exp_spec)
export VectorType.RealOp (rscal rscal_spec rdot rdot_spec)

attribute [vector_to_spec]
  zero_spec
  const_spec
  scal_spec
  scalAdd_spec
  sum_spec
  asum_spec
  nrm2_spec
  iamax_spec
  dot_spec
  conj_spec
  axpy_spec
  axpby_spec
  div_spec
  inv_spec
  exp_spec
  mul_spec
  rscal_spec
  rdot_spec

section BasicOperations

variable
  {X : Type*} {n : Type u} {R K :  Type*}
  {_ : RealScalar R} {_ : Scalar R K} {nn : ℕ} {_ : IdxType n nn} [VectorType.Base X n K]

open VectorType

@[ext]
theorem ext [InjectiveGetElem X n] (x y : X) : (∀ (i : n), x[i] = y[i]) → x = y := by
  intro h
  apply getElem_injective (idx:=n)
  funext i
  exact (h i)

@[simp, simp_core]
theorem getElem_fromVec [Dense X] (x : n → K) (i : n) : (fromVec (X:=X) x)[i] = x i := by
  exact congrFun (Dense.right_inv (X:=X) x) i

-- todo: deprecate this
abbrev toVec (x : X) : n → K := fun i => x[i]
abbrev set [Dense X] (x : X) (i : n) (v : K) : X := setElem x i v .intro

instance : Add X := ⟨fun x y => axpby 1 x 1 y⟩
instance : Sub X := ⟨fun x y => axpby 1 x (-1) y⟩
instance : Neg X := ⟨fun x => scal (-1) x⟩
instance : SMul K X := ⟨fun s x => scal s x⟩
instance [ScalarSMul R K] [ScalarInner R K] [RealOp X] : SMul R X := ⟨fun s x => rscal s x⟩

instance : Zero X := ⟨zero⟩

instance : Inner K X := ⟨fun x y => dot x y⟩
instance [ScalarSMul R K] [ScalarInner R K] [RealOp X] : Inner R X := ⟨fun x y => (rdot x y)⟩
instance : Norm X := ⟨fun x => Scalar.toReal (K:=K) (nrm2 x)⟩
instance : Dist X := ⟨fun x y => ‖x-y‖⟩

@[simp, simp_core, vector_to_spec]
theorem toVec_add (x y : X) (i : n) : (x + y)[i] = x[i] + y[i] := by
  simp[vector_to_spec,HAdd.hAdd,Add.add]

instance : IsAddGetElem X n where
  getElem_add := by simp

@[simp, simp_core, vector_to_spec]
theorem toVec_sub (x y : X) (i : n) : (x - y)[i] = x[i] - y[i] := by
  conv => lhs; simp[vector_to_spec,HSub.hSub,Sub.sub]
  simp[sub_eq_add_neg]

@[simp, simp_core, vector_to_spec]
theorem toVec_neg (x : X) (i : n) : (- x)[i] = - x[i] := by
  simp[vector_to_spec,Neg.neg]

instance : IsNegGetElem X n where
  getElem_neg := by simp

@[simp, simp_core, vector_to_spec]
theorem toVec_smul (k : K) (x : X) (i : n) : (k • x)[i] = k • x[i] := by
  conv => lhs; simp only [HSMul.hSMul, SMul.smul,scal_spec]
  simp only [Pi.smul_apply, smul_eq_mul]

instance : IsSMulGetElem K X n where
  getElem_smul := by simp

@[simp, simp_core, vector_to_spec]
theorem toVec_smul' [ScalarSMul R K] [ScalarInner R K] [RealOp X] (r : R) (x : X) (i : n) :
    (r • x)[i] = r • x[i] := by
  conv => lhs; simp only [HSMul.hSMul, SMul.smul,rscal_spec]
  rfl

instance [ScalarSMul R K] [ScalarInner R K] [RealOp X] : IsSMulGetElem R X n where
  getElem_smul := by simp

@[simp, simp_core, vector_to_spec]
theorem toVec_zero (i : n) : (0 : X)[i] = 0 := by
  conv => lhs; simp only [Zero.zero,OfNat.ofNat]
  simp only [zero_spec]

instance : IsZeroGetElem X n where
  getElem_zero := by simp

@[vector_to_spec]
theorem inner_spec (x y : X) :
    ⟪x,y⟫_K
    =
    ⟪(WithLp.equiv 2 (n → K)).symm (fun i : n => x[i]), (WithLp.equiv 2 (n → K)).symm (fun i : n => y[i])⟫_K := by
  simp only [inner, dot_spec, WithLp.equiv_symm_pi_apply]

instance [IdxType.Fold' n] : IsInnerGetElem K X n where
  inner_eq_sum_getElem := by simp[vector_to_spec, IdxType.sum_eq_finset_sum]

@[vector_to_spec]
theorem inner_spec_real [ScalarSMul R K] [ScalarInner R K] [RealOp X] (x y : X) :
    ⟪x,y⟫_R
    =
    ⟪(WithLp.equiv 2 (n → K)).symm (fun i : n => x[i]), (WithLp.equiv 2 (n → K)).symm (fun i : n => y[i])⟫_R := by
  simp only [inner, dot_spec, WithLp.equiv_symm_pi_apply]
  sorry_proof

instance [IdxType.Fold' n] [ScalarSMul R K] [ScalarInner R K] [RealOp X] : IsInnerGetElem K X n where
  inner_eq_sum_getElem := by simp[vector_to_spec, IdxType.sum_eq_finset_sum]

@[vector_to_spec]
theorem norm_spec (x : X) :
    ‖x‖
    =
    ‖(WithLp.equiv 2 (n → K)).symm (fun i : n => x[i])‖ := by
  conv => lhs; simp only [norm]; simp only [nrm2_spec]
  simp only [Scalar.toReal_ofReal]

@[vector_to_spec]
theorem dist_spec (x y : X) :
    dist x y
    =
    dist ((WithLp.equiv 2 (n → K)).symm (fun i : n => x[i])) ((WithLp.equiv 2 (n → K)).symm (fun i : n => y[i])) := by
  conv => lhs; simp [Dist.dist,vector_to_spec]
  conv => rhs; rw[NormedAddCommGroup.dist_eq]
  rfl


def iamax? (x : X) : Option n :=
  if _ : 0 < nn then
    some (iamax x)
  else
    none

def imaxRe? (x : X) : Option n :=
  if h : 0 < nn then
    some (imaxRe x h)
  else
    none

def iminRe? (x : X) : Option n :=
  if h : 0 < nn then
    some (iminRe x h)
  else
    none

def updateElem [Dense X] (x : X) (i : n) (f : K → K) : X :=
  let xi := x[i]
  setElem x i (f xi) (by dsimp)

@[simp, simp_core]
theorem add_set_zero_eq_updateElem [InjectiveGetElem X n] [Dense X] (x : X) (i : n) (xi : K) :
    x + setElem 0 i xi (by dsimp) = updateElem x i (fun xi' => xi' + xi) := by
  ext
  simp[vector_to_spec,updateElem]
  sorry_proof --split_ifs <;> simp_all

@[simp, simp_core]
theorem set_zero_add_eq_updateElem [InjectiveGetElem X n] [Dense X] (x : X) (i : n) (xi : K) :
    setElem 0 i xi (by dsimp) + x = updateElem x i (fun xi' => xi + xi') := by
  sorry_proof
  -- apply Lawful.toVec_injective;
  -- funext j
  -- simp[vector_to_spec,updateElem]
  -- split_ifs <;> simp_all

end BasicOperations


section AlgebraicInstances

variable
  {X : Type*} {n : Type*} {R K : Type*}
  {_ : RealScalar R} {_ : Scalar R K} {nn} {_ : IdxType n nn} [VectorType.Base X n K] [InjectiveGetElem X n]

open VectorType

instance [VectorType.Base X n R] : VectorType.RealOp X where
  rscal := VectorType.Base.scal
  rscal_spec := by simp[vector_to_spec]

  rdot := VectorType.Base.dot
  rdot_spec := by simp[vector_to_spec]

--set_option trace.Meta.synthOrder true
instance (priority:=low) : AddCommGroup X where
  add_assoc := by intros; ext; simp [vector_to_spec, add_assoc]
  zero_add  := by intros; ext; simp [vector_to_spec]
  add_zero  := by intros; ext; simp [vector_to_spec]
  neg_add_cancel := by intros; ext; simp [vector_to_spec]
  add_comm       := by intros; ext; simp [vector_to_spec, add_comm]
  sub_eq_add_neg := by intros; ext; simp [vector_to_spec, sub_eq_add_neg]
  nsmul n x := scal (n:K) x
  nsmul_zero := by intros; ext; simp [vector_to_spec]
  nsmul_succ := by intros; ext; simp [vector_to_spec, add_mul]
  zsmul n x := scal (n:K) x
  zsmul_zero' := by intros; ext; simp[vector_to_spec]
  zsmul_neg'  := by intros; ext; simp[vector_to_spec, add_mul]
  zsmul_succ' := by intros; ext; simp[vector_to_spec, add_mul]

instance (priority:=low) : Module K X where
  one_smul := by intros; ext; simp[vector_to_spec]
  mul_smul := by intros; ext; simp[mul_smul,vector_to_spec,mul_assoc]
  smul_zero := by intros; ext; simp[vector_to_spec]
  smul_add := by intros; ext; simp[vector_to_spec,mul_add]
  add_smul := by intros; ext; simp[add_smul,vector_to_spec,add_mul]
  zero_smul := by intros; ext; simp[vector_to_spec]

instance : IsModuleGetElem K X n where

instance (priority:=low) [ScalarSMul R K] [ScalarInner R K] [RealOp X] : Module R X where
  one_smul := by intros; ext; simp[vector_to_spec]
  mul_smul := by intros; ext; simp[mul_smul,vector_to_spec,mul_assoc]
  smul_zero := by intros; ext; simp[vector_to_spec]
  smul_add := by intros; ext; simp[vector_to_spec,mul_add]
  add_smul := by intros; ext; simp[add_smul,vector_to_spec,add_mul]
  zero_smul := by intros; ext; simp[vector_to_spec]

instance [ScalarSMul R K] [ScalarInner R K] [RealOp X] : IsModuleGetElem R X n where

instance (priority:=low) : PseudoMetricSpace X where
  dist_self := by intros; simp[dist_spec]
  dist_comm := by intros; simp[dist_spec,dist_comm]
  dist_triangle := by intros; simp[dist_spec,dist_triangle]

instance (priority:=low) : NormedAddCommGroup X where
  dist_eq := by intros; rfl
  eq_of_dist_eq_zero := by
    intro x y h
    apply ext
    sorry_proof
    -- apply (WithLp.equiv 2 (n → K)).symm.injective
    -- simp only [dist_spec] at h
    -- exact (eq_of_dist_eq_zero h)

instance (priority:=low) instNormedSpace : NormedSpace K X where
  norm_smul_le := by
    simp only [norm_spec]
    simp [norm_smul_le,vector_to_spec]
    sorry_proof

instance : IsContinuousGetElem X n where
  continuous_getElem := by sorry_proof

instance (priority:=low) [ScalarSMul R K] [ScalarInner R K] [RealOp X] : NormedSpace R X where
  norm_smul_le := by
    simp only [norm_spec]
    simp [norm_smul_le,vector_to_spec, ScalarSMul.smul_eq_mul_make]
    sorry_proof

instance (priority:=low) instAdjointSpace : AdjointSpace K X where
  inner_top_equiv_norm := by
    use 1; use 1
    simp only [inner_spec,norm_spec]
    constructor
    · simp only [gt_iff_lt, zero_lt_one]
    constructor
    · simp only [gt_iff_lt, zero_lt_one]
    · intro x
      constructor
      · rw[norm_sq_eq_inner (𝕜:=K)]; simp only [one_smul,le_refl]
      · rw[norm_sq_eq_inner (𝕜:=K)]; simp only [one_smul,le_refl]
  conj_symm := by
    simp only [inner_spec]
    intro x y;
    apply conj_symm
  add_left := by
    intros; simp [vector_to_spec, WithLp.equiv_symm_add,add_left,←Finset.sum_add_distrib,add_mul]
  smul_left := by
    intros; simp [vector_to_spec, WithLp.equiv_symm_smul,smul_left,Finset.mul_sum,mul_assoc]

instance (priority:=low) instAdjointSpaceReal [ScalarSMul R K] [ScalarInner R K] [RealOp X] :
    AdjointSpace R X where
  inner_top_equiv_norm := by
    use 1; use 1
    simp only [inner_spec,norm_spec]
    constructor
    · simp only [gt_iff_lt, zero_lt_one]
    constructor
    · simp only [gt_iff_lt, zero_lt_one]
    · intro x
      constructor
      · rw[norm_sq_eq_inner (𝕜:=K)]; simp only [one_smul,le_refl]; sorry_proof
      · rw[norm_sq_eq_inner (𝕜:=K)]; simp only [one_smul,le_refl]; sorry_proof
  conj_symm := by
    intro x y;
    simp only [inner_spec_real]
    apply conj_symm
  add_left := by
    intros; simp [vector_to_spec, WithLp.equiv_symm_add,add_left,←Finset.sum_add_distrib]
  smul_left := by
    intros; simp [vector_to_spec, WithLp.equiv_symm_smul,smul_left,Finset.mul_sum]

instance (priority:=low) instInnerProductSpace : InnerProductSpace K X where
  -- toNormedSpace := instNormedSpace
  norm_sq_eq_inner := by
    simp only [inner_spec,norm_spec]
    intro x
    apply norm_sq_eq_inner
  conj_symm := by
    simp only [inner_spec]
    intro x y;
    apply conj_symm
  add_left := by
    intros; simp [vector_to_spec, WithLp.equiv_symm_add,add_left,←Finset.sum_add_distrib,add_mul]
  smul_left := by
    intros; simp only [vector_to_spec, WithLp.equiv_symm_smul,smul_left,Finset.mul_sum]
    sorry_proof


end AlgebraicInstances


section Equivalences

variable
  {X : Type*} {n : Type u} {R K :  Type*}
  {_ : RealScalar R} {_ : Scalar R K} {nn} {_ : IdxType n nn} [VectorType.Base X n K] [InjectiveGetElem X n]

def toVecₗ : X →ₗ[K] (n → K) :=
  ⟨⟨fun (x : X) (i : n) => x[i],
   by intros; funext i; simp[vector_to_spec]⟩,
   by intros; funext i; simp[vector_to_spec]⟩

instance (priority:=low) : FiniteDimensional K X :=
   FiniteDimensional.of_injective (V₂:=n→K) toVecₗ (getElem_injective)

instance (priority:=low): CompleteSpace X := sorry_proof

variable [VectorType.Dense X]

def vequiv : X ≃ (n → K) where
  toFun x i := x[i]
  invFun := fromVec
  left_inv := by intro x; ext; simp
  right_inv := Dense.right_inv


@[vector_to_spec]
theorem vequiv_apply_eq_toVec (x : X) :
  vequiv x = fun i : n => x[i] := rfl

@[vector_to_spec]
theorem vequiv_symm_apply_eq_fromVec (f : n → K) :
  vequiv.symm f = fromVec (X:=X) f := rfl

@[simp, simp_core]
theorem fromVec_toVec (x : X) :
    fromVec (getElem x · (by dsimp)) = x := by
  rw[← vequiv_apply_eq_toVec, ← vequiv_symm_apply_eq_fromVec]
  simp

/-- Linear vequivalence between vector type `X` and `n → K` -/
def vequivₗ : X ≃ₗ[K] (n → K) :=
  LinearEquiv.mk toVecₗ vequiv.symm (vequiv.left_inv) (vequiv.right_inv)

variable (X)
noncomputable
def basis : _root_.Basis n K X := Basis.ofEquivFun (ι:=n) (R:=K) (M:=X) vequivₗ
variable {X}

@[simp, simp_core]
theorem finrank_eq_index_card : Module.finrank K X = Fintype.card n :=
  Module.finrank_eq_card_basis (basis X)

/-- Continuous linear vequivalence between vector type `X` and `n → K` -/
def vequivL : X ≃L[K] (n → K) := ContinuousLinearEquiv.mk vequivₗ
  (by simp; apply LinearMap.continuous_of_finiteDimensional)
  (by simp; apply LinearMap.continuous_of_finiteDimensional)

end Equivalences


section Functions

end Functions

variable
  {X : Type*} {n : Type u} {R K :  Type*}
  {_ : RealScalar R} {_ : Scalar R K} {nn : ℕ} {_ : IdxType n nn}
  [VectorType.Base X n K] [VectorType.Dense X] [IdxType.Fold' n]

@[inline]
def mapIdx (f : n → K → K) (x : X) : X :=
  IdxType.fold .full (init:=x) (fun (i : n) x =>
    let xi := x[i]
    setElem x i (f i xi) (by dsimp))

@[inline]
def mapIdx₂ (f : n → K → K → K×K) (x y : X) : X×X :=
  IdxType.fold .full (init:=(x,y)) (fun (i : n) (x,y)  =>
    let xi := x[i]
    let yi := y[i]
    let (xi',yi') := f i xi yi
    (setElem x i xi' (by dsimp), setElem y i yi' (by dsimp)))

def map (f : K → K) (x : X) : X := mapIdx (fun _ => f) x
def map₂ (f : K → K → K×K) (x y : X) : X×X := mapIdx₂ (fun _ => f) x y

section Functions

variable
  {X : Type*} {n : Type u} {R :  Type*}
  {_ : RealScalar R} {nn : ℕ} {_ : IdxType n nn}
  [VectorType.Base X n R] [VectorType.Dense X]

def amax (x : X) : R :=
  if h : 0 < nn then
    Scalar.abs x[iamax x]
  else
    0

def max (x : X) : R :=
  if h : 0 < nn then
    x[imaxRe x h]
  else
    0

def min (x : X) : R :=
  if h : 0 < nn then
    x[iminRe x h]
  else
    0

def logsumexp (x : X) : R :=
  if 0 < nn then
    let xmax := max x
    let x := exp (scalAdd 1 (-xmax) x)
    let s := sum x
    Scalar.log s + xmax
  else
    0

def softmax (x : X) : X :=
  let xmax := max x
  let x' := exp (scalAdd 1 (-xmax) x)
  let w := sum x'
  scal w⁻¹ x'

end Functions
