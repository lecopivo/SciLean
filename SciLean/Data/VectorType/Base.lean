import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Data.Matrix.Basic

import SciLean.Analysis.AdjointSpace.Basic
import SciLean.Analysis.Scalar
import SciLean.Data.IndexType
import SciLean.Data.VectorType.Init

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
class VectorType.Base (X : Type*) (n : outParam (Type*)) [outParam (IndexType n)] {R : outParam (Type*)}  (K : outParam (Type*))
        [outParam (RealScalar R)] [outParam (Scalar R K)] where
  toVec (x : X) : (n → K) -- maybe map to Euclidean space

  /-- Zero vector. -/
  zero : X
  zero_spec : toVec zero = 0

  /-- Scalar multiplication.

  `x` should be modified if it is passed with ref counter one. -/
  scal  (alpha : K) (x : X) : X
  scal_spec (alpha : K) (x : X) :
    toVec (scal alpha x) = alpha • toVec x

  /-- Scalar multiplication and scalar addition

  `x` should be modified if it is passed with ref counter one. -/
  scalAdd  (alpha beta : K) (x : X) : X
  scalAdd_spec (alpha beta : K) (x : X) :
    toVec (scalAdd alpha beta x) = fun i => alpha * toVec x i + beta

  /-- `sum x = ∑ i, x[i]` -/
  sum (x : X) : K
  sum_spec (x : X) : sum x = Finset.univ.sum (fun i : n => toVec x i)

  /-- `asum x = ∑ i, |x[i]|` -/
  asum (x : X) : R
  asum_spec (x : X) : asum x = Scalar.ofReal (K:=K) ‖(WithLp.equiv 1 (n → K)).symm (toVec x)‖

  /-- `nrm2 x = √∑ i, |x[i]|²` -/
  nrm2 (x : X) : R
  nrm2_spec (x : X) : nrm2 x = Scalar.ofReal (K:=K) ‖(WithLp.equiv 2 (n → K)).symm (toVec x)‖

  /-- `iamax x = argmaxᵢ |x[i]|` -/
  iamax (x : X) : n -- this is inconsistent if `n` is empty
  iamax_spec (x : X) : Scalar.abs (toVec x (iamax x)) = Scalar.ofReal (K:=K) ‖toVec x‖

  /-- `imaxRe x = argmaxᵢ (real x[i])` -/
  imaxRe (x : X) (h : 0 < size n) : n
  imaxRe_spec (x : X) (h : 0 < size n) :
    Scalar.toReal R (Scalar.real (toVec x (imaxRe x h)))
    =
    iSup (α:=ℝ) (fun i => Scalar.toReal R <| Scalar.real (K:=K) (toVec x i))

  /-- `iminRe x = argmaxᵢ (re x[i])` -/
  iminRe (x : X) (h : 0 < size n) : n
  iminRe_spec (x : X) (h : 0 < size n) :
    Scalar.toReal R (Scalar.real (toVec x (iminRe x h)))
    =
    iInf (α:=ℝ) (fun i => Scalar.toReal R <| Scalar.real (K:=K) (toVec x i))

  /-- `dot x y = ∑ i, conj x[i] y[i]` -/
  dot (x y : X) : K

  dot_spec (x y : X) :
    (dot x y) =
    let x' := (WithLp.equiv 2 (n → K)).symm (toVec x)
    let y' := (WithLp.equiv 2 (n → K)).symm (toVec y)
    (⟪x',y'⟫_K)

  /-- `axpy a x y = a • x + y`

  `y` should be modified if it is passed with ref counter one. -/
  axpy (alpha : K) (x y : X) : X

  axpy_spec (alpha : K) (x y : X) :
    toVec (axpy alpha x y) = alpha • toVec x + toVec y

  /-- `axpby a b x y = a • x + b • y`

  `y` should be modified if it is passed with ref counter one. -/
  axpby (alpha : K) (x : X) (beta : K) (y : X) : X := axpy alpha x (scal beta y)

  axpby_spec (alpha beta : K) (x y : X) :
    toVec (axpby alpha x beta y) = alpha • toVec x + beta • toVec y

  /-  Element wise operations -/

  /-- Element wise multiplication.

  `x` should be modified if it is passed with ref counter one. -/
  mul (x y : X) : X
  mul_spec (x y : X) :
    toVec (mul x y) = toVec x * toVec y

open VectorType.Base Function in
/-- Lawful a vector `x : X` is fully determined by its elements.

This provides the following extensionality property `x = y` if `∀ i, x[i] = y[i]` -/
class VectorType.Lawful (X : Type*)
    {n : outParam (Type*)} [IndexType n]
    {R : outParam (Type*)} {K : outParam (Type*)}
    [RealScalar R] [Scalar R K] [VectorType.Base X n K] : Prop where
  toVec_injective : Injective (toVec (X:=X) (n:=n))

open VectorType.Base in
class VectorType.RealOp (X : Type*)
    {n : outParam (Type*)} [IndexType n]
    {R : outParam (Type*)} {K : outParam (Type*)}
    {_  : outParam (RealScalar R)} {_ : outParam (Scalar R K)} [VectorType.Base X n K]
    [ScalarSMul R K] [ScalarInner R K]  where
  rscal (a : R) (x : X) : X
  rscal_spec (a : R) (x : X) :
    toVec (rscal a x) = a • toVec x

  rdot (x y : X) : R
  rdot_spec (x y : X) :
    (rdot x y)
    =
    let x' := (WithLp.equiv 2 (n → K)).symm (toVec x)
    let y' := (WithLp.equiv 2 (n → K)).symm (toVec y)
    (⟪x',y'⟫_R)


open Function VectorType.Base Classical in
class VectorType.Dense (X : Type*)
    {n : outParam (Type*)} {_ : outParam (IndexType n)}
    {R K : outParam (Type*)} [RealScalar R] [Scalar R K]
    [VectorType.Base X n K] where
  fromVec (f : n → K) : X
  -- protected left_inv : LeftInverse fromVec toVec
  protected right_inv : RightInverse fromVec toVec

  /-- Set the `i`-th element of `x` to `v`. -/
  set (x : X) (i : n) (v : K) : X
  set_spec (x : X) (i : n) (v : K) :
    toVec (set x i v)
    =
    fun j =>
      if j = i then
         v
      else
         toVec x j

  /-- Constant vector with all elements equial to `k`. -/
  const (k : K) : X
  const_spec (k : K) : toVec (const k) = fun _ => k

  /-- Element wise division.

  `x` should be modified if it is passed with ref counter one. -/
  div (x y : X) : X
  div_spec (x y : X) :
    toVec (div x y) = toVec x / toVec y

  /-- Element wise inverse.

  `x` should be modified if it is passed with ref counter one. -/
  inv (x : X) : X
  inv_spec (x : X) :
    toVec (inv x) = fun i => (toVec x i)⁻¹

  /-- Element wise exponentiation.

  `x` should be modified if it is passed with ref counter one. -/
  exp (x : X) : X
  exp_spec (x : X) :
    toVec (exp x) = fun i => Scalar.exp (toVec x i)

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
  (toVec zero zero_spec scal scal_spec scalAdd scalAdd_spec sum sum_spec asum asum_spec nrm2 nrm2_spec
   iamax iamax_spec imaxRe imaxRe_spec iminRe iminRe_spec dot dot_spec axpy axpy_spec axpby axpby_spec
   mul mul_spec)

export VectorType.Lawful (toVec_injective)

export VectorType.Dense (fromVec set set_spec const const_spec div div_spec inv inv_spec exp exp_spec)
export VectorType.RealOp (rscal rscal_spec rdot rdot_spec)

attribute [vector_to_spec,vector_from_spec ←]
  zero_spec
  const_spec
  scal_spec
  scalAdd_spec
  sum_spec
  asum_spec
  nrm2_spec
  iamax_spec
  dot_spec
  axpy_spec
  axpby_spec
  div_spec
  inv_spec
  exp_spec
  mul_spec
  set_spec
  rscal_spec
  rdot_spec

section BasicOperations

variable
  {X : Type*} {n : Type u} {R K :  Type*}
  {_ : RealScalar R} {_ : Scalar R K} {_ : IndexType n} [VectorType.Base X n K]

open VectorType

instance (priority:=low) : Add X := ⟨fun x y => axpy 1 x y⟩
instance (priority:=low) : Sub X := ⟨fun x y => axpby 1 x (-1) y⟩
instance (priority:=low) : Neg X := ⟨fun x => scal (-1) x⟩
instance (priority:=low) : SMul K X := ⟨fun s x => scal s x⟩
instance (priority:=low) [ScalarSMul R K] [ScalarInner R K] [RealOp X] : SMul R X := ⟨fun s x => rscal s x⟩

instance (priority:=low) : Zero X := ⟨zero⟩

instance (priority:=low) : Inner K X := ⟨fun x y => dot x y⟩
instance (priority:=low) [ScalarSMul R K] [ScalarInner R K] [RealOp X] : Inner R X := ⟨fun x y => (rdot x y)⟩
instance (priority:=low) : Norm X := ⟨fun x => Scalar.toReal (K:=K) (nrm2 x)⟩
instance (priority:=low) : Dist X := ⟨fun x y => ‖x-y‖⟩

@[vector_to_spec, vector_from_spec ←]
theorem add_spec (x y : X) : toVec (x + y) = toVec x + toVec y := by
  simp only [HAdd.hAdd, Add.add, axpy_spec, Pi.smul_apply, smul_eq_mul, one_mul]

@[vector_to_spec, vector_from_spec ←]
theorem sub_spec (x y : X) : toVec (x - y) = toVec x - toVec y := by
  conv => lhs; simp only [HSub.hSub,Sub.sub,axpby_spec]
  simp only [one_smul, neg_smul, sub_eq_add_neg]

@[vector_to_spec, vector_from_spec ←]
theorem neg_spec (x : X) : toVec (- x) = - toVec x := by
  simp only [Neg.neg, scal_spec, neg_smul, Pi.smul_apply, smul_eq_mul, one_mul]

@[vector_to_spec, vector_from_spec ←]
theorem smul_spec (k : K) (x : X) : toVec (k • x) = k • toVec x := by
  conv => lhs; simp only [HSMul.hSMul, SMul.smul,scal_spec]
  funext i; simp only [Pi.smul_apply, smul_eq_mul]

@[vector_to_spec, vector_from_spec ←]
theorem smul_spec' [ScalarSMul R K] [ScalarInner R K] [RealOp X] (r : R) (x : X) : toVec (r • x) = r • toVec x := by
  conv => lhs; simp only [HSMul.hSMul, SMul.smul,scal_spec]
  funext i; simp only [Pi.smul_apply, smul_eq_mul]
  sorry_proof

@[vector_to_spec, vector_from_spec ←]
theorem zero_spec' : toVec (0 : X) = 0 := by
  conv => lhs; simp only [Zero.zero,OfNat.ofNat]
  simp only [zero_spec]

@[vector_to_spec, vector_from_spec ←]
theorem inner_spec (x y : X) :
    ⟪x,y⟫_K
    =
    ⟪(WithLp.equiv 2 (n → K)).symm (toVec x), (WithLp.equiv 2 (n → K)).symm (toVec y)⟫_K := by
  simp only [inner, dot_spec, WithLp.equiv_symm_pi_apply]

@[vector_to_spec, vector_from_spec ←]
theorem inner_spec_real [ScalarSMul R K] [ScalarInner R K] [RealOp X] (x y : X) :
    ⟪x,y⟫_R
    =
    ⟪(WithLp.equiv 2 (n → K)).symm (toVec x), (WithLp.equiv 2 (n → K)).symm (toVec y)⟫_R := by
  simp only [inner, dot_spec, WithLp.equiv_symm_pi_apply]
  sorry_proof

@[vector_to_spec, vector_from_spec ←]
theorem norm_spec (x : X) :
    ‖x‖
    =
    ‖(WithLp.equiv 2 (n → K)).symm (toVec x)‖ := by
  conv => lhs; simp only [norm]; simp only [nrm2_spec]
  simp only [Scalar.toReal_ofReal]

@[vector_to_spec, vector_from_spec ←]
theorem dist_spec (x y : X) :
    dist x y
    =
    dist ((WithLp.equiv 2 (n → K)).symm (toVec x)) ((WithLp.equiv 2 (n → K)).symm (toVec y)) := by
  conv => lhs; simp [Dist.dist,vector_to_spec]
  conv => rhs; rw[NormedAddCommGroup.dist_eq]


def iamax? (x : X) : Option n :=
  if _ : 0 < size n then
    some (iamax x)
  else
    none

def imaxRe? (x : X) : Option n :=
  if h : 0 < size n then
    some (imaxRe x h)
  else
    none

def iminRe? (x : X) : Option n :=
  if h : 0 < size n then
    some (iminRe x h)
  else
    none

def updateElem [Dense X] (x : X) (i : n) (f : K → K) : X :=
  let xi := toVec x i
  VectorType.set x i (f xi)


end BasicOperations


section AlgebraicInstances

variable
  {X : Type*} {n : Type*} {R K : Type*}
  {_ : RealScalar R} {_ : Scalar R K} {_ : IndexType n} [VectorType.Base X n K] [VectorType.Lawful X]

open VectorType

@[ext]
theorem ext (x y : X) : (∀ (i : n), toVec x i = toVec y i) → x = y := by
  intro h
  apply toVec_injective
  funext i
  exact (h i)

instance [VectorType.Base X n R] : VectorType.RealOp X where
  rscal := VectorType.Base.scal
  rscal_spec := by simp[vector_to_spec]

  rdot := VectorType.Base.dot
  rdot_spec := by simp[vector_to_spec]

--set_option trace.Meta.synthOrder true
instance (priority:=low) : AddCommGroup X where
  add_assoc := by intros; ext; simp only [add_spec, add_assoc]
  zero_add := by intros; ext; simp only [add_spec, zero_spec', zero_add]
  add_zero := by intros; ext; simp only [add_spec, zero_spec', add_zero]
  neg_add_cancel := by intros; ext; simp only [add_spec, neg_spec, neg_add_cancel, zero_spec']
  add_comm := by intros; ext; simp only [add_spec, add_comm]
  sub_eq_add_neg := by intros; ext; simp only [sub_spec, sub_eq_add_neg, add_spec, neg_spec]
  nsmul n x := scal (n:K) x
  nsmul_zero := by intros; ext; simp only [CharP.cast_eq_zero, scal_spec, zero_smul, zero_spec']
  nsmul_succ := by intros; ext; simp only [Nat.cast_add, Nat.cast_one, scal_spec, add_smul, one_smul, add_spec]
  zsmul n x := scal (n:K) x
  zsmul_zero' := by intros; ext; simp[scal_spec,vector_to_spec]
  zsmul_neg' := by intros; ext; simp[zsmul_neg',scal_spec,add_smul,vector_to_spec,add_mul]
  zsmul_succ' := by intros; ext; simp[scal_spec,add_smul,vector_to_spec,add_mul]

instance (priority:=low) : Module K X where
  one_smul := by intros; ext; simp[vector_to_spec]
  mul_smul := by intros; ext; simp[mul_smul,vector_to_spec,mul_assoc]
  smul_zero := by intros; ext; simp[vector_to_spec]
  smul_add := by intros; ext; simp[vector_to_spec,mul_add]
  add_smul := by intros; ext; simp[add_smul,vector_to_spec,add_mul]
  zero_smul := by intros; ext; simp[vector_to_spec]

instance (priority:=low) [ScalarSMul R K] [ScalarInner R K] [RealOp X] : Module R X where
  one_smul := by intros; ext; simp[vector_to_spec]
  mul_smul := by intros; ext; simp[mul_smul,vector_to_spec,mul_assoc]
  smul_zero := by intros; ext; simp[vector_to_spec]
  smul_add := by intros; ext; simp[vector_to_spec,mul_add]
  add_smul := by intros; ext; simp[add_smul,vector_to_spec,add_mul]
  zero_smul := by intros; ext; simp[vector_to_spec]

instance (priority:=low) : PseudoMetricSpace X where
  dist_self := by intros; simp[dist_spec]
  dist_comm := by intros; simp[dist_spec,dist_comm]
  dist_triangle := by intros; simp[dist_spec,dist_triangle]

instance (priority:=low) : NormedAddCommGroup X where
  dist_eq := by intros; rfl
  eq_of_dist_eq_zero := by
    intro x y h
    apply toVec_injective
    apply (WithLp.equiv 2 (n → K)).symm.injective
    simp only [dist_spec] at h
    exact (eq_of_dist_eq_zero h)

instance (priority:=low) instNormedSpace : NormedSpace K X where
  norm_smul_le := by
    simp only [norm_spec]
    simp [norm_smul_le,vector_to_spec]

instance (priority:=low) [ScalarSMul R K] [ScalarInner R K] [RealOp X] : NormedSpace R X where
  norm_smul_le := by
    simp only [norm_spec]
    simp [norm_smul_le,vector_to_spec, ScalarSMul.smul_eq_mul_make]

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
    intros; simp only [inner_spec,add_spec, WithLp.equiv_symm_add,add_left]
  smul_left := by
    intros; simp only [inner_spec,smul_spec, WithLp.equiv_symm_smul,smul_left]

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
    intros; simp [vector_to_spec, WithLp.equiv_symm_add,add_left]
  smul_left := by
    intros; simp [vector_to_spec, WithLp.equiv_symm_smul,smul_left]

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
    intros; simp only [inner_spec,add_spec, WithLp.equiv_symm_add,add_left]
  smul_left := by
    intros; simp only [inner_spec,smul_spec, WithLp.equiv_symm_smul,smul_left]


end AlgebraicInstances


section Equivalences

variable
  {X : Type*} {n : Type u} {R K :  Type*}
  {_ : RealScalar R} {_ : Scalar R K} {_ : IndexType n} [VectorType.Base X n K] [VectorType.Lawful X]

def toVecₗ : X →ₗ[K] (n → K) :=
  ⟨⟨VectorType.toVec, by simp[vector_to_spec]⟩,by simp[vector_to_spec]⟩

instance (priority:=low) : FiniteDimensional K X :=
   FiniteDimensional.of_injective (V₂:=n→K) toVecₗ VectorType.Lawful.toVec_injective

instance (priority:=low): CompleteSpace X := sorry_proof

variable [VectorType.Dense X]

def vequiv : X ≃ (n → K) where
  toFun := toVec
  invFun := fromVec
  left_inv := by
    have h : (toVec : X → (n → K)).Bijective := by
      constructor
      · apply Lawful.toVec_injective
      · apply Dense.right_inv.surjective
    intro x
    sorry_proof -- this should be true
  right_inv := Dense.right_inv


@[vector_to_spec]
theorem vequiv_apply_eq_toVec (x : X) :
  vequiv x = toVec x := rfl

@[vector_to_spec]
theorem vequiv_symm_apply_eq_fromVec (f : n → K) :
  vequiv.symm f = fromVec (X:=X) f := rfl

omit [Lawful X] in
@[simp, simp_core]
theorem toVec_fromVec (f : n → K) :
    toVec (fromVec (X:=X) f) = f := by
  rw[VectorType.Dense.right_inv]

@[simp, simp_core]
theorem fromVec_toVec (x : X) :
    fromVec (toVec x) = x := by
  rw[← vequiv_apply_eq_toVec, ← vequiv_symm_apply_eq_fromVec]
  simp

/-- Linear vequivalence between vector type `X` and `n → K` -/
def vequivₗ : X ≃ₗ[K] (n → K) :=
  LinearEquiv.mk toVecₗ vequiv.symm (vequiv.left_inv) (vequiv.right_inv)

variable (X)
noncomputable
def basis : Basis n K X := Basis.ofEquivFun (ι:=n) (R:=K) (M:=X) vequivₗ
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

variable
  {X : Type*} {n : Type u} {R :  Type*}
  {_ : RealScalar R} {_ : IndexType n} [VectorType.Base X n R] [VectorType.Dense X]

def max (x : X) : R :=
  if h : 0 < size n then
    toVec x (imaxRe x h)
  else
    0

def min (x : X) : R :=
  if h : 0 < size n then
    toVec x (iminRe x h)
  else
    0

def logsumexp (x : X) : R :=
  if 0 < size n then
    let xmax := max x
    let x := exp (scalAdd 1 (-xmax) x)
    let s := sum x
    Scalar.log s + xmax
  else
    0

def softmax (x : X) : X :=
  let xmax := max x
  let x' := scalAdd 1 (-xmax) x
  let w := sum (exp x')
  scal w⁻¹ x'

end Functions
