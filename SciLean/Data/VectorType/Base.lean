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
  - `NormedAddCommGroup X` with l₂ norm
  - `InnerProductSpace K X`
  - `AdjointSpace K X`
  - `FiniteDimensional K X`

This class is designed to provide Basic Linear Algebra Subprograms(BLAS) which allows us to define
vector space structure on `X` that is computationally efficient.
 -/
class VectorType.Base (X : Type*) (n : outParam (Type*)) [IndexType n] {R : outParam (Type*)}  (K : outParam (Type*))
        [Scalar R R] [Scalar R K] where
  vequiv : X ≃ (n → K) -- maybe EuclideanSpace K n?

  /-- Constant vector with all elements equial to `k`. -/
  const (k : K) : X
  const_spec (k : K) : vequiv (const k) = fun _ => k

  /-- Scalar multiplication.

  `x` should be modified if it is passed with ref counter one. -/
  scal  (alpha : K) (x : X) : X
  scal_spec (alpha : K) (x : X) :
    vequiv (scal alpha x) = alpha • vequiv x

  /-- Scalar multiplication and scalar addition

  `x` should be modified if it is passed with ref counter one. -/
  scalAdd  (alpha beta : K) (x : X) : X
  scalAdd_spec (alpha : K) (x : X) :
    vequiv (scal alpha x) = fun i => alpha * vequiv x i + beta

  /-- `sum x = ∑ i, x[i]` -/
  sum (x : X) : K
  sum_spec (x : X) : sum x = Finset.univ.sum (fun i : n => vequiv x i)

  /-- `asum x = ∑ i, |x[i]|` -/
  asum (x : X) : R
  asum_spec (x : X) : asum x = Scalar.ofReal (K:=K) ‖(WithLp.equiv 1 (n → K)).symm (vequiv x)‖

  /-- `nrm2 x = √∑ i, |x[i]|²` -/
  nrm2 (x : X) : R
  nrm2_spec (x : X) : nrm2 x = Scalar.ofReal (K:=K) ‖(WithLp.equiv 2 (n → K)).symm (vequiv x)‖

  /-- `iamax x = argmaxᵢ |x[i]|` -/
  iamax (x : X) : n
  iamax_spec (x : X) : Scalar.abs (vequiv x (iamax x)) = Scalar.ofReal (K:=K) ‖vequiv x‖

  /-- `imaxRe x = argmaxᵢ (real x[i])` -/
  imaxRe (x : X) (h : 0 < size n) : n
  imaxRe_spec (x : X) (h : 0 < size n) :
    Scalar.toReal R (Scalar.real (vequiv x (imaxRe x h)))
    =
    iSup (α:=ℝ) (fun i => Scalar.toReal R <| Scalar.real (K:=K) (vequiv x i))

  /-- `iminRe x = argmaxᵢ (re x[i])` -/
  iminRe (x : X) (h : 0 < size n) : n
  iminRe_spec (x : X) (h : 0 < size n) :
    Scalar.toReal R (Scalar.real (vequiv x (iminRe x h)))
    =
    iInf (α:=ℝ) (fun i => Scalar.toReal R <| Scalar.real (K:=K) (vequiv x i))

  /-- `dot x y = ∑ i, conj x[i] y[i]` -/
  dot (x y : X) : K

  dot_spec (x y : X) :
    (dot x y) =
    let x' := (WithLp.equiv 2 (n → K)).symm (vequiv x)
    let y' := (WithLp.equiv 2 (n → K)).symm (vequiv y)
    (⟪x',y'⟫_K)

  /-- `axpy a x y = a • x + y`

  `y` should be modified if it is passed with ref counter one. -/
  axpy (alpha : K) (x y : X) : X

  axpy_spec (alpha : K) (x y : X) :
    vequiv (axpy alpha x y) = alpha • vequiv x + vequiv y

  /-- `axpby a b x y = a • x + b • y`

  `y` should be modified if it is passed with ref counter one. -/
  axpby (alpha beta : K) (x y : X) : X := axpy alpha x (scal beta y)

  axpby_spec (alpha beta : K) (x y : X) :
    vequiv (axpby alpha beta x y) = alpha • vequiv x + beta • vequiv y

  /-  Element wise operations -/

  /-- Element wise multiplication.

  `x` should be modified if it is passed with ref counter one. -/
  mul (x y : X) : X
  mul_spec (x y : X) :
    vequiv (mul x y) = vequiv x * vequiv y

  /-- Element wise division.

  `x` should be modified if it is passed with ref counter one. -/
  div (x y : X) : X
  div_spec (x y : X) :
    vequiv (div x y) = vequiv x / vequiv y

  /-- Element wise inverse.

  `x` should be modified if it is passed with ref counter one. -/
  inv (x : X) : X
  inv_spec (x : X) :
    vequiv (inv x) = fun i => (vequiv x i)⁻¹

  /-- Element wise exponentiation.

  `x` should be modified if it is passed with ref counter one. -/
  exp (x : X) : X
  exp_spec (x : X) :
    vequiv (exp x) = fun i => Scalar.exp (vequiv x i)

  -- /-- Element wise logarithm. -/
  -- log {n} [IndexType n] (x : X) : X
  -- log_spec {n} [IndexType n] (x : X) :
  --   vequiv (log x) = fun i => Scalar.log (vequiv x i)

  -- /-- Element wise square root. -/
  -- sqrt {n} [IndexType n] (x : X) : X
  -- sqrt_spec {n} [IndexType n] (x : X) :
  --   vequiv (sqrt x) = fun i => Scalar.sqrt (vequiv x i)

  -- /-- Element wise sine. -/
  -- sin {n} [IndexType n] (x : X) : X
  -- sin_spec {n} [IndexType n] (x : X) :
  --   vequiv (sin x) = fun i => Scalar.sin (vequiv x i)

  -- /-- Element wise cosine. -/
  -- cos {n} [IndexType n] (x : X) : X
  -- cos_spec {n} [IndexType n] (x : X) :
  --   vequiv (cos x) = fun i => Scalar.cos (vequiv x i)

  -- /-- Element wise tangent. -/
  -- tan {n} [IndexType n] (x : X) : X
  -- tan_spec {n} [IndexType n] (x : X) :
  --   vequiv (tan x) = fun i => Scalar.tan (vequiv x i)

  -- /-- Element wise hyperbolic sine. -/
  -- sinh {n} [IndexType n] (x : X) : X
  -- sinh_spec {n} [IndexType n] (x : X) :
  --   vequiv (sinh x) = fun i => Scalar.sinh (vequiv x i)

  -- /-- Element wise hyperbolic cosine. -/
  -- cosh {n} [IndexType n] (x : X) : X
  -- cosh_spec {n} [IndexType n] (x : X) :
  --   vequiv (cosh x) = fun i => Scalar.cosh (vequiv x i)

  -- /-- Element wise hyperbolic tangent. -/
  -- tanh {n} [IndexType n] (x : X) : X
  -- tanh_spec {n} [IndexType n] (x : X) :
  --   vequiv (tanh x) = fun i => Scalar.tanh (vequiv x i)

  -- /-- Element wise inverse sine. -/
  -- asin {n} [IndexType n] (x : X) : X
  -- asin_spec {n} [IndexType n] (x : X) :
  --   vequiv (asin x) = fun i => Scalar.asin (vequiv x i)

  -- /-- Element wise inverse cosine. -/
  -- acos {n} [IndexType n] (x : X) : X
  -- acos_spec {n} [IndexType n] (x : X) :
  --   vequiv (acos x) = fun i => Scalar.acos (vequiv x i)

  -- /-- Element wise inverse tangent. -/
  -- atan {n} [IndexType n] (x : X) : X
  -- atan_spec {n} [IndexType n] (x : X) :
  --   vequiv (atan x) = fun i => Scalar.atan (vequiv x i)

  -- /-- Element wise inverse tangent of `y/x`. -/
  -- atan2 {n} [IndexType n] (y x : X) : X
  -- atan2_spec {n} [IndexType n] (y x : X) :
  --   vequiv (atan2 y x) = fun i => Scalar.atan2 (vequiv y i) (vequiv x i)

  -- /-- Element wise inverse hyperbolic sine. -/
  -- asinh {n} [IndexType n] (x : X) : X
  -- asinh_spec {n} [IndexType n] (x : X) :
  --   vequiv (asinh x) = fun i => Scalar.asinh (vequiv x i)

  -- /-- Element wise inverse hyperbolic cosine. -/
  -- acosh {n} [IndexType n] (x : X) : X
  -- acosh_spec {n} [IndexType n] (x : X) :
  --   vequiv (acosh x) = fun i => Scalar.acosh (vequiv x i)

  -- /-- Element wise inverse hyperbolic tangent. -/
  -- atanh {n} [IndexType n] (x : X) : X
  -- atanh_spec {n} [IndexType n] (x : X) :
  --   vequiv (atanh x) = fun i => Scalar.atanh (vequiv x i)

  -- /-- Element wise power. -/
  -- pow {n} [IndexType n] (x : X) (n : ℕ) : X
  -- pow_spec {n} [IndexType n] (x : X) (n : ℕ) :
  --   vequiv (pow X) = fun i => Scalar.pow (vequiv x i) n

  -- /-- Element wise square. -/
  -- sqr {n} [IndexType n] (x : X) : X
  -- sqr_spec {n} [IndexType n] (x : X) :
  --   vequiv (sqr x) = fun i => Scalar.sqr (vequiv x i)

  -- /-- Element wise cube. -/
  -- cube {n} [IndexType n] (x : X) : X
  -- cube_spec {n} [IndexType n] (x : X) :
  --   vequiv (cube x) = fun i => Scalar.cube (vequiv x i)

  -- /-- Element wise sign. -/
  -- sign {n} [IndexType n] (x : X) : X
  -- sign_spec {n} [IndexType n] (x : X) :
  --   vequiv (sign x) = fun i => Scalar.sign (vequiv x i)

namespace VectorType

export VectorType.Base
  (vequiv const const_spec scal scal_spec scalAdd scalAdd_spec sum sum_spec asum asum_spec nrm2 nrm2_spec
   iamax iamax_spec imaxRe imaxRe_spec iminRe iminRe_spec dot dot_spec axpy axpy_spec axpby axpby_spec
   mul mul_spec div div_spec inv inv_spec exp exp_spec)

attribute [vector_to_spec,vector_from_spec ←]
  const_spec
  scal_spec
  sum_spec
  asum_spec
  nrm2_spec
  iamax_spec
  dot_spec
  axpy_spec
  axpby_spec

section BasicOperations

variable
  {X : Type*} {n : Type u} {R K :  Type*}
  [Scalar R R] [Scalar R K] [IndexType n] [VectorType.Base X n K]

open VectorType

instance : Add X := ⟨fun x y => axpy 1 x y⟩
instance : Sub X := ⟨fun x y => axpby 1 (-1) x y⟩
instance : Neg X := ⟨fun x => scal (-1) x⟩
instance : SMul K X := ⟨fun s x => scal s x⟩

instance : Zero X := ⟨const 0⟩

instance : Inner K X := ⟨fun x y => dot x y⟩
instance : Norm X := ⟨fun x => Scalar.toReal (K:=K) (nrm2 x)⟩
instance : Dist X := ⟨fun x y => ‖x-y‖⟩

@[vector_to_spec, vector_from_spec ←]
theorem add_spec (x y : X) : vequiv (x + y) = vequiv x + vequiv y := by
  simp only [HAdd.hAdd, Add.add, axpy_spec, Pi.smul_apply, smul_eq_mul, one_mul]

@[vector_to_spec, vector_from_spec ←]
theorem sub_spec (x y : X) : vequiv (x - y) = vequiv x - vequiv y := by
  conv => lhs; simp only [HSub.hSub,Sub.sub,axpby_spec]
  simp only [one_smul, neg_smul, sub_eq_add_neg]

@[vector_to_spec, vector_from_spec ←]
theorem neg_spec (x : X) : vequiv (- x) = - vequiv x := by
  simp only [Neg.neg, scal_spec, neg_smul, Pi.smul_apply, smul_eq_mul, one_mul]

@[vector_to_spec, vector_from_spec ←]
theorem smul_spec (k : K) (x : X) : vequiv (k • x) = k • vequiv x := by
  conv => lhs; simp only [HSMul.hSMul, SMul.smul,scal_spec]
  funext i; simp only [Pi.smul_apply, smul_eq_mul]

@[vector_to_spec, vector_from_spec ←]
theorem zero_spec : vequiv (0 : X) = 0 := by
  conv => lhs; simp only [Zero.zero,OfNat.ofNat,const_spec]
  rfl

@[vector_to_spec, vector_from_spec ←]
theorem inner_spec (x y : X) :
    ⟪x,y⟫_K
    =
    ⟪(WithLp.equiv 2 (n → K)).symm (vequiv x), (WithLp.equiv 2 (n → K)).symm (vequiv y)⟫_K := by
  simp only [inner, dot_spec, WithLp.equiv_symm_pi_apply]

@[vector_to_spec, vector_from_spec ←]
theorem norm_spec (x : X) :
    ‖x‖
    =
    ‖(WithLp.equiv 2 (n → K)).symm (vequiv x)‖ := by
  conv => lhs; simp only [norm]; simp only [nrm2_spec]
  simp only [Scalar.toReal_ofReal]

@[vector_to_spec, vector_from_spec ←]
theorem dist_spec (x y : X) :
    dist x y
    =
    dist ((WithLp.equiv 2 (n → K)).symm (vequiv x)) ((WithLp.equiv 2 (n → K)).symm (vequiv y)) := by
  conv => lhs; simp [Dist.dist,vector_to_spec]
  conv => rhs; rw[NormedAddCommGroup.dist_eq]

end BasicOperations


section AlgebraicInstances

variable
  {X : Type*} {n : Type u} {R K :  Type*}
  [Scalar R R] [Scalar R K] [IndexType n] [VectorType.Base X n K]

open VectorType

instance : AddCommGroup X where
  add_assoc := by intros; apply vequiv.injective; simp only [add_spec, add_assoc]
  zero_add := by intros; apply vequiv.injective; simp only [add_spec, zero_spec, zero_add]
  add_zero := by intros; apply vequiv.injective; simp only [add_spec, zero_spec, add_zero]
  neg_add_cancel := by intros; apply vequiv.injective; simp only [add_spec, neg_spec, neg_add_cancel, zero_spec]
  add_comm := by intros; apply vequiv.injective; simp only [add_spec, add_comm]
  sub_eq_add_neg := by intros; apply vequiv.injective; simp only [sub_spec, sub_eq_add_neg, add_spec, neg_spec]
  nsmul n x := scal (n:K) x
  nsmul_zero := by intros; apply vequiv.injective; simp only [CharP.cast_eq_zero, scal_spec, zero_smul, zero_spec]
  nsmul_succ := by intros; apply vequiv.injective; simp only [Nat.cast_add, Nat.cast_one, scal_spec, add_smul, one_smul, add_spec]
  zsmul n x := scal (n:K) x
  zsmul_zero' := by intros; apply vequiv.injective; simp[scal_spec,vector_to_spec]
  zsmul_neg' := by intros; apply vequiv.injective; simp[zsmul_neg',scal_spec,add_smul,vector_to_spec]
  zsmul_succ' := by intros; apply vequiv.injective; simp[scal_spec,add_smul,vector_to_spec]

instance : Module K X where
  one_smul := by intros; apply vequiv.injective; simp[vector_to_spec]
  mul_smul := by intros; apply vequiv.injective; simp[mul_smul,vector_to_spec]
  smul_zero := by intros; apply vequiv.injective; simp[vector_to_spec]
  smul_add := by intros; apply vequiv.injective; simp[vector_to_spec]
  add_smul := by intros; apply vequiv.injective; simp[add_smul,vector_to_spec]
  zero_smul := by intros; apply vequiv.injective; simp[vector_to_spec]

instance : PseudoMetricSpace X where
  dist_self := by intros; simp[dist_spec]
  dist_comm := by intros; simp[dist_spec,dist_comm]
  dist_triangle := by intros; simp[dist_spec,dist_triangle]

instance : NormedAddCommGroup X where
  dist_eq := by intros; rfl
  eq_of_dist_eq_zero := by
    intro x y h;
    apply vequiv.injective;
    apply (WithLp.equiv 2 (n → K)).symm.injective
    simp only [dist_spec] at h
    exact (eq_of_dist_eq_zero h)

instance : NormedSpace K X where
  norm_smul_le := by
    simp only [norm_spec]
    simp [norm_smul_le,vector_to_spec]

instance : InnerProductSpace K X where
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

instance : AdjointSpace K X where
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


/-- Linear vequivalence between vector type `X` and `n → K` -/
def vequivₗ : X ≃ₗ[K] (n → K) :=
  LinearEquiv.mk ⟨⟨vequiv,by simp[vector_to_spec]⟩,by simp[vector_to_spec]⟩
    vequiv.symm (vequiv.left_inv) (vequiv.right_inv)


/-- Continuous linear vequivalence between vector type `X` and `n → K` -/
def vequivL : X ≃L[K] (n → K) := ContinuousLinearEquiv.mk vequivₗ (by sorry_proof) (by sorry_proof)


instance : FiniteDimensional K X :=
   FiniteDimensional.of_injective (V₂:=n→K) (vequivₗ (X:=X) (n:=n) (K:=K)).1
  (vequivₗ.left_inv.injective)


variable (X)
noncomputable
def basis : Basis n K X := Basis.ofEquivFun (ι:=n) (R:=K) (M:=X) vequivₗ
variable {X}


@[simp, simp_core]
theorem finrank_eq_index_card : Module.finrank K X = Fintype.card n :=
  Module.finrank_eq_card_basis (basis X)


end AlgebraicInstances
