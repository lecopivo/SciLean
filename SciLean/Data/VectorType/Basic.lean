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

structure IndexEquiv (I J : Type*) [IndexType I] [IndexType J] extends Equiv I J where
  protected size_eq : size I = size J
  protected toFin_toFun  : ∀ i : I, IndexType.toFin (toFun i) = (size_eq ▸ IndexType.toFin i)
  protected toFin_invFun : ∀ j : J, IndexType.toFin (invFun j) = (size_eq ▸ IndexType.toFin j)

class VectorType.Base (X : (n : Type*) → [IndexType n] → Type*) {R : outParam (Type*)} (K : outParam (Type*))
        [Scalar R K] where


/-- `VectorType X n K` says that `X` behaves like a vector indexed by `n` and with values in `K`.

Providing an instance of `VectorType X n K` will automatically provide the following instances
  - `Add X`, `Sub X`, `Neg X`, `SMul K X`, `Zero X`, `Inner K X`, ...
  - `NormedAddCommGroup X` with l₂ norm
  - `InnerProductSpace K X`
  - `AdjointSpace K X`
  - `FiniteDimensional K X`

This class is designed to provide Basic Linear Algebra Subprograms(BLAS) which allows us to define
vector space structure on `X` that is computationally efficient.
 -/
class VectorType (X : (n : Type*) → [IndexType n] → Type*) {R : outParam (Type*)} (K : outParam (Type*))
        [Scalar R K] where

  equiv {n} [IndexType n] : X n ≃ (n → K) -- maybe EuclideanSpace K n?

  /-- Constant vector with all elements equial to `k`. -/
  const (n) [IndexType n] (k : K) : X n
  const_spec {n} [IndexType n] (k : K) : equiv (const n k) = fun _ => k

  /-- Scalar multiplication. -/
  scal {n} [IndexType n]  (alpha : K) (x : X n) : X n
  scal_spec {n} [IndexType n] (alpha : K) (x : X n) :
    equiv (scal alpha x) = alpha • equiv x

  /-- Scalar multiplication and scalar addition -/
  scalAdd {n} [IndexType n]  (alpha beta : K) (x : X n) : X n
  scalAdd_spec {n} [IndexType n] (alpha : K) (x : X n) :
    equiv (scal alpha x) = fun i => alpha * equiv x i + beta

  /-- `sum x = ∑ i, x[i]` -/
  sum {n} [IndexType n] (x : X n) : K
  sum_spec {n} [IndexType n] (x : X n) : sum x = Finset.univ.sum (fun i => equiv x i)

  /-- `asum x = ∑ i, |x[i]|` -/
  asum {n} [IndexType n] (x : X n) : R
  asum_spec {n} [IndexType n] (x : X n) : asum x = Scalar.ofReal (K:=K) ‖(WithLp.equiv 1 (n → K)).symm (equiv x)‖

  /-- `nrm2 x = √∑ i, |x[i]|²` -/
  nrm2 {n} [IndexType n] (x : X n) : R
  nrm2_spec {n} [IndexType n] (x : X n) : nrm2 x = Scalar.ofReal (K:=K) ‖(WithLp.equiv 2 (n → K)).symm (equiv x)‖

  /-- `iamax x = argmaxᵢ |x[i]|` -/
  iamax {n} [IndexType n] (x : X n) : n
  iamax_spec {n} [IndexType n] (x : X n) : Scalar.abs (equiv x (iamax x)) = Scalar.ofReal (K:=K) ‖equiv x‖

  -- /-- `imax x = argmaxᵢ x[i]` -/
  -- imaxRe {n} [IndexType n] (x : X n) : n
  -- imaxRe_spec {n} [IndexType n] (x : X n) : Scalar.real (equiv x (imaxRe x)) = iSup (fun i => Scalar.real (K:=K) (equiv x))

  -- /-- `imax x = argmaxᵢ x[i]` -/
  -- imin {n} [IndexType n] (x : X n) : n
  -- imin_spec {n} [IndexType n] (x : X n) : (equiv x (imin x)) = Scalar.ofReal (K:=K) ‖equiv x‖

  /-- `dot x y = ∑ i, conj x[i] y[i]` -/
  dot {n} [IndexType n] (x y : X n) : K

  dot_spec {n} [IndexType n] (x y : X n) :
    (dot x y) =
    let x' := (WithLp.equiv 2 (n → K)).symm (equiv x)
    let y' := (WithLp.equiv 2 (n → K)).symm (equiv y)
    (⟪x',y'⟫_K)

  /-- `axpy a x y = a • x + y` -/
  axpy {n} [IndexType n] (alpha : K) (x y : X n) : X n

  axpy_spec {n} [IndexType n] (alpha : K) (x y : X n) :
    equiv (axpy alpha x y) = alpha • equiv x + equiv y

  /-- `axpby a b x y = a • x + b • y` -/
  axpby {n} [IndexType n] (alpha beta : K) (x y : X n) : X n := axpy alpha x (scal beta y)

  axpby_spec {n} [IndexType n] (alpha beta : K) (x y : X n) :
    equiv (axpby alpha beta x y) = alpha • equiv x + beta • equiv y

  /-  Element wise operations -/

  /-- Element wise multiplication. -/
  mul {n} [IndexType n] (x y : X n) : X n
  mul_spec {n} [IndexType n] (x y : X n) :
    equiv (mul x y) = equiv x * equiv y

  /-- Element wise division. -/
  div {n} [IndexType n] (x y : X n) : X n
  div_spec {n} [IndexType n] (x y : X n) :
    equiv (div x y) = equiv x / equiv y

  /-- Element wise inverse. -/
  inv {n} [IndexType n] (x : X n) : X n
  inv_spec {n} [IndexType n] (x : X n) :
    equiv (inv x) = fun i => (equiv x i)⁻¹

  /-- Element wise exponentiation. -/
  exp {n} [IndexType n] (x : X n) : X n
  exp_spec {n} [IndexType n] (x : X n) :
    equiv (exp x) = fun i => Scalar.exp (equiv x i)

  -- /-- Element wise logarithm. -/
  -- log {n} [IndexType n] (x : X n) : X n
  -- log_spec {n} [IndexType n] (x : X n) :
  --   equiv (log x) = fun i => Scalar.log (equiv x i)

  -- /-- Element wise square root. -/
  -- sqrt {n} [IndexType n] (x : X n) : X n
  -- sqrt_spec {n} [IndexType n] (x : X n) :
  --   equiv (sqrt x) = fun i => Scalar.sqrt (equiv x i)

  -- /-- Element wise sine. -/
  -- sin {n} [IndexType n] (x : X n) : X n
  -- sin_spec {n} [IndexType n] (x : X n) :
  --   equiv (sin x) = fun i => Scalar.sin (equiv x i)

  -- /-- Element wise cosine. -/
  -- cos {n} [IndexType n] (x : X n) : X n
  -- cos_spec {n} [IndexType n] (x : X n) :
  --   equiv (cos x) = fun i => Scalar.cos (equiv x i)

  -- /-- Element wise tangent. -/
  -- tan {n} [IndexType n] (x : X n) : X n
  -- tan_spec {n} [IndexType n] (x : X n) :
  --   equiv (tan x) = fun i => Scalar.tan (equiv x i)

  -- /-- Element wise hyperbolic sine. -/
  -- sinh {n} [IndexType n] (x : X n) : X n
  -- sinh_spec {n} [IndexType n] (x : X n) :
  --   equiv (sinh x) = fun i => Scalar.sinh (equiv x i)

  -- /-- Element wise hyperbolic cosine. -/
  -- cosh {n} [IndexType n] (x : X n) : X n
  -- cosh_spec {n} [IndexType n] (x : X n) :
  --   equiv (cosh x) = fun i => Scalar.cosh (equiv x i)

  -- /-- Element wise hyperbolic tangent. -/
  -- tanh {n} [IndexType n] (x : X n) : X n
  -- tanh_spec {n} [IndexType n] (x : X n) :
  --   equiv (tanh x) = fun i => Scalar.tanh (equiv x i)

  -- /-- Element wise inverse sine. -/
  -- asin {n} [IndexType n] (x : X n) : X n
  -- asin_spec {n} [IndexType n] (x : X n) :
  --   equiv (asin x) = fun i => Scalar.asin (equiv x i)

  -- /-- Element wise inverse cosine. -/
  -- acos {n} [IndexType n] (x : X n) : X n
  -- acos_spec {n} [IndexType n] (x : X n) :
  --   equiv (acos x) = fun i => Scalar.acos (equiv x i)

  -- /-- Element wise inverse tangent. -/
  -- atan {n} [IndexType n] (x : X n) : X n
  -- atan_spec {n} [IndexType n] (x : X n) :
  --   equiv (atan x) = fun i => Scalar.atan (equiv x i)

  -- /-- Element wise inverse tangent of `y/x`. -/
  -- atan2 {n} [IndexType n] (y x : X n) : X n
  -- atan2_spec {n} [IndexType n] (y x : X n) :
  --   equiv (atan2 y x) = fun i => Scalar.atan2 (equiv y i) (equiv x i)

  -- /-- Element wise inverse hyperbolic sine. -/
  -- asinh {n} [IndexType n] (x : X n) : X n
  -- asinh_spec {n} [IndexType n] (x : X n) :
  --   equiv (asinh x) = fun i => Scalar.asinh (equiv x i)

  -- /-- Element wise inverse hyperbolic cosine. -/
  -- acosh {n} [IndexType n] (x : X n) : X n
  -- acosh_spec {n} [IndexType n] (x : X n) :
  --   equiv (acosh x) = fun i => Scalar.acosh (equiv x i)

  -- /-- Element wise inverse hyperbolic tangent. -/
  -- atanh {n} [IndexType n] (x : X n) : X n
  -- atanh_spec {n} [IndexType n] (x : X n) :
  --   equiv (atanh x) = fun i => Scalar.atanh (equiv x i)

  -- /-- Element wise power. -/
  -- pow {n} [IndexType n] (x : X n) (n : ℕ) : X n
  -- pow_spec {n} [IndexType n] (x : X n) (n : ℕ) :
  --   equiv (pow x n) = fun i => Scalar.pow (equiv x i) n

  -- /-- Element wise square. -/
  -- sqr {n} [IndexType n] (x : X n) : X n
  -- sqr_spec {n} [IndexType n] (x : X n) :
  --   equiv (sqr x) = fun i => Scalar.sqr (equiv x i)

  -- /-- Element wise cube. -/
  -- cube {n} [IndexType n] (x : X n) : X n
  -- cube_spec {n} [IndexType n] (x : X n) :
  --   equiv (cube x) = fun i => Scalar.cube (equiv x i)

  -- /-- Element wise sign. -/
  -- sign {n} [IndexType n] (x : X n) : X n
  -- sign_spec {n} [IndexType n] (x : X n) :
  --   equiv (sign x) = fun i => Scalar.sign (equiv x i)



namespace VectorType

attribute [vector_to_spec]
  const_spec
  scal_spec
  sum_spec
  asum_spec
  nrm2_spec
  iamax_spec
  dot_spec
  axpy_spec
  axpby_spec

attribute [vector_from_spec ←]
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
  {X : (n : Type u) → [IndexType n] → Type*} {n : Type u} {R K :  Type*}
  [Scalar R K] [IndexType n] [VectorType X K]

open VectorType

instance : Add (X n) := ⟨fun x y => axpy 1 x y⟩
instance : Sub (X n) := ⟨fun x y => axpby 1 (-1) x y⟩
instance : Neg (X n) := ⟨fun x => scal (-1) x⟩
instance : SMul K (X n) := ⟨fun s x => scal s x⟩

instance : Zero (X n) := ⟨const n 0⟩

instance : Inner K (X n) := ⟨fun x y => dot x y⟩
instance : Norm (X n) := ⟨fun x => Scalar.toReal (K:=K) (nrm2 x)⟩
instance : Dist (X n) := ⟨fun x y => ‖x-y‖⟩

@[vector_to_spec, vector_from_spec ←]
theorem add_spec (x y : X n) : equiv (x + y) = equiv x + equiv y := by
  simp only [HAdd.hAdd, Add.add, axpy_spec, Pi.smul_apply, smul_eq_mul, one_mul]

@[vector_to_spec, vector_from_spec ←]
theorem sub_spec (x y : X n) : equiv (x - y) = equiv x - equiv y := by
  conv => lhs; simp only [HSub.hSub,Sub.sub,axpby_spec]
  simp only [one_smul, neg_smul, sub_eq_add_neg]

@[vector_to_spec, vector_from_spec ←]
theorem neg_spec (x : X n) : equiv (- x) = - equiv x := by
  simp only [Neg.neg, scal_spec, neg_smul, Pi.smul_apply, smul_eq_mul, one_mul]

@[vector_to_spec, vector_from_spec ←]
theorem smul_spec (k : K) (x : X n) : equiv (k • x) = k • equiv x := by
  conv => lhs; simp only [HSMul.hSMul, SMul.smul,scal_spec]
  funext i; simp only [Pi.smul_apply, smul_eq_mul]

@[vector_to_spec, vector_from_spec ←]
theorem zero_spec : equiv (0 : X n) = 0 := by
  conv => lhs; simp only [Zero.zero,OfNat.ofNat,const_spec]
  rfl

@[vector_to_spec, vector_from_spec ←]
theorem inner_spec (x y : X n) :
    ⟪x,y⟫_K
    =
    ⟪(WithLp.equiv 2 (n → K)).symm (equiv x), (WithLp.equiv 2 (n → K)).symm (equiv y)⟫_K := by
  simp only [inner, dot_spec, WithLp.equiv_symm_pi_apply]

@[vector_to_spec, vector_from_spec ←]
theorem norm_spec (x : X n) :
    ‖x‖
    =
    ‖(WithLp.equiv 2 (n → K)).symm (equiv x)‖ := by
  conv => lhs; simp only [norm]; simp only [nrm2_spec]
  simp only [Scalar.toReal_ofReal]

@[vector_to_spec, vector_from_spec ←]
theorem dist_spec (x y : X n) :
    dist x y
    =
    dist ((WithLp.equiv 2 (n → K)).symm (equiv x)) ((WithLp.equiv 2 (n → K)).symm (equiv y)) := by
  conv => lhs; simp [Dist.dist,vector_to_spec]
  conv => rhs; rw[NormedAddCommGroup.dist_eq]

end BasicOperations


section AlgebraicInstances

variable
  {X : (n : Type u) → [IndexType n] → Type*} {n : Type u} {R K :  Type*}
  [Scalar R K] [IndexType n] [VectorType X K]

open VectorType

instance : AddCommGroup (X n) where
  add_assoc := by intros; apply equiv.injective; simp only [add_spec, add_assoc]
  zero_add := by intros; apply equiv.injective; simp only [add_spec, zero_spec, zero_add]
  add_zero := by intros; apply equiv.injective; simp only [add_spec, zero_spec, add_zero]
  neg_add_cancel := by intros; apply equiv.injective; simp only [add_spec, neg_spec, neg_add_cancel, zero_spec]
  add_comm := by intros; apply equiv.injective; simp only [add_spec, add_comm]
  sub_eq_add_neg := by intros; apply equiv.injective; simp only [sub_spec, sub_eq_add_neg, add_spec, neg_spec]
  nsmul n x := scal (n:K) x
  nsmul_zero := by intros; apply equiv.injective; simp only [CharP.cast_eq_zero, scal_spec, zero_smul, zero_spec]
  nsmul_succ := by intros; apply equiv.injective; simp only [Nat.cast_add, Nat.cast_one, scal_spec, add_smul, one_smul, add_spec]
  zsmul n x := scal (n:K) x
  zsmul_zero' := by intros; apply equiv.injective; simp[scal_spec,vector_to_spec]
  zsmul_neg' := by intros; apply equiv.injective; simp[zsmul_neg',scal_spec,add_smul,vector_to_spec]
  zsmul_succ' := by intros; apply equiv.injective; simp[scal_spec,add_smul,vector_to_spec]

instance : Module K (X n) where
  one_smul := by intros; apply equiv.injective; simp[vector_to_spec]
  mul_smul := by intros; apply equiv.injective; simp[mul_smul,vector_to_spec]
  smul_zero := by intros; apply equiv.injective; simp[vector_to_spec]
  smul_add := by intros; apply equiv.injective; simp[vector_to_spec]
  add_smul := by intros; apply equiv.injective; simp[add_smul,vector_to_spec]
  zero_smul := by intros; apply equiv.injective; simp[vector_to_spec]

instance : PseudoMetricSpace (X n) where
  dist_self := by intros; simp[dist_spec]
  dist_comm := by intros; simp[dist_spec,dist_comm]
  dist_triangle := by intros; simp[dist_spec,dist_triangle]

instance : NormedAddCommGroup (X n) where
  dist_eq := by intros; rfl
  eq_of_dist_eq_zero := by
    intro x y h;
    apply equiv.injective;
    apply (WithLp.equiv 2 (n → K)).symm.injective
    simp only [dist_spec] at h
    exact (eq_of_dist_eq_zero h)

instance : NormedSpace K (X n) where
  norm_smul_le := by
    simp only [norm_spec]
    simp [norm_smul_le,vector_to_spec]

instance : InnerProductSpace K (X n) where
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

instance : AdjointSpace K (X n) where
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


/-- Linear equivalence between vector type `X` and `n → K` -/
def equivₗ : (X n) ≃ₗ[K] (n → K) :=
  LinearEquiv.mk ⟨⟨equiv,by simp[vector_to_spec]⟩,by simp[vector_to_spec]⟩
    equiv.symm (equiv.left_inv) (equiv.right_inv)


/-- Continuous linear equivalence between vector type `X` and `n → K` -/
def equivL : (X n) ≃L[K] (n → K) := ContinuousLinearEquiv.mk equivₗ (by sorry_proof) (by sorry_proof)


instance : FiniteDimensional K (X n) :=
   FiniteDimensional.of_injective (V₂:=n→K) (equivₗ (X:=X) (n:=n) (K:=K)).1
  (equivₗ.left_inv.injective)


variable (X)
noncomputable
def basis : Basis n K (X n) := Basis.ofEquivFun (ι:=n) (R:=K) (M:=X n) equivₗ
variable {X}


@[simp, simp_core]
theorem finrank_eq_index_card : Module.finrank K (X n) = Fintype.card n :=
  Module.finrank_eq_card_basis (basis X)


end AlgebraicInstances
