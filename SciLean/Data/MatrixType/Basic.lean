import SciLean.Data.MatrixType.Init
import SciLean.Data.MatrixType.Base
import SciLean.Data.MatrixType.Square
import SciLean.Data.MatrixType.Transpose
import SciLean.Data.MatrixType.MatMul

namespace SciLean

open Matrix VectorType

/-- `DenseMatrixType M X Y` says that `M` is a matrix transforming vectors of type `X` to vectors
of type `Y`.

This class provides functionality implementable using BLAS. -/
class DenseMatrixType
      (M : (m : Type u) → (n : Type u) → [IndexType m] → [IndexType n] → Type*)
      (V : outParam ((m : Type u) → [IndexType m] → Type*))
      {R : outParam (Type*)} {K : outParam (Type*)}
      [RealScalar R] [Scalar R K] [VectorType V K]
  where

  mequiv {m n} [IndexType m] [IndexType n] : M m n ≃ Matrix m n K

  /-- Flatten matrix into vector -/
  flatten {m n} [IndexType m] [IndexType n] : M m n ≃ V (m × n)

  -- This forces column majo order which is not desirable
  -- flatten_spec {m n} [IndexType m] [IndexType n] (A : M m n) :
  --   equiv (flatten A) = fun (i,j) => mequiv A i j

  /-- Transpose matrix -/
  transpose  {m n} [IndexType m] [IndexType n] (A : M m n) : M n m

  transpose_spec  {m n} [IndexType m] [IndexType n] (alpha beta : K) (A : M m n) :
    mequiv (transpose A)
    =
    (mequiv A)ᵀ

  /-- Transpose matrix -/

  conjTranspose  {m n} [IndexType m] [IndexType n] (A : M m n) : M n m

  conjTranspose_spec  {m n} [IndexType m] [IndexType n] (alpha beta : K) (A : M m n) :
    mequiv (transpose A)
    =
    (mequiv A)ᴴ

  /-- Matrix trace, `trace A = ∑ i, A i i` -/
  trace    {n} [IndexType n] (A : M n n) : K

  trace_spec {n} [IndexType n] (A : M n n) :
    trace A = ∑ i, (mequiv A) i i


  /-    Level 1 like BLAS operations    -/

  /-- Constant matrix -/
  const (m n) [IndexType m] [IndexType n] (k : K) : M m n :=
    flatten.symm (VectorType.const (m×n) k)

  const_spec (m n) [IndexType m] [IndexType n] (k : K) :
    mequiv (const m n k) = fun _ _ => k

  /-- Scalar multiplication -/
  scal {m n} [IndexType m] [IndexType n] (alpha : K) (A : M m n) : M m n :=
    flatten.symm (VectorType.scal alpha (flatten A))

  scal_spec {m n} [IndexType m] [IndexType n] (alpha : K) (A : M m n) :
    mequiv (scal alpha A) = fun i j => alpha • (mequiv A) i j

  /-- Sum of element absolute values -/
  asum {m n} [IndexType m] [IndexType n] (A : M m n) : R :=
    VectorType.asum (flatten A)

  /-- Frobenious norm of a matrix -/
  nrm2 {m n} [IndexType m] [IndexType n] (A : M m n) : R :=
    VectorType.nrm2 (flatten A)

  /-- Index of element with largest absolute value of a matrix -/
  iamax {m n} [IndexType m] [IndexType n] (A : M m n) : m×n :=
    VectorType.iamax (flatten A)

  /-- Dot product of two matrices -/
  dot {m n} [IndexType m] [IndexType n] (A : M m n) (B : M m n) : K :=
    VectorType.dot (flatten A) (flatten B)

  /-- Sum of two matrices with scalar multiplication, `axpy a A B = a•A+B` -/
  axpy {m n} [IndexType m] [IndexType n] (alpha : K) (A B : M m n) : M m n :=
    flatten.symm (VectorType.axpy alpha (flatten A) (flatten B))

  axpy_spec {m n} [IndexType m] [IndexType n] (alpha : K) (A B : M m n) :
    mequiv (axpy alpha A B)
    =
    alpha • mequiv A + mequiv B

  /-- Sum of two matrices with scalar multiplication, `axpby a b A B = a•A+b•B` -/
  axpby {m n} [IndexType m] [IndexType n] (alpha beta : K) (A B : M m n) : M m n :=
    flatten.symm (VectorType.axpby alpha beta (flatten A) (flatten B))

  axpby_spec {m n} [IndexType m] [IndexType n] (alpha beta : K) (A B : M m n) :
    mequiv (axpby alpha beta A B)
    =
    alpha • mequiv A + beta • mequiv B


  /-- Turn vector into diagonal matrix -/
  diag {n} [IndexType n] (x : V n) : M n n

  diag_spec {n} [IndexType n] [DecidableEq n] (x : V n) :
    mequiv (diag x)
    =
    of fun i j => if i = j then equiv x i else 0

  /-- Extract diagonal of matrix -/
  diagonal {n} [IndexType n] (A : M n n) : V n
  diagonal_spec {n} [IndexType n] (A : M n n) :
    equiv (diagonal A) = fun i => (mequiv A) i i

  /-- Get row of matrix -/
  row {m n} [IndexType m] [IndexType n] (A : M m n) (i : m) : V n
  row_spec {m n} [IndexType m] [IndexType n] (A : M m n) (i : m) :
    equiv (row A i) = fun j => (mequiv A) i j

  /-- Sum rows of a matrix -/
  sumRows {m n} [IndexType m] [IndexType n] (A : M m n) : V m
  sumRows_spec {m n} [IndexType m] [IndexType n] (A : M m n):
    equiv (sumRows A) = fun i => Finset.univ.sum (fun j => (mequiv A) i j)

  /-- Get column of matrix -/
  col {m n} [IndexType m] [IndexType n] (A : M m n) (j : n) : V m
  col_spec {m n} [IndexType m] [IndexType n] (A : M m n) (j : n) :
    equiv (col A j) = fun i => (mequiv A) i j

  /-- Sum columns of a matrix -/
  sumCols {m n} [IndexType m] [IndexType n] (A : M m n) : V n
  sumCols_spec {m n} [IndexType m] [IndexType n] (A : M m n):
    equiv (sumCols A) = fun j => Finset.univ.sum (fun i => (mequiv A) i j)


  /- Level 2 like BLAS operations -/

  /-- Matrix vector multiplication.

  Implementable using BLAS `gemv`. -/
  vecmulAdd      {m n} [IndexType m] [IndexType n] (alpha beta : K) (A : M m n) (x : V n) (y : V m) : V m

  vecmulAdd_spec {m n} [IndexType m] [IndexType n] (alpha beta : K) (A : M m n) (x : V n) (y : V m) :
    equiv (vecmulAdd alpha beta A x y)
    =
    alpha • mequiv A *ᵥ equiv x + beta • equiv y

  /-- Transpose matrix vector multiplication.

  Implementable using BLAS `gemv`. -/
  vecmulTransAdd {m n} [IndexType m] [IndexType n] (alpha beta : K) (A : M m n) (x : V m) (y : V n) : V n

  vecmulTransAdd_spec {m n} [IndexType m] [IndexType n] (alpha beta : K) (A : M m n) (x : V m) (y : V n) :
    equiv (vecmulTransAdd alpha beta A x y)
    =
    alpha • (mequiv A)ᵀ *ᵥ equiv x + beta • equiv y


  /-- Conjugate transpose matrix vector multiplication.

  Implementable using BLAS `gemv`. -/
  vecmulConjTransAdd {m n} [IndexType m] [IndexType n] (alpha beta : K) (A : M m n) (x : V m) (y : V n) : V n

  vecmulConjTransAdd_spec {m n} [IndexType m] [IndexType n] (alpha beta : K) (A : M m n) (x : V m) (y : V n) :
    equiv (vecmulConjTransAdd alpha beta A x y)
    =
    alpha • (mequiv A)ᴴ *ᵥ equiv x + beta • equiv y


  /-- Add outer product of two vectors to a matrix

  Impementable using BLAS `ger`, `geru`, `gerc`. -/
  outerprodAdd  {m n} [IndexType m] [IndexType n] (alpha : K) (x : V m) (y : V n) (A : M m n) : M m n

  outerprodAdd_spec  {m n} [IndexType m] [IndexType n] (alpha : K) (x : V m) (y : V n) (A : M m n) :
    mequiv (outerprodAdd alpha x y A)
    =
    alpha • vecMulVec (equiv x) (star ∘ equiv y) + mequiv A


  /-- Add outer product of a vector to a matrix.

  Impementable using BLAS `her`, `hpr`, `syr`, `spr`. -/
  outerprodselfAdd  {n}[IndexType n] (alpha : K) (x : V n) (A : M n n) : M n n

  outerprodselfAdd_spec  {n}[IndexType n] (alpha : K) (x : V n) (A : M n n) :
    mequiv (outerprodselfAdd alpha x A)
    =
    alpha • vecMulVec (equiv x) (equiv x) + mequiv A


  /-- Add symmetric outer product of two vectors to a matrix.

  Impementable using BLAS `ger`, `geru`, `gerc`. -/
  outerprodsymmAdd  {m n} [IndexType m] [IndexType n] (alpha : K) (x y : V n) (A : M n n) : M n n

  outerprodsymmAdd_spec  {m n} [IndexType m] [IndexType n] (alpha : K) (x y : V n) (A : M n n) :
    mequiv (outerprodAdd alpha x y A)
    =
    alpha • vecMulVec (equiv x) (star ∘ equiv y) + vecMulVec (equiv y) (star ∘ equiv x) + mequiv A



  /-     Level 3 like BLAS operations     -/

  /-- Matrix matrix multiplication.

  Implementable using BLAS `gemm`. -/
  matmul {m n k} [IndexType m] [IndexType n] [IndexType k]
    (alpha beta : K) (A : M m n) (B : M n k) (C : M m k) : M m k

  matmul_spec {m n k} [IndexType m] [IndexType n] [IndexType k]
    (alpha beta : K) (A : M m n) (B : M n k) (C : M m k) :
    mequiv (matmul alpha beta A B C)
    =
    alpha • mequiv A * mequiv B + beta • mequiv C



namespace DenseMatrixType


attribute [matrix_to_spec] const_spec scal_spec trace_spec
  transpose_spec diag_spec diagonal_spec row_spec col_spec
  vecmulAdd_spec vecmulTransAdd_spec vecmulConjTransAdd_spec
  outerprodAdd_spec outerprodselfAdd_spec outerprodsymmAdd_spec
  matmul_spec axpy_spec axpby_spec

attribute [matrix_from_spec ←] const_spec scal_spec trace_spec
  transpose_spec diag_spec diagonal_spec row_spec col_spec
  vecmulAdd_spec vecmulTransAdd_spec vecmulConjTransAdd_spec
  outerprodAdd_spec outerprodselfAdd_spec outerprodsymmAdd_spec
  matmul_spec axpy_spec axpby_spec



section BasicOperations


variable
  {M V R K} [RealScalar R] [Scalar R K] [VectorType V K] [DenseMatrixType M V]
  {m n : Type u} [IndexType m] [IndexType n]

set_default_scalar K

open DenseMatrixType

instance : Add (M m n) := ⟨λ A B => axpby 1 1 A B⟩
instance : Sub (M m n) := ⟨λ A B => axpby 1 (-1) A B⟩
instance : Neg (M m n) := ⟨λ A => scal (-1) A⟩
instance : SMul K (M m n) := ⟨λ a A => scal a A⟩

instance : Zero (M m n) := ⟨const m n 0⟩

instance : Inner K (M m n) := ⟨dot⟩
instance : Norm (M n m) := ⟨fun A => Scalar.toReal R (nrm2 A)⟩
instance : Norm2 R (M n m) := ⟨nrm2⟩
instance : Dist (M n m) := ⟨fun A B => ‖A-B‖⟩


@[matrix_to_spec, matrix_from_spec ←]
theorem add_spec (A B : M m n) : mequiv (A + B) = mequiv A + mequiv B := by
  simp only [HAdd.hAdd, Add.add, axpby_spec, smul_apply, smul_eq_mul, one_mul]

@[matrix_to_spec, matrix_from_spec ←]
theorem sub_spec (A B : M m n) : mequiv (A - B) = mequiv A - mequiv B := by
  conv => lhs; simp  [HSub.hSub,Sub.sub,matrix_to_spec]
  simp only [sub_eq_add_neg]

@[matrix_to_spec, matrix_from_spec ←]
theorem neg_spec (A : M m n) : mequiv (-A) = -mequiv A := by
  simp  [Neg.neg,matrix_to_spec]

@[matrix_to_spec, matrix_from_spec ←]
theorem smul_spec (a : K) (A : M m n) : mequiv (a • A) = a • mequiv A := by
  conv => lhs; simp only [HSMul.hSMul,SMul.smul,matrix_to_spec]
  rfl

@[matrix_to_spec, matrix_from_spec ←]
theorem zero_spec : mequiv (0 : M m n) = 0 := by
  simp only [Zero.zero,OfNat.ofNat,const_spec]

-- @[matrix_to_spec, matrix_from_spec ←]
-- theorem inner_spec (A B : M m n) : ⟪A, B⟫ = ⟪(WithLp.equiv 2 (Matrix m n K)).symm (mequiv A), (WithLp.equiv 2 (Matrix m n K)).symm (equiv B)⟫ := by
--   simp only [inner, dot, matrix_to_spec]

-- @[matrix_to_spec, matrix_from_spec ←]
-- theorem norm_spec (A : M m n) : ‖A‖ = ‖mequiv A‖ := by
--   simp only [norm, Norm.norm, Scalar.toReal, nrm2, matrix_to_spec]

-- @[matrix_to_spec, matrix_from_spec ←]
-- theorem dist_spec (A B : M m n) : dist A B = ‖mequiv A - mequiv B‖ := by
--   simp only [dist, Norm.dist, norm, Norm.norm, Scalar.toReal, nrm2, matrix_to_spec]

end BasicOperations


section AlgebraicInstances


variable
  {M V R K} [RealScalar R] [Scalar R K] [VectorType V K] [DenseMatrixType M V]
  {m n : Type u} [IndexType m] [IndexType n]

open DenseMatrixType

instance : AddCommGroup (M m n) where
  add_assoc := by intros; apply mequiv.injective; simp only [add_spec, add_assoc]
  zero_add := by intros; apply mequiv.injective; simp only [add_spec, zero_spec, zero_add]
  add_zero := by intros; apply mequiv.injective; simp only [add_spec, zero_spec, add_zero]
  neg_add_cancel := by intros; apply mequiv.injective; simp only [add_spec, neg_spec, neg_add_cancel, zero_spec]
  add_comm := by intros; apply mequiv.injective; simp only [add_spec, add_comm]
  sub_eq_add_neg := by intros; apply mequiv.injective; simp only [sub_spec, sub_eq_add_neg, add_spec, neg_spec]
  nsmul n x := scal (n:K) x
  nsmul_zero := by intros; apply mequiv.injective; simp only [CharP.cast_eq_zero, scal_spec, zero_smul, zero_spec]; rfl
  nsmul_succ := by intros; apply mequiv.injective; simp only [Nat.cast_add, Nat.cast_one, scal_spec, add_smul, one_smul, add_spec]; rfl
  zsmul n x := scal (n:K) x
  zsmul_zero' := by intros; apply mequiv.injective; funext i j; simp[scal_spec,matrix_to_spec]
  zsmul_neg' := by intros; apply mequiv.injective; funext i j; simp[zsmul_neg',scal_spec,add_smul,matrix_to_spec]; ring
  zsmul_succ' := by intros; apply mequiv.injective; funext i j; simp[scal_spec,add_smul,matrix_to_spec]; ring


instance : Module K (M m n) where
  one_smul := by intros; apply mequiv.injective; simp[matrix_to_spec]
  mul_smul := by intros; apply mequiv.injective; simp[matrix_to_spec, smul_smul]
  smul_zero := by intros; apply mequiv.injective; simp[matrix_to_spec]
  smul_add := by intros; apply mequiv.injective; simp[matrix_to_spec]
  add_smul := by intros; apply mequiv.injective; simp[add_smul,matrix_to_spec]
  zero_smul := by intros; apply mequiv.injective; simp[matrix_to_spec]


-- instance : PseudoMetricSpace (M m n) where
--   dist_self := by intros; simp[dist_spec]
--   dist_comm := by intros; simp[dist_spec,dist_comm]
--   dist_triangle := by intros; simp[dist_spec,dist_triangle]

-- instance : NormedAddCommGroup (M m n) where
--   dist_eq := by intros; rfl
--   eq_of_dist_eq_zero := by
--     intro x y h;
--     apply equiv.injective;
--     apply (WithLp.equiv 2 (n → K)).symm.injective
--     simp only [dist_spec] at h
--     exact (eq_of_dist_eq_zero h)

-- instance : NormedSpace K (M m n) where
--   norm_smul_le := by
--     simp only [norm_spec]
--     simp [norm_smul_le,vector_to_spec]

-- instance : InnerProductSpace K (M m n) where
--   norm_sq_eq_inner := by
--     simp only [inner_spec,norm_spec]
--     intro x
--     apply norm_sq_eq_inner
--   conj_symm := by
--     simp only [inner_spec]
--     intro x y;
--     apply conj_symm
--   add_left := by
--     intros; simp only [inner_spec,add_spec, WithLp.equiv_symm_add,add_left]
--   smul_left := by
--     intros; simp only [inner_spec,smul_spec, WithLp.equiv_symm_smul,smul_left]

-- instance : AdjointSpace K (M m n) where
--   inner_top_equiv_norm := by
--     use 1; use 1
--     simp only [inner_spec,norm_spec]
--     constructor
--     · simp only [gt_iff_lt, zero_lt_one]
--     constructor
--     · simp only [gt_iff_lt, zero_lt_one]
--     · intro x
--       constructor
--       · rw[norm_sq_eq_inner (𝕜:=K)]; simp only [one_smul,le_refl]
--       · rw[norm_sq_eq_inner (𝕜:=K)]; simp only [one_smul,le_refl]
--   conj_symm := by
--     simp only [inner_spec]
--     intro x y;
--     apply conj_symm
--   add_left := by
--     intros; simp only [inner_spec,add_spec, WithLp.equiv_symm_add,add_left]
--   smul_left := by
--     intros; simp only [inner_spec,smul_spec, WithLp.equiv_symm_smul,smul_left]


/-- Linear equivalence between vector type `X` and `n → K` -/
def mequivₗ : (M m n) ≃ₗ[K] (Matrix m n K) :=
  LinearEquiv.mk ⟨⟨mequiv,by simp[matrix_to_spec]⟩,by simp[matrix_to_spec]⟩
    mequiv.symm (mequiv.left_inv) (mequiv.right_inv)

-- /-- Continuous linear equivalence between vector type `X` and `n → K` -/
-- def mequivL : (M m n) ≃L[K] (Matrix n m K) := ContinuousLinearEquiv.mk mequivₗ (by sorry_proof) (by sorry_proof)


instance : FiniteDimensional K (M m n) :=
   FiniteDimensional.of_injective (V₂:=Matrix m n K) mequivₗ.1
  (mequivₗ.left_inv.injective)


variable (M)
noncomputable
def basis : Basis (m×n) K (M m n) := Basis.ofEquivFun (ι:=m×n) (R:=K) (M:=M m n)
  (mequivₗ.trans (LinearEquiv.curry K K m n).symm)
variable {M}


@[simp, simp_core]
theorem finrank_eq_index_card : Module.finrank K (M m n) = Fintype.card m * Fintype.card n := by
  rw[Module.finrank_eq_card_basis (basis M)]
  simp only [Fintype.card_prod]



end AlgebraicInstances

end DenseMatrixType

end SciLean
