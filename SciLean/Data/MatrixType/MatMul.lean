import SciLean.Data.MatrixType.Base
import SciLean.Data.MatrixType.Square

namespace SciLean

open Matrix


class DenseMatrixType.MatMul
      (M₁ M₂ : Type*) (M₃ : outParam (Type*))
      {l m n : outParam (Type*)} [IndexType l] [IndexType m] [IndexType n]
      {R K : outParam (Type*)} [RealScalar R] [Scalar R K]
      {X Y Z : outParam (Type*)} [VectorType.Base X n K] [VectorType.Base Y m K] [VectorType.Base Z l K]
      [DenseMatrixType.Base M₁ X Y] [DenseMatrixType.Base M₂ Y Z] [DenseMatrixType.Base M₃ X Z]
  where

  matmul (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) : M₃
  matmul_spec (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) :
    mequiv (matmul alpha beta A B C)
    =
    let A := mequiv A
    let B := mequiv B
    let C := mequiv C
    alpha•A*B + beta•C


class DenseMatrixType.MatMulTI
      (M₁ M₂ : Type*) (M₃ : outParam (Type*))
      {l m n : outParam (Type*)} [IndexType l] [IndexType m] [IndexType n]
      {R K : outParam (Type*)} [RealScalar R] [Scalar R K]
      (X Y Z : outParam (Type*)) [VectorType.Base X n K] [VectorType.Base Y m K] [VectorType.Base Z l K]
      [DenseMatrixType.Base M₁ X Y] [DenseMatrixType.Base M₂ Z Y] [DenseMatrixType.Base M₃ X Z]
  where

  matmulTI (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) : M₃
  matmulTI_spec (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) :
    mequiv (matmulTI alpha beta A B C)
    =
    let A := mequiv A
    let B := mequiv B
    let C := mequiv C
    alpha•Aᵀ*B + beta•C

  matmulHI (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) : M₃
  matmulHI_spec (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) :
    mequiv (matmulTI alpha beta A B C)
    =
    let A := mequiv A
    let B := mequiv B
    let C := mequiv C
    alpha•Aᴴ*B + beta•C


class DenseMatrixType.MatMulIT
      (M₁ M₂ : Type*) (M₃ : outParam (Type*))
      {l m n : outParam (Type*)} [IndexType l] [IndexType m] [IndexType n]
      {R K : outParam (Type*)} [RealScalar R] [Scalar R K]
      (X Y Z : outParam (Type*)) [VectorType.Base X n K] [VectorType.Base Y m K] [VectorType.Base Z l K]
      [DenseMatrixType.Base M₁ Y X] [DenseMatrixType.Base M₂ Y Z] [DenseMatrixType.Base M₃ X Z]
  where

  matmulIT (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) : M₃
  matmulIT_spec (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) :
    mequiv (matmulIT alpha beta A B C)
    =
    let A := mequiv A
    let B := mequiv B
    let C := mequiv C
    alpha•A*Bᵀ + beta•C

  matmulIH (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) : M₃
  matmulIH_spec (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) :
    mequiv (matmulIH alpha beta A B C)
    =
    let A := mequiv A
    let B := mequiv B
    let C := mequiv C
    alpha•A*Bᴴ + beta•C


class DenseMatrixType.MatMulTT
      (M₁ M₂ : Type*) (M₃ : outParam (Type*))
      {l m n : outParam (Type*)} [IndexType l] [IndexType m] [IndexType n]
      {R K : outParam (Type*)} [RealScalar R] [Scalar R K]
      (X Y Z : outParam (Type*)) [VectorType.Base X n K] [VectorType.Base Y m K] [VectorType.Base Z l K]
      [DenseMatrixType.Base M₁ Y X] [DenseMatrixType.Base M₂ Z Y] [DenseMatrixType.Base M₃ X Z]
  where

  matmulIT (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) : M₃
  matmulIT_spec (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) :
    mequiv (matmulIT alpha beta A B C)
    =
    let A := mequiv A
    let B := mequiv B
    let C := mequiv C
    alpha•Aᵀ*Bᵀ + beta•C

  matmulIH (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) : M₃
  matmulIH_spec (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) :
    mequiv (matmulIH alpha beta A B C)
    =
    let A := mequiv A
    let B := mequiv B
    let C := mequiv C
    alpha•Aᴴ*Bᴴ + beta•C


namespace DenseMatrixType.MatMul

section Instances

variable
      {M₁ M₂ : Type*} {M₃ : outParam (Type*)}
      {l m n : outParam (Type*)} [IndexType l] [IndexType m] [IndexType n]
      {R K : outParam (Type*)} [RealScalar R] [Scalar R K]
      {X Y Z : outParam (Type*)} [VectorType.Base X n K] [VectorType.Base Y m K] [VectorType.Base Z l K]
      [DenseMatrixType.Base M₁ X Y] [DenseMatrixType.Base M₂ Y Z] [DenseMatrixType.Base M₃ X Z]
      [DenseMatrixType.MatMul M₁ M₂ M₃]

instance : HMul M₂ M₁ M₃ := ⟨(DenseMatrixType.MatMul.matmul 1 1 · · 0)⟩

@[matrix_to_spec, matrix_from_spec ←]
theorem hmul_to_spec (A : M₂) (B : M₁) :
    mequiv (A*B)
    =
    let A := mequiv A
    let B := mequiv B
    A * B := by
  conv => lhs; dsimp[HMul.hMul]
  simp only [matmul_spec, one_smul, zero_spec, smul_zero, add_zero]


end Instances


section SquareInstances

variable
      {M : Type*}
      {n : outParam (Type*)} [IndexType n] [DecidableEq n]
      {R K : outParam (Type*)} [RealScalar R] [Scalar R K]
      {X : outParam (Type*)} [VectorType.Base X n K]
      [DenseMatrixType.Base M X X]
      [DenseMatrixType.Square M X]
      [DenseMatrixType.MatMul M M M]


instance : Mul M := ⟨fun A B => A * B⟩

instance : Monoid M where
  mul_assoc := by intros; apply mequiv.injective; simp only [hmul_to_spec, mul_assoc]
  one_mul := by intros; apply mequiv.injective; simp only [hmul_to_spec, one_spec, one_mul]
  mul_one := by intros; apply mequiv.injective; simp only [hmul_to_spec, one_spec, mul_one]

instance : Semiring M where
  left_distrib := by intros; apply mequiv.injective; simp [hmul_to_spec,add_spec,left_distrib]
  right_distrib := by intros; apply mequiv.injective; simp only [hmul_to_spec, add_spec, right_distrib]
  zero_mul := by intros; apply mequiv.injective; simp only [hmul_to_spec, zero_spec, zero_mul]
  mul_zero := by intros; apply mequiv.injective; simp only [hmul_to_spec, zero_spec, mul_zero]
  mul_assoc := by intros; apply mequiv.injective; simp only [mul_assoc, hmul_to_spec]
  one_mul := by intros; apply mequiv.injective; simp only [one_mul]
  mul_one := by intros; apply mequiv.injective; simp only [mul_one]

instance : Algebra K M where
  toFun k := diagonal (VectorType.const k)
  map_one' := by apply mequiv.injective; simp [matrix_to_spec, vector_to_spec]
  map_mul' := by intros; apply mequiv.injective; simp [matrix_to_spec, vector_to_spec]
  map_zero' := by apply mequiv.injective; simp [matrix_to_spec, vector_to_spec]
  map_add' := by intros; apply mequiv.injective; simp [matrix_to_spec, vector_to_spec]
  commutes' := by intros; apply mequiv.injective; funext i j; simp [matrix_to_spec, vector_to_spec,mul_comm]
  smul_def' := by intros; apply mequiv.injective; funext i j; simp [matrix_to_spec, vector_to_spec]


end SquareInstances
