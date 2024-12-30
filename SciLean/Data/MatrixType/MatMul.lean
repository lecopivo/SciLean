import SciLean.Data.MatrixType.Base

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
      {n : outParam (Type*)} [IndexType n]
      {R K : outParam (Type*)} [RealScalar R] [Scalar R K]
      {X : outParam (Type*)} [VectorType.Base X n K]
      [DenseMatrixType.Base M X X]
      [DenseMatrixType.MatMul M M M]


instance : Mul M := ⟨fun A B => A * B⟩

instance : Monoid M where
  mul_assoc := sorry_proof
  one := sorry_proof
  one_mul := sorry_proof
  mul_one := sorry_proof


end SquareInstances
