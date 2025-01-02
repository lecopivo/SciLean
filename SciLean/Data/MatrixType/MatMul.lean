import SciLean.Data.MatrixType.Base
import SciLean.Data.MatrixType.Square

namespace SciLean

open Matrix

open MatrixType VectorType

class MatrixType.MatMul
      (M₁ M₂ : Type*) (M₃ : outParam (Type*))
      {l m n : outParam (Type*)} [IndexType l] [IndexType m] [IndexType n]
      {R K : outParam (Type*)} [RealScalar R] [Scalar R K]
      {X Y Z : outParam (Type*)} [VectorType.Base X n K] [VectorType.Base Y m K] [VectorType.Base Z l K]
      [MatrixType.Base M₁ X Y] [MatrixType.Base M₂ Y Z] [MatrixType.Base M₃ X Z]
  where

  matmul (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) : M₃
  matmul_spec (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) :
    toMatrix (matmul alpha beta A B C)
    =
    let A := toMatrix A
    let B := toMatrix B
    let C := toMatrix C
    alpha•A*B + beta•C


class MatrixType.MatMulTI
      (M₁ M₂ : Type*) (M₃ : outParam (Type*))
      {l m n : outParam (Type*)} [IndexType l] [IndexType m] [IndexType n]
      {R K : outParam (Type*)} [RealScalar R] [Scalar R K]
      (X Y Z : outParam (Type*)) [VectorType.Base X n K] [VectorType.Base Y m K] [VectorType.Base Z l K]
      [MatrixType.Base M₁ X Y] [MatrixType.Base M₂ Z Y] [MatrixType.Base M₃ X Z]
  where

  matmulTI (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) : M₃
  matmulTI_spec (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) :
    toMatrix (matmulTI alpha beta A B C)
    =
    let A := toMatrix A
    let B := toMatrix B
    let C := toMatrix C
    alpha•Aᵀ*B + beta•C

  matmulHI (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) : M₃
  matmulHI_spec (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) :
    toMatrix (matmulTI alpha beta A B C)
    =
    let A := toMatrix A
    let B := toMatrix B  -- maybe it should be `Matrix m n K → M → M` such that `Dense` works also for submatrices
  -- the current definition forces lawfulness which excludes submatrices

    let C := toMatrix C
    alpha•Aᴴ*B + beta•C


class MatrixType.MatMulIT
      (M₁ M₂ : Type*) (M₃ : outParam (Type*))
      {l m n : outParam (Type*)} [IndexType l] [IndexType m] [IndexType n]
      {R K : outParam (Type*)} [RealScalar R] [Scalar R K]
      (X Y Z : outParam (Type*)) [VectorType.Base X n K] [VectorType.Base Y m K] [VectorType.Base Z l K]
      [MatrixType.Base M₁ Y X] [MatrixType.Base M₂ Y Z] [MatrixType.Base M₃ X Z]
  where

  matmulIT (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) : M₃
  matmulIT_spec (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) :
    toMatrix (matmulIT alpha beta A B C)
    =
    let A := toMatrix A
    let B := toMatrix B
    let C := toMatrix C
    alpha•A*Bᵀ + beta•C

  matmulIH (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) : M₃
  matmulIH_spec (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) :
    toMatrix (matmulIH alpha beta A B C)
    =
    let A := toMatrix A
    let B := toMatrix B
    let C := toMatrix C
    alpha•A*Bᴴ + beta•C


class MatrixType.MatMulTT
      (M₁ M₂ : Type*) (M₃ : outParam (Type*))
      {l m n : outParam (Type*)} [IndexType l] [IndexType m] [IndexType n]
      {R K : outParam (Type*)} [RealScalar R] [Scalar R K]
      (X Y Z : outParam (Type*)) [VectorType.Base X n K] [VectorType.Base Y m K] [VectorType.Base Z l K]
      [MatrixType.Base M₁ Y X] [MatrixType.Base M₂ Z Y] [MatrixType.Base M₃ X Z]
  where

  matmulIT (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) : M₃
  matmulIT_spec (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) :
    toMatrix (matmulIT alpha beta A B C)
    =
    let A := toMatrix A
    let B := toMatrix B
    let C := toMatrix C
    alpha•Aᵀ*Bᵀ + beta•C

  matmulIH (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) : M₃
  matmulIH_spec (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) :
    toMatrix (matmulIH alpha beta A B C)
    =
    let A := toMatrix A
    let B := toMatrix B
    let C := toMatrix C
    alpha•Aᴴ*Bᴴ + beta•C


namespace MatrixType.MatMul

section Instances

variable
      {M₁ M₂ : Type*} {M₃ : outParam (Type*)}
      {l m n : outParam (Type*)} [IndexType l] [IndexType m] [IndexType n]
      {R K : outParam (Type*)} [RealScalar R] [Scalar R K]
      {X Y Z : outParam (Type*)} [VectorType.Base X n K] [VectorType.Base Y m K] [VectorType.Base Z l K]
      [MatrixType.Base M₁ X Y] [MatrixType.Base M₂ Y Z] [MatrixType.Base M₃ X Z]
      [MatrixType.MatMul M₁ M₂ M₃]

instance : HMul M₂ M₁ M₃ := ⟨(MatrixType.MatMul.matmul 1 1 · · 0)⟩

@[matrix_to_spec, matrix_from_spec ←]
theorem hmul_to_spec (A : M₂) (B : M₁) :
    toMatrix (A*B)
    =
    let A := toMatrix A
    let B := toMatrix B
    A * B := by
  conv => lhs; dsimp[HMul.hMul]
  simp only [matmul_spec, one_smul, zero_spec, smul_zero, add_zero]


end Instances


section SquareInstances

variable
      {M : Type*}
      {n : outParam (Type*)} {_ : outParam (IndexType n)}
      {R K : outParam (Type*)} {_ : outParam (RealScalar R)} {_ : outParam (Scalar R K)}
      {X : outParam (Type*)} [VectorType.Base X n K] [VectorType.Dense X]
      [MatrixType.Base M X X] [MatrixType.Lawful M]
      [MatrixType.Square M]
      [MatrixType.MatMul M M M]


instance : Mul M := ⟨fun A B => A * B⟩

open Classical in
instance : Monoid M where
  mul_assoc := by intros; ext; simp only [hmul_to_spec, mul_assoc]
  one_mul := by intros; ext; simp only [hmul_to_spec, one_spec, one_mul]
  mul_one := by intros; ext; simp only [hmul_to_spec, one_spec, mul_one]

instance : Semiring M where
  left_distrib := by intros; ext; simp [hmul_to_spec,add_spec,left_distrib]
  right_distrib := by intros; ext; simp only [hmul_to_spec, add_spec, right_distrib]
  zero_mul := by intros; ext; simp only [hmul_to_spec, zero_spec, zero_mul]
  mul_zero := by intros; ext; simp only [hmul_to_spec, zero_spec, mul_zero]
  mul_assoc := by intros; ext; simp only [mul_assoc, hmul_to_spec]
  one_mul := by intros; ext; simp only [hmul_to_spec, one_spec, one_mul]
  mul_one := by intros; ext; simp only [hmul_to_spec, one_spec, mul_one]

open Classical in
instance instAlgebra : Algebra K M where
  toFun k := diagonal (VectorType.const k)
  map_one' := by ext; simp [matrix_to_spec, vector_to_spec]
  map_mul' := by intros; ext; simp [matrix_to_spec, vector_to_spec]
  map_zero' := by ext; simp [matrix_to_spec, vector_to_spec]
  map_add' := by intros; ext; simp [matrix_to_spec, vector_to_spec,←Matrix.diagonal_add]
  commutes' := by intros; ext; simp [matrix_to_spec, vector_to_spec,mul_comm]
  smul_def' := by intros; ext; simp [matrix_to_spec, vector_to_spec]

-- set_synth_order instAlgebra #[11, 9, 10, 2, 3, 6, 7, 12, 13, 14]


end SquareInstances
