import SciLean.Data.MatrixType.Base
import SciLean.Data.MatrixType.Square

namespace SciLean

open Matrix

open MatrixType VectorType

class MatrixType.MatMul
      (M₁ M₂ : Type*) (M₃ : outParam (Type*))
      {l m n : outParam <| (Type*)} {nl nm nn : outParam ℕ} {_ : outParam (IdxType l nl)} {_ : outParam (IdxType m nm)} {_ : outParam (IdxType n nn)}
      {R K : outParam <| (Type*)} {_ : outParam <| RealScalar R} {_ : outParam <| Scalar R K}
      {X Y Z : outParam <| (Type*)} {_ : outParam <| VectorType.Base X n K} {_ : outParam <| VectorType.Base Y m K} {_ : outParam <| VectorType.Base Z l K}
      [MatrixType.Base M₁ X Y] [MatrixType.Base M₂ Y Z] [MatrixType.Base M₃ X Z]
  where

  matmul (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) : M₃
  matmul_spec (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) (i : l) (j : n)  :
    (matmul alpha beta A B C)[(i,j)]
    =
    let A := toMatrix A
    let B := toMatrix B
    let C := toMatrix C
    (alpha•A*B + beta•C) i j


class MatrixType.MatMulTI
      (M₁ M₂ : Type*) (M₃ : outParam (Type*))
      {l m n : outParam (Type*)} {nl} [IdxType l nl] {nm} [IdxType m nm] {nn} [IdxType n nn]
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
      {l m n : outParam (Type*)} {nl} [IdxType l nl] {nm} [IdxType m nm] {nn} [IdxType n nn]
      {R K : outParam (Type*)} [RealScalar R] [Scalar R K]
      (X Y Z : outParam (Type*)) [VectorType.Base X n K] [VectorType.Base Y m K] [VectorType.Base Z l K]
      [MatrixType.Base M₁ Y X] [MatrixType.Base M₂ Y Z] [MatrixType.Base M₃ X Z]
  where

  matmulIT (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) : M₃
  matmulIT_spec (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) (i : l) (j : n) :
    (matmulIT alpha beta A B C)[(i,j)]
    =
    let A := toMatrix A
    let B := toMatrix B
    let C := toMatrix C
    (alpha•A*Bᵀ + beta•C) i j

  matmulIH (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) : M₃
  matmulIH_spec (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) (i : l) (j : n) :
    (matmulIH alpha beta A B C)[(i,j)]
    =
    let A := toMatrix A
    let B := toMatrix B
    let C := toMatrix C
    (alpha•A*Bᴴ + beta•C) i j


class MatrixType.MatMulTT
      (M₁ M₂ : Type*) (M₃ : outParam (Type*))
      {l m n : outParam (Type*)} {nl} [IdxType l nl] {nm} [IdxType m nm] {nn} [IdxType n nn]
      {R K : outParam (Type*)} [RealScalar R] [Scalar R K]
      (X Y Z : outParam (Type*)) [VectorType.Base X n K] [VectorType.Base Y m K] [VectorType.Base Z l K]
      [MatrixType.Base M₁ Y X] [MatrixType.Base M₂ Z Y] [MatrixType.Base M₃ X Z]
  where

  matmulIT (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) : M₃
  matmulIT_spec (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) (i : l) (j : n) :
    (matmulIT alpha beta A B C)[(i,j)]
    =
    let A := toMatrix A
    let B := toMatrix B
    let C := toMatrix C
    (alpha•Aᵀ*Bᵀ + beta•C) i j

  matmulIH (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) : M₃
  matmulIH_spec (alpha beta : K) (A : M₂) (B : M₁) (C : M₃) (i : l) (j : n) :
    (matmulIH alpha beta A B C)[(i,j)]
    =
    let A := toMatrix A
    let B := toMatrix B
    let C := toMatrix C
    (alpha•Aᴴ*Bᴴ + beta•C) i j


namespace MatrixType.MatMul

section Instances

variable
      {M₁ M₂ : Type*} {M₃ : outParam (Type*)}
      {l m n : outParam <| (Type*)} {nl nm nn : outParam ℕ} {_ : outParam (IdxType l nl)} {_ : outParam (IdxType m nm)} {_ : outParam (IdxType n nn)}
      {R K : outParam <| (Type*)} {_ : outParam <| RealScalar R} {_ : outParam <| Scalar R K}
      {X Y Z : outParam <| (Type*)} {_ : outParam <| VectorType.Base X n K} {_ : outParam <| VectorType.Base Y m K} {_ : outParam <| VectorType.Base Z l K}
      [MatrixType.Base M₁ X Y] [MatrixType.Base M₂ Y Z] [MatrixType.Base M₃ X Z]
      [MatrixType.MatMul M₁ M₂ M₃]

instance (priority:=low) : HMul M₂ M₁ M₃ := ⟨(MatrixType.MatMul.matmul 1 1 · · 0)⟩

@[vector_to_spec]
theorem hmul_to_spec (A : M₂) (B : M₁) (i : l) (j : n) :
    (A*B)[(i,j)]
    =
    let A := toMatrix A
    let B := toMatrix B
    (A * B) i j := by
  conv => lhs; dsimp[HMul.hMul]
  simp [vector_to_spec, matmul_spec]




end Instances


section SquareInstances

variable
      {M : Type*}
      {n : outParam (Type*)} {nn : outParam ℕ} {_ : outParam (IdxType n nn)}
      {R K : outParam (Type*)} {_ : outParam (RealScalar R)} {_ : outParam (Scalar R K)}
      {X : outParam (Type*)} {_ : VectorType.Base X n K}
      [MatrixType.Base M X X] [VectorType.Dense X] [InjectiveGetElem M (n×n)]
      [MatrixType.Square M]
      [MatrixType.MatMul M M M]


instance (priority:=low) : Mul M := ⟨fun A B => A * B⟩

open Classical in
instance (priority:=low) : Monoid M where
  mul_assoc := by intros; ext i; cases i; simp [vector_to_spec, mul_assoc]
  one_mul := by intros; ext i; cases i; simp only [vector_to_spec, one_spec, one_mul]
  mul_one := by intros; ext i; cases i; simp only [vector_to_spec, one_spec, mul_one]

instance (priority:=low) : Semiring M where
  left_distrib := by intros; ext; sorry_proof; -- simp [vector_to_spec,left_distrib]
  right_distrib := by intros; ext; sorry_proof; -- simp only [hmul_to_spec, add_spec, right_distrib]
  zero_mul := by intros; apply MatrixType.ext; sorry_proof
  mul_zero := by intros; ext; simp [vector_to_spec]; sorry_proof
  mul_assoc := by intros; ext; simp [matrix_to_spec, mul_assoc]
  one_mul := by intros; ext; simp [matrix_to_spec]
  mul_one := by intros; ext; simp [matrix_to_spec]

open Classical in
instance (priority:=low) instAlgebra : Algebra K M where
  algebraMap := ⟨⟨⟨fun k => diagonal (VectorType.const k), sorry_proof⟩,
                  sorry_proof⟩, sorry_proof, sorry_proof⟩
  commutes' := by intros; ext i; cases i; simp [matrix_to_spec, vector_to_spec,mul_comm]
  smul_def' := by intros; ext i; cases i; simp [matrix_to_spec, vector_to_spec]


end SquareInstances
