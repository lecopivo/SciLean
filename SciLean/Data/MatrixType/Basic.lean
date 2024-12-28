import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import SciLean.Data.IndexType

import SciLean.Analysis.Scalar
import SciLean.Analysis.AdjointSpace.Basic

import SciLean.Data.VectorType.Basic

namespace SciLean

open Matrix VectorType


/-- `DenseMatrixType M X Y` says that `M` is a matrix transforming vectors of type `X` to vectors
of type `Y`.

This class provides functionality implementable using BLAS. -/
class DenseMatrixType
      (M : (m : Type u) → (n : Type u) → [IndexType m] → [IndexType n] → Type*)
      (V : outParam ((m : Type u) → [IndexType m] → Type*))
      {R : outParam (Type*)} {K : outParam (Type*)}
      [Scalar R K] [VectorType V K]
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

  /-- Matrix trace, `trace A = ∑ i, A i i` -/
  trace    {n} [IndexType n] (A : M n n) : K

  trace_spec {n} [IndexType n] (A : M n n) :
    trace A = ∑ i, (mequiv A) i i


  /-    Level 1 like BLAS operations    -/

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

  /-- Get column of matrix -/
  col {m n} [IndexType m] [IndexType n] (A : M m n) (j : n) : V m

  col_spec {m n} [IndexType m] [IndexType n] (A : M m n) (j : n) :
    equiv (col A j) = fun i => (mequiv A) i j


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
