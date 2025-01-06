import SciLean.Data.MatrixType.Init
import SciLean.Data.MatrixType.Base
import SciLean.Data.MatrixType.Dense
import SciLean.Data.MatrixType.Square
import SciLean.Data.MatrixType.Transpose
import SciLean.Data.MatrixType.MatMul
import SciLean.Data.VectorType.Basic

namespace SciLean

open Matrix VectorType

class MatrixType
    (M : (m n : Type u) → [IndexType m] → [IndexType n] → Type*)
    (X : outParam ((n : Type u) → [IndexType n] → Type*))
    {R : outParam (Type*)} {K : outParam (Type*)} [outParam (RealScalar R)] [outParam (Scalar R K)]
    [VectorType X K]
  where
  [base : ∀ (m n : Type u) [IndexType m] [IndexType n], MatrixType.Base (M m n) (X n) (X m)]
  [dense : ∀ (m n : Type u) [IndexType m] [IndexType n], MatrixType.Dense (M m n)]
  [lawful : ∀ (m n : Type u) [IndexType m] [IndexType n], MatrixType.Lawful (M m n)]
  [square : ∀ (n : Type u) [IndexType n], MatrixType.Square (M n n)]

  -- cast
  -- cast_spec

  -- vconcat
  -- hconcat



instance
    (M : (m n : Type u) → [IndexType m] → [IndexType n] → Type*)
    (X : (n : Type u) → [IndexType n] → Type*)
    {R : outParam (Type*)} {K : outParam (Type*)} {_ : RealScalar R} {_ : Scalar R K}
    [VectorType X K] [inst : MatrixType M X]
    {m n : Type u} {_ : IndexType m} {_ : IndexType n} :
    MatrixType.Base (M m n) (X n) (X m) := inst.base m n

instance
    (M : (m n : Type u) → [IndexType m] → [IndexType n] → Type*)
    (X : (n : Type u) → [IndexType n] → Type*)
    {R : outParam (Type*)} {K : outParam (Type*)} {_ : RealScalar R} {_ : Scalar R K}
    [VectorType X K] [inst : MatrixType M X]
    {m n : Type u} {_ : IndexType m} {_ : IndexType n} :
    MatrixType.Dense (M m n) := inst.dense m n

instance
    (M : (m n : Type u) → [IndexType m] → [IndexType n] → Type*)
    (X : (n : Type u) → [IndexType n] → Type*)
    {R : outParam (Type*)} {K : outParam (Type*)} {_ : RealScalar R} {_ : Scalar R K}
    [VectorType X K] [inst : MatrixType M X]
    {m n : Type u} {_ : IndexType m} {_ : IndexType n} :
    MatrixType.Lawful (M m n) := inst.lawful m n

instance
    (M : (m n : Type u) → [IndexType m] → [IndexType n] → Type*)
    (X : (n : Type u) → [IndexType n] → Type*)
    {R : outParam (Type*)} {K : outParam (Type*)} {_ : RealScalar R} {_ : Scalar R K}
    [VectorType X K] [inst : MatrixType M X]
    {n : Type u}{_ : IndexType n} :
    MatrixType.Square (M n n) := inst.square n
