import SciLean.Data.MatrixType.Base
import SciLean.Data.IndexType.IndexInclusion

namespace SciLean

/-- `SubMatrix M M'` is saying that `A' : M' ι κ` is a `m'×n'` submatrix of `m×n` matrix `A : M`
for index inclusions `ι : m' → m` and `κ : n' → n`. -/
class SubMatrix
      (M : Type*)
      {m n : outParam (Type*)} [IndexType m] [IndexType n]
      {R K : outParam (Type*)} [RealScalar R] [Scalar R K]
      (X Y : outParam (Type*)) [VectorType.Base X n K] [VectorType.Base Y m K]
      [DenseMatrixType.Base M X Y]
      (M' : outParam <| {m' : Type u} → {n' : Type v} → [IndexType m'] → [IndexType n'] →
            (ι : IndexInclusion m' m) → (κ : IndexInclusion n' n) → Type*)
   where

   getSubmatix (A : M)
     {m' : Type u} {n' : Type v} [IndexType m'] [IndexType n']
     (ι : IndexInclusion m' m) (κ : IndexInclusion n' n) : M' ι κ

   getParent
     {m' : Type u} {n' : Type v} [IndexType m'] [IndexType n']
     {ι : IndexInclusion m' m} {κ : IndexInclusion n' n}
     (A' : M' ι κ) : M
