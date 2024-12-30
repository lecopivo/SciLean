import SciLean.Data.VectorType.Base

namespace SciLean

open IndexType
/-- `VectorType X K` says that `X n` behaves like a vector indexed by `n` and with values in `K`.

Providing an instance of `VectorType X K` will automatically provide the following instances
  - `Add (X n)`, `Sub (X n)`, `Neg (X n)`, `SMul K (X n)`, `Zero (X n)`, `Inner K (X n)`, ...
  - `NormedAddCommGroup (X n)` with l₂ norm
  - `InnerProductSpace K (X n)`
  - `AdjointSpace K (X n)`
  - `FiniteDimensional K (X n)`

This class is designed to provide Basic Linear Algebra Subprograms(BLAS) which allows us to define
vector space structure on `(X n)` that is computationally efficient.
 -/
class VectorType
    (X : (n : Type u) → [IndexType n] → Type*)
    {R : outParam (Type*)} (K : outParam (Type*)) [Scalar R R] [Scalar R K]
  where
  [base : ∀ (n : Type u) [IndexType n], VectorType.Base (X n) n K]

  /-- Index vector with different index type with the same number of elements.

  This operation should no perform any computation and be only a type cast. -/
  cast {n : Type u} [IndexType n] (x : X n) (m : Type u) [IndexType m] (h : size m = size n) : X m
  cast_spec {n : Type u} [IndexType n] (x : X n) (m : Type u) [IndexType m]
    (h : size m = size n) :
    VectorType.Base.vequiv (cast x m h)
    =
    fun j => VectorType.Base.vequiv x (fromFin (I:=n) ((toFin (I:=m) j).cast h))


instance
    (X : (n : Type u) → [IndexType n] → Type*)
    {R : outParam (Type*)} (K : outParam (Type*)) [Scalar R R] [Scalar R K]
    {n : Type u} [IndexType n]
    [inst : VectorType X K] : VectorType.Base (X n) n K := inst.base n
