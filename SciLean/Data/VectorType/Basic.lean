import SciLean.Data.VectorType.Base

namespace SciLean

-- open IndexType VectorType
-- /-- `VectorType X K` says that `X n` behaves like a vector indexed by `n` and with values in `K`.

-- Providing an instance of `VectorType X K` will automatically provide the following instances
--   - `Add (X n)`, `Sub (X n)`, `Neg (X n)`, `SMul K (X n)`, `Zero (X n)`, `Inner K (X n)`, ...
--   - `NormedAddCommGroup (X n)` with l₂ norm
--   - `InnerProductSpace K (X n)`
--   - `AdjointSpace K (X n)`
--   - `FiniteDimensional K (X n)`

-- This class is designed to provide Basic Linear Algebra Subprograms(BLAS) which allows us to define
-- vector space structure on `(X n)` that is computationally efficient.
--  -/
-- class VectorType
--     (X : (n : Type u) → [IndexType n] → Type*)
--     {R : outParam (Type*)} (K : outParam (Type*)) [outParam (RealScalar R)] [outParam (Scalar R K)]
--   where
--   [base : ∀ (n : Type u) [IndexType n], VectorType.Base (X n) n K]
--   [dense : ∀ (n : Type u) [IndexType n], VectorType.Dense (X n)]
--   [lawful : ∀ (n : Type u) [IndexType n], InjectiveGetElem (X n) n]

--   /-- Index vector with different index type with the same number of elements.

--   This operation should no perform any computation and be only a type cast. -/
--   cast {n : Type u} [IndexType n] (x : X n) (m : Type u) [IndexType m] (h : size m = size n) : X m
--   cast_spec {n : Type u} [IndexType n] (x : X n) (m : Type u) [IndexType m]
--     (h : size m = size n) (j : m) :
--     (cast x m h)[j]
--     =
--     x[fromFin (I:=n) ((toFin (I:=m) j).cast h)]


-- instance (priority:=low)
--     (X : (n : Type u) → [IndexType n] → Type*)
--     {R : outParam (Type*)} (K : outParam (Type*)) {_ : outParam (RealScalar R)} {_ : outParam (Scalar R K)}
--     {n : outParam (Type u)} {_ : outParam (IndexType n)}
--     [inst : VectorType X K] : VectorType.Base (X n) n K := inst.base n

-- instance (priority:=low)
--     (X : (n : Type u) → [IndexType n] → Type*)
--     {R : outParam (Type*)} (K : outParam (Type*)) {_ : RealScalar R} {_ : Scalar R K}
--     {n : Type u} {_ : IndexType n}
--     [inst : VectorType X K] : VectorType.Dense (X n) := inst.dense n

-- instance (priority:=low)
--     (X : (n : Type u) → [IndexType n] → Type*)
--     {R : outParam (Type*)} (K : outParam (Type*)) {_ : RealScalar R} {_ : Scalar R K}
--     {n : Type u} {_ : IndexType n}
--     [inst : VectorType X K] : InjectiveGetElem (X n) n  := inst.lawful n
