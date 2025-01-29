import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Data.Matrix.Basic

import SciLean.Analysis.AdjointSpace.Basic
import SciLean.Analysis.Scalar
import SciLean.Data.IndexType
import SciLean.Data.IndexType
import SciLean.Data.VectorType.Init


namespace SciLean

open InnerProductSpace

-- TODO: we should remove binary oprations from VectorType.Base and add them to a separete file
--       because we want to have specialize binary oprations between vectors and subvectors
--       i.e. between vectors of different types!


-- /-- `VectorType.Base X n K` says that `X` behaves like a vector indexed by `n` and with values in `K`.

-- Providing an instance of `VectorType X n K` will automatically provide the following instances
--   - `Add X`, `Sub X`, `Neg X`, `SMul K X`, `Zero X`, `Inner K X`, ...

-- To provide algebraic instances you also need to assume `VectorType.Lawful X n K`. Then you obtain
--   - `NormedAddCommGroup X` with l₂ norm
--   - `InnerProductSpace K X`
--   - `AdjointSpace K X`

-- To provide a finite dimensional instance you also need to assume `VectorType.Dense X n K`. Then you obtain
--   - `FiniteDimensional K X` with the dimension equal to the cardinality of `n`.

-- This class is designed to provide Basic Linear Algebra Subprograms(BLAS) which allows us to define
-- vector space structure on `X` that is computationally efficient.
--  -/
-- class VectorType.Base (X : Type*) (n : outParam (Type*)) [outParam (IndexType n)] {R : outParam (Type*)}  (K : outParam (Type*))
--         [outParam (RealScalar R)] [outParam (Scalar R K)] where
--   toVec (x : X) : (n → K) -- maybe map to Euclidean space

--   /-- Zero vector. -/
--   zero : X
--   zero_spec : toVec zero = 0

--   /-- Scalar multiplication.

--   `x` should be modified if it is passed with ref counter one. -/
--   scal  (alpha : K) (x : X) : X
--   scal_spec (alpha : K) (x : X) :
--     toVec (scal alpha x) = alpha • toVec x

--   /-- Scalar multiplication and scalar addition

--   `x` should be modified if it is passed with ref counter one. -/
--   scalAdd  (alpha beta : K) (x : X) : X
--   scalAdd_spec (alpha beta : K) (x : X) :
--     toVec (scalAdd alpha beta x) = fun i => alpha * toVec x i + beta

--   /-- `sum x = ∑ i, x[i]` -/
--   sum (x : X) : K
--   sum_spec (x : X) : sum x = Finset.univ.sum (fun i : n => toVec x i)

--   /-- `asum x = ∑ i, |x[i]|` -/
--   asum (x : X) : R
--   asum_spec (x : X) : asum x = Scalar.ofReal (K:=K) ‖(WithLp.equiv 1 (n → K)).symm (toVec x)‖

--   /-- `nrm2 x = √∑ i, |x[i]|²` -/
--   nrm2 (x : X) : R
--   nrm2_spec (x : X) : nrm2 x = Scalar.ofReal (K:=K) ‖(WithLp.equiv 2 (n → K)).symm (toVec x)‖

--   /-- `iamax x = argmaxᵢ |x[i]|` -/
--   iamax (x : X) : n -- this is inconsistent if `n` is empty
--   iamax_spec (x : X) : Scalar.abs (toVec x (iamax x)) = Scalar.ofReal (K:=K) ‖toVec x‖

--   /-- `imaxRe x = argmaxᵢ (real x[i])` -/
--   imaxRe (x : X) (h : 0 < size n) : n
--   imaxRe_spec (x : X) (h : 0 < size n) :
--     Scalar.toReal R (Scalar.real (toVec x (imaxRe x h)))
--     =
--     iSup (α:=ℝ) (fun i => Scalar.toReal R <| Scalar.real (K:=K) (toVec x i))

--   /-- `iminRe x = argmaxᵢ (re x[i])` -/
--   iminRe (x : X) (h : 0 < size n) : n
--   iminRe_spec (x : X) (h : 0 < size n) :
--     Scalar.toReal R (Scalar.real (toVec x (iminRe x h)))
--     =
--     iInf (α:=ℝ) (fun i => Scalar.toReal R <| Scalar.real (K:=K) (toVec x i))

--   /-- `dot x y = ∑ i, conj x[i] y[i]` -/
--   dot (x y : X) : K

--   dot_spec (x y : X) :
--     (dot x y) =
--     let x' := (WithLp.equiv 2 (n → K)).symm (toVec x)
--     let y' := (WithLp.equiv 2 (n → K)).symm (toVec y)
--     (⟪x',y'⟫_K)


-- open VectorType.Base
-- /-- Binary operattons where `X` and `X'` represent the same vector `n → K` and `X` is modified. -/
-- class VectorType.BinOps (X X' : Type*)
--     {n : outParam (Type*)} [outParam (IndexType n)]
--     {R K : outParam (Type*)} {_ : outParam (RealScalar R)} {_ : outParam (Scalar R K)}
--     [VectorType.Base X n K] [VectorType.Base X' n K] where


--   /-- `axpy a x y = a • x + y`

--   `y` should be modified if it is passed with ref counter one. -/
--   axpy (alpha : K) (x : X') (y : X) : X

--   axpy_spec (alpha : K) (x : X') (y : X) :
--     toVec (axpy alpha x y) = alpha • toVec x + toVec y

--   /-- `axpby a b x y = a • x + b • y`

--   `y` should be modified if it is passed with ref counter one. -/
--   axpby (alpha : K) (x : X') (beta : K) (y : X) : X := axpy alpha x (scal beta y)

--   axpby_spec (alpha beta : K) (x : X') (y : X) :
--     toVec (axpby alpha x beta y) = alpha • toVec x + beta • toVec y

--   /-  Element wise operations -/
--   /- `apxy` and `axpby` follow BLAS conventions that right element of the operation is modified
--      but for operations we modify the left element as it is more natural with operations being
--      left associated -/

--   /-- Element wise multiplication.

--   `x` should be modified if it is passed with ref counter one. -/
--   mul (x : X) (y : X') : X
--   mul_spec (x : X) (y : X') :
--     toVec (mul x y) = toVec x * toVec y


-- open VectorType.Base VectorType.BinOps Classical in
-- /-- `X'` is subvector of `X` with lawful version `Y`  -/
-- class SubvectorType.Base (X' : Type*) (X Y : outParam (Type*))
--     {n' n : Type*} (ι : n' → n) {_ : outParam (IndexType n')} {_ : outParam (IndexType n)}
--     {R K : outParam (Type*)} {_ : outParam (RealScalar R)} {_ : outParam (Scalar R K)}
--     [VectorType.Base X' n' K] [VectorType.Base X n K] [VectorType.Base Y n' K]
--     [VectorType.BinOps X' Y] where

--   index_inclusion_injective : Function.Injective ι

--   toSubvector (x : X) : X'
--   fromSubvector (x' : X') : X

--   toSubvector_spec (x : X) (i' : n')     : toVec (toSubvector x) i' = toVec x (ι i')
--   fromSubvector_spec (x' : X') (i' : n') : toVec (fromSubvector x') (ι i') = toVec x' i'

--   scal_spec_subvector (alpha : K) (x' : X') (i : n) :
--     toVec (fromSubvector (scal alpha x')) i
--     =
--     if i ∈ Set.range ι then
--       alpha * toVec (fromSubvector x) i
--     else
--       toVec (fromSubvector x) i

--   scalAdd_spec_subvector (alpha beta : K) (x' : X') (i : n) :
--     toVec (fromSubvector (scalAdd alpha beta x')) i
--     =
--     if i ∈ Set.range ι then
--       alpha * toVec (fromSubvector x) i + beta
--     else
--       toVec (fromSubvector x) i

--   axpy_spec_subvector (alpha : K) (y : Y) (x' : X') (i : n) :
--     toVec (fromSubvector (axpy alpha y x')) i
--     =
--     if h : i ∈ Set.range ι then
--       alpha * toVec y (choose h) + toVec (fromSubvector x') i
--     else
--       toVec (fromSubvector x') i

--   axpby_spec_subvector (alpha beta : K) (y : Y) (x' : X') (i : n) :
--     toVec (fromSubvector (axpby alpha y beta x')) i
--     =
--     if h : i ∈ Set.range ι then
--       alpha * toVec y (choose h) + beta * toVec (fromSubvector x') i
--     else
--       toVec (fromSubvector x') i
