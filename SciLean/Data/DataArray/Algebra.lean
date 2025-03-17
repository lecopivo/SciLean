import SciLean.Data.DataArray.RnEquiv

/-! Algebraic structure in `X^[I]`

This file automatically pulls algebraic structure of `R^[n]` onto `X^[I]` anytime `X` has
an instance of `HasRnEquiv X m R`.

TODO: There should be a class that the structure of.
-/

namespace SciLean



/-- This very important instances which gives all basic algebraic operations on `X^[I]`. -/
instance {X R : Type*} [RealScalar R] [PlainDataType R]
  [HasRnEquiv X n R] [PlainDataType X]
  {I nI} [IdxType I nI] [BLAS (DataArray R) R R] :
  NormedAddCommGroup (X^[I]) := NormedAddCommGroup.ofRnEquiv (X^[I])

/-- This very important instances which gives scalar multiplication and inner product on `X^[I]`. -/
instance {X R : Type*} [RealScalar R] [PlainDataType R]
  [HasRnEquiv X n R] [PlainDataType X]
  {I nI} [IdxType I nI] [BLAS (DataArray R) R R] :
  AdjointSpace R (X^[I]) := AdjointSpace.ofRnEquiv (X^[I])
