import SciLean.Algebra.TensorProduct.Basic
import SciLean.Analysis.AdjointSpace.CanonicalBasis

namespace SciLean

/--
Class providing identity matrix of type `X ⊗ X`
 -/
class TensorProductSelf
    (R X XX : Type*) [RCLike R]
    [NormedAddCommGroup X] [AdjointSpace R X]
    [AddCommGroup XX] [Module R XX]
    [tp : TensorProductType R X X XX]
  where
    /-- Identit matrix -/
    identity : XX
    identity_spec (x : X) :
      tp.matVecMul (1:R) identity x 0 0 = x


/--
Class providing operations on diagonals of matrices of type `X ⊗ X`

Is there basis free version?
 -/
class TensorProductDiag
    (R X XX : Type*) [RCLike R]
    [NormedAddCommGroup X] [AdjointSpace R X]
    [AddCommGroup XX] [Module R XX]
    [tp : TensorProductType R X X XX]
    [Fintype I] [CanonicalBasis I R X]
  where

    /-- Turn vector `x` into diagonal matrix -/
    diagonal (x : X) : XX
    diagonal_spec : ∀ (x : X) ,
      (diagonal x)
      =
      -- ∑ i, (ℼ i x) • (ⅇ i) ⊗ (ⅇ i)
      Finset.univ.sum fun (i : I) =>
        (ℼ[R,i] x) • (tmul R XX ⅇ[R,X,i] ⅇ'[R,X,i])

    /-- Turn vector `x` into diagonal matrix -/
    diag (A : XX) : X
    diag_spec : ∀ (A : XX) (i : I) ,
      ℼ[R,i] (diag A)
      =
      -- ℼ[i] (A * ⅇ[i])
      ℼ[R,i] (tp.matVecMul (1:R) A ⅇ[R,X,i] 0 0)

    addDiag (a : R) (x : X) (A : XX) : XX
    addDiag_spec (a : R) (x : X) (A : XX) :
      addDiag a x A
      =
      a • diagonal x + A
