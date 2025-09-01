import SciLean.Algebra.TensorProduct.Basic

namespace SciLean


/--
Class providing matrix-matrix multiplcation

This takes `A : Z ⊗ Y` and `B : Y ⊗ X` and produces `A*B : Z ⊗ X`
 -/
class TensorProductTranpose
  (R Y X YX XY : Type*) [RCLike R]
  [NormedAddCommGroup Z] [AdjointSpace R Z] [NormedAddCommGroup Y] [AdjointSpace R Y] [NormedAddCommGroup X] [AdjointSpace R X]
  [AddCommGroup YX] [Module R YX] [AddCommGroup XY] [Module R XY]
  [TensorProductType R Y X YX] [TensorProductType R X Y XY]
  where

    /-- Matrix transposition/conjugation
    ```
    transpose A = Aᵀ  or  Aᴴ
    ```

    The type signature is the same as of `gemm` BLAS function.
    -/
    conjTranspose (A : YX) : XY
