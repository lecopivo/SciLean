import SciLean.Algebra.TensorProduct.Basic

namespace SciLean


/-- Class providing matrix-matrix multiplcation

This takes `A : Z ⊗ Y` and `B : Y ⊗ X` and produces `A*B : Z ⊗ X`
 -/
class TensorProductMul
  (R Z Y X ZY YX ZX : Type*) [RCLike R]
  [NormedAddCommGroup Z] [AdjointSpace R Z] [NormedAddCommGroup Y] [AdjointSpace R Y] [NormedAddCommGroup X] [AdjointSpace R X]
  [AddCommGroup ZY] [Module R ZY] [AddCommGroup YX] [Module R YX] [AddCommGroup ZX] [Module R ZX]
  [TensorProductType R Z Y ZY] [TensorProductType R Y X YX] [TensorProductType R Z X ZX]
  where

    /-- Matrix-matrix multiplication
    ```
    matMul a A B b C = a*A*B + b*C
    ```

    The type signature is the same as of `gemm` BLAS function.
    -/
    matMul (a : R) (A : ZY) (B : YX) (b : R) (C : ZX) : ZX
