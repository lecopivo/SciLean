import SciLean.Algebra.TensorProduct.Basic

namespace SciLean

class TensorProductCurry (𝕜 X Y Z : Type*)
    [RCLike 𝕜]
    [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
    [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
    [NormedAddCommGroup Z] [AdjointSpace 𝕜 Z]
    {XY : Type*} [NormedAddCommGroup XY] [AdjointSpace 𝕜 XY]
    [TensorProductType 𝕜 X Y XY] [TensorProductGetYX 𝕜 X Y XY]
  where
  tcurry : (X ⊗[𝕜] Y →L[𝕜] Z) ≃L[𝕜] (X →L[𝕜] Y →L[𝕜] Z)

export TensorProductCurry (tcurry)
