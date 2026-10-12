module

public import SciLean.Algebra.TensorProduct.Basic

@[expose] public section


namespace SciLean

-- class TensorProductSwap (𝕜 X Y : Type*)
--     [RCLike 𝕜]
--     [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
--     [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
--     {XY : Type*} [NormedAddCommGroup XY] [AdjointSpace 𝕜 XY]
--     {YX : Type*} [NormedAddCommGroup YX] [AdjointSpace 𝕜 YX]
--     [TensorProductType 𝕜 X Y XY] [TensorProductType 𝕜 Y X YX]
--   where
--   tswap : (X ⊗[𝕜] Y) ≃L[𝕜] (Y ⊗[𝕜] X)


-- -- export TensorProductSwap (tswap)


-- def tswap {𝕜 X Y : Type*}
--     [RCLike 𝕜]
--     [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
--     [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
--     {XY : Type*} [NormedAddCommGroup XY] [AdjointSpace 𝕜 XY]
--     {YX : Type*} [NormedAddCommGroup YX] [AdjointSpace 𝕜 YX]
--     [TensorProductType 𝕜 X Y XY] [TensorProductGetRXY 𝕜 X Y XY]
--     [TensorProductType 𝕜 Y X YX]
--     [ts : TensorProductSwap 𝕜 X Y] :
--     X ⊗[𝕜] Y →L[𝕜] Y ⊗[𝕜] X := ts.tswap
