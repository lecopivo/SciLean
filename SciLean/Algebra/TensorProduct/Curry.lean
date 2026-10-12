module

public import SciLean.Algebra.TensorProduct.Basic
public import SciLean.Analysis.AdjointSpace.CanonicalBasis

@[expose] public section


namespace SciLean

-- class TensorProductCurry (𝕜 X Y Z : Type*)
--     [RCLike 𝕜]
--     [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
--     [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
--     [NormedAddCommGroup Z] [AdjointSpace 𝕜 Z]
--     {XY : Type*} [NormedAddCommGroup XY] [AdjointSpace 𝕜 XY]
--     [TensorProductType 𝕜 X Y XY]
--   where
--   tcurry : (X ⊗[𝕜] Y →L[𝕜] Z) ≃L[𝕜] (X →L[𝕜] Y →L[𝕜] Z)

-- export TensorProductCurry (tcurry)

-- class TensorBasis (𝕜 X Y XY : Type*)
--     [RCLike 𝕜] [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
--     [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
--     {XY : Type*} [NormedAddCommGroup XY] [AdjointSpace 𝕜 XY] [TensorProductType 𝕜 X Y XY]
--     {I} [Fintype I] [CanonicalBasis I 𝕜 X]
--     {J} [Fintype J] [CanonicalBasis J 𝕜 Y]
--     [CanonicalBasis (I×J) 𝕜 XY] : Prop where
--   basis_eq_tmul_basis : ∀ i j, ⅇ[𝕜,XY,(i,j)] = ⅇ[𝕜,X,i] ⊗[𝕜] ⅇ[𝕜,Y,j]


-- variable
--     {𝕜 X Y Z W : Type*}
--     [RCLike 𝕜]
--     [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
--     [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
--     [NormedAddCommGroup Z] [AdjointSpace 𝕜 Z]
--     [NormedAddCommGroup W] [AdjointSpace 𝕜 W]
--     {XY : Type*} [NormedAddCommGroup XY] [AdjointSpace 𝕜 XY] [TensorProductType 𝕜 X Y XY]
--     {YX : Type*} [NormedAddCommGroup YX] [AdjointSpace 𝕜 YX] [TensorProductType 𝕜 Y X YX]
--     {ZW : Type*} [NormedAddCommGroup ZW] [AdjointSpace 𝕜 ZW] [TensorProductType 𝕜 Z W ZW]
--     {I} [Fintype I] [CanonicalBasis I 𝕜 X]
--     {J} [Fintype J] [CanonicalBasis J 𝕜 Y]
--     [CanonicalBasis (I×J) 𝕜 XY] [TensorBasis 𝕜 X Y XY]


-- @[fun_prop]
-- theorem tmul.arg_xy.Continuous_rule : Continuous (fun xy : X×Y => xy.1⊗[𝕜]xy.2) := sorry_proof
-- @[fun_prop]
-- theorem tmul.arg_x.IsContinuousLinearMap_rule (y : Y) : IsContinuousLinearMap 𝕜 (fun x : X => x⊗[𝕜]y) := sorry_proof
-- @[fun_prop]
-- theorem tmul.arg_y.IsContinuousLinearMap_rule (x : X) : IsContinuousLinearMap 𝕜 (fun y : Y => x⊗[𝕜]y) := sorry_proof


-- set_default_scalar 𝕜

-- -- noncomputable
-- -- def tcurry : (X ⊗[𝕜] Y →L[𝕜] Z) ≃L[𝕜] (X →L[𝕜] Y →L[𝕜] Z) where
-- --   toFun := fun f => fun x =>L[𝕜] fun y =>L[𝕜] f (x⊗y)
-- --   invFun := fun f => fun xy =>L[𝕜] ∑ (i : I) (j : J), ⟪ⅇ'[X,i]⊗ⅇ'[Y,j], xy⟫ • f ⅇ[X,i] ⅇ[Y,j]
-- --   map_add' := sorry_proof
-- --   map_smul' := sorry_proof
-- --   left_inv := sorry_proof
-- --   right_inv := sorry_proof
-- --   continuous_toFun := by sorry_proof
-- --   continuous_invFun := by sorry_proof



-- def tcurry (f : X ⊗[𝕜] Y → Z) (x : X) (y : Y) : Z := f (x⊗y)


-- /--
-- Uncurry bilinear map `f : X → Y → Z` to a linear map over tensor product `X ⊗ Y`

-- It is marker as noncomputable as it is too slow to compute.
-- -/
-- noncomputable
-- def tuncurry (f : X → Y → Z) (xy : X⊗Y) : Z := ∑ (i : I) (j : J), ⟪ⅇ[X,i]⊗ⅇ[Y,j], xy⟫ • f ⅇ[X,i] ⅇ[Y,j]

-- /--
-- Combine two linear maps to a single linear map over the tensor product of its domains and codomains.

-- It is marker as noncomputable as it is too slow to compute.
-- -/
-- noncomputable
-- def tmap (f : X → Z) (g : Y → W) (xy : X⊗Y) : Z⊗W :=
--   ∑ (i : I) (j : J), ⟪ⅇ'[X,i]⊗ⅇ'[Y,j], xy⟫ • (f ⅇ[X,i] ⊗ g ⅇ[Y,j])
