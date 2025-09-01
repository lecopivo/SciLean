import SciLean.Data.ArrayOperations.Basic
import SciLean.Analysis.AdjointSpace.Basic
import SciLean.Analysis.AdjointSpace.Adjoint
import SciLean.Data.IndexType.Basic
import SciLean.Data.IndexType.Fold
import SciLean.Data.IndexType.Operations

namespace SciLean

class IsZeroGetElem (X I : Type*) {Y : outParam Type*} [GetElem' X I Y]
   [Zero X] [Zero Y] : Prop where
  getElem_zero  (i : I) : (0 : X)[i] = 0

class IsAddGetElem (X I : Type*) {Y : outParam Type*} [GetElem' X I Y]
   [Add X] [Add Y] : Prop where
  getElem_add (x x' : X) (i : I) : (x + x')[i] = x[i] + x'[i]

class IsNegGetElem (X I : Type*) {Y : outParam Type*} [GetElem' X I Y]
   [Neg X] [Neg Y] : Prop where
  getElem_neg (x : X) (i : I) : (-x)[i] = -x[i]

class IsSMulGetElem (𝕜 X I : Type*) {Y : outParam Type*} [GetElem' X I Y]
   [SMul 𝕜 X] [SMul 𝕜 Y] : Prop where
  getElem_smul (c : 𝕜) (x : X) (i : I) : (c • x)[i] = c • x[i]

class IsInnerGetElem (𝕜 X I : Type*) {Y : outParam Type*} [GetElem' X I Y]
    [AddCommMonoid 𝕜] {n} [IndexType I n] [Inner 𝕜 X] [Inner 𝕜 Y] : Prop where
  inner_eq_sum_getElem (x x' : X) : ⟪x,x'⟫[𝕜] = Finset.univ.sum fun (i : I) => ⟪x[i],x'[i]⟫[𝕜]

export IsZeroGetElem (getElem_zero)
export IsAddGetElem (getElem_add)
export IsNegGetElem (getElem_neg)
export IsSMulGetElem (getElem_smul)
export IsInnerGetElem (inner_eq_sum_getElem)

attribute [simp, simp_core] getElem_zero getElem_add getElem_neg getElem_smul

class IsModuleGetElem (𝕜 : outParam Type*) (X I : Type*) {Y : outParam Type*} [GetElem' X I Y]
    [Ring 𝕜] [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y] : Prop
  extends
    IsZeroGetElem X I,
    IsAddGetElem X I,
    IsNegGetElem X I,
    IsSMulGetElem 𝕜 X I

class IsContinuousGetElem (X I : Type*) {Y : outParam Type*} [GetElem' X I Y]
    [TopologicalSpace X] [TopologicalSpace Y] : Prop where
  continuous_getElem (i : I) : Continuous (fun x : X => x[i])

export IsContinuousGetElem (continuous_getElem)
attribute [fun_prop] continuous_getElem


-- ----------------------------------------------------------------------------------------------------
-- -- (Un)curry elements ------------------------------------------------------------------------------
-- ----------------------------------------------------------------------------------------------------

-- instance {X Y Z I J}
--     [GetElem' X I Y] [GetElem' X (I×J) Z]
--     [GetElem' Y J Z] [IsGetElemCurry X I J]
--     [Zero X] [Zero Y] [Zero Z]
--     [IsZeroGetElem X I] [IsZeroGetElem Y J] :
--     IsZeroGetElem X (I×J) where
--   getElem_zero := by simp[getElem_curry]

-- instance {X Y Z I J}
--     [DefaultIndex Y J]
--     [GetElem' X I Y] [GetElem' X (I×J) Z]
--     [GetElem' Y J Z] [InjectiveGetElem Y J] [IsGetElemCurry X I J]
--     [Zero X] [Zero Y] [Zero Z]
--     [IsZeroGetElem X (I×J)] [IsZeroGetElem Y J] :
--     IsZeroGetElem X I where
--   getElem_zero := by intro i; apply getElem_injective (idx:=J); simp[getElem_uncurry]

-- instance {X Y Z I J}
--     [GetElem' X I Y] [GetElem' X (I×J) Z]
--     [GetElem' Y J Z] [IsGetElemCurry X I J]
--     [Add X] [Add Y] [Add Z]
--     [IsAddGetElem X I] [IsAddGetElem Y J] :
--     IsAddGetElem X (I×J) where
--   getElem_add := by simp[getElem_curry]

-- instance {X Y Z I J}
--     [DefaultIndex Y J]
--     [GetElem' X I Y] [GetElem' X (I×J) Z]
--     [GetElem' Y J Z] [InjectiveGetElem Y J] [IsGetElemCurry X I J]
--     [Add X] [Add Y] [Add Z]
--     [IsAddGetElem X (I×J)] [IsAddGetElem Y J] :
--     IsAddGetElem X I where
--   getElem_add := by intro x x' i; apply getElem_injective (idx:=J); simp[getElem_uncurry]

-- instance {X Y Z I J}
--     [GetElem' X I Y] [GetElem' X (I×J) Z]
--     [GetElem' Y J Z] [IsGetElemCurry X I J]
--     [Neg X] [Neg Y] [Neg Z]
--     [IsNegGetElem X I] [IsNegGetElem Y J] :
--     IsNegGetElem X (I×J) where
--   getElem_neg := by simp[getElem_curry]

-- instance {X Y Z I J}
--     [DefaultIndex Y J]
--     [GetElem' X I Y] [GetElem' X (I×J) Z]
--     [GetElem' Y J Z] [InjectiveGetElem Y J] [IsGetElemCurry X I J]
--     [Neg X] [Neg Y] [Neg Z]
--     [IsNegGetElem X (I×J)] [IsNegGetElem Y J] :
--     IsNegGetElem X I where
--   getElem_neg := by intro x i; apply getElem_injective (idx:=J); simp[getElem_uncurry]

-- instance {X Y Z I J 𝕜}
--     [GetElem' X I Y] [GetElem' X (I×J) Z]
--     [GetElem' Y J Z] [IsGetElemCurry X I J]
--     [SMul 𝕜 X] [SMul 𝕜 Y] [SMul 𝕜 Z]
--     [IsSMulGetElem 𝕜 X I] [IsSMulGetElem 𝕜 Y J] :
--     IsSMulGetElem 𝕜 X (I×J) where
--   getElem_smul := by simp[getElem_curry]

-- instance {X Y Z I J 𝕜}
--     [DefaultIndex Y J]
--     [GetElem' X I Y] [GetElem' X (I×J) Z]
--     [GetElem' Y J Z] [InjectiveGetElem Y J] [IsGetElemCurry X I J]
--     [SMul 𝕜 X] [SMul 𝕜 Y] [SMul 𝕜 Z]
--     [IsSMulGetElem 𝕜 X (I×J)] [IsSMulGetElem 𝕜 Y J] :
--     IsSMulGetElem 𝕜 X I where
--   getElem_smul := by intro c x i; apply getElem_injective (idx:=J); simp[getElem_uncurry]

-- instance {X Y Z I J 𝕜}
--     [GetElem' X I Y] [GetElem' X (I×J) Z]
--     [GetElem' Y J Z] [IsGetElemCurry X I J]
--     [Zero 𝕜] [Add 𝕜] {nI} [IndexType I nI] [Fold I] {nJ} [IndexType J nJ] [Fold J]
--     [Inner 𝕜 X] [Inner 𝕜 Y] [Inner 𝕜 Z]
--     [IsInnerGetElem 𝕜 X I] [IsInnerGetElem 𝕜 Y J] :
--     IsInnerGetElem 𝕜 X (I×J) where
--   inner_eq_sum_getElem := by
--     simp [inner_eq_sum_getElem (I:=I), inner_eq_sum_getElem (I:=J), getElem_curry]
--     sorry_proof -- just split the sum over the product into two

-- instance {X Y Z I J 𝕜}
--     [DefaultIndex Y J]
--     [GetElem' X I Y] [GetElem' X (I×J) Z]
--     [GetElem' Y J Z] [IsGetElemCurry X I J]
--     [Zero 𝕜] [Add 𝕜] {nI} [IndexType I nI] [Fold I] {nJ} [IndexType J nJ] [Fold J]
--     [Inner 𝕜 X] [Inner 𝕜 Y] [Inner 𝕜 Z]
--     [IsInnerGetElem 𝕜 X (I×J)] [IsInnerGetElem 𝕜 Y J] :
--     IsInnerGetElem 𝕜 X I where
--   inner_eq_sum_getElem := by
--     simp [inner_eq_sum_getElem (I:=(I×J)), inner_eq_sum_getElem (I:=J), getElem_curry]
--     sorry_proof -- just split the sum over the product into two

-- instance {X Y Z I J 𝕜}
--     [GetElem' X I Y] [GetElem' X (I×J) Z]
--     [GetElem' Y J Z] [IsGetElemCurry X I J] [Ring 𝕜]
--     [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y] [AddCommGroup Z] [Module 𝕜 Z]
--     [IsModuleGetElem 𝕜 X I] [IsModuleGetElem 𝕜 Y J]  :
--     IsModuleGetElem 𝕜 X (I×J) where

-- instance {X Y Z I J 𝕜}
--     [DefaultIndex Y J]
--     [GetElem' X I Y] [GetElem' X (I×J) Z]
--     [GetElem' Y J Z] [InjectiveGetElem Y J] [IsGetElemCurry X I J] [Ring 𝕜]
--     [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y] [AddCommGroup Z] [Module 𝕜 Z]
--     [IsModuleGetElem 𝕜 X (I×J)] [IsModuleGetElem 𝕜 Y J]  :
--     IsModuleGetElem 𝕜 X I where


-- -- I'm having some serious issues with interaction of `IsContinuousGetElem` and `VectorType.Base` :(
-- instance {X Y I} [GetElem' X I Y]
--     [TopologicalSpace X] [TopologicalSpace Y] :
--     IsContinuousGetElem X I where
--   continuous_getElem := sorry_proof

-- -- instance {X Y Z I J}
-- --     [GetElem' X I Y] [GetElem' X (I×J) Z]
-- --     [GetElem' Y J Z] [IsGetElemCurry X I J]
-- --     [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
-- --     [IsContinuousGetElem X I] [IsContinuousGetElem Y J] :
-- --     IsContinuousGetElem X (I×J) where
-- --   continuous_getElem := by simp[getElem_curry]; fun_prop

-- -- instance {X Y Z I J}
-- --     [DefaultIndex Y J]
-- --     [GetElem' X I Y] [GetElem' X (I×J) Z]
-- --     [GetElem' Y J Z] [IsGetElemCurry X I J]
-- --     [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
-- --     [IsContinuousGetElem X (I×J)] [IsContinuousGetElem Y J] :
-- --     IsContinuousGetElem X I where
-- --   continuous_getElem := by
-- --     -- not sure what exact assumptions are needed
-- --     -- this is somehow connected to the problem that we want `ofFn` to be continuous
-- --     sorry_proof
