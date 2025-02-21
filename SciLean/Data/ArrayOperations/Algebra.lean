import SciLean.Data.ArrayOperations.Basic
import SciLean.Analysis.AdjointSpace.Basic
import SciLean.Analysis.AdjointSpace.Adjoint

namespace SciLean

class IsZeroGetElem (X I : Type*) {Y : outParam Type*} [GetElem X I Y (fun _ _ => True)]
   [Zero X] [Zero Y] : Prop where
  getElem_zero  (i : I) : (0 : X)[i] = 0

class IsAddGetElem (X I : Type*) {Y : outParam Type*} [GetElem X I Y (fun _ _ => True)]
   [Add X] [Add Y] : Prop where
  getElem_add (x x' : X) (i : I) : (x + x')[i] = x[i] + x'[i]

class IsNegGetElem (X I : Type*) {Y : outParam Type*} [GetElem X I Y (fun _ _ => True)]
   [Neg X] [Neg Y] : Prop where
  getElem_neg (x : X) (i : I) : (-x)[i] = -x[i]

class IsSMulGetElem (𝕜 X I : Type*) {Y : outParam Type*} [GetElem X I Y (fun _ _ => True)]
   [SMul 𝕜 X] [SMul 𝕜 Y] : Prop where
  getElem_smul (c : 𝕜) (x : X) (i : I) : (c • x)[i] = c • x[i]

class IsInnerGetElem (𝕜 X I : Type*) {Y : outParam Type*} [GetElem X I Y (fun _ _ => True)]
    [Zero 𝕜] [Add 𝕜] [IndexType I] [Inner 𝕜 X] [Inner 𝕜 Y] : Prop where
  inner_eq_sum_getElem (x x' : X) : ⟪x,x'⟫[𝕜] = ∑ (i : I), ⟪x[i],x'[i]⟫[𝕜]

export IsZeroGetElem (getElem_zero)
export IsAddGetElem (getElem_add)
export IsNegGetElem (getElem_neg)
export IsSMulGetElem (getElem_smul)
export IsInnerGetElem (inner_eq_sum_getElem)

attribute [simp, simp_core] getElem_zero getElem_add getElem_neg getElem_smul

class IsModuleGetElem (𝕜 X I : Type*) {Y : outParam Type*} [GetElem X I Y (fun _ _ => True)]
    [Ring 𝕜] [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
  extends
    IsZeroGetElem X I,
    IsAddGetElem X I,
    IsNegGetElem X I,
    IsSMulGetElem 𝕜 X I : Prop

class IsContinuousGetElem (X I : Type*) {Y : outParam Type*} [GetElem X I Y (fun _ _ => True)]
    [TopologicalSpace X] [TopologicalSpace Y] : Prop where
  continuous_getElem (i : I) : Continuous (fun x : X => x[i])

export IsContinuousGetElem (continuous_getElem)
attribute [fun_prop] continuous_getElem
