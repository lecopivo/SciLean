import SciLean.Core
import SciLean.Data.DataArray.DataArray
import SciLean.Data.ArrayType

namespace SciLean

set_option linter.unusedVariables false

variable
  {K : Type u} [RCLike K]
  {ι κ} [Index ι] [Index κ]

section OnVec

variable
  {W : Type} [Vec K W]
  {X : Type} [Vec K X] [PlainDataType X]

example : Vec K (DataArrayN X ι) := by infer_instance

-- #generate DataArrayN.reshape x
--   assume {K : Type} [RCLike K] [Vec K α]
--   IsDifferentible by sorry_proof
--   IsLinearMap by sorry_proof
--   IsLinearMap_simps
--   IsSmoothLinearMap by constructor <;> fprop
--   cderiv by rw[cderiv.of_linear _ (by fprop)]
--   fwdCderiv by unfold cderiv; ftrans

-- #generate DataArrayN.reshape x
--   assume {K : Type} [RCLike K] [SemiInnerProductSpace K α]
--   HasAdjoint by sorry_proof
--   HasAdjDiff by constructor <;> fprop
--   semiAdjoint :=
--   revCDeriv by unfold revCDeriv; ftrans
--   revDeriv by unfold revCDeriv; ftrans

@[fprop]
theorem DataArrayN.reshape.arg_x.IsSmoothLinearMap_rule
  (x : W → DataArrayN X ι) (h : Index.size κ = Index.size ι) (hx : IsSmoothLinearMap K x)
  : IsSmoothLinearMap K (fun w => (x w).reshape κ h) := by sorry_proof

@[fprop]
theorem DataArrayN.reshape.arg_x.IsLinearMap_rule_simple
  (h : Index.size κ = Index.size ι)
  : IsLinearMap K (fun x : DataArrayN X ι => x.reshape κ h) := by
  have hx : IsSmoothLinearMap K (fun x : DataArrayN X ι => x.reshape κ h) := by fprop
  apply hx.1

#generate_linear_map_simps SciLean.DataArrayN.reshape.arg_x.IsLinearMap_rule_simple

#generate_fwdCDeriv DataArrayN.reshape x
  assume {K : Type} [RCLike K] [Vec K α]
  prop_by sorry_proof
  trans_by
    rw[fwdCDeriv.comp_rule K (DataArrayN.reshape · κ hs) x (by sorry_proof) (by fprop)]
    rw[fwdCDeriv.fwdCDeriv_of_linear (DataArrayN.reshape · κ hs) (by fprop)]
    ftrans
