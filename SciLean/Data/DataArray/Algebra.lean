import SciLean.Data.DataArray.RnEquiv
import SciLean.Data.ArrayOperations.Algebra

/-! Algebraic structure in `X^[I]`

This file automatically pulls algebraic structure of `R^[n]` onto `X^[I]` anytime `X` has
an instance of `HasRnEquiv X m R`.

TODO: There should be a class that the structure of.
-/

namespace SciLean


namespace DataArrayN

variable
  (X I Y : Type*)
  {nI} [IdxType I nI]
  [PlainDataType Y]
  [PlainDataType X]
  [DataArrayEquiv X I Y]
  {J nJ} [IdxType J nJ] -- uncurry index
  {K nK} [IdxType K nK] -- this will be the canonical index to get to the data
  {R} [RealScalar R] [PlainDataType R] [BLAS (DataArray R) R R]


-- Derive operations and algebraic structures in `X^[I]`
instance instNormedAddCommGroupInductive [HasRnEquiv X K R] :
    NormedAddCommGroup (X^[I]) := NormedAddCommGroup.ofRnEquiv (X^[I])

instance instAdjointSpaceInductive [HasRnEquiv X K R] :
    AdjointSpace R (X^[I]) := AdjointSpace.ofRnEquiv (X^[I])


-- short circuit instances
instance [HasRnEquiv X K R] : Add (X^[I]) := by infer_instance
instance [HasRnEquiv X K R] : Sub (X^[I]) := by infer_instance
instance [HasRnEquiv X K R] : Neg (X^[I]) := by infer_instance
instance [HasRnEquiv X K R] : SMul ℕ (X^[I]) := by infer_instance
instance [HasRnEquiv X K R] : SMul ℤ (X^[I]) := by infer_instance
instance [HasRnEquiv X K R] : SMul R (X^[I]) := by infer_instance
instance [HasRnEquiv X K R] : Inner R (X^[I]) := by infer_instance
instance [HasRnEquiv X K R] : AddCommGroup (X^[I]) := by infer_instance
instance [HasRnEquiv X K R] : Module R (X^[I]) := by infer_instance


example : Add (R^[I]) := by infer_instance
example : Add (R^[I,J]) := by infer_instance
example : Add (R^[J]^[I]) := by infer_instance
example : Add (R^[I]^[J]) := by infer_instance
example : Add (R^[I]^[J]^[I]) := by infer_instance
example : Add (R^[I]^[J]^[I]) := by infer_instance

example : SMul R (R^[I]) := by infer_instance
example : SMul R (R^[I,J]) := by infer_instance
example : SMul R (R^[J]^[I]) := by infer_instance
example : SMul R (R^[I]^[J]) := by infer_instance
example : SMul R (R^[I]^[J]^[I]) := by infer_instance
example : SMul R (R^[I]^[J]^[I]) := by infer_instance

----------------------------------------------------------------------------------------------------


-- IsZeroGetElem instances
instance instIsZeroGetElemInductive [HasRnEquiv X K R] :
    IsZeroGetElem (X^[J]^[I]) I where
  getElem_zero := by sorry_proof

instance  instIsZeroGetElemBase  : IsZeroGetElem (R^[I]) I := by sorry_proof

instance instIsZeroGetElemUncurry {L nL} [IdxType L nL]
    [HasRnEquiv X K R]
    {Y} [PlainDataType Y] [Zero Y]
    [DataArrayEquiv (X^[L]) J Y] [GetElem' (X^[L]) J Y]  [IsZeroGetElem (X^[L]) J] :
    IsZeroGetElem (X^[L]^[I]) (I × J) where
  getElem_zero := by intro ⟨i,j⟩; simp[getElem_curry]


example : IsZeroGetElem (R^[I]) I := by infer_instance
example : IsZeroGetElem (R^[I,J]) (I×J) := by infer_instance

-- set_option trace.Meta.synthInstance true in
example : IsZeroGetElem (R^[J]^[I]) (I×J) := by infer_instance
example : IsZeroGetElem (R^[I]^[J]) J := by infer_instance
example : IsZeroGetElem (R^[I]^[J]^[I]) (I) := by infer_instance
example : IsZeroGetElem (R^[I]^[J]^[I]) (I×J) := by infer_instance

----------------------------------------------------------------------------------------------------

-- IsAddGetElem instances
instance instIsAddGetElemInductive [HasRnEquiv X K R] :
    IsAddGetElem (X^[J]^[I]) I where
  getElem_add := by intro x x'; sorry_proof

instance instIsAddGetElemBase : IsAddGetElem (R^[I]) I := by sorry_proof

-- this has incorrect assumptions
instance instIsAddGetElemUncurry {L nL} [IdxType L nL]
    [HasRnEquiv X K R]
    {Y} [PlainDataType Y] [Add Y]
    [DataArrayEquiv (X^[L]) J Y] [GetElem' (X^[L]) J Y]  [IsAddGetElem (X^[L]) J] :
    IsAddGetElem (X^[L]^[I]) (I × J) where
  getElem_add := sorry_proof


example : IsAddGetElem (R^[I]) I := by infer_instance
example : IsAddGetElem (R^[I,J]) (I×J) := by infer_instance
example : IsAddGetElem (R^[J]^[I]) (I×J) := by infer_instance
example : IsAddGetElem (R^[I]^[J]) J := by infer_instance
example : IsAddGetElem (R^[I]^[J]^[I]) (I) := by infer_instance
example : IsAddGetElem (R^[I]^[J]^[I]) (I×J) := by infer_instance
example : IsAddGetElem (R^[I]^[J]^[I]) (I×J×I) := by infer_instance

----------------------------------------------------------------------------------------------------


-- IsNegGetElem instances
instance instIsNegGetElemInductive [HasRnEquiv X K R] :
    IsNegGetElem (X^[J]^[I]) I where
  getElem_neg := by sorry_proof

instance instIsNegGetElemBase : IsNegGetElem (R^[I]) I := by sorry_proof

instance instIsNegGetElemUncurry {L nL} [IdxType L nL]
    [HasRnEquiv X K R]
    {Y} [PlainDataType Y] [Neg Y]
    [DataArrayEquiv (X^[L]) J Y] [GetElem' (X^[L]) J Y]  [IsNegGetElem (X^[L]) J] :
    IsNegGetElem (X^[L]^[I]) (I × J) where
  getElem_neg := by intro ⟨i,j⟩; simp[getElem_curry]


example : IsNegGetElem (R^[I]) I := by infer_instance
example : IsNegGetElem (R^[I,J]) (I×J) := by infer_instance
example : IsNegGetElem (R^[J]^[I]) (I×J) := by infer_instance
example : IsNegGetElem (R^[I]^[J]) J := by infer_instance
example : IsNegGetElem (R^[I]^[J]^[I]) (I) := by infer_instance
example : IsNegGetElem (R^[I]^[J]^[I]) (I×J) := by infer_instance

----------------------------------------------------------------------------------------------------


-- IsSMulGetElem instances
instance instIsSMulGetElemInductive [HasRnEquiv X K R] :
    IsSMulGetElem R (X^[J]^[I]) I where
  getElem_smul := by sorry_proof

instance instIsSMulGetElemBase : IsSMulGetElem R (R^[I]) I := by sorry_proof

-- this has incorrect assumptions
instance instIsSMulGetElemUncurry {L nL} [IdxType L nL]
    [HasRnEquiv X K R]
    {Y} [PlainDataType Y] [SMul R Y]
    [DataArrayEquiv (X^[L]) J Y] [GetElem' (X^[L]) J Y]  [IsSMulGetElem R (X^[L]) J] :
    IsSMulGetElem R (X^[L]^[I]) (I × J) where
  getElem_smul := sorry_proof


example : IsSMulGetElem R (R^[I]) I := by infer_instance
example : IsSMulGetElem R (R^[I,J]) (I×J) := by infer_instance
example : IsSMulGetElem R (R^[J]^[I]) (I×J) := by infer_instance
example : IsSMulGetElem R (R^[I]^[J]) J := by infer_instance
example : IsSMulGetElem R (R^[I]^[J]^[I]) (I) := by infer_instance
example : IsSMulGetElem R (R^[I]^[J]^[I]) (I×J) := by infer_instance

----------------------------------------------------------------------------------------------------



-- IsInnerGetElem instances
instance instIsInnerGetElemInductive [HasRnEquiv X K R] :
    IsInnerGetElem R (X^[J]^[I]) I where
  inner_eq_sum_getElem := by sorry_proof

instance instIsInnerGetElemBase : IsInnerGetElem R (R^[I]) I := by sorry_proof

-- this has incorrect assumptions
instance instIsInnerGetElemUncurry {L nL} [IdxType L nL]
    [HasRnEquiv X K R]
    {Y} [PlainDataType Y] [Inner R Y]
    [DataArrayEquiv (X^[L]) J Y] [GetElem' (X^[L]) J Y]  [IsInnerGetElem R (X^[L]) J] :
    IsInnerGetElem R (X^[L]^[I]) (I × J) where
  inner_eq_sum_getElem := sorry_proof


example : IsInnerGetElem R (R^[I]) I := by infer_instance
example : IsInnerGetElem R (R^[I,J]) (I×J) := by infer_instance
example : IsInnerGetElem R (R^[J]^[I]) (I×J) := by infer_instance
example : IsInnerGetElem R (R^[I]^[J]) J := by infer_instance
example : IsInnerGetElem R (R^[I]^[J]^[I]) (I) := by infer_instance
example : IsInnerGetElem R (R^[I]^[J]^[I]) (I×J) := by infer_instance

----------------------------------------------------------------------------------------------------


-- IsModuleGetElem instances
instance instIsModuleGetElemInductive [HasRnEquiv X K R] :
    IsModuleGetElem R (X^[J]^[I]) I where

instance instIsModuleGetElemBase : IsModuleGetElem R (R^[I]) I := by sorry_proof

-- this has incorrect assumptions
instance instIsModuleGetElemUncurry {L nL} [IdxType L nL]
    [HasRnEquiv X K R]
    {Y} [PlainDataType Y] [AddCommGroup Y] [Module R Y]
    [DataArrayEquiv (X^[L]) J Y] [GetElem' (X^[L]) J Y]  [IsModuleGetElem R (X^[L]) J] :
    IsModuleGetElem R (X^[L]^[I]) (I × J) where

example : IsModuleGetElem R (R^[I]) I := by infer_instance
example : IsModuleGetElem R (R^[I,J]) (I×J) := by infer_instance
example : IsModuleGetElem R (R^[J]^[I]) (I×J) := by infer_instance
example : IsModuleGetElem R (R^[I]^[J]) J := by infer_instance
example : IsModuleGetElem R (R^[I]^[J]^[I]) (I) := by infer_instance
example : IsModuleGetElem R (R^[I]^[J]^[I]) (I×J) := by infer_instance

----------------------------------------------------------------------------------------------------



-- IsContinuousGetElem instances
instance instIsContinuousGetElemInductive [HasRnEquiv X K R] :
    IsContinuousGetElem (X^[J]^[I]) I where
  continuous_getElem := sorry_proof

instance instIsContinuousGetElemBase : IsContinuousGetElem (R^[I]) I := by sorry_proof

-- this has incorrect assumptions
instance instIsContinuousGetElemUncurry {L nL} [IdxType L nL]
    [HasRnEquiv X K R]
    {Y} [PlainDataType Y] [TopologicalSpace Y]
    [DataArrayEquiv (X^[L]) J Y] [GetElem' (X^[L]) J Y]  [IsContinuousGetElem (X^[L]) J] :
    IsContinuousGetElem (X^[L]^[I]) (I × J) where
  continuous_getElem := by intro ⟨i,j⟩; simp[getElem_curry]; fun_prop

example : IsContinuousGetElem (R^[I]) I := by infer_instance
example : IsContinuousGetElem (R^[I,J]) (I×J) := by infer_instance
example : IsContinuousGetElem (R^[J]^[I]) (I×J) := by infer_instance
example : IsContinuousGetElem (R^[I]^[J]) J := by infer_instance
example : IsContinuousGetElem (R^[I]^[J]^[I]) (I) := by infer_instance
example : IsContinuousGetElem (R^[I]^[J]^[I]) (I×J) := by infer_instance

----------------------------------------------------------------------------------------------------
