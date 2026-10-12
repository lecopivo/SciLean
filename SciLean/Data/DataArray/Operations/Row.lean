module

public import SciLean.Data.DataArray.Operations.Curry
public import SciLean.Data.ArrayOperations.Operations.GetElem

@[expose] public section



namespace SciLean.DataArrayN


data_array_fun_prop row X R in x : IsLinearMap R by unfold row; fun_prop
data_array_fun_prop row X R in x : Continuous by unfold row; fun_prop
data_array_fun_prop row X R in x : IsContinuousLinearMap R by constructor <;> fun_prop
data_array_fun_prop row X R in x : Differentiable R by fun_prop


data_array_data_synth_abbrev DataArrayN.row X R in x (x₀) : (HasFDerivAt (𝕜:=R) · · x₀) by
  apply hasFDerivAt_from_isContinuousLinearMap
  fun_prop

data_array_data_synth_abbrev DataArrayN.row X R in x : HasFwdFDeriv R by
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intros; data_synth
  case simp => intros; simp; rfl

data_array_data_synth_abbrev DataArrayN.row X R in x : HasAdjoint R by
  unfold row
  data_synth => skip

data_array_data_synth_abbrev DataArrayN.row X R in x : HasAdjointUpdate R by
  conv => enter[3]; assign (fun (x : X^[J]) (A : X^[I,J]) =>
                             let A := A.curry
                             let ai := A[i]
                             let A := (setElem A i (ai + x) .intro).uncurry
                             A)
  apply hasAdjointUpdate_from_hasAdjoint
  case adjoint => data_synth
  case simp =>
    intro y A; simp
    have h1 : setElem A.curry i (A.curry[i] + y) .intro = A.curry + setElem 0 i y .intro := by
      ext i' : 1
      by_cases h : i' = i
      · simp [h]
      · simp [getElem_setElem_neq _ _ _ _ _ _ (Ne.symm h)]
    have h2 : ∀ B : X^[I,J], B.curry.uncurry = B := by simp [curry, uncurry]
    have h3 : ∀ B : X^[J]^[I], B.uncurry.curry = B := by simp [curry, uncurry]
    rw [h1, ← h2 (A + _), (curry.arg_x.IsLinearMap_rule (R:=R)).map_add, h3]

data_array_data_synth_abbrev DataArrayN.row X R in x : HasRevFDeriv R by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intros; data_synth
  case adjoint => intros; simp; data_synth
  case simp => rfl

data_array_data_synth_abbrev DataArrayN.row X R in x : HasRevFDerivUpdate R by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intros; data_synth
  case adjoint => intros; simp; data_synth
  case simp => rfl
