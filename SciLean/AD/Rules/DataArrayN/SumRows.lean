module

public import SciLean.Data.DataArray.TensorOperations
public import SciLean.Data.ArrayOperations.Operations.GetElem

public import SciLean.AD.Rules.Common

public import SciLean.AD.Rules.DataArrayN.ToRn
public import SciLean.AD.Rules.DataArrayN.FromRn
public import SciLean.AD.Rules.DataArrayN.Reshape
public import SciLean.AD.Rules.DataArrayN.SumMiddleR

@[expose] public section


namespace SciLean

set_option linter.unusedTactic false

open DataArrayN



def_fun_prop DataArrayN.sumRows in x with_transitive : IsContinuousLinearMap R by
  unfold DataArrayN.sumRows
  fun_prop

#generate_linear_map_simps sumRows.arg_x.IsLinearMap_rule

abbrev_data_synth DataArrayN.sumRows in x (x₀ : X^[I,J]) : (HasFDerivAt (𝕜:=R) · · x₀) by hasFDerivAt_from_linear
abbrev_data_synth DataArrayN.sumRows in x : HasFwdFDeriv R by hasFwdFDeriv_from_def => simp
abbrev_data_synth DataArrayN.sumRows in x : (HasAdjoint R · (fun x => replicateCol J x)) by sorry_proof
abbrev_data_synth DataArrayN.sumRows in x : (HasAdjointUpdate R · (fun x xs' => xs'.scalAddCols 1 x)) by sorry_proof
abbrev_data_synth DataArrayN.sumRows in x : HasRevFDeriv R by hasRevFDeriv_from_def => skip
abbrev_data_synth DataArrayN.sumRows in x : HasRevFDerivUpdate R by hasRevFDerivUpdate_from_def => skip
