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


def_fun_prop DataArrayN.sum in x
    with_transitive
    [NormedAddCommGroup X] [AdjointSpace R X]
    /- todo: add compatibility condition between `X` and `R^[ι]` -/ :
    IsContinuousLinearMap R by
  unfold DataArrayN.sum
  fun_prop

#generate_linear_map_simps sum.arg_x.IsLinearMap_rule

-- todo: add compatibility condition between `X` and `R^[ι
data_synth_variable [NormedAddCommGroup X] [AdjointSpace R X]

abbrev_data_synth DataArrayN.sum in x (x₀ : X^[I]) : (HasFDerivAt (𝕜:=R) · · x₀) by hasFDerivAt_from_linear
abbrev_data_synth DataArrayN.sum in x : HasFwdFDeriv R by hasFwdFDeriv_from_def => simp
abbrev_data_synth DataArrayN.sum in x : (HasAdjoint R · (fun x => replicate I x)) by  sorry_proof
abbrev_data_synth DataArrayN.sum in x : (HasAdjointUpdate R · (fun x xs' => xs'.scalAdd 1 x)) by sorry_proof
abbrev_data_synth DataArrayN.sum in x : HasRevFDeriv R by hasRevFDeriv_from_def => skip
abbrev_data_synth DataArrayN.sum in x : HasRevFDerivUpdate R by hasRevFDerivUpdate_from_def => skip
