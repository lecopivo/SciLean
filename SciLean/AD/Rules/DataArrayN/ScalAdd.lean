module

public import SciLean.Data.DataArray.TensorOperations
public import SciLean.Data.ArrayOperations.Operations.GetElem

public import SciLean.AD.Rules.Common

@[expose] public section


namespace SciLean

set_option linter.unusedTactic false

open DataArrayN

def_fun_prop scalAdd in x r
    with_transitive
    [BLAS (DataArray R) R R] [NormedAddCommGroup X] [AdjointSpace R X]
    /- todo: add compatibility condition between `X` and `R^[ι]` -/ :
    IsContinuousLinearMap R by
  unfold scalAdd
  sorry_proof

-- todo: add compatibility condition between `X` and `R^[ι
data_synth_variable [BLAS (DataArray R) R R] [NormedAddCommGroup X] [AdjointSpace R X]

abbrev_data_synth scalAdd in x r (x₀ : X^[I]×X) : (HasFDerivAt (𝕜:=R) · · x₀) by hasFDerivAt_from_linear
abbrev_data_synth scalAdd in x r : HasFwdFDeriv R by hasFwdFDeriv_from_def => simp
abbrev_data_synth scalAdd in x r : (HasAdjoint R · (fun z => (z,a•z.sum))) by sorry_proof
abbrev_data_synth scalAdd in x r : HasAdjointUpdate R by hasAdjointUpdate_from_adjoint => skip
abbrev_data_synth scalAdd in x r : HasRevFDeriv R by hasRevFDeriv_from_def => skip
abbrev_data_synth scalAdd in x r : HasRevFDerivUpdate R by hasRevFDerivUpdate_from_def => simp[Prod.add_def]

-- todo: add compatibility condition between `X` and `R^[ι
