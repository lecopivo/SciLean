import SciLean.Data.DataArray.TensorOperations
import SciLean.Data.ArrayOperations.Operations.GetElem

import SciLean.AD.Rules.Common

set_option linter.unusedTactic false

namespace SciLean

open DataArrayN

def_fun_prop fromRn in x
    with_transitive
    [BLAS (DataArray R) R R] [NormedAddCommGroup X] [AdjointSpace R X]
    /- todo: add compatibility condition between `X` and `R^[ι]` -/ :
    IsContinuousLinearMap R by
  sorry_proof

#generate_linear_map_simps SciLean.fromRn.arg_x.IsLinearMap_rule

/- todo: add compatibility condition between `X` and `R^[ι]` -/
data_synth_variable [BLAS (DataArray R) R R] [NormedAddCommGroup X] [AdjointSpace R X]

abbrev_data_synth fromRn in x (x₀ : R^[I]) : (HasFDerivAt (𝕜:=R) · · x₀) by hasFDerivAt_from_linear
abbrev_data_synth fromRn in x :  HasFwdFDeriv R by hasFwdFDeriv_from_def => simp
abbrev_data_synth fromRn in x : (HasAdjoint R · toRn) by sorry_proof
abbrev_data_synth fromRn in x : HasAdjointUpdate R by hasAdjointUpdate_from_adjoint => skip
abbrev_data_synth fromRn in x : HasRevFDeriv R by hasRevFDeriv_from_def => skip
abbrev_data_synth fromRn in x : HasRevFDerivUpdate R by hasRevFDerivUpdate_from_def => skip
