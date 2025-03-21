import SciLean.Data.DataArray.TensorOperations
import SciLean.Data.ArrayOperations.Operations.GetElem

import SciLean.AD.Rules.Common

set_option linter.unusedTactic false

namespace SciLean

open DataArrayN


def_fun_prop toRn in x
    with_transitive
    [BLAS (DataArray R) R R] [NormedAddCommGroup X] [AdjointSpace R X]
    /- todo: add compatibility condition between `X` and `R^[ι]` -/ :
    IsContinuousLinearMap R by
  sorry_proof

#generate_linear_map_simps SciLean.toRn.arg_x.IsLinearMap_rule

/- todo: add compatibility condition between `X` and `R^[ι]` -/
data_synth_variable [BLAS (DataArray R) R R] [NormedAddCommGroup X] [AdjointSpace R X]

abbrev_data_synth toRn in x (x₀ : X) : (HasFDerivAt (𝕜:=R) · · x₀) by hasFDerivAt_from_linear
abbrev_data_synth toRn in x : HasFwdFDeriv R by hasFwdFDeriv_from_def => simp
abbrev_data_synth toRn in x : (HasAdjoint R · fromRn) by  sorry_proof
abbrev_data_synth toRn in x : HasAdjointUpdate R by hasAdjointUpdate_from_adjoint => skip
abbrev_data_synth toRn in x : HasRevFDeriv R by hasRevFDeriv_from_def => skip
abbrev_data_synth toRn in x : HasRevFDerivUpdate R by hasRevFDerivUpdate_from_def => skip
