import SciLean.Data.DataArray.TensorOperations
import SciLean.Data.ArrayOperations.Operations.GetElem

import SciLean.AD.Rules.Common

set_option linter.unusedTactic false

namespace SciLean

open DataArrayN

def_fun_prop sumMiddleR in x with_transitive : IsContinuousLinearMap R by
  sorry_proof

#generate_linear_map_simps sumMiddleR.arg_x.IsLinearMap_rule

abbrev_data_synth sumMiddleR in x (x₀ : R^[I,J,K]) : (HasFDerivAt (𝕜:=R) · · x₀) by hasFDerivAt_from_linear
abbrev_data_synth sumMiddleR in x : HasFwdFDeriv R by hasFwdFDeriv_from_def => simp
abbrev_data_synth sumMiddleR in x : (HasAdjoint R · (replicateMiddleR J)) by sorry_proof
abbrev_data_synth sumMiddleR in x : (HasAdjointUpdate R · (fun y x' => x'.scalAddFstLastR 1 y)) by  sorry_proof
abbrev_data_synth sumMiddleR in x : HasRevFDeriv R by hasRevFDeriv_from_def => skip
abbrev_data_synth sumMiddleR in x : HasRevFDerivUpdate R by hasRevFDerivUpdate_from_def => skip
