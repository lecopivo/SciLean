module

public import SciLean.Data.DataArray.TensorOperations
public import SciLean.Data.ArrayOperations.Operations.GetElem

public import SciLean.AD.Rules.Common
public import SciLean.AD.Rules.DataArrayN.ToRn

@[expose] public section


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
abbrev_data_synth fromRn in x : (HasAdjoint R · toRn) by
  constructor
  case adjoint =>
    intro x y
    have h : HasAdjoint R (fun y : X => toRn y) (fun x : R^[I] => fromRn x) := by data_synth
    rw [← AdjointSpace.conj_symm, ← h.adjoint, AdjointSpace.conj_symm]
  case is_linear => fun_prop
abbrev_data_synth fromRn in x : HasAdjointUpdate R by hasAdjointUpdate_from_adjoint => skip
abbrev_data_synth fromRn in x : HasRevFDeriv R by hasRevFDeriv_from_def => skip
abbrev_data_synth fromRn in x : HasRevFDerivUpdate R by hasRevFDerivUpdate_from_def => skip
