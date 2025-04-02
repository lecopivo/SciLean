import SciLean.Data.DataArray.Operations

import SciLean.AD.Rules.Common
import SciLean.AD.Rules.DataArrayN.Minor
import SciLean.AD.Rules.IndexType.Sum

namespace SciLean

set_option linter.unusedTactic false

open DataArrayN


data_synth_variable [BLAS (DataArray R) R R]



def_data_synth DataArrayN.det in A : HasFwdFDeriv R by
  apply hasFwdFDeriv_nat_induction n
  case zero =>
    simp[DataArrayN.det]; data_synth
  case succ =>
    intro n fn' hfn'
    simp -zeta [DataArrayN.det]
    data_synth => enter[3]; lsimp


attribute [local data_synth high]
  IndexType.sum.arg_f.HasRevFDeriv_rule_scalar
  IndexType.sum.arg_f.HasRevFDerivUpdate_rule_scalar


def_data_synth DataArrayN.det in A : HasRevFDeriv R by
  apply hasRevFDeriv_nat_induction n
  case zero =>
    simp[DataArrayN.det]; data_synth
  case succ =>
    intro n fn' hfn'
    simp -zeta [DataArrayN.det]
    data_synth => enter[3]; lsimp


def_data_synth DataArrayN.det in A : HasRevFDerivUpdate R by
  apply hasRevFDerivUpdate_nat_induction n
  case zero =>
    simp[DataArrayN.det]; data_synth
  case succ =>
    intro n fn' hfn'
    simp -zeta [DataArrayN.det]
    data_synth => enter[3]; lsimp
