import SciLean.Data.DataArray.Operations.Diag

namespace SciLean

open DataArrayN

def_fun_prop trace in A
    with_transitive
    [RealScalar R] : IsContinuousLinearMap R by
  unfold trace;
  sorry_proof

#generate_linear_map_simps DataArrayN.trace.arg_A.IsLinearMap_rule

-- todo: change to abbrev_def_trans
def_fun_trans trace in A : fderiv R by autodiff

-- todo: change to abbrev_def_trans
def_fun_trans trace in A : fwdFDeriv R by autodiff

-- todo: change to abbrev_def_trans
def_fun_trans trace in A [DecidableEq I] : adjoint R by
  equals (fun x => x• Matrix.identity) =>
    funext x
    apply AdjointSpace.ext_inner_left R
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[DataArrayN.inner_def,Function.uncurry,
         DataArrayN.trace,Matrix.identity, sum_pull, sum_over_prod, sum_ite']

-- todo: change to abbrev_def_trans
def_fun_trans trace in A : revFDeriv R by unfold revFDeriv; autodiff
