import SciLean.Data.DataArray.Operations.Diag

namespace SciLean

variable
  {I : Type*} [IndexType I] [DecidableEq I]
  {J : Type*} [IndexType J] [DecidableEq J]
  {R : Type*} [RealScalar R] [PlainDataType R]


open DataArrayN

def_fun_prop cross in x    with_transitive : IsContinuousLinearMap R by sorry_proof
def_fun_prop cross in y    with_transitive : IsContinuousLinearMap R by sorry_proof
def_fun_prop cross in x y  with_transitive : Differentiable R by sorry_proof

#generate_linear_map_simps DataArrayN.cross.arg_x.IsLinearMap_rule
#generate_linear_map_simps DataArrayN.cross.arg_y.IsLinearMap_rule


abbrev_fun_trans cross in x y : fderiv R by
  rw[fderiv_wrt_prod (by fun_prop)]
  fun_trans

abbrev_fun_trans cross in x y : fwdFDeriv R by
  rw[fwdFDeriv_wrt_prod (by fun_prop)]
  autodiff

abbrev_fun_trans cross in x : adjoint R by
  equals (fun z => y.cross z) =>
    sorry_proof

abbrev_fun_trans cross in y : adjoint R by
  equals (fun z => z.cross x) =>
    funext z
    apply AdjointSpace.ext_inner_left R
    intro y
    rw[← adjoint_ex _ (by fun_prop)]
    simp[DataArrayN.inner_def, DataArrayN.cross,
         sum_over_prod, sum_pull]
    -- expand the sum explicitely and call ring
    sorry_proof

abbrev_fun_trans cross in x y : revFDeriv R by
  rw[revFDeriv_wrt_prod (by fun_prop)]
  unfold revFDeriv
  autodiff

abbrev_fun_trans cross in x y : revFDerivProj R Unit by
  unfold revFDerivProj
  autodiff

abbrev_fun_trans cross in x y : revFDerivProjUpdate R Unit by
  unfold revFDerivProjUpdate
  autodiff
