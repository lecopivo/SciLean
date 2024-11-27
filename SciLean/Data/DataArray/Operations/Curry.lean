import SciLean.Data.DataArray.Operations.Matmul

namespace SciLean

open DataArrayN

def_fun_prop curry in x with_transitive
    [AddCommGroup α] :
    IsAddGroupHom by
  simp_rw[curry_def]
  fun_prop

def_fun_prop curry in x with_transitive
    [TopologicalSpace α] :
    Continuous by
  simp_rw[curry_def]
  fun_prop

def_fun_prop curry in x with_transitive
    {R} [RCLike R] [NormedAddCommGroup α] [NormedSpace R α] :
    IsContinuousLinearMap R by
  simp_rw[curry_def]
  fun_prop

abbrev_fun_trans curry in x
    {R} [RCLike R] [NormedAddCommGroup α] [NormedSpace R α] :
    fderiv R by fun_trans

abbrev_fun_trans curry in x
    {R} [RCLike R] [NormedAddCommGroup α] [NormedSpace R α] :
    fwdFDeriv R by fun_trans

abbrev_fun_trans curry in x
    {R} [RCLike R] [NormedAddCommGroup α] [AdjointSpace R α] [CompleteSpace α] :
    adjoint R by
  equals (fun y => y.uncurry) =>
    funext y
    apply AdjointSpace.ext_inner_left R
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp only [inner, curry_def, ArrayType.get_ofFn', uncurry_def, sum_over_prod, uncurry_appply2]

abbrev_fun_trans curry in x
    {R} [RCLike R] [NormedAddCommGroup α] [AdjointSpace R α] [CompleteSpace α] :
    revFDeriv R by unfold revFDeriv; fun_trans
