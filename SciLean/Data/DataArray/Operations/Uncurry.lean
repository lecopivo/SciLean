import SciLean.Data.DataArray.Operations.Matmul

namespace SciLean

open DataArrayN

def_fun_prop uncurry in x with_transitive
    [AddCommGroup α] :
    IsAddGroupHom by
  simp_rw[uncurry_def]
  fun_prop

def_fun_prop uncurry in x with_transitive
    [TopologicalSpace α] :
    Continuous by
  simp_rw[uncurry_def]
  fun_prop

def_fun_prop uncurry in x with_transitive
    {R} [RCLike R] [NormedAddCommGroup α] [NormedSpace R α] :
    IsContinuousLinearMap R by
  simp_rw[uncurry_def]
  fun_prop

abbrev_fun_trans uncurry in x
    {R} [RCLike R] [NormedAddCommGroup α] [NormedSpace R α] :
    fderiv R by fun_trans

abbrev_fun_trans uncurry in x
    {R} [RCLike R] [NormedAddCommGroup α] [NormedSpace R α] :
    fwdFDeriv R by fun_trans

abbrev_fun_trans uncurry in x
    {R} [RCLike R] [NormedAddCommGroup α] [AdjointSpace R α] [CompleteSpace α] :
    adjoint R by
  equals (fun y => y.curry) =>
    funext y
    apply AdjointSpace.ext_inner_left R
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp only [inner, uncurry_def, ArrayType.get_ofFn', sum_prod_eq_sum_sum, uncurry_appply2, curry_def]

abbrev_fun_trans uncurry in x
    {R} [RCLike R] [NormedAddCommGroup α] [AdjointSpace R α] [CompleteSpace α] :
    revFDeriv R by unfold revFDeriv; fun_trans

abbrev_fun_trans
  {α : Type} [pd : PlainDataType α]
  {ι : Type} [inst : IndexType ι] {κ : Type} [IndexType κ] [Inhabited α]
  {R : Type} [RCLike R] [NormedAddCommGroup α] [AdjointSpace R α] [CompleteSpace α] :
  revFDerivProj R Unit (fun (x : DataArrayN (DataArrayN α κ) ι) => x.uncurry) by unfold revFDerivProj; fun_trans

abbrev_fun_trans
  {α : Type} [pd : PlainDataType α]
  {ι : Type} [inst : IndexType ι] {κ : Type} [IndexType κ] [Inhabited α]
  {R : Type} [RCLike R] [NormedAddCommGroup α] [AdjointSpace R α] [CompleteSpace α] :
  revFDerivProjUpdate R Unit (fun (x : DataArrayN (DataArrayN α κ) ι) => x.uncurry) by unfold revFDerivProjUpdate; fun_trans
