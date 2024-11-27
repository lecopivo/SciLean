import SciLean.Data.DataArray.Operations.Multiply

namespace SciLean

section Missing


theorem sum_over_prod' {R} [AddCommMonoid R] {I J : Type*} [IndexType I] [IndexType J]
    {f : I → J → R} : ∑ i j, f i j = ∑ (i : I×J), f i.1 i.2  := sorry

theorem sum_over_prod {R} [AddCommMonoid R] {I J : Type*} [IndexType I] [IndexType J]
    {f : I×J → R} : ∑ i, f i = ∑ i j, f (i,j)  := sorry

@[rsimp]
theorem sum_ite {R} [AddCommMonoid R] {I : Type*} [IndexType I] [DecidableEq I]
    {f : I → R} (j : I) : (∑ i, if i = j then f i else 0) = f j  := sorry

@[rsimp]
theorem sum_ite' {R} [AddCommMonoid R] {I : Type*} [IndexType I] [DecidableEq I]
    {f : I → R} (j : I) : (∑ i, if j = i then f i else 0) = f j  := sorry

theorem sum_swap {R} [AddCommMonoid R] {I J : Type*} [IndexType I] [IndexType J]
    {f : I → J → R} : ∑ i j, f i j = ∑ j i, f i j  := sorry

end Missing


variable
  {I : Type*} [IndexType I] [DecidableEq I]
  {R : Type*} [RealScalar R] [PlainDataType R]


open DataArrayN

def_fun_prop diag in x
  with_transitive : IsContinuousLinearMap R

#generate_linear_map_simps DataArrayN.diag.arg_x.IsLinearMap_rule

-- todo: change to abbrev_def_trans
def_fun_trans diag in x : fderiv R by autodiff

-- todo: change to abbrev_def_trans
def_fun_trans diag in x : fwdFDeriv R by autodiff

-- todo: change to abbrev_def_trans
def_fun_trans diag in x : adjoint R by
  equals (fun x' => x'.diagonal) =>
    funext x
    apply AdjointSpace.ext_inner_left R
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[DataArrayN.inner_def,Function.HasUncurry.uncurry,
         DataArrayN.diag,DataArrayN.diagonal,
         sum_over_prod, sum_ite']

-- todo: change to abbrev_def_trans
def_fun_trans diag in x : revFDeriv R by
  unfold revFDeriv
  autodiff
