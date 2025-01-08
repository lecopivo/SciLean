import SciLean.Data.VectorType.Base
import SciLean.Analysis.Calculus.RevFDeriv

import SciLean.Meta.GenerateFunTrans

namespace SciLean

theorem isContinuousLinearMap_equiv_comp
  {R} [NormedField R]
  {X} [NormedAddCommGroup X] [NormedSpace R X]
  {Y} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace R Z]
  {f : X → Y} (g : Y ≃L[R] Z) :
  IsContinuousLinearMap R f ↔ IsContinuousLinearMap R (g∘f) := sorry


-- def Scalar.realEquiv {


variable
  {R : Type} {_ : RealScalar R}-- {_ : Scalar R K}
  {n : Type} {_ : IndexType n}
  {X : Type} [VectorType.Base X n R]



def_fun_prop VectorType.Base.dot in x [VectorType.Lawful X] : IsContinuousLinearMap K by
  simp?[vector_to_spec]


#exit

def_fun_prop dot in y    with_transitive : IsContinuousLinearMap R
def_fun_prop dot in x y  with_transitive : Differentiable R

#generate_linear_map_simps DataArrayN.dot.arg_x.IsLinearMap_rule
#generate_linear_map_simps DataArrayN.dot.arg_y.IsLinearMap_rule


abbrev_fun_trans dot in x y : fderiv R by
  rw[fderiv_wrt_prod (by fun_prop)]
  fun_trans

abbrev_fun_trans dot in x y : fwdFDeriv R by
  rw[fwdFDeriv_wrt_prod (by fun_prop)]
  autodiff

abbrev_fun_trans dot in x : adjoint R by
  equals (fun z => z•y) =>
    funext x
    apply AdjointSpace.ext_inner_left R
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[DataArrayN.inner_def, DataArrayN.dot,
         sum_prod_eq_sum_sum, Function.HasUncurry.uncurry, sum_pull]
    ac_rfl

abbrev_fun_trans dot in y : adjoint R by
  equals (fun z => z•x) =>
    funext y
    apply AdjointSpace.ext_inner_left R
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[DataArrayN.inner_def, DataArrayN.dot,
         Function.HasUncurry.uncurry, sum_pull]
    ac_rfl

abbrev_fun_trans dot in x y : revFDeriv R by
  rw[revFDeriv_wrt_prod (by fun_prop)]
  unfold revFDeriv
  autodiff


#check IsBilinearMap
