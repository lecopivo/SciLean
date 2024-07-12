import SciLean.Core.FunctionTransformations
import SciLean.Mathlib.Analysis.AdjointSpace.Adjoint
import SciLean.Core.Meta.GenerateFunProp
import SciLean.Core.Meta.GenerateFunTrans

namespace SciLean

variable
  {R} [RealScalar R]
  {X} [NormedAddCommGroup X] [NormedSpace R X]
  {U} [NormedAddCommGroup U] [AdjointSpace R U]


theorem Inner.inner.arg_a0a1.IsBoundedBilinearMap_rule :
    IsBoundedBilinearMap R (fun (x : U×U) => ⟪x.1,x.2⟫[R]) := sorry_proof


def_fun_prop with_transitive : Differentiable R (fun (x : U×U) => ⟪x.1,x.2⟫[R]) by
  fun_prop (disch:=apply Inner.inner.arg_a0a1.IsBoundedBilinearMap_rule)
