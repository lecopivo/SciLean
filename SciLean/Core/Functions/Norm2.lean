import SciLean.Core.Functions.Inner

namespace SciLean

variable
  {R} [RealScalar R]
  {X} [NormedAddCommGroup X] [NormedSpace R X]
  {U} [NormedAddCommGroup U] [AdjointSpace R U]


def_fun_prop with_transitive : Differentiable R (fun u : U => ‖u‖₂²[R]) by
  unfold Norm2.norm2; fun_prop [Norm2.norm2]
