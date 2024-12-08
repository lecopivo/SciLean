import SciLean.Numerics.Optimization.Optimjl.Utilities.Types

/-! Port of Optim.jl, file src/utilities/perform_linesearch.jl

github link:
https://github.com/JuliaNLSolvers/Optim.jl/blob/711dfec61acf5dbed677e1af15f2a3347d5a88ad/src/utilities/perform_linesearch.jl

-/

namespace SciLean.Optimjl



variable
  {R : Type} [RealScalar R] [PlainDataType R]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X]

variable [AbstractOptimizerState R X S]

variable (R)




end
