import SciLean.Core
import SciLean.Core.Functions.Trigonometric
import SciLean.Core.FloatAsReal
import SciLean.Core.Meta.GenerateRevDeriv

namespace SciLean.ML

variable {R : Type} [RealScalar R]

open Scalar RealScalar

def gelu (x : R) : R :=
  let c := sqrt (2/pi)
  x * (1 + tanh (c * x * (1 + 0.044715 * x^2)))

#generate_revDeriv gelu x
  prop_by unfold gelu; fprop
  trans_by
    unfold gelu
    ftrans
