module

public import SciLean.Core
public import SciLean.Core.Functions.Trigonometric
public import SciLean.Core.FloatAsReal
public import SciLean.Core.Meta.GenerateRevDeriv

@[expose] public section


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
