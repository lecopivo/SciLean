import SciLean.Core.Integral.Common
import SciLean.Tactic.IfPull

open SciLean MeasureTheory Set

variable
  {R : Type} [RealScalar R] [MeasureSpace R] [PlainDataType R]

set_default_scalar R


example (w : R) (a b c d : R) :
    (∂ w':=w,
      ∫' x in Icc (0:R) 1, ∫' y in Icc (0:R) 1,
        if a * x + b * y + c ≤ d * w' then (1:R) else 0)
    =
    sorry := by

  conv =>
    lhs
    integral_deriv
    autodiff

  sorry_proof
