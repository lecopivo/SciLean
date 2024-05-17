import SciLean.Core.Integral.Common
import SciLean.Tactic.IfPull

open SciLean MeasureTheory Set

variable
  {R : Type} [RealScalar R] [MeasureSpace R]

set_default_scalar R


example (w : R) :
    (∂ w':=w,
      ∫' x in Icc (0:R) 1,
        if x ≤ w' then (1:R) else 0)
    =
    if 0 ≤ w ∧ w ≤ 1 then 1 else 0 := by

  conv =>
    lhs
    integral_deriv
