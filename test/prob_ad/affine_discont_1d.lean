import SciLean.Core
import SciLean.Tactic.IfPull
import SciLean.Util.Profile

open SciLean MeasureTheory Set

variable
  {R : Type} [RealScalar R] [MeasureSpace R] -- [PlainDataType R]

set_default_scalar R


example (w : R) (a b c : R) (ha : a ≠ 0) :
    (∂ w':=w,
      ∫' x in Icc (0:R) 1,
        if a * x + b ≤ c * w' then (1:R) else 0)
    =
    if a⁻¹ * (c * w - b) ∈ Icc 0 1 then
      (Scalar.abs a)⁻¹ * c
    else 0 := by

  conv =>
    lhs
    integral_deriv
