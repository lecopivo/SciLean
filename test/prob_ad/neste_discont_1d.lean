import SciLean.Core.Integral.Common

open SciLean MeasureTheory Set

variable
  {R : Type} [RealScalar R] [MeasureSpace R]

set_default_scalar R

example (w : R) :
    (∂ w':=w,
      ∫' x in Icc (0:R) 1,
        if x ≤ w' then if x + w' ≤ 0 then (1:R) else 0 else 0)
    =
    let ds := if 0 ≤ w ∧ w ≤ 1 then if w + w ≤ 0 then 1 else 0 else 0;
    let ds_1 := if (0 ≤ -w ∧ -w ≤ 1) ∧ -w ≤ w then -1 else 0;
    let sf' := ds_1 + ds;
    sf' := by

  conv =>
    lhs
    integral_deriv
