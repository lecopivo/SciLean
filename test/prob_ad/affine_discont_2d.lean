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



variable (w : R) (a b c d : R)




/--
info: let ds :=
  ∫' x,
    jacobian R (fun x => (planeDecomposition (a, b) ⋯) ((d * w - c) / Scalar.sqrt (a ^ 2 + b ^ 2), x)) x *
      ((Scalar.sqrt (a ^ 2 + b ^ 2))⁻¹ *
        d) ∂volume.restrict
      (((fun x12 => (planeDecomposition (a, b) ⋯) x12) ⁻¹' Icc 0 1 ×ˢ Icc 0 1).snd
        ((d * w - c) / Scalar.sqrt (a ^ 2 + b ^ 2)));
ds : R
-/
#guard_msgs in
#check (∂ w':=w,
      ∫' x in Icc (0:R) 1, ∫' y in Icc (0:R) 1,
        if a * x + b * y + c ≤ d * w' then (1:R) else 0) rewrite_by integral_deriv; autodiff
