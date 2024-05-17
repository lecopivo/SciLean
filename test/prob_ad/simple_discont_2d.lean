import SciLean.Core.Integral.Common
import SciLean.Tactic.IfPull

open SciLean MeasureTheory Set

variable
  {R : Type} [RealScalar R] [MeasureSpace R] [PlainDataType R]

set_default_scalar R


example (w : R) :
    (∂ w':=w,
      ∫' x in Icc (0:R) 1, ∫' y in Icc (0:R) 1,
        if x + y ≤ w' then (1:R) else 0)
    =
    sorry := by

  conv =>
    lhs
    integral_deriv
    autodiff

  sorry_proof



variable (w : R)

/--
info: let ds :=
  ∫' x,
    jacobian R (fun x => (planeDecomposition (1, 1) ⋯) (w / Scalar.sqrt (1 + 1), x)) x *
      (Scalar.sqrt
          (1 +
            1))⁻¹ ∂volume.restrict
      (preimageSnd ((fun x12 => (planeDecomposition (1, 1) ⋯) x12) ⁻¹' Icc 0 1 ×ˢ Icc 0 1) (w / Scalar.sqrt (1 + 1)));
ds : R
-/
#guard_msgs in
#check (∂ w':=w,
      ∫' x in Icc (0:R) 1, ∫' y in Icc (0:R) 1,
        if x + y ≤ w' then (1:R) else 0) rewrite_by integral_deriv; autodiff
