import SciLean.Numerics.ODE.Basic
import SciLean.Numerics.ODE.Solvers

/-!
# Explicit Runge–Kutta Steppers

This file records that the standard explicit RK-family methods provided in
`SciLean.Numerics.ODE.Solvers` are consistent ODE steppers.

We keep the proofs `sorry_proof`-friendly: SciLean is focused on functionality
and performance, not full verification.
-/

set_option linter.unusedVariables false

namespace SciLean

variable
  {R : Type _} [RCLike R]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace R Z]

set_default_scalar R

namespace explicitMidpoint

theorem isOdeStepper (f : R → X → X)
  : IsOdeStepper f (explicitMidpoint f)
where
  consistent := by
    -- Standard RK2 consistency; proof left for later.
    sorry_proof

end explicitMidpoint


namespace heunMethod

theorem isOdeStepper (f : R → X → X)
  : IsOdeStepper f (heunMethod f)
where
  consistent := by
    -- Improved Euler / Heun method is consistent.
    sorry_proof

end heunMethod


namespace rungeKutta4

theorem isOdeStepper (f : R → X → X)
  : IsOdeStepper f (rungeKutta4 f)
where
  consistent := by
    -- Classical RK4 consistency; proof left for later.
    sorry_proof

end rungeKutta4

end SciLean

