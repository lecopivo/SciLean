import SciLean.Modules.DifferentialEquations.OdeSolvers.Basic
import SciLean.Modules.DifferentialEquations.OdeSolvers.Solvers

namespace SciLean

variable
  {R : Type _} [IsROrC R]
  {X : Type _} [Vec R X]
  {Y : Type _} [Vec R Y]
  {Z : Type _} [Vec R Z]

set_default_scalar R

namespace forwardEuler

theorem isOdeStepper (f : R → X → X)
  : IsOdeStepper f (forwardEuler f)
where
  consistent := by unfold forwardEuler; ftrans
