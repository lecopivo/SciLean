import SciLean.Numerics.ODE.Basic
import SciLean.Numerics.ODE.Solvers

import SciLean.Analysis.Calculus.FDeriv


namespace SciLean

variable
  {R : Type _} [RCLike R]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace R Z]

set_default_scalar R

namespace forwardEuler

theorem isOdeStepper (f : R → X → X)
  : IsOdeStepper f (forwardEuler f)
where
  consistent := by unfold forwardEuler; intros; (conv => autodiff); simp
