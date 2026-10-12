module

public import SciLean.Numerics.ODE.Basic
public import SciLean.Numerics.ODE.Solvers

public import SciLean.Analysis.Calculus.FDeriv

@[expose] public section



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
  consistent := by sorry_proof
