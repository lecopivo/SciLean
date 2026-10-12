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
  consistent := by
    intro t x
    -- the step `xₙ + Δt • f t xₙ` is affine in `Δt`, so its derivative is `f t xₙ` everywhere
    have h : (fun Δt' : R => ∂ (Δt:=Δt'), forwardEuler f t Δt x) = fun _ => f t x := by
      funext Δt'
      unfold forwardEuler
      fun_trans
    rw [h, Filter.limit_of_const]
