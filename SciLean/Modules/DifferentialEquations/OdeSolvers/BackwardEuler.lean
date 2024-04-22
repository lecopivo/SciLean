import SciLean.Modules.DifferentialEquations.OdeSolvers.Basic
import SciLean.Modules.DifferentialEquations.OdeSolvers.Solvers

import SciLean.Tactic.MoveTerms

namespace SciLean

variable
  {R : Type _} [RCLike R]
  {X : Type _} [Vec R X]
  {Y : Type _} [Vec R Y]
  {Z : Type _} [Vec R Z]

set_default_scalar R

namespace backwardEuler

theorem isOdeStepper (f : R → X → X)
  (hf : CDifferentiable R (fun tx : R×X => f tx.1 tx.2))
  (hf' : ∀ tₙ Δt, Diffeomorphism R (fun x : X => x - Δt • f (tₙ + Δt) x))
  : IsOdeStepper f (backwardEuler f)
where
  consistent :=
  by
    intro t x
    unfold backwardEuler

    conv =>
      conv in (solveFun _) =>
        conv in (_=_) =>
          move x' terms_to_lhs
      solve_as_inv
      autodiff

    -- to remove this sorry as is we probably need that the derivative of f is continuous
    rw[Filter.limit_of_continuous _ _ sorry_proof]
    fun_trans
