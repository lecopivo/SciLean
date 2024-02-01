import SciLean.Modules.DifferentialEquations.OdeSolvers.Basic
import SciLean.Modules.DifferentialEquations.OdeSolvers.Solvers

import SciLean.Tactic.MoveTerms

namespace SciLean

variable
  {R : Type _} [IsROrC R]
  {X : Type _} [Vec R X]
  {Y : Type _} [Vec R Y]
  {Z : Type _} [Vec R Z]

set_default_scalar R

namespace backwardEuler

theorem isOdeStepper (f : R → X → X)
  (hf : IsDifferentiable R (fun tx : R×X => f tx.1 tx.2))
  (hf' : ∀ tₙ Δt, Diffeomorphism R (fun x : X => x - Δt • f (tₙ + Δt) x))
  : IsOdeStepper f (backwardEuler f)
where
  consistent :=
  by
    intro t x
    unfold backwardEuler

    -- this will be unecessary after we fix issue #8
    have hf₁ : ∀ t, IsDifferentiable R (f t) := sorry_proof
    have hf₂ : ∀ x, IsDifferentiable R (f · x) := sorry_proof

    conv =>
      conv in (solveFun _) =>
        conv in (_=_) =>
          move x' terms_to_lhs
      solve_as_inv
      ftrans
      ftrans only

    -- to remove this sorry as is we probably need that the derivative of f is continuous
    rw[Filter.limit_of_continuous _ _ sorry_proof]
    simp; ftrans; apply True.intro
