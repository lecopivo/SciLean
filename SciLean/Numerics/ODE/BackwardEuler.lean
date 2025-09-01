import SciLean.Analysis.Normed.Diffeomorphism
import SciLean.Logic.Function.InvFun

import SciLean.Numerics.ODE.Basic
import SciLean.Numerics.ODE.Solvers

import SciLean.Tactic.MoveTerms

namespace SciLean

variable
  {R : Type _} [RCLike R]
  {W : Type _} [NormedAddCommGroup W] [NormedSpace R W]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace R Z]

set_default_scalar R


namespace backwardEuler


theorem isOdeStepper (f : R → X → X)
  (hf : Differentiable R (fun tx : R×X => f tx.1 tx.2))
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
      fun_trans only [deriv, simp_core]

    -- to remove this sorry as is we probably need that the derivative of f is continuous
    rw[Filter.limit_of_continuous _ _ sorry_proof]

    conv => fun_trans only [simp_core]
    simp
