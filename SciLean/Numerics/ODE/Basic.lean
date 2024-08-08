import SciLean.Analysis.ODE.OdeSolve
import SciLean.Meta.Notation.Do
import SciLean.Util.Limit

set_option linter.unusedVariables false

namespace SciLean

variable
  {R : Type _} [RCLike R]
  {W : Type _} [NormedAddCommGroup W] [NormedSpace R W]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace R Z]

set_default_scalar R
open Notation

/-- Can we integrate differential equation `∂ x t = f t (x t)` using `stepper` function?

The function `stepper t₀ Δt x₀` computes approximation of the solution `x (t₀+Δt)` under initial condition `x t₀ = x₀`

TODO: refine the conditions, we probably want consistency and convergence. Maybe integrability in `f` too? or integrability of `f` should be specified somewhere else?
-/
structure IsOdeStepper (f : R → X → X) (stepper : R → R → X → X) : Prop where
  consistent : ∀ t x, (limit Δt' → 0, ∂ Δt:=Δt', stepper t Δt x) = f t x
  -- converges - something that it really converges
  -- maybe integrability of `f` ??

def odeSolveFixedStep (stepper : R → R → X → X) (steps : Nat) (t₁ t₂ : R) (x₀ : X) : X := Id.run do
  let Δt := (t₂-t₁)/steps
  let mut x := x₀
  let mut t := t₁
  for _ in [0:steps] do
    x := stepper t Δt x
    t += Δt
  x


-- TODO: make IsOdeStepper and HasUniqueOdeSolution strong enough such that this theorem is true
theorem odeSolve_fixed_dt {f : R → X → X} (stepper : (R → X → X) → (R → R → X → X))
  (h : HasUniqueOdeSolution f ∧ IsOdeStepper f (stepper f))
  : odeSolve f = fun t₀ t x₀ => limit n → ∞, odeSolveFixedStep (stepper f) n t₀ t x₀ := sorry_proof

-- theorem odeSolve_fixed_dt_on_interval {X} [Vec X] {f : ℝ → X → X} {t₀ : ℝ} {x₀ : X}
--   (stepper : Stepper) (interpol : (ℤ→X) → (ℝ→X)) (T : ℝ)
--   : (λ t => odeSolve f t₀ x₀ t)
--     =
--     limit λ n =>
--       let Δt := (T-t₀) / n
--       let toGrid := λ t : ℝ => (t - t₀)/Δt
--       let odeData := odeSolve_fixed_dt_array f stepper n t₀ x₀ T
--       λ t => interpol (extend1DFinStreak λ i => odeData.get i) (toGrid t)
--   := sorry
