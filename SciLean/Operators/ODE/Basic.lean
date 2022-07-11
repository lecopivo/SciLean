import SciLean.Core.Functions
import SciLean.Functions.Limit

namespace SciLean

noncomputable
opaque ode_solve {X} [Vec X] (f : X → X) (t : ℝ) (x₀ : X) : X

axiom ode_solve.definition {X} [Vec X] (f : X → X) [IsSmooth f] (t dt : ℝ) (x₀ : X) : δ (ode_solve f) t dt x₀ = dt * f (ode_solve f t x₀)

variable {X Y Z} [Vec X] [Vec Y] [Vec Z]

def ode_solve_fixed_dt_impl (n : Nat) (stepper : ℝ → (X → X) → (X → X)) (f : X → X) (t : ℝ) (x₀ : X) : X := 
Id.run do
  let Δt := t/n
  let mut x := x₀
  for i in [0:n] do
    x := (stepper Δt f) x
  x

--- This requires some conditions on the function ... or just add the conclusion as an assumption
def ode_solve_fixed_dt (stepper : ℝ → (X → X) → (X → X)) 
  : ode_solve = limit (λ n => ode_solve_fixed_dt_impl n stepper) := sorry

--  ___ _
-- / __| |_ ___ _ __ _ __  ___ _ _ ___
-- \__ \  _/ -_) '_ \ '_ \/ -_) '_(_-<
-- |___/\__\___| .__/ .__/\___|_| /__/
--             |_|  |_|

def forward_euler_step (Δt : ℝ) (f : X → X) (xₙ : X) : X := xₙ + Δt * f xₙ

def midpoint_step (Δt : ℝ) (f : X → X) (xₙ : X) : X := 
  let x' := xₙ + (Δt/2) * f xₙ
  xₙ + Δt * (f x')

def runge_kutta4_step (Δt : ℝ) (f : X → X) (xₙ : X) : X :=
  let k1 := f xₙ
  let k2 := f (xₙ + (Δt/2) * k1)
  let k3 := f (xₙ + (Δt/2) * k2)
  let k4 := f (xₙ + Δt * k3)
  xₙ + (Δt/6) * (k1 + (2:ℝ)*k2 + (2:ℝ)*k3 + k4)
