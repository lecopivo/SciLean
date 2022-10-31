-- import SciLean.Core.Functions
import SciLean.Mechanics
import SciLean.Operators.ODE
import SciLean.Solver.Solver 
import SciLean.Tactic.LiftLimit
import SciLean.Tactic.FinishImpl


open SciLean

def H (m k : ℝ) (x p : ℝ) := ∥p∥² + ∥x∥²

set_option trace.Meta.Tactic.simp.rewrite true in
approx solver (m k : ℝ) (steps : Nat)
  := (ode_solve (HamiltonianSystem (H m k)))
by
  -- Unfold Hamiltonian definition and compute gradients
  unfold HamiltonianSystem
  unfold H
  simp (config := {singlePass := true}) [hold] 
  simp (config := {singlePass := true}) [hold] 
  simp (config := {singlePass := true}) [hold] 
  simp (config := {singlePass := true}) [hold] 
  simp (config := {singlePass := true}) [hold] 
  simp (config := {singlePass := true}) [hold]

  -- Apply RK4 method
  rw [ode_solve_fixed_dt runge_kutta4_step]
  approx_limit steps; simp; intro steps';


def main : IO Unit := do

  let substeps := 1
  let m := 1.0
  let k := 10.0

  let evolve := (solver m k substeps).val

  let Δt := 0.1
  let x₀ := 1.0
  let p₀ := 0.0
  let mut (x,p) := (x₀, p₀)

  for _ in [0:40] do
  
    (x, p) := evolve Δt (x, p)

    -- print
    for (j : Nat) in [0:20] do
      if j < 10*(x+1) then
        IO.print "o"
    IO.println ""

-- #eval main
