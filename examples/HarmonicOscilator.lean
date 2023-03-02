-- import SciLean.Core.Functions
import SciLean
import SciLean.Functions.OdeSolve
import SciLean.Solver.Solver 

-- import SciLean.Tactic.LiftLimit
-- import SciLean.Tactic.FinishImpl

open SciLean


def H (m k : ℝ) (x p : ℝ) := (1/(2*m)) * ∥p∥² + k/2 * ∥x∥²

approx solver (m k : ℝ) (steps : Nat)
  := odeSolve (λ t (x,p) => ( ∇ (p':=p), H m k x  p',
                             -∇ (x':=x), H m k x' p))
by
  -- Unfold Hamiltonian and compute gradients
  unfold H
  symdiff; symdiff

  -- Apply RK4 method
  rw [odeSolve_fixed_dt runge_kutta4_step]
  approx_limit steps; simp; intro steps';


def main : IO Unit := do

  let substeps := 1
  let m := 1.0
  let k := 10.0

  let Δt := 0.1
  let x₀ := 1.0
  let p₀ := 0.0
  let mut t := 0
  let mut (x,p) := (x₀, p₀)

  for _ in [0:40] do
  
    (x, p) := solver m k substeps 0 (x, p) Δt
    t += Δt

    -- print
    for (j : Nat) in [0:20] do
      if j < 10*(x+1) then
        IO.print "o"
    IO.println ""

#eval main
