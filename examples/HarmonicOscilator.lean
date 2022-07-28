-- import SciLean.Core.Functions
import SciLean.Mechanics
import SciLean.Operators.ODE
import SciLean.Solver 
import SciLean.Tactic.LiftLimit
import SciLean.Tactic.FinishImpl


open SciLean

abbrev V := ℝ × ℝ

def H (m k : ℝ) (x p : V) := (1/(2*m)) * ∥p∥² + k/2 * ∥x∥²

-- set_option trace.Meta.Tactic.simp.rewrite true in
def solver (m k : ℝ) (steps : Nat)
  : Impl (ode_solve (HamiltonianSystem (H m k))) :=
by
  -- Unfold Hamiltonian definition and compute gradients
  simp [HamiltonianSystem, H]; unfold hold; simp

  -- Apply RK4 method
  rw [ode_solve_fixed_dt runge_kutta4_step]
  lift_limit steps "Number of ODE solver steps."; admit; simp
  
  finish_impl

def main : IO Unit := do

  let substeps := 1
  let m := 1.0
  let k := 10.0

  let evolve ← (solver m k substeps).assemble

  let t := 1.0
  let x₀ := (1.0, 0.5)
  let p₀ := (0.0, 0.0)
  let mut (x,p) := (x₀, p₀)

  for i in [0:40] do
  
    (x, p) := evolve 0.1 (x, p)

    -- print
    for (j : Nat) in [0:20] do
      if j < 10*(x.1+1) then
        IO.print "o"
    IO.println ""


