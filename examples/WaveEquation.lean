import SciLean.Mechanics
import SciLean.Operators.ODE
import SciLean.Solver.Solver
-- import SciLean.Tactic.LiftLimit
-- import SciLean.Tactic.FinishImpl
import SciLean.Data.DataArray
import SciLean.Core.Extra

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 500000

open Function SciLean

variable {n : Nat} [Nonempty (Fin n)]

-- set_option trace.Meta.synthInstance true in
def H (m k : ℝ) (x p : ℝ^{n}) : ℝ := 
  let Δx := (1 : ℝ)/(n : ℝ)
  (Δx/(2*m)) * ∥p∥² + (Δx * k/2) * (∑ i , ∥x[i] - x[i - 1]∥²)
argument x
  isSmooth, diff, hasAdjDiff, adjDiff
argument p
  isSmooth, diff, hasAdjDiff, adjDiff


approx solver (m k : ℝ) (steps : Nat) := (ode_solve (HamiltonianSystem (H (n:=n) m k)))
by
  -- Unfold Hamiltonian definition and compute gradients
  unfold HamiltonianSystem
  simp [HamiltonianSystem]

  -- Apply RK4 method
  rw [ode_solve_fixed_dt runge_kutta4_step]
  approx_limit steps; simp; intro steps'


def main : IO Unit := do

  let substeps := 1
  let m := 1.0
  let k := 100000.0

  let N : Nat := 100
  have h : Nonempty (Fin N) := sorry

  let evolve := (solver (n:=N) m k substeps).val

  let t := 1.0
  let x₀ : (ℝ^{N}) := .intro λ (i : Fin N) => (Math.sin ((i.1 : ℝ)/10))
  let p₀ : (ℝ^{N}) := .intro λ i => (0 : ℝ)
  let mut (x,p) := (x₀, p₀)

  for i in [0:1000] do
  
    (x, p) := evolve 0.1 (x, p)

    let M : Nat := 20
    for (m : Nat) in [0:M] do
      for (n : Nat) in [0:N] do
        
        let xi := x[!n]
        if (2*m - M)/(M : ℝ) - xi < 0  then
          IO.print "x"
        else
          IO.print "."

      IO.println ""


-- #eval main
