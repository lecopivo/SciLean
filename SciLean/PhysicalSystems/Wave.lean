import SciLean.Mechanics
import SciLean.Operators.ODE
import SciLean.Solver.Solver
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

