import SciLean.Mechanics
import SciLean.Operators.ODE
import SciLean.Solver 
import SciLean.Tactic.LiftLimit
import SciLean.Tactic.FinishImpl
import SciLean.Data.DataArray
import SciLean.Core.Extra
import SciLean.Functions

open SciLean

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 500000

def LennardJones (ε minEnergy : ℝ) (radius : ℝ) (x : ℝ^{3}) : ℝ :=
  let x' := ∥1/radius * x∥^{-6, ε}
  4 * minEnergy * x' * (x' - 1)
argument x [Fact (ε≠0)]
  isSmooth, diff, hasAdjDiff, adjDiff

def Coloumb (ε strength mass : ℝ) (x : ℝ^{3}) : ℝ := - strength * mass * ∥x∥^{-1,ε}
argument x [Fact (ε≠0)]
  isSmooth, diff, hasAdjDiff, adjDiff

def H (n : ℕ) (ε : ℝ) (C LJ : ℝ) (r m : Fin n → ℝ) (x p : (ℝ^{3})^{n}) : ℝ :=
  (∑ i, (1/(2*m i)) * ∥p[i]∥²)
  +
  ∑ i j,   Coloumb ε C (m i * m j) (x[i] - x[j])
         + LennardJones ε LJ (r i + r j) (x[i] - x[j])
argument p [Fact (n≠0)] [Fact (ε≠0)]
  isSmooth, diff, hasAdjDiff, adjDiff
argument x [Fact (n≠0)] [Fact (ε≠0)]
  isSmooth, diff, hasAdjDiff,
  adjDiff by
    simp[H]; unfold hold; simp; unfold hold; simp
    simp [sum_into_lambda]
    simp [← sum_of_add]

def solver (steps : ℕ) (n : ℕ) (ε : ℝ) [Fact (n≠0)] [Fact (ε≠0)] (C LJ : ℝ) (r m : Idx n → ℝ) : Impl (ode_solve (HamiltonianSystem (H n ε C LJ r m))) :=
by
  -- Unfold Hamiltonian definition and compute gradients
  simp [HamiltonianSystem]

  -- Apply RK4 method
  rw [ode_solve_fixed_dt runge_kutta4_step]
  lift_limit steps "Number of ODE solver steps."; admit; simp
    
  finish_impl
