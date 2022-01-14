import SciLean.Basic
import SciLean.Mechanics

set_option synthInstance.maxHeartbeats 5000

open Function
namespace SciLean

variable (n : Nat) [NonZero n]

def H (m k : ℝ) (x p : ℝ^n) := 
  ∥p∥² + ∑ i, ∥x[i] - x[i-1]∥²


-- set_option trace.Meta.Tactic.simp true in
def solver (m k : ℝ) (steps : Nat) : Impl (ode_solve (HamiltonianSystem (H n m k))) :=
by
  -- Unfold Hamiltonian definition and compute gradients
  simp[HamiltonianSystem, H, swap];
  autograd
  conv in (∇ _) =>
    simp[gradient]
    pattern (δ _)
    enter [x,dx]
    simp
    
  -- autograd
  .

  -- Apply RK4 method
  rw [ode_solve_fixed_dt runge_kutta4_step]
  lift_limit steps "Number of ODE solver steps."; admit; simp
    
  finish_impl
