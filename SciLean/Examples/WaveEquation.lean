import SciLean.Basic
import SciLean.Mechanics


open Function
namespace SciLean

variable (n : Nat) [NonZero n]

def H (m k : ℝ) (x p : ℝ^n) := 
  let Δx := 1/n
  (Δx/(2*m)) * ⟪p,p⟫ + (k*Δx)/2 * ∑ i, ⟪x[i] - x[i-1], x[i] - x[i-1]⟫


def solver (m k : ℝ) (steps : Nat) : Impl (ode_solve (HamiltonianSystem (H n m k))) :=
by
  -- Unfold Hamiltonian definition and compute gradients
  simp[HamiltonianSystem, H, swap];
  autograd
  autograd
  
  -- Adds a runtime check
  impl_check (m>0) "Mass has to be non zero."

  -- Apply RK4 method
  rw [ode_solve_fixed_dt runge_kutta4_step]
  lift_limit steps "Number of ODE solver steps."; admit; simp
    
  finish_impl
