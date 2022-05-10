import SciLean.Mechanics
import SciLean.Operators.ODE
import SciLean.Solver 
import SciLean.Tactic.LiftLimit
import SciLean.Tactic.FinishImpl
import SciLean.Data.PowType
import SciLean.Core.Extra
import SciLean.Functions

open SciLean

set_option synthInstance.maxSize 2048

notation x "[[" i "]]" => PowType.powType.getOp x i

def H (n : Nat) (m l w : Idx n → ℝ) (x p : ((ℝ^(3:Nat))^n)) : ℝ := 
  (∑ i, (1/(2*m i)) * ∥p[i]∥²)
  +
  (∑ i, ∥ ∥x[i] - x[i+(1:USize)]∥² - l i * l i∥² +  
        ∥ ∥cross (x[i+(1:USize)] - x[i]) (x[i-(1:USize)] - x[i]) ∥² - w i * w i∥²)
argument p [Fact (n≠0)]
  isSmooth, hasAdjDiff, adjDiff
argument x [Fact (n≠0)]
  isSmooth, hasAdjDiff, adjDiff
      
  
def solver (steps : ℕ) (n : Nat) [Fact (n≠0)] (m l w : Idx n → ℝ)
  : Impl (ode_solve (HamiltonianSystem (H n m l w))) :=
by
  -- Unfold Hamiltonian definition and compute gradients
  simp[HamiltonianSystem]
  
  -- Apply RK4 method
  rw [ode_solve_fixed_dt runge_kutta4_step]
  lift_limit steps "Number of ODE solver steps."; admit; simp

  finish_impl
