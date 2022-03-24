import SciLean.Basic
import SciLean.Mechanics

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 500000

open Function SciLean

notation x "[[" i "]]" => PowType.powType.getOp x i

variable (n : Nat) [NonZero n]

def H (m k : ℝ) (x p : ℝ^n) := 
  let Δx := (1 : ℝ)/(n : ℝ)
  (Δx/(2*m)) * ∥p∥² + (Δx * k/2) * (∑ i, ∥x[i] - x[i-1]∥²) -- + 2 * k * (∑ i, ∥(∥x[i] - x[i-1]∥² - 0.1)∥²)

-- set_option trace.Meta.Tactic.simp.discharge true in
def solver (m k : ℝ) (steps : Nat) : Impl (ode_solve (HamiltonianSystem (H n m k))) :=
by
  -- Unfold Hamiltonian definition and compute gradients
  simp[HamiltonianSystem, H]
  simp[gradient, AtomicSmoothFun₂.df₁, AtomicSmoothFun₂.df₂, AtomicSmoothFun.df]
  -- simp[gradient, AtomicSmoothFun₂.df₁, AtomicSmoothFun₂.df₂, AtomicSmoothFun.df]

  -- Apply RK4 method
  rw [ode_solve_fixed_dt runge_kutta4_step]
  lift_limit steps "Number of ODE solver steps."; admit; simp
    
  finish_impl

def main : IO Unit := do

  let substeps := 1
  let m := 1.0
  let k := 100000.0

  let N : Nat := 100
  let evolve ← (solver N m k substeps).assemble

  let t := 1.0
  let x₀ : (ℝ^N) := PowType.intro λ (i : Fin N) => (Math.sin ((i : ℝ)/10))
  let p₀ : (ℝ^N) := PowType.intro λ i => (0 : ℝ)
  let mut (x,p) := (x₀, p₀)

  for i in [0:300] do
  
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


