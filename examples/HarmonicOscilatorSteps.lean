import SciLean.Basic
import SciLean.Mechanics

set_option synthInstance.maxHeartbeats 5000

open SciLean

abbrev V := ℝ × ℝ

def H (x p : V) := ∥p∥² + ∥x∥²

set_option trace.Meta.Tactic.simp.rewrite true in
def solver (steps : Nat)
  : Impl (ode_solve (HamiltonianSystem H)) :=
by
  -- Unfold Hamiltonian definition and compute gradients
  simp[HamiltonianSystem, H]
  
  conv =>
    pattern (gradient _)
    enter [p]
    simp[gradient]
    conv =>
      pattern (differential _)
      enter [p,dp]
      simp (config := { singlePass := true })
      simp (config := { singlePass := true })
      simp (config := { singlePass := true })
      simp (config := { singlePass := true })
      simp (config := { singlePass := true })
    .
    simp (config := { singlePass := true })
    simp (config := { singlePass := true })
    simp (config := { singlePass := true })

  conv =>
    pattern (gradient _)
    enter [x]
    simp[gradient]
    conv =>
      pattern (differential _)
      enter [x,dx]
      simp (config := { singlePass := true })
      simp (config := { singlePass := true })
      simp (config := { singlePass := true })
      simp (config := { singlePass := true })
    .
    simp (config := { singlePass := true })
    simp (config := { singlePass := true })
    simp (config := { singlePass := true })

  -- impl_check (steps>0) "Number of steps is zero"

  -- Apply RK4 method
  rw [ode_solve_fixed_dt runge_kutta4_step]
  lift_limit steps "Number of ODE solver steps."; admit; simp
  
  finish_impl

def main : IO Unit := do

  let substeps := 1

  let evolve ← (solver substeps).assemble

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

-- #eval main
