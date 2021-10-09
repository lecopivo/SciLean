import SciLean.Basic
import SciLean.Mechanics

set_option synthInstance.maxHeartbeats 5000
set_option synthInstance.maxSize 1000

abbrev V := ℝ × ℝ

def H (m k : ℝ) (x p : V) := 1/(2*m) * ⟨p,p⟩ + k/2 * ⟨x, x⟩

def solver (m k : ℝ) (steps : Nat) : Impl (ode_solve (HamiltonianSystem (H m k))) :=
by
  impl_check (m.toFloat>0) "Mass has to be non zero."
    
  simp [HamiltonianSystem, symp, uncurry, H, gradient]
  autograd

  rw [ode_solve_fixed_dt runge_kutta4_step]
  lift_limit steps "Number of ODE solver steps."; admit; simp
  
  finish_impl

def harmonic_oscillator_main : IO Unit := do

  let steps := 100
  let m := 1.0
  let k := 10.0

  let evolve ← (solver m k steps).assemble

  let t := 1.0
  let x₀ := (1.0, 0.5)
  let p₀ := (0.0, 0.0)
  let (x,p) := evolve t (x₀, p₀)
  
  IO.println s!"In {t} seconds the harmonic oscillator evolved from ({x₀}, {p₀}) to ({x},{p})."

#eval harmonic_oscillator_main
