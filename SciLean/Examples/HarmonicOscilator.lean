import SciLean.Basic
import SciLean.Mechanics

set_option synthInstance.maxHeartbeats 5000
set_option synthInstance.maxSize 1000

abbrev V := ℝ × ℝ

def H (m k : ℝ) (x p : V) := 1/(2*m) * ⟨p,p⟩ + k/2 * ⟨x, x⟩

def solver (m k : ℝ) (steps : Nat) : Impl (ode_solve (HamiltonianSystem (H m k))) :=
by
  impl_check (m.toFloat>0) "Mass has to be nonzero."
   
  simp [HamiltonianSystem, symp, uncurry, H, gradient]
  autograd

  rw [ode_solve_fixed_dt forward_euler_step]
  lift_limit steps "Number of ODE solver steps."; admit; simp
  
  finish_impl

def grad (m k : ℝ) : Impl (HamiltonianSystem (H m k)) :=
by
  -- impl_check (m.toFloat>0) "Mass has to be nonzero."
   
  simp [HamiltonianSystem, symp, uncurry, H, gradient]
  autograd

  conv in (comp _ _) => 
    enter [xp]
    simp
  
  simp

  finish_impl

def foo_impl : Impl (δ (λ x : ℝ => x*x)) :=
by
  simp [gradient]
  autodiff
  
  finish_impl

def main : IO Unit := do

  let steps := 10
  let m := 1.0
  let k := 10.0

  -- let evolve ← (solver m k steps).assemble

  -- let F := (grad m k).assemble!
  let foo := foo_impl.assemble!
  let bar := fun (x : ℝ) => 1 * x + x * 1

  let t := 1.0
  let x₀ := (1.0, 0.0)
  let p₀ := (0.0, 0.0)
  -- let (x,p) := evolve t (x₀, p₀)

  let y := foo t t
  
  -- IO.println s!"In {t} seconds the harmonic oscillator evolved from ({x₀}, {p₀}) to ({x},{p})."
  IO.println s!"Time change of harmonic oscillator at state ({x₀}, {p₀}) is {y}."

#eval main

def foo := foo_impl.assemble!

#eval (foo 1.0 2.0)
