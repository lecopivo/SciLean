import SciLean.Basic
import SciLean.Mechanics

namespace SciLean

set_option synthInstance.maxHeartbeats 5000
set_option synthInstance.maxSize 1000

def V := ℝ × ℝ
instance : Hilbert V := by simp[V]; infer_instance

-- unfortunatelly defining `V` as `abbrev V := ℝ × ℝ` breaks typeclass system and some function cannot be proven smooth anymore :(

def H (m k : ℝ) (x p : V) := (1/(2*m)) * ⟨p,p⟩ + k/2 * ⟨x, x⟩

example (m k : ℝ) (x p dp : V) : δ (H m k x) p dp = 1/(2*m) * (⟨dp,p⟩ + ⟨p,dp⟩) := 
by
  simp[H]
  done

example (p : V) : IsLin (λ dx => 1/2*(⟨dx,p⟩ + ⟨p,dx⟩)) := by infer_instance


example (p : V) : (λ (dx : V) => ⟨dx,p⟩)† (1 : ℝ) = p := by simp done
example (p : V) : (λ (dx : V) => ⟨p,dx⟩)† (1 : ℝ) = p := by simp done

-- set_option trace.Meta.Tactic.simp true
-- example (p : V) : (λ (dx : V) => (2 : ℝ)*(⟨p,p⟩))† (1 : ℝ) = 0 := by simp done


def solver (m k : ℝ) (steps : Nat) : Impl (ode_solve (HamiltonianSystem (H m k))) :=
by
  simp [HamiltonianSystem, H, swap];
  
  conv in (∇ _) =>
    simp[gradient]
    conv  =>
      pattern (δ _)
      enter [x,dx]
      simp

  conv in (∇ _) =>
    simp[gradient]
    conv  =>
      pattern (δ _)
      enter [x,dx]
      simp

  conv in (adjoint _) =>
    simp
    
  
  admit


  -- impl_check (m.toFloat>0) "Mass has to be non zero."
  
  -- simp [HamiltonianSystem, uncurry, H, gradient];
  -- autograd

  -- rw [ode_solve_fixed_dt runge_kutta4_step]
  -- lift_limit steps "Number of ODE solver steps."; admit; simp
  
  -- finish_impl

-- def harmonic_oscillator_main : IO Unit := do

--   let steps := 100
--   let m := 1.0
--   let k := 10.0

--   let evolve ← (solver m k steps).assemble

--   let t := 1.0
--   let x₀ := (1.0, 0.5)
--   let p₀ := (0.0, 0.0)
--   let (x,p) := evolve t (x₀, p₀)
  
--   IO.println s!"In {t} seconds the harmonic oscillator evolved from ({x₀}, {p₀}) to ({x},{p})."

-- #eval harmonic_oscillator_main
