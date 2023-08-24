import SciLean
import SciLean.Core.Approx.ApproxLimit
import SciLean.Tactic.LetNormalize
import SciLean.Tactic.PullLimitOut
import SciLean.Modules.DifferentialEquations

set_default_scalar Float

open SciLean

def H (m k : Float) (x p : Float) := (1/(2*m)) * p*p + k/2 * x*x

approx solver (m k : Float)
  := odeSolve (λ (t : Float) (x,p) => ( ∇ (p':=p), H m k x  p',
                                       -∇ (x':=x), H m k x' p))
by
  -- Unfold Hamiltonian and compute gradients
  unfold H
  ftrans; simp; ring_nf -- symbolic differentiation
  
  -- Apply RK4 method
  rw [odeSolve_fixed_dt rungeKutta4 sorry_proof]
  
  approx_limit n := sorry_proof

def main : IO Unit := do

  let substeps := 1
  let m := 1.0
  let k := 10.0

  let Δt := 0.1
  let x₀ := 1.0
  let p₀ := 0.0
  let mut t := 0
  let mut (x,p) := (x₀, p₀)

  for _ in [0:50] do
  
    (x, p) := solver m k substeps t (t+Δt) (x, p) 
    t += Δt

    -- print
    for (j : Nat) in [0:20] do
      if j < 10*(x+1) then
        IO.print "o"
    IO.println ""

-- #eval main
