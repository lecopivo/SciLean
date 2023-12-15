import SciLean
import SciLean.Core.Approx.ApproxLimit
import SciLean.Tactic.LetNormalize
import SciLean.Tactic.PullLimitOut
import SciLean.Modules.DifferentialEquations
import SciLean.Core.Meta.GenerateRevCDeriv'

open SciLean

variable {n : USize} [Nonempty (Idx n)]

set_option synthInstance.maxSize 20000
open NotationOverField
set_default_scalar Float

-- set_option trace.Meta.synthInstance true in
def H (m k : Float) (x p : Float^[n]) : Float := 
  let Δx := 1.0/n.toFloat
  (Δx/(2*m)) * ‖p‖₂² + (Δx * k/2) * (∑ i, ‖x[i.shift 1] - x[i]‖₂²)


#generate_revCDeriv' H x p
  prop_by unfold H; fprop
  trans_by unfold H; ftrans; ftrans; ftrans


approx solver (m k : Float)
  :=  odeSolve (λ t (x,p) => ( ∇ (p':=p), H (n:=n) m k x p',
                              -∇ (x':=x), H (n:=n) m k x' p))
by
  -- Unfold Hamiltonian definition and compute gradients
  unfold scalarGradient
  ftrans; simp (config:={zeta:=false}); ftrans

  -- Apply RK4 method
  rw [odeSolve_fixed_dt (R:=Float) rungeKutta4 sorry_proof]

  approx_limit steps := sorry_proof
  

def main : IO Unit := do

  let substeps := 1
  let m := 1.0
  let k := 10000.0

  let N : USize := 100
  -- have h : Nonempty (Idx N) := sorry

  let Δt := 0.1
  let x₀ : Float^[N] := ⊞ (i : Idx N) => (Scalar.sin (i.1.toFloat/10))
  let p₀ : Float^[N] := ⊞ i => (0 : Float)
  let mut t := 0
  let mut (x,p) := (x₀, p₀)

  for i in [0:1000] do
  
    (x, p) := solver m k (substeps,()) t (t+Δt) (x, p) 
    t += Δt

    let M : USize := 20
    for m in fullRange (Idx M) do
      for n in fullRange (Idx N) do
        let xi := x[n]
        if (2*m.1.toFloat - M.toFloat)/(M.toFloat) - xi < 0  then
          IO.print "x"
        else
          IO.print "."

      IO.println ""


-- #eval main

