import SciLean

open SciLean

set_default_scalar Float

def H (m k : Float) (x p : Float) := (1/(2*m)) * p*p + k/2 * x*x

approx solver (m k : Float)
  := odeSolve (fun (t : Float) (x,p) => ( ∇ (p':=p), H m k x  p',
                                         -∇ (x':=x), H m k x' p))
by
  -- Unfold Hamiltonian and compute gradients
  unfold H
  autodiff

  -- Apply RK4 method
  simp_rw (config:={zeta:=false}) [odeSolve_fixed_dt rungeKutta4 sorry_proof]

  -- todo: make approx_limit ignore leading let bindings
  approx_limit n sorry_proof

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
      if j.toFloat < 10*(x+1.0) then
        IO.print "o"
    IO.println ""

#eval main
