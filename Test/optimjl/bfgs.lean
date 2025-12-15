import SciLean

open SciLean Optimjl

def rosenbrock (a b x y : Float) := (a - x)^2 + b * (y - x^2)^2

def objective : ObjectiveFunction Float (Float^[2]) where
  f x := rosenbrock 1 100 x[0] x[1]
  f' x :=
    let x0 := x[0]
    let x1 := x[1]
    let t := x1 - x0^2
    let fx := rosenbrock 1 100 x0 x1
    let dx := 2 * (x0 - 1) - 400 * x0 * t
    let dy := 200 * t
    (fx, fun dr => ⊞[dr * dx, dr * dy])
  hf := by
    -- TODO: prove `HasRevFDeriv` for the manual derivative above.
    -- This repo allows `sorry_proof` as technical debt.
    sorry_proof

def main : IO Unit := do
  let r ← optimizeM objective {g_abstol:=1e-4, show_trace:=true : BFGS Float} ⊞[-10.0,-10.0]
  r.print

def run : IO (Float^[2] × Float) := do
  let r ← optimizeM objective {g_abstol:=1e-4, show_trace:=false : BFGS Float} ⊞[-10.0,-10.0]
  return (r.minimizer, r.minimum)

-- NOTE:
-- This example uses `sorry_proof` internally, and as of Lean 4.26 `#eval`
-- aborts when the evaluated expression depends on `sorry` (even via proof
-- fields in a structure), so we keep this as a runtime executable example.
