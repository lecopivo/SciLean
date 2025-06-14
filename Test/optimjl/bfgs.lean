import SciLean

open SciLean Optimjl

def rosenbrock (a b x y : Float) := (a - x)^2 + b * (y - x^2)^2

def objective : ObjectiveFunction Float (Float^[2]) where
  f x := rosenbrock 1 100 x[0] x[1]
  hf := by
    unfold rosenbrock
    data_synth => lsimp
  f' := _

def main : IO Unit := do
  let r ← optimizeM objective {g_abstol:=1e-4, show_trace:=true : BFGS Float} ⊞[-10.0,-10.0]
  r.print

def run : IO (Float^[2] × Float) := do
  let r ← optimizeM objective {g_abstol:=1e-4, show_trace:=false : BFGS Float} ⊞[-10.0,-10.0]
  return (r.minimizer, r.minimum)

/-- info: (⊞[1.000001, 1.000001], 0.000000) -/
#guard_msgs in
#eval run
