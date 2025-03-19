import SciLean

open SciLean Optimjl

set_default_scalar Float

def rosenbrock (a b x y : Float) := (a - x)^2 + b * (y - x^2)^2

def objective : ObjectiveFunction Float (Float^[2]) where
  f x := rosenbrock 1 100 x[0] x[1]
  hf := by
    unfold rosenbrock
    data_synth => lsimp
  f' := _

def main : IO Unit := do
  let r ← optimizeM objective {show_trace:=true : LBFGS Float 1} ⊞[-10.0,100]
  r.print


def run : IO (Float^[2] × Float) := do
  let r ← optimizeM objective {show_trace:=false : LBFGS Float 1} ⊞[-10.0,100]
  return (r.minimizer, r.minimum)

/-- info: (⊞[1.000006, 1.000013], 0.000000) -/
#guard_msgs in
#eval run
