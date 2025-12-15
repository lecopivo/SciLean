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
  IO.println "LBFGS example disabled temporarily"
