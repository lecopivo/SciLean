import SciLean.Numerics.Optimization.Optimjl.Multivariate.Solvers.FirstOrder.LBFGS
import SciLean.Numerics.Optimization.Optimjl.Multivariate.Optimize.Optimize
import SciLean.Tactic.DataSynth.ArrayOperations


open SciLean Optimjl

def rosenbrock (a b x y : Float) := (a - x)^2 + b * (y - x^2)^2

-- def f : ObjectiveFunction Float (Float^[2]) where
--   f x := rosenbrock 1 100 x[0] x[1]
--   hf := by
--     unfold rosenbrock
--     -- TODO: this fails right now as we are missing HasRevFDeriv(Update) theorems for `ArrayType`
--     apply hasRevFDeriv_from_hasRevFDerivUpdate
--     data_synth => lsimp
--   f' := _

def main : IO Unit := do
  IO.println "fix this test!"
  -- let r ← optimize f {show_trace:=true : LBFGS Float 1} ⊞[0.0,0]
  -- r.print
