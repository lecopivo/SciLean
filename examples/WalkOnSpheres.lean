import SciLean.Core.Rand.Distributions.WalkOnSpheres

open SciLean Prob

set_default_scalar Float

def φ (x : Vec3) : Float := |‖x‖₂ - 1|
def g (x : Vec3) : Float := if ‖x‖₂² < 1.01 then 1 else 0

#eval φ v[1,0,0]

def main : IO Unit := do

  timeit "" <| Prob.print_mean_variance (walkOnSpheres φ g 100 v[10,0,0]) 100 ""
  timeit "" <| Prob.print_mean_variance (walkOnSpheres φ g 100 v[10,0,0]) 100 ""
