import SciLean

open SciLean

example
  : ∂† (λ xy : ℝ × ℝ => xy.1 + xy.2) 
    =
    λ xy ds => (ds,ds)
  := 
by
  conv => lhs; fun_trans

example {X Y} [Hilbert X] [Hilbert Y]
  : ∂† (λ xy : X × Y => ‖xy.1‖² + ‖xy.2‖²) 
    =
    λ xy dz => (((2:ℝ) * dz) • xy.1, ((2:ℝ) * dz) • xy.2)
  := 
by
  conv => lhs; fun_trans
  

set_option trace.Meta.Tactic.fun_trans.step true in
example
  : ℛ (λ xy : ℝ × ℝ => xy.1 + xy.2) 
    =
    λ xy => (xy.1 + xy.2, λ ds => (ds,ds))
  := 
by
  conv => 
    lhs
    fun_trans -- this is bad
