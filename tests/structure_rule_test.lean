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
  
