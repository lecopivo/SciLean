import SciLean

open SciLean


-- set_option pp.all true in
set_option trace.Meta.Tactic.fun_trans.rewrite true in
example
  : ∂† (λ xy : ℝ × ℝ => xy.1 + xy.2) 
    =
    λ xy ds => (ds,ds)
  := 
by
  conv => lhs; fun_trans
  
