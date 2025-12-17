import SciLean

open SciLean

variable
  {K : Type} [RealScalar K]
  {X : Type} [NormedAddCommGroup X] [NormedSpace K X]

set_default_scalar K

example (f : X → X) (hf : Differentiable K f) (x dx)
  : (∂ (x'':=x;dx), (let df := ∂ (x':=0), f x'
                     df x'' + df x''))
    =
    let df := ∂ (x':=0), f x';
    ∂ (x:=x;dx), df x + ∂ (x:=x;dx), df x := by
  -- conv =>
  --   lhs; autodiff
  sorry_proof
