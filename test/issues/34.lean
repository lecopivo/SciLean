import SciLean

open SciLean

variable
  {K : Type} [RealScalar K]
  {X : Type} [Vec K X]
  {ι : Type} {κ : Type} [IndexType ι] [IndexType κ]

set_default_scalar K

example (f : X → X) (hf : CDifferentiable K f)
  : (∂ x, let df := ∂ (x':=0), f x'
          df x + df x)
    =
    let df := ∂ (x':=0), f x';
    fun x dx => ∂ (x:=x;dx), df x + ∂ (x:=x;dx), df x :=
by
  conv =>
    lhs; autodiff
  sorry
