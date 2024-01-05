import SciLean

open SciLean

variable
  {R : Type} [RealScalar R]

set_default_scalar R

-- fprop example
example : IsDifferentiable R fun x : R => x^2 := by fprop
-- ftrans example
example : ∂ x : R, x^2 = fun x => 2 * x := by conv => lhs; ftrans

-- derivative
-- ∂ : (R→X) → (R→X)
#check ∂ x : R, (x^2)
#check ∂! x : R, (x^2)


-- gradient
-- ∇ : (X→R) → (X→X)
#check ∇ x : R×R, x.1
#check ∇! x : R×R, x.1
#check ∇! x : R×R, ‖x‖₂²



-- forward AD
-- ∂> : (X→Y) → (X→X→Y×Y)
#check ∂> x : R, x^2
#check ∂>! x : R, x^2


-- reverse AD
-- <∂ : (X→Y) → (X→Y×(Y→X))
#check <∂! x : R×R, x.1


------------------------------------------------

def foo (x y : R) : R := x + y^2

#generate_fwdCDeriv foo x y
  prop_by unfold foo; fprop
  trans_by unfold foo; ftrans

#print foo.arg_xy.IsDifferentiable_rule
#print foo.arg_xy.fwdCDeriv
#check foo.arg_xy.fwdCDeriv_rule

#check ∂>! x : R, foo x x
