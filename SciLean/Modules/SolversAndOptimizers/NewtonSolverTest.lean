import SciLean.Modules.SolversAndOptimizers.NewtonSolver

open SciLean

variable
  {R} [RealScalar R]

set_default_scalar R



-- direct use of newton solver
----------------------------------------------------------------------------------------------------

def mySqrt' (y : R) : R :=
  let f := fun x : R => x^2 - y
  let iJ := (fun x y => y/(∂! (x':=x), f x'))
  newtonSolver {relTol := (1e-6 : R), absTol := 1e-9} f iJ y


#eval mySqrt' 2.0



-- use of newton solver through rewrites
----------------------------------------------------------------------------------------------------

approx mySqrt :=
  -- specification of sqrt function
  fun (y : R) => (fun x : R => x^2).invFun y
by
  -- rules how to construct approximation from the specification
  conv =>
    enter[2,y]
    rw[invFun_as_newtonSolver (R:=R) 1 (by fun_prop) sorry]

  -- fix limit at some value `s`
  approx_limit s sorry

  autodiff -- compute derivative
  autodiff -- compute inverse


-- evaluation
#eval mySqrt ({ relTol := 1e-6, absTol := 1e-9},()) 2.0
