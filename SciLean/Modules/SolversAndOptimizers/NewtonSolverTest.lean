import SciLean.Modules.SolversAndOptimizers.NewtonSolver

open SciLean

variable
  {R} [RealScalar R]

-- approximate sqrt function using newton solver
approx mySqrt :=
  -- specification of sqrt function
  fun (y : R) => (fun x : R => x^2).invFun y
by
  -- rules how to construct approximation from the specification
  conv =>
    enter[2,y]
    rw[invFun_as_newtonSolver (R:=R) 1 sorry]

  approx_limit s := sorry

  fun_trans (disch:=sorry)


-- evaluation
#eval mySqrt ({ relTol := 1e-6, absTol := 1e-9},()) 2.0
