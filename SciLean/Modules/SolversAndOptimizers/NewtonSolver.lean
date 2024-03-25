import SciLean.Core
import SciLean.Util.Limit


namespace SciLean

variable
  {R} [RealScalar R]
  {X} [SemiHilbert R X]
  {Y} [SemiHilbert R Y]

set_default_scalar R

variable (R)
/-- Settings for Newton Solver -/
structure NewtonSolverSettings where
  relTol : R := 1e-3
  absTol : R := 1e-6
  maxSteps : ℕ := 100
  -- ...

-- NOTE:
/-- Filter specifying how are we supposed to decrease relative/absolute tolerances and increase
maximum steps to achieve convergence. -/
opaque newtonSolverSettingsFilter : Filter (NewtonSolverSettings (R:=R)) := default
variable {R}


-- NOTE: to compute norm with values in `R` use ‖x‖₂
variable (x : X)
#check ‖x‖₂


/-- Newton Solver, finds `x` such that `f x = y`

Arguments:
- `s`n settings
- `f` function to invert
- `iJ` inverse jacobian of `f`
- `x₀` initial guess for `x`
- `y` function value to be inverted -/
def newtonSolver (s : NewtonSolverSettings R) (f : X → Y) (iJ : X → Y → X) (x₀ : X) (y : Y) : X := x₀
  -- TODO: implement newton solver here
  -- update step
  -- x' := x - iJ x (f x)




open Notation

variable (R)
/-- Predicate saying that newton solver converges when solving `f x = y` with initial guess `x₀` -/
def NewtonSolverConvergesAt  (f : X → Y) (x₀ : X) (y : Y) : Prop :=
  f.invFun y
  =
  let iJ := (fun x => (∂ (x':=x), f x').invFun)
  (limit s ∈ newtonSolverSettingsFilter R, newtonSolver s f iJ x₀ y)
variable {R}


-- NOTE: this theorems seems like a completely useless as a mathematical theorem as it is tautology `A → A`.
--       It is used as a rewrite rule when creating approximate programs and `NewtonSolverConvergesAt` packages
--       the statement of this rewrite rule.
--
--       Most of the time we are not interested in proving `NewtonSolverConvergesAt` we just want to
--       keep it around such that we remember we are assuming it when running our program.
theorem invFun_as_newtonSolver {f : X → Y} (x₀ : X) {y : Y}
    (h : NewtonSolverConvergesAt R f x₀ y) :
    f.invFun y
    =
    let iJ := (fun x => (∂ (x':=x), f x').invFun)
    (limit s ∈ newtonSolverSettingsFilter R, newtonSolver s f iJ x₀ y) := h
