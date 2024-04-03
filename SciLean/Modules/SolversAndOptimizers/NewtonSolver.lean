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



def newtonSolverStep (f : X → Y) (iJ : X → Y → X) (xᵢ : X) : X :=
  xᵢ - iJ xᵢ (f xᵢ)


partial def newtonIterate (s: NewtonSolverSettings R) (f : X → Y) (iJ : X → Y → X) (x_curr : X) (iter_count : ℕ) : X :=
  let x_next := x_curr - iJ x_curr (f x_curr)
  if ‖(f x_next)‖₂ < s.absTol then x_curr
  else if ‖(f x_next) - (f x_curr)‖₂ < s.relTol then x_curr
  else if iter_count ≥ s.maxSteps then x_curr
  else newtonIterate s f iJ x_curr (iter_count + 1)
/-- Newton Solver, finds `x` such that `f x = 0`

Arguments:
- `s`n settings
- `f` function to invert
- `iJ` inverse jacobian of `f`
- `x₀` initial guess for `x` -/
def newtonSolver (s : NewtonSolverSettings R) (f : X → Y) (iJ : X → Y → X) (x₀ : X) : X :=
  -- TODO: proper implementation
  newtonIterate s f iJ x₀ 0



open Notation

variable (R)
/-- Predicate saying that newton solver converges when solving `f x = y` with initial guess `x₀` -/
def NewtonSolverConvergesAt (f : X → Y) (x₀ : X) : Prop :=
  f.invFun 0
  =
  let iJ := (fun x => (∂ (x':=x), f x').invFun)
  (limit s ∈ newtonSolverSettingsFilter R, newtonSolver s f iJ x₀)
variable {R}


theorem invFun_as_newtonSolver {f : X → Y} (x₀ : X) {y : Y}
    (hf : CDifferentiable R f) /- some sensible invertibility condition on `f` -/
    (h : NewtonSolverConvergesAt R (fun x => f x - y) x₀) :
    f.invFun y
    =
    let iJ := (fun x => (∂ (x':=x), f x').invFun)
    (limit s ∈ newtonSolverSettingsFilter R, newtonSolver s (fun x => f x - y) iJ x₀) := sorry
