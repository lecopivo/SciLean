import SciLean.Numerics.Optimization.Optimjl.Utilities.Types
import SciLean.Numerics.Optimization.Optimjl.LinerSearches.Types
import SciLean.Numerics.Optimization.Optimjl.LinerSearches.BackTracking

/-! Port of Optim.jl, file src/multivariate/solvers/first_order/bfgs.jl

github link:
https://github.com/JuliaNLSolvers/Optim.jl/blob/711dfec61acf5dbed677e1af15f2a3347d5a88ad/src/multivariate/solvers/first_order/bfgs.jl

-/

namespace SciLean.Optimjl


variable
  {R : Type} [RealScalar R] [PlainDataType R] [ToString R]


variable (R)
inductive BFGS.InitialInvH (n : ℕ) where
/-- Initialize inverse Hessian to this specified value -/
| invH (invH : R^[n,n])
/-- Initialize inverse Hessian such that the step length is the specified `stepnorm` -/
| stepnorm (stepnorm : R)
/-- Initialize inverse Hessian to identity matrix -/
| identity

open BFGS in
structure BFGS extends Options R where
  /-- Linear search that finds appropriate `α` `xₙ₊₁ = xₙ + α • sₙ` -/
  lineSearch : LineSearch0Obj R := .mk (BackTracking R) {}
  /-- Guess initial `α` to try given function value and gradient -/
  alphaguess (φ₀ dφ₀ : R) (d : ObjectiveFunction R (R^[n])) : R := 1
  /-- How to initialize inverse Hessian at the start.

  This is also use on gradient reset when invalid   -/
  initialInvH : InitialInvH R n := .identity
variable {R}


set_default_scalar R

namespace BFGS


structure State (R : Type) (n : ℕ) [RealScalar R] [PlainDataType R] where
   /-- current position `xₙ` -/
   x : R^[n]
   /-- previous position `xₙ₋₁`-/
   x_previous : R^[n] := x
   /-- current gradient `∇f(xₙ)` -/
   g : R^[n] := 0
   /-- previous gradient `∇f(xₙ₋₁)` -/
   g_previous : R^[n] := g
   /-- current valus `f(xₙ)` -/
   f_x : R
   /-- previous valus `f(xₙ₋₁)` -/
   f_x_previous : R := f_x
   /-- position difference `xₙ-xₙ₋₁` -/
   dx : R^[n] := 0
   /-- gradient difference `∇f(xₙ)-∇f(xₙ₋₁)`-/
   dg : R^[n] := 0
   /-- `(∇²f)⁻¹(xₙ)*(xₙ-xₙ₋₁)` i.e. `invH*dx`  -/
   u : R^[n] := 0
   /-- current inverse hessian `(∇²f)⁻¹(xₙ)` -/
   invH : R^[n,n] := .identity
   /-- step direction `- (∇²f)⁻¹ ∇f` i.e. `- (invH * g)` -/
   s : R^[n] := - g
   /-- line search scalle `dx := α • s` -/
   alpha : R := 1
   /-- somethig to do with line search -/
   x_ls : R^[n] := 0
   f_calls : ℕ := 0
   g_calls : ℕ := 0
   h_calls : ℕ := 0


-- this should be specific to BFGS
def reset_search_direction (method : BFGS R) (state : State R n)
    : State R n := Id.run do

  let mut ⟨x, x_previous, g, g_previous, f_x, f_x_previous, dx, dg, u, invH, s,alpha,x_ls,f_calls, g_calls, h_calls⟩ := state

  match method.initialInvH with
  | .invH iH =>     invH := iH
  | .stepnorm sn => invH := (sn / ‖g‖₂⁻¹) • 𝐈 n
  | .identity =>    invH := 𝐈 n

  s := - invH * g -- original code has only `- g` for some reason
  return ⟨x, x_previous, g, g_previous, f_x, f_x_previous, dx, dg, u, invH, s,alpha,x_ls,f_calls, g_calls, h_calls⟩


def perform_linesearch (method : BFGS R) (state : State R n) (d : ObjectiveFunction R (R^[n])) :
    (Except LineSearchError (R×R)) := Id.run do

  let mut state := state
  let mut dφ₀ := ⟪state.g, state.s⟫

  -- not decreasing, we have to reset the gradient
  if dφ₀ >= 0 then
    state := reset_search_direction method state
    dφ₀ := ⟪state.g, state.s⟫

  let φ₀ := state.f_x

  state.alpha := method.alphaguess φ₀ dφ₀ d

  state.f_x_previous := φ₀
  state.x_previous   := state.x

  let φ := fun α => d.f (state.x + α • state.s)

  -- WARNING! Here we run IO code in pure code, the last `()` is `IO.RealWorld`
  --          This hould be fixed, eiter remove LineSearch.call from IO or make this function in IO
  match method.lineSearch.call φ φ₀ dφ₀ state.alpha () () with
  | .ok (αφα,_) _ =>
    return .ok αφα
  | .error e _ =>
    return .error e


def updateState (method : BFGS R) (state : State R n) (d : ObjectiveFunction R (R^[n])) :
    (Except LineSearchError (State R n)) := Id.run do

  let mut state := state

  state.s := - (state.invH * state.g)
  state.g_previous := state.g

  match perform_linesearch method state d with
  | .error e => return .error e
  | .ok (α,_φα) =>

  state.alpha := α

  -- update position
  state.dx := state.alpha • state.s
  state.x_previous := state.x
  state.x := state.x + state.dx

  -- do not update `f_x` as it will be updated in `updateFG`

  -- TODO: update f_calls and g_calls
  --       this information should be somehow given by line search

  return .ok state


def updateFG (state : State R n) (d : ObjectiveFunction R (R^[n])) :
    State R n := Id.run do

  let mut ⟨x, x_previous, g, g_previous, f_x, f_x_previous, dx, dg, u, invH, s,alpha,x_ls,f_calls, g_calls, h_calls⟩ := state

  f_x_previous := f_x
  g_previous := g

  let (f_x', updateFun) := d.f' x
  f_x := f_x'
  g := updateFun 1

  f_calls += 1
  g_calls += 1

  return ⟨x, x_previous, g, g_previous, f_x, f_x_previous, dx, dg, u, invH, s,alpha,x_ls,f_calls, g_calls, h_calls⟩


def updateH (state : State R n)  :
    State R n := Id.run do

  let mut ⟨x, x_previous, g, g_previous, f_x, f_x_previous, dx, dg, u, invH, s,alpha,x_ls,f_calls, g_calls, h_calls⟩ := state

  dg := g - g_previous

  let dx_dg := ⟪dx, dg⟫

  -- update `H⁻¹` only if we can guarangee positive definitness
  if dx_dg > 0 then

    u := invH*dg
    let c1 := (dx_dg + ⟪dg,u⟫)/dx_dg^2
    let c2 := dx_dg⁻¹
    -- todo: add `A.addsmulouterprod s x y` function
    invH := invH + c1 • dx.outerprod dx
                 - c2 • (u.outerprod dx + dx.outerprod u)

  return ⟨x, x_previous, g, g_previous, f_x, f_x_previous, dx, dg, u, invH, s,alpha,x_ls,f_calls, g_calls, h_calls⟩

local instance [Zero R] : Inhabited R := ⟨0⟩

def assessConvergence (method : BFGS R) (state : State R n) :=

    let ⟨..⟩ := state
    let ⟨..⟩ := method.toOptions

    Id.run do

    let mut x_converged := false
    let mut f_converged := false
    let mut f_increased := false
    let mut g_converged := false

    if (x - x_previous).abs.max ≤ x_abstol then
      x_converged := true

    if (x - x_previous).abs.max ≤ x_reltol * x.abs.max then
      x_converged := true

    if Scalar.abs (f_x - f_x_previous) ≤ f_abstol then
      f_converged := true

    if Scalar.abs (f_x - f_x_previous) ≤ f_reltol * Scalar.abs f_x then
      f_converged := true

    if f_x > f_x_previous then
      f_increased := true

    g_converged := g.abs.max ≤ g_abstol

    return (x_converged, f_converged, g_converged, f_increased)

def initState (method : BFGS R) (d : ObjectiveFunction R (R^[n])) (x₀ : R^[n]) : BFGS.State R n := Id.run do

  let (fx,df) := d.f' x₀
  let g := df 1

  let mut state : BFGS.State R n := {
    x := x₀
    f_x := fx
    f_x_previous := fx
    g := g
    f_calls := 1
    g_calls := 1
  }

  state := reset_search_direction method state

  return state

end BFGS

set_option linter.unusedVariables false in
instance {n} : AbstractOptimizer (BFGS R) (BFGS.State R n) R (R^[n]) where

  getOptions m := m.toOptions
  getPosition s := s.x
  getGradient s := s.g

  initialConvergence method state := (false,false)
  assessConvergence method state := BFGS.assessConvergence method state

  printStateHeader := s!"xₙ\tf(xₙ)\t∇f(xₙ)\tsₙ\tα"
  printState state := s!"{state.x}\t{state.f_x}\t{state.g}\t{state.s}\t{state.alpha}"

  initState m d x₀ := BFGS.initState m d x₀

  updateState method state d := BFGS.updateState method state d
  updateFG method state d := BFGS.updateFG state d
  updateH method state d := BFGS.updateH state

  pick_best_x take_prev state   := if take_prev then state.x_previous else state.x
  pick_best_f take_prev state d := if take_prev then state.f_x_previous else state.f_x

  x_abschange state := (state.x - state.x_previous).abs.max
  x_relchange state := (state.x - state.x_previous).abs.max / state.x.abs.max
  f_abschange d state := Scalar.abs (state.f_x - state.f_x_previous)
  f_relchange d state := Scalar.abs (state.f_x - state.f_x_previous) / Scalar.abs (state.f_x)
  g_residual d state := state.g.abs.max

  f_calls d state := state.f_calls
  g_calls d state := state.g_calls
  h_calls d state := state.h_calls
