import SciLean.Numerics.Optimization.Optimjl.Utilities.Types
import SciLean.Numerics.Optimization.Optimjl.LinerSearches.Types
import SciLean.Numerics.Optimization.Optimjl.LinerSearches.BackTracking
import SciLean.Data.DataArray
import SciLean.Data.DataArray.Algebra
import SciLean.Data.DataArray.TensorProduct
import SciLean.Data.Vector

set_option linter.unusedVariables false

/-! Port of Optim.jl, file src/multivariate/solvers/first_order/l_bfgs.jl

github link:
https://github.com/JuliaNLSolvers/Optim.jl/blob/711dfec61acf5dbed677e1af15f2a3347d5a88ad/src/multivariate/solvers/first_order/l_bfgs.jl

-/

namespace SciLean.Optimjl


variable
  {R : Type} [RealScalar R] [PlainDataType R]
  [BLAS (DataArray R) R R] [ToString R]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace R X] [ToString X] [CompleteSpace X]

noncomputable section

variable (R X)

structure LBFGS (m : ℕ) extends Options R where
  /-- Linear search that finds appropriate `α` `xₙ₊₁ = xₙ + α • sₙ` -/
  lineSearch : LineSearch0Obj R := .mk (BackTracking R) {}
  -- /-- Guess initial `α` to try given function value and gradient -/
  -- alphaguess (φ₀ dφ₀ : R) /-(d : ObjectiveFunction R X)-/ : R := 1
  -- P : T
  -- precondprep!::Tprep
  -- scaleinvH0 : Bool := true
variable {R X}

instance : Inhabited (LBFGS R m) := ⟨{}⟩

set_default_scalar R

namespace LBFGS

structure State (R X : Type) (m : ℕ) [Zero X] [Neg X] [RealScalar R] [PlainDataType R]
   [BLAS (DataArray R) R R] where
   /-- current position `xₙ₊₁` -/
   x : X
   /-- previous position `xₙ`-/
   x_previous : X := x
   /-- current gradient `∇f(xₙ₊₁)` -/
   g : X := 0
   /-- previous gradient `∇f(xₙ)` -/
   g_previous : X := g
   /-- current valus `f(xₙ₊₁)` -/
   f_x : R
   /-- previous valus `f(xₙ)` -/
   f_x_previous : R := f_x
   /-- difference between positions `xₙ₊₁ - xₙ` -/
   dx : X := 0
   /-- difference between positions `xₙ₊₁ - xₙ` -/
   dg : X := 0
   /-- step direction `- (∇²f)⁻¹ ∇f` -/
   s : X := - g
   /-- position difference `xₙ₊₁-xₙ` -/
   dx_history : Vector X m := ⊞ (i:Fin m) => (0:X)
   /-- gradient difference `∇f(xₙ₊₁)-∇f(xₙ)`-/
   dg_history : Vector X m := ⊞ (i:Fin m) => (0:X)
   /-- ρₙ := 1 / ⟪∇f(xₙ₊₁) - ∇f(xₙ), xₙ₊₁ - xₙ⟫ -/
   ρ : R^[m] := (0 : R^[m])
   /-- -/
   pseudo_iteration : ℤ := 0
   -- /-- preconditioner scale -/
   -- precon : R := 1
   /-- line search scalle `dx := α • s` -/
   alpha : R := 1
   f_calls : ℕ := 0
   g_calls : ℕ := 0
   h_calls : ℕ := 0


open Set in
/-- This function updates search direction `s` from gradient `g` by so called "two loop recursion". -/
def twoloop (g : X) (k : ℤ) (m : ℕ)
    (ρ : Icc (k-m) (k-1) → R) (dx dg : Icc (k-m) (k-1) → X)
    /- (scaleinvH0 : Bool) (precon : R) -/ : X := Id.run do
  if h : m = 0 then
    -g
  else if k-m < 0 then
    return -g
  else

  let mut α : R^[m] := 0

  -- initialize `q`
  let mut q := g

  -- Backward pass
  for h : j in [0:m] do
    have : 0 ≤ j := h.1
    have : j < m := h.2.1
    -- indices going in reverse order
    let iᵣ : Icc (k-m) (k-1) := ⟨k-1-j, by constructor <;> omega⟩
    let jᵣ : Fin m := ⟨m-j-1, by omega⟩

    -- skip iterations with negative index
    if iᵣ.1 < 0 then
      continue

    let dxi := dx iᵣ
    let dgi := dg iᵣ
    let α' := ρ iᵣ * ⟪dxi, q⟫
    α[jᵣ.toIdx] := α'
    q -= α' • dgi

  let mut s :=
    if k > 0 then
      let i₀ : Icc (k-m) (k-1) := ⟨k-1, by constructor <;> omega⟩
      let γ := ⟪dx i₀, dg i₀⟫ / ‖dg i₀‖₂²
      γ • q
    else
      q

  -- forward pass
  for h : j in [0:m] do
    have : 0 ≤ j := h.1
    have : j < m := h.2.1
    -- indices going in forward order
    let i : Icc (k-m) (k-1) := ⟨k-m+j, by constructor <;> omega⟩
    let j : Fin m := ⟨j, by omega⟩

    -- skip iterations with negative index
    if i.1 < 0 then
      continue

    let dxi := dx i
    let dgi := dg i
    let β := ρ i * ⟪dgi,s⟫
    s += (α[j.toIdx] - β) • dxi

  return - s


open Set in
def updateSearchDirection (method : LBFGS R m) (state : State R X m) : State R X m :=  Id.run do
  let mut state := state

  let k : ℤ := state.pseudo_iteration

  let ρ : Icc (k-m) (k-1) → R := fun i =>
    let i : Fin m := ⟨(i.1%m).toNat, by sorry_proof⟩
    state.ρ[i.toIdx]

  let dx : Icc (k-m) (k-1) → X := fun i =>
    let i : Fin m := ⟨(i.1%m).toNat, by sorry_proof⟩
    state.dx_history[i]

  let dg : Icc (k-m) (k-1) → X := fun i =>
    let i : Fin m := ⟨(i.1%m).toNat, by sorry_proof⟩
    state.dg_history[i]

  state.s := twoloop state.g k m ρ dx dg -- method.scaleinvH0 precon

  return state


def reset_search_direction (state : State R X m)
    : State R X m := Id.run do

  let mut state := state

  -- we do not have to reset this data because of the `iᵣ.1 < 0` and `i.1 < 0` checks in `twoloop`
  -- state.dx_history := 0
  -- state.dg_history := 0
  -- state.ρ := 0

  state.pseudo_iteration := 0

  state.s := - state.g

  return state


/-- Find appropriate step length `α`. Resets the search direction if the it is invalid. -/
def perform_linesearch (method : LBFGS R m) (state : State R X m) (d : ObjectiveFunction R X) :
    (Except LineSearchError (State R X m)) := Id.run do

  let mut state := state
  let mut dφ₀ := ⟪state.g, state.s⟫

  let φ₀ := state.f_x

  -- not decreasing, we have to reset the gradient
  if dφ₀ >= 0 then
    state := reset_search_direction state
    dφ₀ := ⟪state.g, state.s⟫

  state.alpha := method.init_alpha
    -- method.alphaguess φ₀ dφ₀

  state.f_x_previous := φ₀
  state.x_previous   := state.x

  let φ := fun α => d.f (state.x + α • state.s)

  -- WARNING! Here we run IO code in pure code, the last `()` is `IO.RealWorld`
  --          This hould be fixed, eiter remove LineSearch.call from IO or make this function in IO
  match method.lineSearch.call φ φ₀ dφ₀ state.alpha () () with
  | .ok ((α,φα),_) _ =>
    state.alpha := α
    return .ok state
  | .error e _ =>
    return .error e


def updateState (method : LBFGS R m) (state : State R X m) (d : ObjectiveFunction R X) :
    (Except LineSearchError (State R X m)) := Id.run do

  let mut state := state

  -- unlike Optim.jl we update pseudo_iteration at the end of updateH
  -- I think this is beause of Julia uses 1-based indexing but we use 0-based
  -- so incrementing pseudo_iteration is more natural at the end of `updateH`
  -- state.pseudo_iteration := state.pseudo_iteration + 1

  -- update the preconditioner
  -- method.precon := precondPrep state.x

  -- Determine the L-BFGS search direction
  state := updateSearchDirection method state

  -- -- store old gradient
  -- state.g_previous := state.g

  match perform_linesearch method state d with
  | .error e => return .error e
  | .ok state' =>

  state := state'

  -- update position
  state.dx := state.alpha • state.s
  state.x_previous := state.x
  state.x := state.x + state.dx

  -- do not update `f_x` as it will be updated in `updateFG`

  -- TODO: update f_calls and g_calls
  --       this information should be somehow given by line search

  return .ok state


def updateFG (state : State R X m) (d : ObjectiveFunction R X) :
    State R X m := Id.run do

  let mut state := state

  state.f_x_previous := state.f_x
  state.g_previous := state.g

  let (f_x, updateFun) := d.f' state.x
  state.f_x := f_x
  state.g := updateFun 1

  state.f_calls += 1
  state.g_calls += 1

  return state


def updateH (state : State R X m)  :
    State R X m := Id.run do

  let mut state := state

  state.dg := state.g - state.g_previous

  let ρ := 1 / ⟪state.dg, state.dx⟫
  if ¬(Scalar.isFinite ρ) then
    -- Optim.jl resets to zero which does not make sense to me
    -- shouldn't we just ignore this step? i.e. reduce `preseudo_iteration` by one?
    state.pseudo_iteration := 0
    return state

  let k := state.pseudo_iteration
  let i : Fin m := ⟨(k%m).toNat, by sorry_proof⟩
  state.dx_history[i] := state.dx
  state.dg_history[i] := state.dg
  state.ρ[i.toIdx] := ρ

  state.pseudo_iteration += 1

  return state


def assessConvergence (method : LBFGS R m) (state : State R X m) :=

    let ⟨..⟩ := state
    let ⟨..⟩ := method.toOptions

    Id.run do

    let mut x_converged := false
    let mut f_converged := false
    let mut f_increased := false
    let mut g_converged := false

    if ‖x - x_previous‖₂² ≤ x_abstol then
      x_converged := true

    if ‖x - x_previous‖₂² ≤ x_reltol * ‖x‖₂² then
      x_converged := true

    if Scalar.abs (f_x - f_x_previous) ≤ f_abstol then
      f_converged := true

    if Scalar.abs (f_x - f_x_previous) ≤ f_reltol * Scalar.abs f_x then
      f_converged := true

    if f_x > f_x_previous then
      f_increased := true

    g_converged := ‖g‖₂² ≤ g_abstol

    return (x_converged, f_converged, g_converged, f_increased)


def initState (method : LBFGS R m) (d : ObjectiveFunction R X) (x₀ : X) : LBFGS.State R X m := Id.run do

  let (fx,df) := d.f' x₀
  let g := df 1

  let mut state : LBFGS.State R X m := {
    x := x₀
    f_x := fx
    f_x_previous := fx
    g := g
    f_calls := 1
    g_calls := 1
  }

  state := reset_search_direction state

  return state

end LBFGS


instance : AbstractOptimizer (LBFGS R m) (LBFGS.State R X m) R X where

  setOptions m opt := {m with toOptions := opt}
  getOptions m := m.toOptions
  getPosition s := s.x
  getGradient s := s.g

  initialConvergence method state := (false,false)
  assessConvergence method state := LBFGS.assessConvergence method state

  printStateHeader := s!"xₙ\txₙ₊₁\tf(xₙ)\t∇f(xₙ)\tsₙ\tα"
  printState state := s!"{state.x_previous}\t{state.x}\t{state.f_x_previous}\t{state.g_previous}\t{state.s}\t{state.alpha}"

  initState m d x₀ := LBFGS.initState m d x₀

  updateState method state d := LBFGS.updateState method state d
  updateFG method state d := LBFGS.updateFG state d
  updateH method state d := LBFGS.updateH state

  pick_best_x take_prev state   := if take_prev then state.x_previous else state.x
  pick_best_f take_prev state d := if take_prev then state.f_x_previous else state.f_x

  x_abschange state := ‖state.x - state.x_previous‖₂²
  x_relchange state := ‖state.x - state.x_previous‖₂² / ‖state.x‖₂²
  f_abschange d state := Scalar.abs (state.f_x - state.f_x_previous)
  f_relchange d state := Scalar.abs (state.f_x - state.f_x_previous) / Scalar.abs (state.f_x)
  g_residual d state := ‖state.g‖₂²

  f_calls d state := state.f_calls
  g_calls d state := state.g_calls
  h_calls d state := state.h_calls
