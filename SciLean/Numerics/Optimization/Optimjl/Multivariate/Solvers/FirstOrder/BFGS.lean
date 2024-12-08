import SciLean.Numerics.Optimization.Optimjl.Utilities.Types

/-! Port of Optim.jl, file src/multivariate/solvers/first_order/bfgs.jl

github link:
https://github.com/JuliaNLSolvers/Optim.jl/blob/711dfec61acf5dbed677e1af15f2a3347d5a88ad/src/multivariate/solvers/first_order/bfgs.jl

-/

namespace SciLean.Optimjl



/-- Let binding that deconstructs structure into its fields.

The notation
```
let ⟨..⟩ := s
b
```
expands to
```
let ⟨x₁,...,xₙ⟩ := s
b
```
where `x₁` are field names of struct `s`.

For example, `Prod` has field `fst` and `snd` therefore
```
let ⟨..⟩ := (1,2)
fst + snd
```
as it expands to
```
let ⟨fst,snd⟩ := (1,2)
fst + snd
```
 -/
syntax (name:=let_struct_syntax) withPosition("let" "⟨..⟩" (ident)? ":=" term) optSemicolon(term) : term

open Lean Elab Term Syntax Meta
elab_rules (kind:=let_struct_syntax) : term
| `(let ⟨..⟩ $[$suffix:ident]? := $x:term
    $b) => do

  let X ← inferType (← elabTerm x none)
  let .const struct _ := X.getAppFn' | throwError "structure expected"
  let info := getStructureInfo (← getEnv) struct
  let addSuffix := fun n : Name => suffix.map (fun s => n.appendAfter (s.getId.toString)) |>.getD n
  let ids := info.fieldNames.map (fun n => mkIdent (addSuffix n))
  let stx ← `(let ⟨$ids,*⟩ := $x; $b)
  elabTerm stx none

open Lean Parser
syntax atomic(Term.ident) noWs "." noWs ident ":=" term : doElem

macro_rules
| `(doElem| $s:ident . $a:ident := $x) => `(doElem| $s:ident := {$s with $a:ident := $x})


  -- generalize it to abstract vector array types
  -- todo: define class `MatrixType M X` saying that `M` is matrix associated with `X`
  -- {X : Type} [ArrayType X I R]
  -- {M : Type} [ArrayType M (I×I) R] -- [MatrixType M X]

variable
  {R : Type} [RealScalar R] [PlainDataType R] [ToString R]

def _root_.SciLean.DataArrayN.abs {I} [IndexType I] (x : R^[I]) : R^[I] :=
    x.mapMono (fun x => Scalar.abs x)


set_default_scalar R

namespace BFGS

/-- BFGS configuration -/
structure Method (R : Type) (n : ℕ) [RealScalar R] [PlainDataType R]  where
  alphaguess (phi_0 dphi_0 : R) (d : ObjectiveFunction R (R^[n])) : R
  linesearch (d : ObjectiveFunction R (R^[n])) (x s : R^[n]) (alpha x_ls phi_0 dphi_0 : R) : Option (R × R)
  initial_invH (x : R^[n]) : Option (R^[n,n]) := none
  initial_stepnorm : Option R := none
  -- manifold : Manifold

structure State (R : Type) (n : ℕ) [RealScalar R] [PlainDataType R] where
   /-- current position `xₙ` -/
   x : R^[n]
   /-- previous position `xₙ₋₁`-/
   x_previous : R^[n]
   /-- current gradient `∇f(xₙ)` -/
   g : R^[n]
   /-- previous gradient `∇f(xₙ₋₁)` -/
   g_previous : R^[n]
   /-- current valus `f(xₙ)` -/
   f_x : R
   /-- previous valus `f(xₙ₋₁)` -/
   f_x_previous : R
   /-- position difference `xₙ-xₙ₋₁` -/
   dx : R^[n]
   /-- gradient difference `∇f(xₙ)-∇f(xₙ₋₁)`-/
   dg : R^[n]
   /-- `(∇²f)⁻¹(xₙ)*(xₙ-xₙ₋₁)` i.e. `invH*dx`  -/
   u : R^[n]
   /-- current inverse hessian `(∇²f)⁻¹(xₙ)` -/
   invH : R^[n,n]
   /-- step direction `- (∇²f)⁻¹ ∇f` i.e. `- (invH * g)` -/
   s : R^[n]
   /-- line search scalle `dx := α • s` -/
   alpha : R
   /-- somethig to do with line search -/
   x_ls : R^[n]
   --@add_linesearch_fields()
   f_calls : ℕ
   g_calls : ℕ
   h_calls : ℕ



-- this should be specific to BFGS
def reset_search_direction (state : State R n) (d : ObjectiveFunction R (R^[n]))
    (method : Method R n) : State R n := Id.run do

  let mut ⟨x, x_previous, g, g_previous, f_x, f_x_previous, dx, dg, u, invH, s,alpha,x_ls,f_calls, g_calls, h_calls⟩ := state

  if let some invH₀ := method.initial_invH x then
    invH := invH₀
  else
    if let some stepnorm₀ := method.initial_stepnorm  then
      let initial_scale := stepnorm₀ * ‖g‖₂⁻¹
      invH := initial_scale • 𝐈 n
    else
      invH := 𝐈 n

  s := -g
  return ⟨x, x_previous, g, g_previous, f_x, f_x_previous, dx, dg, u, invH, s,alpha,x_ls,f_calls, g_calls, h_calls⟩


def perform_linesearch (state : State R n) (method : Method R n) (d : ObjectiveFunction R (R^[n])) :
    (State R n × Bool) := Id.run do

  let mut state := state
  let mut dphi_0 := ⟪state.g, state.s⟫

  if dphi_0 >= 0 then
    state := reset_search_direction state d method
    dphi_0 := ⟪state.g, state.s⟫

  let phi_0 := state.f_x

  state := method.alphaguess state phi_0 dphi_0 d

  state . f_x_previous := phi_0
  state . x_previous   := state.x

  if let some (alpha, ϕalpha) :=
        method.linesearch d state.x state.s state.alpha state.x_ls phi_0 dphi_0 then
    state . alpha := alpha
    return (state, true)
  else
    return (state, false)



def updateState (d : ObjectiveFunction R (R^[n])) (state : State R n) (method : Method R n) :
    (State R n × Bool) := Id.run do

  let mut state := state

  state . s := - (state.invH * state.g)
  state . g_previous := state.g

  let mut ls_success := false
  (state,ls_success) := perform_linesearch state method d

  state . dx := state.alpha • state.s
  state . x_previous := state.x
  state . x := state.s + state.x
  state . f_x_previous := state.f_x

  return (state,ls_success)


def updateFG (d : ObjectiveFunction R (R^[n])) (state : State R n) (method : Method R n) :
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



def updateH (d : ObjectiveFunction R (R^[n])) (state : State R n) (method : Method R n) :
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

def assessConvergence (state : State R n) (d : ObjectiveFunction R (R^[n])) (options : Options R) :=

    let ⟨..⟩ := state
    let ⟨..⟩ := options

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


end BFGS


set_option linter.unusedVariables false in
instance {n} : AbstractOptimizerState R (R^[n]) (BFGS.State R n) (BFGS.Method R n) where

  initialConvergence d state x₀ options := (false,false)
  assessConvergence := BFGS.assessConvergence

  updateState := BFGS.updateState
  updateFG := BFGS.updateFG
  updateH := BFGS.updateH

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
