import SciLean.Util.Approx.Basic
import SciLean.Logic.Function.Argmin
import SciLean.Tactic.DataSynth.HasRevFDerivUpdate
import SciLean.Tactic.DataSynth.ArrayOperations
import SciLean.Tactic.DataSynth.DefRevDeriv
import SciLean.Data.DataArray
import SciLean.Analysis.Calculus.Notation.Gradient

namespace SciLean

/-!

Based on implementation in Optim.jl
https://github.com/JuliaNLSolvers/Optim.jl/blob/711dfec61acf5dbed677e1af15f2a3347d5a88ad/src/multivariate/solvers/first_order/bfgs.jl

-/

instance {R} [RealScalar R] : WellFoundedLT R := sorry_proof

variable
  {R : Type} [RealScalar R] [PlainDataType R] [ToString R]
  {n : ℕ}

  -- generalize it to
  -- todo: define class `MatrixType M X` saying that `M` is matrix associated with `X`
  -- {X : Type} [ArrayType X I R]
  -- {M : Type} [ArrayType M (I×I) R] -- [MatrixType M X]

set_default_scalar R

namespace BFGS

abbrev OptimM := IO

variable (R n)
structure State where
  /-- previous position -/
  x₀ : R^[n]
  /-- current position -/
  x  : R^[n]
  /-- gradient `∇ f x` -/
  df₀ : R^[n] -- ??
  fx₀ : R
  /-- change in the position `xₙ₊₁ - xₙ` -/
  Δx : R^[n]
  /-- change in the gradient `∇ f xₙ₊₁ - ∇ f xₙ` -/
  Δdf : R^[n] -- ??
  u : R^[n]
  /-- approximation to inverse hessian `H⁻¹` -/
  invH : R^[n,n]
  /-- search direction, equals to `- H⁻¹ * ∇ f x` -/
  p : R^[n] -- ??
variable {R n}


/-- Liner search  -/
def lineSearch (f : R^[n] → R) (x p : R^[n]) (m : R) : OptimM R := sorry

def update (state : State R n) (f : R^[n] → R) (hf : HasRevFDeriv R f f') : OptimM (State R n) := do

  -- todo: add this notation!!!
  -- with_struct state do
  let mut ⟨x₀,x,df₀,fx₀,Δx,Δdf,u,invH,p⟩ := state

  let df := (f' x).2 1 -- ∇! f x
  p := - (invH * df)

  let α ← lineSearch f x p ⟪p,df⟫

  Δx := α • p
  x₀ := x
  x := x + Δx
  df₀ := df

  return ⟨x₀,x,df₀,fx₀,Δx,Δdf,u,invH,p⟩


def updateH (state : State R n) (f : R^[n] → R) (hf : HasRevFDeriv R f f') : OptimM (State R n) := do

  let mut ⟨x₀,x,df₀,fx₀,Δx,Δdf,u,invH,p⟩ := state

  let df := (f' x).2 1 -- ∇! f x
  Δdf := df - df₀

  let s := ⟪Δx, Δdf⟫

  -- update `H⁻¹` only if we can guarangee positive definitness
  if s > 0 then

    -- todo: I would like the implementation to look like this:
    -- invH :=
    --   let H := invH⁻¹
    --   (H + s⁻¹ • Δdf.outerprod Δdf - ⟪Δx,H*Δx⟫ • (H*Δx).outerprod (H*Δx))⁻¹
    --   rewrite_by  .... somehow apply Sherman–Morrison formula

    u := invH*Δdf
    let c1 := (s + ⟪Δdf,u⟫)/s^2
    let c2 := s⁻¹
    invH := invH + c1 • Δx.outerprod Δx
                 - c2 • (u.outerprod Δx + Δx.outerprod u)


  return sorry


end BFGS


def bfgs (f : R^[n] → R) {f'} (hf : HasRevFDerivUpdate R f f') (x₀ : R^[n] := 0) : R^[n] := Id.run do

  let mut xₙ := x₀
  let (fx', updateFun) := f' xₙ
  let df' := updateFun 1 0
  let mut fxₙ := fx'
  let mut dfₙ := df'
  let mut Hₙ := 𝐈 n

  let mut firstRun := true
  for n in [0:10] do

    let pₙ := - (Hₙ * df')

    let α := (argmin (α : R), f (xₙ + α • pₙ))
      -- approx_by
      --   simp only [linese_search_with_wolfe_condition]

    let sₙ := α • pₙ
    let x' := xₙ + sₙ

    let (fx', updateFun) := f' xₙ
    let df' := updateFun 1 0
    let yₙ := df' - dfₙ

    Hₙ := Hₙ + ((⟪sₙ,yₙ⟫ + ⟪yₙ,Hₙ*yₙ⟫)/⟪sₙ,yₙ⟫^2) • sₙ.outerprod sₙ
            - ⟪sₙ,yₙ⟫⁻¹ • ((Hₙ*yₙ).outerprod sₙ + sₙ.outerprod (Hₙᵀ*yₙ))
       -- rewrite_by optimize_array_expr
       -- todo: simplify/optimize this, add function (A.addOuterprod x y) and use that

    -- compute errors
    let Δx := ‖x'-xₙ‖₂
    let Δxᵣ := Δx / ‖xₙ‖₂
    let Δf := ‖fx'-fxₙ‖₂
    let Δfᵣ := Δf / ‖fxₙ‖₂

    dbg_trace s!"\
       ‖xₙ₊₁-xₙ‖       = {Δx}\
       ‖xₙ₊₁-xₙ‖ / ‖xₙ‖ = {Δxᵣ}\
       ‖f(xₙ₊₁) - f(xₙ)‖          = {Δf}\
       ‖f(xₙ₊₁) - f(xₙ)‖ / ‖f(xₙ)‖ = {Δfᵣ}"

    fxₙ := fx'
    xₙ := x'

  return xₙ



-- def cg (f : R^[n] → R) {f' f''} (hf : HasRevFDeriv R f f')  (x₀ : R^[n] := 0) : R^[n] := Id.run do
