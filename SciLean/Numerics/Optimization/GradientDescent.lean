import SciLean.Util.Approx.Basic
import SciLean.Logic.Function.Argmin
import SciLean.Tactic.DataSynth.HasRevFDerivUpdate
import SciLean.Tactic.DataSynth.ArrayOperations
import SciLean.Tactic.DataSynth.DefRevDeriv
import SciLean.Data.DataArray

namespace SciLean




structure GradientDescent.Config (R) [RealScalar R] where
  maxSteps : ℕ
  rate : R
  absError : R



variable
  {R : Type} [RealScalar R]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X]

set_default_scalar R


structure Optimization.State (R) [RealScalar R] where
  step : ℕ := 0
  Δx : R := 0
  Δx_rel : R := 0
  Δf : R := 0
  Δf_rel : R := 0

open Lean


abbrev OptimizationM (R : Type) [RealScalar R] := StateM (Optimization.State R)


open GradientDescent Optimization in
def gradientDescent [ToString R] [ToString X] (cfg : Config R)
  (f : X → R) {f'} (hf : HasRevFDerivUpdate R f f') (x₀ : X := 0) : OptimizationM R X := do

  let mut val : R := 0
  let mut xₙ := x₀

  dbg_trace "current point: {xₙ}"
  dbg_trace "f(xₙ): {val}"

  let mut firstRun := true
  for i in [0:cfg.maxSteps] do
    let (val',updateFun) := f' xₙ
    let x' := updateFun (-cfg.rate) xₙ

    let Δx := ‖x'-xₙ‖₂
    let Δxᵣ := Δx / ‖xₙ‖₂
    let Δf := ‖val'-val‖₂
    let Δfᵣ := Δf / ‖val‖₂

    xₙ := x'
    val := val'

    dbg_trace "current point: {xₙ}"
    dbg_trace "f(xₙ): {val}"
    -- todo: set state

  return xₙ

-- using Optimization, Zygote
-- rosenbrock(u, p) = (p[1] - u[1])^2 + p[2] * (u[2] - u[1]^2)^2
-- u0 = zeros(2)
-- p = [1.0, 100.0]

-- optf = OptimizationFunction(rosenbrock, AutoZygote())
-- prob = OptimizationProblem(optf, u0, p)

-- sol = solve(prob, Optimization.LBFGS())

variable [PlainDataType R]

def rosenbrock (a b : R) (u : R^[2]) :=
  let x := u[0]
  let y := u[1]
  (a - x)^2 + b * (y - x^2)^2

set_option trace.Meta.Tactic.data_synth true in
def_rev_deriv rosenbrock in u by
  unfold rosenbrock
  data_synth => lsimp

#eval
  gradientDescent
    {maxSteps := 300, rate := 1e-2, absError := 1e-6}
    (rosenbrock 1.0 10.0)
    (by data_synth)
    ⊞[0,3]
  |>.run {}
  |>.fst


variable (a b : R)
