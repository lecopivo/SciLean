import SciLean.Util.Approx.Basic
import SciLean.Logic.Function.Argmin
import SciLean.Tactic.DataSynth.HasRevFDerivUpdate
import SciLean.Tactic.DataSynth.HasFwdFDeriv
import SciLean.Tactic.DataSynth.ArrayOperations
import SciLean.Tactic.DataSynth.DefRevDeriv
import SciLean.Data.DataArray

namespace SciLean

instance {R} [RealScalar R] : WellFoundedLT R := sorry_proof

variable
  {R : Type} [RealScalar R] [PlainDataType R] [ToString R]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X]

set_default_scalar R



variable (R)
structure BacktrackingLineSearch.Config where
  /-- Step reduction factor -/
  τ : R := 0.5
  c : R := 0.5
  maxSteps : ℕ := 100
variable {R}


open BacktrackingLineSearch in
def backtrackingLineSearch (cfg : Config R) (f : X → R) (x p : X) (m : R) (α₀ : R) : R := Id.run do

  let mut fxₙ := f x
  let mut αₙ := α₀

  let t := -cfg.c*m
  for _ in [0:cfg.maxSteps] do

    let fx' := f (x + αₙ•p)
    if fxₙ - fx' ≥ αₙ * t then
      break

    fxₙ := fx'
    αₙ := cfg.τ * αₙ

  return αₙ
