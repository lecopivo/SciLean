import SciLean.Core.Notation.Symdiff
import SciLean.Tactic.LetNormalize
import SciLean.Tactic.LSimp2.Elab
import SciLean.Data.Curry

namespace SciLean

open Lean Elab Tactic

macro "autodiff" : conv => do
  `(conv|
    (lsimp (config := {failIfUnchanged := false, zeta := false, singlePass := true}) only [cderiv_as_fwdCDeriv, scalarGradient, gradient, scalarCDeriv,revCDerivEval]
     ftrans only
     lsimp (config := {failIfUnchanged := false, zeta := false}) [uncurryN, UncurryN.uncurry, curryN, CurryN.curry]))

macro "autodiff" : tactic => do
  `(tactic| conv => autodiff)
