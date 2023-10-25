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
     simp (config := {zeta:=false}) only [uncurryN, UncurryN.uncurry, CurryN.curry, curryN]
     lsimp (config := {failIfUnchanged := false, zeta := false})))

macro "autodiff" : tactic => do
  `(tactic| conv => autodiff)
