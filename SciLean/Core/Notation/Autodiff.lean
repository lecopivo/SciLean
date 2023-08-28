import SciLean.Core.Notation.Symdiff
import SciLean.Tactic.LetNormalize

namespace SciLean

open Lean Elab Tactic

macro "autodiff" : conv => do
  `(conv|
    (simp (config := {failIfUnchanged := false, zeta := false}) only [cderiv_as_fwdCDeriv, scalarGradient, gradient, scalarCDeriv,revCDerivEval]
     ftrans only
     simp (config := {failIfUnchanged := false, zeta := false})
     conv => let_normalize))

macro "autodiff" : tactic => do
  `(tactic| conv => autodiff)
