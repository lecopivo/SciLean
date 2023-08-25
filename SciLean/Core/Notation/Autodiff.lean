import SciLean.Core.Notation.Symdiff
import SciLean.Tactic.LetNormalize

namespace SciLean

open Lean Elab Tactic

macro "autodiff" : tactic => do
  `(tactic| 
    (simp (config := {zeta := false}) only [cderiv_as_fwdCDeriv, scalarGradient, gradient, scalarCDeriv]
     ftrans only
     simp (config := {zeta := false})
     conv => let_normalize))
