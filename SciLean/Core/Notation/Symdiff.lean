import SciLean.Core.FunctionTransformations

namespace SciLean

open Lean Elab Tactic

theorem cderiv_as_fwdCDeriv {K} [RCLike K] {X Y} [Vec K X] [Vec K Y]
  (f : X → Y)
  : cderiv K f
    =
    fun x dx => (fwdCDeriv K f x dx).2 := by rfl


macro "symdiff" : conv => do
  `(conv|
    (simp (config := {failIfUnchanged := false, zeta := false}) only [cderiv_as_fwdCDeriv, scalarGradient, gradient, scalarCDeriv, revCDerivEval]
     ftrans
     simp (config := {failIfUnchanged := false})
     ring_nf))

macro "symdiff" : tactic => do
  `(tactic| conv => symdiff)
