import SciLean.Core.Tactic.FunctionTransformation.Core
import SciLean.Core.CoreFunctions
import SciLean.Tactic.Basic

namespace SciLean


theorem gradient_as_revDiff {X} [SemiHilbert X] (f : X → ℝ)
  : (∇ f) = λ x => (ℛ f x).2 1 := by rfl

theorem adjDiff_as_revDiff {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y)
  : (∂† x, f x) = λ x => (ℛ f x).2 := by rfl

theorem differential_as_tangentMap {X Y} [Vec X] [Vec Y] (f : X → Y)
  : (∂ f) = λ x dx => (𝒯 f x dx).2 := by rfl

theorem differentialScalar_as_tangentMap {X} [Vec X] (f : ℝ → X)
  : (ⅆ f) = λ x => (𝒯 f x 1).2 := by rfl


macro "autodiff" : conv => `(conv| (rw'[gradient_as_revDiff, adjDiff_as_revDiff, differential_as_tangentMap]; fun_trans only; clean_up_simp))
macro "autodiff" : tactic => `(tactic| conv => autodiff)

macro "symdiff" : conv => `(conv| (simp[gradient, differentialScalar]; fun_trans only; simp))
macro "symdiff" : tactic => `(tactic| conv => symdiff)
