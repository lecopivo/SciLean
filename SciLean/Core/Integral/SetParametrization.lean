import Mathlib.Init.Set
import Mathlib.Analysis.Calculus.FDeriv.Basic

import SciLean.Tactic.GTrans -- import SciLean.Core


namespace SciLean


@[gtrans]
structure SetParametrization {X : Type} (A : Set X)
    (U : outParam <| Type) [outParam (NormedAddCommGroup U)] (param : outParam <| List (Set U × (U → X))) : Prop where

  /-- Every point of the parametrization yields point in `A` -/
  is_parametrization : ∀ p ∈ param, ∀ u ∈ p.1, p.2 u ∈ A
  /-- Every point in `A` has unique parametrization representative -/
  complete_and_unique : ∀ x ∈ A, ∃! p ∈ param, ∃! u ∈ p.1, p.2 u = x
  -- /-- -/
  -- non_empty_interior : ∀ p ∈ param, interior p.1 ≠ ∅



@[gtrans]
structure SurfaceParametrization
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : Set X)
    (U : outParam <| Type) [outParam (NormedAddCommGroup U)] [outParam (NormedSpace ℝ U)]
    (param : outParam <| List (Set U × (U → X))) : Prop where

  /-- Every point of the parametrization yields point in `A` -/
  is_parametrization : ∀ p ∈ param, ∀ u ∈ p.1, p.2 u ∈ A
  /-- Every point in `A` has unique parametrization representative -/
  complete_and_unique : ∀ x ∈ A, ∃! p ∈ param, ∃! u ∈ p.1, p.2 u = x
  /-- -/
  non_empty_interior : ∀ p ∈ param, interior p.1 ≠ ∅
  /-- differentiable parametrizations -/
  differentiable : ∀ p ∈ param, DifferentiableOn ℝ p.2 p.1
