import Mathlib.Init.Set

import SciLean.Tactic.GTrans -- import SciLean.Core


namespace SciLean


@[gtrans]
structure SetParametrization {X : Type} (A : Set X)
    (U : outParam <| Type) (param : outParam <| List (Set U × (U → X))) : Prop where

  /-- Every point of the parametrization yields point in `A` -/
  is_parametrization : ∀ p ∈ param, ∀ u ∈ p.1, p.2 u ∈ A
  /-- Every point in `A` has unique parametrization representative -/
  complete_and_unique : ∀ x ∈ A, ∃! p ∈ param, ∃! u ∈ p.1, p.2 u = x
  -- /-- -/
  -- non_empty_interior : ∀ p ∈ param, interior p.1 ≠ ∅
