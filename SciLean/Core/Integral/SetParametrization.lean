import Mathlib.Init.Set

import SciLean.Core


namespace SciLean


/-- Predicate that describes a set as a graph of a function(s). -/
@[gtrans]
structure SetParametrization
    {X : Type _} (A : Set X)
    (I : outParam <| Type _) (X₁ X₂ : outParam <| I → Type _)
    (p : outParam <| ∀ i, X₁ i → X₂ i → X)
    (f : outParam <| (i : I) → X₁ i → X₂ i)
    (dom : outParam <| (i : I) → Set (X₁ i)) : Prop where
  /-- all parameters yield poin in `A` -/
  param_set  : ∀ (i : I) (x₁ : X₁ i), (x₁ ∈ dom i) →  p i x₁ (f i x₁) ∈ A
  /-- every point in `A` is parametrized -/
  param_full : ∀ x : X, (x ∈ A) → ∃ (i : I) (x₁ : X₁ i), (x₁ ∈ dom i) ∧ (p i x₁ (f i x₁) = x)
  /-- parametrization is unique -/
  point_uniq : ∀ (i : I) (i' : I) (x₁ : X₁ i) (x₁' : X₁ i'),
    p i x₁ (f i x₁) = p i' x₁' (f i' x₁') → (i = i') ∧ (HEq x₁ x₁')



variable {R} [RealScalar R]

inductive Sign where
  | neg | zero | pos

def sign (x : R) : Sign :=
  match compare x 0 with
  | .lt => .neg
  | .eq => .zero
  | .gt => .pos

def SqrtIndexType : Sign → Type
  | .neg  => Empty
  | .zero => Unit
  | .pos  => Bool



theorem setparametrization_sqrt (f : α → R) (y : R)
    (hf : SetParametrization (f ⁻¹' {Scalar.sqrt y}) I X₁ X₂ p g dom)
    (hf : SetParametrization (f ⁻¹' {-Scalar.sqrt y}) I X₁ X₂ p g' dom') :
    SetParametrization ((fun x => (f x)^2) ⁻¹' {y})
      (I  := (match (sign y) with | .neg => Empty | .zero => Unit | .pos => Bool)×I)
      (X₁ := fun (_,i) => X₁ i)
      (X₂ := fun (_,i) => X₂ i)
      (p := fun (_,i) x y => p i x y)
      (f := fun (j,i) x₁ =>
        match (sign y), j with
        | .zero, _ => sorry
        |  .pos, b => sorry )
      (dom := _) := sorry
