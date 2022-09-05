import SciLean.Algebra

namespace SciLean

  class Basis (X : Type u) (ι : outParam $ Type v) (K : outParam $ Type w) where
    basis : ι → X
    proj  : ι → X → K

  class OrthBasis (X : Type u) [Basis X ι K] : Prop where

  macro:max "𝔼" i:term : term => `(Basis.basis $i)

  /- Currently we assume that the basis for FinVec is orthonormal through out the codebase. 
     For example divergence assumes this.
     Is it safe to assume that the default basis is orthonormal? -/
  class FinVec (X : Type) (ι : outParam $ Type) [outParam $ Enumtype ι] extends Hilbert X, Basis X ι ℝ  -- where 
    -- proj_inner : ∀ (x : X) i, Basis.proj i x = ⟪Basis.basis i, x⟫
    -- sum_proj : ∀ x : X, (∑ i : ι, (Basis.proj i x) * (Basis.basis i : X)) = x
    -- orthonormality : ∀ i j : ι, ⟪(Basis.basis i : X), (Basis.basis j : X)⟫ = if i=j then 1 else 0

  instance : Basis ℝ Unit ℝ :=
  {
    basis := λ _ => 1
    proj  := λ _ x => x
  }

  instance : FinVec ℝ Unit := FinVec.mk


  @[inferTCGoalsRL]
  instance {X Y ι κ : Type} [Enumtype ι] [Enumtype κ] [Zero X] [Zero Y] 
    [Basis X ι ℝ] [Basis Y κ ℝ] : Basis (X×Y) (ι⊕κ) ℝ where
    basis idx := 
      match idx with
      | .inl i => (𝔼 i, 0)
      | .inr j => (0, 𝔼 j)
    proj := λ idx (x,y) => 
      match idx with
      | .inl i => Basis.proj i x
      | .inr j => Basis.proj j y

  @[inferTCGoalsRL]
  instance {X Y ι κ} [Enumtype ι] [Enumtype κ] [FinVec X ι] [FinVec Y κ]
    : FinVec (X×Y) (ι⊕κ) := ⟨⟩
