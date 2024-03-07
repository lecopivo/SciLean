import Mathlib.Data.Sigma.Basic
import SciLean.Core.Vec
import SciLean.Core.Hilbert

namespace SciLean


/--
  -/
@[reducible]
class Diff (X : Type) where
  TangentSpace : X → Type
  [instVecTS : ∀ x, Vec (TangentSpace x)]

attribute [reducible] Diff.TangentSpace Diff.instVecTS Diff.mk

abbrev TangentSpace (X : Type) (x : X) [Diff X] : Type := Diff.TangentSpace x
def TangentBundle (X : Type) [Diff X] : Type := (x : X) × TangentSpace X x

notation "𝒯[" x "]" X:max => (TangentSpace X x)

/-- Provides notation `𝒯 X` for `TangentBundle X` -/
instance (X : Type) [Diff X] : TangentMap X (TangentBundle X) := ⟨⟩

@[reducible]
instance (priority:=low) (X : Type) [Vec X] : Diff X := ⟨(λ _ => X)⟩

@[reducible]
instance (X) [Diff X] (x : X) : Vec (𝒯[x] X) := Diff.instVecTS x

@[reducible]
instance Diff_of_Prod
  (X) [Diff X] (Y) [Diff Y]
  : Diff (X×Y) := ⟨λ (x,y) => 𝒯[x] X × 𝒯[y] Y⟩

@[reducible]
instance Diff_of_funType
  {α : Type}
  (X) [Diff X]
  : Diff (α → X) := ⟨λ x => (a : α) → 𝒯[x a] X⟩


@[reducible]
instance
  (X Y : Type)  (xy : X⊕Y) [Diff X] [Diff Y]
  : Vec (((𝒯[·] X) ⊕ (𝒯[·] Y)) xy) -- (λ xy => match xy with | .inl x => 𝒯[x] X | .inr y => 𝒯[y] Y) xy)  --
  := inferInstance


@[reducible]
instance Diff_of_Sum (X) [Diff X] (Y) [Diff Y]
  : Diff (X⊕Y) := ⟨((𝒯[·] X) ⊕ (𝒯[·] Y))⟩

--------------------------------------------------------------------------------

section TangentSpaceTests

example (x : ℝ) : Vec (𝒯[x] ℝ) = Vec ℝ := by rfl

  -- Opacity test
  private class TestClass (X : Type)
  private instance : TestClass ℝ := ⟨⟩
  private instance : TestClass (ℝ×ℝ) := ⟨⟩
  example : TestClass (𝒯[x] (ℝ×ℝ)) := inferInstance

  variable {X Y Z W Y₁ Y₂ Y₃} [Diff X] [Diff Y] [Diff Z] [Diff W] [Diff Y₁] [Diff Y₂] [Diff Y₃]

  example : (λ ((x,y) : Nat×Nat) => x + y) = (λ xy : Nat×Nat => xy.1 + xy.2) := by rfl; done
  example : (𝒯 (X×Y×Z)) = ((xyz : (X×Y×Z)) × (𝒯[xyz.1] X × 𝒯[xyz.2.1] Y × 𝒯[xyz.2.2] Z)) := by rfl; done
  example (x : X) (y : Y) (z : Z) : 𝒯[(x,y,z)] (X×Y×Z) = (𝒯[x] X × 𝒯[y] Y × 𝒯[z] Z) := by rfl; done

end TangentSpaceTests



--------------------------------------------------------------------------------
