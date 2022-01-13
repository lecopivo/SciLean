import SciLean.Algebra.FinEnumVec

import SciLean.Categories.Lin.Operations

namespace SciLean.Lin

variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

abbrev Hom (X Y : Type) [Vec X] [Vec Y] := { f : X → Y // IsLin f}

infixr:25 " ⊸ " => Hom

instance {X Y} [Vec X] [Vec Y] : CoeFun (X ⊸ Y) (λ _ => X → Y) := ⟨λ f => f.1⟩

instance (priority := high) {X Y} [Vec X] [Vec Y] (f : X ⊸ Y) : IsLin (f : X → Y) := by apply f.2

namespace Hom

  variable (f : X → Y) [IsLin f]
  variable (g : X → Y) [IsLin g]
  variable (r : ℝ)

  instance : IsLin (f + g) :=
  by 
    conv => 
      enter [1,x]
      simp[HAdd.hAdd, Add.add]
    infer_instance; done

  instance : IsLin (f - g) :=
  by 
    conv => 
      enter [1,x]
      simp[HSub.hSub, Sub.sub]
    infer_instance; done

  instance : IsLin (r*f) :=
  by 
    conv => 
      enter [1,x]
      simp[HMul.hMul]
    infer_instance; done

  instance : IsLin (-f) :=
  by
    conv =>
      enter [1,x]
      simp[Neg.neg]
    infer_instance; done

  instance : IsLin (0 : X → Y) :=
  by 
    conv => 
      enter[1]
      simp[OfNat.ofNat]
      simp[Zero.zero]
    infer_instance; done

  instance : Zero (X ⊸ Y) := ⟨⟨0, by infer_instance⟩⟩
  instance : Add (X ⊸ Y) := ⟨λ f g => ⟨f.1 + g.1, by infer_instance⟩⟩
  instance : Sub (X ⊸ Y) := ⟨λ f g => ⟨f.1 - g.1, by infer_instance⟩⟩
  instance : HMul ℝ (X ⊸ Y) (X ⊸ Y) := ⟨λ r f => ⟨r * f.1, by infer_instance⟩⟩
  instance : Neg (X ⊸ Y) := ⟨λ f => ⟨-f.1, by infer_instance⟩⟩

  instance : AddSemigroup (X ⊸ Y) := AddSemigroup.mk sorry
  instance : AddMonoid (X ⊸ Y)    := AddMonoid.mk sorry sorry nsmul_rec sorry sorry
  instance : SubNegMonoid (X ⊸ Y) := SubNegMonoid.mk sorry gsmul_rec sorry sorry sorry
  instance : AddGroup (X ⊸ Y)     := AddGroup.mk sorry
  instance : AddCommGroup (X ⊸ Y) := AddCommGroup.mk sorry

  instance : MulAction ℝ (X ⊸ Y) := MulAction.mk sorry sorry
  instance : DistribMulAction ℝ (X ⊸ Y) := DistribMulAction.mk sorry sorry
  instance : Module ℝ (X ⊸ Y) := Module.mk sorry sorry

  instance : Vec (X ⊸ Y) := Vec.mk

  open SemiInner

  -- instance {X Y R D e ι} [Enumtype ι] [Basis X ι ℝ] [FinVec X ι] [Vec R] [SemiInner Y R D e] [Vec Y]
  --   : SemiInner (X ⊸ Y) R D e :=
  -- {
  --   semiInner := λ f g => ∑ i, ⟪f (𝔼 i), g (𝔼 i)⟫
  --   testFunction := λ D f => ∀ i, testFunction' D (f (𝔼 i))
  -- }

  -- instance {X Y R D e ι} [Enumtype ι] [Basis X ι ℝ] [FinVec X ι] [Trait Y] [Vec R] [SemiHilbert Y R D e] 
  --   : SemiHilbert (X ⊸ Y) R D e :=
  -- {
  --   semi_inner_add := sorry
  --   semi_inner_mul := sorry
  --   semi_inner_sym := sorry
  --   semi_inner_pos := sorry
  --   semi_inner_ext := sorry
  -- }

  -- open SemiInner
  -- @[reducible]
  -- instance {X Y} [FinEnumVec X] [Vec Y] [Trait Y] [SemiInner Y (Trait.R Y) (Trait.D Y) Trait.eval] 
  --   : Trait (X ⊸ Y) := ⟨Trait.R Y, Trait.D Y, Trait.eval⟩

  -- TODO: Figure out why does signature does not get infered here automatically??
  -- example : SemiInner.Trait ℝ := by infer_instance
  example : Hilbert ℝ := by infer_instance
  example : SemiHilbert ℝ ℝ Unit (λ r _ => r) := by infer_instance


  -- set_option trace.Meta.isDefEq true in
  -- instance {X} [FinEnumVec X] : SemiHilbert (X ⊸ ℝ) ℝ Unit (λ r _ => r) := by apply instSemiHilbertHom

  
  -- open SemiInner in
  -- @[reducible] instance {X Y} [Trait Y] [Vec X] [Vec Y] : Trait (X ⊸ Y) := ⟨Trait.sig Y⟩

  -- instance (X Y) [FinEnumVec X] [SemiHilbert Y S] : SemiHilbert (X ⊸ Y) s 

  abbrev mk {X Y : Type} [Vec X] [Vec Y] (f : X → Y) [IsLin f] : X ⊸ Y := ⟨f, by infer_instance⟩

  -- Right now, I prefer this notation
  macro "fun" xs:Lean.explicitBinders " ⊸ " b:term : term => Lean.expandExplicitBinders `SciLean.Lin.Hom.mk  xs b
  macro "λ"   xs:Lean.explicitBinders " ⊸ " b:term : term => Lean.expandExplicitBinders `SciLean.Lin.Hom.mk  xs b

  -- alternative notation
  -- I will decide on one after some use
  macro "funₗ" xs:Lean.explicitBinders " => " b:term : term => Lean.expandExplicitBinders `Lin.Hom.mk  xs b
  macro "λₗ"   xs:Lean.explicitBinders " => " b:term : term => Lean.expandExplicitBinders `Lin.Hom.mk  xs b

  -- Another option would be
  -- λ (x : X)ₗ (r)ₗ => r*x  -- t


  instance (f : X → (Y → Z)) [IsLin f] [∀ x, IsLin (f x)] : IsLin (λ x => Hom.mk (f x)) := sorry
  example : X ⊸ X := fun (x : X) ⊸ x
  example : X ⊸ ℝ ⊸ X := fun (x : X) (r : ℝ) ⊸ r*x
  example : X ⊸ ℝ ⊸ X :=   λ (x : X) (r : ℝ) ⊸ r*x

  -- probably a bad idea
  -- instance {X Y Y' Z'} [Vec X] [Vec Y] [CoeFun Y (λ _ => Y' → Z')] : CoeFun (X ⊸ Y) (λ _ => X → Y' → Z') := ⟨λ f x => f.1 x⟩
  -- example : X → ℝ → X := λ (x : X) (r : ℝ) ⊸ r*x


  -- instance : Coe (X → Y ⊸ Z) (X → Y → Z) := ⟨λ f x => f x⟩
  -- instance : IsLin (λ (f : X → Y ⊸ Z) => (f : X → Y → Z)) := sorry

  -- instance : IsLin (Subtype.val : (X ⊸ Y) → (X → Y)) := sorry
  
  -- instance : Coe (X ⊸ Y ⊸ Z) (X ⊸ Y → Z) := ⟨(λ f => λ (x : X) ⊸ f x)⟩
  -- set_option synthInstance.maxHeartbeats 773
  -- instance : IsLin (λ (f : X ⊸ Y ⊸ Z) => (f : X ⊸ Y → Z)) := by infer_instance --- This needs 773 heartbeats ... why?

  -- Can we infer this automatically? 
  -- set_option synthInstance.maxHeartbeats 2500
  -- instance {X Y Z W} [Vec X] [Vec Y] [Vec Z] [Vec W] : Coe (X ⊸ Y ⊸ Z ⊸ W) (X ⊸ Y → Z → W) := ⟨λ f => λ (x : X) ⊸ f x⟩

end Hom
