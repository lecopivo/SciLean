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

  instance : Vec (X ⊸ Y) :=
  {
    add_assoc := sorry,
    add_comm := sorry,
    add_zero := sorry,
    zero_add := sorry
  }

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


  -- instance : Coe (X → Y ⊸ Z) (X → Y → Z) := ⟨λ f x => f x⟩
  -- instance : IsLin (λ (f : X → Y ⊸ Z) => (f : X → Y → Z)) := sorry

  -- instance : IsLin (Subtype.val : (X ⊸ Y) → (X → Y)) := sorry
  
  instance : Coe (X ⊸ Y ⊸ Z) (X ⊸ Y → Z) := ⟨(λ f => λ (x : X) ⊸ f x)⟩
  -- set_option synthInstance.maxHeartbeats 773
  -- instance : IsLin (λ (f : X ⊸ Y ⊸ Z) => (f : X ⊸ Y → Z)) := by infer_instance --- This needs 773 heartbeats ... why?

  -- Can we infer this automatically? 
  -- set_option synthInstance.maxHeartbeats 2500
  -- instance {X Y Z W} [Vec X] [Vec Y] [Vec Z] [Vec W] : Coe (X ⊸ Y ⊸ Z ⊸ W) (X ⊸ Y → Z → W) := ⟨λ f => λ (x : X) ⊸ f x⟩

end Hom
