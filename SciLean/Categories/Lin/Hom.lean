import SciLean.Categories.Lin.Operations

namespace SciLean.Lin

variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

def Hom (X Y : Type) [Vec X] [Vec Y] := { f : X → Y // IsLin f}

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

  def mk {X Y : Type} [Vec X] [Vec Y] (f : X → Y) [IsLin f] : X ⊸ Y := ⟨f, sorry⟩

  macro "fun" xs:Lean.explicitBinders " ⊸ " b:term : term => Lean.expandExplicitBinders `Lin.Hom.mk xs b
  macro "λ" xs:Lean.explicitBinders " ⊸ " b:term : term => Lean.expandExplicitBinders `Lin.Hom.mk xs b

  instance (f : X → (Y → Z)) [IsLin f] [∀ x, IsLin (f x)] : IsLin (λ x => Hom.mk (f x)) := sorry

  #check (Hom.mk (λ (x : X) => Hom.mk (λ (r : ℝ) => r * x)) : X ⊸ (ℝ ⊸ X))
  #check ((fun (x : X) ⊸ x))
  #check ((fun (x : X) (r : ℝ) ⊸ r*x))
  #check ((λ (x : X) (r : ℝ) ⊸ r*x))

end Hom




