import SciLean.Categories.Lin.Operations

namespace SciLean.Lin

variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

def Hom (X Y : Type) [Vec X] [Vec Y] := { f : X → Y // IsLin f}

infixr:25 "⊸" => Hom

namespace Hom

  variable (f : X → Y) [IsLin f]
  variable (g : X → Y) [IsLin g]
  variable (r : ℝ)

  instance : IsLin (f + g) :=
  by 
    conv => 
      enter [1,x]
      simp[HAdd.hAdd, Add.add]
    infer_instance

  instance : IsLin (f - g) :=
  by 
    conv => 
      enter [1,x]
      simp[HSub.hSub, Sub.sub]
    infer_instance

  instance : IsLin (r*f) :=
  by 
    conv => 
      enter [1,x]
      simp[HMul.hMul]
    infer_instance

  instance : IsLin (-f) :=
  by
    conv =>
      enter [1,x]
      simp[Neg.neg]
    infer_instance

  instance : Add (X ⊸ Y) := ⟨λ f g => ⟨f.1 + g.1, by infer_instance⟩⟩
  instance : Sub (X ⊸ Y) := ⟨λ f g => ⟨f.1 - g.1, by infer_instance⟩⟩
  -- TODO: why is `by infer_instance` not working here?
  instance : HMul ℝ (X ⊸ Y) (X ⊸ Y) := ⟨λ r f => ⟨r * f.1, sorry⟩⟩
  instance : Neg (X ⊸ Y) := ⟨λ f => ⟨-f.1, sorry⟩⟩


  instance : Vec (X ⊸ Y) := sorry
  

end Hom




