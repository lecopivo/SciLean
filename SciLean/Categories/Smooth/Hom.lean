import SciLean.Categories.Smooth.Operations

namespace SciLean.Smooth

variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

def Hom (X Y : Type) [Vec X] [Vec Y] := { f : X → Y // IsSmooth f}

infixr:25 "⟿" => Hom

namespace Hom

  variable (f : X → Y) [IsSmooth f]
  variable (g : X → Y) [IsSmooth g]
  variable (r : ℝ)

  instance : IsSmooth (f + g) :=
  by 
    infer_instance

  instance : IsSmooth (f - g) :=
  by 
    infer_instance

  instance : IsSmooth (r*f) :=
  by 
    conv => 
      enter [1,x]
      simp[HMul.hMul]
    infer_instance

  instance : IsSmooth (-f) :=
  by
    conv =>
      enter [1,x]
      simp[Neg.neg]
    infer_instance

  instance : Add (X ⟿ Y) := ⟨λ f g => ⟨f.1 + g.1, by infer_instance⟩⟩
  instance : Sub (X ⟿ Y) := ⟨λ f g => ⟨f.1 - g.1, by infer_instance⟩⟩
  -- TODO: why is `by infer_instance` not working here?
  instance : HMul ℝ (X ⟿ Y) (X ⟿ Y) := ⟨λ r f => ⟨r * f.1, sorry⟩⟩
  instance : Neg (X ⟿ Y) := ⟨λ f => ⟨-f.1, sorry⟩⟩

  instance : Vec (X ⟿ Y) := sorry

end Hom




