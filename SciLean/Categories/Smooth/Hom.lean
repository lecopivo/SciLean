import SciLean.Categories.Smooth.Operations

namespace SciLean.Smooth

variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

def Hom (X Y : Type) [Vec X] [Vec Y] := { f : X → Y // IsSmooth f}

infixr:25 "⟿" => Hom

instance {X Y} [Vec X] [Vec Y] : CoeFun (X ⟿ Y) (λ _ => X → Y) := ⟨λ f => f.1⟩
instance {X Y} [Vec X] [Vec Y] (f : X ⟿ Y) : IsSmooth (f : X → Y) := by apply f.2

namespace Hom

  variable (f : X → Y) [IsSmooth f]
  variable (g : X → Y) [IsSmooth g]
  variable (r : ℝ)

  -- instance : IsSmooth (f + g) :=
  -- by 
  --   conv => 
  --     enter [1,x]
  --     simp[HAdd.hAdd, Add.add]
  --   infer_instance

  -- instance : IsSmooth (f - g) :=
  -- by 
  --   conv => 
  --     enter [1,x]
  --     simp[HSub.hSub, Sub.sub]
  --   infer_instance

  -- instance : IsSmooth (r*f) :=
  -- by 
  --   conv => 
  --     enter [1,x]
  --     simp[HMul.hMul]
  --   infer_instance

  -- instance : IsSmooth (-f) :=
  -- by
  --   conv =>
  --     enter [1,x]
  --     simp[Neg.neg]
  --   infer_instance

  -- instance : Add (X ⟿ Y) := ⟨λ f g => ⟨f.1 + g.1, sorry⟩⟩
  -- instance : Sub (X ⟿ Y) := ⟨λ f g => ⟨f.1 - g.1, sorry⟩⟩
  -- instance : HMul ℝ (X ⟿ Y) (X ⟿ Y) := ⟨λ r f => ⟨r * f.1, by infer_instance⟩⟩
  -- instance : Neg (X ⟿ Y) := ⟨λ f => ⟨-f.1, by infer_instance⟩⟩

  instance : Vec (X ⟿ Y) := sorry

end Hom




