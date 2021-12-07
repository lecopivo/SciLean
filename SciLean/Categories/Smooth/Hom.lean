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
 
  instance : IsSmooth (f + g) :=
  by 
    conv => 
      enter [1,x]
      simp
    infer_instance

  instance : IsSmooth (f - g) :=
  by 
    conv => 
      enter [1,x]
      simp
    infer_instance

  instance : IsSmooth (r*f) :=
  by 
    conv => 
      enter [1,x]
      simp
    infer_instance

  instance : IsSmooth (-f) :=
  by
    conv =>
      enter [1,x]
      simp[Neg.neg]
    infer_instance

  instance : Zero (X ⟿ Y) := ⟨⟨0, by infer_instance⟩⟩
  instance : Add (X ⟿ Y) := ⟨λ f g => ⟨f.1 + g.1, by infer_instance⟩⟩
  instance : Sub (X ⟿ Y) := ⟨λ f g => ⟨f.1 - g.1, by infer_instance⟩⟩
  instance : HMul ℝ (X ⟿ Y) (X ⟿ Y) := ⟨λ r f => ⟨r * f.1, by infer_instance⟩⟩
  instance : Neg (X ⟿ Y) := ⟨λ f => ⟨-f.1, by infer_instance⟩⟩

  instance : AddSemigroup (X ⟿ Y) := AddSemigroup.mk sorry
  instance : AddMonoid (X ⟿ Y)    := AddMonoid.mk sorry sorry nsmul_rec sorry sorry
  instance : SubNegMonoid (X ⟿ Y) := SubNegMonoid.mk sorry gsmul_rec sorry sorry sorry
  instance : AddGroup (X ⟿ Y)     := AddGroup.mk sorry
  instance : AddCommGroup (X ⟿ Y) := AddCommGroup.mk sorry

  instance : MulAction ℝ (X ⟿ Y) := MulAction.mk sorry sorry
  instance : DistribMulAction ℝ (X ⟿ Y) := DistribMulAction.mk sorry sorry
  instance : Module ℝ (X ⟿ Y) := Module.mk sorry sorry

  instance : Vec (X ⟿ Y) := Vec.mk

  abbrev mk {X Y : Type} [Vec X] [Vec Y] (f : X → Y) [IsSmooth f] : X ⟿ Y := ⟨f, by infer_instance⟩

  -- Right now, I prefer this notation
  macro "fun" xs:Lean.explicitBinders " ⟿ " b:term : term => Lean.expandExplicitBinders `SciLean.Smooth.Hom.mk  xs b
  macro "λ"   xs:Lean.explicitBinders " ⟿ " b:term : term => Lean.expandExplicitBinders `SciLean.Smooth.Hom.mk  xs b

  -- alternative notation
  -- I will decide on one after some use
  macro "funₛ" xs:Lean.explicitBinders " => " b:term : term => Lean.expandExplicitBinders `SciLean.Smooth.Hom.mk  xs b
  macro "λₛ"   xs:Lean.explicitBinders " => " b:term : term => Lean.expandExplicitBinders `SciLean.Smooth.Hom.mk  xs b

  instance (f : X → (Y → Z)) [IsSmooth f] [∀ x, IsSmooth (f x)] : IsSmooth (λ x => Hom.mk (f x)) := sorry
  example : X ⟿ X := fun (x : X) ⟿ x
  example : X ⟿ ℝ ⟿ X := fun (x : X) (r : ℝ) ⟿ r*x
  example : X ⟿ ℝ ⟿ X := λ (x : X) (r : ℝ) ⟿ r*x
  example : X ⟿ ℝ → X := λ (x : X) (r : ℝ) ⟿ r*x
  example : X → ℝ ⟿ X := λ (x : X) (r : ℝ) ⟿ r*x


  -- This instance is probably a bad idea ... but I'm not sure
  -- instance {X Y Y' Z'} [Vec X] [Vec Y] [CoeFun Y (λ _ => Y' → Z')] : CoeFun (X ⟿ Y) (λ _ => X → Y' → Z') := ⟨λ f x => f.1 x⟩
  -- example : X → ℝ → X := λ (x : X) (r : ℝ) ⟿ r*x

end Hom




