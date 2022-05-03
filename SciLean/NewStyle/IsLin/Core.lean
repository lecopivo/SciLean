import SciLean.Algebra
-- import SciLean.Categories.Basic

namespace SciLean

-- set_option synthInstance.maxHeartbeats 5000

class IsLin {U V} [Vec U] [Vec V] (f : U → V) : Prop :=
  ( add : ∀ x y, f (x + y) = f x + f y )
  ( mul : ∀ (s : ℝ) x, f (s*x) = s * (f x) )

-- set_option synthInstance.maxHeartbeats 500

def LinMap (X Y : Type) [Vec X] [Vec Y] := { f : X → Y // IsLin f }


------------------------------------------------------------------------------------


variable {α β γ : Type} 
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]

instance id.arg_x.isLin 
  : IsLin λ x : X => x := sorry

instance const.arg_y.isLin 
  : IsLin (λ y : Y => (0 : X)) := sorry

instance (priority := low) swap.arg_y.isLin 
  (f : α → Y → Z) [∀ a, IsLin (f a)] 
  : IsLin (λ y x => f x y) := sorry

instance parm.arg_x.isLin 
  (f : X → β → Z) [IsLin f] (y : β) 
  : IsLin (λ x => f x y) := sorry

instance comp.arg_x.isLin 
  (f : Y → Z) [IsLin f] 
  (g : X → Y) [IsLin g]
  : IsLin (λ x => f (g x)) := sorry

instance diag.arg_x.isLin 
  (f : Y₁ → Y₂ → Z) [IsLin (λ yy : Y₁ × Y₂ => f yy.1 yy.2)] 
  (g₁ : X → Y₁) [IsLin g₁]
  (g₂ : X → Y₂) [IsLin g₂] 
  : IsLin (λ x => f (g₁ x) (g₂ x)) := sorry

instance diag_parm.arg_x.isLin 
  (f : Y₁ → Y₂ → Z) [IsLin (λ yy : Y₁ × Y₂ => f yy.1 yy.2)] 
  (g₁ : X → α → Y₁) [IsLin g₁] 
  (g₂ : X → α → Y₂) [IsLin g₂] 
  : IsLin (λ x a => f (g₁ x a) (g₂ x a)) := sorry
