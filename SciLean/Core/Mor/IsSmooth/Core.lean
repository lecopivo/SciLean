import SciLean.Std.Function
import SciLean.Mathlib.Convenient.Basic

import SciLean.Core.Mor.IsLin

namespace SciLean

variable {X Y} [Vec X] [Vec Y]

open SciLean.Mathlib.Convenient

class IsSmooth {X Y} [Vec X] [Vec Y] (f : X → Y) : Prop := (is_smooth : is_smooth f)

def SmoothMap (X Y : Type) [Vec X] [Vec Y] := { f : X → Y // IsSmooth f }

-- Would be a bad instance!
theorem linear_is_smooth (f : X → Y) [IsLin f] : IsSmooth f := sorry

------------------------------------------------------------------------------------

variable {α β : Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]

instance id.arg_x.isSmooth 
  : IsSmooth λ x : X => x := sorry

instance const.arg_y.isSmooth (x : X) 
  : IsSmooth λ y : Y => x := sorry

instance (priority := low) swap.arg_y.isSmooth 
  (f : α → Y → Z) [∀ x, IsSmooth (f x)] 
  : IsSmooth (λ y x => f x y) := sorry

instance parm.arg_x.isSmooth 
  (f : X → β → Z) [IsSmooth f] (y : β) 
  : IsSmooth (λ x => f x y) := sorry

instance comp.arg_x.isSmooth 
  (f : Y → Z) [IsSmooth f]
  (g : X → Y) [IsSmooth g] 
  : IsSmooth (λ x => f (g x)) := sorry

instance diag.arg_x.isSmooth 
  (f : Y₁ → Y₂ → Z) [IsSmooth f] [∀ y₁, IsSmooth (f y₁)] 
  (g₁ : X → Y₁) [IsSmooth g₁] 
  (g₂ : X → Y₂) [IsSmooth g₂] :
  IsSmooth (λ x => f (g₁ x) (g₂ x)) := sorry



