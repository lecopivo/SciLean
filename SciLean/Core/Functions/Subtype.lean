import SciLean.Core.Mor
import SciLean.Core.Fun

namespace SciLean

variable {X Y Z} [Vec X] [Vec Y] [Vec Z]

--- `Subtype.mk` is not simply typed so we have to formulate properties
-- through well behaved function `f`

instance Subtype.mk.arg_x.isLin
  (P : Y → Prop) [Vec {y : Y // P y}] 
  (f : X → Y) [IsLin f] 
  (p : (x : X) → P (f x)) 
  : IsLin λ x => Subtype.mk (f x) (p x) := sorry

instance Subtype.mk.arg_x.isSmooth
  (P : Y → Prop) [Vec {y : Y // P y}] 
  (f : X → Y) [IsSmooth f] 
  (p : (x : X) → P (f x)) 
  : IsSmooth λ x => Subtype.mk (f x) (p x) := sorry


-- The fact that the subtype forms a vector space is crucially important!!!
theorem diff_of_vec_subtype_is_subtype 
  (P : Y → Prop) [Vec {y : Y // P y}] 
  (f : X → Y) [IsSmooth f] 
  (p : (x : X) → P (f x)) (x dx : X)
  : P (∂ f x dx) := sorry

@[simp]
theorem Subtype.mk.arg_x.diff_simp
  (P : Y → Prop) [Vec {y : Y // P y}] 
  (f : X → Y) [IsSmooth f] 
  (p : (x : X) → P (f x)) 
  : ∂ (λ x => Subtype.mk (f x) (p x))
    = 
    λ x dx => Subtype.mk (∂ f x dx) (diff_of_vec_subtype_is_subtype P f p x dx) := sorry

----

function_properties Subtype.val {α : Type} {P : α → Prop} (x : Subtype P) : α
argument x [Vec α] [Vec {y : α // P y}]
  isLin := sorry,
  isSmooth, diff_simp
