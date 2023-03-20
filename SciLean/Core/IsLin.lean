import SciLean.Core.IsSmooth
import SciLean.Core.LinMap

namespace SciLean

open SciLean.Mathlib.Convenient


--------------------------------------------------------------------------------



variable {α β : Type}
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]
variable {Y₁ Y₂ Y₃ : Type} [Vec Y₁] [Vec Y₂] [Vec Y₃]


--------------------------------------------------------------------------------
-- Adding Arguments Instances --
--------------------------------------------------------------------------------

instance linear_add_extra_2_1 (f : X → Y) [hf : IsLinT f]
  : IsLinNT 2 (λ (z : Z) x => f x) := sorry_proof

instance linear_add_extra_2_2 (f : X → Y) [IsLinT f]
  : IsLinNT 2 (λ x (z : Z) => f x) := sorry_proof

instance linear_add_extra_3_1 (f : Y → Z → W) [IsLinNT 2 f]
  : IsLinNT 3 (λ (x : X) y z => f y z) := sorry_proof

instance linear_add_extra_3_2 (f : X → Z → W) [IsLinNT 2 f]
  : IsLinNT 3 (λ x (y : Y) z => f x z) := sorry_proof

instance linear_add_extra_3_3 (f : X → Y → W) [IsLinNT 2 f]
  : IsLinNT 3 (λ x y (z : Z) => f x y) := sorry_proof


-- IsLinNT 3 fun x y => f (g₁ x)


--------------------------------------------------------------------------------
-- Core IsLin Instances --
--------------------------------------------------------------------------------

instance id.arg_x.isLin 
  : IsLinT λ x : X => x := sorry_proof

-- I think this is waying that `(λ x y => x : X ⊸ Y → X)` not `(λ x y => x : X ⊸ Y ⟿ X)`
instance const.arg_xy.isLin 
  : IsLinT λ (x : X) (y : Y) => x := sorry_proof

instance (priority := low) swap.arg_y.isLin 
  (f : α → Y → Z) [∀ x, IsLinT (f x)] 
  : IsLinT (λ y x => f x y) := sorry

instance parm.arg_x.isLin 
  (f : X → β → Z) [IsLinT f] (y : β) 
  : IsLinT (λ x => f x y) := sorry

instance (priority := mid-1) subst.arg_x.isLin 
  (f : X → Y → Z) [IsLinNT 2 f]
  (g : X → Y) [IsLinT g] :
  IsLinT (λ x => f x (g x)) := sorry

instance (priority := mid-1) subst2.arg_x.isLin 
  (f : X → Y → Y₁ → Z) [IsLinNT 3 f]
  (g : X → Y → Y₁) [IsLinNT 2 g] :
  IsLinNT 2 (λ x y => f x y (g x y)) := sorry

instance (priority := mid-1) subst3.arg_x.isLin 
  (f : X → Y → Z → Y₁ → W) [IsLinNT 4 f]
  (g : X → Y → Z → Y₁) [IsLinNT 3 g] :
  IsLinNT 3 (λ x y z => f x y z (g x y z)) := sorry

instance comp.arg_x.isLin 
  (f : Y → Z) [IsLinT f]
  (g : X → Y) [IsLinT g] 
  : IsLinT (λ x => f (g x)) := by infer_instance


instance {Ws W' : Type} [Vec Ws] [Vec W']
  (f : Z → W) [Prod.Uncurry n W Ws W'] [IsLinNT (n+1) f]
  (g : X → Y → Z) [IsLinNT 2 g]
  : IsLinNT (n+2) fun x y => f (g x y) := sorry

instance {Ws W' : Type} [Vec Ws] [Vec W']
  (f : Y₁ → Y₂→ W) [Prod.Uncurry n W Ws W'] [IsLinNT (n+2) f]
  (g₁ : X → Y → Z → Y₁) [IsLinNT 3 g₁]
  (g₂ : X → Y → Z → Y₂) [IsLinNT 3 g₂]
  : IsLinNT (n+3) fun x y z => f (g₁ x y z) (g₂ x y z) := sorry

instance comp2.arg_x.isLin
  (f : Y₁ → Y₂ → Z) [IsLinNT 2 f]
  (g₁ : X → Y → Y₁) [IsLinNT 2 g₁]
  (g₂ : X → Y → Y₂) [IsLinNT 2 g₂]
  : IsLinNT 2 (λ x y => f (g₁ x y) (g₂ x y)) := 
by
  infer_instance 

instance comp3.arg_x.isLin 
  (f : Y₁ → Y₂ → Y₃ → W) [IsLinNT 3 f]
  (g₁ : X → Y → Z → Y₁) [IsLinNT 3 g₁]
  (g₂ : X → Y → Z → Y₂) [IsLinNT 3 g₂]
  (g₃ : X → Y → Z → Y₃) [IsLinNT 3 g₃]
  : IsLinNT 3 (λ x y z => f (g₁ x y z) (g₂ x y z) (g₃ x y z)) := 
by
  infer_instance


----------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Lin Map Lambda Notation --
--------------------------------------------------------------------------------

-- instance LinMap.mk'.arg_f.isSmooth {X Y W} [Vec X] [Vec Y] [Vec W]
--   (f : W → X → Y) [IsSmoothNT 2 f] [∀ w, IsLinT (f w)]
--   : IsSmoothT λ w => λ x ⊸ f w x := by (try infer_instance); sorry_proof

