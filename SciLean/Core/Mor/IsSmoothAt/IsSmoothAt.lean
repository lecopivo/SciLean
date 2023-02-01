-- import SciLean.Std.Function
import SciLean.Mathlib.Convenient.Basic

namespace SciLean

open SciLean.Mathlib.Convenient

class IsSmoothAt {X Y} [Vec X] [Vec Y] (x : X) (f : X → Y) : Prop := (is_smooth_at : is_smooth_at f x)

/-- Transitive closure of `IsSmoothAt` -/
class IsSmoothAtT {X Y} [Vec X] [Vec Y] (x : X) (f : X → Y) : Prop := (is_smooth_at : is_smooth_at f x)

instance {X Y} [Vec X] [Vec Y] (f : X → Y) (x : X) [inst : IsSmoothAt x f] : IsSmoothAtT x f := ⟨inst.1⟩


------------------------------------------------------------------------------------

variable {α β : Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]

instance id.arg_x.isSmoothAt (x : X)
  : IsSmoothAt x (λ x' : X => x') := sorry_proof

instance const.arg_y.isSmooth (y : Y) (x : X)
  : IsSmoothAt y (λ _ : Y => x) := sorry_proof

-- Is this true???
instance (priority := low) swap.arg_y.isSmoothAt (y : Y)
  (f : α → Y → Z) [∀ x, IsSmoothAtT y (f x)]
  : IsSmoothAtT y (λ y' x => f x y') := sorry_proof

-- Is this true???
instance parm.arg_x.isSmoothAt (x : X)
  (f : X → β → Z) [IsSmoothAtT x f] (y : β) 
  : IsSmoothAtT x (λ x' => f x' y) := sorry_proof

-- Is this true???
instance (priority := mid-1) subst.arg_x.isSmoothAt (x : X)
  (g : X → Y) [IsSmoothAtT x g]
  (f : X → Y → Z) [IsSmoothAtT x f] [IsSmoothAtT (g x) (f x)]
  : IsSmoothAtT x (λ x' => f x' (g x')) := sorry_proof

instance comp.arg_x.isSmoothAt (x : X)
  (g : X → Y) [IsSmoothAtT x g] 
  (f : Y → Z) [IsSmoothAtT (g x) f]
  : IsSmoothAtT x (λ x' => f (g x')) := inferInstance
 
instance diag.arg_x.isSmoothAt (x : X)
  (g₁ : X → Y₁) [IsSmoothAtT x g₁] 
  (g₂ : X → Y₂) [IsSmoothAtT x g₂]
  (f : Y₁ → Y₂ → Z) [IsSmoothAtT (g₁ x) f] [IsSmoothAtT (g₂ x) (f (g₁ x))]
  : IsSmoothAtT x (λ x => f (g₁ x) (g₂ x)) := inferInstance

----------------------------------------------------------------------


instance (priority := mid-1) subst.arg_x.parm_a.isSmooth
  (x : X) (a : α)
  (g : X → Y) [IsSmoothAtT x g] 
  (f : X → Y → α → Z) [IsSmoothAtT x (λ x' y => f x' y a)] [IsSmoothAtT (g x) (λ y => f x y a)]
  : IsSmoothAtT x (λ x => f x (g x) a) := 
by
  try infer_instance
  apply subst.arg_x.isSmoothAt _ _ (λ x y => f x y a)
  done

-- instance (priority := mid-1) subst.arg_x.parm_Wa.isSmooth 
--   [Vec W₁]
--   (a₁ : α₁) 
--   (f : X → Y → W₁ → α₁ → Z) [IsSmooth (λ x y w₁ => f x y w₁ a₁)] [∀ x, IsSmooth (λ y w₁ => f x y w₁ a₁)] 
--   (g : X → Y) [IsSmooth g] :
--   IsSmooth (λ x w₁ => f x (g x) w₁ a₁) := 
-- by
--   try infer_instance
--   apply subst.arg_x.parm_a.isSmooth a₁ (λ x y α₁ w₁ => f x y w₁ a₁) g
--   done

-- instance (priority := mid-1) subst.arg_x.parm_WWa.isSmooth 
--   [Vec W₁] [Vec W₂]
--   (a₁ : α₁) 
--   (f : X → Y → W₁ → W₂ → α₁ → Z) [IsSmooth (λ x y w₁ w₂ => f x y w₁ w₂ a₁)] [∀ x, IsSmooth (λ y w₁ w₂ => f x y w₁ w₂ a₁)] 
--   (g : X → Y) [IsSmooth g] :
--   IsSmooth (λ x w₁ w₂ => f x (g x) w₁ w₂ a₁) := 
-- by
--   try infer_instance
--   apply subst.arg_x.isSmooth (λ x y w₁ w₂ => f x y w₁ w₂ a₁) g 
--   done

-- instance (priority := mid-1) subst.arg_x.parm_WaW.isSmooth 
--   {W₁ W₂ : Type} [Vec W₁] [Vec W₂]
--   (a₁ : α₁) 
--   (f : X → Y → W₁ → α₁ → W₂ → Z) [IsSmooth (λ x y w₁ w₂ => f x y w₁ a₁ w₂)] [∀ x, IsSmooth (λ y w₁ w₂ => f x y w₁ a₁ w₂)] 
--   (g : X → Y) [IsSmooth g] :
--   IsSmooth (λ x w₁ w₂ => f x (g x) w₁ a₁ w₂) := 
--   -- IsSmooth (λ x w₁ => f x (g x) w₁ a₁) :=   --- TODO: Really odd, when stated like this it gets infered.
-- by
--   try infer_instance
--   apply subst.arg_x.parm_Wa.isSmooth a₁ f g
--   done

-- instance (priority := mid-1) subst.arg_x.parm_aa.isSmooth
--   (a : α) (b : β)
--   (f : X → Y → α → β → Z) [IsSmooth (λ x y => f x y a b)] [∀ x, IsSmooth (λ y => f x y a b)] 
--   (g : X → Y) [IsSmooth g] :
--   IsSmooth (λ x => f x (g x) a b) := 
-- by
--   try infer_instance
--   apply subst.arg_x.isSmooth (λ x y => f x y a b)
--   done

-- instance (priority := mid-1) subst.arg_x.parm_aaa.isSmooth
--   (a : α) (b : β) (c : γ)
--   (f : X → Y → α → β → γ → Z) [IsSmooth (λ x y => f x y a b c)] [∀ x, IsSmooth (λ y => f x y a b c)] 
--   (g : X → Y) [IsSmooth g] :
--   IsSmooth (λ x => f x (g x) a b c) := 
-- by
--   try infer_instance
--   apply subst.arg_x.isSmooth (λ x y => f x y a b c)
--   done
