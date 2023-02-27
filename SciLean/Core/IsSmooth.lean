import SciLean.Data.Prod

import SciLean.Core.Attributes
import SciLean.Core.Defs
import SciLean.Core.CoreFunctions

namespace SciLean

open SciLean.Mathlib.Convenient

--------------------------------------------------------------------------------

variable {α β : Type}
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]
variable {Y₁ Y₂ Y₃ : Type} [Vec Y₁] [Vec Y₂] [Vec Y₃]


--- Removing arguments - generalized this 

instance IsSmooth2_to_IsSmooth1_1 (f : X → Y → Z) [IsSmoothNT 2 f]
  : IsSmoothT (λ x => f x) := sorry_proof

instance IsSmooth2_to_IsSmooth1_2 (f : X → Y → Z) [IsSmoothNT 2 f] (x : X)
  : IsSmoothT (λ y => f x y) := sorry_proof


instance IsSmooth3_to_IsSmooth2_1 (f : X → Y → Z → W) [IsSmoothNT 3 f]
  : IsSmoothNT 2 (λ x y => f x y) := sorry_proof

instance IsSmooth3_to_IsSmooth2_2 (f : X → Y → Z → W) [IsSmoothNT 3 f] (x : X)
  : IsSmoothNT 2 (λ y z => f x y z) := sorry_proof


-- instance (f : X → Y → Z → W) [IsSmoothNT 3 f]
--   : IsSmoothT (λ x => f x) := by infer_instance

-- instance (f : X → Y → Z → W) [IsSmoothNT 3 f] (x : X)
--   : IsSmoothT (λ y => f x y) := by infer_instance

-- instance (f : X → Y → Z → W) [IsSmoothNT 3 f] (x : X) (y : Y)
--   : IsSmoothT (λ z => f x y z) := by infer_instance



--- Adding arguments - generalized this 

instance add_extra_2_1 (f : X → Y) [IsSmoothT f]
  : IsSmoothNT 2 (λ (z : Z) x => f x) := sorry_proof

instance add_extra_2_2 (f : X → Y) [IsSmoothT f]
  : IsSmoothNT 2 (λ x (z : Z) => f x) := sorry_proof


instance add_extra_3_1 (f : Y → Z → W) [IsSmoothNT 2 f]
  : IsSmoothNT 3 (λ (x : X) y z => f y z) := sorry_proof

instance add_extra_3_2 (f : X → Z → W) [IsSmoothNT 2 f]
  : IsSmoothNT 3 (λ x (y : Y) z => f x z) := sorry_proof

instance add_extra_3_3 (f : X → Y → W) [IsSmoothNT 2 f]
  : IsSmoothNT 3 (λ x y (z : Z) => f x y) := sorry_proof



-- IsSmoothNT 3 fun x y => f (g₁ x)


instance id.arg_x.isSmooth 
  : IsSmooth λ x : X => x := sorry_proof

instance const.arg_xy.isSmooth 
  : IsSmoothNT 2 λ (x : X) (y : Y) => x := inferInstance

instance const.arg_y.isSmooth (x : X)
  : IsSmoothT λ (y : Y) => x := by apply IsSmooth2_to_IsSmooth1_2 (f := λ x y => x); done

instance (priority := low) swap.arg_y.isSmooth 
  (f : α → Y → Z) [∀ x, IsSmoothT (f x)] 
  : IsSmoothT (λ y x => f x y) := sorry_proof

instance parm.arg_x.isSmooth 
  (f : X → β → Z) [IsSmoothT f] (y : β) 
  : IsSmoothT (λ x => f x y) := sorry_proof

instance (priority := mid-1) subst.arg_x.isSmooth 
  (f : X → Y → Z) [IsSmoothNT 2 f]
  (g : X → Y) [IsSmoothT g] :
  IsSmoothT (λ x => f x (g x)) := sorry_proof

instance (priority := mid-1) subst2.arg_x.isSmooth 
  (f : X → Y → Y₁ → Z) [IsSmoothNT 3 f]
  (g : X → Y → Y₁) [IsSmoothNT 2 g] :
  IsSmoothNT 2 (λ x y => f x y (g x y)) := sorry_proof

instance (priority := mid-1) subst3.arg_x.isSmooth 
  (f : X → Y → Z → Y₁ → W) [IsSmoothNT 4 f]
  (g : X → Y → Z → Y₁) [IsSmoothNT 3 g] :
  IsSmoothNT 3 (λ x y z => f x y z (g x y z)) := sorry_proof

instance comp.arg_x.isSmooth 
  (f : Y → Z) [IsSmoothT f]
  (g : X → Y) [IsSmoothT g] 
  : IsSmoothT (λ x => f (g x)) := by infer_instance

instance {Ws W' : Type} [Vec Ws] [Vec W']
  (f : Z → W) [Prod.Uncurry n W Ws W'] [IsSmoothNT (n+1) f]
  (g : X → Y → Z) [IsSmoothNT 2 g]
  : IsSmoothNT (n+2) fun x y => f (g x y) := sorry_proof

instance hoho {Ws W' : Type} [Vec Ws] [Vec W']
  (f : Y₁ → Y₂→ W) [Prod.Uncurry n W Ws W'] [IsSmoothNT (n+2) f]
  (g₁ : X → Y → Z → Y₁) [IsSmoothNT 3 g₁]
  (g₂ : X → Y → Z → Y₂) [IsSmoothNT 3 g₂]
  : IsSmoothNT (n+3) fun x y z => f (g₁ x y z) (g₂ x y z) := sorry_proof

instance comp2.arg_x.isSmooth
  (f : Y₁ → Y₂ → Z) [IsSmoothNT 2 f]
  (g₁ : X → Y → Y₁) [IsSmoothNT 2 g₁]
  (g₂ : X → Y → Y₂) [IsSmoothNT 2 g₂]
  : IsSmoothNT 2 (λ x y => f (g₁ x y) (g₂ x y)) := 
by
  -- have : IsSmoothNT 3 fun x y => f (g₁ x y) := sorry_proof
  infer_instance 

instance comp3.arg_x.isSmooth 
  (f : Y₁ → Y₂ → Y₃ → W) [IsSmoothNT 3 f]
  (g₁ : X → Y → Z → Y₁) [IsSmoothNT 3 g₁]
  (g₂ : X → Y → Z → Y₂) [IsSmoothNT 3 g₂]
  (g₃ : X → Y → Z → Y₃) [IsSmoothNT 3 g₃]
  : IsSmoothNT 3 (λ x y z => f (g₁ x y z) (g₂ x y z) (g₃ x y z)) := 
by
  -- have : IsSmoothNT 4 fun x y z => f (g₁ x y z) (g₂ x y z) := by apply hoho
  infer_instance

instance diag.arg_x.isSmooth
  (f : Y₁ → Y₂ → Z) [IsSmoothNT 2 f]
  (g₁ : X → Y₁) [IsSmoothT g₁]
  (g₂ : X → Y₂) [IsSmoothT g₂]
  : IsSmoothT (λ x => f (g₁ x) (g₂ x)) := by infer_instance

-- instance Prod.fst.arg_xy.isSmooth : IsSmooth (Prod.fst : X×Y → X) := sorry_proof

function_property Prod.fst (xy : X×Y) argument xy isSmooth := sorry_proof
function_property Prod.snd (xy : X×Y) argument xy isSmooth := sorry_proof
function_property HAdd.hAdd (x y : X) argument (x,y) isSmooth := sorry_proof

--------------------------------------------------------------------------------
-- Highorder unification instances
--------------------------------------------------------------------------------

instance(priority:=low) comp.arg_x.isSmooth_unif1 {X Y Z} [Vec X] [Vec Y] [Vec Z] {α β : Type} (a)
  (f : Y → α → Z) [IsSmoothT λ y => f y a]
  (g : X → Y) [IsSmoothT g] 
  : IsSmoothT (λ x => f (g x) a) :=
by
  try infer_instance
  apply comp.arg_x.isSmooth (λ y => f y a)


instance(priority:=low+1) comp.arg_x.isSmooth_unif {X Y Z} [Vec X] [Vec Y] [Vec Z] {α β : Type} (a b)
  (f : Y → α → β → Z) [IsSmoothT λ y => f y a b]
  (g : X → Y) [IsSmoothT g] 
  : IsSmoothT (λ x => f (g x) a b) :=
by
  try infer_instance
  apply comp.arg_x.isSmooth (λ y => f y a b)


--------------------------------------------------------------------------------
-- Smooth Map - part 1
--------------------------------------------------------------------------------

function_properties SmoothMap.val (f : X⟿Y) (x : X) : Y
argument (f,x)
  isSmooth := sorry_proof
argument f 
  isSmooth := by apply IsSmoothN.mk
argument x 
  isSmooth := by apply IsSmoothN.mk

--------------------------------------------------------------------------------
-- Smooth Map Lambda Notation --
--------------------------------------------------------------------------------

@[macro_inline]
abbrev SmoothMap.mk' (f : X → Y) [inst : IsSmoothT f] : X ⟿ Y := ⟨f, inst.proof⟩

open Lean.TSyntax.Compat in
macro "fun" xs:Lean.explicitBinders " ⟿ " b:term : term => 
  Lean.expandExplicitBinders `SciLean.SmoothMap.mk' xs b

open Lean.TSyntax.Compat in
macro "λ"   xs:Lean.explicitBinders " ⟿ " b:term : term => 
  Lean.expandExplicitBinders `SciLean.SmoothMap.mk' xs b

@[simp, diff_simp]
theorem SmoothMap.eta_reduction (f : X ⟿ Y)
    : (λ (x : X) ⟿ f x) = f := by rfl; done

instance SmoothMap.mk'.arg_f.isSmooth
  (f : W → X → Y) [IsSmoothNT 2 f]
  : IsSmoothT λ w => λ x ⟿ f w x := by (try infer_instance); sorry_proof

--------------------------------------------------------------------------------
-- Smooth Map - part 2
--------------------------------------------------------------------------------


instance scomb.arg_fgx.isSmooth [Vec X] [Vec Y] [Vec Z] 
  : IsSmoothNT 3 λ (f : X⟿Y⟿Z) (g : X⟿Y) (x : X) => f x (g x) := by (try infer_instance); sorry_proof

instance scomb.arg_gx.isSmooth [Vec X] [Vec Y] [Vec Z] 
  (f : X → Y → Z) [IsSmoothNT 2 f]
  : IsSmoothNT 2 λ (g : X⟿Y) (x : X) => f x (g x) := 
by 
  infer_instance
  done

-- This was necessary at some point ... most likely delete it
-- instance scomb.arg_gx.isSmooth_alt  {X Y Y' Z} [Vec X] [Vec Y] [Vec Y'] [Vec Z] 
--   (f : X → Y → Y' → Z) [IsSmoothNT 3 f]  
--   (g' : X → Y') [IsSmoothNT 1 g']
--   : IsSmoothNT 2 λ (g : X⟿Y) x => f x (g x) (g' x) := 
-- by 
--   infer_instance
--   done

instance comp.arg_fgx.isSmooth {X Y Z} [Vec X] [Vec Y] [Vec Z]
  : IsSmoothNT 3 (λ (f : Y ⟿ Z) (g : X ⟿ Y) x => f (g x)) := 
by (try infer_instance); sorry_proof

instance comp.arg_gx.isSmooth {X Y Z} [Vec X] [Vec Y] [Vec Z] 
  (f : Y → Z) [IsSmoothT f] 
  : IsSmoothNT 2 (λ (g : X ⟿ Y) x => f (g x)) := by infer_instance

