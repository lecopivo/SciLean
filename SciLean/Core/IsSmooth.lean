import SciLean.Data.Prod

import SciLean.Core.SmoothMap

namespace SciLean

open SciLean.Mathlib.Convenient

/-- Transitive closure of `IsSmoothN`
-/
class IsSmoothNT {X Y : Type} {Xs Y' : Type} [Vec Xs] [Vec Y'] 
  (n : Nat) (f : X → Y) [Prod.Uncurry n (X → Y) Xs Y'] : Prop where
  proof : is_smooth (uncurryN n f)

class IsSmoothN {X Y : Type} {Xs Y' : Type} [Vec Xs] [Vec Y'] 
  (n : Nat) (f : X → Y) [Prod.Uncurry n (X → Y) Xs Y'] extends IsSmoothNT n f : Prop


/-- Abbreviation for `IsSmoothN 1`
-/
abbrev IsSmooth {X Y} [Vec X] [Vec Y] (f : X → Y) : Prop := IsSmoothN 1 f


/-- Abbreviation for `IsSmoothNT 1`
-/
abbrev IsSmoothT {X Y} [Vec X] [Vec Y] (f : X → Y) : Prop := IsSmoothNT 1 f


--------------------------------------------------------------------------------

variable {α β : Type}
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]
variable {Y₁ Y₂ Y₃ : Type} [Vec Y₁] [Vec Y₂] [Vec Y₃]


--- Removing arguments - generalized this 

instance (f : X → Y → Z) [IsSmoothNT 2 f]
  : IsSmoothT (λ x => f x) := sorry_proof

instance (f : X → Y → Z) [IsSmoothNT 2 f] (x : X)
  : IsSmoothT (λ y => f x y) := sorry_proof


instance (f : X → Y → Z → W) [IsSmoothNT 3 f]
  : IsSmoothT (λ x => f x) := sorry_proof

instance (f : X → Y → Z → W) [IsSmoothNT 3 f] (x : X)
  : IsSmoothT (λ y => f x y) := sorry_proof

instance (f : X → Y → Z → W) [IsSmoothNT 3 f] (x : X) (y : Y)
  : IsSmoothT (λ z => f x y z) := sorry_proof


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
  : IsSmoothN 2 λ (x : X) (y : Y) => x := sorry_proof

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


instance Prod.fst.arg_xy.isSmooth : IsSmooth (Prod.fst : X×Y → X) := sorry_proof
instance Prod.snd.arg_xy.isSmooth : IsSmooth (Prod.snd : X×Y → Y) := sorry_proof

--------------------------------------------------------------------------------
-- Smooth Map --
--------------------------------------------------------------------------------

/-- SmoothMap is a smooth function

We consider function `f : X ⟿ Y` to be atomically smooth thus we provide IsSmooth
instance and not IsSmoothT instance -/  
instance instSmoothMapIsSmooth (f : X ⟿ Y) : IsSmooth (λ x => f x) := by 
  unfold IsSmooth; apply (IsSmoothN.mk (toIsSmoothNT:=_)); 
  constructor; apply f.2; done


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

@[simp]
theorem SmoothMap.simp_normalize (f : X ⟿ Y) 
    : (λ (x : X) ⟿ f x) = f := by simp; done
