import SciLean.Core.IsSmooth
import SciLean.Core.LinMap

namespace SciLean

open SciLean.Mathlib.Convenient


--TODO: Question?
-- Should linearity include smoothness? Are there usefull linear 
-- functions that are not smooth? 
-- In finite dimension every linear function is smooth but in infitite
-- dimensional spaces it does not have to be the case.
/-- Function `f : X₁ → ... Xₙ → Y'` is a linear as a function `X₁ × ... × Xₙ → Y'`.

Where `X = X₁` and `Y = X₂ → ... → Xₙ → Y'`

Transitive closure of `IsLinNT`
-/
class IsLinNT {X Y : Type} {Xs Y' : Type} [Vec Xs] [Vec Y'] 
  (n : Nat) (f : X → Y) [Prod.Uncurry n (X → Y) Xs Y'] : Prop where
  proof : is_linear (uncurryN n f) ∧ is_smooth (uncurryN n f)


/-- Function `f : X₁ → ... Xₙ → Y'` is a linear as a function `X₁ × ... × Xₙ → Y'`.

Where `X = X₁` and `Y = X₂ → ... → Xₙ → Y'`
-/
class IsLinN {X Y : Type} {Xs Y' : Type} [Vec Xs] [Vec Y'] 
  (n : Nat) (f : X → Y) [Prod.Uncurry n (X → Y) Xs Y'] extends IsLinNT n f : Prop

/-- `IsLin f` says that `f : X → Y` is linear.

Abbreviation for `IsLinN 1 f`
-/
abbrev IsLin {X Y} [Vec X] [Vec Y] (f : X → Y) : Prop := IsLinN 1 f

/-- `IsLinT f` says that `f : X → Y` is linear.

Abbreviation for `IsLinNT 1 f`.

`IsLinT` is transitive closure of `IsLin`.
-/
abbrev IsLinT {X Y} [Vec X] [Vec Y] (f : X → Y) : Prop := IsLinNT 1 f


--------------------------------------------------------------------------------

instance instIsLin_is_IsSmooth {X Y} [Vec X] [Vec Y] {Xs Y' : Type} [Vec Xs] [Vec Y'] 
  (n : Nat) (f : X → Y) [Prod.Uncurry n (X → Y) Xs Y'] [inst : IsLinN n f] 
  : IsSmoothNT n f := ⟨inst.proof.2⟩

--------------------------------------------------------------------------------



variable {α β : Type}
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]
variable {Y₁ Y₂ Y₃ : Type} [Vec Y₁] [Vec Y₂] [Vec Y₃]


--------------------------------------------------------------------------------
-- Adding Arguments Instances --
--------------------------------------------------------------------------------

instance linear_add_extra_2_1 (f : X → Y) [hf : IsLinT f]
  : IsLinNT 2 (λ (z : Z) x => f x) := 
by
  -- An example how to go about proving these things
  let F : Z×X ⊸ Y := Linear.comp ⟨f, hf.1⟩ Linear.snd
  have h : F.1 = λ (zx : Z×X) => f zx.2 := by ext; simp; admit
  constructor; simp[uncurryN, Prod.Uncurry.uncurry]
  rw[← h]; apply F.2

instance linear_add_extra_2_2 (f : X → Y) [IsLinT f]
  : IsLinNT 2 (λ x (z : Z) => f x) := sorry

instance linear_add_extra_3_1 (f : Y → Z → W) [IsLinNT 2 f]
  : IsLinNT 3 (λ (x : X) y z => f y z) := sorry

instance linear_add_extra_3_2 (f : X → Z → W) [IsLinNT 2 f]
  : IsLinNT 3 (λ x (y : Y) z => f x z) := sorry

instance linear_add_extra_3_3 (f : X → Y → W) [IsLinNT 2 f]
  : IsLinNT 3 (λ x y (z : Z) => f x y) := sorry


-- IsLinNT 3 fun x y => f (g₁ x)


--------------------------------------------------------------------------------
-- Core IsLin Instances --
--------------------------------------------------------------------------------

instance id.arg_x.isLin 
  : IsLin λ x : X => x := sorry

-- I think this is waying that `(λ x y => x : X ⊸ Y → X)` not `(λ x y => x : X ⊸ Y ⟿ X)`
instance const.arg_xy.isLin 
  : IsLin λ (x : X) (y : Y) => x := sorry_proof

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
-- Linear Map --
--------------------------------------------------------------------------------

/-- LinMap is a linear function

We consider function `f : X ⊸ Y` to be atomically linear thus we provide IsLin
instance and not IsLinT instance -/  
instance instLinMapIsLin (f : X ⊸ Y) : IsLin (λ x => f x) := by 
  unfold IsLin; apply (IsLinN.mk (toIsLinNT:=_)); 
  constructor; apply f.2; done


--------------------------------------------------------------------------------
-- Lin Map Lambda Notation --
--------------------------------------------------------------------------------

@[macro_inline]
abbrev LinMap.mk' (f : X → Y) [inst : IsLinT f] : X ⊸ Y := ⟨f, inst.proof⟩

open Lean.TSyntax.Compat in
macro "fun" xs:Lean.explicitBinders " ⊸ " b:term : term => 
  Lean.expandExplicitBinders `SciLean.LinMap.mk' xs b

open Lean.TSyntax.Compat in
macro "λ"   xs:Lean.explicitBinders " ⊸ " b:term : term => 
  Lean.expandExplicitBinders `SciLean.LinMap.mk' xs b

@[simp]
theorem LinMap.simp_normalize (f : X ⊸ Y) 
    : (λ (x : X) ⊸ f x) = f := by simp; done
