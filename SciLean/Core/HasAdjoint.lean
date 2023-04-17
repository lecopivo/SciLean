import SciLean.Core.IsLin
import SciLean.Core.Hilbert

namespace SciLean

open SciLean.Mathlib.Convenient
  

-- class HasAdjointNT {X Y : Type} {Xs Y' : Type} [SemiHilbert Xs] [SemiHilbert Y'] 
--   (n : Nat) (f : X → Y) [Prod.Uncurry n (X → Y) Xs Y'] : Prop where
--   proof : has_adjoint (uncurryN n f) ∧ is_linear (uncurryN n f) ∧ is_smooth (uncurryN n f)


-- class HasAdjointN {X Y : Type} {Xs Y' : Type} [SemiHilbert Xs] [SemiHilbert Y'] 
--   (n : Nat) (f : X → Y) [Prod.Uncurry n (X → Y) Xs Y'] extends HasAdjointNT n f : Prop


-- abbrev HasAdjointT {X Y : Type} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) := HasAdjointNT 1 f
-- abbrev HasAdjoint {X Y : Type} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) := HasAdjointN 1 f

-- --------------------------------------------------------------------------------


-- instance instHasAdjoint_is_IsLin {X Y : Type} {Xs Y' : Type} [SemiHilbert Xs] [SemiHilbert Y'] 
--   (n : Nat) (f : X → Y) [Prod.Uncurry n (X → Y) Xs Y'] 
--   [inst : HasAdjointN n f]  : IsLinN n f := IsLinN.mk (toIsLinNT:=⟨sorry_proof,sorry_proof⟩)

-- instance instHasAdjoint_is_IsSmooth {X Y : Type} {Xs Y' : Type} [SemiHilbert Xs] [SemiHilbert Y'] 
--   (n : Nat) (f : X → Y) [Prod.Uncurry n (X → Y) Xs Y'] 
--   [HasAdjointN n f]  : IsSmoothNT n f := inferInstance


--------------------------------------------------------------------------------

variable {α β : Type}
variable {X Y Z W : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] [SemiHilbert W]
variable {Y₁ Y₂ Y₃ : Type} [SemiHilbert Y₁] [SemiHilbert Y₂] [SemiHilbert Y₃]
variable {ι κ : Type} [Index ι]

@[fun_prop_rule]
theorem HasAdjoint.rule_id 
  : HasAdjoint (λ x : X => x) := sorry

@[fun_prop_rule]
theorem HasAdjoint.rule_comp 
  (f : Y → Z) [HasAdjoint f]
  (g : X → Y) [HasAdjoint g]
  : HasAdjoint (λ x => f (g x)) := sorry

@[fun_prop_rule]
theorem HasAdjoint.rule_prodMk
  (f : X → Y) [HasAdjoint f]
  (g : X → Z) [HasAdjoint g]
  : HasAdjoint (λ x => (f x, g x)) := sorry

@[fun_prop_rule]
theorem HasAdjoint.rule_pi
  (f : ι → X → Y) [∀ i, HasAdjoint (f i)]
  : HasAdjoint (λ x i => f i x) := sorry

@[fun_prop_rule]
theorem HasAdjoint.rule_eval (i : ι)
  : HasAdjoint (λ (f : ι → X)  => f i) := sorry

@[fun_prop_rule]
theorem HasAdjoint.rule_comp_eval 
  (i : ι) (f : X → ι → Y) [HasAdjoint f]
  : HasAdjoint (λ x => f x i) := HasAdjoint.rule_comp (λ g : ι → Y => g i) f

@[fun_prop_rule]
theorem HasAdjoint.rule_fst
  : HasAdjoint (λ xy : X×Y => xy.1) := sorry

@[fun_prop_rule]
theorem HasAdjoint.rule_snd
  : HasAdjoint (λ xy : X×Y => xy.2) := sorry

#exit

instance HasAdjoint_add_extra_2_1 (f : X → Y) [hf : HasAdjointT f]
  : HasAdjointNT 2 (λ (z : Z) x => f x) := sorry_proof

instance HasAdjoint_add_extra_2_2 (f : X → Y) [HasAdjointT f]
  : HasAdjointNT 2 (λ x (z : Z) => f x) := sorry_proof

instance HasAdjoint_add_extra_3_1 (f : Y → Z → W) [HasAdjointNT 2 f]
  : HasAdjointNT 3 (λ (x : X) y z => f y z) := sorry_proof

instance HasAdjoint_add_extra_3_2 (f : X → Z → W) [HasAdjointNT 2 f]
  : HasAdjointNT 3 (λ x (y : Y) z => f x z) := sorry_proof

instance HasAdjoint_add_extra_3_3 (f : X → Y → W) [HasAdjointNT 2 f]
  : HasAdjointNT 3 (λ x y (z : Z) => f x y) := sorry_proof


-- HasAdjointNT 3 fun x y => f (g₁ x)

--------------------------------------------------------------------------------
-- Core HasAdjoint Instances --
--------------------------------------------------------------------------------

instance id.arg_x.hasAdjoint 
  : HasAdjointT λ x : X => x := sorry_proof

-- I think this is waying that `(λ x y => x : X ⊸ Y → X)` not `(λ x y => x : X ⊸ Y ⟿ X)`
instance const.arg_x.hasAdjoint 
  : HasAdjointT λ (x : X) (i : ι) => x := sorry_proof

instance const.arg_y.hasAdjoint 
  : HasAdjointT λ (y : Y) => (0 : X) := sorry_proof

instance (priority := low) swap.arg_y.hasAdjoint 
  (f : ι → Y → Z) [∀ i, HasAdjointT (f i)] 
  : HasAdjointT (λ y x => f x y) := sorry

instance (priority := low-1) swapDep.arg_y.hasAdjoint 
  {ι Y} {Z : ι → Type} [SemiHilbert Y] [∀ i, SemiHilbert (Z i)] [Index ι]
  (f : (i : ι) → Y → Z i) [∀ x, HasAdjointT (f x)] 
  : HasAdjointT (λ y x => f x y) := sorry


instance (priority := mid-1) subst.arg_x.hasAdjoint 
  (f : X → Y → Z) [HasAdjointNT 2 f]
  (g : X → Y) [HasAdjointT g] :
  HasAdjointT (λ x => f x (g x)) := sorry

instance (priority := mid-1) subst2.arg_x.hasAdjoint 
  (f : X → Y → Y₁ → Z) [HasAdjointNT 3 f]
  (g : X → Y → Y₁) [HasAdjointNT 2 g] :
  HasAdjointNT 2 (λ x y => f x y (g x y)) := sorry

instance (priority := mid-1) subst3.arg_x.hasAdjoint 
  (f : X → Y → Z → Y₁ → W) [HasAdjointNT 4 f]
  (g : X → Y → Z → Y₁) [HasAdjointNT 3 g] :
  HasAdjointNT 3 (λ x y z => f x y z (g x y z)) := sorry

instance comp.arg_x.hasAdjoint 
  (f : Y → Z) [HasAdjointT f]
  (g : X → Y) [HasAdjointT g] 
  : HasAdjointT (λ x => f (g x)) := by infer_instance

instance {Ws W' : Type} [SemiHilbert Ws] [SemiHilbert W']
  (f : Z → W) [Prod.Uncurry n W Ws W'] [HasAdjointNT (n+1) f]
  (g : X → Y → Z) [HasAdjointNT 2 g]
  : HasAdjointNT (n+2) fun x y => f (g x y) := sorry

instance {Ws W' : Type} [SemiHilbert Ws] [SemiHilbert W']
  (f : Y₁ → Y₂→ W) [Prod.Uncurry n W Ws W'] [HasAdjointNT (n+2) f]
  (g₁ : X → Y → Z → Y₁) [HasAdjointNT 3 g₁]
  (g₂ : X → Y → Z → Y₂) [HasAdjointNT 3 g₂]
  : HasAdjointNT (n+3) fun x y z => f (g₁ x y z) (g₂ x y z) := sorry

instance comp2.arg_x.hasAdjoint
  (f : Y₁ → Y₂ → Z) [HasAdjointNT 2 f]
  (g₁ : X → Y → Y₁) [HasAdjointNT 2 g₁]
  (g₂ : X → Y → Y₂) [HasAdjointNT 2 g₂]
  : HasAdjointNT 2 (λ x y => f (g₁ x y) (g₂ x y)) := 
by
  infer_instance 

instance comp3.arg_x.hasAdjoint 
  (f : Y₁ → Y₂ → Y₃ → W) [HasAdjointNT 3 f]
  (g₁ : X → Y → Z → Y₁) [HasAdjointNT 3 g₁]
  (g₂ : X → Y → Z → Y₂) [HasAdjointNT 3 g₂]
  (g₃ : X → Y → Z → Y₃) [HasAdjointNT 3 g₃]
  : HasAdjointNT 3 (λ x y z => f (g₁ x y z) (g₂ x y z) (g₃ x y z)) := 
by
  infer_instance

instance diag.arg_x.hasAdjoint
  (f : Y₁ → Y₂ → Z) [HasAdjointNT 2 f] 
  (g₁ : X → Y₁) [HasAdjointT g₁] 
  (g₂ : X → Y₂) [HasAdjointT g₂] 
  : HasAdjointT (λ x => f (g₁ x) (g₂ x)) := 
by 
  infer_instance
 
instance eval.arg_x.parm1.hasAdjoint
  (f : X → ι → Z) [HasAdjointT f] (i : ι) 
  : HasAdjointT (λ x => f x i) := sorry_proof

instance (priority := mid-1) evalDep.arg_x.parm1.hasAdjoint {Z : ι → Type} [∀ i, SemiHilbert (Z i)]
  (f : X → (i : ι) → Z i) [HasAdjointT f] (i : ι) 
  : HasAdjointT (λ x => f x i) := sorry_proof

  
--------------------------------------------------------------------
-- Variants a of theorems at points --
-- These are necessary as higher order unification is only approximated

instance comp.arg_x.parm1.hasAdjoint
  (a : α)
  (f : Y → α → Z) [HasAdjointT (λ y => f y a)]
  (g : X → Y) [HasAdjointT g] 
  : HasAdjointT (λ x => f (g x) a)
:= by 
  (apply comp.arg_x.hasAdjoint (λ y => f y a) g); done

instance comp.arg_x.parm2.hasAdjoint
  (a : α) (b : β)
  (f : Y → α → β → Z) [HasAdjointT (λ y => f y a b)]
  (g : X → Y) [HasAdjointT g] 
  : HasAdjointT (λ x => f (g x) a b)
:= by 
  (apply comp.arg_x.hasAdjoint (λ y => f y a b) g); done

instance comp.arg_x.parm3.hasAdjoint
  (a : α) (b : β) (c : γ)
  (f : Y → α → β → γ → Z) [HasAdjointT (λ y => f y a b c)]
  (g : X → Y) [HasAdjointT g] 
  : HasAdjointT (λ x => f (g x) a b c)
:= by 
  (apply comp.arg_x.hasAdjoint (λ y => f y a b c) g); done

instance diag.arg_x.parm1.hasAdjoint
  (a : α)
  (f : Y₁ → Y₂ → α → Z) [HasAdjointNT 2 (λ y₁ y₂ => f y₁ y₂ a)]
  (g₁ : X → Y₁) [HasAdjointT g₁] 
  (g₂ : X → Y₂) [HasAdjointT g₂] 
  : HasAdjointT (λ x => f (g₁ x) (g₂ x) a)
:= by 
  (apply diag.arg_x.hasAdjoint (λ y₁ y₂ => f y₁ y₂ a) g₁ g₂); done

instance diag.arg_x.parm2.hasAdjoint
  (a : α) (b : β)
  (f : Y₁ → Y₂ → α → β → Z) [HasAdjointNT 2 (λ y₁ y₂ => f y₁ y₂ a b)] 
  (g₁ : X → Y₁) [HasAdjointT g₁] 
  (g₂ : X → Y₂) [HasAdjointT g₂] 
  : HasAdjointT (λ x => f (g₁ x) (g₂ x) a b)
:= by 
  (apply diag.arg_x.hasAdjoint (λ y₁ y₂ => f y₁ y₂ a b) g₁ g₂); done

instance diag.arg_x.parm3.hasAdjoint
  (a : α) (b : β) (c : γ)
  (f : Y₁ → Y₂ → α → β → γ → Z) [HasAdjointNT 2 (λ y₁ y₂ => f y₁ y₂ a b c)] 
  (g₁ : X → Y₁) [HasAdjointT g₁] 
  (g₂ : X → Y₂) [HasAdjointT g₂] 
  : HasAdjointT (λ x => f (g₁ x) (g₂ x) a b c)
:= by 
  (apply diag.arg_x.hasAdjoint (λ y₁ y₂ => f y₁ y₂ a b c) g₁ g₂); done




