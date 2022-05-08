import SciLean.Algebra

namespace SciLean

-- TODO: 
--   - define adjoint in distributional sense and 
--   - redefine SemiHilbert as space with test functions and pairng with them
class HasAdjoint {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) : Prop
    -- has_dual : ∀ y, HasDual (λ x Ω => ⟪y, f x⟫[f‡ Ω])

variable {α β γ : Type}
variable {X Y Z : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
variable {Y₁ Y₂ : Type} [SemiHilbert Y₁] [SemiHilbert Y₂]
variable {ι κ : Type} [Enumtype ι] [Enumtype κ]

-- I combinator
instance id.arg_x.hasAdjoint
  : HasAdjoint λ x : X => x := sorry

instance const.arg_x.hasAdjoint
  : HasAdjoint (λ (x : X) (i : ι) => x)
:= sorry

instance const.arg_y.hasAdjoint
  : HasAdjoint (λ (y : Y) => (0:X)) := sorry

instance (priority := low) swap.arg_y.hasAdjoint
  (f : ι → Y → Z) [∀ x, HasAdjoint (f x)]
  : HasAdjoint (λ y x => f x y) := sorry

instance comp.arg_x.hasAdjoint
  (f : Y → Z) [HasAdjoint f] 
  (g : X → Y) [HasAdjoint g] 
  : HasAdjoint (λ x => f (g x)) := sorry

instance diag.arg_x.hasAdjoint
  (f : Y₁ → Y₂ → Z) [HasAdjoint (λ yy : Y₁ × Y₂ => f yy.1 yy.2)] 
  (g₁ : X → Y₁) [HasAdjoint g₁] 
  (g₂ : X → Y₂) [HasAdjoint g₂] 
  : HasAdjoint (λ x => f (g₁ x) (g₂ x)) := sorry

instance eval.arg_x.parm1.hasAdjoint
  (f : X → ι → Z) [HasAdjoint f] (i : ι) 
  : HasAdjoint (λ x => f x i) := sorry


--------------------------------------------------------------------
-- Variants a of theorems at points --
-- These are necessary as higher order unification is only approximated

instance comp.arg_x.parm1.hasAdjoint
  (a : α)
  (f : Y → α → Z) [HasAdjoint (λ y => f y a)]
  (g : X → Y) [HasAdjoint g] 
  : HasAdjoint (λ x => f (g x) a)
:= by 
  (apply comp.arg_x.hasAdjoint (λ y => f y a) g) done

instance comp.arg_x.parm2.hasAdjoint
  (a : α) (b : β)
  (f : Y → α → β → Z) [HasAdjoint (λ y => f y a b)]
  (g : X → Y) [HasAdjoint g] 
  : HasAdjoint (λ x => f (g x) a b)
:= by 
  (apply comp.arg_x.hasAdjoint (λ y => f y a b) g) done

instance comp.arg_x.parm3.hasAdjoint
  (a : α) (b : β) (c : γ)
  (f : Y → α → β → γ → Z) [HasAdjoint (λ y => f y a b c)]
  (g : X → Y) [HasAdjoint g] 
  : HasAdjoint (λ x => f (g x) a b c)
:= by 
  (apply comp.arg_x.hasAdjoint (λ y => f y a b c) g) done

instance diag.arg_x.parm1.hasAdjoint
  (a : α)
  (f : Y₁ → Y₂ → α → Z) [HasAdjoint (λ (y₁,y₂) => f y₁ y₂ a)] 
  (g₁ : X → Y₁) [HasAdjoint g₁] 
  (g₂ : X → Y₂) [HasAdjoint g₂] 
  : HasAdjoint (λ x => f (g₁ x) (g₂ x) a)
:= by 
  (apply diag.arg_x.hasAdjoint (λ y₁ y₂ => f y₁ y₂ a) g₁ g₂) done

instance diag.arg_x.parm2.hasAdjoint
  (a : α) (b : β)
  (f : Y₁ → Y₂ → α → β → Z) [HasAdjoint (λ (y₁,y₂) => f y₁ y₂ a b)] 
  (g₁ : X → Y₁) [HasAdjoint g₁] 
  (g₂ : X → Y₂) [HasAdjoint g₂] 
  : HasAdjoint (λ x => f (g₁ x) (g₂ x) a b)
:= by 
  (apply diag.arg_x.hasAdjoint (λ y₁ y₂ => f y₁ y₂ a b) g₁ g₂) done

instance diag.arg_x.parm3.hasAdjoint
  (a : α) (b : β) (c : γ)
  (f : Y₁ → Y₂ → α → β → γ → Z) [HasAdjoint (λ (y₁,y₂) => f y₁ y₂ a b c)] 
  (g₁ : X → Y₁) [HasAdjoint g₁] 
  (g₂ : X → Y₂) [HasAdjoint g₂] 
  : HasAdjoint (λ x => f (g₁ x) (g₂ x) a b c)
:= by 
  (apply diag.arg_x.hasAdjoint (λ y₁ y₂ => f y₁ y₂ a b c) g₁ g₂) done


