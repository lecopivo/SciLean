import SciLean.Notation
import SciLean.Core.Attributes
import SciLean.Core.HasAdjoint
import SciLean.Core.Defs

import SciLean.Tactic.CustomSimp.AllPrePost

namespace SciLean

instance adjoint.arg_y.hasAdjoint {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) [HasAdjointT f]
  : HasAdjoint (f†) := sorry_proof


instance adjoint.arg_fy.isSmooth_2 {X Y W} [Vec W] [SemiHilbert X] [SemiHilbert Y]
  (A : W → X → Y) [∀ x, HasAdjointT (A x)] [∀ w, IsSmoothT (A w)] [IsSmoothT λ w => λ x ⟿ A w x] (w : W)
  : IsSmoothT (λ y => (A w)† y) := sorry_proof

instance adjoint.arg_fy.isSmooth_1 {X Y W} [Vec W] [SemiHilbert X] [SemiHilbert Y]
  (A : W → X → Y) [∀ x, HasAdjointT (A x)] [∀ w, IsSmoothT (A w)] [IsSmoothT λ w => λ x ⟿ A w x]
  : IsSmoothT (λ w => λ y ⟿ (A w)† y) := sorry_proof

-- on Hilbert spaces any linear function has adjoint
-- We only want this to apply for atomic functions that is why we ask for `IsLin` and not for `IsLinT`
-- This causes some issues
-- instance {X Y} [Hilbert X] [Hilbert Y] (A : X → Y) [IsLin A] : HasAdjointT A := sorry_proof

-- example {X Y} [Hilbert X] [Hilbert Y] (A : X ⊸ Y) : IsLinT λ x => adjoint A x := by infer_instance

--------------------------------------------------------------------------------

variable {α β γ : Type}
variable {X Y Z : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
variable {Y₁ Y₂ : Type} [SemiHilbert Y₁] [SemiHilbert Y₂]
variable {ι : Type} [Enumtype ι]

@[simp ↓, diff]
theorem id.arg_x.adj_simp
  : (λ x : X => x)† = λ x => x := sorry_proof

@[simp ↓, diff]
theorem const.arg_x.adj_simp
  : (λ (x : X) (i : ι) => x)† = λ f => ∑ i, f i := sorry_proof

@[simp ↓, diff]
theorem const.arg_y.adj_simp
  : (λ (y : Y) => (0 : X))† = λ y' => (0 : Y) := sorry_proof

@[simp ↓ low-3, diff low-3]
theorem swap.arg_y.adj_simp
  (f : ι → Y → Z) [∀ i, HasAdjointT (f i)] 
  : (λ y i => f i y)† = λ g => ∑ i, (f i)† (g i) := sorry_proof

@[simp ↓ low-4, diff low-4]
theorem swapDep.arg_y.adj_simp
  {ι Y} {Z : ι → Type} [SemiHilbert Y] [∀ i, SemiHilbert (Z i)] [Enumtype ι]
  (f : (i : ι) → Y → Z i) [∀ i, HasAdjointT (f i)] 
  : (λ y i => f i y)† = λ g => ∑ i, (f i)† (g i) := sorry_proof

-- @[simp ↓ (low-1), diff low-4, simp_guard g (λ x => x)]
theorem scomb.arg_x.adj_simp
  (f : X → Y → Z) [HasAdjointNT 2 f]
  (g : X → Y) [HasAdjointT g]
  : (λ x => f x (g x))† 
    =
    λ z' =>
      let (x',y') := (uncurryN 2 f)† z'
      x' + g† y'  
  := sorry_proof
  
@[simp ↓ low, diff low-3, simp_guard g (λ x => x)]
theorem comp.arg_x.adj_simp
  (f : Y → Z) [HasAdjointT f] 
  (g : X → Y) [HasAdjointT g] 
  : (λ x => f (g x))† = λ z => g† (f† z) := sorry_proof

-- @[simp ↓ low]
-- theorem subst.arg_x.adj_simp
--   (f : X → Y → Z) [HasAdjoint (λ ((x,y) : X × Y) => f x y)] 
--   (g : X → Y) [HasAdjoint g] 
--   : (λ x => f x (g x))† 
--     = λ z =>
--         let f' := (λ (x,y) => f x y)†
--         (f' z).1 + g† (f' z).2
-- := by sorry_proof

-- TODO: add simp guard!
@[simp ↓ low, diff low, simp_guard g₁ Prod.fst, g₂ Prod.snd]
theorem diag.arg_x.adj_simp
  (f : Y₁ → Y₂ → Z) [HasAdjointNT 2 f] 
  (g₁ : X → Y₁) [HasAdjointT g₁] 
  (g₂ : X → Y₂) [HasAdjointT g₂] 
  : (λ x => f (g₁ x) (g₂ x))† 
    = λ z => 
      let (y₁, y₂) := (uncurryN 2 f)† z
      (g₁† y₁) + (g₂† y₂)
:= by sorry_proof

-- This prevents an infinite loop when using `adjoint_of_diag` 
-- with `g₁ = Prod.fst` and `g₂ = Prod.snd`
-- @[simp ↓ low+1, diff low+1]
-- theorem diag.arg_x.adj_simp_safeguard
--   (f : X → Y → Z) [HasAdjointNT 2 f]
--   : adjoint (λ xy => f xy.1 xy.2) = (uncurryN 2 f)† := by rfl; done 

@[simp ↓ low, diff low]
theorem eval.arg_f.adj_simp
  (i : ι)
  : (λ (f : ι → X) => f i)† = (λ f' j => ([[i = j]] • f' : X))
:= sorry_proof

@[simp ↓ low-1, diff low-1]
theorem evalDep.arg_f.adj_simp
  {ι} {X : ι → Type} [∀ i, SemiHilbert (X i)] [Enumtype ι]
  (i : ι)
  : (λ (f : (i' : ι) → X i') => f i)† = (λ f' j => (if h : i = j then h ▸ f' else 0))
:= sorry_proof

@[simp ↓ low-1, diff low-1]
theorem eval.arg_x.parm1.adj_simp
  (f : X → ι → Z) [HasAdjointT f] (i : ι)
  : (λ x => f x i)† = (λ x' => f† (λ j => ([[i = j]] • x')))
:= 
by 
  rw [comp.arg_x.adj_simp (λ (x : ι → Z) => x i) f]
  simp; done

@[simp ↓ low-2, diff low-2]
theorem evalDep.arg_x.parm1.adj_simp
  {ι Y} {Z : ι → Type} [SemiHilbert Y] [∀ i, SemiHilbert (Z i)] [Enumtype ι]
  (f : X → (i : ι) → Z i) [HasAdjointT f] (i : ι)
  : (λ x => f x i)† = (λ x' => f† (λ j => (if h : i = j then h ▸ x' else 0)))
:= 
by 
  rw [comp.arg_x.adj_simp (λ (x : (i : ι) → Z i) => x i) f]
  simp; done

--------------------------------------------------------------------------------
-- Unification Hints
--------------------------------------------------------------------------------

unif_hint comp.arg_x.adj_simp.unif_hint_1 (f? : Y → Z)
  (f :  Y → α → Z) (g  : X → Y) (a : α)  
where
  f? =?= λ x => f x a
  |- 
  (λ x => f? (g x))† =?= (λ x => f (g x) a)†

unif_hint comp.arg_x.adj_simp.unif_hint_2 (f? : Y → Z)  
  (f  : Y → α → β → Z) (g  : X → Y) (a : α) (b : β)
where
  f? =?= λ x => f x a b
  |-
  (λ x => f? (g x))† =?= (λ x => f (g x) a b)†

unif_hint comp.arg_x.adj_simp.unif_hint_3 (f? : Y → Z)
  (f  : Y → α → β → γ → Z) (g  : X → Y) (a : α) (b : β) (c : γ)  
where
  f? =?= λ x => f x a b c
  |-
  (λ x => f? (g x))† =?= (λ x => f (g x) a b c)†

-- unif_hint scomb.arg_x.adj_simp.unif_hint_1
--   (a : α)
--   (g? : X → Y) (f? : X → Y → Z)
--   (g : X → Y) (f  : X → Y → α → Z) where
--   g? =?= g
--   f? =?= λ x y => f x y a
--   |-
--   (λ x => f? x (g? x))† =?= (λ x => f x (g x) a)†


unif_hint diag.arg_x.adj_simp.unif_hint_1 (f? : Y₁ → Y₂ → Z)
  (f : Y₁ → Y₂ → α → Z) (g₁ : X → Y₁) (g₂ : X → Y₂) (a : α)
where  
  f? =?= λ y₁ y₂ => f y₁ y₂ a
  |-
  (λ x => f? (g₁ x) (g₂ x))† =?= (λ x => f (g₁ x) (g₂ x) a)† 

unif_hint diag.arg_x.adj_simp.unif_hint_2 (f? : Y₁ → Y₂ → Z)
  (f : Y₁ → Y₂ → α → β → Z) (g₁ : X → Y₁) (g₂ : X → Y₂) (a : α) (b : β)
where  
  f? =?= λ y₁ y₂ => f y₁ y₂ a b
  |-
  (λ x => f? (g₁ x) (g₂ x))† =?= (λ x => f (g₁ x) (g₂ x) a b)† 

unif_hint diag.arg_x.adj_simp.unif_hint_3 (f? : Y₁ → Y₂ → Z)
  (f : Y₁ → Y₂ → α → β → γ → Z) (g₁ : X → Y₁) (g₂ : X → Y₂) (a : α) (b : β) (c : γ)
where  
  f? =?= λ y₁ y₂ => f y₁ y₂ a b c
  |-
  (λ x => f? (g₁ x) (g₂ x))† =?= (λ x => f (g₁ x) (g₂ x) a b c)† 
