import SciLean.Core.Defs
import SciLean.Core.IsInv

namespace SciLean


variable {X Y Z : Type} [Nonempty X] [Nonempty Y] [Nonempty Z]


--------------------------------------------------------------------------------
-- Inverse rules
--------------------------------------------------------------------------------

@[fun_trans_rule]
theorem invFun.rule_id (X) [Nonempty X]
  : (λ x : X => x)⁻¹
    =
    λ x => x := sorry

@[fun_trans_rule]
theorem invFun.rule_comp 
  (f : Y → Z) [IsInv f]
  (g : X → Y) [IsInv g]
  : (λ x : X => f (g x))⁻¹
    =
    λ x' => g⁻¹ (f⁻¹ x') := sorry

@[fun_trans_rule]
theorem invFun.rule_letComp 
  (f : Y → Z) [IsInv f]
  (g : X → Y) [IsInv g]
  : (λ (x : X) => let y := g x; f y)⁻¹
    =
    λ z =>
      let y  := f⁻¹ z
      g⁻¹ y := sorry


@[fun_trans_rule]
theorem invFun.rule_pi
  (f : α → X → Y) [∀ a, IsInv (f a)]
  : (λ (g : α → X) (a : α) => f a (g a))⁻¹
    =
    λ g' a => (f a)⁻¹ (g' a)  := sorry


-- @[fun_trans_rule]
theorem invFun.rule_piComp [Nonempty α]
  (f : α → X → Y) [∀ a, IsInv (f a)]
  (h : α → β) [IsInv h]
  : (λ (g : β → X) (a : α) => f a (g (h a)))⁻¹
    =
    λ g' b => 
      let a := h⁻¹ b
      (f a)⁻¹ (g' a) := sorry

theorem InvFun.rule_prodMap [Nonempty α] [Nonempty β]
  (f : α → α') [IsInv f] 
  (g : β → β') [IsInv g] 
  : (λ ab : α×β => (f ab.1, g ab.2))⁻¹
    =
    λ ab : α'×β' => (f⁻¹ ab.1, g⁻¹ ab.2) := sorry

theorem InvFun.rule_prodMap_rev [Nonempty α] [Nonempty β]
  (f : α → α') [IsInv f] 
  (g : β → β') [IsInv g] 
  : IsInv (λ ab : α×β => (g ab.2, f ab.1)) := sorry
