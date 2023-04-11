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
