import SciLean.Core.InvMap

namespace SciLean

--------------------------------------------------------------------------------

variable {X Y Z : Type} 

@[fun_prop_rule]
theorem IsInv.rule_id 
  : IsInv (λ x : X => x) := sorry

@[fun_prop_rule]
theorem IsInv.rule_comp 
  (f : Y → Z) [IsInv f]
  (g : X → Y) [IsInv g]
  : IsInv (λ x => f (g x)) := sorry

theorem IsInv.rule_prodMap
  (f : α → α') [IsInv f] 
  (g : β → β') [IsInv g] 
  : IsInv (λ ab : α×β => (f ab.1, g ab.2)) := sorry

theorem IsInv.rule_prodMap_rev
  (f : α → α') [IsInv f] 
  (g : β → β') [IsInv g] 
  : IsInv (λ ab : α×β => (g ab.2, f ab.1)) := sorry
