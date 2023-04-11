import SciLean.Core.InvMap

namespace SciLean

--------------------------------------------------------------------------------

variable {X Y Z : Type} 

@[fun_prop_rule]
theorem IsLin.rule_id 
  : IsInv (λ x : X => x) := sorry

@[fun_prop_rule]
theorem IsInv.rule_comp 
  (f : Y → Z) [IsInv f]
  (g : X → Y) [IsInv g]
  : IsInv (λ x => f (g x)) := sorry

