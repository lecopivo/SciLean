import Lean

/-! # SciLean Simp Attributes

Simp attributes for algebraic transformations.

Each attribute has both lemma support (`attr_name`) and simproc support (`attr_name_proc`).
-/

namespace SciLean

open Lean Meta

-- Core simp attribute (most commonly used)
initialize simpCore : SimpExtension ←
  registerSimpAttr `simp_core "Core simp attribute for fundamental simplifications"
initialize simpCoreProc : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `simp_core_proc "Simproc extension for simp_core" none

-- Push/pull attributes for algebraic operations
initialize addPull : SimpExtension ←
  registerSimpAttr `add_pull "Simp attribute for pulling addition out of expressions"
initialize addPush : SimpExtension ←
  registerSimpAttr `add_push "Simp attribute for pushing addition into expressions"

initialize sumPush : SimpExtension ←
  registerSimpAttr `sum_push "Simp attribute for pushing sums into expressions"
initialize sumPull : SimpExtension ←
  registerSimpAttr `sum_pull "Simp attribute for pulling sums out of expressions"

initialize subPull : SimpExtension ←
  registerSimpAttr `sub_pull "Simp attribute for pulling subtraction out of expressions"
initialize subPush : SimpExtension ←
  registerSimpAttr `sub_push "Simp attribute for pushing subtraction into expressions"

initialize negPull : SimpExtension ←
  registerSimpAttr `neg_pull "Simp attribute for pulling negation out of expressions"
initialize negPush : SimpExtension ←
  registerSimpAttr `neg_push "Simp attribute for pushing negation into expressions"

initialize smulPull : SimpExtension ←
  registerSimpAttr `smul_pull "Simp attribute for pulling scalar multiplication out"
initialize smulPush : SimpExtension ←
  registerSimpAttr `smul_push "Simp attribute for pushing scalar multiplication in"

initialize mulPull : SimpExtension ←
  registerSimpAttr `mul_pull "Simp attribute for pulling multiplication out of expressions"
initialize mulPush : SimpExtension ←
  registerSimpAttr `mul_push "Simp attribute for pushing multiplication into expressions"

initialize powPush : SimpExtension ←
  registerSimpAttr `pow_push "Simp attribute for pushing powers into expressions"
initialize powPull : SimpExtension ←
  registerSimpAttr `pow_pull "Simp attribute for pulling powers out of expressions"

initialize expPush : SimpExtension ←
  registerSimpAttr `exp_push "Simp attribute for pushing exponentials into expressions"
initialize expPull : SimpExtension ←
  registerSimpAttr `exp_pull "Simp attribute for pulling exponentials out of expressions"

initialize logPush : SimpExtension ←
  registerSimpAttr `log_push "Simp attribute for pushing logarithms into expressions"
initialize logPull : SimpExtension ←
  registerSimpAttr `log_pull "Simp attribute for pulling logarithms out of expressions"

end SciLean
