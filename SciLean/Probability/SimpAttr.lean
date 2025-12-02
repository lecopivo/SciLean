import Lean

/-! # Probability Simp Attributes

Simp attributes for probability-related transformations.
Each provides both lemma support (`attr`) and simproc support (`attr_proc`).
-/

namespace SciLean.Probability

open Lean Meta

initialize randSimp : SimpExtension ←
  registerSimpAttr `rand_simp "Simp attribute for probability simplifications"
initialize randSimpProc : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `rand_simp_proc "Simproc extension for rand_simp" none

initialize randAD : SimpExtension ←
  registerSimpAttr `rand_AD "Simp attribute for probability automatic differentiation"
initialize randADProc : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `rand_AD_proc "Simproc extension for rand_AD" none

initialize randPushE : SimpExtension ←
  registerSimpAttr `rand_push_E "Simp attribute for pushing expectations"
initialize randPushEProc : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `rand_push_E_proc "Simproc extension for rand_push_E" none

initialize randPullE : SimpExtension ←
  registerSimpAttr `rand_pull_E "Simp attribute for pulling expectations"
initialize randPullEProc : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `rand_pull_E_proc "Simproc extension for rand_pull_E" none

end SciLean.Probability
