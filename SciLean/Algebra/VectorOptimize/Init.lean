import Lean

/-! # Vector Optimize Init

Initialization for vector optimization simp attributes.
Provides both `vector_optimize` for lemmas and `vector_optimize_proc` for simprocs.
-/

namespace SciLean

open Lean Meta

initialize vectorOptimize : SimpExtension ←
  registerSimpAttr `vector_optimize "Simp attribute for vector optimizations"
initialize vectorOptimizeProc : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `vector_optimize_proc "Simproc extension for vector_optimize" none

end SciLean
