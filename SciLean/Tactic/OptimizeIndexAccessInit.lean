import Lean

/-! # Optimize Index Access Init

Initialization for index access optimization simp attributes.
Provides both `optimize_index_access` for lemmas and `optimize_index_access_proc` for simprocs.
-/

namespace SciLean

open Lean Meta

initialize optimizeIndexAccess : SimpExtension ←
  registerSimpAttr `optimize_index_access "Simp attribute for optimizing index access patterns"
initialize optimizeIndexAccessProc : Simp.SimprocExtension ←
  Simp.registerSimprocAttr `optimize_index_access_proc "Simproc extension for optimize_index_access" none

end SciLean
