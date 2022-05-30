import Lean

namespace SciLean

open Lean.Meta

initialize differentiation_simp_extension 
  : SimpExtension ← registerSimpAttr `simp_diff "Differentiation "

-- initialize differentiation_core_simp_extension 
--   : SimpExtension ← registerSimpAttr `diff_core "Core Differentiation Rules"

