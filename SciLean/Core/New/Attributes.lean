import Lean

namespace SciLean


-- TODO: Custom simp attributes do not allow for pre specification
-- auto-differentiation really needs to have its theorems marked with pre
-- so right now we use `simp ↓` and use the whole simp set for autodiff
open Lean.Meta in
initialize differentiation_simp_extension 
  : SimpExtension ← registerSimpAttr `autodiff "Attribute to mark theorems involved in symbolic and automatic differentiation."
