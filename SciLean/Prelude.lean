import Lean
import SciLean.Mathlib.Data.Enumtype
import SciLean.Notation

--- In this file we define bunch of conventions and conveniences through out the library

-- Export symbols from Mathlib
export Enumtype (sum)

--- !i creates an element of a subtype with an omitted proof
--- much nicer then writing ⟨i, sorry⟩
macro:max "!" noWs t:term : term => `(⟨$t, sorry⟩)

notation "!?" P => (sorry : P)


macro:max "#" noWs t:term : term => `(⟨$t, by decide⟩)


open Lean.Meta

initialize differentiation_simp_extension 
  : SimpExtension ← registerSimpAttr `diff "Differentiation Rules"

initialize differentiation_core_simp_extension 
  : SimpExtension ← registerSimpAttr `diff_core "Core Differentiation Rules"


initialize lambdaPush_simp_extension 
  : SimpExtension ← registerSimpAttr `lambdaPush "Propagate Lambdas Inside"

initialize lambdaPull_simp_extension 
  : SimpExtension ← registerSimpAttr `lambdaPull "Propagate Lambdas Outside"


-- initialize differentiation_simp_extension 
--   : SimpExtension ← registerSimpAttr `my_simp "my own simp attribute"


