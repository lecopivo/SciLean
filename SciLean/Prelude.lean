import SciLean.Mathlib.Data.Enumtype

--- In this file we define bunch of conventions and conveniences through out the library

-- Export symbols from Mathlib
export Enumtype (sum)

--- !i creates an element of a subtype with an omitted proof
--- much nicer then writing ⟨i, sorry⟩
macro:max "!" noWs t:term : term => `(⟨$t, sorry⟩)

notation "!?" P => (sorry : P)


