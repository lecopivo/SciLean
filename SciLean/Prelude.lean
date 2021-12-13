import SciLean.Mathlib.Data.Iterable

--- In this file we define bunch of conventions and conveniences through out the library

-- Export symbols from Mathlib
export Iterable (sum)

--- !i creates an element of a subtype with an omitted proof
--- much nicer then writing ⟨i, sorry⟩
macro:max "!" noWs t:term : term => `(⟨$t, sorry⟩)



