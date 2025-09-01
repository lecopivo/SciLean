import Lean

open Lean

namespace SciLean

/-- Gives a name based on `baseName` that's not already in the list. -/
partial def mkUnusedName (names : List Name) (baseName : Name) : Name :=
  if not (names.contains baseName) then
    baseName
  else
    let rec loop (i : Nat := 0) : Name :=
      let w := Name.appendIndexAfter baseName i
      if names.contains w then
        loop (i + 1)
      else
        w
    loop 1
