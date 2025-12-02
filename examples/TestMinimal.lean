/-
Test: After clean rebuild with mathlib
-/

import Mathlib.Data.List.Defs

def main : IO Unit := do
  IO.println "Works after clean rebuild!"
