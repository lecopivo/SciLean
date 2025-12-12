import Lean
open Lean Elab

def Icc.unexpand : Syntax → MacroM Syntax
  | `(Icc $a $b) => `(Set.Icc $a $b)
  | `(Icc ($a + $c) ($b - $d)) => `(Set.Icc ($a + $c) ($b - $d))
  | _ => Macro.throwError "Invalid Icc syntax"

where
  isValidBounds (a b : Syntax) : MacroM Bool := do
    -- Implement bounds checking logic here
    pure true  -- Placeholder

-- Test the unexpander
#eval do
  let test1 ← Icc.unexpand (← `(Icc 0 1))
  let test2 ← Icc.unexpand (← `(Icc (x + 2) (y - 3)))
  let test3 ← Icc.unexpand (← `(Icc a b))
  IO.println s!"Test 1: {test1}"
  IO.println s!"Test 2: {test2}"
  IO.println s!"Test 3: {test3}"
