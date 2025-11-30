import SciLean.Logic.Function.TransitiveClosure
import SciLean.Meta.Notation.FunctionArgument
import SciLean.Analysis.Calculus.NonSmoothDifferential

/-- Test file for new SciLean modules -/

def main : IO Unit := do
  IO.println "Testing new SciLean modules"
  
  -- Test function argument notation
  let result1 := SciLean.Meta.Notation.exampleFunction 5
  IO.println s!"exampleFunction 5 = {result1}"
  
  let result2 := SciLean.Meta.Notation.exampleFunction 5 20
  IO.println s!"exampleFunction 5 20 = {result2}"
  
  IO.println "All tests completed successfully!"

#eval main
