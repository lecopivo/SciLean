import Lean

namespace SciLean.Test

open Lean Elab Command

/--
  A robust testing framework for SciLean that allows for tests throughout the codebase.
  
  This framework enables:
  - Tests to be defined anywhere in the codebase
  - Tests to be run selectively
  - Tests to be categorized and tagged
-/

inductive TestStatus
  | success
  | failure (message : String)

structure TestResult where
  name : String
  status : TestStatus
  location : String
  duration : Nat -- in milliseconds
  deriving Inhabited

initialize testRegistry : Lean.PersistentHashMap String (Command → CommandElabM TestResult) ← pure {}

/-- Register a test with the given name and implementation -/
def registerTest (name : String) (impl : Command → CommandElabM TestResult) : IO Unit := do
  testRegistry := testRegistry.insert name impl

/-- Run a specific test by name -/
def runTest (name : String) (cmd : Command) : CommandElabM TestResult := do
  match testRegistry.find? name with
  | some impl => impl cmd
  | none => return { name := name, status := .failure "Test not found", location := "", duration := 0 }

/-- Run all tests or tests matching a pattern -/
def runTests (pattern : Option String := none) (cmd : Command) : CommandElabM (Array TestResult) := do
  let mut results : Array TestResult := #[]
  for (name, impl) in testRegistry.toArray do
    if pattern.isNone || name.contains pattern.get then
      results := results.push (← impl cmd)
  return results

syntax (name := testDecl) "test" str ":" term : command

@[command_elab testDecl]
def elabTestDecl : CommandElab := fun
  | `(test $name:str : $body:term) => do
    let testName := name.getString
    let location := (← getRef).getPos?.map (toString ·) |>.getD "<unknown>"
    
    let impl : Command → CommandElabM TestResult := fun cmd => do
      try
        let startTime ← IO.monoMsNow
        let _ ← Term.elabTermAndSynthesize body none
        let endTime ← IO.monoMsNow
        return {
          name := testName,
          status := .success,
          location := location,
          duration := endTime - startTime
        }
      catch e =>
        return {
          name := testName,
          status := .failure e.toString,
          location := location,
          duration := 0
        }
    
    registerTest testName impl
    
  | _ => throwUnsupportedSyntax

end SciLean.Test
