import Lean.Data.PersistentHashMap

import SciLean.Data.ArraySet
import SciLean.Lean.HashMap

open Lean

namespace SciLean

structure FunctionTheorem where
  normalTheorem : Name
  compTheorem : Name

initialize functionPropertyMapRef : IO.Ref (PersistentHashMap (Name × Name) (PersistentHashMap (ArraySet Nat) FunctionTheorem)) ← IO.mkRef {}

def addFunctionProperty (constName opName : Name) (ids : ArraySet Nat) (thrm : FunctionTheorem) : IO Unit := do
  functionPropertyMapRef.modify λ thrmMap =>
    thrmMap.modifyD (constName,opName) (PersistentHashMap.empty.insert ids thrm)
      (λ argMap => argMap.insert ids thrm)


def printFunctionProperties : IO Unit := do
  let m ← functionPropertyMapRef.get
  m.forM λ (const, op) argMap => do
      IO.println s!"{const} {op}"
      argMap.forM λ ids thrm => 
        IO.println s!"  {ids.data} {thrm.1}"
