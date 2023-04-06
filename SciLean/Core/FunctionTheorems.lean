import Lean.Data.PersistentHashMap

import SciLean.Data.ArraySet

open Lean

namespace SciLean

structure FunctionTheorem where
  normalTheorem : Name
  compTheorem : Name

initialize functionTheoremsMapRef : IO.Ref (PersistentHashMap (Name × Name) (PersistentHashMap (ArraySet Nat) FunctionTheorem)) ← IO.mkRef {}


unsafe def _root_.Lean.HashMap.modify {α β} [BEq α] [Hashable α] (m : HashMap α β) (key : α) (f : β → β) : HashMap α β :=
  if let .some val := m.find? key then
    let m := m.insert key (unsafeCast ()) -- ensures linearity?
    m.insert key (f val)
  else
    m

unsafe def _root_.Lean.PersistentHashMap.modify {α β} [BEq α] [Hashable α] (m : PersistentHashMap α β) (key : α) (f : β → β) : PersistentHashMap α β :=
  if let .some val := m.find? key then
    let m := m.insert key (unsafeCast ()) -- ensures linearity?
    m.insert key (f val)
  else
    m

unsafe def _root_.Lean.PersistentHashMap.modifyDUsafe {α β} [BEq α] [Hashable α] (m : PersistentHashMap α β) (key : α) (b : β) (f : β → β)  : PersistentHashMap α β :=
  if let .some val := m.find? key then
    let m := m.insert key (unsafeCast ()) -- ensures linearity?
    m.insert key (f val)
  else
    m.insert key b

@[implemented_by _root_.Lean.PersistentHashMap.modifyDUsafe]
def _root_.Lean.PersistentHashMap.modifyD {α β} [BEq α] [Hashable α] (m : PersistentHashMap α β) (key : α) (b : β) (f : β → β)  : PersistentHashMap α β :=
  if let .some val := m.find? key then
    m.insert key (f val)
  else
    m.insert key b

def addFunctionTheorem (constName opName : Name) (ids : ArraySet Nat) (thrm : FunctionTheorem) : IO Unit := do
  functionTheoremsMapRef.modify λ thrmMap =>
    thrmMap.modifyD (constName,opName) (PersistentHashMap.empty.insert ids thrm)
      (λ argMap => argMap.insert ids thrm)


def printFunctionTheorems : IO Unit := do
  let m ← functionTheoremsMapRef.get
  m.forM λ (const, op) argMap => do
      IO.println s!"{const} {op}"
      argMap.forM λ ids thrm => 
        IO.println s!"  {ids.data} {thrm.1}"
