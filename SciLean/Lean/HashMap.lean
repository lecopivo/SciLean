import Lean
open Lean

namespace Lean

unsafe def HashMap.modify {α β} [BEq α] [Hashable α] (m : Std.HashMap α β) (key : α) (f : β → β) : Std.HashMap α β :=
  if let .some val := m[key]? then
    let m := m.insert key (unsafeCast ()) -- ensures linearity?
    m.insert key (f val)
  else
    m

unsafe def PersistentHashMap.modify {α β} [BEq α] [Hashable α] (m : PersistentHashMap α β) (key : α) (f : β → β) : PersistentHashMap α β :=
  if let .some val := m.find? key then
    let m := m.insert key (unsafeCast ()) -- ensures linearity?
    m.insert key (f val)
  else
    m

unsafe def PersistentHashMap.modifyDUsafe {α β} [BEq α] [Hashable α] (m : PersistentHashMap α β) (key : α) (b : β) (f : β → β)  : PersistentHashMap α β :=
  if let .some val := m.find? key then
    let m := m.insert key (unsafeCast ()) -- ensures linearity?
    m.insert key (f val)
  else
    m.insert key b

@[implemented_by PersistentHashMap.modifyDUsafe]
def PersistentHashMap.modifyD {α β} [BEq α] [Hashable α] (m : PersistentHashMap α β) (key : α) (b : β) (f : β → β)  : PersistentHashMap α β :=
  if let .some val := m.find? key then
    m.insert key (f val)
  else
    m.insert key b
