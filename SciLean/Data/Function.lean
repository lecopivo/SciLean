import Mathlib.Logic.Function.Basic
import SciLean.Data.Index

def Function.Inverse (g : β → α) (f : α → β) :=
  Function.LeftInverse g f ∧ Function.RightInverse g f

open SciLean

variable {α β}
  {ι} [EnumType ι]

def Function.foldlM {m} [Monad m] (f : ι → α) (op : β → α → m β) (init : β) : m β := do
  let mut b := init
  for i in fullRange ι do
    b ← op b (f i)
  return b

def Function.foldl (f : ι → α) (op : β → α → β) (init : β) : β :=
  Id.run <| Function.foldlM f (fun x y => pure (op x y)) init

variable [Index ι]

/--
  TODO: needs beter implementation but that requires refining EnumType and Index
  -/
def Function.reduceMD {m} [Monad m] (f : ι → α) (op : α → α → m α) (default : α) : m α := do
  let n := Index.size ι
  if n = 0 then
    return default
  let mut a := f (fromIdx ⟨0,sorry_proof⟩)
  for i in [1:n.toNat] do
    a ← op a (f (fromIdx ⟨i.toUSize,sorry_proof⟩))
  return a

def Function.reduceD (f : ι → α) (op : α → α → α) (default : α) : α :=
  Id.run <| Function.reduceMD f (fun x y => pure (f:=Id) op x y) default

abbrev Function.reduce [Inhabited α] (f : ι → α) (op : α → α → α) : α := 
  f.reduceD op default
