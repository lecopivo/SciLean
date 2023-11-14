import Mathlib.Logic.Function.Basic
import SciLean.Data.Index

def Function.Inverse (g : β → α) (f : α → β) :=
  Function.LeftInverse g f ∧ Function.RightInverse g f


open SciLean

variable {α β}
  {ι} [EnumType ι]

def Function.foldl (f : ι → α) (op : β → α → β) (init : β) : β := Id.run do
  let mut b := init
  for i in fullRange ι do
    b := op b (f i)
  return b


variable [Index ι]

/-- 
  TODO: needs beter implementation but that requires refining EnumType and Index
  -/
def Function.joinlD (f : ι → α) (op : α → α → α) (default : α) : α := Id.run do
  let n := Index.size ι
  if n = 0 then
    return default
  let mut a := f (fromIdx ⟨0,sorry_proof⟩)
  for i in [1:n.toNat] do
    a := op a (f (fromIdx ⟨i.toUSize,sorry_proof⟩))
  return a




