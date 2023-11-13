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


/-- Reverse derivative of `Function.foldl` w.r.t. `f` and `init`. It is implemented using `Array`.

  TODO: 
    1. needs beter implementation but that requires refining EnumType and Index
    2. add a version with DataArray
-/
def Function.foldl.revDeriv_arrayImpl {α β : Type} [Add α] [Add β] [ToString β] 
  (f : ι → α) (op : β → α → β) (dop : β → α → β → β×α) (init : β) : β × (β → Array α×β) := Id.run do
  let n := (Index.size ι).toNat
  let mut bs : Array β := .mkEmpty n
  let mut b := init
  for i in fullRange ι do
    bs := bs.push b
    b := op b (f i)
  dbg_trace bs
  (b, 
   fun db => Id.run do
     let mut das : Array α := .mkEmpty n
     let mut db : β := db
     for i in [0:n] do
       let j : ι := fromIdx ⟨n.toUSize-i.toUSize-1, sorry_proof⟩
       let aj := f j
       let bj := bs[n-i-1]'sorry_proof
       let (db',da) := dop bj aj db
       das := das.push da
       db := db'
     das := das.reverse
     (das, db))



#eval Function.foldl.revDeriv_arrayImpl (β:=USize) (fun i : Idx 5 => i.1) (fun s x => s + x*x*x) (fun s x d => (d, 3*x*x*d)) 0 |>.snd 1

#eval Function.foldl.revDeriv_arrayImpl (β:=Float) (fun i : Idx 3 => (i.1+5).toNat.toFloat) (fun s x => s/x) (fun s x d => (d/x, -s*d/(x*x))) 1 |>.snd 1

