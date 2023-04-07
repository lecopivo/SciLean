import Std.Logic

namespace Array

def partitionIdxM {m} [Monad m] (p : α → m Bool) (as : Array α) 
  : m (Array α × Array α × Array (Sum Nat Nat)) := 
do
  let mut bs := #[]
  let mut cs := #[]
  let mut ids : Array (Sum Nat Nat) := #[]
  let mut i := 0
  let mut j := 0
  for a in as do
    if ← p a then
      bs := bs.push a
      ids := ids.push (.inl i)
      i := i + 1
    else
      cs := cs.push a
      ids := ids.push (.inr j)
      j := j + 1
  return (bs, cs, ids)

def partitionIdx (p : α → Bool) (as : Array α) 
  : Array α × Array α × Array (Sum Nat Nat) := 
Id.run do
  as.partitionIdxM p

def merge (ids : Array (Sum Nat Nat)) (bs cs : Array α) [Inhabited α] : Array α :=
  ids.map λ id => 
    match id with
    | .inl i => bs[i]!
    | .inr j => cs[j]!

def riffle (xs ys : Array α) : Array α := Id.run do
  let mut zs : Array α := .mkEmpty (xs.size + ys.size)
  let m := min xs.size ys.size
  let M := max xs.size ys.size
  for i in [0:m] do
    have : i < xs.size := sorry
    have : i < ys.size := sorry
    zs := zs.push xs[i] 
    zs := zs.push ys[i]
  let xys := if xs.size < ys.size then ys else xs
  for i in [m:M] do
    have : i < xys.size := sorry
    zs := zs.push xys[i]
  zs

def joinlM [Monad m] [Inhabited β] (xs : Array α) (map : α → m β) (op : β → β → m β) : m β := do
  if h : 0 < xs.size then
    xs[1:].foldlM (init:=(← map xs[0])) λ acc x => do op acc (← map x)
  else
    pure default

def joinl [Inhabited β] (xs : Array α) (map : α → β) (op : β → β → β) : β := Id.run do
  xs.joinlM map op

def joinrM [Monad m] [Inhabited β] (xs : Array α) (map : α → m β) (op : β → β → m β) : m β := do
  if h : 0 < xs.size then
    let n := xs.size - 1
    have : n < xs.size := sorry
    xs[0:n].foldrM (init:=(← map xs[n])) λ x acc => do op (← map x) acc 
  else
    pure default

def joinr [Inhabited β] (xs : Array α) (map : α → β) (op : β → β → β) : β := Id.run do
  xs.joinrM map op

