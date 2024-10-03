import SciLean.Util.SorryProof

namespace Array

def partitionIdxM {m} [Monad m] (as : Array α) (p : Fin as.size → α → m Bool)
  : m (Array α × Array α × Array (Sum Nat Nat)) :=
do
  let mut bs := #[]
  let mut cs := #[]
  let mut ids : Array (Sum Nat Nat) := #[]
  let mut i := 0
  let mut j := 0
  let mut idx := 0
  for a in as do
    if ← p ⟨idx, sorry_proof⟩ a then
      bs := bs.push a
      ids := ids.push (.inl i)
      i := i + 1
    else
      cs := cs.push a
      ids := ids.push (.inr j)
      j := j + 1
    idx := idx + 1
  return (bs, cs, ids)

def splitM {α : Type _} {m : Type _ → Type _} [Monad m] (as : Array α) (p : α → m Bool) : m (Array α × Array α) :=
  as.foldlM (init := (#[], #[])) fun (as, bs) a => do
    pure <| if ← p a then (as.push a, bs) else (as, bs.push a)

/-- Splits array into two based on function p. It also returns indices that can be used to merge two array back together.
-/
def splitIdx (as : Array α) (p : Fin as.size → α → Bool)
  : Array α × Array α × Array (Sum Nat Nat) :=
Id.run do
  as.partitionIdxM p

def mergeSplit (ids : Array (Sum Nat Nat)) (bs cs : Array α) [Inhabited α] : Array α :=
  ids.map λ id =>
    match id with
    | .inl i => bs[i]!
    | .inr j => cs[j]!

def riffle (xs ys : Array α) : Array α := Id.run do
  let mut zs : Array α := .mkEmpty (xs.size + ys.size)
  let m := min xs.size ys.size
  let M := max xs.size ys.size
  for i in [0:m] do
    have : i < xs.size := sorry_proof
    have : i < ys.size := sorry_proof
    zs := zs.push xs[i]
    zs := zs.push ys[i]
  let xys := if xs.size < ys.size then ys else xs
  for i in [m:M] do
    have : i < xys.size := sorry_proof
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
  if _h : 0 < xs.size then
    let n := xs.size - 1
    have : n < xs.size := sorry_proof
    xs[0:n].foldrM (init:=(← map xs[n])) λ x acc => do op (← map x) acc
  else
    pure default

def joinr [Inhabited β] (xs : Array α) (map : α → β) (op : β → β → β) : β := Id.run do
  xs.joinrM map op



/--
Ordering by size then by lexicographical ordering(left to right).
  -/
def lexOrd {α} [Ord α] (as bs : Array α) : Ordering := Id.run do
  match compare as.size bs.size with
  | .lt => return .lt
  | .gt => return .gt
  | .eq =>
    for i in [0:as.size] do
      have : i < as.size := sorry_proof
      have : i < bs.size := sorry_proof
      match compare as[i] bs[i] with
      | .lt => return .lt
      | .gt => return .gt
      | .eq => continue
    return .eq

/--
Ordering by size then by colexicographical ordering(right to left).
  -/
def colexOrd {α} [Ord α] (as bs : Array α) : Ordering := Id.run do
  match compare as.size bs.size with
  | .lt => return .lt
  | .gt => return .gt
  | .eq =>
    for i in [0:as.size] do
      let i := as.size - i - 1
      have : i < as.size := sorry_proof
      have : i < bs.size := sorry_proof
      match compare as[i] bs[i] with
      | .lt => return .lt
      | .gt => return .gt
      | .eq => continue
    return .eq


/-- Return array of all subarrays of the input array. -/
def allSubsets {α} (a : Array α) : Array (Array α) := Id.run do
  let mut as : Array (Array α) := #[]
  let n := a.size
  for i in [0:2^n] do
    let mut ai : Array α := #[]
    for h : j in [0:a.size] do
      if (2^j).toUInt64 &&& i.toUInt64 ≠ 0 then
        ai := ai.push (a[j])

    as := as.push ai
  return as
