module

public import SciLean.Util.SorryProof

public meta import SciLean.Util.SorryProof

@[expose] public meta section


namespace Array

def partitionIdxM {m} [Monad m] (as : Array α) (p : Fin as.size → α → m Bool)
  : m (Array α × Array α × Array (Sum Nat Nat)) :=
do
  let mut bs := #[]
  let mut cs := #[]
  let mut ids : Array (Sum Nat Nat) := #[]
  let mut i := 0
  let mut j := 0
  for h : idx in [0:as.size] do
    let a := as[idx]'h.2.1
    if ← p ⟨idx, h.2.1⟩ a then
      bs := bs.push a
      ids := ids.push (.inl i)
      i := i + 1
    else
      cs := cs.push a
      ids := ids.push (.inr j)
      j := j + 1
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
  for h : i in [0:m] do
    have : i < xs.size := Nat.lt_of_lt_of_le h.2.1 (Nat.min_le_left _ _)
    have : i < ys.size := Nat.lt_of_lt_of_le h.2.1 (Nat.min_le_right _ _)
    zs := zs.push xs[i]
    zs := zs.push ys[i]
  let xys := if xs.size < ys.size then ys else xs
  for h : i in [m:M] do
    have : i < xys.size := by
      have := h.2.1
      simp only [xys, M] at *
      split <;> omega
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
    have : n < xs.size := by omega
    xs[0:n].foldrM (init:=(← map xs[n])) λ x acc => do op (← map x) acc
  else
    pure default

def joinr [Inhabited β] (xs : Array α) (map : α → β) (op : β → β → β) : β := Id.run do
  xs.joinrM map op



/--
Ordering by size then by lexicographical ordering(left to right).
  -/
def lexOrd {α} [Ord α] (as bs : Array α) : Ordering := Id.run do
  match hs : compare as.size bs.size with
  | .lt => return .lt
  | .gt => return .gt
  | .eq =>
    have hsize : as.size = bs.size := Nat.compare_eq_eq.mp hs
    for h : i in [0:as.size] do
      have : i < as.size := h.2.1
      have : i < bs.size := hsize ▸ h.2.1
      match compare as[i] bs[i] with
      | .lt => return .lt
      | .gt => return .gt
      | .eq => continue
    return .eq

/--
Ordering by size then by colexicographical ordering(right to left).
  -/
def colexOrd {α} [Ord α] (as bs : Array α) : Ordering := Id.run do
  match hs : compare as.size bs.size with
  | .lt => return .lt
  | .gt => return .gt
  | .eq =>
    have hsize : as.size = bs.size := Nat.compare_eq_eq.mp hs
    for h : i in [0:as.size] do
      have hi : as.size - i - 1 < as.size := by
        have hi0 : i < as.size := h.2.1
        omega
      let i := as.size - i - 1
      have hi' : i < as.size := hi
      have : i < bs.size := hsize ▸ hi'
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
