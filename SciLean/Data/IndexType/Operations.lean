import SciLean.Data.IndexType.Basic
import SciLean.Tactic.RefinedSimp

namespace SciLean

namespace IndexType

namespace Range

variable {ι : Type*} [IndexType ι]

def foldlIdxM {m} [Monad m] (r : Range ι) (op : α → ι → Fin (size r) → m α) (init : α) : m α := do
  let mut a := init
  let mut idx : Nat := 0
  for i in Iterator.start r do
    a ← op a i ⟨idx, sorry_proof⟩
    idx := idx + 1
  return a

def foldlM {m} [Monad m] (r : Range ι) (op : α → ι → m α) (init : α) : m α := do
  let mut a := init
  for i in Iterator.start r do
    a ← op a i
  return a

def foldl (r : Range ι) (op : α → ι → α) (init : α) : α := Id.run do
  r.foldlM op init

def reduceMD {m} [Monad m] (r : Range ι) (f : ι → α) (op : α → α → m α) (default : α) : m α := do
  match first? r with
  | none => return default
  | .some fst => do
    let mut a := (f fst)
    for i in Iterator.val fst r do
      a ← op a (f i)
    return a

def reduceD (r : Range ι) (f : ι → α) (op : α → α → α) (default : α) : α := Id.run do
  r.reduceMD f (fun x y => pure (op x y)) default

abbrev reduce [Inhabited α] (r : Range ι) (f : ι → α) (op : α → α → α) : α :=
  r.reduceD f op default


----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

end Range

variable {ι : Type*} [IndexType ι]

abbrev foldlM {m} [Monad m] (op : α → ι → m α) (init : α) : m α :=
  Range.full.foldlM op init

abbrev foldl (op : α → ι → α) (init : α) : α :=
  Range.full.foldl op init

abbrev reduceMD {m} [Monad m] (f : ι → α) (op : α → α → m α) (default : α) : m α :=
  Range.full.reduceMD f op default

abbrev reduceD (f : ι → α) (op : α → α → α) (default : α) : α :=
  Range.full.reduceD f op default

abbrev reduce [Inhabited α] (f : ι → α) (op : α → α → α) : α :=
  reduceD f op default

def argValMax {I} [IndexType I] [Inhabited I]
    (f : I → X) [LT X] [∀ x x' : X, Decidable (x<x')] : I×X :=
  IndexType.reduceD
    (fun i => (i,f i))
    (fun (i,e) (i',e') => if e < e' then (i',e') else (i,e))
    (default, f default)

def argMax {I} [IndexType I] [Inhabited I]
    (f : I → X) [LT X] [∀ x x' : X, Decidable (x<x')] : I :=
  (IndexType.argValMax f).1

variable {I : Type*} [IndexType I]

open IndexType
@[rsimp guard I .notAppOf ``Fin]
theorem reduce_linearize {I X : Type _} [IndexType I] (init : X) (f : I → X) (op : X → X → X) :
    IndexType.reduceD f op init
    =
    IndexType.reduceD (fun i : Fin (size I) => f (fromFin i)) op init := sorry_proof
