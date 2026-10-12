module

public import Batteries.Data.Array.Merge
public import Batteries.Data.List.Basic

public import SciLean.Lean.Array
public import SciLean.Util.SorryProof
public import Aesop

@[expose] public section


namespace SciLean

/--
  `Array α` that is guaranteed to be sorted based on `[Ord α]` and has no duplicates.

  WARRNING: `Ord α` is assumed to be lawful, currently there is no typeclass for it.
  -/
structure ArraySet (α : Type _) [ord : Ord α] where
  data : Array α
  isSet : data.sortDedup = data
deriving Hashable

namespace ArraySet

  variable {α} [ord : Ord α]

  def size (as : ArraySet α) : Nat := as.data.size

  instance : GetElem (ArraySet α) Nat α (λ as i => i < as.size) where
    getElem as i h := as.data[i]

  def toArray (as : ArraySet α) : Array α := as.data
  def toList (as : ArraySet α) : List α := as.data.toList

  instance : Coe (ArraySet α) (Array α) := ⟨λ as => as.data⟩
  instance [ToString α] : ToString (ArraySet α) := ⟨λ as => toString as.data⟩

  def _root_.Array.toArraySet (as : Array α) : ArraySet α where
    data := as.sortDedup
    isSet := sorry_proof

  def mem (as : ArraySet α) (a : α) [DecidableEq α] : Bool := Id.run do
    for a' in as.toArray do
      if a' = a then
        return true
    return false

  instance [DecidableEq α] : Membership α (ArraySet α) where
    mem as a := as.mem a

  instance [DecidableEq α] (a : α) (as : ArraySet α) : Decidable (a ∈ as) :=
    if h : as.mem a then
      .isTrue (by exact h)
    else
      .isFalse h

  instance : HasSubset (ArraySet α) where
    Subset as bs := (List.Subset as.toList bs.toList)

  -- Inclusion of array sets is inclusion of the underlying lists, which is decidable as soon as
  -- the elements have decidable equality. The previous hand written loop is kept below, it relies
  -- on `Ord α` being lawful which is not assumed anywhere.
  instance instDecidableSubsetArraySet [DecidableEq α] (a b : ArraySet α) : Decidable (a ⊆ b) :=
    inferInstanceAs (Decidable (a.toList ⊆ b.toList))

  -- -- TODO: This needs lawful Ord
  -- instance (a b : ArraySet α) : Decidable (a ⊆ b) := Id.run do
  --   let mut j := 0
  --   for h : i in [0:b.size] do
  --     if _h' : (a.size - j) > (b.size - i) then
  --       return isFalse sorry_proof
  --     if h' : j < a.size then
  --       have _ := h.2
  --       match compare b[i] a[j] with
  --       | .eq =>
  --         j := j + 1
  --         continue
  --       | .lt =>
  --         continue
  --       | .gt =>
  --         return isFalse sorry_proof
  --     else
  --       -- we have exhausted whole as
  --       return isTrue sorry_proof
  --
  --   if j = a.size then
  --     isTrue sorry_proof
  --   else
  --     isFalse sorry_proof

  -- Two array sets are equal exactly when their underlying arrays are, so we can simply decide
  -- the equality of the underlying arrays. The previous hand written loop is kept below as it
  -- could not be given a proof of the positive case.
  instance instDecidableEqArraySet (a b : ArraySet α) [DecidableEq α] : Decidable (a = b) :=
    decidable_of_iff (a.data = b.data) (by cases a; cases b; simp)

  -- instance (a b : ArraySet α) [DecidableEq α] : Decidable (a = b) := Id.run do
  --   if h : a.size = b.size then
  --     for h' : i in [0:a.size] do
  --       have : i < a.size := h'.2.1
  --       have : i < b.size := h ▸ h'.2.1
  --       if a[i] ≠ b[i] then
  --         return isFalse sorry_proof
  --     return isTrue sorry_proof
  --   else
  --     return isFalse sorry_proof

  meta def lexOrd [Ord α] (a b : ArraySet α) : Ordering := a.data.lexOrd b.data

  -- def a := #[1,2,3,4].toArraySet
  -- def b := #[4,3,2].toArraySet

  -- #eval (b ⊆ a)

  -- #exit
