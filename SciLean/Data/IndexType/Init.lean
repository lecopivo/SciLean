import Mathlib.Data.Int.Interval

import SciLean.Meta.SimpAttr

namespace SciLean

class Size {α : Sort u} (a : α) where
  size : Nat

export Size (size)

namespace Size

instance (a : List α) : Size a where
  size := a.length

@[simp, simp_core]
theorem size_list {α} (a : List α) : size a = a.length := by rfl

instance (a : Array α) : Size a where
  size := a.size

@[simp, simp_core]
theorem size_array {α} (a : Array α) : size a = a.size := by rfl

instance : Size Empty where
  size := 0

@[simp, simp_core]
theorem size_empty : size Empty = 0 := by rfl

instance : Size Unit where
  size := 1

@[simp, simp_core]
theorem size_unit : size Unit = 1 := by rfl

instance : Size Bool where
  size := 2

@[simp, simp_core]
theorem size_bool : size Bool = 2 := by rfl

instance : Size (Fin n) where
  size := n

@[simp, simp_core]
theorem size_fin (n : Nat) : size (Fin n) = n := by rfl

instance {α β} [Size α] [Size β] : Size (α × β) where
  size := size α * size β

@[simp, simp_core]
theorem size_prod {ι κ} [Size ι] [Size κ] : size (ι × κ) = size ι * size κ := by rfl

instance {α β} [Size α] [Size β] : Size ((_ : α) × β) where
  size := size α * size β

@[simp, simp_core]
theorem size_sigma {ι κ} [Size ι] [Size κ] : size ((_:ι) × κ) = size ι * size κ := by rfl

instance {α β} [Size α] [Size β] : Size (α ⊕ β) where
  size := size α + size β

@[simp, simp_core]
theorem size_sum {ι κ} [Size ι] [Size κ] : size (ι ⊕ κ) = size ι + size κ := by rfl

open Set in
instance (a b : Int) : Size (Icc a b) where
  size := (b - a + 1).toNat

open Set in
@[simp, simp_core]
theorem size_Icc (a b : Int) : size (Icc a b) = (b - a + 1).toNat := by rfl

end Size

-- TODO: remove `Size` and replace it with this
class Size' {X : Sort*} (x : X) (n : outParam Nat)

namespace Size'

instance : Size' Empty 0 where
instance : Size' Unit 1 where
instance : Size' Bool 2 where
instance : Size' (Fin n) n where
instance [Size' α m] [Size' β n] : Size' (α×β) (m*n) where
instance [Size' α m] [Size' β n] : Size' (α⊕β) (m+n) where

end Size'
------------------

class FirstLast {α : Sort u} (a : α) (β : outParam (Type v)) where
  /-- The first and the last element of a value or a type

  This function can be called on values
  ```
  firstLast? [1,2,3,4] = .some (1,4)
  ```
  and on types
  ```
  firstLast? (Fin n) = .some (⟨0,⋯⟩, ⟨n-1,⋯⟩)
  ```
  -/
  firstLast? : Option (β×β)

export FirstLast (firstLast?)

/-- The first element of of a value or a type.

This function can be called on values
```
first? [1,2,3,4] = .some 0
```
and on types
```
first? (Fin n) = .some ⟨0,⋯⟩
```
-/
def first? {α : Sort u} (a : α) [FirstLast a β] : Option β :=
  match FirstLast.firstLast? a with
  | .some (a,_) => .some a
  | .none => .none


/-- The last element of of a value or a type.

This function can be called on values
```
last? [1,2,3,4] = .some 4
```
and on types
```
last? (Fin n) = .some ⟨n-1,⋯⟩
```
-/
def last? {α : Sort u} (a : α) [FirstLast a β] : Option β :=
  match FirstLast.firstLast? a with
  | .some (_,b) => .some b
  | .none => .none



----------------------------------------------------------------------------------------------------

instance {α} (a : List α) : FirstLast a α where
  firstLast? :=
    match a with
    | [] => .none
    | [a] => .some (a,a)
    | a :: a' :: as => .some (a, (a'::as)[as.length])

@[simp, simp_core]
theorem firstLast_list_empty {α} : firstLast? ([] : List α) = none := by rfl

@[simp, simp_core]
theorem firstLast_list_singleton {α} (a : α) : firstLast? [a] = some (a,a) := by rfl

@[simp, simp_core]
theorem firstLast_list {α} (a a' : α) (as : List α) : firstLast? (a::a'::as) = some (a,(a'::as)[as.length]) := by rfl


instance {α} (a : Array α) : FirstLast a α where
  firstLast? :=
    if h : a.size ≠ 0 then
      .some (a[0], a[a.size-1])
    else
      .none

@[simp, simp_core]
theorem firstLast_array {α} : firstLast? (Array.empty : Array α) = none := by rfl

instance : FirstLast Empty Empty where
  firstLast? := .none

@[simp, simp_core]
theorem firstLast_empty : firstLast? Empty = none := by rfl

instance : FirstLast Unit Unit where
  firstLast? := .some ((),())

@[simp, simp_core]
theorem firstLast_unit : firstLast? Unit = some ((),()) := by rfl

instance : FirstLast Bool Bool where
  firstLast? := .some (false,true)

@[simp, simp_core]
theorem firstLast_bool : firstLast? Bool = some (false,true) := by rfl

instance {n} : FirstLast (Fin n) (Fin n) where
  firstLast? :=
    if h : n ≠ 0 then
      .some (⟨0, by omega⟩, ⟨n-1,by omega⟩)
    else
      .none

@[simp, simp_core]
theorem firstLast_fin (n : Nat) (hn : n≠0) :
    firstLast? (Fin n) = some (⟨0,by omega⟩,⟨n-1,by omega⟩) := by simp[firstLast?,hn]

instance {α β} [FirstLast α α] [FirstLast β β] : FirstLast (α × β) (α × β) where
  firstLast? :=
    match FirstLast.firstLast? α, FirstLast.firstLast? β with
    | .some (a,a'), .some (b,b') => .some ((a,b),(a',b'))
    | _, .none => .none
    | .none, _ => .none


instance {α β} [FirstLast α α] [FirstLast β β] : FirstLast (α ⊕ β) (α ⊕ β) where
  firstLast? :=
    match FirstLast.firstLast? α, FirstLast.firstLast? β with
    | .some (a,_), .some (_,b') => .some (.inl a, .inr b')
    | .some (a,a'), .none => .some (.inl a, .inl a')
    | .none, .some (b,b') => .some (.inr b, .inr b')
    | .none, .none => .none
