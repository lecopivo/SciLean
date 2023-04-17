import SciLean.Data.Idx

namespace SciLean

class Index (ι : Type u) extends Enumtype ι where
  size := (min numOf (USize.size - 1)).toUSize
  fromIdx : Idx size → ι
  toIdx : ι → Idx size

  -- This is used to assert that the number of elements is smaller then `USize.size`
  -- The point is that we want to have an instance `Index (ι×κ)` from `Index ι` and `Index κ` 
  -- without proving `numOf ι * numOf κ < USize.size-1`. 
  -- Thus if `numOf ι * numOf κ ≥ USize.size` we set `isValid` to `false` and 
  -- give up any formal guarantees and we also panic.
  isValid := if size.toNat = numOf then true else false
  
  fromIdx_toIdx : isValid = true → fromIdx ∘ toIdx = id
  toIdx_fromIdx : isValid = true → toIdx ∘ fromIdx = id

export Index (toIdx fromIdx)

namespace Index

instance : Index (Idx n) where

  fromIdx := id
  toIdx := id
  
  fromIdx_toIdx := by simp
  toIdx_fromIdx := by simp

-- Row major ordering, this respects `<` defined on `ι × κ`
instance [Index ι] [Index κ] : Index (ι×κ) where
  
  -- This has still some issues when overflow happends
  -- numOf := numOf ι * numOf κ
  fromIdx := λ i => (fromIdx ⟨i.1 / size κ, sorry⟩, fromIdx ⟨i.1 % numOf κ, sorry⟩)
  toIdx := λ (i,j) => ⟨(toIdx i).1 * size κ + (toIdx j).1, sorry⟩

  isValid := 
    if numOf ι * numOf κ < USize.size - 1  then 
      Index.isValid ι && Index.isValid κ
    else 
      -- this is using the fact that `(default : Bool) = false`
      panic! s!"Attempting to create `Index (ι×κ)` for too big `ι` and `κ`.\n  `numOf ι = {numOf ι}`\n  `numOf κ = {numOf κ}`" 
  
  fromIdx_toIdx := λ _ => sorry
  toIdx_fromIdx := λ _ => sorry


#eval numOf (Idx (((0 : USize) - 1)/2 +1) × Idx (2))

variable (ι) [Index ι] (i : ι)

#check toIdx i
