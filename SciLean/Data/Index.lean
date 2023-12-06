import SciLean.Util.SorryProof
import SciLean.Data.EnumType

namespace SciLean

class Index (ι : Type u) extends EnumType ι where
  size : USize
  -- This is used to assert that the number of elements is smaller then `USize.size`
  -- The point is that we want to have an instance `Index (ι×κ)` from `Index ι` and `Index κ` 
  -- without proving `numOf ι * numOf κ < USize.size-1`. 
  -- Thus if `numOf ι * numOf κ ≥ USize.size` we set `isValid` to `false` and 
  -- give up any formal guarantees and we also panic.
  isValid : Bool

  fromIdx : Idx size → ι
  toIdx : ι → Idx size
  
  fromIdx_toIdx : isValid = true → fromIdx ∘ toIdx = id
  toIdx_fromIdx : isValid = true → toIdx ∘ fromIdx = id


export Index (toIdx fromIdx)

namespace Index

-- @[macro_inline]
instance : Index Empty where
  size := 0
  isValid := true

  fromIdx := λ a => absurd (a := a.1<0) a.2 (by intro h; cases h)
  toIdx := λ a => (by induction a; done)

  fromIdx_toIdx := sorry_proof
  toIdx_fromIdx := sorry_proof

-- @[macro_inline]
instance : Index Unit where
  size := 1
  isValid := true

  fromIdx := λ _ => ()
  toIdx := λ _ => ⟨0, sorry_proof⟩

  fromIdx_toIdx := sorry_proof
  toIdx_fromIdx := sorry_proof

-- @[macro_inline]
instance : Index (Idx n) where
  size := n
  isValid := true

  fromIdx := id
  toIdx := id
  
  fromIdx_toIdx := by simp
  toIdx_fromIdx := by simp

-- @[macro_inline]
instance : Index (Idx' a b) where
  size := let n := b - a; if 0 < n then n.toUSize else 0
  isValid := true

  fromIdx i := ⟨i.1.toInt64 + a, sorry_proof⟩
  toIdx i := ⟨(i.1 - a).1, sorry_proof⟩
  
  fromIdx_toIdx := sorry_proof
  toIdx_fromIdx := sorry_proof


-- Row major ordering, this respects `<` defined on `ι × κ`
@[macro_inline]
instance [Index ι] [Index κ] : Index (ι×κ) where  
  size := (min ((size ι).toNat * (size κ).toNat) (USize.size -1)).toUSize
  isValid := 
    if (size ι).toNat * (size κ).toNat < USize.size - 1  then 
      Index.isValid ι && Index.isValid κ
    else 
      -- this is using the fact that `(default : Bool) = false`
      panic! s!"Attempting to create `Index (ι×κ)` for too big `ι` and `κ`.\n  `size ι = {size ι}`\n  `size κ = {size κ}`" 
  
  -- This has still some issues when overflow happends
  -- numOf := numOf ι * numOf κ
  fromIdx := λ i => (fromIdx ⟨i.1 / size κ, sorry_proof⟩, fromIdx ⟨i.1 % size κ, sorry_proof⟩)
  toIdx := λ (i,j) => ⟨(toIdx i).1 * size κ + (toIdx j).1, sorry_proof⟩
  
  fromIdx_toIdx := λ _ => sorry_proof
  toIdx_fromIdx := λ _ => sorry_proof


-- Row major ordering, this respects `<` defined on `ι × κ`
-- @[macro_inline]
instance [Index ι] [Index κ] : Index (ι×ₗκ) where  
  size := (min ((size ι).toNat * (size κ).toNat) (USize.size -1)).toUSize
  isValid := 
    if (size ι).toNat * (size κ).toNat < USize.size - 1  then 
      Index.isValid ι && Index.isValid κ
    else 
      -- this is using the fact that `(default : Bool) = false`
      panic! s!"Attempting to create `Index (ι×ₗκ)` for too big `ι` and `κ`.\n  `size ι = {size ι}`\n  `size κ = {size κ}`" 
  
  -- This has still some issues when overflow happends
  -- numOf := numOf ι * numOf κ
  fromIdx := λ i => (fromIdx ⟨i.1 % size ι, sorry_proof⟩, fromIdx ⟨i.1 / size ι, sorry_proof⟩)
  toIdx := λ (i,j) => ⟨(toIdx j).1 * size ι + (toIdx i).1, sorry_proof⟩
  
  fromIdx_toIdx := λ _ => sorry_proof
  toIdx_fromIdx := λ _ => sorry_proof

  instance [Index ι] [Index κ] : Index (ι ⊕ κ) where
    size := (min ((size ι).toNat + (size κ).toNat) (USize.size -1)).toUSize
    isValid := 
      if (size ι).toNat + (size κ).toNat < USize.size - 1  then 
        Index.isValid ι && Index.isValid κ
      else 
        -- this is using the fact that `(default : Bool) = false`
        panic! s!"Attempting to create `Index (ι⊕κ)` for too big `ι` and `κ`.\n  `size ι = {size ι}`\n  `size κ = {size κ}`" 
 
    fromIdx := λ i => 
      if i.1 < size ι
      then Sum.inl $ fromIdx ⟨i.1, sorry_proof⟩ 
      else Sum.inr $ fromIdx ⟨i.1 - size ι, sorry_proof⟩
    toIdx := λ ij => 
      match ij with
      | Sum.inl i => ⟨(toIdx i).1, sorry_proof⟩
      | Sum.inr j => ⟨(toIdx j).1 + size ι, sorry_proof⟩

    fromIdx_toIdx := λ _ => sorry_proof
    toIdx_fromIdx := λ _ => sorry_proof


  -- TODO: revive parallel sum/join . I ditched ranges as the required decidable order, which is too much to ask sometimes

  -- /--
  -- Joins all values `f i` from left to right with operation `op` 
  
  -- The operation `op` is assumed to be associative and `unit` is the left unit of this operation i.e. `∀ a, op unit a = a`

  -- WARRNING: This does not work correctly for small `m`. FIX THIS!!!!
  -- -/
  -- def parallelJoin {α ι} [Index ι] (m : USize) (f : ι → α) (op : α → α → α) (unit : α) : α := Id.run do
  --   dbg_trace "!!!FIX ME!!! Index.parallelJoin is not implemented correctly!"
  --   let n := size ι
  --   if n == 0 then
  --     return unit
  --   let mut tasks : Array (Task α) := Array.mkEmpty m.toNat
  --   let m := max 1 (min m n) -- cap min/max of `m` 
  --   let stride : USize := (n+m-1)/m
  --   let mut start : Idx n := ⟨0,sorry_proof⟩
  --   let mut stop  : Idx n := ⟨stride-1, sorry_proof⟩
  --   for i in fullRange (Idx m) do
  --     let r : EnumType.Range ι := some (fromIdx start, fromIdx stop)
  --     let partialJoin : Unit → α := λ _ => Id.run do
  --       let mut a := unit
  --       for i in r do
  --         a := op a (f i)
  --       a
  --     tasks := tasks.push (Task.spawn partialJoin)
  --     start := ⟨min (start.1 + stride) (n-1), sorry_proof⟩
  --     stop  := ⟨min (stop.1 + stride) (n-1), sorry_proof⟩

  --   let mut a := unit
  --   for t in tasks do
  --     a := op a t.get
  --   a


  -- open EnumType in
  -- /--
  -- Split the sum `∑ i, f i` into `m` chuncks and compute them in parallel
  -- -/
  -- def parallelSum {X ι} [Zero X] [Add X] [Index ι] (m : USize) (f : ι → X) : X :=
  --   parallelJoin m f (λ x y => x + y) 0
