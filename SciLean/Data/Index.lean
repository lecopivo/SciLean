import SciLean.Data.Idx

namespace SciLean

class Index (ι : Type u) extends Enumtype ι where
  size := (min numOf (USize.size - 1)).toUSize
  -- This is used to assert that the number of elements is smaller then `USize.size`
  -- The point is that we want to have an instance `Index (ι×κ)` from `Index ι` and `Index κ` 
  -- without proving `numOf ι * numOf κ < USize.size-1`. 
  -- Thus if `numOf ι * numOf κ ≥ USize.size` we set `isValid` to `false` and 
  -- give up any formal guarantees and we also panic.
  isValid := if size.toNat = numOf then true else false

  fromIdx : Idx size → ι
  toIdx : ι → Idx size
  advance : USize → ι → ι 
  
  fromIdx_toIdx : isValid = true → fromIdx ∘ toIdx = id
  toIdx_fromIdx : isValid = true → toIdx ∘ fromIdx = id

export Index (toIdx fromIdx)

namespace Index

instance : Index Empty where
  fromIdx := λ a => absurd (a := a.1<0) a.2 (by intro h; cases h)
  toIdx := λ a => (by induction a; done)
  advance := λ s a => a

  fromIdx_toIdx := sorry
  toIdx_fromIdx := sorry


instance : Index Unit where
  fromIdx := λ a => ()
  toIdx := λ a => ⟨0, sorry⟩
  advance := λ s a => a

  fromIdx_toIdx := sorry
  toIdx_fromIdx := sorry


instance : Index (Idx n) where
  fromIdx := id
  toIdx := id
  advance := λ s a => a + s
  
  fromIdx_toIdx := by simp
  toIdx_fromIdx := by simp


-- Row major ordering, this respects `<` defined on `ι × κ`
instance [Index ι] [Index κ] : Index (ι×κ) where  
  isValid := 
    if numOf ι * numOf κ < USize.size - 1  then 
      Index.isValid ι && Index.isValid κ
    else 
      -- this is using the fact that `(default : Bool) = false`
      panic! s!"Attempting to create `Index (ι×κ)` for too big `ι` and `κ`.\n  `numOf ι = {numOf ι}`\n  `numOf κ = {numOf κ}`" 
  
  -- This has still some issues when overflow happends
  -- numOf := numOf ι * numOf κ
  fromIdx := λ i => (fromIdx ⟨i.1 / size κ, sorry⟩, fromIdx ⟨i.1 % size κ, sorry⟩)
  toIdx := λ (i,j) => ⟨(toIdx i).1 * size κ + (toIdx j).1, sorry⟩
  advance := λ s (i,j) => (advance (((toIdx j).1 + s) / size κ) i, advance s j)
  
  fromIdx_toIdx := λ _ => sorry
  toIdx_fromIdx := λ _ => sorry


-- Row major ordering, this respects `<` defined on `ι × κ`
instance [Index ι] [Index κ] : Index (ι×ₗκ) where  
  isValid := 
    if numOf ι * numOf κ < USize.size - 1  then 
      Index.isValid ι && Index.isValid κ
    else 
      -- this is using the fact that `(default : Bool) = false`
      panic! s!"Attempting to create `Index (ι×ₗκ)` for too big `ι` and `κ`.\n  `numOf ι = {numOf ι}`\n  `numOf κ = {numOf κ}`" 
  
  -- This has still some issues when overflow happends
  -- numOf := numOf ι * numOf κ
  fromIdx := λ i => (fromIdx ⟨i.1 % size ι, sorry⟩, fromIdx ⟨i.1 / size ι, sorry⟩)
  toIdx := λ (i,j) => ⟨(toIdx j).1 * size ι + (toIdx i).1, sorry⟩
  advance := λ s (i,j) => (advance s i, advance (((toIdx i).1 + s) / size ι) j)
  
  fromIdx_toIdx := λ _ => sorry
  toIdx_fromIdx := λ _ => sorry

  instance [Index ι] [Index κ] : Index (ι ⊕ κ) where
    isValid := 
    if numOf ι + numOf κ < USize.size - 1  then 
      Index.isValid ι && Index.isValid κ
    else 
      -- this is using the fact that `(default : Bool) = false`
      panic! s!"Attempting to create `Index (ι⊕κ)` for too big `ι` and `κ`.\n  `numOf ι = {numOf ι}`\n  `numOf κ = {numOf κ}`" 
 
    fromIdx := λ i => 
      if i.1 < size ι
      then Sum.inl $ fromIdx ⟨i.1, sorry⟩ 
      else Sum.inr $ fromIdx ⟨i.1 - size ι, sorry⟩
    toIdx := λ ij => 
      match ij with
      | Sum.inl i => ⟨(toIdx i).1, sorry⟩
      | Sum.inr j => ⟨(toIdx j).1 + size ι, sorry⟩
    advance := λ s ij => 
      have : Inhabited _ := ⟨ij⟩
      panic! "Implement Index.advance for ι⊕κ!"

    fromIdx_toIdx := λ _ => sorry
    toIdx_fromIdx := λ _ => sorry


  structure Range (ι : Type u) [Index ι] where
    start? : Option ι := Iterable.first
    stop  : USize := Index.size ι
    step  : USize := 1

  def fullRange (ι : Type u) [Index ι] : Range ι := {}


  -- syntax:max "range[" term "]" : term
  -- -- syntax:max "r[" withoutPosition(":" term) "]" : term
  -- -- syntax:max "r[" withoutPosition(term ":" term) "]" : term
  -- -- syntax:max "r[" withoutPosition(":" term ":" term) "]" : term
  -- -- syntax:max "r[" withoutPosition(term ":" term ":" term) "]" : term

  -- macro_rules
  --   | `(range[ $type ]) => `(({} : Range $type))
    -- | `(r[ : $stop]) => `({ stop := $stop : Range _ })
    -- | `(r[ $start : $stop ]) => `({ start? := some $start, stop := $stop : Range _ })
    -- | `(r[ $start : $stop : $step ]) => `({ start? := some $start, stop := $stop, step := $step : Range _ })
    -- | `(r[ : $stop : $step ]) => `({ stop := $stop, step := $step : Range _ })

  @[inline] partial def Range.forIn {ι : Type v} [Index ι] {β : Type u} {m : Type u → Type v} [Monad m] (range : Range ι) (init : β) (f : ι × USize → β → m (ForInStep β)) : m β :=
    -- pass `stop` and `step` separately so the `range` object can be eliminated through inlining
    let rec @[specialize] loop (i : USize) (idx : ι) (stop step : USize) (b : β) : m β := do
      if i ≥ stop then
        return b
      else
        match (← f (idx, i) b) with
          | ForInStep.done b  => pure b
          | ForInStep.yield b => loop (i + step) (advance step idx) stop step b
    match range.start? with
    | none => pure init
    | some start =>
      loop (toIdx start).1 start range.stop range.step init


  instance {ι : Type v} [Index ι] : ForIn m (Range ι) (ι × USize) where
    forIn := Range.forIn


  -- It is important to fetch a new instance of `UpperBoundUnsafe` at call site.
  -- That way we are likely to fetch an instance of `UpperBound` if available
  def sum {α} [Zero α] [Add α] {ι} [Index ι] (f : ι → α) : α := ((do
    let mut r : α := 0 
    for (i,_) in fullRange ι do
      r := r + (f i)
    r) : Id α)

  -- TODO: add priority b:term:66
  --       This way `∑ i, f i + c = (∑ i, f i) + c` i.e. sum gets stopped by `+` and `-`
  --       The paper 'I♥LA: compilable markdown for linear algebra' https://doi.org/10.1145/3478513.3480506  
  --           claims on page 5 that conservative sum is more common then greedy


  open Lean.TSyntax.Compat in
  macro "∑" xs:Lean.explicitBinders ", " b:term:66 : term => Lean.expandExplicitBinders ``Index.sum xs b

