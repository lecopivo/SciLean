import Mathlib.Algebra.Group.Defs

import SciLean.Mathlib.Data.ColProd

-- `first` is `Option ι` because we want `Fin n`, in particular `Fin 0`, to be Iterable.
-- I do not like it and we might want to define a new `Fin n` where `n` is a true natural number i.e. positive integers
class Iterable (ι : Type u) where
  first    : Option ι  
  next     : ι → Option ι
  -- TODO: valid : "traverses the whole type" i.e. every element is reachable by `next`
  -- This can be stated as an existence of a bijection between `ι` and `Fin n` for suitable `n`
  decEq : DecidableEq ι

attribute [reducible] Iterable.decEq

-- Iterable that respects inequality
class IterableLt (ι : Type u) extends LT ι, Iterable ι where 
  next_lt : ∀ (i : ι), 
               match (next i) with
                   | (some nxt) => i < nxt
                   | none => True

namespace Iterable 

  variable {ι} [Iterable ι]

  def next! : Option ι → Option ι 
    | none => none
    | some i => next i

  def move! (n : Nat) (i : Option ι) : Option ι :=
    match n with
      | 0 => i
      | n+1 => move! n (next! i)

  instance : DecidableEq ι := Iterable.decEq

  instance : Iterable Unit :=
  {
    first := some Unit.unit
    next  := λ i => none
    decEq := by infer_instance
  }

  instance : Iterable (Fin n) :=
  {
    first := match n with | 0 => none | _ => some ⟨0,sorry⟩
    next  := λ i => if (i.1+1<n) then some ⟨i.1+1, sorry⟩ else none
    decEq := by infer_instance
  }

  -- Row major ordering, this respects `<` defined on `ι × κ`
  instance [Iterable ι] [Iterable κ]
           : Iterable (ι × κ) :=
  {
    first := 
      match first, first with
        | (some i), (some j) => some (i,j)
        | _, _ => none
    next := λ (i,j) => 
      let j' := next j
      match (next j) with
        | some j' => some (i, j')
        | none => 
        match (next i), first with
          | (some i'), (some js) => some (i', js)
          | _, _ => none
    decEq := by infer_instance
  }
  
  -- Iterators on `ι × κ` respects `<`
  instance [IterableLt ι] [IterableLt κ] : IterableLt (ι × κ) := ⟨sorry⟩

    -- Column major ordering, this respects `<` defined on `ι ×ₗ κ`
  instance [Iterable ι] [Iterable κ]
           : Iterable (ι ×ₗ κ) :=
  {
    first := 
      match first, first with
        | (some i), (some j) => some (i,j)
        | _, _ => none
    next := λ (i,j) => 
      let i' := next i
      match (next i) with
        | some i' => some (i', j)
        | none => 
        match first, (next j) with
          | (some is), (some j') => some (is, j')
          | _, _ => none
    decEq := by simp[ColProd] infer_instance
  }
  
  -- Iterators on `ι ×ₗ κ` respects `<`
  instance [IterableLt ι] [IterableLt κ] : IterableLt (ι ×ₗ κ) := ⟨sorry⟩


  instance [Iterable ι] [Iterable κ]
           : Iterable (ι ⊕ κ) :=
  {
    first := 
      match (first : Option ι) with
        | some i => some $ Sum.inl i
        | none =>
        match (first : Option κ) with
          | some j => some $ Sum.inr j
          | none => none

    next := λ ij =>
      match ij with
        | Sum.inl i => 
          match (next i) with
            | some i' => some $ Sum.inl i'
            | none    => 
              match (first : Option κ) with
                | some j => some $ Sum.inr j
                | none   => none
        | Sum.inr j => 
          match (next j) with
            | some j' => some $ Sum.inr j'
            | none    => none
         
    decEq := by infer_instance
  }

  -- This range might be confusing because if `<` is defined on `ι`
  -- then the range (i,j) for `i>j` is not empty but equivalent to (i,pastLast)
  def LinRange (ι : Type u) [Iterable ι] := Option (ι × Option ι)

  -- Closed range 
  def Range (ι : Type u) [Iterable ι] := Option (ι × ι)
  -- TODO: Get range over a box given by ranges along each dimension
  instance {κ} [Iterable κ] : HMul (Range ι) (Range κ) (Range (ι × κ)) := ⟨sorry⟩
  
  def fullRange (ι : Type u) [Iterable ι] : LinRange ι := 
    match first with 
      | some fst => some (fst, none) 
      | none => none

  class UpperBoundUnsafe (ι) [Iterable ι] where 
    upperBound : Nat

  export UpperBoundUnsafe (upperBound)

  -- For any practical purposes you do not want to do more then USize.size iterations :)
  instance (priority := low) (ι) [Iterable ι] : UpperBoundUnsafe ι := ⟨USize.size⟩

  class UpperBound (ι) [Iterable ι] extends UpperBoundUnsafe ι where 
    valid : ∃ n : Nat, n < upperBound ∧ move! n (first : Option ι) = none 

  instance {m} [Monad m] {ι} [Iterable ι] [UpperBoundUnsafe ι]
           : ForIn m (LinRange ι) ι :=
  {
    forIn := λ r init f => do
      match r with
        | none => pure init
        | some (s, e) => do
          let mut val := init
          let mut it := s
          for i in [0 : upperBound ι] do
            match (← f it val) with
              | ForInStep.done val' => return val'
              | ForInStep.yield val' => 
                match (next it) with
                  | none => return val'
                  | some nxt => 
                    --- We might want to check if `e` is `none` at the beginning 
                    --- then add a branch that does not have this check
                    if nxt == e then   
                      return val'
                    else do
                      val ← pure val'
                      it := nxt
          pure val
  }

  -- -- It is important to fetch a new instance of `UpperBoundUnsafe` at call site.
  -- -- That way we are likely to fetch an instance of `UpperBound` if available
  -- def sum {α} [Zero α] [Add α] {ι} [Iterable ι] [outParam $ UpperBoundUnsafe ι] (f : ι → α) : α := ((do
  --   let mut r : α := 0 
  --   for i in fullRange ι do
  --     r := r + (f i)
  --   r) : Id α)

  -- macro "∑" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders `Iterable.sum xs b

  
  --- TODO: Add ForIn over Range
  --- see ForIn in Enumtype for inspiration
