
-- `first` is `Option ι` because we want `Fin n`, in particular `Fin 0`, to be Iterable.
-- I do not like it and we might want to define a new `Fin n` where `n` is a true natural number i.e. positive integers
class Iterable (ι : Type u) where
  first    : Option ι  
  next     : ι → Option ι
  -- TODO: valid : "traverses the whole type" i.e. every element is reachable by `next`
  -- This can be stated as an existence of a bijection between `ι` and `Fin n` for suitable `n`
  decEq : DecidableEq ι

-- Iterable that respects inequality
class IterableLt (ι : Type u) extends LT ι, Iterable ι where 
  next_lt : ∀ (i : ι), 
               match (next i) with
                   | (some nxt) => i < nxt
                   | none => True

--- !i creates an element of a subtype with an omitted proof
--- much nicer then writing ⟨i, sorry⟩
macro:max "!" noWs t:term : term => `(⟨$t, sorry⟩)

namespace Iterable 

  variable {ι} [Iterable ι]

  def next! : Option ι → Option ι 
    | none => none
    | some i => next i

  instance : DecidableEq ι := Iterable.decEq

  instance : Iterable (Fin n) :=
  {
    first := match n with | 0 => none | _ => some !0
    next  := λ i => if (i.1+1<n) then some !(i.1+1) else none
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

  -- This range might be confusing because if `<` is defined on `ι`
  -- then the range (i,j) for `i>j` is not empty but equivalent to (i,pastLast)
  def LinRange (ι : Type u) [Iterable ι] := Option (ι × Option ι)

  def Range (ι : Type u) [Iterable ι] := Option (ι × Option ι)
  instance {κ} [Iterable κ] : HMul (Range ι) (Range κ) (Range (ι × κ)) := ⟨sorry⟩

  -- Alternative way to define a range 
  -- inductive Range' (ι : Type u) [Iterable ι] where
  -- | empty : Range' ι
  -- | full  : Range' ι
  -- | half (fst : ι) : Range' ι
  -- | interval (fst lst : ι) : Range' ι
  
  def fullRange (ι : Type u) [Iterable ι] : LinRange ι := 
    match first with 
      | some fst => some (fst, none) 
      | none => none

  --- This is not good! 
  --- We should have special for (Fin n) and then for products `×` `×ₗ` as in Enumtype
  --- Maybe provide a LinRange
  instance {m} [Monad m] {ι} [Iterable ι]
           : ForIn m (LinRange ι) ι :=
  {
    forIn := λ r init f => do
      match r with
        | none => pure init
        | some (s, e) => do
          let mut val := init
          let mut it := s
          -- Doing maximum of USize.size should be enough for any practical purposes
          for i in [0:USize.size] do
            match (← f it val) with
              | ForInStep.done val' => return val'
              | ForInStep.yield val' => 
                match (next it) with
                  | none => return val'
                  | some nxt => 
                    --- We might want to check if `e` is `none` at the beginning 
                    --- then add a branch that does not have this check
                    if (next nxt) == e then   
                      return val'
                    else do
                      val ← val'
                      it := nxt
          pure val
  }
  
  -- TODO: Move ColProd somewhere else
  def ColProd (α β) := α × β 
  -- we use `×ₗ` because some moron did not include subscript c (as 'C'olumn) into unicode 
  infixr:35 " ×ₗ "  => ColProd  

  instance [ToString α] [ToString β] : ToString (α ×ₗ β) := by simp[ColProd] infer_instance

  -- Column-wise ordering 
  instance [LT α] [LT β] : LT (α ×ₗ β) where
    lt s t := s.2 < t.2 ∨ (s.2 = t.2 ∧ s.1 < t.1)

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

  -- def rowWiseTest : IO Unit := do
  --   for i in fullRange (Fin 4 × Fin 4 × Fin 4) do
  --     IO.println s!"i = {i}" --  |  i = {i}"

  -- #eval rowWiseTest

  -- def colWiseTest : IO Unit := do
  --   for i in fullRange (Fin 4 ×ₗ Fin 4 ×ₗ Fin 4) do
  --     IO.println s!"i = {i}"

  -- #eval colWiseTest

