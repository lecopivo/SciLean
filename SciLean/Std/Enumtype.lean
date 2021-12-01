namespace SciLean

-- Enumerable type
class Enumtype (α : Type u) where
  numOf : Nat
  fromFin : Fin numOf → α
  toFin : α → Fin numOf
  to_from : ∀ i, toFin (fromFin i) = i
  from_to : ∀ a, fromFin (toFin a) = a

export Enumtype (numOf fromFin toFin)

namespace Enumtype

-- Column major ordering
-- TODO: Add global option to switch to row-major
-- As discussion on stackexchange: https://scicomp.stackexchange.com/questions/4796/row-major-versus-column-major-layout-of-matrices
-- It seems that there is no real benefit of one or the other
-- The choice is mainly for convenience/historical reasons rather then speed reason.
-- I will stick with Fortran style colum major as in the future I will probably wrap Eigen library that is column-major.
instance [Enumtype α] [Enumtype β] : Enumtype (α × β) :=
{
   numOf := numOf α * numOf β
   fromFin := λ i => (fromFin ⟨i.1 % numOf α, sorry⟩, fromFin ⟨i.1 / numOf α, sorry⟩)
   toFin   := λ (a,b) => ⟨(toFin a).1 + (numOf α) * (toFin b).1, sorry⟩
   to_from := sorry
   from_to := sorry
}

-- instance [Enumtype α] [Enumtype β] : Enumtype (α → β) :=
-- {
--   numOf := (numOf β)^(numOf α)
--   fromFin := λ i a => fromFin (⟨i.1 / ((numOf β)^(toFin a).1) % (numOf β), sorry⟩)
--   toFin   := λ f => ⟨∑ i : Fin (numOf α), (i |> fromFin |> f |> toFin).1 * (numOf β)^i.1, sorry⟩
--   to_from := sorry
--   from_to := sorry
-- }

instance : Enumtype (Fin n) :=
{
  numOf := n
  fromFin := id
  toFin := id
  to_from := by intro _; simp done
  from_to := by intro _; simp done
}

-- TODO: Somehow add this to the for loop. 
-- Having a proof about the compatibility of the index and linear index.
structure ValidLinIndex {ι} [Enumtype ι] (i : ι) (li : Nat) : Type where
  valid : li = (toFin i).1

-- A range is `some (first, last)` where last is !included! to the range
-- if an empty range then it is `none`
def Range (α : Type u) [Enumtype α] := Option (α × α)
def range {α} [Enumtype α] (s e : α) : Range α := some (s,e)

instance (α : Type u) [Enumtype α] [ToString α] : ToString (Range α) := 
  ⟨λ r => 
    match r with
      | none => "[:]"
      | some (s,e) => s!"[{s}:{e}]"⟩

def fullRange (α : Type u) [Enumtype α] : Range α :=
    match (numOf α) with
      | 0 => none
      | n+1 => some (fromFin ⟨0, sorry⟩, fromFin ⟨n, sorry⟩)

instance {m} [Monad m] {n}
         : ForIn m (Range (Fin n)) (Fin n × Nat) :=
{
  forIn := λ r init f => 
             match r with
               | none => init
               | some (s,e) => do
                 let mut val := init
                 for i in [s.1:e.1+1] do
                   match (← f (⟨i,sorry⟩, i) val) with
                     | ForInStep.done d => return d
                     | ForInStep.yield d => val ← d
                 pure val
}

-- Colum-major ordering, i.e. the inner loop runs over ι
instance {m} [Monad m] [Enumtype ι] [Enumtype κ]
         [ForIn m (Range ι) (ι × Nat)]
         [ForIn m (Range κ) (κ × Nat)]
         : ForIn m (Range (ι × κ)) ((ι × κ) × Nat) :=
{
  forIn := λ r init f => 
             match r with 
               | none => init
               | some ((is,js),(ie,je)) => do
                 let mut val := init
                 for (j,lj) in (range js je) do
                   let offset := (numOf ι) * lj
                   for (i,li) in (range is ie) do
                     match (← f ((i,j), li + offset) val) with
                       | ForInStep.done d => return d
                       | ForInStep.yield d => val ← d
                 pure val
}


-- Marking product to be stored in row-major order
def RowProd (α β) := α × β
infixr:35 " ×ᵣ "  => RowProd

instance [ToString α] [ToString β] : ToString (α ×ᵣ β) := ⟨λ (a,b) => s!"({a},{b})"⟩

instance [Enumtype α] [Enumtype β] : Enumtype (α ×ᵣ β) :=
{
   numOf := numOf α * numOf β
   fromFin := λ i => (fromFin ⟨i.1 / numOf β, sorry⟩, fromFin ⟨i.1 % numOf β, sorry⟩)
   toFin   := λ (a,b) => ⟨(toFin b).1 + (numOf β) * (toFin a).1, sorry⟩
   to_from := sorry
   from_to := sorry
}

-- Row-major ordering, i.e. the inner loop runs over κ
instance {m} [Monad m] [Enumtype ι] [Enumtype κ]
         [ForIn m (Range ι) (ι × Nat)]
         [ForIn m (Range κ) (κ × Nat)]
         : ForIn m (Range (ι ×ᵣ κ)) ((ι ×ᵣ κ) × Nat) :=
{
  forIn := λ r init f =>
             match r with 
               | none => init
               | some ((is,js),(ie,je)) => do
                 let mut val := init
                 for (i,li) in (range is ie) do
                   let offset := (numOf κ) * li
                   for (j,lj) in (range js je) do
                     match (← f ((i,j), lj + offset) val) with
                       | ForInStep.done d => return d
                       | ForInStep.yield d => val ← d
                 pure val
}

-- example : (236 : Fin 1000) = (toFin ((6 : Fin 10), (3 : Fin 10), (2 : Fin 10))) := by rfl
-- example : (3,5,8) = (fromFin (853 : Fin 1000) : Fin 10 × Fin 10 × Fin 10) := by rfl
-- example : (⟨1023,sorry⟩ : Fin (2^10)) = (toFin (λ i : Fin 10 => (1 : Fin 2))) := by rfl

