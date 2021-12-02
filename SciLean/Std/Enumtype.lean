import SciLean.Std.Iterable
namespace SciLean

-- Enumerable type
class Enumtype (α : Type u) extends Iterable α where
  numOf : Nat
  fromFin : Fin numOf → α
  toFin : α → Fin numOf

  --- Data compatibility of Enumtype and Iterable
  first_fromFin :
    match numOf with
      | 0 => True
      | n+1 => first = fromFin !0
  next_fromFin : 
    match numOf with
      | 0 => True
      | n+1 => ∀ (i : Fin n), 
        next (fromFin !i.1) = fromFin (!(i.1+1))
        ∧ 
        next (fromFin !n) = none
  next_toFin : ∀ (a : α),
    match (next a) with
      | none => True
      | some nxt => Iterable.next (toFin a) = some (toFin nxt)

export Enumtype (numOf fromFin toFin)

namespace Enumtype

  instance : Enumtype (Fin n) :=
  {
    numOf := n
    fromFin := id
    toFin := id

    first_fromFin := sorry
    next_fromFin  := sorry
    next_toFin    := sorry
  }

  --- Row-major 
  instance [Enumtype α] [Enumtype β] : Enumtype (α × β) :=
  {
     numOf := numOf α * numOf β
     fromFin := λ i => (fromFin ⟨i.1 / numOf β, sorry⟩, fromFin ⟨i.1 % numOf β, sorry⟩)
     toFin   := λ (a,b) => ⟨(toFin b).1 + (numOf β) * (toFin a).1, sorry⟩

     first_fromFin := sorry
     next_fromFin  := sorry
     next_toFin    := sorry
  }

  --- Col-major
  instance [Enumtype α] [Enumtype β] : Enumtype (α ×ₗ β) :=
  {
     numOf := numOf α * numOf β
     fromFin := λ i => (fromFin ⟨i.1 % numOf α, sorry⟩, fromFin ⟨i.1 / numOf α, sorry⟩)
     toFin   := λ (a,b) => ⟨(toFin a).1 + (numOf α) * (toFin b).1, sorry⟩

     first_fromFin := sorry
     next_fromFin  := sorry
     next_toFin    := sorry
  }

  -- This is closed range! Includes last element!
  def Range (α : Type u) [Enumtype α] := Option (α × α)
  def range {α} [Enumtype α] (s e : α) : Range α := some (s,e)

  --- Should we have `×` or `×ₗ` there?
  instance [Enumtype ι] [Enumtype κ] : HMul (Range ι) (Range κ) (Range (ι × κ)) :=
    ⟨λ I J =>
       match I, J with
         | (some (is,ie)), (some (js,je)) => some ((is,js), (ie,je))
         | _, _ => none⟩

  instance (α : Type u) [Enumtype α] [ToString α] : ToString (Range α) := 
    ⟨λ r => 
      match r with
        | none => "[]"
        | some (s,e) => s!"[{s}:{e}]"⟩

  def fullRange (α : Type u) [Enumtype α] : Range α :=
      match (numOf α) with
        | 0 => none
        | n+1 => some (fromFin ⟨0, sorry⟩, fromFin ⟨n, sorry⟩)


  -- TODO: Somehow add this to the for loop. 
  -- Having a proof about the compatibility of the index and linear index would be nice.
  structure ValidLinIndex {ι} [Enumtype ι] (i : ι) (li : Nat) : Type where
    valid : li = (toFin i).1

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

  -- Row-major ordering, i.e. the inner loop runs over κ
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
                   for (i,li) in (range is ie) do
                     let offset := (numOf κ) * li
                     for (j,lj) in (range js je) do
                       match (← f ((i,j), lj + offset) val) with
                         | ForInStep.done d => return d
                         | ForInStep.yield d => val ← d
                   pure val
  }

  -- Colum-major ordering, i.e. the inner loop runs over ι
  instance {m} [Monad m] [Enumtype ι] [Enumtype κ]
           [ForIn m (Range ι) (ι × Nat)]
           [ForIn m (Range κ) (κ × Nat)]
           : ForIn m (Range (ι ×ₗ κ)) ((ι ×ₗ κ) × Nat) :=
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


  -- Marking product to be stored in Column-major order


  -- example : (236 : Fin 1000) = (toFin ((6 : Fin 10), (3 : Fin 10), (2 : Fin 10))) := by rfl
  -- example : (3,5,8) = (fromFin (853 : Fin 1000) : Fin 10 × Fin 10 × Fin 10) := by rfl
  -- example : (⟨1023,sorry⟩ : Fin (2^10)) = (toFin (λ i : Fin 10 => (1 : Fin 2))) := by rfl

