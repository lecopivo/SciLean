import SciLean.Algebra

namespace SciLean

-- Enumerable type
class Enumtype (α : Type u) where
  num : Nat
  fromFin : Fin num → α
  toFin : α → Fin num
  to_from : ∀ i, toFin (fromFin i) = i
  from_to : ∀ a, fromFin (toFin a) = a

export Enumtype (fromFin toFin)

namespace Enumtype

-- Column major ordering
-- TODO: Add global option to switch to row-major
-- As discussion on stackexchange: https://scicomp.stackexchange.com/questions/4796/row-major-versus-column-major-layout-of-matrices
-- It seems that there is no real benefit of one or the other
-- The choice is mainly for convenience/historical reasons rather then speed reason.
-- I will stick with Fortran style colum major as in the future I will probably wrap Eigen library that is column-major.
instance [Enumtype α] [Enumtype β] : Enumtype (α × β) :=
{
   num := num α * num β
   fromFin := λ i => (fromFin ⟨i.1 % num α, sorry⟩, fromFin ⟨i.1 / num α, sorry⟩)
   toFin   := λ (a,b) => ⟨(toFin a).1 + (num α) * (toFin b).1, sorry⟩
   to_from := sorry
   from_to := sorry
}

-- Marking product to be stored in row-major order
def RowProd (α β) := α × β
infixr:35 " ×ᵣ "  => RowProd

instance [Enumtype α] [Enumtype β] : Enumtype (α ×ᵣ β) :=
{
   num := num α * num β
   fromFin := λ i => (fromFin ⟨i.1 % num β, sorry⟩, fromFin ⟨i.1 / num β, sorry⟩)
   toFin   := λ (a,b) => ⟨(toFin b).1 + (num β) * (toFin a).1, sorry⟩
   to_from := sorry
   from_to := sorry
}

instance [Enumtype α] [Enumtype β] : Enumtype (α → β) :=
{
  num := (num β)^(num α)
  fromFin := λ i a => fromFin (⟨i.1 / ((num β)^(toFin a).1) % (num β), sorry⟩)
  toFin   := λ f => ⟨∑ i : Fin (num α), (i |> fromFin |> f |> toFin).1 * (num β)^i.1, sorry⟩
  to_from := sorry
  from_to := sorry
}

instance : Enumtype (Fin n) :=
{
  num := n
  fromFin := id
  toFin := id
  to_from := by intro _; simp done
  from_to := by intro _; simp done
}

-- Preform fold based on the linearization in Enumtype
def seqForIdxM {ι} [Enumtype ι] {m} [Monad m] 
               (f : ι → Fin (num ι) → m Unit) : m Unit :=
do 
  for i in [0:num ι] do
    let i' := ⟨i, sorry⟩
    let id := fromFin ⟨i, sorry⟩
    f id i'
  ()
  
class For (ι : Type u) [Enumtype ι] where
  forIdxM {m} [Monad m] (f : ι → Fin (num ι) → m Unit) : m Unit
  valid : @seqForIdxM ι _ = @forIdxM

instance {n} : For (Fin n) :=
{
  forIdxM := seqForIdxM
  valid := by rfl
}

instance {ι κ} [Enumtype ι] [Enumtype κ] [For ι] [For κ] : For (ι × κ) :=
{
  forIdxM := λ {m} [Monad m] 
               (f : ι × κ → Fin (num (ι×κ)) → m Unit) =>
               do
                 let col := λ (j : κ) (lj : Fin (num κ)) =>
                              let offset := (num ι) * lj.1
                              For.forIdxM (λ i li => f (i,j) ⟨li.1 + offset, sorry⟩)
                 For.forIdxM col
  valid := sorry
}

-- Preform fold based on the linearization in Enumtype
def seqFoldIdxM {ι} [Enumtype ι] {α β m} [Monad m] 
                (f : ι → Fin (num ι) → α) (op : ι → Fin (num ι) → α → β → m β) (b₀ : β) : m β :=
do 
  let mut b := b₀
  for i in [0:num ι] do
    let i' := ⟨i, sorry⟩
    let id := fromFin i'
    b ← (op id i' (f id i') b)
  b  

--- Specialized fold function 
-- Maybe I want to include linear index to `op` and `f` as it can be usually computed incrementaly
-- and quite often getting an element with linear index is the fastest way
-- it might not be effective to call fromFin all the time for complicated indices!
class Fold (ι : Type u) [Enumtype ι] where
  foldIdxM {α β m} [Monad m] (f : ι → Fin (num ι) → α) (op : ι → Fin (num ι) → α → β → m β) (b₀ : β) : m β
  valid : @seqFoldIdxM ι _ = @foldIdxM


instance {n} : Fold (Fin n) :=
{
  foldIdxM := seqFoldIdxM
  valid := by rfl
}

-- TODO: Support row-major ordering!
instance {ι κ} [Enumtype ι] [Enumtype κ] [Fold ι] [Fold κ] : Fold (ι × κ) :=
{
  foldIdxM := λ {α β m} [Monad m] 
                (f : ι × κ → Fin (num (ι×κ)) → α) 
                (op : ι × κ → Fin (num (ι×κ)) → α → β → m β) (b₀ : β) => 
                do
                  let col := λ (j : κ) (lj : Fin (num κ)) (b : β) => 
                               let offset := (num ι) * lj.1
                               Fold.foldIdxM (λ i li =>  f (i,j) ⟨li.1 + offset, sorry⟩) 
                                             (λ i li => op (i,j) ⟨li.1 + offset, sorry⟩) b
                  let op' := λ (j : κ) (lj : Fin (num κ)) (col : β → m β) (b : β) => col b
                  Fold.foldIdxM col op' b₀
  valid := sorry
}

open Fold (foldIdxM) 

variable {ι} [Enumtype ι] [Fold ι]

def foldIdx {α β} (f : ι → Fin (num ι) → α) (op : ι → Fin (num ι) → α → β → β) (b₀ : β) : β 
            := (Fold.foldIdxM f op b₀ : Id β)

 
example : (236 : Fin 1000) = (toFin ((6 : Fin 10), (3 : Fin 10), (2 : Fin 10))) := by rfl
example : (3,5,8) = (fromFin (853 : Fin 1000) : Fin 10 × Fin 10 × Fin 10) := by rfl
example : (⟨1023,sorry⟩ : Fin (2^10)) = (toFin (λ i : Fin 10 => (1 : Fin 2))) := by rfl
example : 61 = (foldIdx (λ ((i,j) : Fin 4 × Fin 10) _ => i.1) (λ _ _ a b => a + b) 1) := by rfl

