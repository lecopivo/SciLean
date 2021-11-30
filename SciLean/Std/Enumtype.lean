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

example : (236 : Fin 1000) = (toFin ((6 : Fin 10), (3 : Fin 10), (2 : Fin 10))) := by rfl
example : (3,5,8) = (fromFin (853 : Fin 1000) : Fin 10 × Fin 10 × Fin 10) := by rfl

-- #eval (toFin (λ i : Fin 50 => (1 : Fin 2)))
-- #eval (fromFin (⟨234,sorry⟩ : Fin _) : Fin 4 → Fin 10)
