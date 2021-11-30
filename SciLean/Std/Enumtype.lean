namespace SciLean

-- Enumerable type
class Enumtype (α : Type u) where
  n : Nat
  fromFin : Fin n → α
  toFin : α → Fin n
  to_from : ∀ i, toFin (fromFin i) = i
  from_to : ∀ a, fromFin (toFin a) = a

--- TODO: Add product
--        Which order do we prefer?
--- TODO: Add function from Enumtype to Enumtype
--        Which order do we prefer?
