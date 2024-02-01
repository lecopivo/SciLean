
namespace SciLean

structure ArrayN (α : Type) (n : Nat) where
  data : Array α
  h_size : n = data.size

@[default_instance]
instance : GetElem (ArrayN α n) (Fin n) α (λ _ _ => True) where
  getElem arr i _ := arr.data.get (arr.h_size ▸ i)

instance [Inhabited α] : Inhabited (ArrayN α n) :=
  ⟨{
    data := .mkArray n default
    h_size := by simp
  }⟩
