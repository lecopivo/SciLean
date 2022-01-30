import SciLean.Algebra

namespace SciLean

structure FreeMonoid (X : Type u) where
  vars : List X

namespace FreeMonoid

  instance {X} : Mul (FreeMonoid X) := ⟨λ x y => ⟨x.1.append y.1⟩⟩
  instance {X} : One (FreeMonoid X) := ⟨⟨[]⟩⟩

  def rank {X} (x : FreeMonoid X) : Nat := x.1.length

  -- inductive SymmMonoidEq {X} : FreeMonoid X → FreeMonoid X → Prop where
  --   | mul_comm (x y : FreeMonoid X) : SymmMonoidEq (x*y) (y*x)

end FreeMonoid

