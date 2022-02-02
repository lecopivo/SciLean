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

  def toString {X} [ToString X] (x : FreeMonoid X) (mul : String) : String :=
    let rec impl (l : List X) : String :=
      match l with
      | [] => "1"
      | [x1] => s!"[{x1}]"
      | x1 :: x2 :: xs => s!"[{x1}]{mul}{impl $ x2 :: xs}"
    impl x.1

  instance {X} [ToString X] : ToString (FreeMonoid X) :=
    ⟨λ x => x.toString "⊗"⟩

  def x : FreeMonoid ℕ := ⟨[0,1,2,3]⟩

  #eval x.toString " ⊗ "
  #eval x

  instance {X} : Monoid (FreeMonoid X) := 
  {
    mul_assoc := sorry
    mul_one := sorry
    one_mul := sorry
    npow_zero' := sorry
    npow_succ' := sorry
  }

end FreeMonoid

