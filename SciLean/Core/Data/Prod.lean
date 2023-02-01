namespace SciLean


class ProdInfo (n : outParam Nat) (X : Type) where
  proj : Fin size → Type

class FunInfo (nargs : outParam Nat) (F : Type) : Type 1 where
  arg : Fin nargs → Type

abbrev funNArg (F : Type) [FunInfo nargs F] := nargs
abbrev funArg (F : Type) [FunInfo nargs F] (i : Fin (funNArg F)) := FunInfo.arg F i

attribute [reducible] FunInfo.arg


@[reducible]
instance (priority := low) : FunInfo (no_index 0) X where
  arg := λ ⟨i,h⟩ => absurd h sorry

@[reducible]
instance {n : Nat} {X F : Type} [inst : FunInfo n F] : FunInfo (no_index (n+1)) (X → F) where
  arg := λ i => 
    match i with
    | ⟨0, _⟩ => X
    | ⟨n+1, _⟩ => FunInfo.arg F ⟨n,sorry⟩


variable (X Y Z : Type)

example : funArg (X → Y) 0 = X := by rfl
example : funArg (X → Y → Z) 0 = X := by rfl
example : funArg (X → Y → Z) 1 = Y := by rfl
