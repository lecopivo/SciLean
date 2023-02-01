namespace SciLean

class Uncurry (n : Nat) (F : Type) (Xs : outParam Type) (Y : outParam Type) where
  uncurry : F → Xs → Y

attribute [reducible] Uncurry.uncurry

@[reducible]
instance prod_uncurry_zero {X : Type} : Uncurry (no_index 0) X Unit X where
  uncurry := λ f _ => f

@[reducible]
instance (priority:=high) prod_uncurry_one {X Y : Type} : Uncurry (no_index 1) (X→Y) X Y where
  uncurry := λ f => f

@[reducible]
instance uncurry_succ {X Y : Type} {Xs Y' : outParam Type} [c : Uncurry n Y Xs Y'] : Uncurry (no_index (n+1)) (X→Y) (X×Xs) Y' where
  uncurry := λ (f : X → Y) (x,xs) => c.uncurry n (f x) xs

abbrev uncurry {F : Type} {Xs Y : outParam Type} (n : Nat) (f : F) [Uncurry n F Xs Y] 
  := Uncurry.uncurry (n:=n) f


-- example {F Xs Y' : Type} [Uncurry (n+1) F Xs Y'] 
--   : Uncurry n F (X×Ys) Y' := by infer_instance


------------------------------------------------------------------------------------------


class Curry (n : Nat) (Xs : Type) (Y : Type) (F : outParam Type) where
  curry : (Xs → Y) → F

attribute [reducible] Curry.curry

@[reducible]
instance prod_curry_zero {X : Type} : Curry (no_index 0) Unit X X where
  curry := λ f => f ()

@[reducible]
instance (priority:=high) prod_curry_one {X : Type} : Curry (no_index 1) X Y (X→Y) where
  curry := λ f => f

@[reducible]
instance {X Xs Y : Type} {F : outParam Type} [c : Curry n Xs Y F] : Curry (no_index (n+1)) (X×Xs) Y (X→F) where
  curry := λ (f : X×Xs → Y) x => c.curry n (λ xs => f (x,xs))

abbrev curry {Xs Y : Type} {F : outParam Type} (n : Nat) (f : Xs → Y) [Curry n Xs Y F] 
  := Curry.curry (n:=n) f


------------------------------------------------------------------------------------------

#check uncurry 4 (λ (a b c : Nat) (d : Float) => a + b + c + d.toUInt64.toNat)
#check curry 4 <| uncurry 4 (λ (a b c : Nat) (d : Float) => a + b + c + d.toUInt64.toNat)


example : uncurry 3 (λ i j k : Nat => i + j) = λ (i,j,k) => i + j := by rfl
example : uncurry 2 (λ i j k : Nat => i + j) = λ (i,j) k => i + j := by rfl

example : curry 3 (λ ((i,j,k) : Nat×Nat×Nat) => i + j) = (λ i j k : Nat => i + j) := by rfl
