
namespace SciLean


--------------------------------------------------------------------------------

class UncurryN (n : Nat) (F : Type) (Xs : outParam Type) (Y : outParam Type) where
  uncurry : F → Xs → Y

attribute [reducible] UncurryN.uncurry

@[reducible]
instance (priority := low) {X Y : Type} : UncurryN 1 (X→Y) X Y where
  uncurry := λ (f : X → Y) (x : X) => f x

@[reducible]
instance {X Y : Type} {Xs' Y' : outParam Type} [c : UncurryN n Y Xs' Y']
  : UncurryN (n+1) (X→Y) (X×Xs') Y' where
  uncurry := λ (f : X → Y) ((x,xs) : X×Xs') => c.uncurry (n:=n) (f x) xs

abbrev uncurryN {F : Type} {Xs Y : outParam Type} 
  (n : Nat) (f : F) [UncurryN n F Xs Y] 
  := UncurryN.uncurry (n:=n) f

----

class UncurryAll (F : Sort _) (Xs : outParam (Sort _)) (Y : outParam (Sort _)) where
  uncurry : F → Xs → Y

attribute [reducible] UncurryAll.uncurry

@[reducible]
instance (priority := low) {X Y : Sort _} : UncurryAll (X→Y) X Y where
  uncurry := λ (f : X → Y) (x : X) => f x

@[reducible]
instance {X Y : Sort _} {Xs' Y' : outParam (Sort _)} [c : UncurryAll Y Xs' Y']
  : UncurryAll (X→Y) (X×Xs') Y' where
  uncurry := λ (f : X → Y) ((x,xs) : X×Xs') => c.uncurry (f x) xs

abbrev uncurryAll {F : Type} {Xs Y : outParam Type} 
  (f : F) [UncurryAll F Xs Y] 
  := UncurryAll.uncurry f


--------------------------------------------------------------------------------

class CurryN (n : Nat) (Xs : Type) (Y : Type) (F : outParam Type) where
  curry : (Xs → Y) → F

attribute [reducible] CurryN.curry

@[reducible]
instance (priority := low) : CurryN 1 X Y (X→Y) where
  curry := λ (f : X → Y) => f

@[reducible]
instance {X Xs Y : Type} {F : outParam Type} [c : outParam $ CurryN n Xs Y F] 
  : CurryN (n+1) (X×Xs) Y (X→F) where
  curry := λ (f : X×Xs → Y) => (λ (x : X) => c.curry (n:=n) (λ y => f (x,y)))

abbrev curryN {Xs Y : outParam $ Type} {F : outParam Type} 
  (n : Nat) (f : Xs → Y) [outParam $ CurryN n Xs Y F] := CurryN.curry n f

---


class CurryAll (n : Nat) (Xs : Type) (Y : Type) (F : outParam Type) where
  curry : (Xs → Y) → F

attribute [reducible] CurryAll.curry

@[reducible]
instance (priority := low) : CurryAll 1 X Y (X→Y) where
  curry := λ (f : X → Y) => f

@[reducible]
instance {X Xs Y : Type} {F : outParam Type} [c : outParam $ CurryAll n Xs Y F] 
  : CurryAll (n+1) (X×Xs) Y (X→F) where
  curry := λ (f : X×Xs → Y) => (λ (x : X) => c.curry (n:=n) (λ y => f (x,y)))

abbrev curryAll {Xs Y : outParam $ Type} {F : outParam Type} 
  (n : Nat) (f : Xs → Y) [outParam $ CurryAll n Xs Y F] := CurryAll.curry n f



--------------------------------------------------------------------------------



section Tests

  example : uncurryN 3 (λ i j k : Nat => i + j) = λ (i,j,k) => i + j := by rfl
  example : uncurryN 2 (λ i j k : Nat => i + j) = λ (i,j) k => i + j := by rfl

  example : curryN 3 (λ ((i,j,k) : Nat×Nat×Nat) => i + j) = (λ i j k : Nat  => i + j) := by rfl
  -- example : curryN 2 (λ ((i,j,k) : Nat×Nat×Nat) => i + j) = (λ (i : Nat) ((j,k) : Nat×Nat) => i + j) := by rfl

end Tests
