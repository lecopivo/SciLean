import SciLean.Util.SorryProof
namespace SciLean

--------------------------------------------------------------------------------

class FunNArgs (n : Nat) (F : Sort _) (Xs : outParam <| Sort _) (Y : outParam <| Sort _) where
  uncurry : F → Xs → Y
  curry : (Xs → Y) → F
  is_equiv : curry ∘ uncurry = id ∧ uncurry ∘ curry = id

attribute [reducible] FunNArgs.uncurry FunNArgs.curry

@[reducible]
instance (priority := low) {X Y : Sort _} : FunNArgs 1 (X→Y) X Y where
  uncurry := λ (f : X → Y) (x : X) => f x
  curry := λ (f : X → Y) (x : X) => f x
  is_equiv := by constructor <;> rfl

@[reducible]
instance (priority := low) {X Xs Y F : Sort _} [fn : FunNArgs n F Xs Y] : FunNArgs (n+1) (X→F) (X×Xs) Y where
  uncurry := λ (f : X → F) ((x,xs) : X×Xs) => fn.uncurry (n:=n) (f x) xs
  curry := λ (f : X×Xs → Y) (x : X) => fn.curry (n:=n) (fun xs => f (x,xs))
  is_equiv :=
    by constructor
       . funext x xs; simp; sorry_proof
       . funext f (x,xs); simp; sorry_proof


--------------------------------------------------------------------------------

class UncurryN (n : Nat) (F : Sort _) (Xs : outParam (Sort _)) (Y : outParam (Sort _)) where
  uncurry : F → Xs → Y

attribute [reducible] UncurryN.uncurry

@[reducible]
instance (priority := low) {X Y : Sort _} : UncurryN 1 (X→Y) X Y where
  uncurry := λ (f : X → Y) (x : X) => f x

@[reducible]
instance {X Y : Sort _} {Xs' Y' : outParam (Sort _)} [c : UncurryN n Y Xs' Y']
  : UncurryN (n+1) (X→Y) (X×Xs') Y' where
  uncurry := λ (f : X → Y) ((x,xs) : X×Xs') => c.uncurry (n:=n) (f x) xs

abbrev uncurryN {F : Sort _} {Xs Y : outParam (Sort _)}
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

abbrev uncurryAll {F : Sort _} {Xs Y : outParam (Sort _)}
  (f : F) [UncurryAll F Xs Y]
  := UncurryAll.uncurry f


--------------------------------------------------------------------------------

class CurryN (n : Nat) (Xs : Sort _) (Y : Sort _) (F : outParam (Sort _)) where
  curry : (Xs → Y) → F

attribute [reducible] CurryN.curry

@[reducible]
instance (priority := low) : CurryN 1 X Y (X→Y) where
  curry := λ (f : X → Y) => f

@[reducible]
instance {X Xs Y : Sort _} {F : outParam (Sort _)} [c : outParam $ CurryN n Xs Y F]
  : CurryN (n+1) (X×Xs) Y (X→F) where
  curry := λ (f : X×Xs → Y) => (λ (x : X) => c.curry (n:=n) (λ y => f (x,y)))

abbrev curryN {Xs Y : outParam $ Sort _} {F : outParam (Sort _)}
  (n : Nat) (f : Xs → Y) [outParam $ CurryN n Xs Y F] := CurryN.curry n f

---


class CurryAll (n : Nat) (Xs : Sort _) (Y : Sort _) (F : outParam (Sort _)) where
  curry : (Xs → Y) → F

attribute [reducible] CurryAll.curry

@[reducible]
instance (priority := low) : CurryAll 1 X Y (X→Y) where
  curry := λ (f : X → Y) => f

@[reducible]
instance {X Xs Y : Sort _} {F : outParam (Sort _)} [c : outParam $ CurryAll n Xs Y F]
  : CurryAll (n+1) (X×Xs) Y (X→F) where
  curry := λ (f : X×Xs → Y) => (λ (x : X) => c.curry (n:=n) (λ y => f (x,y)))

abbrev curryAll {Xs Y : outParam $ Sort _} {F : outParam (Sort _)}
  (n : Nat) (f : Xs → Y) [outParam $ CurryAll n Xs Y F] := CurryAll.curry n f



--------------------------------------------------------------------------------



section Tests
  set_option linter.unusedVariables false

  example : uncurryN 3 (λ i j k : Nat => i + j) = λ (i,j,k) => i + j := by rfl
  example : uncurryN 2 (λ i j k : Nat => i + j) = λ (i,j) k => i + j := by rfl

  example : curryN 3 (λ ((i,j,k) : Nat×Nat×Nat) => i + j) = (λ i j k : Nat  => i + j) := by rfl
  -- example : curryN 2 (λ ((i,j,k) : Nat×Nat×Nat) => i + j) = (λ (i : Nat) ((j,k) : Nat×Nat) => i + j) := by rfl

end Tests
