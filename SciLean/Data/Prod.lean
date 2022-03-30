import SciLean.Operators

----------------------------------------------------------------------

class Prod.Get (X : Type) (i : Nat) where
  {T : Type}
  geti : X → T

attribute [reducible] Prod.Get.T Prod.Get.geti

@[reducible]
instance (priority := low) : Prod.Get X 0 := ⟨λ x => x⟩

@[reducible]
instance : Prod.Get (X×Y) 0 := ⟨λ x => x.fst⟩ -- `λ (x,y) => x` causes some trouble while infering IsSmooth

@[reducible]
instance [pg : Prod.Get Y n] : Prod.Get (X×Y) (n+1) := ⟨λ x => pg.geti x.snd⟩ -- `λ (x,y) => pg.geti y` causes some trouble while infering IsSmooth

abbrev Prod.get {X Y} (i : Nat) [pg : Prod.Get (X×Y) i] (x : X×Y) := pg.geti x
abbrev Prod.getOp {X Y} (idx : Nat) [pg : Prod.Get (X×Y) idx] (self : X×Y) := pg.geti self

----------------------------------------------------------------------

class Prod.Set (X : Type) (i : Nat) where
  {T : Type}
  seti : X → T → X

attribute [reducible] Prod.Set.T Prod.Set.seti

@[reducible]
instance (priority := low) : Prod.Set X 0 := ⟨λ x x₀ => x₀⟩

@[reducible]
instance : Prod.Set (X×Y) 0 := ⟨λ (x,y) x₀ => (x₀,y)⟩

@[reducible]
instance [pg : Prod.Set Y n] : Prod.Set (X×Y) (n+1) := ⟨λ (x,y) y₀ => (x, pg.seti y y₀)⟩

abbrev Prod.set {X Y} (i : Nat) [pg : Prod.Set (X×Y) i] (x : X×Y) (xi) := pg.seti x xi

----------------------------------------------------------------------

class Prod.Uncurry (n : Nat) (F : Type) where
  {Y : Type}
  {Xs : Type}
  uncurry : F → Xs → Y

attribute [reducible] Prod.Uncurry.Y Prod.Uncurry.Xs Prod.Uncurry.uncurry

@[reducible]
instance (priority := low) {X Y : Type} : Prod.Uncurry 1 (X→Y) where
  uncurry := λ (f : X → Y) (x : X) => f x

@[reducible]
instance {X Y : Type} [c : Prod.Uncurry n Y] : Prod.Uncurry (n+1) (X→Y) where
  Xs := X×c.Xs
  Y := c.Y
  uncurry := λ (f : X → Y) ((x,xs) : X×c.Xs) => c.uncurry (f x) xs

abbrev huncurry (n : Nat) (f : F) [Prod.Uncurry n F] := Prod.Uncurry.uncurry (n:=n) f

----------------------------------------------------------------------

class Prod.Curry (n : Nat) (Xs : Type) (Y : Type) where
  {F : Type}
  curry : (Xs → Y) → F

attribute [reducible] Prod.Uncurry.Y Prod.Uncurry.Xs Prod.Uncurry.uncurry

@[reducible]
instance (priority := low) : Prod.Curry 1 X Y where
  curry := λ (f : X → Y) => f

@[reducible]
instance {X Y Z : Type} [c : Prod.Curry n Y Z] : Prod.Curry (n+1) (X×Y) Z where
  curry := λ (f : X×Y → Z) => (λ (x : X) => c.curry (λ y => f (x,y)))

abbrev hcurry {Xs Y : Type} (n : Nat) (f : Xs → Y) [Prod.Curry n Xs Y] := Prod.Curry.curry (n:=n) f

----------------------------------------------------------------------

example : (42,3.14159,"hello").get 0 = 42 := by rfl
example : (42,3.14159,"hello")[0] = 42 := by rfl
example : (42,3.14159,"hello")[1] = 3.14159 := by rfl
example : (42,3.14159,"hello")[2] = "hello" := by rfl

example : (42,3.14159,"hello").set 2 "world" = (42,3.14159,"world") := by rfl

example : huncurry 3 (λ i j k : Nat => i + j) = λ (i,j,k) => i + j := by rfl
example : huncurry 2 (λ i j k : Nat => i + j) = λ (i,j) k => i + j := by rfl

example : hcurry 3 (λ ((i,j,k) : Nat×Nat×Nat) => i + j) = (λ i j k => i + j) := by rfl
example : hcurry 2 (λ ((i,j,k) : Nat×Nat×Nat) => i + j) = (λ i (j,k) => i + j) := by rfl
