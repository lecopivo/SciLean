import SciLean.Operators


-- class ProdTypes (X : Type) (Xs : outParam (List Type)) --  where
  -- get (x : X) (i : Fin Xs.length) : Xs.get i
  -- set (x : X) (i : Fin Xs.length) (xi : Xs.get i) : X

class ProdGet (X : Type) (i : Nat) where
  {T : Type}
  geti : X → T

attribute [reducible] ProdGet.T ProdGet.geti

-- instance ProdGet
@[reducible]
instance (priority := low) : ProdGet X 0 := ⟨λ x => x⟩

@[reducible]
instance : ProdGet (X×Y) 0 := ⟨λ (x,y) => x⟩

@[reducible]
instance [pg : ProdGet Y n] : ProdGet (X×Y) (n+1) := ⟨λ (x,y) => pg.geti y⟩

class ProdSet (X : Type) (i : Nat) where
  {T : Type}
  seti : X → T → X

attribute [reducible] ProdSet.T ProdSet.seti

@[reducible]
instance (priority := low) : ProdSet X 0 := ⟨λ x x₀ => x₀⟩

@[reducible]
instance : ProdSet (X×Y) 0 := ⟨λ (x,y) x₀ => (x₀,y)⟩

@[reducible]
instance [pg : ProdSet Y n] : ProdSet (X×Y) (n+1) := ⟨λ (x,y) y₀ => (x, pg.seti y y₀)⟩

-- abbrev prodTypes (X) {Xs} [ProdTypes X Xs] := Xs
-- abbrev prodSize (X) {Xs} [ProdTypes X Xs] := Xs.length

-- instance : ProdTypes X [X] := ⟨⟩
-- instance {Y Ys} [ProdTypes Y Ys] : ProdTypes (X×Y) (Xs := X::(prodTypes Y)) := ⟨⟩

-- def Prod.size {X Y} {Xs} [ProdTypes (X×Y) Xs] (x : X×Y) := Xs.length

abbrev Prod.get {X Y} (i : Nat) [pg : ProdGet (X×Y) i] (x : X×Y) := pg.geti x
abbrev Prod.set {X Y} (i : Nat) [pg : ProdSet (X×Y) i] (x : X×Y) (xi) := pg.seti x xi

abbrev Prod.getOp {X Y} (idx : Nat) [pg : ProdGet (X×Y) idx] (self : X×Y) := pg.geti self

-- def Prod.getOp {X Y} (self : X×Y) (idx : Nat) [pg : ProdGet (X×Y) i] := pg.geti self

-- #eval (2,3,"asdf").size
#eval (2,3,"asdf").get 2
#eval (2,3,"asdf").get 0
#eval (2,3,"asdf")[0]
#eval ((2,3,"asdf").set 2 ("aaa"))

namespace SciLean

variable  {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]

example : IsSmooth (λ x : X×Y => x.get 0) := by infer_instance 
example : IsSmooth (λ x : X×Y => x.get 1) := by infer_instance 

example : IsSmooth (λ x : X×Y×Z => x.get 0) := by infer_instance
example : IsSmooth (λ x : X×Y×Z => x.get 1) := by infer_instance 
example : IsSmooth (λ x : X×Y×Z => x.get 2) := by infer_instance 

example : IsSmooth (λ x : X×Y×Z×W => x.get 3) := by infer_instance 
example : IsSmooth (λ x : X×Y×Z×W => x.get 1) := by infer_instance 

variable {X Y Z : Type}
#check (λ x : X×Y×Z => x.get 2)


-- attribute [reducible] ProdInterface.Xs ProdInterface.get

@[reducible]
instance (priority := low) : ProdInterface X where
  Xs := [X]
  get := λ x i => 
    let h : X = [X].get i := sorry
    (h ▸ x)
  set := λ x i xi =>
    let h : [X].get i = X := sorry
    (h ▸ xi)

open ProdInterface in
@[reducible]
instance [ProdInterface X] [ProdInterface Y] : ProdInterface (X×Y) where
  Xs := List.append (Xs X) (Xs Y)
  get := λ (x,y) i => 
    if h : i.1 < (Xs X).length then
      let i' : Fin (Xs X).length := ⟨i.1, h⟩ 
      let h : (Xs X).get i' = List.get (List.append (Xs X) (Xs Y)) i := sorry
      (h ▸ get x i')
    else 
      let i' : Fin (Xs Y).length := ⟨i.1 - (Xs X).length, sorry⟩
      let h : (Xs Y).get i' = List.get (List.append (Xs X) (Xs Y)) i := sorry
      (h ▸ get y i')
  set := sorry --λ x i xi => sorry


abbrev Prod.get [inst : ProdInterface (X×Y)] (p : X×Y) (i) := ProdInterface.get (self := inst) i

def x := (2, 1.0, "hello")

#eval (x.get ⟨0,sorry⟩)
  
-- structure HArray (Ts : List Type) where
--   data : Array (Sigma (λ T : Type => T))
--   h_len : Ts.length = data.size
--   typed : ∀ i : Fin Ts.length, (data.get (h_len ▸ i)).1 = Ts.get i

-- namespace HArray

--   variable {n} {Ts : List Type}

--   def get (u : HArray Ts) (i : Fin Ts.length) : Ts.get i
--     := u.typed i ▸ (u.data.get (u.h_len ▸ i)).2

--   def getOp (self : HArray Ts) (idx : Fin Ts.length) : Ts.get idx
--     := self.typed idx ▸ (self.data.get (self.h_len ▸ idx)).2

--   def set (u : HArray Ts) (i : Fin Ts.length) (x : Ts.get i) : HArray Ts
--     := ⟨u.data.set (u.h_len ▸ i) (⟨_, x⟩), sorry, sorry⟩

--   instance [Zero T] : Zero (Fin 1 → T) := ⟨λ _ => 0⟩
--   instance [Zero T] [z : Zero $ (i : Fin Ts.length) → Ts.get i] : Zero $ (i : Fin (T::Ts).length) → (T::Ts).get i := ⟨λ _ => 0⟩
--   instance [Zero T] [Zero (HArray Ts)] : Zero (HArray (T::Ts)) := ⟨⟨#[Sigma.mk T (0:T)].append ((0 : HArray Ts).1), sorry, sorry⟩⟩

--   example : Zero (HArray [Nat, Int, Nat]) := by infer_instance

-- end HArray

-- class HCurryType (n : Nat) (F : Type) where
--   Xs : List Type
--   Y  : Type

-- attribute [reducible] HCurryType.Xs HCurryType.Y

-- @[reducible]
-- instance : HCurryType 0 Y where
--   Xs := []
--   Y := Y

-- @[reducible]
-- instance {X Y : Type} [t : HCurryType n Y] : HCurryType (n + 1) (X → Y) where
--   Xs := X::t.Xs
--   Y := t.Y

-- class HCurry (i : Nat) (Xs' Xs : List Type) (Y : Type) where
--   index_valid : Xs'.length + i = Xs.length
--   types_valid : ∀ j, i + j < Xs.length → Xs'.get ⟨j, sorry⟩ = Xs.get ⟨i + j, sorry⟩
--   F : Type
--   uncurry : F → (HArray Xs → Y)

-- attribute [reducible] HCurry.F HCurry.uncurry

-- @[reducible]
-- instance (Xs : List Type) (Y : Type) : HCurry n [] Xs Y where
--   index_valid := sorry
--   types_valid := sorry
--   F := Y
--   uncurry := λ y xs => y

-- @[reducible]
-- instance [c : HCurry (i+1) (Xs') Xs Y] : HCurry (i) (X'::Xs') Xs Y where
--   index_valid := sorry
--   types_valid := sorry
--   F := X' → c.F
--   uncurry := λ f xs => 
--     let h : (Xs.get ⟨i,sorry⟩ = X') := sorry
--     let xi : X' := (h ▸ xs[⟨i,sorry⟩])
--     c.uncurry (f xi) xs

-- def huncurry (n : Nat) {F : Type} [HCurryType n F] 
--   [ci : HCurry 0 (HCurryType.Xs n F) (HCurryType.Xs n F) (HCurryType.Y n F)] 
--   (f : F) := 
--     let h : F = ci.F := sorry
--     ci.uncurry (h ▸ f)


-- example : huncurry 3 (λ (i j k : Nat) => i + j) 
--           = 
--           λ xs => xs[#0] + xs[#1] := 
-- by rfl

-- example : huncurry 2 (λ (i j k : Nat) => i + j) 
--           = 
--           λ xs k => xs[#0] + xs[#1] := 
-- by rfl 

