import SciLean.Operators

namespace SciLean

variable  {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]


structure HArray (Ts : List Type) where
  data : Array (Sigma (λ T : Type => T))
  h_len : Ts.length = data.size
  typed : ∀ i : Fin Ts.length, (data.get (h_len ▸ i)).1 = Ts.get i

namespace HArray

  variable {n} {Ts : List Type}

  def get (u : HArray Ts) (i : Fin Ts.length) : Ts.get i
    := u.typed i ▸ (u.data.get (u.h_len ▸ i)).2

  def getOp (self : HArray Ts) (idx : Fin Ts.length) : Ts.get idx
    := self.typed idx ▸ (self.data.get (self.h_len ▸ idx)).2

  def set (u : HArray Ts) (i : Fin Ts.length) (x : Ts.get i) : HArray Ts
    := ⟨u.data.set (u.h_len ▸ i) (⟨_, x⟩), sorry, sorry⟩

end HArray

class HCurryType (n : Nat) (F : Type) where
  Xs : List Type
  Y  : Type

attribute [reducible] HCurryType.Xs HCurryType.Y

@[reducible]
instance : HCurryType 0 Y where
  Xs := []
  Y := Y

@[reducible]
instance {X Y : Type} [t : HCurryType n Y] : HCurryType (n + 1) (X → Y) where
  Xs := X::t.Xs
  Y := t.Y

class HCurry (i : Nat) (Xs' Xs : List Type) (Y : Type) where
  index_valid : Xs'.length + i = Xs.length
  types_valid : ∀ j, i + j < Xs.length → Xs'.get ⟨j, sorry⟩ = Xs.get ⟨i + j, sorry⟩
  F : Type
  uncurry : F → (HArray Xs → Y)

attribute [reducible] HCurry.F HCurry.uncurry

@[reducible]
instance (Xs : List Type) (Y : Type) : HCurry n [] Xs Y where
  index_valid := sorry
  types_valid := sorry
  F := Y
  uncurry := λ y xs => y

@[reducible]
instance [c : HCurry (i+1) (Xs') Xs Y] : HCurry (i) (X'::Xs') Xs Y where
  index_valid := sorry
  types_valid := sorry
  F := X' → c.F
  uncurry := λ f xs => 
    let h : (Xs.get ⟨i,sorry⟩ = X') := sorry
    let xi : X' := (h ▸ xs[⟨i,sorry⟩])
    c.uncurry (f xi) xs

def huncurry (n : Nat) {F : Type} [HCurryType n F] 
  [ci : HCurry 0 (HCurryType.Xs n F) (HCurryType.Xs n F) (HCurryType.Y n F)] 
  (f : F) := 
    let h : F = ci.F := sorry
    ci.uncurry (h ▸ f)


example : huncurry 3 (λ (i j k : Nat) => i + j) 
          = 
          λ xs => xs[#0] + xs[#1] := 
by rfl

example : huncurry 2 (λ (i j k : Nat) => i + j) 
          = 
          λ xs k => xs[#0] + xs[#1] := 
by rfl 

