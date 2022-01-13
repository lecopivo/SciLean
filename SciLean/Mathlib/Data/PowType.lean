import SciLean.Mathlib.Data.Table

namespace SciLean

class PowType (X : Type) (n : Nat) where
  powType : Type
  intro : (Fin n → X) → powType
  get : powType → Fin n → X
  set : powType → Fin n → X → powType
  ext  : ∀ x y, (∀ i, get x i = get y i) → x = y

-- instance (priority := low) {X} (n : Nat) : PowType X n :=
-- {
--   powType := {a : Array X // a.size = n}
--   intro := λ f => Id.run do
--     let mut x : Array X := Array.mkEmpty n
--     for i in [0:n] do
--       let i := ⟨i, sorry⟩
--       x := x.push (f i)
--     ⟨x, sorry⟩
--   get := λ x i => x.1.get ⟨i.1, sorry⟩
--   set := λ x i xi => ⟨x.1.set ⟨i.1, sorry⟩ xi, sorry⟩
--   ext := sorry
-- }

instance (n : Nat) : PowType Float n := 
{
  powType := {a : FloatArray // a.size = n}
  intro := λ f => Id.run do
    let mut x := FloatArray.mkEmpty n
    for i in [0:n] do
      let i := ⟨i, sorry⟩
      x := x.push (f i)
    ⟨x, sorry⟩
  get := λ x i => x.1.get ⟨i.1, sorry⟩
  set := λ x i xi => ⟨x.1.set ⟨i.1, sorry⟩ xi, sorry⟩
  ext := sorry
}

notation X "^" n => PowType.powType X n

abbrev PowType.powType.get {X n} [PowType X n] (x : X^n) (i : Fin n) : X := PowType.get x i
abbrev PowType.powType.set {X n} [PowType X n] (x : X^n) (i : Fin n) (xi : X) : X^n := PowType.set x i xi

instance {X n} [PowType X n] : Table (X^n) (Fin n) X := 
  ⟨λ x i => x.get i⟩

instance {X n} [PowType X n] : Table.Intro (X^n):= 
  ⟨λ f => PowType.intro f, sorry⟩

-- instance {X} [PowType X 1] : Coe (X^1) X := ⟨λ x => x.get 0⟩

instance {X} [PowType X 0] : Coe (X^(0:Nat)) Unit := ⟨λ x => ()⟩

def PowType.powType.mapIdx {X n} [PowType X n] (x : X^n) (f : Fin n → X → X) : X^n :=
  Id.run do
  let mut x' := x
  for i in [0:n] do
    let i := ⟨i, sorry⟩
    x' := set x' i (f i (get x' i))
  x'

def PowType.powType.map {X n} [PowType X n] (x : X^n) (f : X → X) : X^n := 
  x.mapIdx λ i xi => f xi

def PowType.powType.concat {X n m} [PowType X n] [PowType X m] [PowType X (n+m)] : (X^n) → (X^m) → X^(n+m) :=
  λ x y => PowType.intro λ i => 
    if i < n then
      x.get ⟨i, sorry⟩
    else
      y.get ⟨i.1-n, sorry⟩

def PowType.powType.split {X N} (n : Fin N) [PowType X N] [PowType X n] [PowType X (N-n)] : (X^N) → (X^n) × (X^(N-n)) :=
  λ x => 
    (PowType.intro λ i => x.get ⟨i.1, sorry⟩, 
     PowType.intro λ i => x.get ⟨i.1 + n, sorry⟩)

def List.toPowType {X} (l : List X) [PowType X l.length] : X^l.length :=
  PowType.intro λ i => l.toArray.get ⟨i.1, sorry⟩

syntax "^[" sepBy(term, ", ") "]" : term

macro_rules
  | `(^[ $elems,* ]) => `(List.toPowType [ $elems,* ])

instance {X n} [ToString X] [PowType X n] : ToString (X^n) :=
  ⟨λ x => 
    if n == 0 then
      "^[]"
    else Id.run do
      let mut s : String := "^[" ++ toString (x.get ⟨0, sorry⟩)
      for i in [1:n] do
        s := s ++ ", " ++ toString (x.get ⟨i, sorry⟩)
      s ++ "]"⟩

-- instance {X} (n : Nat) [PowType X n] [Add X] : Add (X^n) :=
--   ⟨λ x y => x.mapIdx λ i xi => xi + y.get i⟩

-- instance {X} (n : Nat) [PowType X n] [Add X] : HAdd X (X^n) (X^n) :=
--   ⟨λ a x => x.map λ xi => a + xi⟩

-- instance {X} (n : Nat) [PowType X n] [Add X] : HAdd (X^n) X (X^n) :=
--   ⟨λ x a => x.map λ xi => xi + a⟩

-- instance {X} (n : Nat) [PowType X n] [Sub X] : Sub (X^n) :=
--   ⟨λ x y => x.mapIdx λ i xi => xi - y.get i⟩

-- instance {X} (n : Nat) [PowType X n] [Mul X] : Mul (X^n) :=
--   ⟨λ x y => x.mapIdx λ i xi => xi * y.get i⟩

-- instance {X} (n : Nat) [PowType X n] [Mul X] : HMul X (X^n) (X^n) :=
--   ⟨λ a x => x.map λ xi => a * xi⟩

-- instance {X} (n : Nat) [PowType X n] [Mul X] : HMul (X^n) X (X^n) :=
--   ⟨λ x a => x.map λ xi => xi * a⟩

-- instance {X} (n : Nat) [PowType X n] [Div X] : Div (X^n) :=
--   ⟨λ x y => x.mapIdx λ i xi => xi / y.get i⟩

-- instance {X} (n : Nat) [PowType X n] [Neg X] : Neg (X^n) :=
--   ⟨λ x => x.map λ xi => - xi⟩

-- instance {X} (n : Nat) [PowType X n] [Zero X] : Zero (Float^n) :=
--   ⟨PowType.intro λ _ => 0⟩

-- instance {X} (n : Nat) [PowType X n] [One X] : One (Float^n) :=
--   ⟨PowType.intro λ _ => 1⟩

def v1 : Float^(3 : Nat) := ^[1.0,2.0,3.0]
def v2 : Float^(3 : Nat) := ^[2.0,3.0,5.0]
def v3 : Float^(3 : Nat) := v1 / v2

#eval (v1.concat v2).split 4

#eval v1[(0 : Fin 3)]

#eval ∑ i, v1[i]
#eval ∑ i, v2[i]
