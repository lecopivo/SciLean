import SciLean.Mathlib.Data.Enumtype
import Mathlib.Algebra.Group.Defs
import SciLean.Data.Idx

namespace SciLean

class PowType (X : Type) where
  powType : USize → Type
  intro {n} : (Idx n → X) → powType n
  get {n} : powType n → Idx n → X
  set {n} : powType n → Idx n → X → powType n
  ext {n} : ∀ x y : powType n, (∀ i, get x i = get y i) → x = y

notation X "^" n => PowType.powType X n

namespace PowType.powType

  variable {X} {n : USize} [PowType X]

  abbrev set (x : X^n) (i : Idx n) (xi : X) : X^n := PowType.set x i xi

  def getOp (self : X^n) (idx : Idx n) : X := PowType.get self idx
 
  -- @[simp]
  -- theorem get_to_getop (x : X^n) (i : Idx n) : x.get i = x[i] := by simp[getOp] done

  @[simp]
  theorem intro_getop (f : Idx n → X) (i : Idx n) : (intro f)[i] = f i := by sorry

  def modify {X} {n : USize} [PowType X] [Inhabited X] (x : X^n) (i : Idx n) (f : X → X) : X^n := Id.run do
    let mut x := x
    let xi := x[i]
    -- Reset x[i] to ensure `xi` be modified in place if possible
    -- I do not thin we can take the same liberty as Array.modifyMUnsafe and assign `unsafeCast ()`
    x := x.set i default
    x := x.set i (f xi)
    x

  def mapIdx {X} {n : USize} [PowType X] (x : X^n) (f : Idx n → X → X) : X^n :=
    Id.run do
    let mut x' := x
    for i in Idx.all do
      x' := set x' i (f i (get x' i))
    x'

  def map {X} {n : USize} [PowType X] (x : X^n) (f : X → X) : X^n := 
    x.mapIdx λ i xi => f xi


  section Operations

    variable {X} {n : USize} [PowType X]

    instance [Add X] : Add (X^n) := ⟨λ x y => x.mapIdx λ i xi => xi + y[i]⟩
    instance [Sub X] : Sub (X^n) := ⟨λ x y => x.mapIdx λ i xi => xi - y[i]⟩
    instance [Mul X] : Mul (X^n) := ⟨λ x y => x.mapIdx λ i xi => xi * y[i]⟩
    instance [Div X] : Div (X^n) := ⟨λ x y => x.mapIdx λ i xi => xi / y[i]⟩

    instance {R} [HMul R X X] : HMul R (X^n) (X^n) := ⟨λ r x => x.map λ xi => r*xi⟩

    instance [Neg X] : Neg (X^n) := ⟨λ x => x.map λ xi => -xi⟩
    instance [Inv X] : Inv (X^n) := ⟨λ x => x.map λ xi => xi⁻¹⟩

    instance [One X]  : One (X^n)  := ⟨intro λ _ => 1⟩
    instance [Zero X] : Zero (X^n) := ⟨intro λ _ => 0⟩

    instance [LT X] : LT (X^n) := ⟨λ u v => ∀ i, u[i] < v[i]⟩ 
    instance [LE X] : LE (X^n) := ⟨λ u v => ∀ i, u[i] ≤ v[i]⟩ 

    instance [DecidableEq X] : DecidableEq (X^n) := 
      λ u v => Id.run do
        let mut eq : Bool := true
        for i in Idx.all do
          if u[i] ≠ v[i] then
            eq := false
            break
        if eq then isTrue sorry else isFalse sorry

    instance [LT X] [∀ x y : X, Decidable (x < y)] (u v : X^n) : Decidable (u < v) := Id.run do
      let mut eq : Bool := true
      for i in Idx.all do
        if ¬(u[i] < v[i]) then
          eq := false
          break
      if eq then isTrue sorry else isFalse sorry

    instance [LE X] [∀ x y : X, Decidable (x ≤ y)] (u v : X^n) : Decidable (u ≤ v) := Id.run do
      let mut eq : Bool := true
      for i in Idx.all do
        if ¬(u[i] ≤ v[i]) then
          eq := false
          break
      if eq then isTrue sorry else isFalse sorry
 
  end Operations

  def concat {X} {n m : USize} [PowType X] : (X^n) → (X^m) → X^(n+m) :=
    λ x y => PowType.intro λ i => 
      if i.1 < n then
        x[⟨i.1, sorry⟩]
      else
        y[⟨i.1-n, sorry⟩]

  def split {X} {N : USize} (n : Idx N) [PowType X] : (X^N) → (X^n.1) × (X^(N-n.1)) :=
    λ x => 
      (PowType.intro λ i => x[⟨i.1, sorry⟩], 
       PowType.intro λ i => x[⟨i.1 + n.1, sorry⟩])

  instance {X} {n : USize} [ToString X] [PowType X] : ToString (X^n) :=
    ⟨λ x => 
      if n == 0 then
        "^[]"
      else Id.run do
        let mut s : String := "^[" ++ toString (x[⟨0, sorry⟩])
        for i in Idx.all do
          if i.1 ≠ 0 then
            s := s ++ ", " ++ toString (x[i])
        s ++ "]"⟩

end PowType.powType

def List.toPowType {X} (l : List X) [PowType X] : X^l.length.toUSize :=
  PowType.intro λ i => l.toArray.get ⟨i.1.toNat, sorry⟩

syntax "^[" sepBy(term, ", ") "]" : term

macro_rules
  | `(^[ $elems,* ]) => `(List.toPowType [ $elems,* ])

namespace PowType

  @[simp]
  theorem sum_intro {ι} [Enumtype ι]
    [PowType α] [Add α] [Zero α] [Zero (Idx n → α)] [Add (Idx n → α)]
    (f : ι → Idx n → α) 
    : (∑ i, PowType.intro (f i)) = (PowType.intro (∑ i, f i))
    := 
  by
    admit

  @[simp]
  theorem add_intro 
    (f g : Idx n → α) [PowType α] [Add α]
    : 
      (PowType.intro f)  + (PowType.intro g)
      = 
      (PowType.intro λ i => f i + g i)
    := 
  by
    admit

  @[simp]
  theorem sub_intro 
    (f g : Idx n → α) [PowType α] [Sub α]
    : 
      (PowType.intro f)  - (PowType.intro g)
      = 
      (PowType.intro λ i => f i - g i)
    := 
  by
    admit


  @[simp]
  theorem hmul_intro 
    (f : Idx n → α) [PowType α] [HMul β α α] (b : β)
    :
      b * (PowType.intro f) = PowType.intro λ i => b * f i
    := 
  by 
    admit
