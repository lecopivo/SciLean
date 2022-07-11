import SciLean.Mathlib.Data.Enumtype
import SciLean.Data.Idx

namespace SciLean

class SetElem (Cont : Type u) (Idx : Type v) (Elem : outParam (Type w)) (Dom : outParam (Cont → Idx → Prop)) where
  setElem (xs : Cont) (i : Idx) (x : Elem) (h : Dom xs i) : Cont

def setElem {Cont Idx Elem} [SetElem Cont Idx Elem (λ _ _ => True)] 
  (x : Cont) (i : Idx) (xi : Elem) : Cont := SetElem.setElem x i xi True.intro

def setElem' {Cont Idx Elem Dom} [SetElem Cont Idx Elem Dom] 
  (x : Cont) (i : Idx) (xi : Elem) (h : Dom x i) : Cont := SetElem.setElem x i xi h

macro_rules
| `(doElem| $x:ident[ $i:term ] := $xi) => `(doElem| $x:ident := setElem ($x:ident) $i $xi)

class FunType (Cont : Type u) (Idx : outParam (Type v)) (Elem : outParam (Type w)) 
  extends GetElem Cont Idx Elem (λ _ _ => True),
          SetElem Cont Idx Elem (λ _ _ => True)
  where

  ext : ∀ x y : Cont, 
    (∀ i : Idx, getElem x i True.intro = getElem y i True.intro) ↔ x = y

  -- recover set element
  getElem_setElem_eq : ∀ (i : Idx) (val : Elem) (x : Cont),
    getElem (setElem x i val True.intro) i True.intro = val

  -- settting element do not alter other elements
  getElem_setElem_neq : ∀ (i j : Idx) (val : Elem) (x : Cont),
    i ≠ j → (setElem x i val True.intro)[j] = x[j]

namespace FunType

  @[ext]
  theorem ext_simp {Cont Idx Elem} [FunType Cont Idx Elem] (x y : Cont)
    : (∀ i : Idx, x[i] = y[i]) → x = y
  := (FunType.ext x y).1

  @[simp]
  theorem fun_getElem_setElem_eq {Cont Idx Elem} [FunType Cont Idx Elem]
    (x : Cont) (i : Idx) (val : Elem)
    : (setElem x i val)[i] = val
  := by simp[setElem]; apply FunType.getElem_setElem_eq; done

  class HasIntro {X Y} (T : Type) [FunType T X Y] where
    intro : (X → Y) → T
    
    toFun_intro : ∀ f i, (intro f)[i] = f i

  export HasIntro (intro)

  attribute [simp] HasIntro.toFun_intro

  unsafe def modifyUnsafe {T X Y} [FunType T X Y] [Inhabited Y]
    (f : T) (x : X) (g : Y → Y) : T := Id.run do
    let mut f := f
    let y := f[x]
    -- Reset `f x` to ensure `y` can be modified in place if possible
    -- This is the same trick as in Array.modifyMUnsafe
    -- f := set f x (unsafeCast ())
    f[x] := default
    f[x] := (g y)
    f

  @[implementedBy modifyUnsafe]
  def modify {T X Y} [FunType T X Y] [Inhabited Y] (f : T) (x : X) (g : Y → Y) : T := 
    setElem f x (g f[x])
    
  @[simp]
  theorem getElem_modify_eq [FunType T X Y] [Inhabited Y] (f : T) (x : X) (g : Y → Y) 
    : (modify f x g)[x] = g f[x] := by simp[modify]; done

  @[simp]
  theorem getElem_modify_neq [FunType T X Y] [Inhabited Y] (f : T) (x x' : X) (g : Y → Y) 
    : x ≠ x' → (modify f x g)[x'] = f[x'] := by simp[modify, setElem]; apply FunType.getElem_setElem_neq; done

  def mapIdx [FunType T X Y] [Enumtype X] [Inhabited Y] (g : X → Y → Y) (f : T) : T := Id.run do
    let mut f := f
    for (i,_) in Enumtype.fullRange X do
      f := modify f i (g i)
    f

  @[simp]
  theorem toFun_mapIdx [FunType T X Y] [HasSet T] [Enumtype X] [Inhabited Y] (g : X → Y → Y) (f : T) (x : X) 
    : toFun (mapIdx g f) x = g x (toFun f x) := sorry

  def map [FunType T X Y] [HasSet T] [Enumtype X] [Inhabited Y] (g : Y → Y) (f : T) : T := Id.run do
    let mut f := f
    for (x,i) in Enumtype.fullRange X do
      f := modify f x g
    f
    
  @[simp]
  theorem toFun_map [FunType T X Y] [HasSet T] [Enumtype X] [Inhabited Y] (g : Y → Y) (f : T) (x : X) 
    : toFun (map g f) x = g (toFun f x) := sorry
  
  section Operations

    variable {T X Y} [FunType T X Y] [HasSet T] [HasIntro T] [Enumtype X] [Inhabited Y]

    instance [Add Y] : Add T := ⟨λ f g => mapIdx (λ x fx => fx + toFun g x) f⟩
    instance [Sub Y] : Sub T := ⟨λ f g => mapIdx (λ x fx => fx - toFun g x) f⟩
    instance [Mul Y] : Mul T := ⟨λ f g => mapIdx (λ x fx => fx * toFun g x) f⟩
    instance [Div Y] : Div T := ⟨λ f g => mapIdx (λ x fx => fx / toFun g x) f⟩

    instance {R} [HMul R Y Y] : HMul R T T := ⟨λ r f => map (λ fx => r*(fx : Y)) f⟩

    instance [Neg Y] : Neg T := ⟨λ f => map (λ fx => -(fx : Y)) f⟩
    instance [Inv Y] : Inv T := ⟨λ f => map (λ fx => (fx : Y)⁻¹) f⟩

    instance [One Y]  : One T  := ⟨intro λ _ => 1⟩
    instance [Zero Y] : Zero T := ⟨intro λ _ => 0⟩

    instance [LT Y] : LT T := ⟨λ f g => ∀ x, toFun f x < toFun g x⟩ 
    instance [LE Y] : LE T := ⟨λ f g => ∀ x, toFun f x ≤ toFun g x⟩

    instance [DecidableEq Y] : DecidableEq T := 
      λ f g => Id.run do
        let mut eq : Bool := true
        for (x,_) in Enumtype.fullRange X do
          if toFun f x ≠ toFun g x then
            eq := false
            break
        if eq then isTrue sorry else isFalse sorry

    instance [LT Y] [∀ x y : Y, Decidable (x < y)] (f g : T) : Decidable (f < g) := Id.run do
      let mut lt : Bool := true
      for (x,_) in Enumtype.fullRange X do
        if ¬(toFun f x < toFun g x) then
          lt := false
          break
      if lt then isTrue sorry else isFalse sorry

    instance [LE Y] [∀ x y : Y, Decidable (x ≤ y)] (f g : T) : Decidable (f ≤ g) := Id.run do
      let mut le : Bool := true
      for (x,_) in Enumtype.fullRange X do
        if ¬(toFun f x ≤ toFun g x) then
          le := false
          break
      if le then isTrue sorry else isFalse sorry

  end Operations

