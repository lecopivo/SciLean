import SciLean.Mathlib.Data.Enumtype
import SciLean.Data.Idx

namespace SciLean

class FunType (T : Type) (X Y : outParam Type) where
  toFun : T → X → Y

  ext : ∀ f g : T, (∀ x : X, toFun f x = toFun g x) ↔ f = g

namespace FunType

  @[ext]
  theorem fun_ext {T X Y} [FunType T X Y] (f g : T) : (∀ x : X, toFun f x = toFun g x) → f = g := (FunType.ext f g).1

  -- To easily enable function application `f x` for `f : T` provide an instance of HasFunCoe
  class HasFunCoe {X Y} (T : Type) [FunType T X Y] 
  instance [FunType T X Y] [HasFunCoe T] : CoeFun T (λ _ => X → Y) where
    coe := λ f => FunType.toFun f 

  section Example

    variable {T X Y} [FunType T X Y] [HasFunCoe T] (f : T) (x : X)

  end Example

  class HasSet {X Y} (T : Type) [FunType T X Y] where
    set : T → X → Y → T

    toFun_set_eq  : ∀ (x : X) (y : Y) (f : T), toFun (set f x y) x = y
    toFun_set_neq : ∀ (x x' : X) (y : Y) (f : T), x' ≠ x → toFun (set f x y) x' = toFun f x'

  export HasSet (set)

  attribute [simp] HasSet.toFun_set_eq

  class HasIntro {X Y} (T : Type) [FunType T X Y] where
    intro : (X → Y) → T
    
    toFun_intro : ∀ f x, toFun (intro f) x = f x

  export HasIntro (intro)

  attribute [simp] HasIntro.toFun_intro

  unsafe def modifyUnsafe {T X Y} [FunType T X Y] [HasSet T] [Inhabited Y]
    (f : T) (x : X) (g : Y → Y) : T := 
    Id.run do
    let mut f := f
    let y := toFun f x
    -- Reset `f x` to ensure `y` can be modified in place if possible
    -- This is the same trick as in Array.modifyMUnsafe
    -- f := set f x (unsafeCast ())
    f := set f x default
    f := set f x (g y)
    f

  @[implementedBy modifyUnsafe]
  def modify {T X Y} [FunType T X Y] [HasSet T] [Inhabited Y] (f : T) (x : X) (g : Y → Y) : T := 
    set f x (g (toFun f x))

  @[simp]
  theorem toFun_modify_eq [FunType T X Y] [HasSet T] [Inhabited Y] (f : T) (x : X) (g : Y → Y) 
    : toFun (modify f x g) x = g (toFun f x) := by simp[modify]; done

  @[simp]
  theorem toFun_modify_neq [FunType T X Y] [HasSet T] [Inhabited Y] (f : T) (x x' : X) (g : Y → Y) 
    : x' ≠ x → toFun (modify f x g) x' = toFun f x' := by simp[modify]; apply HasSet.toFun_set_neq; done

  def mapIdx [FunType T X Y] [HasSet T] [Enumtype X] [Inhabited Y] (g : X → Y → Y) (f : T) : T := Id.run do
    let mut f := f
    for (x,i) in Enumtype.fullRange X do
      f := modify f x (g x)
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
