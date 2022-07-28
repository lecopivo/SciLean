-- import SciLean.Mathlib.Data.Enumtype
-- import SciLean.Data.Idx
import SciLean.Core

namespace SciLean

class SetElem (Cont : Type u) (Idx : Type v) (Elem : outParam (Type w)) where
  setElem : (x : Cont) → (i : Idx) → (xi : Elem) → Cont

export SetElem (setElem)

class ModifyElem (Cont : Type u) (Idx : Type v) (Elem : outParam (Type w)) where
  modifyElem : (x : Cont) → (i : Idx) → (Elem → Elem) → Cont

export ModifyElem (modifyElem)

open Lean Parser Term

open TSyntax.Compat

syntax (priority := high+1) atomic(Lean.Parser.Term.ident) noWs "[" term "]" " := " term : doElem
macro_rules
| `(doElem| $x:ident[ $i:term ] := $xi) => do
  let lhs ← `($x[$i])
  -- Do we alias? Does `x[i]` appear on the right hand side too?
  -- For example `x[i] := 2 * x[i]`
  -- In such cases we want to use `modifyElem` instead of `setElem`
  if let .some _ := xi.raw.find? (λ x => lhs.raw == x) then
    let var ← `(y)
    let xi' ← xi.raw.replaceM (λ s => if s == lhs.raw then pure $ .some var else pure $ none)
    let g ← `(λ $var => $xi')
    -- dbg_trace s!"aliasing, new rhs {g.raw.prettyPrint}"
    `(doElem| $x:ident := modifyElem ($x:ident) $i $g)
  else 
    `(doElem| $x:ident := setElem ($x:ident) $i $xi)


class FunType (T : Type) (X Y : outParam Type) extends GetElem T X Y (λ _ _ => True) where
  ext : ∀ f g : T, (∀ x : X, f[x] = g[x]) ↔ f = g

attribute [defaultInstance] FunType.toGetElem

namespace FunType

  @[ext]
  theorem fun_ext {T X Y} [FunType T X Y] (f g : T) : (∀ x : X, f[x] = g[x]) → f = g := (FunType.ext f g).1

  -- -- To easily enable function application `f x` for `f : T` provide an instance of HasFunCoe
  -- class HasFunCoe {X Y} (T : Type) [FunType T X Y] 
  -- instance [FunType T X Y] [HasFunCoe T] : CoeFun T (λ _ => X → Y) where
  --   coe := λ f x => f[x]

  -- section Example

  --   variable {T X Y} [FunType T X Y] [HasFunCoe T] (f : T) (x : X)

  -- end Example

  class HasSet {X Y} (T : Type) [FunType T X Y] extends SetElem T X Y where
    toFun_set_eq  : ∀ (x : X) (y : Y) (f : T), (setElem f x y)[x] = y
    toFun_set_neq : ∀ (x x' : X) (y : Y) (f : T), x' ≠ x → (setElem f x y)[x'] = f[x']

  attribute [defaultInstance] HasSet.toSetElem
  attribute [simp] HasSet.toFun_set_eq

  class HasIntro {X Y} (T : Type) [FunType T X Y] where
    intro : (X → Y) → T
    
    toFun_intro : ∀ f x, (intro f)[x] = f x

  -- export HasIntro (intro)

  abbrev intro {X Y} (T : Type) [FunType T X Y] [HasIntro T] (f : X → Y) : T := HasIntro.intro f

  attribute [simp] HasIntro.toFun_intro

  unsafe def modifyUnsafe {T X Y} [FunType T X Y] [HasSet T]
    (f : T) (x : X) (g : Y → Y) : T := 
    Id.run do
    let mut f := f
    let y := f[x]
    -- Reset `f x` to ensure `y` can be modified in place if possible
    -- This is the same trick as in Array.modifyMUnsafe
    -- Unfortunatelly `unsafeCast ()` does not seem to be working :( 
    -- I could require [Inhabited Y] but that was causing other problems
    -- f[x] := unsafeCast ()
    f[x] := g y
    f

  -- TODO: figure out how to make modifyUnsafe work
  -- @[implementedBy modifyUnsafe]
  @[inline]
  def modify {T X Y} [FunType T X Y] [HasSet T] (f : T) (x : X) (g : Y → Y) : T := 
    setElem f x (g (f[x]))

  instance [FunType T X Y] [HasSet T] : ModifyElem T X Y where
    modifyElem f x g := modify f x g

  @[simp]
  theorem toFun_modify_eq [FunType T X Y] [HasSet T] (f : T) (x : X) (g : Y → Y)
    : (modifyElem f x g)[x] = g f[x] := by simp[modifyElem, modify]; done

  @[simp]
  theorem toFun_modify_neq [FunType T X Y] [HasSet T] (f : T) (x x' : X) (g : Y → Y)
    : x' ≠ x → (modifyElem f x g)[x'] = f[x'] := by simp[modify]; apply HasSet.toFun_set_neq; done

  def mapIdx [FunType T X Y] [HasSet T] [Enumtype X] (g : X → Y → Y) (f : T) : T := Id.run do
    let mut f := f
    for (x,_) in Enumtype.fullRange X do
      -- This notation should correctly handle aliasing 
      -- It should expand to `f := modifyElem f x (g x) True.intro`
      -- This prevent from making copy of `f[x]`
      f[x] := g x f[x]
    f

  @[simp]
  theorem getElem_mapIdx [FunType T X Y] [HasSet T] [Enumtype X] (g : X → Y → Y) (f : T) (x : X) 
    : (mapIdx g f)[x] = g x f[x] := sorry

  def map [FunType T X Y] [HasSet T] [Enumtype X] (g : Y → Y) (f : T) : T := Id.run do
    let mut f := f
    for (x,_) in Enumtype.fullRange X do
      f[x] := g f[x]
    f
    
  @[simp]
  theorem getElem_map [FunType T X Y] [HasSet T] [Enumtype X] (g : Y → Y) (f : T) (x : X) 
    : (map g f)[x] = g f[x] := sorry
  
  section Operations

    variable {T X Y} [FunType T X Y] [HasSet T] [HasIntro T] [Enumtype X] 

    instance [Add Y] : Add T := ⟨λ f g => mapIdx (λ x fx => fx + g[x]) f⟩
    instance [Sub Y] : Sub T := ⟨λ f g => mapIdx (λ x fx => fx - g[x]) f⟩
    instance [Mul Y] : Mul T := ⟨λ f g => mapIdx (λ x fx => fx * g[x]) f⟩
    instance [Div Y] : Div T := ⟨λ f g => mapIdx (λ x fx => fx / g[x]) f⟩

    instance {R} [HMul R Y Y] : HMul R T T := ⟨λ r f => map (λ fx => r*(fx : Y)) f⟩

    instance [Neg Y] : Neg T := ⟨λ f => map (λ fx => -(fx : Y)) f⟩
    instance [Inv Y] : Inv T := ⟨λ f => map (λ fx => (fx : Y)⁻¹) f⟩

    instance [One Y]  : One T  := ⟨intro T λ _ => 1⟩
    instance [Zero Y] : Zero T := ⟨intro T λ _ => 0⟩

    instance [LT Y] : LT T := ⟨λ f g => ∀ x, f[x] < g[x]⟩ 
    instance [LE Y] : LE T := ⟨λ f g => ∀ x, f[x] ≤ g[x]⟩

    instance [DecidableEq Y] : DecidableEq T := 
      λ f g => Id.run do
        let mut eq : Bool := true
        for (x,_) in Enumtype.fullRange X do
          if f[x] ≠ g[x] then
            eq := false
            break
        if eq then isTrue sorry else isFalse sorry

    instance [LT Y] [∀ x y : Y, Decidable (x < y)] (f g : T) : Decidable (f < g) := Id.run do
      let mut lt : Bool := true
      for (x,_) in Enumtype.fullRange X do
        if ¬(f[x] < g[x]) then
          lt := false
          break
      if lt then isTrue sorry else isFalse sorry

    instance [LE Y] [∀ x y : Y, Decidable (x ≤ y)] (f g : T) : Decidable (f ≤ g) := Id.run do
      let mut le : Bool := true
      for (x,_) in Enumtype.fullRange X do
        if ¬(f[x] ≤ g[x]) then
          le := false
          break
      if le then isTrue sorry else isFalse sorry

  end Operations
