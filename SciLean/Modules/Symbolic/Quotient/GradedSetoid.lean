module

public import SciLean.Data.Quotient.Setoid

@[expose] public section


namespace SciLean


/-- Setoid where elements are have a reduction level/rank.
    Every equivalence class has exacly one element of bottom(⊥) level.

    Not sure about the name: LeveledSetoid, RankedSetoid, Gradedsetoid?
    -/

class GradedSetoid (α : Type u) (Lvl : outParam (Type v)) [outParam (BoundedLattice Lvl)]
  extends Setoid α, BoundedLattice Lvl where
  OfLevel (a : α) (lvl : Lvl) : Prop

  lvl_order : ∀ (x : α) (l l' : Lvl), OfLevel x l → l ≤ l' → OfLevel x l'
  every_top  : ∀ x : α, OfLevel x ⊤
  unique_bottom : ∀ x y : α, x ≈ y → OfLevel x ⊥ → OfLevel y ⊥ → x = y

/-- Representant of GradedSetoid with upper bound on the reduction level/rank -/
structure GradedSetoid.Repr (α : Type u) {Lvl : Type v} [BoundedLattice Lvl] [GradedSetoid α Lvl] (maxLvl : Lvl) where
  val : α
  lvl : Lvl
  of_lvl : OfLevel val lvl
  lvl_le_maxLvl : lvl ≤ maxLvl

instance instSetoidGradedSetoidRepr (α : Type u) {Lvl : Type v} [BoundedLattice Lvl] [GradedSetoid α Lvl] (maxLvl : Lvl)
  : Setoid (GradedSetoid.Repr α maxLvl) where
  r x y := x.1 ≈ y.1
  iseqv := ⟨fun _ => Setoid.refl _, Setoid.symm, Setoid.trans⟩

class GradedSetoid.Morphism {α : Type u} {β : Type v} {Lvl : Type w} [BoundedLattice Lvl] [GradedSetoid α Lvl] [GradedSetoid β Lvl]
  (f : α → β) extends Setoid.Morphism f : Prop where
  preserves_level : ∀ a lvl, OfLevel a lvl → OfLevel (f a) lvl

class GradedSetoid.Morphism₂ {α : Type u} {β : Type v} {γ : Type w} {Lvl : Type u₁} [BoundedLattice Lvl] [GradedSetoid α Lvl] [GradedSetoid β Lvl] [GradedSetoid γ Lvl]
  (f : α → β → γ) extends Setoid.Morphism₂ f : Prop where
  preserves_level : ∀ a b lvl, OfLevel a lvl → OfLevel b lvl → OfLevel (f a b) lvl

namespace GradedSetoid

  variable {Lvl : Type v} [BoundedLattice Lvl]  [∀ l l' : Lvl, Decidable (l ≤ l')]

  class Reduce (α : Type u) (lvl : Lvl) [GradedSetoid α Lvl] where
    reduce : α → α
    reduce_sound : ∀ a, reduce a ≈ a
    reduce_lvl   : ∀ a : α, OfLevel (reduce a) lvl

  instance (α : Type u) [GradedSetoid α Lvl] : Reduce α ⊤ where
    reduce := id
    reduce_sound := sorry_proof
    reduce_lvl   := sorry_proof

  variable {α : Type u} [GradedSetoid α Lvl]

  instance : Setoid.Morphism (λ a : GradedSetoid.Repr α lvl => a.1) := ⟨fun _ _ h => h⟩

  def reduceToLvl (lvl : Lvl) [Reduce α lvl] (a : α) : GradedSetoid.Repr α lvl :=
    ⟨Reduce.reduce lvl a, lvl, Reduce.reduce_lvl a, le_refl _⟩

  instance (lvl : Lvl) [Reduce α lvl] : Setoid.Morphism (λ a : α => reduceToLvl lvl a) :=
    ⟨fun a a' h => show Reduce.reduce lvl a ≈ Reduce.reduce lvl a' from
      Setoid.trans (Reduce.reduce_sound a) (Setoid.trans h (Setoid.symm (Reduce.reduce_sound a')))⟩

end GradedSetoid

namespace GradedSetoid.Repr

  variable {α : Type u} {Lvl : Type v} [BoundedLattice Lvl] [GradedSetoid α Lvl] [∀ l l' : Lvl, Decidable (l ≤ l')]

  def reduce (lvl : Lvl) [Reduce α (lvl ⊓ maxLvl)] (a : GradedSetoid.Repr α maxLvl) : GradedSetoid.Repr α maxLvl :=
    if a.lvl ≤ lvl then
      a
    else
      -- We have to include `maxLvl` to guarantee that the reduction is at least maxLvl
      ⟨Reduce.reduce (lvl ⊓ maxLvl) a.1, (lvl ⊓ maxLvl), Reduce.reduce_lvl a.1, sorry_proof⟩

  instance (lvl : Lvl) [Reduce α (lvl ⊓ maxLvl)]
    : Setoid.Morphism (λ (a : GradedSetoid.Repr α maxLvl) => a.reduce lvl) :=
    have key : ∀ b : GradedSetoid.Repr α maxLvl, (b.reduce lvl).1 ≈ b.1 := by
      intro b; unfold reduce; split
      · exact Setoid.refl _
      · exact Reduce.reduce_sound _
    ⟨fun a a' h => show (a.reduce lvl).1 ≈ (a'.reduce lvl).1 from
      Setoid.trans (key a) (Setoid.trans h (Setoid.symm (key a')))⟩

  abbrev normalize [inst : Reduce α ⊥] (a : GradedSetoid.Repr α maxLvl) : GradedSetoid.Repr α maxLvl :=
    have h : ⊥ = (⊥ ⊓ maxLvl : Lvl) := sorry_proof
    have : Reduce α (⊥ ⊓ maxLvl) := h ▸ inst
    a.reduce ⊥

end GradedSetoid.Repr

namespace GradedSetoid.Morphism

  variable {Lvl : Type u'} [BoundedLattice Lvl] [∀ l l' : Lvl, Decidable (l ≤ l')]
  variable {α : Type u} [GradedSetoid α Lvl]
  variable {β : Type v} [GradedSetoid β Lvl]
  variable {γ : Type w} [GradedSetoid γ Lvl]

  instance id_is_mor : Morphism (λ x : α => x) where
    preserves_level := by simp

  instance comp_is_mor (f : β → γ) [Morphism f] (g : α → β) [Morphism g]
    : Morphism (λ x : α => f (g x)) where
    preserves_level := fun a l h => Morphism.preserves_level (f := f) _ l (Morphism.preserves_level (f := g) a l h)

  instance scomb_is_mor (f : α → β → γ) [Morphism₂ f] (g : α → β) [Morphism g]
    : Morphism (λ x : α => f x (g x)) where
    preserves_level := fun a l h => Morphism₂.preserves_level (f := f) a _ l h (Morphism.preserves_level (f := g) a l h)


end GradedSetoid.Morphism


inductive TwoLevel | any | canonical
deriving DecidableEq

instance : LE TwoLevel where
  le x y := match x, y with
            | .any, .canonical => False
            | _, _ => True

instance : LT TwoLevel where
  lt x y := match x, y with
            | .canonical, .any => True
            | _, _ => False

instance : DecidableRel (. ≤ . : TwoLevel → TwoLevel → Prop) :=
  λ x y => match x, y with
           | .any, .canonical => isFalse (by simp[LE.le]; done)
           | .any, .any | .canonical, .any | .canonical, .canonical => isTrue trivial

instance : DecidableRel (. < . : TwoLevel → TwoLevel → Prop) :=
  λ x y => match x, y with
           | .canonical, .any => isTrue (by simp[LT.lt]; done)
           | .any, .any | .any, .canonical | .canonical, .canonical => isFalse nofun

instance : LinearOrder TwoLevel where
  le_refl := by intro a; cases a <;> simp [LE.le]
  le_trans := by intro a b c; cases a <;> cases b <;> cases c <;> simp [LE.le]
  lt_iff_le_not_le := by intro a b; cases a <;> cases b <;> simp [LE.le, LT.lt]
  le_antisymm := by intro a b; cases a <;> cases b <;> simp [LE.le]
  le_total := by intro a b; cases a <;> cases b <;> simp [LE.le]
  decidable_eq := by infer_instance
  decidable_le := by infer_instance
  decidable_lt := by infer_instance

instance : GreatestLowerBound TwoLevel where
  glb x y := match x, y with
             | .canonical, _ => .canonical
             | _, .canonical => .canonical
             | .any, .any => .any

instance : LowestUpperBound TwoLevel where
  lub x y := match x, y with
             | .any, _ => .any
             | _, .any => .any
             | .canonical, .canonical => .canonical

instance : GreatestElement TwoLevel := ⟨.any⟩
instance : LowestElement TwoLevel := ⟨.canonical⟩

instance : BoundedLattice TwoLevel where
  le_bottom := sorry_proof
  le_top    := sorry_proof
