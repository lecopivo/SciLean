import SciLean.Data.Quotient.GradedSetoid

namespace SciLean

def GradedQuotient (α : Type u) {Lvl : Type v} [BoundedLattice Lvl] [GradedSetoid α Lvl] (maxLvl : Lvl := ⊤)
  := Quotient (instSetoidGradedSetoidRepr α maxLvl)


namespace GradedQuotient


  variable {α : Type u} {Lvl : Type v} [BoundedLattice Lvl] [inst : GradedSetoid α Lvl] [∀ l l' : Lvl, Decidable (l ≤ l')]

  notation " ⟦ " lvl " | " x " ⟧ " => ⟦GradedSetoid.reduceToLvl lvl x⟧

  noncomputable
  def repr (a : GradedQuotient α maxLvl) : α := (Quotient.repr a).1

  @[simp high]
  theorem repr_quotient (a : GradedQuotient α maxLvl) [GradedSetoid.Reduce α maxLvl]
    : ⟦maxLvl| a.repr⟧ = a
    := sorry_proof

  def ungraded (a : GradedQuotient α maxLvl) := a.liftOn (λ a => ⟦a.1⟧) sorry_proof

  @[simp high]
  theorem repr_ungraded (a : GradedQuotient α maxLvl)
    : ⟦a.repr⟧ = a.ungraded
    := sorry_proof

  noncomputable
  def grepr (a : GradedQuotient α maxLvl) : GradedSetoid.Repr α maxLvl := Quotient.repr a

  @[simp high]
  theorem grepr_quotient (a : GradedQuotient α maxLvl)
    : ⟦a.grepr⟧ = a
    := sorry_proof

  noncomputable
  def lvl (a : GradedQuotient α maxLvl) : Lvl := (Quotient.repr a).2

  def reduce (lvl : Lvl) [GradedSetoid.Reduce α (lvl ⊓ maxLvl)] (a : GradedQuotient α maxLvl) : GradedQuotient α maxLvl
    := ⟦a.grepr.reduce lvl⟧ rewrite_by simp

  /-- Reduction on quotient does nothing, it only changes the internal representation -/
  theorem reduce_identity (a : GradedQuotient α maxLvl) (lvl : Lvl) [GradedSetoid.Reduce α (lvl ⊓ maxLvl)]
    : a.reduce lvl = a := sorry_proof

  def normalize [inst : GradedSetoid.Reduce α ⊥] (a : GradedQuotient α maxLvl) : GradedQuotient α maxLvl :=
    have h :  ⊥ = (⊥ ⊓ maxLvl : Lvl) := sorry_proof
    have : GradedSetoid.Reduce α (⊥ ⊓ maxLvl) := h ▸ inst
    a.reduce ⊥

  def nrepr [inst : GradedSetoid.Reduce α ⊥] (a : GradedQuotient α maxLvl) : α :=
    a.liftOn (λ a => a.normalize.1) sorry_proof

  @[simp]
  theorem nrepr_quotient_mk [inst : GradedSetoid.Reduce α ⊥] (a : GradedQuotient α maxLvl)
    : ⟦a.nrepr⟧ = a.ungraded
  := sorry_proof

  @[simp]
  theorem nrepr_graded_quotient_mk [GradedSetoid.Reduce α ⊥] [GradedSetoid.Reduce α maxLvl] (a : GradedQuotient α maxLvl)
    : ⟦maxLvl| a.nrepr⟧ = a
  := sorry_proof

  variable {β : Type w} [GradedSetoid β Lvl]

  @[simp high]
  theorem lift_graded_morphism
    {Lvl : Type u'} [BoundedLattice Lvl] {lvl : Lvl}
    {α : Type u} [GradedSetoid α Lvl] [GradedSetoid.Reduce α lvl]
    {β : Type v} [GradedSetoid β Lvl] [GradedSetoid.Reduce β lvl]
    (f : α → β) [GradedSetoid.Morphism f]
    (x : α)
    : ⟦lvl| f x⟧ = Quotient.lift (λ (a : GradedSetoid.Repr α lvl) => ⟦GradedSetoid.Repr.mk (f a.1) a.2 sorry_proof sorry_proof⟧) sorry_proof ⟦lvl| x⟧
    := sorry_proof

  @[simp]
  theorem lift_graded_morphism₂
    {Lvl : Type u'} {lvl : Lvl} [BoundedLattice Lvl]
    {α : Type u} [GradedSetoid α Lvl] [GradedSetoid.Reduce α lvl]
    {β : Type v} [GradedSetoid β Lvl] [GradedSetoid.Reduce β lvl]
    {γ : Type v} [GradedSetoid γ Lvl] [GradedSetoid.Reduce γ lvl]
    (f : α → β → γ) [GradedSetoid.Morphism₂ f]
    (x : α) (y : β)
    : ⟦lvl| f x y⟧ = Quotient.lift₂ (λ (x : GradedSetoid.Repr α lvl) (y : GradedSetoid.Repr β lvl) => ⟦GradedSetoid.Repr.mk (f x.1 y.1) x.2 sorry_proof x.4⟧) sorry_proof ⟦lvl| x⟧ ⟦lvl| y⟧
    := sorry_proof

end GradedQuotient
