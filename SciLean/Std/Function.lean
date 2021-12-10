import Mathlib.Init.Function

namespace Function

-- id already exists ... not in Function namespace though

-- const already exists

-- comp already exists

-- @[inline]
-- def eval {α} {β : α → Sort v} : (a : α) → ((a' : α) → (β a')) → (β a) := λ a f => f a
-- @[simp] theorem eval_apply {β : α → Sort v} (a : α) (f : (a' : α) → (β a')): eval a f = f a := rfl

-- There is already function called flip that does this ... not in Function namespace though
-- #check swap
-- @[inline]
-- def swap : (α → β → γ) → (β → α → γ) := λ f b a => f a b
-- @[simp] theorem swap_apply (f : α → β → γ) : swap f b a = f a b := rfl

-- @[inline]
-- def curry : (α × β → γ) → (α → β → γ) := λ f a b => f (a,b) 
-- @[simp] theorem curry_apply (f : α × β → γ) (a : α) (b : β) : curry f a b = f (a,b) := rfl

-- @[inline]
-- def uncurry : (α → β → γ) → (α × β → γ) := λ f ab => f ab.1 ab.2
-- @[simp] theorem uncurry_apply (f : α → β → γ) (ab : α × β) : uncurry f ab = f ab.1 ab.2 := rfl

@[inline]
def fmap {E : α → Sort u} {F : α → Sort v} (f : (a : α) → E a → F a) 
    : ((a : α) → E a) → ((a' : α) → F a') := λ g a => (f a) (g a)
@[simp] theorem fmap_apply {E : α → Sort u} {F : α → Sort v} (f : (a : α) → E a → F a) (g : (a : α) → E a)
                : fmap f g a = (f a) (g a) := rfl

@[inline]
def pmap : (α → γ) → (β → δ) → (α×β → γ×δ) := λ f g ac => (f ac.1, g ac.2)
@[simp] theorem pmap_apply (f : α → γ) (g : β → δ) (ab : α×β) : pmap f g ab = (f ab.1, g ab.2) := rfl


  section CombinatorIdentities

  @[simp]
  def comp_id (f : α → β) : f ∘ id = f := by funext x; simp done

  @[simp]
  def id_comp (f : α → β) : id ∘ f = f := by funext x; simp done

  end CombinatorIdentities

