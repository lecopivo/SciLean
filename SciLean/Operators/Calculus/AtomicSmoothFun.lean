import SciLean.Operators.Calculus.Basic

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]

class AtomicSmoothFun (f : X → Y) where
  is_smooth : IsSmooth f
  df : X → X → Y
  is_df : δ f = df

class AtomicSmoothFun₂ (f : X → Y → Z) where
  is_smooth₁ : IsSmooth f
  is_smooth₂ (x : X) : IsSmooth (f x)
  df₁ : X → X → Y → Z
  df₂ : X → Y → Y → Z
  is_df₁ : δ f = df₁
  is_df₂ : ∀ x, δ (f x) = df₂ x

attribute [reducible] AtomicSmoothFun.df
attribute [reducible] AtomicSmoothFun₂.df₁
attribute [reducible] AtomicSmoothFun₂.df₂

@[simp high]
theorem differential_of_atomic (f : X → Y) [AtomicSmoothFun f]
  : δ f = AtomicSmoothFun.df f :=
by
  apply AtomicSmoothFun.is_df
  done

@[simp high]
theorem differential_of_atomic₂_df₁ (f : X → Y → Z) [AtomicSmoothFun₂ f]
  : δ f = AtomicSmoothFun₂.df₁ f :=
by
  apply AtomicSmoothFun₂.is_df₁
  done

@[simp high]
theorem differential_of_atomic₂_df₂ (f : X → Y → Z) [AtomicSmoothFun₂ f] (x : X)
  : δ (λ y => f x y) = AtomicSmoothFun₂.df₂ f x :=
by
  apply AtomicSmoothFun₂.is_df₂ (f := f) x
  done

instance (priority := high) (f : X → Y) [AtomicSmoothFun f] : IsSmooth f := AtomicSmoothFun.is_smooth
instance (priority := high) (f : X → Y → Z) [AtomicSmoothFun₂ f] : IsSmooth f := AtomicSmoothFun₂.is_smooth₁

-- The form `(λ y => f x y)` is important for certain unifications
instance (priority := high) (f : X → Y → Z) (x : X) [AtomicSmoothFun₂ f] : IsSmooth (λ y => f x y) := AtomicSmoothFun₂.is_smooth₂ (f := f) x

-- These can't be derived automatically as there are problems with high order unification
instance (priority := high) (f : X → Y → α → Z) (x : X) [AtomicSmoothFun₂ f] : IsSmooth (λ y a => f x y a) := AtomicSmoothFun₂.is_smooth₂ (f := f) x
instance (priority := high) (f : X → Y → α → β → Z) (x : X) [AtomicSmoothFun₂ f] : IsSmooth (λ y a b => f x y a b) := AtomicSmoothFun₂.is_smooth₂ (f := f) x
instance (priority := high) (f : X → Y → α → β → γ → Z) (x : X) [AtomicSmoothFun₂ f] : IsSmooth (λ y a b c => f x y a b c) := AtomicSmoothFun₂.is_smooth₂ (f := f) x


macro "unfold_atomic" : tactic => 
  `(unfold AtomicSmoothFun₂.df₁; unfold AtomicSmoothFun₂.df₂; unfold AtomicSmoothFun.df; simp only [])

-- macro "unfold_atomic" : conv => 
--   `(unfold AtomicSmoothFun₂.df₁; unfold AtomicSmoothFun₂.df₂; unfold AtomicSmoothFun.df; simp only [])
