import Mathlib.Algebra.Group.Basic
import Mathlib.Init.Function

namespace Function

variable {α : Type u₁} {β : Type u₂} {φ : Type u₃}

-- @[simp] theorem uncurry_apply (f : α → β → φ) (ab : α × β) : uncurry f ab = f ab.1 ab.2 := rfl

-- @[simp] theorem curry_apply (f : α × β → φ) (a b) : curry f a b = f (a,b):= rfl
