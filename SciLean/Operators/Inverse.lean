import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ring

import SciLean.Categories
import SciLean.Tactic.Basic

import Init.Classical

namespace SciLean

variable {α β γ}

noncomputable
def inverse [n : Nonempty α] (f : α → β) (b : β)  : α :=
    match Classical.propDecidable (IsInv f) with
      | isTrue h => Classical.choose ((@IsInv.is_inv _ _ f h).2 b)
      | _ => Classical.choice n

postfix:max "⁻¹" => inverse

namespace Inverse

  variable {β1 β1}
  variable [Nonempty α] [Nonempty β] [Nonempty γ] [Nonempty β1] [Nonempty β2]

  theorem inverse_ext (f : α → β) : (∀ x, g (f x) = x) → (∀ y, f (g y) = y) → (f⁻¹ = g) := sorry
  macro  "inverse_ext" : tactic => `(apply inverse_ext)

  @[simp]
  def inverse_of_inverse (f : α → β) [IsInv f] 
      : (f⁻¹)⁻¹ = f := sorry

  @[simp]
  def inverse_of_id
      : (λ a : α => a)⁻¹ = id := sorry

  @[simp]
  def inverse_of_comp (f : β → γ) (g : α → β) [IsInv f] [IsInv g]
      : (λ x => f (g x))⁻¹ = g⁻¹ ∘ f⁻¹ := sorry

  @[simp]
  def inverse_of_function_comp (f : β → γ) (g : α → β) [IsInv f] [IsInv g]
      : (f ∘ g)⁻¹ = g⁻¹ ∘ f⁻¹ := sorry

  -- This is a dangerous theorem that can rewrite itself and cause simp to loop indefinitely
  -- Therefore we will define tactic `autoinvert := repeat (simp; rw[inverse_of_comp_parm]; simp)`
  def inverse_of_comp_parm (f : β1 → β2 → γ) (g1 : α → β1) (b2 : β2) [IsInv (λ b1 => f b1 b2)] [IsInv g1]
      : (λ a => f (g1 a) b2)⁻¹ = g1⁻¹ ∘ (λ b1 => f b1 b2)⁻¹ := sorry


  -------------------------------------------------------------------------

  macro "autoinvert" : conv => `(repeat' (conv => pattern (inverse _); simp; rw[inverse_of_comp_parm]; simp))
  macro "autoinvert" : tactic => `(conv => autoinvert)

  -------------------------------------------------------------------------

  variable {X Y} 
  variable [Nonempty X] [AddGroup X]
  variable [Nonempty Y] [AddGroup Y]

  @[simp]
  def inverse_of_add_arg1 (y : X)
      : (λ x => x + y)⁻¹ = (λ x => x - y) :=
  by
    inverse_ext
    intro x; rw [SubNegMonoid.sub_eq_add_neg]; simp
    intro x; rw [SubNegMonoid.sub_eq_add_neg, add_assoc, add_left_neg]; simp
    done -- ugh what a chore ... I want `abel`

  @[simp]
  def inverse_of_add_arg2 (x : X)
      : (λ y => x + y)⁻¹ = (λ y => -x + y) := 
  by
    inverse_ext
    intro y; rw [← add_assoc, add_left_neg]; simp
    intro y; rw [← add_assoc, add_right_neg]; simp
    done  --- ugh what a chore again ... I want `abal` :( :(

  @[simp]
  def inverse_of_sub_arg1 (y : X) (f : α → X) [IsInv f]
      : (λ a => (f a) - y)⁻¹ = f⁻¹ ∘ (λ x => x + y) := sorry

  @[simp]
  def inverse_of_sub_arg2 (x : X)
      : (λ y => x - y)⁻¹ = (λ y => x - y) := sorry

  @[simp]
  def inverse_of_mul_arg1 (s : ℝ) [NonZero s] (f : α → ℝ) [IsInv f]
      : (λ a => (f a)*s)⁻¹ = f⁻¹ ∘ (λ r => r/s) := sorry

  -- @[simp]
  -- def inverse_of_mul_arg2 {X} [Vec X] (r : ℝ) [NonZero r]
  --     : (λ (x : X) => r*x)⁻¹ = (λ (x : X) => (1/r)*x) := sorry
  
  -- @[simp]
  -- def inverse_of_neg {X} [Vec X]
  --     : (λ (x : X) => -x)⁻¹ = (λ (x : X) => -x) := sorry

  -- example {X Y : Type} [Vec X] [Vec Y] (f : X → Y) [IsInv f] (y' : Y) 
  --         : (λ x => - (f x) + y')⁻¹ = (λ y => f⁻¹ (-(y - y'))) :=
  -- by
  --   simp
  --   funext y
  --   simp

end Inverse
