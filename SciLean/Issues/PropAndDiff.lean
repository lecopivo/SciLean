import SciLean.Core

namespace SciLean

/- This came up when working with 
        `getElem : (x : Cont) → (i : Idx) → Dom x i → Elem` 

   The trouble is:
     1. `Dom x i` is in `Prop` thus `Dom x i → Elem` is not(with 
        current definitions) Vec if Elem is Vec
     2. `Dom x i` is dependent type and autodiff does not work properly
        with dependent types yet.
 -/

-- This is direct application of `diff_of_parm`
example {α : Type} (a : α) (f : ℝ → α → ℝ) [IsSmooth f]
  : ∂ (λ x => f x a) = λ x dx => ∂ f x dx a := by simp; done

-- This needs variant of `diff_of_parm`
example {α β : Type} (a : α) (b : β) (f : ℝ → α → β → ℝ) [IsSmooth λ x a => f x a b] 
  : ∂ (λ x => f x a b) = λ x dx => ∂ (λ x a => f x a b) x dx a := by simp

-- When ‵α` is Prop insteadd of Type, we can't even state that
example {α : Prop} (a : α) (f : ℝ → α → ℝ) [IsSmooth f] 
  : ∂ (λ x => f x a) = λ x dx => ∂ f x dx a := by simp

variable (P : Prop) (X : Type)
example (P : Prop) (X : Type) [Vec X] : Vec (P → X) := by infer_instance

@[simp ↓ low, simp_diff low]
theorem diff_of_parm.parm_a {X Y α β : Type} [Vec X] [Vec Y]
  (f : X → α → β → Y) (a : α) (b : β) [IsSmooth λ x a => f x a b]
  : ∂ (λ x => f x a b) = λ x dx => ∂ (λ x a => f x a b) x dx a := sorry
