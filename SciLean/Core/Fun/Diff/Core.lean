import Lean
import Init.Classical

import SciLean.Core.Prelude
import SciLean.Core.Attr
import SciLean.Core.Mor.IsLin
import SciLean.Core.Mor.IsSmooth

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z] 
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]

------------------
-- Differential --
------------------
-- @[irreducible] -- this does not work work as intended and I switched to `constant`
noncomputable 
def differential (f : X → Y) (x dx : X) : Y := 
    match Classical.propDecidable (IsSmooth f) with
      | isTrue  h => sorry
      | _ => (0 : Y)

prefix:max "δ" => differential

-- Potential notation
-- prefix:max "∂" => differential 
-- macro "∂/∂" noWs x:ident b:term : term => `(λ x₀ => δ (λ $x => $b) x₀ 1)
-- variable (f : ℝ → ℝ → ℝ) (x y : ℝ)
-- #check (∂/∂x f x y) x + (∂/∂y f x y) y

-- -- Bad as an instance
-- theorem linear_is_smooth (f : X → Y) [IsLin f] : IsSmooth f := sorry
-- Bad for simp
theorem diff_of_linear (f : X → Y) [IsLin f] : δ f = λ x dx => f dx := sorry

instance diff.arg_x.isSmooth (f : X → Y) [IsSmooth f] : IsSmooth (δ f) := sorry
instance diff.arg_dx.isLin    (f : X → Y) [IsSmooth f] (x : X) : IsLin (δ f x) := sorry
instance diff.arg_dx.isSmooth (f : X → Y) [IsSmooth f] (x : X) : IsSmooth (δ f x) := sorry

instance diff.arg_y.isSmooth (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)] (x dx) : IsSmooth (δ f x dx) := sorry

instance diff.arg_x.comp.isSmooth {X Y Z} [Vec X] [Vec Y] [Vec Z] [Vec W]
  (f : Y → Z → W) [IsSmooth f] [∀ y, IsSmooth (f y)] 
  (g : X → Y) [IsSmooth g]
  : IsSmooth (λ x => δ (f (g x))) := sorry


@[simp]
theorem diff.arg_df.diff_simp (f : X → Y) [IsSmooth f] (x : X)
  : (δ (δ f x)) = (λ _ dx => δ f x dx) := by 
  -- apply (diff_of_linear (λ dx => δ f x dx))
  rw[diff_of_linear (λ dx => δ f x dx)]
  done


theorem WTF_INVESTIGATE_THIS {X} {Y} [Vec X] [Vec Y] (f : X → Y) [IsSmooth f] (x : X)
  : (δ (δ f x)) = (λ x' dx => δ f x' x') := by 
  apply (diff_of_linear (λ dx => δ f x dx)) --- WTF??!!!!
  done

----------------------------------------------------------------------

@[simp ↓, simp_diff]
theorem id.arg_x.diff_simp
  : δ (λ x : X => x) = λ x dx => dx := sorry

@[simp ↓, simp_diff]
theorem const.arg_y.diff_simp (x : X)
  : δ (λ y : Y => x) = λ y dy => (0 : X) := sorry

@[simp ↓ low-3, simp_diff low-3]
theorem diff_of_swap (f : α → X → Y) [∀ i, IsSmooth (f i)]
  : δ (λ x a => f a x) = λ x dx a => δ (f a) x dx := sorry

@[simp ↓ low-1, simp_diff low-1]
theorem diff_of_comp
  (f : Y → Z) [IsSmooth f] 
  (g : X → Y) [IsSmooth g] 
  : δ (λ x => f (g x)) = λ x dx => δ f (g x) (δ g x dx) := sorry

@[simp ↓ low-2, simp_diff low-2]
theorem diff_of_diag
  (f : Y₁ → Y₂ → Z) [IsSmooth f] [∀ y₁, IsSmooth (f y₁)]
  (g₁ : X → Y₁) [IsSmooth g₁]
  (g₂ : X → Y₂) [IsSmooth g₂]
  : δ (λ x => f (g₁ x) (g₂ x)) 
    = 
    λ x dx => δ f (g₁ x) (δ g₁ x dx) (g₂ x) + 
              δ (f (g₁ x)) (g₂ x) (δ g₂ x dx) := sorry

@[simp ↓ low, simp_diff low]
theorem diff_of_parm
  (f : X → α → Y) [IsSmooth f] (a : α)
  : δ (λ x => f x a) = λ x dx => δ f x dx a := sorry

@[simp ↓, simp_diff]
theorem diff_of_eval
  (a : α)
  : δ (λ f : α → Y => f a) = λ f df => df a := by simp

@[simp ↓ low, simp_diff low]
theorem uncurry.arg_xy.diff_simp
  (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)]
  : δ (λ ((x,y) : (X×Y)) => f x y) = λ (x,y) (dx,dy) => δ f x dx y + δ (f x) y dy := sorry 

@[simp ↓ low, simp_diff low]
theorem uncurry.arg_xy.parm1.diff_simp
  (a : α)
  (f : X → Y → α → Z) [IsSmooth λ x y => f x y a] [∀ x, IsSmooth (λ y => f x y a)]
  : δ (λ ((x,y) : (X×Y)) => f x y a) = λ (x,y) (dx,dy) => δ f x dx y a + δ (f x) y dy a := sorry
