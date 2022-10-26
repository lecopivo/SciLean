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
noncomputable 
opaque differentialSpec (f : X → Y) (x dx : X) : Y := 
    match Classical.propDecidable (IsSmooth f) with
      | isTrue  h => sorry
      /- For nondifferentiable function the value is not specified.
         Maybe we could assign zero, similarly to division by zero.
         With zero, `differential` might be semilinear in `f`.
         This should be investigated! -/
      | _ => Classical.choice (by infer_instance) 

class Differential (Fun : Type) (Diff : outParam Type) where
  differential : Fun → Diff

@[default_instance]
noncomputable
instance : Differential (X → Y) (X → X → Y) where
  differential := differentialSpec

export Differential (differential)

prefix:max "∂" => differential
macro "∂" x:Lean.Parser.Term.funBinder "," f:term:66 : term => `(∂ λ $x => $f)

-- maybe provide notation  `∂[dx] (x:=x₀), f x = ∂ f x₀ dx` and its variants
-- Variants
--     1. ∂[dx] (x:=x₀), f x          -- `∂[dx]` would be directional derivative operator
--     2. ∂ (x:=x₀;dx), f x           -- this has weird version without `x₀` ∂ (x:=;dx), f x 
--     3. ∂_dx (x:=x₀), f x           -- Can we parse this properly? What if `dx` is complicated, do we allow `∂_(dx)` ?
--     4. ??

class Derivative (Fun : Type) where
  derivative : Nat → Fun → Fun

@[default_instance]
noncomputable
instance : Derivative (ℝ → X) where
  derivative := 
    let rec dn (n : Nat) (f : ℝ → X) : ℝ → X :=
      match n with
      | 0    => f
      | n'+1 => dn n' (λ t => ∂ f t 1)
    dn

export Derivative (derivative)

prefix:max "ⅆ" => derivative 1
macro:max "ⅆ[" n:term "]" : term => `(derivative $n)

-- Notation 
-- ⅆ s, f s         --> ⅆ λ s => f s
-- ⅆ s : ℝ, f s     --> ⅆ λ s : ℝ => f s
-- ⅆ s := t, f s    --> (ⅆ λ s => f s) t
syntax diffBinderType  := ":" term
syntax diffBinderValue := ":=" term
syntax diffBinder := ident (diffBinderType <|> diffBinderValue)?
syntax "ⅆ" diffBinder "," term:66 : term
syntax "ⅆ" "(" diffBinder ")" "," term:66 : term
syntax "ⅆ[" term "]" diffBinder "," term:66 : term            -- TODO: implement macro_rule
syntax "ⅆ[" term "]" "(" diffBinder ")" "," term:66 : term    -- TODO: implement macro_rule
macro_rules
| `(ⅆ $x:ident, $f) =>
  `(ⅆ λ $x => $f)
| `(ⅆ $x:ident : $type:term, $f) =>
  `(ⅆ λ $x : $type => $f)
| `(ⅆ $x:ident := $val:term, $f) =>
  `((ⅆ λ $x => $f) $val)
| `(ⅆ ($b:diffBinder), $f) =>
  `(ⅆ $b, $f)

@[simp]
theorem derivative_is_diff (f : ℝ → X) 
  : ⅆ f = λ t => ∂ f t 1 := by rfl

-- -- Bad as an instance
-- theorem linear_is_smooth (f : X → Y) [IsLin f] : IsSmooth f := sorry
-- Bad for simp
theorem diff_of_linear (f : X → Y) [IsLin f] : ∂ f = λ x dx => f dx := sorry

instance diff.arg_x.isSmooth (f : X → Y) [IsSmooth f] : IsSmooth (∂ f) := sorry
instance diff.arg_dx.isLin    (f : X → Y) [IsSmooth f] (x : X) : IsLin (∂ f x) := sorry
instance diff.arg_dx.isSmooth (f : X → Y) [IsSmooth f] (x : X) : IsSmooth (∂ f x) := sorry

instance diff.arg_y.isLin (f : X → Y → Z) [IsSmooth f] [∀ x, IsLin (f x)] (x dx) : IsLin (∂ f x dx) := sorry
instance diff.arg_y.isSmooth (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)] (x dx) : IsSmooth (∂ f x dx) := sorry

instance diff.arg_x.comp.isSmooth {X Y Z} [Vec X] [Vec Y] [Vec Z] [Vec W]
  (f : Y → Z → W) [IsSmooth f] [∀ y, IsSmooth (f y)] 
  (g : X → Y) [IsSmooth g]
  : IsSmooth (λ x => ∂ (f (g x))) := sorry


@[simp]
theorem diff.arg_df.diff_simp (f : X → Y) [IsSmooth f] (x : X)
  : (∂ (∂ f x)) = (λ _ dx => ∂ f x dx) := by 
  -- apply (diff_of_linear (λ dx => ∂ f x dx))
  rw[diff_of_linear (λ dx => ∂ f x dx)]
  done

----------------------------------------------------------------------

@[simp ↓, simp_diff]
theorem id.arg_x.diff_simp
  : ∂ (λ x : X => x) = λ x dx => dx := sorry

@[simp ↓, simp_diff]
theorem const.arg_y.diff_simp (x : X)
  : ∂ (λ y : Y => x) = λ y dy => (0 : X) := sorry

@[simp ↓ low-3, simp_diff low-3]
theorem diff_of_swap (f : α → X → Y) [∀ i, IsSmooth (f i)]
  : ∂ (λ x a => f a x) = λ x dx a => ∂ (f a) x dx := sorry

@[simp ↓ low-1, simp_diff low-1]
theorem diff_of_comp
  (f : Y → Z) [IsSmooth f] 
  (g : X → Y) [IsSmooth g] 
  : ∂ (λ x => f (g x)) = λ x dx => ∂ f (g x) (∂ g x dx) := sorry

@[simp ↓ low-2, simp_diff low-2]
theorem diff_of_diag
  (f : Y₁ → Y₂ → Z) [IsSmooth f] [∀ y₁, IsSmooth (f y₁)]
  (g₁ : X → Y₁) [IsSmooth g₁]
  (g₂ : X → Y₂) [IsSmooth g₂]
  : ∂ (λ x => f (g₁ x) (g₂ x)) 
    = 
    λ x dx => ∂ f (g₁ x) (∂ g₁ x dx) (g₂ x) + 
              ∂ (f (g₁ x)) (g₂ x) (∂ g₂ x dx) := sorry

@[simp ↓ low, simp_diff low]
theorem diff_of_parm
  (f : X → α → Y) [IsSmooth f] (a : α)
  : ∂ (λ x => f x a) = λ x dx => ∂ f x dx a := sorry

@[simp ↓, simp_diff]
theorem diff_of_eval
  (a : α)
  : ∂ (λ f : α → Y => f a) = λ f df => df a := by simp

@[simp ↓ low, simp_diff low]
theorem uncurry.arg_xy.diff_simp
  (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)]
  : ∂ (λ (xy : (X×Y)) => f xy.1 xy.2) = λ (x,y) (dx,dy) => ∂ f x dx y + ∂ (f x) y dy := sorry 

  -- : ∂ (λ ((x,y) : (X×Y)) => f x y) = λ (x,y) (dx,dy) => ∂ f x dx y + ∂ (f x) y dy := sorry 

@[simp ↓ low, simp_diff low]
theorem uncurry.arg_xy.parm1.diff_simp
  (a : α)
  (f : X → Y → α → Z) [IsSmooth λ x y => f x y a] [∀ x, IsSmooth (λ y => f x y a)]
  : ∂ (λ (xy : (X×Y)) => f xy.1 xy.2 a) = λ (x,y) (dx,dy) => ∂ f x dx y a + ∂ (f x) y dy a := sorry
