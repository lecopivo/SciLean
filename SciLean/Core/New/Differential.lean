import Lean
import Init.Classical

import SciLean.Core.New.Attributes
import SciLean.Core.New.IsSmooth
import SciLean.Core.New.IsLin

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z] 
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]

--------------------------------------------------------------------------------
-- Differential --
--------------------------------------------------------------------------------

noncomputable 
opaque differentialSpec (f : X → Y) (x dx : X) : Y := 
    match Classical.propDecidable (IsSmooth f) with
      | isTrue  h => Mathlib.Convenient.derivative f h.proof x dx
      /- For nondifferentiable function the value is not specified.
         Maybe we could assign zero, similarly to division by zero.
         With zero, `differential` might be semilinear in `f`.
         This should be investigated! -/
      | _ => 0

class Differential (α : Type) (β : outParam Type) where
  differential : α → β

export Differential (differential)

prefix:max "∂" => Differential.differential

@[default_instance]
noncomputable
instance : Differential (X → Y) (X → X → Y) where
  differential := differentialSpec


-- maybe provide notation  `∂[dx] (x:=x₀), f x = ∂ f x₀ dx` and its variants
-- Variants
--     1. ∂[dx] (x:=x₀), f x          -- `∂[dx]` would be directional derivative operator
--     2. ∂ (x:=x₀,dx), f x           -- this has weird version without `x₀` ∂ (x:=;dx), f x 
--     3. ∂_dx (x:=x₀), f x           -- Can we parse this properly? What if `dx` is complicated, do we allow `∂_(dx)` ?
--     4. ??
-- macro "∂" x:Lean.Parser.Term.funBinder "," f:term:66 : term => `(∂ λ $x => $f)
syntax diffBinderType  := ":" term
syntax diffBinderValue := ":=" term
syntax diffBinder := ident (diffBinderType <|> diffBinderValue)?
syntax "∂" diffBinder "," term:66 : term
syntax "∂" "(" diffBinder ")" "," term:66 : term
macro_rules
| `(∂ $x:ident, $f) =>
  `(∂ λ $x => $f)
| `(∂ $x:ident : $type:term, $f) =>
  `(∂ λ $x : $type => $f)
| `(∂ $x:ident := $val:term, $f) =>
  `((∂ λ $x => $f) $val)
| `(∂ ($b:diffBinder), $f) =>
  `(∂ $b, $f)


--------------------------------------------------------------------------------
-- Smooth Differential --
--------------------------------------------------------------------------------


instance differential.arg_x.isSmooth (f : X → Y) [IsSmoothT f] 
  : IsSmoothNT 2 (λ x dx => ∂ f x dx) := sorry_proof
instance differential.arg_dx.isLin    (f : X → Y) [IsSmoothT f] (x : X) 
  : IsLinT (λ dx => ∂ f x dx) := sorry_proof

instance differential.arg_y.isLin 
  (f : X → Y → Z) [IsSmoothT f] [∀ x, IsLinT (f x)] (x dx) 
  : IsLinT (λ y => ∂ f x dx y) := sorry_proof
instance differential.arg_y.isSmooth (f : X → Y → Z) [IsSmoothNT 2 f] (x dx) 
  : IsSmoothT (λ y => ∂ f x dx y) := sorry_proof

instance differential.arg_x.comp.isSmooth {X Y Z} [Vec X] [Vec Y] [Vec Z] [Vec W]
  (f : Y → Z → W) [IsSmoothNT 2 f]
  (g : X → Y) [IsSmoothT g]
  : IsSmoothT (λ x => ∂ (f (g x))) := sorry_proof


variable (f : X ⟿ Y) 

example : IsSmoothT (λ x => f x) := by infer_instance
example : IsSmoothT (λ x => ∂ f.1 x) := by infer_instance

#check (λ x => ∂ f.1 x)
#check (λ x ⟿ ∂ f.1 x)
#check (λ x => λ dx ⊸ ∂ f.1 x dx)
-- #check (λ x ⟿ λ dx ⟿ ∂ f.1 x dx)
-- #check (λ x ⟿ λ dx ⊸ ∂ f.1 x dx)


instance (f : X → Y → Z) [IsSmoothNT 2 f] 
  : IsSmoothT λ x => λ y ⟿ f x y := sorry_proof -- follows from currying 

variable (f : X → Y → Z) [IsSmoothNT 2 f] 

#check λ x => λ y ⟿ f x y

#check λ x ⟿ λ y ⟿ f x y

--------------------------------------------------------------------------------
-- Scalar Differential --
--------------------------------------------------------------------------------

@[reducible]
class ScalarDifferential (α : Type) (β : outParam Type) where
  scalarDifferential : α → β

export ScalarDifferential (scalarDifferential)

prefix:max "ⅆ" => ScalarDifferential.scalarDifferential

@[default_instance, reducible]
noncomputable
instance : ScalarDifferential (ℝ → X) (ℝ → X) where
  scalarDifferential := λ f x => ∂ f x 1

 
-- Notation 
-- ⅆ s, f s         --> ⅆ λ s => f s
-- ⅆ s : ℝ, f s     --> ⅆ λ s : ℝ => f s
-- ⅆ s := t, f s    --> (ⅆ λ s => f s) t
syntax "ⅆ" diffBinder "," term:66 : term
syntax "ⅆ" "(" diffBinder ")" "," term:66 : term
macro_rules
| `(ⅆ $x:ident, $f) =>
  `(ⅆ λ $x => $f)
| `(ⅆ $x:ident : $type:term, $f) =>
  `(ⅆ λ $x : $type => $f)
| `(ⅆ $x:ident := $val:term, $f) =>
  `((ⅆ λ $x => $f) $val)
| `(ⅆ ($b:diffBinder), $f) =>
  `(ⅆ $b, $f)


--------------------------------------------------------------------------------
-- Dual Number Differential --
--------------------------------------------------------------------------------

@[reducible]
class DualNumberDifferential (α : Type) (β : outParam Type) where
  dualNumberDifferential : α → β

export DualNumberDifferential (dualNumberDifferential)

prefix:max "𝒟" => dualNumberDifferential

@[default_instance]
noncomputable
instance : DualNumberDifferential (X → Y) (X×X → Y×Y) where
  dualNumberDifferential := λ f (x,dx) => (f x, ∂ f x dx)


--------------------------------------------------------------------------------
-- Dual Number Differential --
--------------------------------------------------------------------------------

@[reducible]
class ForwardDifferential (α : Type) (β : outParam Type) where
  forwardDifferential : α → β

export ForwardDifferential (forwardDifferential)

prefix:max "ℱ" => forwardDifferential

@[default_instance]
noncomputable
instance : ForwardDifferential (X → Y) (X → Y×(X→Y)) where
  forwardDifferential := λ f x => (f x, λ dx => ∂ f x dx)


--------------------------------------------------------------------------------
-- Core Differentiation Rules --
--------------------------------------------------------------------------------

@[simp ↓, autodiff]
theorem id.arg_x.diff_simp
  : ∂ (λ x : X => x) = λ x dx => dx := sorry_proof

@[simp ↓, autodiff]
theorem const.arg_y.diff_simp (x : X)
  : ∂ (λ y : Y => x) = λ y dy => (0 : X) := sorry_proof

@[simp ↓ low-3, autodiff]
theorem diff_of_swap (f : α → X → Y) [∀ i, IsSmoothT (f i)]
  : ∂ (λ x a => f a x) = λ x dx a => ∂ (f a) x dx := sorry_proof

@[simp ↓ low-1, autodiff]
theorem diff_of_comp
  (f : Y → Z) [IsSmoothT f] 
  (g : X → Y) [IsSmoothT g] 
  : ∂ (λ x => f (g x)) 
    = 
    λ x dx => 
      let y := g x
      let dy := ∂ g x dx
      ∂ f y dy := sorry_proof

@[simp ↓ low-2, autodiff]
theorem diff_of_diag
  (f : Y₁ → Y₂ → Z) [IsSmoothNT 2 f]
  (g₁ : X → Y₁) [IsSmoothT g₁]
  (g₂ : X → Y₂) [IsSmoothT g₂]
  : ∂ (λ x => f (g₁ x) (g₂ x)) 
    = 
    λ x dx => 
      let y₁ := g₁ x
      let dy₁ := ∂ g₁ x dx
      let y₂ := g₂ x
      let dy₂ := ∂ g₂ x dx
      ∂ f y₁ dy₁ y₂ + 
      ∂ (f y₁) y₂ dy₂ := sorry_proof

@[simp ↓ low, autodiff]
theorem diff_of_parm
  (f : X → α → Y) [IsSmoothT f] (a : α)
  : ∂ (λ x => f x a) = λ x dx => ∂ f x dx a := 
by
  rw[diff_of_swap (λ a x => f x a)]

@[simp ↓, autodiff]
theorem diff_of_eval
  (a : α)
  : ∂ (λ f : α → Y => f a) = λ _ df => df a := by simp


-- @[simp ↓ low, autodiff]
-- theorem uncurry.arg_xy.diff_simp
--   (f : X → Y → Z) [IsSmoothNT 2 f]
--   : ∂ (λ (xy : (X×Y)) => f xy.1 xy.2) = λ (x,y) (dx,dy) => ∂ f x dx y + ∂ (f x) y dy := sorry_proof

--   -- : ∂ (λ ((x,y) : (X×Y)) => f x y) = λ (x,y) (dx,dy) => ∂ f x dx y + ∂ (f x) y dy := sorry_proof 

-- @[simp ↓ low, autodiff]
-- theorem uncurry.arg_xy.parm1.diff_simp
--   (a : α)
--   (f : X → Y → α → Z) [IsSmoothNT 2 f]
--   : ∂ (λ (xy : (X×Y)) => f xy.1 xy.2 a) = λ (x,y) (dx,dy) => ∂ f x dx y a + ∂ (f x) y dy a := sorry_proof



--------------------------------------------------------------------------------

/-- Differential of linear function is the function itself.

This theorem is too general and we do not want to try to apply it 
every time we try to differentiate something. That is why it it has 
low priority and more importantly it asks for `IsLin` and not for `IsLinT`.
Only elementary functions(that are not composite composite) are allowed
to be differentiated with this theorem. -/
@[simp low, autodiff] 
theorem diff_of_linear (f : X → Y) [IsLin f]
  : ∂ f = λ _ dx => f dx := sorry_proof

@[simp low, autodiff] 
theorem diff_of_linear_2_1 (f : X → Y → Z) [IsLinN 2 f] : ∂ f = λ _ dx _ => f dx 0 := sorry_proof
@[simp low, autodiff] 
theorem diff_of_linear_2_2 (f : X → Y → Z) [IsLinN 2 f] (x : X) : ∂ (f x) = λ _ dy => f 0 dy := sorry_proof
