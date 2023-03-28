import Lean
import Init.Classical

import SciLean.Core.Attributes
import SciLean.Core.HasAdjoint
import SciLean.Core.Defs

import SciLean.Tactic.CustomSimp.DebugSimp

-- import SciLean.Tactic.CustomSimp.SimpGuard
import SciLean.Tactic.AutoDiff
import SciLean.Core.AutoDiffSimps

namespace SciLean

variable {α β γ : Type}
variable {X Y Z U V : Type} [Vec X] [Vec Y] [Vec Z] [Vec U] [Vec V]
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]


--------------------------------------------------------------------------------
-- Differential --
--------------------------------------------------------------------------------

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

-- instance differential.arg_dx.isSmooth (f : X → Y) [IsSmoothT f] (x : X) 
--   : IsSmoothT (λ dx => ∂ f x dx) := by (try infer_instance); sorry_proof
-- instance differential.arg_dx.isLin    (f : X → Y) [IsSmoothT f] (x : X) 
--   : IsLinT (λ dx => ∂ f x dx) := by (try infer_instance); sorry_proof
-- instance differential.arg_x.isSmooth  (f : X → Y) [IsSmoothT f] 
--   : IsSmoothT (λ x => λ dx ⊸ ∂ f x dx) := by (try infer_instance); sorry_proof
-- instance differential.arg_x.isSmooth' (f : X → Y) [IsSmoothT f] 
--   : IsSmoothT (λ x => λ dx ⟿ ∂ f x dx) := by (try infer_instance); sorry_proof


-- instance differential.arg_y.isLin 
--   (f : X → Y → Z) [IsSmoothT f] [∀ x, IsLinT (f x)] (x dx) 
--   : IsLinT (λ y => ∂ f x dx y) := by (try infer_instance); sorry_proof
-- instance differential.arg_y.isSmooth (f : X → Y → Z) [IsSmoothNT 2 f] (x dx) 
--   : IsSmoothT (λ y => ∂ f x dx y) := by (try infer_instance); sorry_proof

-- instance differential.arg_x.comp.isSmooth {X Y Z} [Vec X] [Vec Y] [Vec Z] [Vec W]
--   (f : Y → Z → W) [IsSmoothNT 2 f]
--   (g : X → Y) [IsSmoothT g]
--   : IsSmoothT (λ x => ∂ (f (g x))) := by (try infer_instance); sorry_proof


-- instance SmoothMap.mk'.arg_f.diff_simp {X Y W} [Vec X] [Vec Y] [Vec W]
--   (f : W → X → Y) [IsSmoothNT 2 f]
--   : ∂ (λ w => λ x ⟿ f w x)
--     =
--     λ w dw => λ x ⟿ ∂ f w dw x := by simp; sorry_proof


-- instance LinMap.mk'.arg_f.diff_simp {X Y W} [Vec X] [Vec Y] [Vec W]
--   (f : W → X → Y) [IsSmoothNT 2 f] [∀ w, IsLinT (f w)]
--   : ∂ (λ w => λ x ⊸ f w x)
--     =
--     λ w dw => λ x ⊸ ∂ f w dw x := by sorry_proof

-- noncomputable
-- def Smooth.differential (f : X ⟿ Y) : (X ⟿ X ⊸ Y) := fun x ⟿ fun dx ⊸ ∂ f.1 x dx

-- instance (f : X ⟿ Y) : Partial f (Smooth.differential f) := ⟨⟩


-- --------------------------------------------------------------------------------
-- -- Scalar Differential --
-- --------------------------------------------------------------------------------

-- noncomputable
-- abbrev differentialScalar (f : ℝ → X) (t : ℝ) : X := ∂ f t 1

-- noncomputable
-- abbrev Smooth.differentialScalar (f : ℝ ⟿ X) : ℝ ⟿ X := λ t ⟿ ((∂ f t) 1)

-- @[default_instance] 
-- instance differentialScalar.instDifferentialNotation (f : ℝ → X) 
--   : Differential f (differentialScalar f) := ⟨⟩

-- instance Smooth.differentialScalar.instDifferentialNotation (f : ℝ ⟿ X) 
--   : Differential f (Smooth.differentialScalar f) := ⟨⟩

 
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


-- --------------------------------------------------------------------------------
-- -- Dual Number Differential --
-- --------------------------------------------------------------------------------

-- noncomputable
-- def tangentMap (f : X → Y) : X×X → Y×Y := λ (x,dx) => (f x, ∂ f x dx)

-- instance Prod.mk.arg_xy.isSmooth : IsSmoothN 2 (Prod.mk : X → Y → X×Y) := sorry_proof

-- instance (f : X → Y) : IsSmooth (λ (x,dx) => ∂ f x dx) := sorry_proof
-- instance (f : X ⟿ Y) : IsSmooth (λ (x,dx) => ∂ f x dx) := sorry_proof

-- noncomputable
-- def Smooth.tangentMap (f : X ⟿ Y) : X×X ⟿ Y×Y := λ xdx ⟿ (f xdx.1, ∂ f xdx.1 xdx.2)

-- @[default_instance]
-- instance (f : X → Y) : TangentMap f (tangentMap f) := ⟨⟩

-- instance (f : X ⟿ Y) : TangentMap f (Smooth.tangentMap f) := ⟨⟩



instance differential.arg_dx.isLin (f : X → Y) [IsSmoothT f] (x : X)
  : IsLinT (λ dx => ∂ f x dx) := sorry_proof

instance differential.arg_dx.isSmooth (f : X → Y) [IsSmoothT f] (x : X)
  : IsSmoothT (λ dx => ∂ f x dx) := sorry_proof


instance (f : X → Y → Z) [∀ x, IsLin (f x)] [IsSmoothT λ x => λ y ⊸ f x y]
  : IsSmoothT (λ x => λ y ⟿ f x y) := show_smoothness_via (Smooth.comp (λ (L : Y⊸Z) ⟿ λ y ⟿ L y) (λ x ⟿ λ y ⊸ f x y)) (by ext x y; simp)

-- instance differential.arg_x_dx.isSmooth' (f : X → Y) [IsSmoothT f]
--   : IsSmoothT (λ x => λ dx ⊸ ∂ f x dx) := sorry_proof

instance differential.arg_x_dx.isSmooth (f : X → Y) [IsSmoothT f]
  : IsSmoothT (λ x => λ dx ⟿ ∂ f x dx) := sorry_proof

-- instance differential.arg_f_xdx.isSmooth' (f : U → X → Y) [∀ u, IsSmoothT (f u)] [IsSmoothT λ u => λ x ⟿ f u x]
--   : IsSmoothT (λ u => λ x ⟿ λ dx ⊸ ∂ (f u) x dx) := sorry_proof

instance differential.arg_f_xdx.isSmooth (f : U → X → Y) [∀ u, IsSmoothT (f u)] [IsSmoothT λ u => λ x ⟿ f u x]
  : IsSmoothT (λ u => λ x dx ⟿ ∂ (f u) x dx) := sorry_proof

instance differential.arg_y.isSmooth (f : X → Y → Z) [∀ x, IsSmoothT (f x)] [IsSmoothT (λ x => λ y ⟿ f x y)] (x dx : X)
  : IsSmoothT (λ y => ∂ f x dx y) := by (try infer_instance); sorry_proof
instance differential.arg_dx_y.isSmooth (f : X → Y → Z) [∀ x, IsSmoothT (f x)] [IsSmoothT (λ x => λ y ⟿ f x y)] (x : X)
  : IsSmoothT (λ dx => λ y ⟿ ∂ f x dx y) := by (try infer_instance); sorry_proof
instance differential.arg_x_dxy.isSmooth (f : X → Y → Z) [∀ x, IsSmoothT (f x)] [IsSmoothT (λ x => λ y ⟿ f x y)]
  : IsSmoothT (λ x => λ dx y ⟿ ∂ f x dx y) := by (try infer_instance); sorry_proof
instance differential.arg_f_xdxy.isSmooth (f : U → X → Y → Z) [∀ u x, IsSmoothT (f u x)] [∀ u, IsSmoothT (λ x => λ y ⟿ f u x y)] [IsSmoothT (λ u => λ x y ⟿ f u x y)]
  : IsSmoothT (λ u => λ x dx y ⟿ ∂ (f u) x dx y) := by (try infer_instance); sorry_proof

  
--------------------------------------------------------------------------------
-- Differential Rules --
--------------------------------------------------------------------------------

-- -- I: X⟿X

-- @[diff]
-- theorem differential_rule_I 
--   : ∂ (λ x : X => x) = λ _ dx => dx := sorry_proof


-- -- K: X⟿Y⟿X

-- @[diff]
-- theorem differential_rule_K₂ (x : X) 
--   : ∂ (λ _ : Y => x) = λ _ _ => 0 := sorry_proof

-- set_option trace.Meta.Tactic.simp.rewrite true in
-- @[diff]
-- theorem differential_rule_K₁ 
--   : ∂ (λ (x : X) (_ : Y) => x) = λ _ dx _ => dx := sorry_proof


-- -- S: (X⟿Y⟿Z)⟿(X⟿Y)⟿X⟿Z

-- @[diff]
-- theorem differential_rule_S₃
--   (f : X → Y → Z) [∀ x, IsSmoothT (f x)] [IsSmoothT λ x => λ y ⟿ f x y] -- [IsSmoothN 2 f]
--   (g : X → Y)  [IsSmoothT g]
--   : ∂ (λ x => f x (g x)) 
--     = 
--     λ x dx => 
--       let (y,dy) := 𝒯 g x dx
--       ∂ f x dx y + ∂ (f x) y dy
--   := sorry_proof

-- instance (f : U → X → Y → Z) [∀ u x, IsSmoothT (f u x)] [∀ u, IsSmoothT (λ x => λ y ⟿ f u x y)] [IsSmoothT (λ u => λ x y ⟿ f u x y)]
--   (g : U → X) [IsSmoothT g]
--   : IsSmoothT λ u => λ y ⟿ f u (g u) y := 
-- by 
--   try infer_instance
--   have : IsSmoothT fun u => λ u' y ⟿ f u (g u') y := by (try infer_instance); apply IsSmoothT_rule_S₁ (λ u x y => f u y x) (λ v _ => g v)
--   apply IsSmoothT_duplicate_argument (λ u u' => λ y ⟿ f u (g u') y)

-- @[diff]
-- theorem differential_rule_S₂
--   (f : X → Y → Z)   [∀ x, IsSmoothT (f x)] [IsSmoothT λ x => λ y ⟿ f x y] -- [IsSmoothN 2 f]
--   (g : V → (X → Y)) [∀ v, IsSmoothT (g v)] [IsSmoothT λ v => λ x ⟿ g v x] -- [IsSmoothN 2 g]
--   : ∂ (λ v => λ x ⟿ f x (g v x))
--     =
--     λ v dv => λ x ⟿ ∂ (f x) (g v x) (∂ g v dv x)
--   := sorry_proof


--------------------------

@[simp ↓, diff]
theorem differential.of_id
  : ∂ (λ x : X => x) = λ x dx => dx := sorry_proof

@[simp ↓, diff]
theorem differential.of_const (x : X)
  : ∂ (λ y : Y => x) = λ y dy => (0 : X) := sorry_proof

@[simp ↓ low-3, diff low-3]
theorem differential.of_swap (f : α → X → Y) [∀ i, IsSmoothT (f i)]
  : ∂ (λ x a => f a x) = λ x dx a => ∂ (f a) x dx := sorry_proof

@[simp ↓ low-1, diff low-1, simp_guard g (λ x => x)]
theorem differential.of_comp
  (f : Y → Z) [IsSmoothT f] 
  (g : X → Y) [IsSmoothT g]
  : ∂ (λ x => f (g x)) 
    = 
    λ x dx => 
      let (y,dy) := (𝒯 g) x dx
      -- let y := g x
      -- let dy := ∂ g x dx
      ∂ f y dy 
  := sorry_proof

@[simp ↓ low-2, diff low-2, simp_guard g₁ Prod.fst, g₂ Prod.snd]
theorem differential.of_diag
  (f : Y₁ → Y₂ → Z) [∀ x, IsSmoothT (f x)] [IsSmoothT λ x => λ y ⟿ f x y] 
  (g₁ : X → Y₁) [IsSmoothT g₁]
  (g₂ : X → Y₂) [IsSmoothT g₂]
  : ∂ (λ x => f (g₁ x) (g₂ x)) 
    = 
    λ x dx => 
      let (y₁,dy₁) := 𝒯 g₁ x dx
      let (y₂,dy₂) := 𝒯 g₂ x dx
      let df := ∂ (uncurryN 2 f)
      -- let y₁ := g₁ x
      -- let dy₁ := ∂ g₁ x dx
      -- let y₂ := g₂ x
      -- let dy₂ := ∂ g₂ x dx
      df (y₁,y₂) (dy₁,dy₂)
      -- ∂ f y₁ dy₁ y₂ +  ∂ (f y₁) y₂ dy₂ 
  := sorry_proof

/-- Last resort theorem that changes tangent map to normal differential 

Bilinear maps should usually provide a rewrite rule for `𝒯 (uncurryN 2 f)`
-/
@[simp ↓ low-5, diff low-5]
theorem differential.of_uncurryN (f : Y₁ → Y₂ → Z) [∀ x, IsSmoothT (f x)] [IsSmoothT λ x => λ y ⟿ f x y]
  : ∂ (uncurryN 2 f) 
    =
    λ (y₁,y₂) (dy₁,dy₂) =>
    ∂ f y₁ dy₁ y₂ + ∂ (f y₁) y₂ dy₂
  := sorry_proof

@[simp ↓ low, diff low]
theorem differential.of_parm
  (f : X → α → Y) [IsSmoothT f] (a : α)
  : ∂ (λ x => f x a) = λ x dx => ∂ f x dx a := 
by
  rw[differential.of_swap (λ a x => f x a)]

@[simp ↓, diff]
theorem differential.of_eval
  (a : α)
  : ∂ (λ f : α → Y => f a) = λ _ df => df a := by simp


--------------------------------------------------------------------------------
-- Tangent Map Rules --
--------------------------------------------------------------------------------

@[simp ↓, diff]
theorem tangentMap.of_id
  : 𝒯 (λ x : X => x) = λ x dx => (x,dx)
  := by symdiff; done

@[simp ↓, diff]
theorem tangentMap.of_const (x : X)
  : 𝒯 (λ y : Y => x) = λ y dy => (x,0) 
  := by symdiff; done

@[simp ↓ low-3, diff]
theorem tangentMap.of_swap (f : α → X → Y) [∀ i, IsSmoothT (f i)]
  : 𝒯 (λ x a => f a x) = λ x dx => (λ a => f a x, λ a => ∂ (f a) x dx) 
  := by symdiff; done

set_option trace.Meta.Tactic.simp true in
set_option trace.Meta.Tactic.simp.unify false in
@[simp ↓ low-1, diff, simp_guard g (λ x => x)]
theorem tangentMap.of_comp
  (f : Y → Z) [IsSmoothT f] 
  (g : X → Y) [IsSmoothT g] 
  : 𝒯 (λ x => f (g x)) 
    = 
    λ x dx =>
      let (y,dy) := 𝒯 g x dx
      𝒯 f y dy
  := by unfold tangentMap; simp[tangentMap] --  debug_simp; symdiff_core; done


@[simp ↓ low-2, diff, simp_guard g₁ Prod.fst, g₂ Prod.snd]
theorem tangentMap.of_diag
  (f : Y₁ → Y₂ → Z) [∀ x, IsSmoothT (f x)] [IsSmoothT λ x => λ y ⟿ f x y]
  (g₁ : X → Y₁) [IsSmoothT g₁]
  (g₂ : X → Y₂) [IsSmoothT g₂]
  : 𝒯 (λ x => f (g₁ x) (g₂ x))
    = 
    λ x dx => 
      let (y₁,dy₁) := 𝒯 g₁ x dx
      let (y₂,dy₂) := 𝒯 g₂ x dx
      -- (f y₁ y₂, ∂ f y₁ dy₁ y₂ + ∂ (f y₁) y₂ dy₂)
      𝒯 (uncurryN 2 f) (y₁,y₂) (dy₁,dy₂)
  := by simp[tangentMap]; done

/-- Last resort theorem that changes tangent map to normal differential 

Bilinear maps should usually provide a rewrite rule for `𝒯 (uncurryN 2 f)`
-/
@[simp ↓ low-5, diff low-5]
theorem tangentMap.of_uncurryN (f : Y₁ → Y₂ → Z) [∀ x, IsSmoothT (f x)] [IsSmoothT λ x => λ y ⟿ f x y]
  : 𝒯 (uncurryN 2 f) 
    =
    λ (y₁,y₂) (dy₁,dy₂) =>
    (f y₁ y₂, ∂ f y₁ dy₁ y₂ + ∂ (f y₁) y₂ dy₂)
  := by simp[tangentMap]; done

@[simp ↓ low, diff]
theorem tangentMap.of_parm
  (f : X → α → Y) [IsSmoothT f] (a : α)
  : 𝒯 (λ x => f x a) = λ x dx => let (f',df') := 𝒯 f x dx; (f' a, df' a) 
  := by simp[tangentMap]; done

@[simp ↓, diff]
theorem tangentMap.of_eval
  (a : α)
  : 𝒯 (λ f : α → Y => f a) = λ f df => (f a, df a) := by simp

-- @[simp ↓ low, diff]
-- theorem uncurry.arg_xy.diff_simp
--   (f : X → Y → Z) [∀ x, IsSmoothT (f x)] [IsSmoothT λ x => λ y ⟿ f x y]
--   : ∂ (λ (xy : (X×Y)) => f xy.1 xy.2) = λ (x,y) (dx,dy) => ∂ f x dx y + ∂ (f x) y dy := sorry_proof

--   -- : ∂ (λ ((x,y) : (X×Y)) => f x y) = λ (x,y) (dx,dy) => ∂ f x dx y + ∂ (f x) y dy := sorry_proof 

-- @[simp ↓ low, diff]
-- theorem uncurry.arg_xy.parm1.diff_simp
--   (a : α)
--   (f : X → Y → α → Z) [∀ x, IsSmoothT (f x)] [IsSmoothT λ x => λ y ⟿ f x y]
--   : ∂ (λ (xy : (X×Y)) => f xy.1 xy.2 a) = λ (x,y) (dx,dy) => ∂ f x dx y a + ∂ (f x) y dy a := sorry_proof



--------------------------------------------------------------------------------

/-- Differential of linear function is the function itself.

This theorem is too general and we do not want to try to apply it 
every time we try to differentiate something. That is why it it has 
low priority and more importantly it asks for `IsLin` and not for `IsLinT`.
Only elementary functions(that are not composite composite) are allowed
to be differentiated with this theorem. -/

@[simp low, diff] 
theorem tangentMap_of_linear (f : X → Y) [IsLin f]
  : 𝒯 f = λ x dx => (f x, f dx) := by simp[tangentMap]; done


@[simp low, diff] 
theorem diff_of_linear_2_1 (f : X → Y → Z) [IsLinN 2 f] : ∂ f = λ _ dx _ => f dx 0 := sorry_proof
@[simp low, diff] 
theorem diff_of_linear_2_2 (f : X → Y → Z) [IsLinN 2 f] (x : X) : ∂ (λ y => f x y) = λ _ dy => f 0 dy := sorry_proof
