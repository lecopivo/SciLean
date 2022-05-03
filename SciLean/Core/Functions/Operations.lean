import SciLean.Core.IsSmooth
import SciLean.Core.IsLin
import SciLean.Core.HasAdjoint

import SciLean.Core.Diff
import SciLean.Core.Adjoint
import SciLean.Core.AdjDiff

namespace SciLean


-- Negation --
--------------

function_properties Neg.neg {X : Type} (x : X) : X
argument x [Vec X]
  isLin      := sorry,
  isSmooth   := sorry,
  diff_simp  := - dx by sorry
argument x [SemiHilbert X]
  hasAdjoint := sorry,
  adj_simp   := - x' by sorry


-- Multiplication --
--------------------

function_properties HMul.hMul {X : Type} (x : ℝ) (y : X) : X
argument x [Vec X] 
  isLin      := sorry,
  isSmooth   := sorry, 
  diff_simp  := dx * y by sorry
argument x [Hilbert X]
  hasAdjoint := sorry,
  adj_simp   := ⟪x', y⟫ by sorry
argument y [Vec X]
  isLin      := sorry,
  isSmooth   := sorry,
  diff_simp  := x * dy by sorry
argument y [SemiHilbert X]
  hasAdjoint := sorry,
  adj_simp   := x * y' by sorry


-- Addition --
--------------

function_properties HAdd.hAdd {X : Type} [Vec X] (x y : X) : X
argument x
  isSmooth  := sorry, 
  diff_simp := dx by sorry
  -- isInv       := sorry
  -- inv         := x' - y
argument y
  isSmooth  := sorry,
  diff_simp := dy by sorry
  -- isInv       := sorry
  -- inv         := y' - x
-- argument x y
--   isLin

instance HAdd.hAdd.arg_xy.hasAdjoint {X} [SemiHilbert X] 
  : HasAdjoint (λ ((x, y) : (X × X)) => x + y) := sorry

@[simp] theorem HAdd.hAdd.arg_xy.adj_simp {X} [SemiHilbert X] 
  : (Function.uncurry HAdd.hAdd)† = λ xy' : X => (xy', xy') := sorry

-- function_properties HAdd.hAdd {X : Type} [SemiHilbert X] (x y : X) : X
--   hasAdjoint


-- Subtraction --
-----------------

function_properties HSub.hSub {X : Type} [Vec X] (x y : X) : X
argument x
  isSmooth  := sorry, 
  diff_simp := dx by sorry
  -- isInv       := sorry
  -- inv         := x' + y
  
argument y
  isSmooth  := sorry,
  diff_simp := - dy by sorry
  -- isInv       := sorry
  -- inv         := y' + x
-- argument x y
--   isLin

instance HSub.hSub.arg_xy.hasAdjoint {X} [SemiHilbert X] 
  : HasAdjoint (λ ((x, y) : (X × X)) => x - y) := sorry

@[simp] theorem HSub.hSub.arg_xy.adj_simp {X} [SemiHilbert X] 
  : (Function.uncurry HSub.hSub)† = λ xy' : X => (xy', - xy') := sorry

-- function_properties HSub.hSub {X : Type} [SemiHilbert X] (x y : X) : X
-- argument x y
--   hasAdjoint

-- Inner product --
-------------------

function_properties SemiInner.semiInner {X} [Hilbert X] (x y : X) (Ω : 𝓓 X) : ℝ
argument x
  isLin       := sorry,
  isSmooth    := sorry,
  hasAdjoint  := sorry,
  diff_simp   := ⟪dx, y⟫[Ω] by sorry,
  adj_simp    := x' * y by sorry
argument y    
  isLin       := sorry,
  isSmooth    := sorry,
  hasAdjoint  := sorry,
  diff_simp   := ⟪x, dy⟫[Ω] by sorry,
  adj_simp    := y' * x by sorry

-- variable {α β γ : Type}
-- variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]

-- variable (f : Y → Z) [IsSmooth f]
-- variable (F : X → Y → Z) [IsSmooth F] [∀ x, IsSmooth (F x)]

-- example g dg x : δ (λ (g : X → Y) => f (g x)) g dg = δ f (g x) (dg x) := by simp done
-- example (r dr : ℝ) : δ (λ x : ℝ => x*x*x + x) r dr = (dr * r + r * dr) * r + r * r * dr + dr := by simp done
-- example g dg y : δ (λ (g : X → X) (x : X) => F (g x) y) g dg x = δ F (g x) (dg x) y := by simp done 

-- noncomputable
-- @[reducible]
-- abbrev grad [SemiHilbert X] (f : X → ℝ) : X → X := λ x => δ† f x (1:ℝ)


set_option trace.Meta.Tactic.simp.discharge true in
example (y : X) [Hilbert X]
  : 
    ∇ (λ x : X => ⟪x,x⟫ * ⟪x,x⟫) = 0
  := by simp[adjointDifferential]; unfold hold; simp; done
