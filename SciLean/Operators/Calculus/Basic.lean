import Lean
import SciLean.Categories
import SciLean.Operators.Adjoint

import Init.Classical

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]
variable {U V W : Type} [SemiHilbert U] [SemiHilbert V] [SemiHilbert W]

------------------
-- Differential --
------------------
-- @[irreducible] -- this does not work work as intended and I switched to `constant`
noncomputable 
constant differential (f : X → Y) (x dx : X) : Y := 
    match Classical.propDecidable (IsSmooth f) with
      | isTrue  h => sorry
      | _ => (0 : Y)

prefix:max "δ" => differential


--------------------------
-- Adjoint Differential --
--------------------------
noncomputable 
def adjoint_differential (f : U → V) (x : U) (dy : V) : U := (δ f x)† dy

prefix:max "δ†" => adjoint_differential


----------------
-- Derivative --
----------------
noncomputable 
def derivative (f : ℝ → X) : ℝ → X := λ t => δ f t 1

prefix:max "ⅆ" => derivative


--------------
-- Gradient --
-------------- 
noncomputable
abbrev gradient [Hilbert U] (f : U → ℝ) : U → U := λ x => δ† f x 1

prefix:max "∇" => gradient


------------------
-- Forward mode --
------------------
noncomputable 
def forward_diff (f : X → Y) : X×X → Y×Y := λ (x,dx) => (f x, δ f x dx)

prefix:max "𝓣" => forward_diff

------------------
-- Reverse Mode --
------------------
open SemiInner in
noncomputable 
def reverse_diff 
  (f : U → V) : U → V × (V → U) := λ x => (f x, δ† f x)

prefix:max "𝓑" => reverse_diff

-- special composition for backpropagation such that 𝓑(f ∘ g) = 𝓑f • 𝓑g
def reverse_comp (f : β → γ×(γ→β)) (g : α → β×(β→α)) : α → γ×(γ → α) := 
    λ a => 
        let (b, B) := g a
        let (c, C) := f b
        (c, B ∘ C)

infixr:90 " • "  => reverse_comp
