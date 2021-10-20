import SciLean.Categories
import SciLean.Operators.Adjoint

import Init.Classical

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]
variable {U V W : Type} [Hilbert U] [Hilbert V] [Hilbert W]

------------------
-- Differential --
------------------
noncomputable 
def differential (f : X → Y) (x dx : X) : Y := 
    match Classical.propDecidable (IsSmooth f) with
      | isTrue  h => sorry
      | _ => (0 : Y)

prefix:max "δ" => differential


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
def gradient (f : U → ℝ) : U → U := λ x => (δ f x)† 1

prefix:max "∇" => gradient


-----------------
-- Tangent Map --
-----------------
noncomputable 
def tangent_map (f : X → Y) : X×X → Y×Y := λ (x,dx) => (f x, δ f x dx)

prefix:max "𝓣" => tangent_map


-----------------
-- Tangent Map --
-----------------
noncomputable 
def backprop (f : U → V) : U → V×(V→U) := λ x => (f x, (δ f x)†)

prefix:max "𝓑" => backprop

-- special composition for backpropagation such that 𝓑(f ∘ g) = 𝓑f • 𝓑g
def backcomp (f : β → γ×(γ→β)) (g : α → β×(β→α)) : α → γ×(γ → α) := 
    λ a => 
        let (b, B) := g a
        let (c, C) := f b
        (c, B ∘ C)

infixr:90 " • "  => backcomp
