import Lean
import SciLean.Categories
import SciLean.Operators.Adjoint

import Init.Classical

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]
variable {U V W : Type} {S} [Vec S.R] [SemiHilbert' U S] [SemiHilbert' V S] [SemiHilbert' W S]

------------------
-- Differential --
------------------
-- @[irreducible] -- this does not work work as intended and I switched to `constant`
noncomputable 
constant differential (f : X → Y) (x dx : X) : Y := 
    match Classical.propDecidable (IsSmooth f) with
      | isTrue  h => sorry
      | _ => (0 : Y)

-- noncomputable
-- def Smooth.diff (f : X ⟿ Y) : (X ⟿ X ⊸ Y) := ⟨λ x => ⟨λ dx => differential f.1 x dx, sorry⟩, sorry⟩
-- Can we have unified 

-- class Differential (Hom : Type → Type → Type) (X Y : Type) where
--   diff (f : Hom X Y) : (Hom X (Hom X Y))

-- attribute [reducible] Differential.diff

-- @[reducible]
-- noncomputable
-- instance instNormalDiff : Differential (λ X Y : Type => X → Y) X Y:=
-- {
--   diff := (differential : (X → Y) → X → X → Y)
-- }

-- @[reducible]
-- noncomputable
-- instance instSmoothDiff : Differential (λ X Y : Type => X ⟿ Y) X Y:=
-- {
--   diff := λ f => Smooth.diff f
-- }

-- #check Differential.

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
abbrev gradient [Hilbert U] (f : U → ℝ) : U → U := λ x => (δ f x)† 1

prefix:max "∇" => gradient


------------------
-- Forward mode --
------------------
noncomputable 
def tangent_map (f : X → Y) : X×X → Y×Y := λ (x,dx) => (f x, δ f x dx)

prefix:max "𝓣" => tangent_map

------------------
-- Reverse Mode --
------------------
noncomputable 
def backprop {U V} [PairTrait U V] [Vec (sig U V).R] 
  [SemiHilbert' U (sig U V)] [SemiHilbert' V (sig U V)]
  (f : U → V) : U → V×(V→U) := λ x => (f x, (δ f x)†)

prefix:max "𝓑" => backprop

-- special composition for backpropagation such that 𝓑(f ∘ g) = 𝓑f • 𝓑g
def backcomp (f : β → γ×(γ→β)) (g : α → β×(β→α)) : α → γ×(γ → α) := 
    λ a => 
        let (b, B) := g a
        let (c, C) := f b
        (c, B ∘ C)

infixr:90 " • "  => backcomp


--- Maybe add other operators based on: 
--- "The simple essence of automatic differentiation" 
--- https://arxiv.org/abs/1804.00746

noncomputable 
def tangent_map_2 (f : X → Y) : X×X×X → Y×Y×Y := λ (x,dx,ddx) => (f x, δ f x dx, δ (δ f) x dx dx)

prefix:max "𝓓" => tangent_map_2
