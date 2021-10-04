import SciLean.Prelude

import SciLean.Linear
import SciLean.Smooth
import SciLean.Invert

import SciLean.Solver
import SciLean.Meta

import SciLean.Simp

import SciLean.Math.Basic

-- def sum {n α} [Zero α] [Add α] (f : Fin n → α) : α := do
--   let mut r := zero 
--   for i in [0:n] do
--     r := r + f ⟨i, sorry⟩
--   r
--   -- match n with
--   --   | 0 => zero
--   --   | 1 => f ⟨0, sorry⟩
--   --   | n+1 => (sum (λ i : Fin n => f ⟨i, sorry⟩)) + f ⟨n, sorry⟩

-- macro "∑" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders `sum xs b

-- def big_product {n α} [One α] [Mul α] (f : Fin n → α) : α :=
--   match n with
--     | 0 => one
--     | 1 => f ⟨0, sorry⟩
--     | n+1 => (big_product (λ i : Fin n => f ⟨i, sorry⟩)) * f ⟨n, sorry⟩

-- macro "∏" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders `big_product xs b




