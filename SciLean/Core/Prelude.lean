import Mathlib
import SciLean.Algebra

namespace SciLean

@[inline] 
def kron {ι} [DecidableEq ι] (i j : ι) : ℝ := if (i=j) then 1 else 0

class Fact (P : Prop) : Prop where
  proof : P

instance : Fact (x=x) := ⟨by rfl⟩

--- Bounded Types

macro "ℕ⁺" : term => `({n : ℕ // 0 < n})

macro "ℝ[" a:term "," b:term "]" : term => `({x : ℝ // $a ≤ x ∧ x ≤ $b})
macro "ℝ[" a:term "," b:term ")" : term => `({x : ℝ // $a ≤ x ∧ x < $b})
macro "ℝ(" a:term "," b:term "]" : term => `({x : ℝ // $a < x ∧ x ≤ $b})
macro "ℝ(" a:term "," b:term ")" : term => `({x : ℝ // $a < x ∧ x < $b})

macro "ℝ(" "-∞" "," b:term "]" : term => `({x : ℝ // x ≤ $b})
macro "ℝ(" "-∞" "," b:term ")" : term => `({x : ℝ // x < $b})
macro "ℝ(" a:term "," "∞" "]" : term => `({x : ℝ // $a ≤ x})
macro "ℝ(" a:term "," "∞" ")" : term => `({x : ℝ // $a < x})

macro "ℤ[" a:term "," b:term "]" : term => `({x : ℤ // $a ≤ x ∧ x ≤ $b})
macro "ℤ[" a:term "," b:term ")" : term => `({x : ℤ // $a ≤ x ∧ x < $b})
macro "ℤ(" a:term "," b:term "]" : term => `({x : ℤ // $a < x ∧ x ≤ $b})
macro "ℤ(" a:term "," b:term ")" : term => `({x : ℤ // $a < x ∧ x < $b})

macro "ℤ(" "-∞" "," b:term "]" : term => `({x : ℤ // x ≤ $b})
macro "ℤ(" "-∞" "," b:term ")" : term => `({x : ℤ // x < $b})
macro "ℤ(" a:term "," "∞" "]" : term => `({x : ℤ // $a ≤ x})
macro "ℤ(" a:term "," "∞" ")" : term => `({x : ℤ // $a < x})

