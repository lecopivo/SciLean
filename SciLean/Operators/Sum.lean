import SciLean.Mathlib.Data.Enumtype
import SciLean.Categories
import SciLean.Operators.Inverse

namespace SciLean

instance {X ι} [Vec X] [Enumtype ι] : IsLin (Enumtype.sum : (ι → X) → X) := sorry

@[inline] 
def kron {ι} [DecidableEq ι] (i j : ι) : ℝ := if (i==j) then 1 else 0



--- Sum simplifications ---
---------------------------
-- These theorems probably should not be under `simp` but under specialized tactic
-- For now, they are under `simp` to get some nice examples working

@[simp] 
theorem sum_into_lambda {X Y ι} [Enumtype ι] [Vec Y]
  (f : ι → X → Y)
  : (∑ i, λ j => f i j) = (λ j => ∑ i, f i j)
  := sorry

@[simp] 
theorem sum_of_sum {X ι} [Enumtype ι] [Vec X]
  (f g : ι → X)
  : (∑ i, f i + g i) = (∑ i, f i) + (∑ i, g i)
  := sorry


--- Kronecker delta simplifications ---
---------------------------------------
-- The idea behind these is that when ever we have a sum with kronecker
-- delta we want to get it to the form `∑ i, (kron i j) * (f i)`
-- Then it can be easily simplified to `f j`
section KronSimps

  -- TOOD: These theorems do not work properly with generic `Enumtype`
  -- I think it is a problem with `Iterable` as it has its own copy of
  -- DecEq and then there is a problem with unifications when combined 
  -- with `sum`
  variable {ι} [Enumtype ι] 
  variable {X} [Vec X]

  @[simp] 
  theorem kron_mul_assoc {i j : Fin n} (x y : ℝ) : (kron i j) * x * y = (kron i j) * (x * y) 
    := sorry

  @[simp] 
  theorem kron_smul_assoc {i j : Fin n} (r : ℝ) (x : X) : (kron i j) * r * x = (kron i j) * (r * x) 
    := sorry

  @[simp] 
  theorem kron_right_mul {i j : Fin n} (x : ℝ) : x * (kron i j)  = (kron i j) * x
    := sorry

  @[simp] 
  theorem kron_neg {i j : Fin n} : -(kron i j) = (kron i j) * (-1) 
    := sorry

  @[simp] 
  theorem kron_neg_mul {i j : Fin n} (x : X) : -(kron i j * x) = kron i j * (-x) 
    := sorry

end KronSimps

--- Sum & Kronecker delta simplifications ---
---------------------------------------------
-- These two theorems should 

section SumKronSimps

  -- variable {ι κ} [Enumtype ι] [Enumtype κ] [Inhabited ι]

  @[simp] 
  theorem sum_of_kron_1 {n} [NonZero n] 
    (g : Fin n → Fin n) [IsInv g]
    (j : Fin n)
    : (∑ i, kron (g i) j) = 1
    := sorry

  @[simp] 
  theorem sum_of_kron_2 {n} [NonZero n]
    {X} [Vec X] (f : ℝ → α → X) [IsLin f]
    (h : Fin n → α)
    (g : Fin n → Fin n) [IsInv g]
    (j : Fin n)
    : (∑ i, f (kron (g i) j) (h i)) = f 1 (h (g⁻¹ j))
    := sorry

end SumKronSimps

-- Ideal form of the theorem, but it does not unify properly
-- @[simp]
-- theorem sum_of_kron_ideal {n} [NonZero n]
--   {X} [Vec X] (f : ℝ → Fin n → Fin n → X) [IsLin f]
--   (g : Fin n → Fin n) [IsInv g]
--   (j : Fin n)
--   : (∑ i, f (kron (g i) j) i j) = f 1 (g⁻¹ j) j
--   := sorry


example [NonZero n] (j : Fin n) 
  : (∑ i : Fin n, kron (i+1) j) = 1
  :=
  by simp done


example [NonZero n] (j : Fin n) 
  : (∑ i : Fin n, i * (kron (i+1) j)) = (j-1)
  :=
  by simp done

example [NonZero n] (j : Fin n) 
  : (∑ i : Fin n, (kron (i+1) j) * i) = (j-1)
  :=
  by simp done
