import SciLean.Core.Functions.Operations
import SciLean.Core.Functions.Sum

namespace SciLean

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
  variable {ι} [DecidableEq ι] 
  variable {X} [Vec X]

  @[simp, simp_diff] 
  theorem kron_mul_assoc {i j : ι} (x y : ℝ) : (kron i j) * x * y = (kron i j) * (x * y) 
    := sorry

  @[simp, simp_diff] 
  theorem kron_smul_assoc {i j : ι} (r : ℝ) (x : X) : (kron i j) * r * x = (kron i j) * (r * x) 
    := sorry

  @[simp, simp_diff] 
  theorem kron_mul_assoc_mid (x : ℝ) (y : X) (i j : ι) 
    : x * ((kron i j) * y)  = (kron i j) * (x * y)
    := sorry

  @[simp, simp_diff] 
  theorem kron_mul_kron_add (x : ℝ) (y z : X) (i j k l : ι) 
    : x * (kron i j * y + kron k l * z) = (kron i j) * (x * y) + kron k l * (x * z)
    := sorry

  @[simp, simp_diff] 
  theorem kron_mul_kron_sub (x : ℝ) (y z : X) (i j k l : ι) 
    : x * (kron i j * y - kron k l * z) = (kron i j) * (x * y) - kron k l * (x * z)
    := sorry

  @[simp, simp_diff] 
  theorem kron_right_mul (x : ℝ) (i j : ι) : x * (kron i j)  = (kron i j) * x
    := sorry

  @[simp, simp_diff] 
  theorem kron_neg {i j : ι} : -(kron i j) = (kron i j) * (-1) 
    := sorry

  @[simp, simp_diff] 
  theorem kron_neg_mul {i j : ι} (x : X) : -(kron i j * x) = kron i j * (-x) 
    := sorry

end KronSimps

--- Sum & Kronecker delta simplifications ---
---------------------------------------------
-- These two theorems should 

section SumKronSimps

  -- -- Ideal form of the theorem, but it does not unify properly
  -- @[simp]
  -- theorem sum_of_kron_ideal {n} [Nonempty (Fin n)]
  --   {X} [Vec X] (f : ℝ → Fin n → Fin n → X) [IsLin f]
  --   (g : Fin n → Fin n) [IsInv g]
  --   (j : Fin n)
  --   : (∑ i, f (kron (g i) j) i j) = f 1 (g⁻¹ j) j
  --   := sorry

  @[simp, simp_diff] 
  theorem sum_of_kron_1 {ι} [Enumtype ι] [Nonempty ι] 
    (g : ι → ι) [IsInv g]
    (j : ι)
    : (∑ i, kron (g i) j) = 1
    := sorry

  @[simp, simp_diff] 
  theorem sum_of_kron_2 
    {ι} [Enumtype ι] [Nonempty ι]
    {κ} [Enumtype κ]
    {X} [Vec X] 
    (f : ℝ → α → X) [IsLin f]
    (h : ι → α)
    (g : ι → κ) [IsInv g]
    (j : κ)
    : (∑ i, f (kron (g i) j) (h i)) = f 1 (h (g⁻¹ j))
    := sorry

  @[simp, simp_diff] 
  theorem sum_of_kron_3
    {ι} [Enumtype ι] [Nonempty ι]
    {κ} [Enumtype κ]
    {X} [Vec X] 
    (f : ℝ → α → X) [IsLin f]
    (h : ι → α)
    (g : ι → κ) [IsInv g]
    (j : κ)
    : (∑ i, f (kron j (g i)) (h i)) = f 1 (h (g⁻¹ j))
    := sorry

end SumKronSimps


example [Nonempty (Fin n)] (j : Fin n) (f : Fin n → ℝ)
  : (∑ i : Fin n, kron i j * f i) = f j
  :=
  by simp done

example [Nonempty (Fin n)] (j : Fin n) 
  : (∑ i : Fin n, kron (i+1) j) = 1
  :=
  by simp done

-- example [Nonempty (Fin n)] (j : Fin n) 
--   : (∑ i : Fin n, i * (kron (i+1) j)) = j - 1
--   :=
--   by simp done

-- example [Nonempty (Fin n)] (j : Fin n) 
--   : (∑ i : Fin n, (kron (i+1) j) * i) = (j-1)
--   :=
--   by simp done

end SciLean
