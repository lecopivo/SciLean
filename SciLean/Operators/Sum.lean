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
theorem sum_of_const {X ι} [Enumtype ι] [Vec X] (x : X)
  : (∑ i : ι, x) = (Enumtype.numOf ι : ℝ) * x
  := sorry

@[simp] 
theorem sum_into_lambda {X Y ι} [Enumtype ι] [Vec Y]
  (f : ι → X → Y)
  : (∑ i, λ j => f i j) = (λ j => ∑ i, f i j)
  := sorry

@[simp] 
theorem sum_of_add {X ι} [Enumtype ι] [Vec X]
  (f g : ι → X)
  : (∑ i, f i + g i) = (∑ i, f i) + (∑ i, g i)
  := sorry

@[simp] 
theorem sum_of_sub {X ι} [Enumtype ι] [Vec X]
  (f g : ι → X)
  : (∑ i, f i - g i) = (∑ i, f i) - (∑ i, g i)
  := sorry

@[simp] 
theorem sum_of_smul {X ι} [Enumtype ι] [Vec X]
  (f : ι → X) (c : ℝ)
  : (∑ i, c * f i ) = c * (∑ i, f i)
  := sorry

@[simp]
theorem sum_of_neg {X ι} [Enumtype ι] [Vec X]
  (f : ι → X)
  : (∑ i, - f i ) = - (∑ i, f i)
  := sorry

-- @[simp low]
-- This can loop together with `sum_into_lambda`
theorem sum_of_linear {X Y ι} [Enumtype ι] [Vec X] [Vec Y]
  (f : X → Y) [IsLin f]
  (g : ι → X)
  : (∑ i, f (g i)) = f (∑ i, g i)
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
  variable {ι} [DecidableEq ι] 
  variable {X} [Vec X]

  @[simp] 
  theorem kron_mul_assoc {i j : ι} (x y : ℝ) : (kron i j) * x * y = (kron i j) * (x * y) 
    := sorry

  @[simp] 
  theorem kron_smul_assoc {i j : ι} (r : ℝ) (x : X) : (kron i j) * r * x = (kron i j) * (r * x) 
    := sorry

  @[simp] 
  theorem kron_mul_assoc_mid (x : ℝ) (y : X) (i j : ι) 
    : x * ((kron i j) * y)  = (kron i j) * (x * y)
    := sorry

  @[simp] 
  theorem kron_mul_kron_add (x : ℝ) (y z : X) (i j k l : ι) 
    : x * (kron i j * y + kron k l * z) = (kron i j) * (x * y) + kron k l * (x * z)
    := sorry

  @[simp] 
  theorem kron_mul_kron_sub (x : ℝ) (y z : X) (i j k l : ι) 
    : x * (kron i j * y - kron k l * z) = (kron i j) * (x * y) - kron k l * (x * z)
    := sorry

  @[simp] 
  theorem kron_right_mul (x : ℝ) (i j : ι) : x * (kron i j)  = (kron i j) * x
    := sorry

  @[simp] 
  theorem kron_neg {i j : ι} : -(kron i j) = (kron i j) * (-1) 
    := sorry

  @[simp] 
  theorem kron_neg_mul {i j : ι} (x : X) : -(kron i j * x) = kron i j * (-x) 
    := sorry

end KronSimps

--- Sum & Kronecker delta simplifications ---
---------------------------------------------
-- These two theorems should 

section SumKronSimps

  -- TODO: Switch to Enumtype instead of Fin.
  --       What was the problem with Enumtype?
  -- variable {ι κ} [Enumtype ι] [Enumtype κ] [Inhabited ι]

  @[simp] 
  theorem sum_of_kron_1 {n} [NonZero n] 
    (g : Fin n → Fin n) [IsInv g]
    (j : Fin n)
    : (∑ i, kron (g i) j) = 1
    := sorry

  @[simp] 
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

  @[simp] 
  theorem sum_of_kron_2''
    {ι} [Enumtype ι] [Nonempty ι]
    {κ} [Enumtype κ]
    {X} [Vec X] 
    (f : ℝ → α → X) [IsLin f]
    (h : ι → α)
    (g : ι → κ) [IsInv g]
    (j : κ)
    : (∑ i, f (kron j (g i)) (h i)) = f 1 (h (g⁻¹ j))
    := sorry


  @[simp] 
  theorem sum_of_kron_2' {n} [NonZero n]
    {X} [Vec X] (f : ℝ → α → X) [IsLin f]
    (h : Fin n → α)
    (g : Fin n → Fin n) [IsInv g]
    (j : Fin n)
    : (∑ i, f (kron (g i) j) (h i)) = f 1 (h (g⁻¹ j))
    := sorry -- Why it this not done with 

  @[simp] 
  theorem sum_of_kron_1' {ι} [Enumtype ι] [Nonempty ι]
    (g : ι → ι) [IsInv g]
    (j : ι)
    : (∑ i, kron (g i) j) = 1
    := sorry

  theorem sum_of_kron_1'' {ι} [Enumtype ι] [Nonempty ι]
    (g : ι → ι) [IsInv g]
    (j : ι)
    : (∑ i, kron (g i) j) = 1
    := by simp; done

end SumKronSimps

-- Ideal form of the theorem, but it does not unify properly
-- @[simp]
-- theorem sum_of_kron_ideal {n} [NonZero n]
--   {X} [Vec X] (f : ℝ → Fin n → Fin n → X) [IsLin f]
--   (g : Fin n → Fin n) [IsInv g]
--   (j : Fin n)
--   : (∑ i, f (kron (g i) j) i j) = f 1 (g⁻¹ j) j
--   := sorry

example [NonZero n] (j : Fin n) (f : Fin n → ℝ)
  : (∑ i : Fin n, kron i j * f i) = f j
  :=
  by simp done

example [NonZero n] (j : Fin n) 
  : (∑ i : Fin n, kron (i+1) j) = 1
  :=
  by simp done

-- set_option trace.Meta.Tactic.simp true in
example [NonZero n] (j : Fin n) 
  : (∑ i : Fin n, i * (kron (i+1) j)) = (j-1)
  :=
  by simp; done

example [NonZero n] (j : Fin n) 
  : (∑ i : Fin n, (kron (i+1) j) * i) = (j-1)
  :=
  by simp done

--- TODO: add tactics sum_together sum_apart sum_expand 
end SciLean

-- def kron' (i j : Int) : Float := if (i=j) then 1 else 0
-- def kron'' (i j : α) [DecidableEq α] : Float := if (i=j) then 1 else 0

-- class Foo (α : Type) where
--   decEq : DecidableEq α

-- instance {α} [Foo α] : DecidableEq α := Foo.decEq
-- instance {n} : Foo (Fin n) := ⟨by infer_instance⟩

-- @[simp] 
-- theorem kron'_right_mul {i j : Int} (x : Float) : x * kron' i j = kron' i j * x := sorry
-- @[simp] 
-- theorem kron''_right_mul {i j : α} [Foo α] (x : Float) : x * kron'' i j = kron'' i j * x := sorry

-- #check Iterable
-- def Int.toFloat : Int → Float
-- | Int.ofNat   n => n.toFloat
-- | Int.negSucc n => - (n + 1).toFloat

-- instance : Coe Int Float := ⟨λ i => i.toFloat⟩

-- variable (i : Int)

-- set_option trace.Meta.isDefEq true in
-- example {i j : Fin n} : (i) * kron'' i j = kron'' i j * (i) := 
-- by
--   -- simp
--   rw[kron''_right_mul]


-- -- @[inline] 
-- -- def kron {ι} [DecidableEq ι] (i j : ι) : ℝ := if (i==j) then 1 else 0

-- example (P : Prop) (f g : α → P) : f = g := 
-- by
--   simp
--   done

-- example (P : Prop) : ∀ (a b : Decidable P), a = b := 
-- by intro a b; 
--    induction a; 
--    induction b;
--    simp (discharger := assumption)
--    simp
   

-- example : DecidableEq ℕ := by infer_instance

-- #check instDecidableEqNat

-- variable (a b : ℕ) (P : Prop) (a b : Decidable P)

-- class Foo (α : Type) where
--   dec_eq : DecidableEq α

-- instance : Foo ℕ := { dec_eq := by infer_instance }

-- example : decide (1=1) (h := instDecidableEqNat 1 1) = decide (1=1) (h := instFooNat.dec_eq 1 1) := by simp

-- example :  = decide (1=1) (h := b) := by simp
