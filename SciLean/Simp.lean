import Mathlib.Data.Prod
import Mathlib.Logic.Function.Basic

import SciLean.Algebra

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]
variable {U V W : Type} [Hilbert U] [Hilbert V] [Hilbert W]

variable (u : U)
variable (r : ℝ)

@[simp] theorem add_zero (x : X) : x + 0 = x := by simp
@[simp] theorem zero_add (x : X) : 0 + x = x := by simp 

@[simp] theorem sub_zero (x : X) : x - 0 = x := sorry
@[simp] theorem zero_sub (x : X) : 0 - x = -x := sorry

@[simp] theorem zero_mul (x : X) : (0 : ℝ)*x = (0 : X) := sorry
-- @[simp] theorem mul_zero (r : ℝ) : r*(0:ℝ) = (0 : ℝ) := by simp

@[simp] theorem zero_eval [Zero β] : (0 : α → β) a = 0 := by simp[Zero.zero,OfNat.ofNat]; done

@[simp] theorem mul_one' (x : ℝ) : x * 1 = x := by simp
@[simp] theorem one_mul (x : X) : (1:ℝ) * x = x := sorry
@[simp] theorem neg_one_mul (x : X) : (-1:ℝ) * x = -x := sorry

@[simp] theorem div_one (x : ℝ) : x/1 = x := sorry

-- @[simp] theorem mul_one (r : ℝ) : r * (1:ℝ) = r := sorry

-- @[simp] theorem neg_neg (x : X) : - - x = x := by simp

@[simp] theorem sub_neg (x y : X) : x - (-y) = x + y := sorry 
@[simp] theorem add_neg (x y : X) : x + (-y) = x - y := sorry
@[simp] theorem neg_sub (x y : X) : -x - y = -(x + y) := sorry 

@[simp] theorem eval_neg (f : α → X) (x : α) : (-f) x = -(f x) := sorry

@[simp] theorem mul_neg_neg (r : ℝ) (x : X) : (-r) * (-x) = r * x := sorry
theorem mul_neg_1 (r : ℝ) (x : X) : (-r) * x = -(r * x) := sorry
theorem mul_neg_2 (r : ℝ) (x : X) : r * (-x) = -(r * x) := sorry
theorem smul_smul_mul (r s: ℝ) (x : X) : r * (s * x) = ((r * s) * x) := sorry

@[simp] theorem pair_mul (r : ℝ) (x : X) (y : Y) : r * (x, y) = (r * x, r * y) := sorry

@[simp] theorem inner_mul_1 {X} [SemiHilbert X] (r : ℝ) (x y : X) Ω : ⟪r * x, y⟫[Ω] = r * ⟪x,y⟫[Ω] := sorry
@[simp] theorem inner_mul_2 {X} [SemiHilbert X] (r : ℝ) (x y : X) Ω : ⟪x, r * y⟫[Ω] = r * ⟪x,y⟫[Ω] := sorry
@[simp] theorem inner_zero1 {X} [SemiHilbert X] (x : X) Ω : ⟪(0 : X), x⟫[Ω] = 0 := sorry
@[simp] theorem inner_zero2 {X} [SemiHilbert X] (x : X) Ω : ⟪x, (0 : X)⟫[Ω] = 0 := sorry

@[simp] theorem inner_prod (u u' : U) (v v' : V) : ⟪(u,v), (u',v')⟫ = ⟪u,u'⟫ + ⟪v,v'⟫ := sorry
@[simp] theorem inner_real (x y : ℝ) : ⟪x, y⟫ = x * y := sorry
@[simp] theorem square_sqrt_square (x : ℝ) : (Math.sqrt (x * x))^2 = x * x := sorry

@[simp] theorem add_same_1 (a b : ℝ) (x : X) : a*x + b*x = (a+b)*x := sorry
@[simp] theorem add_same_2 (a : ℝ) (x : X) : a*x + x = (a+1)*x := sorry
@[simp] theorem add_same_3 (a : ℝ) (x : X) : x + a*x = (1+a)*x := sorry
@[simp] theorem add_same_4 (x : X) : x + x = (2:ℝ)*x := sorry

-- @[simp] theorem smul_smul_mul (a b : ℝ) (x : X) : a * (b * x) = (a*b) * x := sorry

@[simp] theorem prod_sum (x x' : X) (y y' : Y) : (x, y) + (x', y') = (x + x', y + y') := sorry
@[simp] theorem prod_fst_hmul (x : X) (y : Y) (r : ℝ) : (r*(x,y)).fst = r*x := sorry
@[simp] theorem prod_snd_hmul (x : X) (y : Y) (r : ℝ) : (r*(x,y)).snd = r*y := sorry

@[simp] theorem add_normalize [Add α] (a b : α) : Add.add a b = a + b := by simp[HAdd.hAdd] done
@[simp] theorem sub_normalize [Sub α] (a b : α) : Sub.sub a b = a - b := by simp[HSub.hSub] done
@[simp] theorem mul_normalize [Mul α] (a b : α) : Mul.mul a b = a * b := by simp[HMul.hMul] done
@[simp] theorem div_normalize [Div α] (a b : α) : Div.div a b = a / b := by simp[HDiv.hDiv] done
