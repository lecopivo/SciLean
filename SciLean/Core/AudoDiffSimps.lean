import SciLean.Core.AdjDiff


namespace SciLean


-- Additional simp lemmas for automatic/symbolic differentiation




namespace VecSimps
variable {X} [Vec X]
@[simp,autodiff] theorem one_smul (x : X) : (1 : ℝ) * x = x := sorry
@[simp,autodiff] theorem zero_smul (x : X) : (0 : ℝ) * x = (0 : X) := sorry
@[simp,autodiff] theorem smul_zero (r : ℝ) : r * (0 : X) = (0 : X) := sorry
@[simp,autodiff] theorem neg_one_smul (x : X) : (-1 : ℝ) * x = -x := sorry

@[simp,autodiff] theorem add_neg_sub (x y : X) : x + -y = x - y := sorry
@[simp,autodiff] theorem neg_add_sub (x y : X) : -x + y = y - x := sorry

@[simp,autodiff] theorem smul_smul_mul (r s: ℝ) (x : X) : r * (s * x) = ((r * s) * x) := sorry


@[simp,autodiff] theorem add_same_1 (a b : ℝ) (x : X) : a*x + b*x = (a+b)*x := sorry
@[simp,autodiff] theorem add_same_2 (a : ℝ) (x : X) : a*x + x = (a+1)*x := sorry
@[simp,autodiff] theorem add_same_3 (a : ℝ) (x : X) : x + a*x = (1+a)*x := sorry
@[simp,autodiff] theorem add_same_4 (x : X) : x + x = (2:ℝ)*x := sorry


end VecSimps

