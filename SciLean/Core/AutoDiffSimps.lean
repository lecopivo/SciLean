import SciLean.Core.AdjDiff


namespace SciLean.AutoDiffSimp


-- Additional simp lemmas for automatic/symbolic differentiation

attribute [autodiff_simp] mul_one one_mul zero_add add_zero

attribute [autodiff_simp] fun_zero_eval fun_one_eval fun_neg_eval fun_add_eval fun_sub_eval fun_mul_eval fun_div_eval fun_hmul_eval

section VecSimps
variable {X} [Vec X]
@[simp,autodiff_simp] theorem one_smul (x : X) : (1 : ℝ) * x = x := sorry_proof
@[simp,autodiff_simp] theorem zero_smul (x : X) : (0 : ℝ) * x = (0 : X) := sorry_proof
@[simp,autodiff_simp] theorem smul_zero (r : ℝ) : r * (0 : X) = (0 : X) := sorry_proof
@[simp,autodiff_simp] theorem neg_one_smul (x : X) : (-1 : ℝ) * x = -x := sorry_proof

@[simp,autodiff_simp] theorem add_neg_sub (x y : X) : x + -y = x - y := sorry_proof
@[simp,autodiff_simp] theorem neg_add_sub (x y : X) : -x + y = y - x := sorry_proof

@[simp,autodiff_simp] theorem smul_smul_mul (r s: ℝ) (x : X) : r * (s * x) = ((r * s) * x) := sorry_proof

@[simp,autodiff_simp] theorem add_same_1 (a b : ℝ) (x : X) : a*x + b*x = (a+b)*x := sorry_proof
@[simp,autodiff_simp] theorem add_same_2 (a : ℝ) (x : X) : a*x + x = (a+1)*x := sorry_proof
@[simp,autodiff_simp] theorem add_same_3 (a : ℝ) (x : X) : x + a*x = (1+a)*x := sorry_proof
@[simp,autodiff_simp] theorem add_same_4 (x : X) : x + x = (2:ℝ)*x := sorry_proof

@[simp,autodiff_simp] theorem inner_real (x y : ℝ) : ⟪x,y⟫ = x*y := by rfl; done

end VecSimps


instance : Fact ((1:ℝ) ≠ 0) := sorry_proof
instance : Fact ((2:ℝ) ≠ 0) := sorry_proof
instance : Fact ((3:ℝ) ≠ 0) := sorry_proof

@[simp, autodiff_simp]
theorem mul_val_recip (x y : ℝ) [Fact (x≠0)] : x * (y/x) = y := sorry_proof

@[simp, autodiff_simp]
theorem mul_val_recip_alt (x y z : ℝ) [Fact (x≠0)] : x * (y/(x*z)) = y/z := sorry_proof

@[simp, autodiff_simp]
theorem mul_recip_val (x y : ℝ) [Fact (x≠0)]: (y/x) * x = 1 := sorry_proof

@[simp, autodiff_simp]
theorem mul_recip_val_alt (x y z : ℝ) [Fact (x≠0)]: (y/(x*z)) * x = y/z := sorry_proof




