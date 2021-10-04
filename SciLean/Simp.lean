import SciLean.Algebra

variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]

@[simp] theorem add_zero (x : X) : x + 0 = x := sorry
@[simp] theorem zero_add (x : X) : 0 + x = x := sorry

@[simp] theorem mul_one (x : ℝ) : x * 1 = x := sorry
@[simp] theorem one_mul (x : X) : (1:ℝ) * x = x := sorry

@[simp] theorem add_same_1 (a b : ℝ) (x : X) : a*x + b*x = (a+b)*x := sorry
@[simp] theorem add_same_2 (a : ℝ) (x : X) : a*x + x = (a+1)*x := sorry
@[simp] theorem add_same_3 (a : ℝ) (x : X) : x + a*x = (1+a)*x := sorry
@[simp] theorem add_same_4 (x : X) : x + x = (2:ℝ)*x := sorry

@[simp] theorem smul_smul_mul (a b : ℝ) (x : X) : a * (b * x) = (a*b) * x := sorry

@[simp] theorem prod_sum (x x' : X) (y y' : Y) : (x, y) + (x', y') = (x + x', y + y') := sorry

-- @[simp] theorem real_nat_mul (n m : Nat) : ((OfNat.ofNat n) : ℝ) * ((OfNat.ofNat m) : ℝ) = (( (m*n)) : ℝ) := sorry


