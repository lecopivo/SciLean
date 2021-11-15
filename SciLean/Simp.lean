import SciLean.Algebra

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]
variable {U V W : Type} [Hilbert U] [Hilbert V] [Hilbert W]

@[simp] theorem add_zero (x : X) : x + 0 = x := sorry
@[simp] theorem zero_add (x : X) : 0 + x = x := sorry

@[simp] theorem mul_one (x : ℝ) : x * 1 = x := sorry
@[simp] theorem one_mul (x : X) : (1:ℝ) * x = x := sorry

@[simp] theorem neg_neg (x : X) : - - x = x := sorry

@[simp] theorem neg_sub (x y : X) : x - (-y) = x + y := sorry
@[simp] theorem add_neg (x y : X) : x + (-y) = x - y := sorry

@[simp] theorem mul_neg_neg (r : ℝ) (x : X) : (-r) * (-x) = r * x := sorry
@[simp] theorem mul_neg_1 (r : ℝ) (x : X) : (-r) * x = -(r * x) := sorry
@[simp] theorem mul_neg_2 (r : ℝ) (x : X) : r * (-x) = -(r * x) := sorry

@[simp] theorem pair_mul (r : ℝ) (x : X) (y : Y) : (r * x, r * y) = r * (x, y) := sorry

@[simp] theorem inner_mul_1 (r : ℝ) (x y : U) : ⟨r * x, y⟩ = r * ⟨x,y⟩ := sorry
@[simp] theorem inner_mul_2 (r : ℝ) (x y : U) : ⟨x, r * y⟩ = r * ⟨x,y⟩ := sorry

@[simp] theorem inner_prod (u u' : U) (v v' : V) : ⟨(u,v), (u',v')⟩ = ⟨u,u'⟩ + ⟨v,v'⟩ := sorry
@[simp] theorem inner_real (x y : ℝ) : ⟨x, y⟩ = x * y := sorry

@[simp] theorem add_same_1 (a b : ℝ) (x : X) : a*x + b*x = (a+b)*x := sorry
@[simp] theorem add_same_2 (a : ℝ) (x : X) : a*x + x = (a+1)*x := sorry
@[simp] theorem add_same_3 (a : ℝ) (x : X) : x + a*x = (1+a)*x := sorry
@[simp] theorem add_same_4 (x : X) : x + x = (2:ℝ)*x := sorry

@[simp] theorem smul_smul_mul (a b : ℝ) (x : X) : a * (b * x) = (a*b) * x := sorry

@[simp] theorem prod_sum (x x' : X) (y y' : Y) : (x, y) + (x', y') = (x + x', y + y') := sorry

@[simp] theorem func_add_eval (f g : α → X) (a : α) : (f + g) a = f a + g a := by simp[HAdd.hAdd,Add.add]; done
@[simp] theorem func_sub_eval (f g : α → X) (a : α) : (f - g) a = f a - g a := by simp[HSub.hSub,Sub.sub]; done
@[simp] theorem func_mul_eval (f : α → X) (a : α) (c : ℝ) : (c*f) a = c * (f a) := by simp[HMul.hMul,Mul.mul]; done

@[simp] theorem composition_eval {α β γ} (f : β → γ) (g : α → β) (a : α) : (f ∘ g) a = f (g a) := by simp
