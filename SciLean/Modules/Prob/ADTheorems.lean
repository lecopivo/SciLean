import SciLean.Core
import SciLean.Modules.Prob.SimpAttr

namespace SciLean.Prob

variable {R} [IsROrC R]


@[rand_AD ↓]
theorem fwdFDeriv_id  :
  fwdFDeriv ℝ (fun (x : R) => x)
  =
  fun x dx => (x, dx) := sorry

@[rand_AD ↓]
theorem fwdFDeriv_const (y : R) :
  fwdFDeriv ℝ (fun (x : R) => y)
  =
  fun x dx => (y, 0) := sorry


@[rand_AD ↓ low]
theorem fwdFDeriv_add (f g : R → R) :
  fwdFDeriv ℝ (fun (x : R) => f x + g x)
  =
  fun x dx =>
    let ydy := fwdFDeriv ℝ f x dx
    let zdz := fwdFDeriv ℝ g x dx
    (ydy.1 + zdz.1, ydy.2 + zdz.2) := sorry

@[rand_AD ↓ low]
theorem fwdFDeriv_add2_simple (c : R) :
  fwdFDeriv ℝ (HAdd.hAdd c)
  =
  fun x dx => (c + x, dx) := sorry

@[rand_AD ↓ low]
theorem fwdFDeriv_mul (f g : R → R) :
  fwdFDeriv ℝ (fun (x : R) => f x * g x)
  =
  fun x dx =>
    let ydy := fwdFDeriv ℝ f x dx
    let zdz := fwdFDeriv ℝ g x dx
    (ydy.1 * zdz.1, (ydy.2 * zdz.1 + ydy.1 * zdz.2) ) := sorry

@[rand_AD ↓]
theorem fwdFDeriv_mul1 (f  : R → R) (c : R) :
  fwdFDeriv ℝ (fun (x : R) => f x * c)
  =
  fun x dx =>
    let ydy := fwdFDeriv ℝ f x dx
    (ydy.1 * c, ydy.2 * c) := sorry

@[rand_AD ↓]
theorem fwdFDeriv_mul2_simple (c : R) :
  fwdFDeriv ℝ (HMul.hMul c)
  =
  fun x dx =>
    (c * x, c * dx) := sorry

@[rand_AD ↓ low]
theorem fwdFDeriv_div (f g : R → R) :
  fwdFDeriv ℝ (fun (x : R) => f x / g x)
  =
  fun x dx =>
    let ydy := fwdFDeriv ℝ f x dx
    let zdz := fwdFDeriv ℝ g x dx
    (ydy.1 / zdz.1, (ydy.2 * zdz.1 - ydy.1 * zdz.2) / (zdz.1^2)) := sorry

@[rand_AD ↓]
theorem fwdFDeriv_div1 (f  : R → R) (c : R) :
  fwdFDeriv ℝ (fun (x : R) => f x / c)
  =
  fun x dx =>
    let ydy := fwdFDeriv ℝ f x dx
    (ydy.1 / c, ydy.2 / c) := sorry

@[rand_AD ↓]
theorem fwdFDeriv_neg (f : R → R) :
  fwdFDeriv ℝ (fun (x : R) => - f x)
  =
  fun x dx =>
    let ydy := fwdFDeriv ℝ f x dx
    (- ydy.1, - ydy.2) := sorry


@[rand_AD ↓]
theorem fwdFDeriv_neg_simple :
  fwdFDeriv ℝ (fun (x : R) => - x)
  =
  fun x dx =>
    (- x, - dx) := sorry
