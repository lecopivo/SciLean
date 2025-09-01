import SciLean.Core.FunctionTransformations
import SciLean.Modules.Prob.SimpAttr
import SciLean.Modules.Prob.FDRand

namespace SciLean.Prob

variable {R} [RealScalar R]


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
theorem fwdFDeriv_sub (f g : R → R) :
  fwdFDeriv ℝ (fun (x : R) => f x - g x)
  =
  fun x dx =>
    let ydy := fwdFDeriv ℝ f x dx
    let zdz := fwdFDeriv ℝ g x dx
    (ydy.1 - zdz.1, ydy.2 - zdz.2) := sorry

@[rand_AD ↓ low]
theorem fwdFDeriv_sub2_simple (c : R) :
  fwdFDeriv ℝ (HSub.hSub c)
  =
  fun x dx => (c - x, - dx) := sorry

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


variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace R X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedSpace R Y]

@[rand_AD ↓]
theorem fwdFDeriv_ite {c} [Decidable c] (f g : X → Y) :
  fwdFDeriv ℝ (fun (x : X) => if c then f x else g x)
  =
  fun x dx =>
    if c then fwdFDeriv ℝ f x dx else fwdFDeriv ℝ g x dx := sorry


@[rand_AD ↓]
theorem weightByDensity_fwdDeriv (p q : R) (f : X → Y×Y) :
    fwdFDeriv ℝ (fun x => weightByDensity' p q (f x))
    =
    fun x dx =>
      let ydy := fwdFDeriv ℝ f x dx
      (weightByDensity' p q ydy.1, weightByDensity' p q ydy.2) := sorry
