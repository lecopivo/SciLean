import SciLean.Operators.Adjoint.Combinators

open Function
namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [Hilbert X] [Hilbert Y] [Hilbert Z]

namespace Adjoint

  variable (f g : X → Y) 
  variable (r : ℝ)

  @[simp]
  theorem adjoint_of_hadd : (λ x : X×X => x.1 + x.2)† = (λ x => (x,x)) := sorry
  @[simp]
  theorem adjoint_of_add : (λ x : X×X => Add.add x.1 x.2)† = (λ x => (x,x)) := sorry
  @[simp]
  theorem adjoint_of_add_of_fun [IsLin f] [IsLin g] : (f + g)† = f† + g† := by simp[HAdd.hAdd, Add.add]; funext a; simp
  @[simp]
  theorem adjoint_of_add_of_fun_arg [IsLin f] [IsLin g] : (λ x => f x + g x)† = (λ y => f† y + g† y) := by simp[HAdd.hAdd, Add.add]; funext a; simp
  @[simp]
  theorem adjoint_of_add_of_fun_arg_parm (f g : X → Fin n → Y) [IsLin f] [IsLin g] 
      : (λ x i => f x i + g x i)† = (λ x i => f x i)† + (λ x i => g x i)† := by funext z; simp

  @[simp]
  theorem adjoint_of_hsub : (λ x : X×X => x.1 - x.2)† = (λ x => (x,-x)) := sorry
  @[simp]
  theorem adjoint_of_sub : (λ x : X×X => Sub.sub x.1 x.2)† = (λ x => (x,-x)) := sorry
  @[simp]
  theorem adjoint_of_sub_of_fun [IsLin f] [IsLin g] : (f - g)† = f† - g† := sorry -- by funext y; simp[HSub.hSub, Sub.sub]
  @[simp]
  theorem adjoint_of_sub_of_fun_arg [IsLin f] [IsLin g] : (λ x => f x - g x)† = λ y => f† y - g† y := sorry -- by funext y; simp[pmap, uncurry]; done
  @[simp]
  theorem adjoint_of_sub_of_fun_arg_parm (f g : X → Fin n → Y) [IsLin f] [IsLin g] 
      : (λ x i => f x i - g x i)† = (λ x i => f x i)† - (λ x i => g x i)† := sorry -- by funext z; simp[pmap, uncurry]; done

  @[simp]
  theorem adjoint_of_hmul_1 (f : X → ℝ) [IsLin f] (y : Y) : (λ x => (f x)*y)† = f† ∘ (λ y' => ⟨y,y'⟩) := sorry
  @[simp]
  theorem adjoint_of_hmul_1_parm (f : X → Fin i → ℝ) [IsLin f] (y : Fin i → Y) 
      : (λ x i => (f x i)*(y i))† = f† ∘ (λ y' i => ⟨y i,y' i⟩) := sorry
  @[simp]
  theorem adjoint_of_hmul_2 : (HMul.hMul r : X → X)† = HMul.hMul r := sorry
  @[simp]
  theorem adjoint_of_hmul_of_fun [IsLin f] : (r*f)† = r*f† := sorry -- by funext y; simp[HMul.hMul, Mul.mul]
  @[simp]
  theorem adjoint_of_hmul_of_fun_arg [IsLin f] (r : ℝ) : (λ x => r*(f x))† = (λ y => r*(f† y)) := sorry -- by funext y; simp

  @[simp]
  theorem adjoint_of_neg : (Neg.neg : X → X)† = Neg.neg := sorry
  @[simp]
  theorem adjoint_of_neg_of_fun [IsLin f] : (-f)† = -(f†) := sorry -- by funext y; simp[Neg.neg]

  @[simp]
  theorem adjoint_of_inner_1 (f : X → Y) [IsLin f] (y : Y) : (λ x : X => ⟨f x, y⟩)† = (λ (s : ℝ) => s * f† y) := sorry
  @[simp]
  theorem adjoint_of_inner_2 (f : X → Y) [IsLin f] (y : Y) : (λ x : X => ⟨y, f x⟩)† = (λ (s : ℝ) => s * f† y) := sorry
