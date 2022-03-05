import SciLean.Operators.Adjoint.Combinators

import SciLean.Simp

open Function
namespace SciLean

open SemiInner

variable {α β γ : Type}
variable {X Y Z : Type} {R D e}
variable [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
variable {ι κ : Type} [Enumtype ι] [Enumtype κ]

namespace Adjoint

  variable (f g : X → Y) 
  variable (r : ℝ)

  --- Addition
  instance : HasAdjoint (λ x : X×X => x.1 + x.2) := sorry
  @[simp]
  theorem adjoint_of_hadd : adjoint (λ x : X×X => x.1 + x.2) = (λ x => (x,x)) := sorry
  @[simp]
  theorem adjoint_of_add_of_fun [HasAdjoint f] [HasAdjoint g] : adjoint (f + g) = adjoint f + adjoint g := by funext a; simp[HAdd.hAdd, Add.add]; done
  @[simp]
  theorem adjoint_of_add_of_fun_arg [HasAdjoint f] [HasAdjoint g] : adjoint (λ x => f x + g x) = (λ y => adjoint f y + adjoint g y) := by funext a; simp; done
  @[simp]
  theorem adjoint_of_add_of_fun_arg_parm (f g : X → ι → Y) [HasAdjoint f] [HasAdjoint g]
      : adjoint (λ x i => f x i + g x i) = adjoint (λ x i => f x i) + adjoint (λ x i => g x i) := by funext z; simp; done

  example [HasAdjoint f] [HasAdjoint g] : (f + g)† = f† + g† := by simp

  --- Subtraction
  instance : HasAdjoint (λ x : X×X => x.1 - x.2) := sorry
  @[simp]
  theorem adjoint_of_hsub : adjoint (λ x : X×X => x.1 - x.2) = (λ x => (x,-x)) := sorry
  @[simp]
  theorem adjoint_of_sub_of_fun [HasAdjoint f] [HasAdjoint g] : adjoint (f - g) = adjoint f - adjoint g := by funext a; simp[HSub.hSub, Sub.sub]; admit -- almost done
  @[simp]
  theorem adjoint_of_sub_of_fun_arg [HasAdjoint f] [HasAdjoint g] : adjoint (λ x => f x - g x) = λ y => adjoint f y - adjoint g y := by funext a; simp; admit -- almost done
  @[simp]
  theorem adjoint_of_sub_of_fun_arg_parm (f g : X → Fin n → Y) [HasAdjoint f] [HasAdjoint g]
      : adjoint (λ x i => f x i - g x i) = adjoint (λ x i => f x i) - adjoint (λ x i => g x i) := by funext z; simp; admit

  --- Multiplication
  instance (r : ℝ) : HasAdjoint (λ x : X => r * x) := sorry
  instance {X} [Hilbert X] (x : X) : HasAdjoint (λ r : ℝ => r * x) := sorry
  -- TODO: Figure out why the following instance is necessary to prove:
  -- example : ∀ y, HasAdjoint (λ x : ℝ => y * x) := by infer_instance
  -- oddly enought moving `y` before the colon makes it work
  instance (r : ℝ) : HasAdjoint (λ x : ℝ => r * x) := sorry

  @[simp]
  theorem adjoint_of_hmul_1 {X} [Hilbert X] (x : X) : adjoint (λ r : ℝ => r * x ) = (λ y => ⟪x, y⟫) := sorry
  @[simp]
  theorem adjoint_of_hmul_2 (r : ℝ) : adjoint (λ x : X => r*x) = (λ x : X => r*x) := sorry

  -- set_option trace.Meta true in
  -- @[simp]
  -- theorem adjoint_of_hmul_1_parm {X Y ι : Type} [Hilbert X] [Hilbert Y] [Enumtype ι] (f : X → ι → ℝ) [HasAdjoint f] (y : ι → Y) 
  --     : (λ x i => (f x i)*(y i))† = f† ∘ (λ y' i => ⟪y i,y' i⟫ ()) := by simp done
  @[simp]
  theorem adjoint_of_hmul_of_fun [HasAdjoint f] : adjoint (r*f) = r*(adjoint f) := by funext y; simp[HMul.hMul, Mul.mul] admit
  @[simp]
  theorem adjoint_of_hmul_of_fun_arg [HasAdjoint f] (r : ℝ) : adjoint (λ x => r*(f x)) = (λ y => r*(adjoint f y)) := by funext x; simp admit -- by funext y; simp

  instance : HasAdjoint (λ x : X => -x) := sorry
  @[simp]
  theorem adjoint_of_neg : adjoint (Neg.neg : X → X) = Neg.neg := sorry
  @[simp]
  theorem adjoint_of_neg_of_fun [HasAdjoint f] : adjoint (-f) = -(adjoint f) := sorry --by funext y; simp[Neg.neg]


  instance {X} [Hilbert X] (y : X) : HasAdjoint (λ x : X => ⟪x, y⟫) := sorry
  instance {X} [Hilbert X] (x : X) : HasAdjoint (λ y : X => ⟪x, y⟫) := sorry
  @[simp]
  theorem adjoint_of_inner_1 {X} [Hilbert X] (y : X) : (λ x : X => ⟪x, y⟫)† = (λ (s : ℝ) => s * y) := sorry
  @[simp]
  theorem adjoint_of_inner_2 {X} [Hilbert X] (x : X) : (λ y : X => ⟪x, y⟫)† = (λ (s : ℝ) => s * x) := sorry

  @[simp]
  theorem adjoint_of_inner_1' {X Y : Type} [Hilbert X] [Hilbert Y] (f : X → Y) [HasAdjoint f] (y : Y) : adjoint (λ x : X => ⟪f x, y⟫) = (λ (s : ℝ) => s * (adjoint f) y) := by sorry -- funext r; autoadjoint; simp; admit
  @[simp]
  theorem adjoint_of_inner_2' {X Y : Type} [Hilbert X] [Hilbert Y] (f : X → Y) [HasAdjoint f] (y : Y) : adjoint (λ x : X => ⟪y, f x⟫) = (λ (s : ℝ) => s * (adjoint f) y) := by sorry


  
