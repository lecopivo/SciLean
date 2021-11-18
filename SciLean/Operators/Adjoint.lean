import SciLean.Categories
import SciLean.Operators.Inverse
import SciLean.Operators.Sum
import SciLean.Simp

import Init.Classical

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [Hilbert X] [Hilbert Y] [Hilbert Z]

def adjoint_definition (f : X → Y) (h : IsLin f) (y : Y) 
    : ∃ (x' : X), ∀ x, ⟨x', x⟩ = ⟨y, (f x)⟩ := sorry

noncomputable
def adjoint (f : X → Y) (y : Y) : X :=
    match Classical.propDecidable (IsLin f) with
      | isTrue  h => Classical.choose (adjoint_definition f h y)
      | _ => (0 : X)

postfix:max "†" => adjoint

def kron {n} (i j : Fin n) : ℝ := if (i==j) then 1 else 0

namespace Adjoint

  instance (f : X → Y) [IsLin f] : IsLin f† := sorry

  @[simp]
  def adjoint_of_adjoint (f : X → Y) [IsLin f] : f†† = f := sorry

  @[simp] 
  def adjoint_of_id 
      : (id : X → X)† = id := sorry

  @[simp] 
  def adjoint_of_id'
      : (λ x : X => x)† = id := sorry

  @[simp]
  def adjoint_of_const {n}
      : (λ (x : X) (i : Fin n) => x)† = sum := sorry

  @[simp]
  def adjoint_of_sum {n}
      : (sum)† = (λ (x : X) (i : Fin n) => x) := sorry

  @[simp]
  def adjoint_of_swap {n m}
      : (λ (f : Fin n → Fin m → Y) => (λ j i => f i j))† = λ f i j => f j i := sorry

  @[simp]
  def adjoint_of_parm {n} (f : X → Fin n → Y) (i : Fin n) [IsLin f]
      : (λ x => f x i)† = (λ y => f† (λ j => (kron i j)*y)) := sorry

  @[simp]
  def adjoint_of_arg {n} [NonZero n] 
      (f : Y → Fin n → Z) [IsLin f]
      (g1 : X → Y) [IsLin g1]
      (g2 : Fin n → Fin n) [IsInv g2]
      : (λ x i => f (g1 x) (g2 i))† = g1† ∘ f† ∘ (λ h => h ∘ g2⁻¹) := sorry

  @[simp] 
  def adjoint_of_composition (f : Y → Z) [IsLin f] (g : X → Y) [IsLin g] 
      : (f∘g)† = g† ∘ f† := sorry

  @[simp] 
  def adjoint_of_composition_parm {n} (f : β → Y → Z) [∀ b, IsLin (f b)] (g1 : Fin n → β) (g2 : X → Fin n → Y) [IsLin g2] 
      : (λ x i => (f (g1 i) (g2 x i)))† = g2† ∘ (λ z i => (f (g1 i))† (z i)) := sorry

  -- Unfortunatelly this theorem is dangerous and causes simp to loop indefinitely
  -- @[simp 1000000] 
  -- def adjoint_of_composition_arg (f : Y → β → Z) (b : β) [IsLin (λ y => f y b)] (g : X → Y) [IsLin g] 
  --     : (λ x => f (g x) b)† = g† ∘ (λ y => f y b)† := sorry

  @[simp]
  def adjoint_of_inner_1 (f : X → Y) [IsLin f] (y : Y) : (λ x : X => ⟨f x, y⟩)† = (λ (s : ℝ) => s * f† y) := sorry

  @[simp]
  def adjoint_of_inner_2 (f : X → Y) [IsLin f] (y : Y) : (λ x : X => ⟨y, f x⟩)† = (λ (s : ℝ) => s * f† y) := sorry

  @[simp]
  def adjoint_of_diag {Y1 Y2 : Type} [Hilbert Y1] [Hilbert Y2]
      (f : Y1 → Y2 → Z) (g1 : X → Y1) (g2 : X → Y2) 
      [IsLin (uncurry f)] [IsLin g1] [IsLin g2]
      : (λ x => f (g1 x) (g2 x))† = (uncurry HAdd.hAdd) ∘ (pmap g1† g2†) ∘ (uncurry f)† := sorry

  @[simp]
  def adjoint_of_diag_arg {Y1 Y2 : Type} [Hilbert Y1] [Hilbert Y2]
      (f : Y1 → Y2 → Z) (g1 : X → Fin n → Y1) (g2 : X → Fin n → Y2)
      [IsLin (uncurry f)] [IsLin g1] [IsLin g2]
      : (λ x i => f (g1 x i) (g2 x i))† = (uncurry HAdd.hAdd) ∘ (pmap g1† g2†) ∘ (λ f => (λ i => (f i).1, λ i => (f i).2)) ∘ (comp (uncurry f)†) := sorry

  @[simp]
  def adjoint_of_pullback {n} [NonZero n]
      (g : Fin n → Fin n) [IsInv g]
      : (λ (f : Fin n → X) => f ∘ g)† = (λ f => f ∘ g⁻¹) := sorry

  @[simp]
  def adjoint_of_pullback_arg {n} [NonZero n]
      (g : Fin n → Fin n) [IsInv g]
      : (λ (f : Fin n → X) i => f (g i))† = (λ f => f ∘ g⁻¹) := by simp


  variable (f g : X → Y) 
  variable (r : ℝ)

  @[simp]
  def adjoint_of_hadd : (λ x : X×X => x.1 + x.2)† = (λ x => (x,x)) := sorry
  @[simp]
  def adjoint_of_add : (λ x : X×X => Add.add x.1 x.2)† = (λ x => (x,x)) := sorry
  @[simp]
  def adjoint_of_add_of_fun [IsLin f] [IsLin g] : (f + g)† = f† + g† := by simp [HAdd.hAdd, Add.add]
  @[simp]
  def adjoint_of_add_of_fun_arg [IsLin f] [IsLin g] : (λ x => f x + g x)† = (λ y => f† y + g† y) := by simp
  @[simp]
  def adjoint_of_add_of_fun_arg_parm (f g : X → Fin n → Y) [IsLin f] [IsLin g] 
      : (λ x i => f x i + g x i)† = (λ x i => f x i)† + (λ x i => g x i)† := by funext z; simp

  @[simp]
  def adjoint_of_hsub : (λ x : X×X => x.1 - x.2)† = (λ x => (x,-x)) := sorry
  @[simp]
  def adjoint_of_sub : (λ x : X×X => Sub.sub x.1 x.2)† = (λ x => (x,-x)) := sorry
  @[simp]
  def adjoint_of_sub_of_fun [IsLin f] [IsLin g] : (f - g)† = f† - g† := sorry -- by funext y; simp[HSub.hSub, Sub.sub]
  @[simp]
  def adjoint_of_sub_of_fun_arg [IsLin f] [IsLin g] : (λ x => f x - g x)† = λ y => f† y - g† y := sorry -- by funext y; simp[pmap, uncurry]; done
  @[simp]
  def adjoint_of_sub_of_fun_arg_parm (f g : X → Fin n → Y) [IsLin f] [IsLin g] 
      : (λ x i => f x i - g x i)† = (λ x i => f x i)† - (λ x i => g x i)† := sorry -- by funext z; simp[pmap, uncurry]; done

  @[simp]
  def adjoint_of_hmul_1 (f : X → ℝ) [IsLin f] (y : Y) : (λ x => (f x)*y)† = f† ∘ (λ y' => ⟨y,y'⟩) := sorry
  @[simp]
  def adjoint_of_hmul_1_parm (f : X → Fin i → ℝ) [IsLin f] (y : Fin i → Y) 
      : (λ x i => (f x i)*(y i))† = f† ∘ (λ y' i => ⟨y i,y' i⟩) := sorry
  @[simp]
  def adjoint_of_hmul_2 : (HMul.hMul r : X → X)† = HMul.hMul r := sorry
  @[simp]
  def adjoint_of_hmul_of_fun [IsLin f] : (r*f)† = r*f† := sorry -- by funext y; simp[HMul.hMul, Mul.mul]
  @[simp]
  def adjoint_of_hmul_of_fun_arg [IsLin f] (r : ℝ) : (λ x => r*(f x))† = (λ y => r*(f† y)) := sorry -- by funext y; simp

  @[simp]
  def adjoint_of_neg : (Neg.neg : X → X)† = Neg.neg := sorry
  @[simp]
  def adjoint_of_neg_of_fun [IsLin f] : (-f)† = -(f†) := sorry -- by funext y; simp[Neg.neg]

  example [IsLin f] [IsLin g] (y : Y) : (λ x => f x + g x)† y = f† y + g† y := by simp done

  example (y : Y) (r : ℝ) : (λ x => ⟨x,y⟩)† r = r*y := by simp 

  example (y : X) (r : ℝ) : (λ x => ⟨x,y⟩ + ⟨y,x⟩)† r = 2*r*y := by simp; done

  example (r : ℝ) (x' : X)
          : (λ x : X => r*((λ x'' => ⟨x', x''⟩) x))† = λ s => r * s * x' :=
  by
    simp; done

  example {n} [NonZero n] (f : Fin n → ℝ) (c : Fin n) 
          : (λ (g : Fin n → ℝ) => sum (λ i => (f i) * (g (i+c))))† (1 : ℝ) = (fun i => f (i - c)) := by simp; done

  example {n} [NonZero n] (f : Fin n → ℝ) (c : Fin n) 
          : (λ (g : Fin n → ℝ) => ⟨f, λ i => (g (i+c))⟩)† (1 : ℝ) = (fun i => f (i - c)) := by simp; done

  example : IsLin (λ (g : Fin n → ℝ) => (λ i => g (i+c))) := by infer_instance

  example {n} [NonZero n] (c : Fin n) : (λ (g : Fin n → ℝ) => (λ i => g (i+c)))† = (fun f x => f (x - c)) := by simp; done

end Adjoint
