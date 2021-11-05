import SciLean.Categories.Lin
import SciLean.Simp

import Init.Classical

namespace SciLean

variable {X Y Z : Type} [Hilbert X] [Hilbert Y] [Hilbert Z]

def adjoint_definition (f : X → Y) (h : IsLin f) (y : Y) 
    : ∃ (x' : X), ∀ x, ⟨x', x⟩ = ⟨y, (f x)⟩ := sorry

noncomputable
def adjoint (f : X → Y) (y : Y) : X :=
    match Classical.propDecidable (IsLin f) with
      | isTrue  h => Classical.choose (adjoint_definition f h y)
      | _ => (0 : X)

postfix:max "†" => adjoint

namespace Adjoint

  instance (f : X → Y) [IsLin f] : IsLin f† := sorry

  @[simp]
  def adjoint_of_adjoint (f : X → Y) [IsLin f] : f†† = f := sorry

  @[simp] 
  def adjoint_of_id 
      : (id : X → X)† = id := sorry

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
  def adjoint_of_composition (f : Y → Z) [IsLin f] (g : X → Y) [IsLin g] 
      : (f∘g)† = g† ∘ f† := sorry

  @[simp]
  def adjoint_of_inner_1 (x : X) (s : ℝ) : (λ y : X => ⟨y, x⟩)† s = s * x := sorry

  @[simp]
  def adjoint_of_inner_2 (x : X) (s : ℝ) : (λ y : X => ⟨x, y⟩)† s = s * x := sorry

  variable (f g : X → Y) 
  variable (r : ℝ)

  @[simp]
  def adjoint_of_add [IsLin f] [IsLin g] : (f + g)† = f† + g† := sorry

  @[simp]
  def adjoint_of_add_alt [IsLin f] [IsLin g] : (λ x => f x + g x)† = (λ y => f† y + g† y) := sorry

  @[simp]
  def adjoint_of_sub [IsLin f] [IsLin g] : (f - g)† = f† - g† := sorry

  -- @[simp]
  -- def adjoint_of_hmul [IsLin f] : (r*f)† = r*f† := sorry

  @[simp]
  def adjoint_of_hmul : (HMul.hMul r : X → X)† = HMul.hMul r := sorry


  @[simp]
  def adjoint_of_hmul_alt (f : X → Y) [IsLin f] (r : ℝ) : (λ x => r*(f x))† = (λ y => r*(f† y)) := sorry

  @[simp]
  def adjoint_of_neg [IsLin f] : (-f)† = -f† := sorry


  example [IsLin f] [IsLin g] (y : Y) : (λ x => f x + g x)† y = f† y + g† y := by simp

  example (y : Y) (r : ℝ) : (λ x => ⟨x,y⟩)† r = r*y := by simp

  example (y : X) (r : ℝ) : (λ x => ⟨x,y⟩ + ⟨y,x⟩)† r = 2*r*y := by simp; done

  example (r : ℝ) (x' : X)
          : (λ x : X => r*((λ x'' => ⟨x', x''⟩) x))† = λ s => r * s * x' := 
  by
    simp; funext s; simp[Function.comp]



end Adjoint

