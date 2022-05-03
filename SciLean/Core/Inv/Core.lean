import SciLean.Core.Prelude
import SciLean.Core.IsInv

namespace SciLean

noncomputable
constant inverse {X Y} [Nonempty X] (f : X → Y) : Y → X 

postfix:max "⁻¹" => inverse

----------------------------------------------------------------------

variable {α β γ : Type}
variable {X Y Z : Type} [Nonempty X] [Nonempty Y]
variable {Y₁ Y₂ : Type} [SemiHilbert Y₁] [SemiHilbert Y₂]
variable {ι : Type} [Enumtype ι]

@[simp]
theorem id.arg_x.inv_simp 
  : (λ x : X => x)⁻¹ = λ x => x := sorry

@[simp]
theorem const.arg_x.inv_simp [Subsingleton Y] [Inhabited Y]
  : (λ (x : X) (y : Y) => x)⁻¹ = λ x' => x' default := sorry

@[simp low]
theorem swap.arg_x.inv_simp 
  (f : Y → X → Z) [∀ y, IsInv (f y)] [Subsingleton Y] [Inhabited Y]
  : (λ x y => f y x)⁻¹ = λ x' => (f default)⁻¹ (x' default) := sorry
--- swap f x y = f y x

@[simp low]
theorem comp.arg_x.inv_simp 
  (f : Y → Z) [IsInv f] 
  (g : X → Y) [IsInv g] 
  : (λ x => f (g x))⁻¹ = λ x' => g⁻¹ (f⁻¹ x') := sorry

----------------------------------------------------------------------
-- These theorems are problematic when used with simp

@[simp low-1] -- try to avoid using this theorem
theorem comp.arg_x.parm1.inv_simp 
  (a : α) 
  (f : Y → α → Z) [IsInv (λ y => f y a)]
  (g : X → Y) [IsInv g] 
  : 
    (λ x => f (g x) a)⁻¹ = λ x' => g⁻¹ ((hold λ y => f y a)⁻¹ x')
:= by 
  (apply comp.arg_x.inv_simp (λ y => f y a) g) done

example [Nonempty Y]
  (a : α) 
  (f : Y → α → Z) [IsInv (λ y => f y a)]
  (g : X → Y) [IsInv g] 
  : 
    (λ x => f (g x) a)⁻¹ = λ z => g⁻¹ ((λ y => f y a)⁻¹ z)
:= by simp

@[simp low-1] -- try to avoid using this theorem
theorem comp.arg_x.parm2.inv_simp
  (a : α) (b : β)
  (f : Y → α → β → Z) [IsInv (λ y => f y a b)]
  (g : X → Y) [IsInv g] 
  : 
    (λ x => f (g x) a b)⁻¹ = λ x' => g⁻¹ ((hold λ y => f y a b)⁻¹ x')
:= by 
  (apply comp.arg_x.inv_simp (λ y => f y a b) g) done

@[simp low-1] -- try to avoid using this theorem
theorem comp.arg_x.parm3.inv_simp
  (a : α) (b : β) (c : γ)
  (f : Y → α → β → γ → Z) [IsInv (λ y => f y a b c)]
  (g : X → Y) [IsInv g] 
  : 
    (λ x => f (g x) a b c)⁻¹ = λ z => g⁻¹ ((hold λ y => f y a b c)⁻¹ z)
:= by 
  (apply comp.arg_x.inv_simp (λ y => f y a b c) g) done

-- theorem comp.arg_x.parm4.inv_simp
-- ...
