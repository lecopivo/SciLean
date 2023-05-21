import SciLean.Mathlib.Convenient.Basic
import SciLean.Core

namespace SciLean

class IsSmoothAt {X Y : Type _} [Vec X] [Vec Y] (f : X → Y) (x : X) : Prop where
  isSmooth : Mathlib.Convenient.is_smooth_at f x

--------------------------------------------------------------------------------

variable {α β : Type}
variable {X Y Z W U V: Type} [Vec X] [Vec Y] [Vec Z] [Vec W] [Vec U] [Vec V]
variable {Y₁ Y₂ Y₃ : Type} [Vec Y₁] [Vec Y₂] [Vec Y₃]


@[fun_prop_rule]
theorem IsSmoothAt.rule_id (x : X)
  : IsSmoothAt (λ x : X => x) x := sorry

@[fun_prop_rule]
theorem IsSmoothAt.rule_const (x : X) (y : Y)
  : IsSmoothAt (λ y : Y => x) y := sorry

@[fun_prop_rule]
theorem IsSmoothAt.rule_comp (x : X)
  (g : X → Y) [IsSmoothAt g x]
  (f : Y → Z) [IsSmoothAt f (g x)]
  : IsSmoothAt (λ x => f (g x)) x := sorry

@[fun_prop_rule]
theorem IsSmoothA.rule_prodMk (x : X)
  (f : X → Y) [IsSmoothAt f x]
  (g : X → Z) [IsSmoothAt g x]
  : IsSmoothAt (λ x => (f x, g x)) x := sorry

@[fun_prop_rule]
theorem IsSmoothAt.rule_pi (x : X)
  (f : α → X → Y) [∀ a, IsSmoothAt (f a) x]
  : IsSmoothAt (λ x a => f a x) x := sorry

@[fun_prop_rule]
theorem IsSmoothAt.rule_eval (a : α) (f : α → X)
  : IsSmoothAt (λ (f : α → X) => f a) f := sorry

@[fun_prop_rule]
theorem IsSmoothAt.rule_comp_eval 
  (x : X) (a : α) (f : X → α → Y) [IsSmoothAt f x]
  : IsSmoothAt (λ x => f x a) x := IsSmoothAt.rule_comp x f (λ g : α → Y => g a)

@[fun_prop_rule]
theorem IsSmoothAt.rule_fst (xy)
  : IsSmoothAt (λ xy : X×Y => xy.1) xy := sorry

@[fun_prop_rule]
theorem IsSmoothAt.rule_snd (xy)
  : IsSmoothAt (λ xy : X×Y => xy.2) xy := sorry
