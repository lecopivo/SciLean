import SciLean.Experimental.DiffAt.IsSmoothAt

namespace SciLean

variable {α β γ : Type}
variable {X Y Z U V : Type} [Vec X] [Vec Y] [Vec Z] [Vec U] [Vec V]
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]


@[fun_trans_rule]
theorem differentialAt.rule_comp {x : X}
  (g : X → Y) [IsSmoothAt g x]
  (f : Y → Z) [IsSmoothAt f (g x)]
  : ∂ (λ x : X => f (g x))
    =
    λ x dx => ∂ f (g x) (∂ g x dx) := sorry

@[fun_trans_rule]
theorem differentialAt.rule_pi {x : X}
  (f : α → X → Y) [∀ a, IsSmoothAt (f a) x]
  : ∂ (λ (g : α → X) (a : α) => f a (g a))
    =
    λ g dg a => ∂ (f a) (g a) (dg a) := sorry

theorem differential.rule_const' 
  : ∂ (λ (x : X) (y : Y) => x)
    =
    λ x dx y => dx := sorry

@[fun_trans_rule]
theorem differential.rule_swap 
  (f : α → X → Y) [∀ a, IsSmooth (f a)]
  : ∂ (λ (x : X) (a : α) => f a x)
    =
    λ x dx a => ∂ (f a) x dx := 
by 
  rw[differential.rule_comp (λ (g : α → X) (a : α) => f a (g a)) (λ x a => x)]
  simp[differential.rule_pi, differential.rule_const']
  done

@[fun_trans_rule]
theorem differential.rule_eval (X) [Vec X] (a : α)
  : ∂ (λ (f : α → X) => f a)
    =
    λ f df => df a := sorry

set_option pp.all true in
@[fun_trans_rule]
theorem differential.rule_prodMk 
  (f : X → Y) [IsSmooth f]
  (g : X → Z) [IsSmooth g]
  : ∂ (λ x => (f x, g x))
    =
    λ x dx => (∂ f x dx, ∂ g x dx) := sorry

@[fun_trans_rule]
theorem differential.rule_letComp 
  (f : Y → Z) [IsSmooth f]
  (g : X → Y) [IsSmooth g]
  : ∂ (λ (x : X) => let y := g x; f y)
    =
    λ x dx =>
      let y  := g x
      let dy := ∂ g x dx 
      ∂ f y dy := sorry

@[fun_trans_rule]
theorem differential.rule_letBinop 
  (f : X → Y → Z) [IsSmooth λ xy : X×Y => f xy.1 xy.2]
  (g : X → Y) [IsSmooth g]
  : ∂ (λ (x : X) => let y := g x; f x y)
    =
    λ x dx =>
      let y  := g x
      let dy := ∂ g x dx 
      ∂ (λ xy => f xy.1 xy.2) (x,y) (dx,dy) := sorry
