import Mathlib.Init.Function
import SciLean.Tactic.FunctionTransform.Core

postfix:max "⁻¹" => Function.invFun

set_option trace.Meta.Tactic.fun_trans.trans true 

example {α β γ : Type} [Nonempty α] [Nonempty β]
  : ∂(λ (x : Nat) => x) = λ x dx => dx := 
by
  fun_trans
  done

example {α β γ : Type} [Nonempty α] [Nonempty β]
  : ∂(λ (x : Nat) (y : Nat) => x) = λ x dx y => dx := 
by
  fun_trans  -- (config := {singlePass := true})
  done

example {α β γ : Type} [Nonempty α] [Nonempty β]
  : ∂(λ (x : Nat) (y z : Nat) => x) = λ x dx y z => dx := 
by
  fun_trans
  done

example {α β γ : Type} (f : β → γ) (g : α → β) [Nonempty α] [Nonempty β]
  : ∂(λ x => f (g x)) = λ x dx => ∂ f (g x) (∂ g x dx) := 
by
  fun_trans
  done

example {α β γ : Type} (f : α → β → γ) (g : α → β)  [Add γ]
  : ∂(λ x => f x (g x)) 
    = 
    λ x dx => 
      ∂ f x dx (g x)
      +
      ∂ (f x) (g x) (∂ g x dx) := 
by
  fun_trans
  done

example {α β γ δ : Type} (f : β → δ → γ) (g : α → β) (d : δ)
  : ∂(λ x => f (g x) d) = λ x dx => ∂ (λ y => f y d) (g x) (∂ g x dx) := 
by
  fun_trans
  done

example (x : Nat)
  : ∂(λ (y : Nat) => x) = λ y dy => 0 := 
by
  fun_trans
  done


example (x : α)
  : ∂ (λ (f : α → β) => f x) 
    =
    λ f df => df x :=
by
  fun_trans
  done

example
  : ∂ (λ (f : α → β) x => f x) 
    =
    λ f df x => df x :=
by
  fun_trans
  done


-- set_option trace.Meta.Tactic.fun_trans.step true in
example (x : α) (y : β)
  : ∂ (λ (f : α → β → γ) => f x y) 
    =
    λ f df => df x y :=
by
  fun_trans
  done


example c
  : ∂ (λ (f : α → β → γ → δ) y x => f x y c) 
    =
    λ f df y x=> df x y c :=
by
  fun_trans
  done


-- set_option trace.Meta.Tactic.fun_trans.step true in
example (f : α → β → γ)
  : ∂ (λ y => sum (λ x => f x y))
    =
    λ y dy => sum λ x => ∂ (f x) y dy :=
by
  fun_trans
  done


-- set_option trace.Meta.Tactic.fun_trans.step true in
example (f : α → β → γ)
  : ∂ (λ y => (sum f) y)
    =
    λ y dy => sum λ x => ∂ (f x) y dy :=
by
  fun_trans
  done
  


example (f : β₁ → β₂ → γ) (g₁ : α → β₁) (g₂ : α → β₂) [Add γ]
  : ∂ (λ x => f (g₁ x) (g₂ x))
    = 
    λ x dx => 
      ∂ (f (g₁ x)) (g₂ x) (∂ g₂ x dx)
      +
      ∂ (λ y => f y (g₂ x)) (g₁ x) (∂ g₁ x dx) :=
by
  fun_trans
  done


example (f : β → γ) (g : α → β) 
  : (λ x => f (g x))†
    =
    λ z => g† (f† z) :=
by
  fun_trans
  done


example {α β₁ β₂ γ : Type} [Add α] [Add (α×β₁)] [Add ((α×β₂)×β₂)] (f : β₁ → β₂ → γ) (g₁ : α → β₁) (g₂ : α → β₂) 
  : (λ x => f (g₁ x) (g₂ x))†
    = 
    λ z => sorry
:=
by
  fun_trans
  done
