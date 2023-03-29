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
      ∂ (λ x' => f x' (g x)) x dx
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
    λ f df y x => df x y c :=
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
  fun_trans
  done


example {α β₁ β₂ γ : Type} (f : β₁ → β₂ → γ) (g₁ : α → β₁) (g₂ : α → β₂) [Add γ]
  : ∂ (λ x => f (g₁ x) (g₂ x))
    = 
    λ x dx => 
      ∂ (λ x' => f x' (g₂ x)) (g₁ x) (∂ g₁ x dx)        
      +
      ∂ (f (g₁ x)) (g₂ x) (∂ g₂ x dx) :=
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


example {α β₁ β₂ γ : Type} [Add α] (f : β₁ → β₂ → γ) (g₁ : α → β₁) (g₂ : α → β₂)
  : (λ x => f (g₁ x) (g₂ x))†
    = 
    λ z => 
      let (b₁,b₂) := (uncurry f)† z 
      g₁† b₁ + g₂† b₂ :=
by
  fun_trans
  done


example {α β : Type} [Add α] [Add β] (g₁ : α → β) (g₂ : α → β)
  : (λ x => (g₁ x) + (g₂ x))†
    = 
    λ z => g₁† z + g₂† z :=
by
  fun_trans
  done


example {α β₁ β₂ β₃ γ : Type} [Add α] (f : β₁ → β₂ → β₃ → γ) (g₁ : α → β₁) (g₂ : α → β₂) (g₃ : α → β₃)
  : (λ x => f (g₁ x) (g₂ x) (g₃ x))†
    =
    λ z => 
      let (b₁,b₂,b₃) := (uncurry3 f)† z
      g₁† b₁ + (g₂† b₂ + g₃† b₃) :=
by
  fun_trans
  done


example {α β₁ β₂ γ : Type} [Add α] [Add (α×β₁)] [Add ((α×β₂)×β₂)] (f : β₁ → β₂ → β₃ → γ) (g₁ : α → β₁) (g₂ : α → β₂) (g₃ : α → β₃) 
 : (λ x => (λ (b₁,b₂,b₃) => f b₁ b₂ b₃) (g₁ x, g₂ x, g₃ x))
   =
   λ x => f  (g₁ x) (g₂ x) (g₃ x) :=
by
  rfl

@[simp ↓ high]
theorem Prod.fst.diff 
  : ∂ (λ x : α × β => x.1) = λ x dx => dx.1 := sorry

@[simp ↓ high]
theorem Prod.snd.diff 
  : ∂ (λ x : α × β => x.2) = λ x dx => dx.2 := sorry

@[simp ↓ high]
theorem Prod.fst.adj [OfNat β 0]
  : (λ x : α × β => x.1)† = λ x => (x,0) := sorry

@[simp ↓ high]
theorem Prod.snd.adj [OfNat α 0]
  : (λ x : α × β => x.2)† = λ x => (0,x) := sorry

@[simp]
theorem add_diff [Add α]
  : ∂ (uncurry λ x y : α => x + y) = λ (x,y) (dx,dy) => dx + dy := sorry

example (f : α → α) [Add α] [OfNat α 0]
  : ∂ (λ x => 
         let y := f x
         let z := f y
         y + z + f z)
    =
    sorry
  :=
by
  fun_trans
  fun_trans
  simp (config := {zeta := false}) []
  done


@[simp ↓]
theorem hoho (f : β → γ) (z : γ)
  : ((fun x : β × α => f x.fst)† z).fst 
    =
    f† z
  := sorry

@[simp ↓]
theorem hoho' (f : β → γ) (z : γ) [OfNat α 0]
  : ((fun x : β × α => f x.fst)† z).snd
    =
    0
  := sorry


set_option trace.Meta.Tactic.simp.discharge true in
example {α : Type} (f g h : α → α) [Add α] [Add (α×α)] [OfNat α 0] [OfNat (α×α) 0]
  : (λ x => 
         let y := f x
         let z := g y
         let z' := g z
         h z')†
    =
    sorry
  :=
by
  fun_trans
  fun_trans
  simp (config := {zeta := false}) []
  fun_trans
  simp (config := {zeta := false}) []
  simp
  done



set_option trace.Meta.Tactic.fun_trans.step true in
set_option trace.Meta.Tactic.simp.rewrite true in
-- set_option pp.all true in
example {α β γ : Type}
  : ∂ (λ (x : α × β × γ) =>
         x.snd.fst)
    =
    sorry 
  :=
by
  fun_trans
  done



example 
  : ∂ (Prod.snd : α × (β × γ) → β × γ)
  =
    fun x dx => sorry
        -- ((∂fun x => x.snd.fst) x dx, (∂fun x => x.snd.snd) x dx)
  :=
by
  simp
  

