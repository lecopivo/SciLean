import SciLean.Core
import SciLean.Tactic.AutoDiff

open SciLean

variable {α β γ : Type}
variable {X Y Z W : Type} [Vec X] [Vec Y] [Vec Z] [Vec W]
variable {Y₁ Y₂ : Type} [Vec Y₁] [Vec Y₂]

set_option maxHeartbeats 4000
set_option synthInstance.maxHeartbeats 1000
set_option synthInstance.maxSize 80

example (f : Y → Z) [IsSmoothT f] (g : X → Y) [IsSmoothT g]
  : ∂ (λ x => f (g x)) = λ x dx => ∂ f (g x) (∂ g x dx) := by symdiff

example (a : α) (f : Y → α → Z) [IsSmoothT f] (g : X → Y) [IsSmoothT g]
  : ∂ (λ x => f (g x) a) = λ x dx => ∂ f (g x) (∂ g x dx) a := by symdiff

example (f : Y → Z) [IsSmoothT f]
  : ∂ (λ (g : α → Y) (a : α) => f (g a)) = λ g dg a => ∂ f (g a) (dg a) := by symdiff

example
  : ∂ (λ (f : β → Z) (g : α → β) (a : α) => f (g a)) = λ f df (g : α → β) a => df (g a) := by symdiff

example (f : Y → β → Z) (g : X → Y) [IsSmoothT f] [IsSmoothT g] (b) 
  : ∂ (λ x => f (g x) b) = λ x dx => ∂ f (g x) (∂ g x dx) b := by symdiff

example (f : Y → β → Z) [IsSmoothT f] (b)
  : ∂ (λ (g : α → Y) a => f (g a) b) = λ g dg a => ∂ f (g a) (dg a) b := by symdiff

example (f : β → Y → Z) (g : β → X → Y) [∀ b, IsSmoothT (f b)] [∀ b, IsSmoothT (g b)]
  : ∂ (λ x b => f b (g b x)) = λ x dx b => ∂ (f b) (g b x) (∂ (g b) x dx) := by symdiff

example (f : Y → β → Z) (g : X → Y) [IsSmoothT f] [IsSmoothT g]
  : ∂ (λ x b => f (g x) b) = λ x dx b => ∂ f (g x) (∂ g x dx) b := by symdiff

example (f : Y → β → Z) [IsSmoothT f]
  : ∂ (λ (g : α → Y) a b => f (g a) b) = λ g dg a b => ∂ f (g a) (dg a) b := by symdiff

example (f : Y₁ → β2 → Z) (g2 : α → β2) [IsSmoothT f] (g dg)
  : ∂ (λ  (g1 : α → Y₁) a => f (g1 a) (g2 a)) g dg = λ a => ∂ f (g a) (dg a) (g2 a) := by symdiff

example (f : β1 → Y₂ → Z) (g1 : α → β1) [∀ y1, IsSmoothT (f y1)] 
  : ∂ (λ (g2 : α → Y₂) a => f (g1 a) (g2 a)) = λ g dg a => ∂ (f (g1 a)) (g a) (dg a) := by symdiff

example {α : Type} {β : α → Type} (a : α) [∀ a, Add (β a)] 
  : (λ (f g : (a:α) → β a) a => (f + g) a) = (λ (f g : (a:α) → β a) a => f a + g a) := by symdiff; done


example (f g : X → α → Y) [IsSmoothT f] [IsSmoothT g]
  : ∂ (λ x a => f x a + g x a) 
    =
    λ x dx a => ∂ f x dx a + ∂ g x dx a := by symdiff; done

set_option maxHeartbeats 7000 in  
set_option synthInstance.maxHeartbeats 5000 in
example (f : Y₁ → Y₂ → β → Z) (g1 : X → Y₁) (g2 : X → Y₂)
  [IsSmoothNT 2 f] [IsSmoothT g1] [IsSmoothT g2]
  : ∂ (λ (x : X) (b : β) => f (g1 x) (g2 x) b) 
    = 
    λ x dx b => ∂ f (g1 x) (∂ g1 x dx) (g2 x) b + ∂ (f (g1 x)) (g2 x) (∂ g2 x dx) b := by symdiff; done

example {X} [Hilbert X] : ∂ (λ x : X => ⟪x, x⟫) = λ x dx =>  ⟪dx, x⟫ + ⟪x, dx⟫ := by symdiff; done


--- Other a bit more disorganized tests

variable (f : Y → Z) [IsSmoothT f]
variable (g : X → Y) [IsSmoothT g]
variable (f1 : X → X) [IsSmoothT f1]
variable (f2 : Y → Y) [IsSmoothT f2]
variable (f3 : Z → Z) [IsSmoothT f3]
variable (F : X → Y → Z) [IsSmoothNT 2 F]
variable (G : X × Y → Z) [IsSmoothT G]

variable (x dx : X) (y dy : Y) (z dz : Z)

example : ∂ (λ x => f (g (f1 x))) x dx = ∂ f (g (f1 x)) (∂ g (f1 x) (∂ f1 x dx)) := by symdiff; done
example : ∂ (λ x : X => x + x) x dx = (2:ℝ) * dx := by symdiff; done

example : ∂ (λ (x : X) => F x (g x)) x dx = ∂ F x dx (g x) + ∂ (F x) (g x) (∂ g x dx) := by symdiff; done
example : ∂ (λ (x : X) => f3 (F x (g x))) x dx = ∂ f3 (F x (g x)) (∂ F x dx (g x) + ∂ (F x) (g x) (∂ g x dx)) := by symdiff; done
example g dg x : ∂ (λ (g : X → Y) => f (g x)) g dg = ∂ f (g x) (dg x) := by symdiff; done
example g dg x : ∂ (λ (g : X → Y) (x : X) => F x (g x)) g dg x = ∂ (F x) (g x) (dg x) := by symdiff; done
set_option synthInstance.maxHeartbeats 3000 in
example g dg x : ∂ (λ (g : X → X) (y : Y) => F (g x) y) g dg y = ∂ F (g x) (dg x) y := by symdiff; done
example (r dr : ℝ) : ∂ (λ x : ℝ => x*x + x) r dr = dr * r + r * dr + dr := by symdiff; done
example g dg y : ∂ (λ (g : X → X) (x : X) => F (g x) y) g dg x = ∂ F (g x) (dg x) y := by symdiff; done 
example (r dr : ℝ) : ∂ (λ x : ℝ => x*x*x + x) r dr = (dr * r + r * dr) * r + r * r * dr + dr := by symdiff; done


example : ⅆ (λ x : ℝ => ∥x∥²) = λ x => (2:ℝ) * x := by symdiff; done
example {X} [Hilbert X] (m k : ℝ) (p : X) : ∇ (λ x : X => 1/2*m * ∥p∥² + 1/2*k * ∥x∥²) = λ x : X => k * x := by symdiff; done
example {X} [Hilbert X] (m k : ℝ) (x : X) : ∇ (λ p : X => 1/(2*m) * ∥p∥² + 1/2*k * ∥x∥²) = λ p : X => 1/m * p := by symdiff; done
